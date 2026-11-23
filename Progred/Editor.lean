import Progred.Editing
import Deui.Redraw

/-!
The editor as a deui app: its state is the model, and its view the lines
of the layout that the window shows, each a row of the scene: the
selection's wash, a mark on the other places the selected cell is, the
text, a caret, and a target on each span, tagged with its occurrence, so a
click finds what it's on. Over them, the card of
offers for what's being typed.
-/

namespace Progred.Editor

open Progred Deui

def paper : UInt32 := 0xFFFFFF
def wash : UInt32 := 0xC7E2FF
def accent : UInt32 := 0x007AFF
def card : UInt32 := 0xF1F4F9
def chosen : UInt32 := 0xD3E4FF
def mistaken : UInt32 := 0xFFD9D6
def same : UInt32 := 0xE4ECF7

def color : Face → UInt32
  | .ink => 0x212B41
  | .name => 0x145BDB
  | .label => 0x7B3FC7
  | .string => 0xC34100
  | .number => 0x0B6E5A
  | .dim => 0x66738B
  | .delimiter => 0x8D9BB3
  | .result => 0x1A7F37
  | .error => 0xC62828
  | .caret => accent

def textSize : UInt32 := 15

def px (n : Nat) : Int32 := Int32.ofNat n

/-- Where a column is, in pixels from the left. -/
def x (col : Nat) : Int32 := px (Model.margin + col * Model.charWidth)

/-- Whether a selection covers an occurrence: it, and what's drawn inside
it; not the label of the field it's the value of. -/
def covers (sel : Selection) (o : Occ) : Bool :=
  match sel.stage with
  | .label => o.kind == .fieldEnd && o.path == sel.path
  | _ => sel.path.isPrefixOf o.path && !(o.kind == .label && o.path == sel.path) && o.kind != .fieldEnd

/-- The cell the selection is on: the cell selected, or the one whose name
is. -/
def selectedCell (m : Model) : Option CellId :=
  m.selection.bind fun sel =>
    if sel.stage != Stage.edge then none
    else
      let cellAt (path : Path) : Option CellId :=
        match m.at? path with
        | some (.cell c) => some c
        | _ => none
      (cellAt sel.path).orElse fun _ =>
        if sel.path.length ≥ 2 && sel.path.drop (sel.path.length - 2) == [.follow, .key Kinds.name] then
          cellAt (sel.path.take (sel.path.length - 2))
        else none

/-- One line, as a row's parts, from the row's top left. -/
def lineParts (m : Model) (occs : Array Occ) (line : Line) : List Scene :=
  let selected (s : Span) : Bool :=
    match m.selection, occs[s.mark - 1]? with
    | some sel, some o => s.mark > 0 && covers sel o
    | _, _ => false
  let covered := line.toList.filter selected
  let washes : List Scene :=
    match covered with
    | [] => []
    | first :: _ =>
      let stop := covered.foldl (fun acc s => max acc s.stop) first.col
      let width := max 1 (stop - first.col)
      [.fill (x first.col - 2) 1 (px (width * Model.charWidth) + 4) (px Model.lineHeight - 2) wash]
  let texts := line.toList.filterMap fun s =>
    if s.text.isEmpty then none else some (.label (x s.col) 2 textSize (color s.face) s.text)
  let carets := line.toList.filterMap fun s =>
    if s.face == .caret then some (.fill (x s.col - 1) 2 2 (px Model.lineHeight - 4) accent) else none
  let targets := line.toList.filterMap fun s =>
    if s.mark > 0 && !s.text.isEmpty then
      some (.target (x s.col) 0 (px (s.text.length * Model.charWidth)) (px Model.lineHeight) s.mark.toUInt32)
    else none
  -- What an evaluation's error is about, on red.
  let failed := line.toList.filter fun s => s.mark > 0 && ((occs[s.mark - 1]?).map (·.failed)).getD false
  let errors : List Scene :=
    match failed with
    | [] => []
    | first :: _ =>
      let stop := failed.foldl (fun acc s => max acc s.stop) first.col
      [.fill (x first.col - 2) 1 (px ((stop - first.col) * Model.charWidth) + 4) (px Model.lineHeight - 2) mistaken]
  -- The other places the selected cell is, marked: where it's a value, and
  -- where it's a field's label.
  let others : List Scene :=
    match selectedCell m with
    | none => []
    | some c => line.toList.filterMap fun s =>
      match occs[s.mark - 1]? with
      | some o =>
        let isIt := (o.kind == .value && m.at? o.path == some (.cell c)) ||
          (o.kind == .label && o.path.getLast? == some (.key c))
        if s.mark > 0 && !s.text.isEmpty && !selected s && isIt then
          some (.fill (x s.col - 2) 1 (px (s.text.length * Model.charWidth) + 4) (px Model.lineHeight - 2) same)
        else none
      | none => none
  errors ++ others ++ washes ++ texts ++ carets ++ targets

/-- Where the caret is: its line and column. -/
def caretAt (lines : Array Line) : Option (Nat × Nat) :=
  (List.range lines.size).findSome? fun i =>
    (lines[i]!.toList.find? (·.face == .caret)).map fun s => (i, s.col)

/-- The card of offers, under the caret: up to 8, the chosen one marked. -/
def offersCard (m : Model) (lines : Array Line) : List Scene :=
  let offers := Model.offers m
  match m.selection.bind (·.editing), caretAt lines with
  | some e, some (line, col) =>
    if offers.isEmpty || !e.picker then []
    else
      let from_ := if e.choice ≥ 8 then e.choice - 7 else 0
      let shown := (offers.drop from_).take 8
      let width := (shown.foldl (fun acc o => max acc (o.text.length + o.detail.length + 8)) 24) * Model.charWidth
      let top := px (Model.margin + (line + 1) * Model.lineHeight) - px m.scroll
      let rows := (List.range shown.length).zip shown |>.flatMap fun (i, o) =>
        let y := px (i * Model.lineHeight)
        let index := from_ + i
        (if index == e.choice then [Scene.fill 0 y (px width) (px Model.lineHeight) chosen] else []) ++
          [.label 8 (y + 2) textSize (color (if o.isNew then .dim else .ink)) (if o.isNew then "new " ++ o.text else o.text),
           .label (px width - px ((o.detail.length + 1) * Model.charWidth)) (y + 2) textSize (color .dim) o.detail,
           .target 0 y (px width) (px Model.lineHeight) (Model.offerTag + index.toUInt32)]
      [.group (x col) top
        ([Scene.fill (-1) (-1) (px width + 2) (px (shown.length * Model.lineHeight) + 2) (color .delimiter),
          .fill 0 0 (px width) (px (shown.length * Model.lineHeight)) card] ++ rows)]
  | _, _ => []

/-- The rows on screen: the lines in the window, then the card of offers. -/
def rows (m : Model) : List Scene :=
  let (lines, occs) := m.laid
  let first := m.scroll / Model.lineHeight
  let count := m.height / Model.lineHeight + 2
  let visible := (List.range count).filterMap fun k =>
    let i := first + k
    lines[i]?.map fun line =>
      Scene.group 0 (px (Model.margin + i * Model.lineHeight) - px m.scroll) (lineParts m occs line)
  visible ++ offersCard m lines

/-- What an event does to the model. -/
def event (m : Model) (scene : Scene) : App.Event → Model
  | .text t => (t.foldl Model.typed m).revealed
  | .key code true mods => (Model.key m code mods).revealed
  | .press px_ py 0 true =>
    match scene.hit (App.coordinate px_) (App.coordinate py) with
    | some h => Model.clicked m h.tag
    | .none => { m with selection := .none }
  | .scroll _ _ _ dy =>
    let lines := m.laid.1.size
    let most := (lines * Model.lineHeight + 2 * Model.margin) - min m.height (lines * Model.lineHeight + 2 * Model.margin)
    let step := 3 * Model.lineHeight
    { m with scroll := if dy > 0 then m.scroll - min m.scroll step else min most (m.scroll + step) }
  | .resize w h => { m with width := w.toNat, height := h.toNat }
  | _ => m

/-- The editor's state is the model, replaced whole. -/
abbrev edits : EditStructure := whole (plain Model)

def app : App.App edits where
  view := Redraw.redraw (cs := edits) rows
  respond m scene e := [.replace (event m scene e)]

end Progred.Editor
