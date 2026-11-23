import Progred.Display

/-!
The editor's state: the document, the selection, folds, what evaluations
gave, and undo. A write records where the document was, so undo is the
whole state before it. Navigation goes by what's drawn: the occurrences of
the layout, part by part, in reading order.
-/

namespace Progred

/-- The state an undo goes back to. -/
structure Snapshot where
  doc : Document
  selection : Option Path
  folds : List (Path × Bool)

structure Model where
  doc : Document := {}
  library : Library := Builtin.library
  selection : Option Selection := none
  folds : List (Path × Bool) := []
  /-- What evaluations gave, by expression; `stale` when the document has
  changed since they ran. -/
  results : List (Value × Outcome) := []
  /-- What projections that are functions gave, held as one object so
  parts compare it at once. -/
  layouts : Shared (List (Value × Value × Value)) := ⟨[]⟩
  stale : Bool := true
  undo : List Snapshot := []
  redo : List Snapshot := []
  /-- Whether the last write was typing in a line, which the next
  keystroke's write joins rather than adding an undo step. -/
  typingRun : Bool := false
  /-- Fresh cell ids, minted outside and used as new cells are made. -/
  ids : List CellId := []
  /-- Whether the document differs from the file, and a save was asked. -/
  dirty : Bool := false
  saveAsked : Bool := false
  /-- Text waiting to go to the clipboard, and whether a paste was asked. -/
  copied : Option String := none
  pasteAsked : Bool := false
  /-- Whether the selection is to be scrolled into the window, once it's
  laid out. -/
  reveal : Bool := false
  /-- The window, in pixels, and how far the view is scrolled down. -/
  width : Nat := 900
  height : Nat := 700
  scroll : Nat := 0

namespace Model

/-- A character's width and a line's height, in pixels, and the margin. -/
def charWidth : Nat := 9
def lineHeight : Nat := 22
def margin : Nat := 16

def shown (m : Model) : Shown :=
  { doc := m.doc, library := m.library, selection := m.selection, folds := m.folds, results := m.results,
    layouts := m.layouts.val }

def ribbon (m : Model) : Nat := max 30 ((m.width - 2 * margin) / charWidth)

/-- The value at a path. -/
def at? (m : Model) (path : Path) : Option Value := m.doc.find? m.library path

/-- The cell the selection is on: the cell selected, or the one whose name
is. -/
def selectedCell (m : Model) : Option CellId :=
  m.selection.bind fun sel =>
    if sel.stage != .edge then none
    else
      let cellAt (path : Path) : Option CellId :=
        match m.at? path with
        | some (.cell c) => some c
        | _ => none
      (cellAt sel.path).orElse fun _ =>
        if sel.path.length ≥ 2 && sel.path.drop (sel.path.length - 2) == [.follow, .key Kinds.name] then
          cellAt (sel.path.take (sel.path.length - 2))
        else none

/-- What of the state the parts are drawn with. -/
def seen (m : Model) : Display.Seen :=
  let marked := m.selectedCell
  { selection := m.selection, folds := m.folds, results := m.results, layouts := m.layouts, marked,
    markedDefined := (marked.bind m.doc.definition?).isSome, ribbon := m.ribbon }

def snapshot (m : Model) : Snapshot := ⟨m.doc, m.selection.map (·.path), m.folds⟩

/-- The model with a new document: an undo step, unless it joins a run of
typing. -/
def write (m : Model) (doc : Document) (typing : Bool := false) : Model :=
  { m with
    doc, redo := [], stale := true, dirty := true, typingRun := typing,
    undo := if typing && m.typingRun then m.undo else m.snapshot :: m.undo }

def restore (m : Model) (s : Snapshot) : Model :=
  { m with doc := s.doc, selection := s.selection.map ({ path := · }), folds := s.folds,
           stale := true, dirty := true, typingRun := false }

def undone (m : Model) : Model :=
  match m.undo with
  | s :: rest => { m.restore s with undo := rest, redo := m.snapshot :: m.redo }
  | [] => m

def redone (m : Model) : Model :=
  match m.redo with
  | s :: rest => { m.restore s with redo := rest, undo := m.snapshot :: m.undo }
  | [] => m

/-- A fresh cell id, and the model without it. -/
def fresh (m : Model) : CellId × Model :=
  match m.ids with
  | id :: rest => (id, { m with ids := rest })
  | [] => (default, m)

/-! ## What's drawn, in reading order -/

open Display (Block Stop)

/-- The document laid out: its parts, one under another. -/
structure Layout where
  blocks : List Block

namespace Layout

/-- The document's layout, worked out from nothing. -/
def of (m : Model) : Layout := ⟨Display.blocks m.doc m.seen⟩

def lineCount (l : Layout) : Nat := l.blocks.foldl (fun n b => n + b.lines.size) 0

/-- The line a part starts at. -/
def lineOf (l : Layout) (block : Nat) : Nat :=
  (l.blocks.take block).foldl (fun n b => n + b.lines.size) 0

/-- The part a line is in, and the line within it. -/
def lineAt (l : Layout) (line : Nat) : Option (Block × Nat) := Id.run do
  let mut rest := line
  for b in l.blocks do
    if rest < b.lines.size then return some (b, rest)
    rest := rest - b.lines.size
  return none

/-- The lines, as plain text. -/
def plain (l : Layout) : List String :=
  l.blocks.flatMap fun b => b.lines.toList.map (·.plain)

end Layout

/-- Whether an occurrence is the selection's. -/
def isSelected (sel : Selection) (o : Occ) : Bool :=
  o.path == sel.path &&
    match sel.stage, o.kind with
    | .edge, .value | .edge, .hole | .pending, .hole | .pending, .insertion | .label, .fieldEnd => true
    | _, _ => false

/-- The selection an occurrence gives when chosen: a value rests; a place
with no value opens, to be typed into. -/
def selectionOf (o : Occ) : Option Selection :=
  let picker : Editing := { text := "", caret := 0, picker := true }
  match o.kind with
  | .value | .label => some { path := o.path }
  | .hole | .insertion => some { path := o.path, stage := .pending, editing := some picker }
  | .fieldEnd => some { path := o.path, stage := .label, editing := some picker }
  | .computed => none

def select (m : Model) (o : Occ) : Model :=
  match selectionOf o with
  | some sel => { m with selection := some sel, typingRun := false }
  | none => m

/-- Where the selection is drawn: its part, and its stop there. -/
def Layout.here (l : Layout) (m : Model) : Option (Nat × Nat) :=
  m.selection.bind fun sel =>
    (List.range l.blocks.length).findSome? fun b =>
      let block := l.blocks[b]!
      if block.selection.isNone then none
      else (block.stops.findIdx? fun s => isSelected sel block.occs[s.occ]!).map (b, ·)

def isPlace (k : OccKind) : Bool := k == .value || k == .hole
def isTabStop (k : OccKind) : Bool := k == .hole || k == .insertion || k == .fieldEnd

/-- The nearest stop after or before a place that `want` accepts, with its
part: in the same part, else in the parts that follow, or come before. From
no place, the first of the document, or the last. -/
def Layout.next (l : Layout) (from_ : Option (Nat × Nat)) (forward : Bool) (want : OccKind → Bool) :
    Option (Block × Stop) :=
  let wanted (block : Block) (keep : Nat → Bool) : List Stop :=
    (List.range block.stops.size).filterMap fun i =>
      let s := block.stops[i]!
      if keep i && want block.occs[s.occ]!.kind then some s else none
  let pick (block : Block) (stops : List Stop) : Option (Block × Stop) :=
    (if forward then stops.head? else stops.getLast?).map (block, ·)
  let others (blocks : List Nat) : Option (Block × Stop) :=
    blocks.findSome? fun b => pick l.blocks[b]! (wanted l.blocks[b]! fun _ => true)
  let all := List.range l.blocks.length
  match from_ with
  | some (b, i) =>
    (pick l.blocks[b]! (wanted l.blocks[b]! fun j => if forward then j > i else j < i)).orElse fun _ =>
      others (if forward then all.filter (· > b) else (all.filter (· < b)).reverse)
  | none => others (if forward then all else all.reverse)

/-- The selection moved to the next or previous thing drawn. -/
def step (laid : Model → Layout) (m : Model) (forward : Bool) (want : OccKind → Bool := isPlace) : Model :=
  let l := laid m
  match l.next (l.here m) forward want with
  | some (block, s) => m.select block.occs[s.occ]!
  | none => if want .insertion then { m with selection := none } else m

/-- The selection moved to the nearest line above or below with something
on it, to what starts nearest the column it's at. -/
def stepLine (laid : Model → Layout) (m : Model) (down : Bool) : Model :=
  let l := laid m
  match l.here m with
  | none => m.step laid true
  | some (b, i) =>
    let here := l.blocks[b]!.stops[i]!
    -- The places of a part, and whether each is past the line left.
    let places (block : Block) (keep : Stop → Bool) : List Stop :=
      block.stops.toList.filter fun s => isPlace block.occs[s.occ]!.kind && keep s
    let away (s : Stop) : Nat := if s.col < here.col then here.col - s.col else s.col - here.col
    let nearest (block : Block) (stops : List Stop) : Option (Block × Stop) :=
      ((if down then stops.head? else stops.getLast?).map fun near =>
        (stops.filter (·.line == near.line)).foldl (fun best s => if away s < away best then s else best) near).map
        (block, ·)
    let all := List.range l.blocks.length
    let target :=
      (nearest l.blocks[b]! (places l.blocks[b]! fun s => if down then s.line > here.line else s.line < here.line)).orElse
        fun _ => (if down then all.filter (· > b) else (all.filter (· < b)).reverse).findSome? fun b' =>
          nearest l.blocks[b']! (places l.blocks[b']! fun _ => true)
    match target with
    | some (block, s) => m.select block.occs[s.occ]!
    | none => m

/-- The scroll that keeps the selection's line in the window. -/
def revealed (l : Layout) (m : Model) : Model :=
  match l.here m with
  | none => m
  | some (b, i) =>
    let top := (l.lineOf b + l.blocks[b]!.stops[i]!.line) * lineHeight
    let room := m.height - 2 * margin
    if top < m.scroll then { m with scroll := top }
    else if top + lineHeight > m.scroll + room then { m with scroll := top + lineHeight - room }
    else m

end Model

end Progred
