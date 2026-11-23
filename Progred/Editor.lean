import Progred.Editing
import Deui.Redraw
import Deui.Anchored
import Deui.Flatten
import Deui.Drawn
import Deui.Sift

/-!
The editor as a deui app. Its state is the model, and its view is made of
incremental steps, each proved: the document's parts, kept while the
document is; each part's input, compared with what it was; each part laid
out where its input changed; the parts' lines joined, at the scroll offset;
the window's lines; and each line a row of the scene: the selection's wash,
a mark on the other places the selected cell is, the text, a caret, and a
target on each span, tagged with its occurrence, so a click finds what it's
on. Over them, the card of offers for what's being typed. An edit lays out
the entries it touches and changes the rows that differ; the rest is as it
was.
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

/-- One line, as a row's parts, from the row's top left. -/
def lineParts (line : Array Display.Piece) : List Scene :=
  let stopOf (s : Display.Piece) : Nat := s.col + s.text.length
  -- A wash behind the pieces that `which` picks, from the first to the last.
  let span (which : Display.Piece → Bool) (least : Nat) (color : UInt32) : List Scene :=
    match line.toList.filter which with
    | [] => []
    | first :: rest =>
      let stop := (first :: rest).foldl (fun acc s => max acc (stopOf s)) first.col
      [.fill (x first.col - 2) 1 (px ((max least (stop - first.col)) * Model.charWidth) + 4) (px Model.lineHeight - 2) color]
  let washes := span (·.selected) 1 wash
  -- What an evaluation's error is about, on red.
  let errors := span (·.failed) 0 mistaken
  -- The other places the selected cell is, marked.
  let others := line.toList.filterMap fun s =>
    if s.other then
      some (Scene.fill (x s.col - 2) 1 (px (s.text.length * Model.charWidth) + 4) (px Model.lineHeight - 2) same)
    else none
  let texts := line.toList.filterMap fun s =>
    if s.text.isEmpty then none else some (Scene.label (x s.col) 2 textSize (color s.face) s.text)
  let carets := line.toList.filterMap fun s =>
    if s.face == .caret then some (Scene.fill (x s.col - 1) 2 2 (px Model.lineHeight - 4) accent) else none
  let targets := line.toList.filterMap fun s =>
    if s.mark > 0 && !s.text.isEmpty then
      some (Scene.target (x s.col) 0 (px (s.text.length * Model.charWidth)) (px Model.lineHeight) s.mark.toUInt32)
    else none
  errors ++ others ++ washes ++ texts ++ carets ++ targets

/-! ## The view -/

abbrev Row := Display.Row

def rowsOf (b : Display.Block) : List Row := b.rows

def rowHeight (_ : Row) : Nat := Model.lineHeight

def rowScene (r : Row) : Scene := .group 0 0 (lineParts r.val)

/-- The editor's state is the model, replaced whole. -/
abbrev edits : EditStructure := whole (plain Model)

/-- The model, and the document laid out: its parts, edited as a list. -/
abbrev Laid : EditStructure := prod (latest Model) (runs (Lists.editStructure (whole (plain Display.Block))))

/-- Whether two models hold the same definitions: at once if they're the
one object, as they are unless an edit wrote to a definition. -/
def sameCells (a b : Model) : Bool :=
  withPtrEq a.doc.cells b.doc.cells (fun _ => decide (a.doc.cells.toList = b.doc.cells.toList))
    (by intro h; simp [h])

/-- The document's definitions in order, kept while they're the same. -/
def cells : Cached (runs edits) (latest (Model × Display.Cells)) :=
  memo (ca := runs edits) (fun m => Display.Cells.of m.doc) sameCells

theorem cells_ok : cells.ok :=
  memo_ok _ _ fun a b h => by
    have e : a.doc.cells.toList = b.doc.cells.toList := of_decide_eq_true h
    show (⟨a.doc.cells.toList.toArray⟩ : Display.Cells) = ⟨b.doc.cells.toList.toArray⟩
    rw [e]

/-- The model, the definitions, and what each part is worked out from. -/
abbrev Keys : EditStructure := latest ((Model × Display.Cells) × List Display.ItemKey)

/-- What each part is worked out from, kept while the root and the
definitions are the same. -/
def keysKept : Cached (latest (Model × Display.Cells)) Keys :=
  memo (ca := latest (Model × Display.Cells)) (fun a => Display.itemKeys a.1.doc.root a.2)
    (fun a b => decide (a.1.doc.root = b.1.doc.root ∧ a.2 = b.2))

theorem keysKept_ok : keysKept.ok :=
  memo_ok _ _ fun a b h => by
    have e : a.1.doc.root = b.1.doc.root ∧ a.2 = b.2 := of_decide_eq_true h
    show Display.itemKeys a.1.doc.root a.2 = Display.itemKeys b.1.doc.root b.2
    rw [e.1, e.2]

/-- And as edits to the list of them: an entry whose value and the
definitions are as they were is no edit. -/
def keys : Cached Keys (prod (latest (Model × Display.Cells)) (runs (Lists.editStructure (plain Display.ItemKey)))) :=
  tracked (ca := Keys) (fun (a : (Model × Display.Cells) × List Display.ItemKey) => a.1)
    (fun (a : (Model × Display.Cells) × List Display.ItemKey) => a.2) equal equal_refl

theorem keys_ok : keys.ok := tracked_ok _ _ _ _ equal_sound

/-- A part with what it reaches, of what it's worked out from. -/
def itemInc : Inc (plain Display.ItemKey) (plain Display.Item) := ⟨Display.item, fun _ e => nomatch e⟩

theorem itemInc_ok : itemInc.ok := fun _ e => nomatch e

/-- The model, the definitions, and the parts with what they reach. -/
abbrev Items : EditStructure :=
  prod (latest (Model × Display.Cells)) (runs (Lists.editStructure (plain Display.Item)))

/-- The model, the parts' items, and the parts. -/
abbrev Frames : EditStructure :=
  latest (((Model × Display.Cells) × List Display.Item) × List Display.Frame)

/-- The parts, kept while the items are the same and no entry is being
added, or the same one is. -/
def framesKept : Cached Items Frames :=
  memo (ca := Items)
    (fun (a : (Model × Display.Cells) × List Display.Item) =>
      Display.frames a.2 (Display.pendingEntry a.1.1.selection))
    (fun (a b : (Model × Display.Cells) × List Display.Item) =>
      Lists.alike (A := Display.Item) equal equal_refl a.2 b.2 &&
        decide (Display.pendingEntry a.1.1.selection = Display.pendingEntry b.1.1.selection))

theorem framesKept_ok : framesKept.ok :=
  memo_ok _ _ fun a b h => by
    simp only [Bool.and_eq_true] at h
    have e1 : a.2 = b.2 := Lists.alike_sound (A := Display.Item) equal equal_refl equal_sound _ _ h.1
    have e2 : Display.pendingEntry a.1.1.selection = Display.pendingEntry b.1.1.selection := of_decide_eq_true h.2
    show Display.frames a.2 (Display.pendingEntry a.1.1.selection) =
      Display.frames b.2 (Display.pendingEntry b.1.1.selection)
    rw [e1, e2]

/-- The model with what the parts are drawn with, and the parts, edited as
a list. -/
abbrev Parts : EditStructure :=
  prod (latest (Model × Display.Seen)) (runs (Lists.editStructure (plain Display.Frame)))

/-- The parts as edits to the list of them, with what of the model they're
drawn with worked out once. -/
def frames : Cached Frames Parts :=
  tracked (ca := Frames)
    (fun (a : ((Model × Display.Cells) × List Display.Item) × List Display.Frame) => (a.1.1.1, a.1.1.1.seen))
    (fun (a : ((Model × Display.Cells) × List Display.Item) × List Display.Frame) => a.2) equal equal_refl

theorem frames_ok : frames.ok := tracked_ok _ _ _ _ equal_sound

/-- Each part's input. A change of the model is asked of each part, and
only a part it touches is given a new input: a selection that moves makes
edits at the parts it leaves and enters. -/
def inputs : Cached Parts (prod (latest Model) (runs (Lists.editStructure (whole (plain Display.Input))))) :=
  Cached.carrying (fun (a : Model × Display.Seen) => a.1)
    (Lists.sifted (cc := latest (Model × Display.Seen)) (fun (a : Model × Display.Seen) frame => Display.input a.2 frame)
      (fun (a b : Model × Display.Seen) frame _ => Display.touched a.2 b.2 frame)
      (fun (a b : Model × Display.Seen) => Display.still a.2 b.2))

theorem inputs_ok : inputs.ok :=
  Cached.carrying_ok _ _
    (Lists.sifted_ok _ _ _
      (fun (c d : Model × Display.Seen) frame h => Display.input_of_not_touched c.2 d.2 frame h)
      (fun (c d : Model × Display.Seen) h frame => Display.not_touched_of_still c.2 d.2 h frame))

/-- A part's layout, of its input. -/
def partInc : Inc (plain Display.Input) (plain Display.Block) := ⟨Display.part, fun _ e => nomatch e⟩

theorem partInc_ok : partInc.ok := fun _ e => nomatch e

/-- The document laid out, as an incremental function of the model: a part
is laid out again only where its input changed. -/
def layout : Cached (runs edits) Laid :=
  compose
    (compose
      (compose
        (compose (compose (compose (compose cells keysKept) keys) (Cached.second (cached (Lists.map.inc itemInc))))
          framesKept)
        frames)
      inputs)
    (Cached.second (cached (Lists.map.inc (whole.lift partInc))))

theorem layout_ok : layout.ok :=
  compose_ok _ _
    (compose_ok _ _
      (compose_ok _ _
        (compose_ok _ _
          (compose_ok _ _ (compose_ok _ _ (compose_ok _ _ cells_ok keysKept_ok) keys_ok)
            (Cached.second_ok _ (cached_ok _ (Lists.map_inc_ok _ itemInc_ok))))
          framesKept_ok)
        frames_ok)
      inputs_ok)
    (Cached.second_ok _ (cached_ok _ (Lists.map_inc_ok _ (whole_lift_ok _ partInc_ok))))

/-- How far the lines' top is above the window's top. -/
def offset (m : Model) : Int := (m.scroll : Int) - Model.margin

/-- The model, and the lines of the document's parts, joined. -/
abbrev Lines : EditStructure := prod (latest Model) (runs (Lists.editStructure (plain Row)))

/-- The parts' lines, joined: where a part was laid out again, only the
lines that differ from what they were are edits. -/
def lines : Cached Laid Lines :=
  Cached.second
    (Lists.flatChange (cb := whole (plain Display.Block)) rowsOf Display.Block.same Display.Block.same_refl
      fun a b => decide (a = b))

theorem lines_ok : lines.ok :=
  Cached.second_ok _ (Lists.flatChange_ok _ _ _ _ Display.Block.same_sound fun _ _ h => of_decide_eq_true h)

/-- The lines, at the scroll offset. -/
def placedRows : Inc Lines (runs (Lists.Scrolled.At.edits (plain Row))) :=
  Lists.Scrolled.At.inc (plain Row) (Inc.onSecond Inc.identity) (fun (a : Model × List Row) => offset a.1)

/-- The lines a window of a height shows, on the screen. -/
def window (height : Nat) : Cached Lines (runs sceneEdits) :=
  compose (cached placedRows)
    (compose (Lists.Scrolled.anchored (plain Row) rowHeight)
      (compose (cached (Lists.Scrolled.view.inc (plain Row) rowHeight height)) (cached (Drawing.inc rowScene))))

theorem window_ok (height : Nat) : (window height).ok :=
  compose_ok _ _ (cached_ok _ (Lists.Scrolled.At.inc_ok _ _ _ (Inc.onSecond_ok _ Inc.identity_ok)))
    (compose_ok _ _ (Lists.Scrolled.anchored_ok _ _)
      (compose_ok _ _ (cached_ok _ (Lists.Scrolled.view_inc_ok _ _ _)) (cached_ok _ (Drawing.inc_ok rowScene))))

/-- The window's lines, whatever its height: a new height shows them anew. -/
def rowsLayer : Cached Laid (runs sceneEdits) :=
  compose lines (keyed (fun (a : Model × List Row) => a.1.height) window)

theorem rowsLayer_ok : rowsLayer.ok :=
  compose_ok _ _ lines_ok (keyed_ok _ _ window_ok)

/-- Where the caret is: its line and column. -/
def caretAt (l : Model.Layout) : Option (Nat × Nat) :=
  l.blocks.zipIdx.findSome? fun (block, b) =>
    if block.selection.isNone then none
    else (List.range block.lines.size).findSome? fun i =>
      (block.lines[i]!.toList.find? (·.face == .caret)).map fun s => (l.lineOf b + i, s.col)

/-- The card of offers, under the caret: up to 8, the chosen one marked. -/
def offersCard (m : Model) (l : Model.Layout) : List Scene :=
  match m.selection.bind (·.editing) with
  | some e =>
    let offers := if e.picker then Model.offers m else []
    if offers.isEmpty then []
    else match caretAt l with
      | some (line, col) =>
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
      | none => []
  | none => []

/-- The card of offers, drawn again whenever anything changes: it's small. -/
def cardLayer : Cached Laid (runs sceneEdits) :=
  Redraw.redraw (ca := Laid) fun (a : Model × List Display.Block) => offersCard a.1 ⟨a.2⟩

/-- The view: the document laid out, its window's lines, and the card over
them. -/
def view : Cached (runs edits) (runs sceneEdits) :=
  compose layout (layers rowsLayer cardLayer)

/-- The view's derivative is correct: its scene edits take the scene on
screen to the view of the edited model. -/
theorem view_ok : view.ok :=
  compose_ok _ _ layout_ok (layers_ok _ _ rowsLayer_ok (Redraw.redraw_ok _))

/-! ## What the view keeps -/

/-- The model and its layout, as the view keeps them. -/
def laidOf (c : view.Cache) : Model × List Display.Block :=
  let kept : layout.Cache × (rowsLayer.Cache × ((Model × List Display.Block) × Nat)) := c
  kept.2.2.1

/-- The layout of another model, from what the view keeps for this one:
only the parts whose inputs differ are laid out. -/
def relaid (c : view.Cache) (m : Model) : Model.Layout :=
  let kept : layout.Cache × (rowsLayer.Cache × ((Model × List Display.Block) × Nat)) := c
  let made : (Model × List (Lists.Edit.of (whole (plain Display.Block)))) × layout.Cache :=
    layout.df kept.1 [.replace m]
  ⟨Lists.patch (whole (plain Display.Block)) made.1.2 kept.2.2.1.2⟩

/-- What the view keeps for a model is the model and its layout. -/
theorem laidOf_view (m : Model) : laidOf (view.f m).2 = (m, Display.blocks m.doc m.seen) := rfl

/-- And the layout it gives of another model is that model's layout, as if
worked out from nothing. -/
theorem relaid_view (m m' : Model) : relaid (view.f m).2 m' = Model.Layout.of m' := by
  have h := congrArg (fun r => r.1.2) (layout_ok m [.replace m'])
  exact congrArg (fun bs : List Display.Block => (⟨bs⟩ : Model.Layout)) h

/-! ## Events -/

/-- What a click does: on an offer, takes it; on a span, selects the
occurrence it's marked with, found in the part of the line it's on. -/
def clicked (l : Model.Layout) (m : Model) (h : Hit) : Model :=
  if h.tag ≥ Model.offerTag then Model.clickedOffer m (h.tag - Model.offerTag).toNat
  else
    match h.path with
    | 0 :: 0 :: row :: _ =>
      -- The window's first row is the line the scroll offset falls in.
      let first := (offset m).toNat / Model.lineHeight
      match l.lineAt (first + row) with
      | some (block, _) =>
        match block.occs[h.tag.toNat - 1]? with
        | some o => if h.tag == 0 then m else m.select o
        | none => m
      | none => m
    | _ => m

/-- What an event does to the model, given its layout, and the layout of
any model. -/
def event (here : Model.Layout) (laid : Model → Model.Layout) (m : Model) (scene : Scene) : App.Event → Model
  | .text t => { t.foldl Model.typed m with reveal := true }
  | .key code true mods => { Model.key laid m code mods with reveal := true }
  | .press px_ py 0 true =>
    match scene.hit (App.coordinate px_) (App.coordinate py) with
    | some h => clicked here m h
    | .none => { m with selection := .none }
  | .scroll _ _ _ dy =>
    let lines := here.lineCount
    let most := (lines * Model.lineHeight + 2 * Model.margin) - min m.height (lines * Model.lineHeight + 2 * Model.margin)
    let step := 3 * Model.lineHeight
    { m with scroll := if dy > 0 then m.scroll - min m.scroll step else min most (m.scroll + step) }
  | .resize w h => { m with width := w.toNat, height := h.toNat }
  | _ => m

def app : App.App edits where
  view := view
  respond m scene kept e := [.replace (event ⟨(laidOf kept).2⟩ (relaid kept) m scene e)]
  settle m kept :=
    if m.reveal then [.replace (Model.revealed ⟨(laidOf kept).2⟩ { m with reveal := false })] else []

end Progred.Editor
