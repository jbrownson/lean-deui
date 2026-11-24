import Progred.Editing
import Progred.Entries
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

/-- The editor's state is the model, edited by what changed: something the
view reads, or the rest. -/
abbrev edits : EditStructure := ⟨Model, Model.Edit, Model.Edit.apply⟩

/-- The model, and the document laid out: its parts, edited as a list. -/
abbrev Laid : EditStructure := prod (latest Model) (runs (Lists.editStructure (whole (plain Display.Block))))

/-- A table of definitions. -/
abbrev Cells := Std.TreeMap CellId Value

abbrev cellsEdits : EditStructure := ⟨Cells, Model.CellsEdit, Model.CellsEdit.apply⟩

/-- The model with its definitions, edited by which were written, and the
document's parts, edited by which were: what the model's edits say, sorted
by what they're asked of. -/
abbrev Source : EditStructure :=
  prod (prod (latest Model) (runs cellsEdits)) (runs (Lists.editStructure Entries.Parts))

/-- The parts' edits for a run of the model's, each from the model before it. -/
def source.parts (m : Model) : List Model.Edit → List (Lists.Edit.of Entries.Parts)
  | [] => []
  | e :: t => Entries.edits m e ++ source.parts (e.apply m) t

def source : Inc (runs edits) Source :=
  ⟨fun m => ((m, m.doc.cells), Display.entries m.doc.root),
   fun m es => ((run edits es m, es.flatMap Model.Edit.cells?), source.parts m es)⟩

theorem source_ok : source.ok := by
  intro m es
  have cells : ∀ (es : List Model.Edit) (m : Model),
      run cellsEdits (es.flatMap Model.Edit.cells?) m.doc.cells = (run edits es m).doc.cells := by
    intro es
    induction es with
    | nil => intro m; rfl
    | cons e t ih =>
      intro m
      show run cellsEdits (e.cells? ++ t.flatMap Model.Edit.cells?) m.doc.cells = _
      rw [run_append]
      have step : run cellsEdits e.cells? m.doc.cells = (Model.Edit.apply e m).doc.cells := by
        cases e with
        | rest _ => rfl
        | change c => cases c <;> rfl
      rw [step]
      exact ih _
  have parts : ∀ (es : List Model.Edit) (m : Model),
      Lists.patch Entries.Parts (source.parts m es) (Display.entries m.doc.root) =
        Display.entries (run edits es m).doc.root := by
    intro es
    induction es with
    | nil => intro m; rfl
    | cons e t ih =>
      intro m
      have step : run (Lists.editStructure Entries.Parts) (Entries.edits m e) (Display.entries m.doc.root) =
          Display.entries (e.apply m).doc.root := Entries.edits_ok m e
      exact (run_append (Lists.editStructure Entries.Parts) _ _ _).trans
        ((congrArg (run (Lists.editStructure Entries.Parts) _) step).trans (ih _))
  show (((run edits es m, run cellsEdits (es.flatMap Model.Edit.cells?) m.doc.cells) : Model × Cells),
      Lists.patch Entries.Parts (source.parts m es) (Display.entries m.doc.root)) =
    ((run edits es m, (run edits es m).doc.cells), Display.entries (run edits es m).doc.root)
  rw [cells, parts]
  rfl

/-- A table of definitions, as what gives a cell's. -/
def look (cells : Cells) (c : CellId) : Option Value := cells[c]?

/-- Whether an edit to the definitions touches a part: whether it writes a
cell the part asked for. -/
def writes (item : Display.Item) : Model.CellsEdit → Bool
  | .set c _ => item.reads.contains c
  | .all _ => true

/-- A part that no edit of a run touches is the part it was: each edit
writes a cell the part never asked for. -/
theorem item_untouched (e : Display.Entry) (ces : List Model.CellsEdit) (cells : Cells)
    (h : ces.any (writes (Display.item (look cells) e)) = false) :
    Display.item (look (run cellsEdits ces cells)) e = Display.item (look cells) e := by
  induction ces generalizing cells with
  | nil => rfl
  | cons ce t ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    cases ce with
    | all new => simp [writes] at h
    | set c v =>
      have hc : c ∉ (Display.item (look cells) e).reads := by
        have := h.1
        simpa [writes] using this
      have step : Display.item (look (Model.defined cells c v)) e = Display.item (look cells) e :=
        Display.item_agree (look cells) (look (Model.defined cells c v)) e fun x hx =>
          Model.defined_other cells c v x fun eq => hc (eq ▸ hx)
      have rest := ih (Model.defined cells c v) (by rw [step]; exact h.2)
      show Display.item (look (run cellsEdits t (Model.defined cells c v))) e = _
      rw [rest, step]

/-- The model, its definitions, and the parts with what they reach. -/
abbrev Items : EditStructure :=
  prod (latest (Model × Cells)) (runs (Lists.editStructure (whole (plain Display.Item))))

/-- Each part with what it reaches. An edit to the definitions is asked of
each part, and only one that asked for a cell it writes is worked out
again: writing a definition leaves alone every part that doesn't reach it. -/
def items : Cached Source Items :=
  Cached.carrying (fun (a : Model × Cells) => a)
    (Lists.siftedWhole (cc := prod (latest Model) (runs cellsEdits))
      (fun (a : Model × Cells) entry => Display.item (look a.2) entry)
      (fun (_ : Model × Cells) (d : Model × List Model.CellsEdit) _ item => d.2.any (writes item))
      (fun (_ : Model × Cells) (d : Model × List Model.CellsEdit) => d.2.isEmpty))

theorem items_ok : items.ok :=
  Cached.carrying_ok _ _
    (Lists.siftedWhole_ok _ _ _
      (fun (c : Model × Cells) (d : Model × List Model.CellsEdit) entry h => item_untouched entry d.2 c.2 h)
      (fun (_ : Model × Cells) (d : Model × List Model.CellsEdit) h _ => by
        have : d.2 = [] := List.isEmpty_iff.mp h
        simp [this]))

/-- Each part's input. A change of what the model shows is asked of each
part, and only a part it touches is given a new input: a selection that
moves makes edits at the parts it leaves and enters. -/
def inputs : Cached Items (prod (latest Model) (runs (Lists.editStructure (whole (plain Display.Input))))) :=
  compose (Cached.mapFirst fun (a : Model × Cells) => (a.1, a.1.seen))
    (Cached.carrying (fun (a : Model × Display.Seen) => a.1)
      (Lists.siftedWhole (cc := latest (Model × Display.Seen))
        (fun (a : Model × Display.Seen) item => Display.input a.2 item)
        (fun (a b : Model × Display.Seen) item _ => Display.touched a.2 b.2 item)
        (fun (a b : Model × Display.Seen) => Display.still a.2 b.2)))

theorem inputs_ok : inputs.ok :=
  compose_ok _ _ (Cached.mapFirst_ok _)
    (Cached.carrying_ok _ _
      (Lists.siftedWhole_ok _ _ _
        (fun (c d : Model × Display.Seen) item h => Display.input_of_not_touched c.2 d.2 item h)
        (fun (c d : Model × Display.Seen) h item => Display.not_touched_of_still c.2 d.2 h item)))

/-- A part's layout, of its input. -/
def partInc : Inc (plain Display.Input) (plain Display.Block) := ⟨Display.part, fun _ e => nomatch e⟩

theorem partInc_ok : partInc.ok := fun _ e => nomatch e

/-- The document laid out, as an incremental function of the model: a part
is laid out again only where its input changed. -/
def layout : Cached (runs edits) Laid :=
  compose (compose (compose (cached source) items) inputs)
    (Cached.second (cached (Lists.map.inc (whole.lift partInc))))

theorem layout_ok : layout.ok :=
  compose_ok _ _ (compose_ok _ _ (compose_ok _ _ (cached_ok _ source_ok) items_ok) inputs_ok)
    (Cached.second_ok _ (cached_ok _ (Lists.map_inc_ok _ (whole_lift_ok _ partInc_ok))))

/-- How far the lines' top is above the window's top. -/
def offset (m : Model) : Int := (m.scroll : Int) - Model.margin

/-- The model, and the lines of the document's parts, joined. -/
abbrev Lines : EditStructure := prod (latest Model) (runs (Lists.editStructure (plain Row)))

/-- The parts' lines, joined: a part laid out again has its lines taken out
and its new ones put in. Without a derivative of a part's layout, its lines
are all new. -/
def lines : Cached Laid Lines :=
  Cached.second (cached (Lists.flatBy.inc (cb := whole (plain Display.Block)) rowsOf))

theorem lines_ok : lines.ok :=
  Cached.second_ok _ (cached_ok _ (Lists.flatBy_inc_ok _))

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

/-- How many parts an edit lays out again before the window's lines are
worked out afresh, not edit by edit: an edit that large costs more that way. -/
def manyParts : Nat := 1

/-- The window's lines, whatever its height: a new height shows them anew,
and so does an edit that lays out many parts at once. -/
def rowsLayer : Cached Laid (runs sceneEdits) :=
  keyed (fun (a : Model × List Display.Block) => a.1.height) (fun height => compose lines (window height))
    (fun _ (d : Model × List (Lists.Edit.of (whole (plain Display.Block)))) => decide (d.2.length > manyParts))

theorem rowsLayer_ok : rowsLayer.ok :=
  keyed_ok _ _ _ fun height => compose_ok _ _ lines_ok (window_ok height)

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

/-- The layout of the model an edit is passing through, from what the view
keeps for the one it began from: the edits the model has come to so far
are run through the layout's derivative, and only the parts they touch are
laid out. -/
def relaid (c : view.Cache) (m : Model) : Model.Layout :=
  let kept : layout.Cache × (rowsLayer.Cache × ((Model × List Display.Block) × Nat)) := c
  let made : (Model × List (Lists.Edit.of (whole (plain Display.Block)))) × layout.Cache :=
    layout.df kept.1 m.emitted
  ⟨Lists.patch (whole (plain Display.Block)) made.1.2 kept.2.2.1.2⟩

/-- What the view keeps for a model is the model and its layout. -/
theorem laidOf_view (m : Model) : laidOf (view.f m).2 = (m, Display.blocks m.doc m.seen) := rfl

/-- And the layout it gives of a model passing through is the layout of the
model those edits make, as if worked out from nothing. -/
theorem relaid_view (m m' : Model) : relaid (view.f m).2 m' = Model.Layout.of (run edits m'.emitted m) := by
  have h := congrArg (fun r => r.1.2) (layout_ok m m'.emitted)
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
    | .none => m.change (.select .none)
  | .scroll _ _ _ dy =>
    let lines := here.lineCount
    let most := (lines * Model.lineHeight + 2 * Model.margin) - min m.height (lines * Model.lineHeight + 2 * Model.margin)
    let step := 3 * Model.lineHeight
    m.change (.scroll (if dy > 0 then m.scroll - min m.scroll step else min most (m.scroll + step)))
  | .resize w h => m.change (.size w.toNat h.toNat)
  | _ => m

def app : App.App edits where
  view := view
  respond m scene kept e := (event ⟨(laidOf kept).2⟩ (relaid kept) m.taken scene e).emitted
  settle m kept :=
    if m.reveal then [.rest (Model.revealed ⟨(laidOf kept).2⟩ { m with reveal := false })] else []

end Progred.Editor
