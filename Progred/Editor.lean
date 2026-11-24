import Progred.Editing
import Progred.Entries
import Deui.Redraw
import Deui.Anchored
import Deui.Join
import Deui.Under
import Deui.Drawn

/-!
The editor as a deui app. Its state is the model, and its view is made of
incremental steps, each proved. The model's edits are sorted by what
they're asked of: the definitions, what of the editor's state is drawn,
and the document's parts. Each part keeps its own: what it reaches, its
frames, and how they're laid out; an edit it isn't sensitive to makes
nothing of it. The parts' lines are joined, the window's are found, and
each is a row of the scene: its text, a caret, and a target on each span,
so a click finds what it's on. Under the rows, the selection's wash; over
them, the card of offers for what's being typed.
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

/-- A line's spans that `which` picks, as one wash from the first to the
last. -/
def span (placed : List (Nat × Span)) (which : Span → Bool) (least : Nat) (color : UInt32) : List Scene :=
  match placed.filter fun p => which p.2 with
  | [] => []
  | first :: rest =>
    let stop := (first :: rest).foldl (fun acc p => max acc (p.1 + p.2.text.length)) first.1
    [.fill (x first.1 - 2) 1 (px ((max least (stop - first.1)) * Model.charWidth) + 4) (px Model.lineHeight - 2) color]

/-- One line, as a row's parts, from the row's top left: what an
evaluation's error is about on red, the text, a caret, and a target on
each span that shows something, tagged with where the span is in the line. -/
def lineParts (line : Line) : List Scene :=
  let placed := line.placed
  let errors := span placed (fun s => (s.occ.map (·.failed)).getD false) 0 mistaken
  let texts := placed.filterMap fun (col, s) =>
    if s.text.trimAscii.isEmpty then none else some (Scene.label (x col) 2 textSize (color s.face) s.text)
  let carets := placed.filterMap fun (col, s) =>
    if s.face == .caret then some (Scene.fill (x col - 1) 2 2 (px Model.lineHeight - 4) accent) else none
  let targets := placed.zipIdx.filterMap fun ((col, s), i) =>
    if s.occ.isSome && !s.text.isEmpty then
      some (Scene.target (x col) 0 (px (s.text.length * Model.charWidth)) (px Model.lineHeight) (i + 1).toUInt32)
    else none
  errors ++ texts ++ carets ++ targets

/-- What's washed over the lines: where the selection is, and the cell
it's on. -/
structure Paint where
  selection : Option (Path × Stage)
  marked : Option CellId
  deriving DecidableEq

def paint (m : Model) : Paint := ⟨m.selection.map fun sel => (sel.path, sel.stage), m.selectedCell⟩

/-- A line's washes: the selection's, and a mark on the other places the
selected cell is. -/
def washParts (p : Paint) (line : Line) : List Scene :=
  if p.selection.isNone && p.marked.isNone then []
  else
    let placed := line.placed
    let selected (s : Span) : Bool :=
      match p.selection, s.occ with
      | some (path, stage), some o => Display.covers { path, stage } o
      | _, _ => false
    let others := placed.filterMap fun (col, s) =>
      match s.occ with
      | some o =>
        if !selected s && !s.text.isEmpty && (o.kind == .value || o.kind == .label) && o.cell.isSome &&
            o.cell == p.marked then
          some (Scene.fill (x col - 2) 1 (px (s.text.length * Model.charWidth) + 4) (px Model.lineHeight - 2) same)
        else none
      | none => none
    others ++ span placed selected 1 wash

/-! ## The view -/

def rowHeight (_ : Line) : Nat := Model.lineHeight

def rowScene (line : Line) : Scene := .group 0 0 (lineParts line)

def washScene (p : Paint) (line : Line) : Scene := .group 0 0 (washParts p line)

/-- The editor's state is the model, edited by what changed: something the
view reads, or the rest. -/
abbrev edits : EditStructure := ⟨Model, Model.Edit, Model.Edit.apply⟩

/-- A table of definitions. -/
abbrev Cells := Std.TreeMap CellId Value

abbrev cellsEdits : EditStructure := ⟨Cells, Model.CellsEdit, Model.CellsEdit.apply⟩

/-- What every part is drawn under: what of the editor's state is drawn,
and the definitions, edited by which were written. -/
abbrev Under : EditStructure := prod (latest Display.Seen) (runs cellsEdits)

/-- A line's edits: it's replaced. -/
abbrev LineEdits : EditStructure := whole (plain Line)

/-- A part's lines, edited as a list. -/
abbrev PartLines : EditStructure := runs (Lists.editStructure LineEdits)

/-- The model; what the parts are drawn under; and the document's parts,
edited by which were: what the model's edits say, sorted by what they're
asked of. -/
abbrev Source : EditStructure := prod (latest Model) (prod Under (runs (Lists.editStructure Entries.Parts)))

/-- The parts' edits for a run of the model's, each from the model before it. -/
def source.parts (m : Model) : List Model.Edit → List (Lists.Edit.of Entries.Parts)
  | [] => []
  | e :: t => Entries.edits m e ++ source.parts (e.apply m) t

def source : Inc (runs edits) Source :=
  ⟨fun m => (m, (m.seen, m.doc.cells), Display.entries m.doc.root),
   fun m es => (run edits es m, ((run edits es m).seen, es.flatMap Model.Edit.cells?), source.parts m es)⟩

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
  show ((run edits es m, ((run edits es m).seen, run cellsEdits (es.flatMap Model.Edit.cells?) m.doc.cells),
      Lists.patch Entries.Parts (source.parts m es) (Display.entries m.doc.root)) :
        Model × (Display.Seen × Cells) × List Display.Entry) =
    (run edits es m, ((run edits es m).seen, (run edits es m).doc.cells), Display.entries (run edits es m).doc.root)
  rw [cells, parts]

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

/-! ### A part -/

/-- A part's frames within their ribbon, edited frame by frame. -/
abbrev Framed : EditStructure := prod (latest Nat) (runs (Fit.edits Span))

/-- What a part's frames keep: what they were drawn under, the part, what
it reaches, and all it's drawn from. -/
structure Drawn where
  seen : Display.Seen
  cells : Cells
  entry : Display.Entry
  item : Display.Item
  input : Display.Input

def drawn.f (seen : Display.Seen) (cells : Cells) (entry : Display.Entry) : (Nat × Fit.Frame Span) × Drawn :=
  let item := Display.item (look cells) entry
  let input := Display.input seen item
  ((input.ribbon, Display.frame input), ⟨seen, cells, entry, item, input⟩)

/-- A part's frames after an edit. One that writes no definition the part
asked for, leaves the part as it is, and changes nothing the part is drawn
with, makes no edit; any other has the part's frames grown again. -/
def drawn.df (k : Drawn) (seen : Display.Seen) (ces : List Model.CellsEdit)
    (ees : List (Whole (plain Display.Entry))) : (Nat × List (Fit.Edit Span)) × Drawn :=
  if ees.isEmpty && !ces.any (writes k.item) && !Display.touched k.seen seen k.item then
    ((k.input.ribbon, []), { k with seen, cells := run cellsEdits ces k.cells })
  else
    let made := drawn.f seen (run cellsEdits ces k.cells) (run (whole (plain Display.Entry)) ees k.entry)
    ((made.1.1, [.replace made.1.2]), made.2)

/-- A part's frames, as an incremental function of what it's drawn under
and the part. -/
def drawn : Cached (prod Under Entries.Parts) Framed where
  Cache := Drawn
  f a := drawn.f a.1.1 a.1.2 a.2
  df k d := drawn.df k d.1.1 d.1.2 d.2

theorem drawn_ok : drawn.ok := by
  intro a d
  obtain ⟨⟨seen, cells⟩, entry⟩ := a
  obtain ⟨⟨seen', ces⟩, ees⟩ := d
  show (Framed.apply (drawn.df (drawn.f seen cells entry).2 seen' ces ees).1 (drawn.f seen cells entry).1,
      (drawn.df (drawn.f seen cells entry).2 seen' ces ees).2) =
    drawn.f seen' (run cellsEdits ces cells) (run (whole (plain Display.Entry)) ees entry)
  by_cases h : (ees.isEmpty && !ces.any (writes (Display.item (look cells) entry)) &&
      !Display.touched seen seen' (Display.item (look cells) entry)) = true
  · simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at h
    obtain ⟨⟨he, hc⟩, ht⟩ := h
    subst he
    have hi := item_untouched entry ces cells hc
    have hin := Display.input_of_not_touched seen seen' _ ht
    simp only [drawn.df, drawn.f, List.isEmpty_nil, hc, ht, Bool.not_false, Bool.and_self, ite_true]
    show (((Display.input seen (Display.item (look cells) entry)).ribbon,
        Display.frame (Display.input seen (Display.item (look cells) entry))), _) = _
    simp only [run, hi, hin]
  · have hf : (ees.isEmpty && !ces.any (writes (Display.item (look cells) entry)) &&
        !Display.touched seen seen' (Display.item (look cells) entry)) = false := by simpa using h
    simp only [drawn.df, drawn.f] at hf ⊢
    simp only [hf]
    rfl

/-- A part: its frames, laid out within the ribbon, as lines. -/
def part : Cached (prod Under Entries.Parts) PartLines :=
  compose drawn (compose (Fit.fit measure) (cached (lift Text.rows)))

theorem part_ok : part.ok :=
  compose_ok _ _ drawn_ok (compose_ok _ _ (Fit.fit_ok measure) (cached_ok _ (lift_ok _ Text.rows_ok)))

/-- What a part gives from nothing is its lines. -/
theorem part_lines (seen : Display.Seen) (cells : Cells) (entry : Display.Entry) :
    (part.f ((seen, cells), entry)).1 = Display.part (Display.input seen (Display.item (look cells) entry)) := by
  simp only [part, compose, drawn, drawn.f, Fit.fit, cached, lift, Text.rows, Display.part, id]
  with_reducible_and_instances rfl

/-! ### The parts -/

/-- The model, and the document laid out: each part's lines. -/
abbrev Laid : EditStructure := prod (latest Model) (runs (Lists.editStructure PartLines))

/-- An edit of what the parts are drawn under that changes nothing. -/
def idle (u : Display.Seen × Cells) : Display.Seen × List Model.CellsEdit := (u.1, [])

/-- Whether an edit of what the parts are drawn under changes nothing of
it: then no part is asked. -/
def quiet (u : Display.Seen × Cells) (d : Display.Seen × List Model.CellsEdit) : Bool :=
  Display.still u.1 d.1 && d.2.isEmpty

/-- The document laid out, as an incremental function of the model: each
part is given the edits, and makes of them what it's sensitive to. -/
def layout : Cached (runs edits) Laid :=
  compose (cached source) (Cached.second (Lists.mapUnder part idle quiet))

theorem layout_ok : layout.ok :=
  compose_ok _ _ (cached_ok _ source_ok)
    (Cached.second_ok _ (Lists.mapUnder_ok part idle quiet part_ok (fun _ => rfl)
      (fun u d h x => by
        obtain ⟨seen, cells⟩ := u
        obtain ⟨seen', ces⟩ := d
        simp only [quiet, Bool.and_eq_true, List.isEmpty_iff] at h
        obtain ⟨hs, hc⟩ := h
        have e := Display.eq_of_still seen seen' hs
        subst hc
        show part.f ((seen', cells), x) = part.f ((seen, cells), x)
        rw [e])))

/-- How far the lines' top is above the window's top. -/
def offset (m : Model) : Int := (m.scroll : Int) - Model.margin

/-- The model, and the lines of the document's parts, joined. -/
abbrev Lines : EditStructure := prod (latest Model) (runs (Lists.editStructure LineEdits))

/-- The parts' lines, joined: a line of a part edited is that line of the
whole edited. -/
def lines : Cached Laid Lines := Cached.second (cached (Lists.join LineEdits))

theorem lines_ok : lines.ok := Cached.second_ok _ (cached_ok _ (Lists.join_ok LineEdits))

/-- The lines, at the scroll offset. -/
def placedRows : Inc Lines (runs (Lists.Scrolled.At.edits LineEdits)) :=
  Lists.Scrolled.At.inc LineEdits (Inc.onSecond Inc.identity) (fun (a : Model × List Line) => offset a.1)

/-- The model, and the lines a window shows, placed. -/
abbrev Visible : EditStructure := prod (latest Model) (runs (Drawing.editStructure Line))

/-- The lines a window of a height shows. -/
def visible (height : Nat) : Cached Lines Visible :=
  Cached.carrying (fun (m : Model) => m)
    (compose (cached placedRows)
      (compose (Lists.Scrolled.anchored LineEdits rowHeight)
        (cached (Lists.Scrolled.view.inc LineEdits rowHeight height))))

theorem visible_ok (height : Nat) : (visible height).ok :=
  Cached.carrying_ok _ _
    (compose_ok _ _ (cached_ok _ (Lists.Scrolled.At.inc_ok _ _ _ (Inc.onSecond_ok _ Inc.identity_ok)))
      (compose_ok _ _ (Lists.Scrolled.anchored_ok _ _) (cached_ok _ (Lists.Scrolled.view_inc_ok _ _ _))))

/-- The lines' text, each a row of the scene. -/
def textLayer : Cached Visible (runs sceneEdits) := cached (Inc.onSecond (Drawing.inc rowScene))

/-- The lines' washes, under their text: drawn again when the selection
moves, and else following the lines as the text does. -/
def washLayer : Cached Visible (runs sceneEdits) :=
  keyed (fun (a : Model × List (Placed Line)) => paint a.1)
    (fun p => cached (Inc.onSecond (Drawing.inc (washScene p))))

/-- How many parts an edit lays out again before the window's lines are
worked out afresh, not edit by edit: an edit that large costs more that way. -/
def manyParts : Nat := 8

/-- The window's lines, whatever its height: a new height shows them anew,
and so does an edit of many parts at once. -/
def rowsLayer : Cached Laid (runs sceneEdits) :=
  keyed (fun (a : Model × List (List Line)) => a.1.height)
    (fun height => compose lines (compose (visible height) (layers washLayer textLayer)))
    (fun _ (d : Model × List (Lists.Edit.of PartLines)) => decide (d.2.length > manyParts))

theorem rowsLayer_ok : rowsLayer.ok :=
  keyed_ok _ _ _ fun height =>
    compose_ok _ _ lines_ok
      (compose_ok _ _ (visible_ok height)
        (layers_ok _ _ (keyed_ok _ _ _ fun p => cached_ok _ (Inc.onSecond_ok _ (Drawing.inc_ok (washScene p))))
          (cached_ok _ (Inc.onSecond_ok _ (Drawing.inc_ok rowScene)))))

/-- Where the caret is: its line and column. -/
def caretAt (m : Model) (l : Model.Layout) : Option (Nat × Nat) :=
  m.selection.bind fun sel =>
    (m.partOf sel).bind fun b =>
      (l.parts[b]?).bind fun lines =>
        lines.zipIdx.findSome? fun (line, i) =>
          (line.placed.find? (·.2.face == .caret)).map fun p => (l.lineOf b + i, p.1)

/-- The card of offers, under the caret: up to 8, the chosen one marked. -/
def offersCard (m : Model) (l : Model.Layout) : List Scene :=
  match m.selection.bind (·.editing) with
  | some e =>
    let offers := if e.picker then Model.offers m else []
    if offers.isEmpty then []
    else match caretAt m l with
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
  Redraw.redraw (ca := Laid) fun (a : Model × List (List Line)) => offersCard a.1 ⟨a.2⟩

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
def laidOf (c : view.Cache) : Model × List (List Line) :=
  let kept : layout.Cache × (rowsLayer.Cache × ((Model × List (List Line)) × Nat)) := c
  kept.2.2.1

/-- The layout of the model an edit is passing through, from what the view
keeps for the one it began from: the edits the model has come to so far
are run through the layout's derivative, and only what they touch is laid
out. -/
def relaid (c : view.Cache) (m : Model) : Model.Layout :=
  let kept : layout.Cache × (rowsLayer.Cache × ((Model × List (List Line)) × Nat)) := c
  let made : (Model × List (Lists.Edit.of PartLines)) × layout.Cache := layout.df kept.1 m.emitted
  ⟨Lists.patch PartLines made.1.2 kept.2.2.1.2⟩

/-- What the view keeps for a model is the model and its layout. -/
theorem laidOf_view (m : Model) : laidOf (view.f m).2 = (m, Display.lines m.doc m.seen) := by
  show (m, (Display.entries m.doc.root).map fun x => (part.f ((m.seen, m.doc.cells), x)).1) = _
  simp only [Display.lines, List.map_map]
  exact congrArg (Prod.mk m) (List.map_congr_left fun x _ => part_lines m.seen m.doc.cells x)

/-- And the layout it gives of a model passing through is the layout of the
model those edits make, as if worked out from nothing. -/
theorem relaid_view (m m' : Model) : relaid (view.f m).2 m' = Model.Layout.of (run edits m'.emitted m) := by
  have h := congrArg (fun r => r.1.2) (layout_ok m m'.emitted)
  have e := laidOf_view (run edits m'.emitted m)
  have e2 : (layout.f (run edits m'.emitted m)).1.2 = Display.lines (run edits m'.emitted m).doc
      (run edits m'.emitted m).seen := congrArg Prod.snd e
  exact congrArg (fun ps : List (List Line) => (⟨ps⟩ : Model.Layout)) (h.trans e2)

/-! ## Events -/

/-- What a click does: on an offer, takes it; on a span, selects the
occurrence it shows, found by the line it's on and where it is in it. -/
def clicked (l : Model.Layout) (m : Model) (h : Hit) : Model :=
  if h.tag ≥ Model.offerTag then Model.clickedOffer m (h.tag - Model.offerTag).toNat
  else
    match h.path with
    | 0 :: 0 :: 1 :: row :: _ =>
      -- The window's first row is the line the scroll offset falls in.
      let first := (offset m).toNat / Model.lineHeight
      match l.lineAt (first + row) with
      | some (lines, i) =>
        match ((lines[i]?).bind fun line => line.cells[h.tag.toNat - 1]?).bind (·.occ) with
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
