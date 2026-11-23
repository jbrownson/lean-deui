import Progred.Display

/-!
The editor's state: the document, the selection, folds, what evaluations
gave, and undo. A write records where the document was, so undo is the
whole state before it. Navigation goes by what's drawn: the occurrences of
the layout, in reading order.
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
  { doc := m.doc, library := m.library, selection := m.selection, folds := m.folds, results := m.results }

def ribbon (m : Model) : Nat := max 30 ((m.width - 2 * margin) / charWidth)

/-- The document laid out, as the window shows it. -/
def laid (m : Model) : Array Line × Array Occ := Display.laid m.shown m.ribbon

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

/-- The value at a path. -/
def at? (m : Model) (path : Path) : Option Value := m.doc.find? m.library path

/-! ## What's drawn, in reading order -/

/-- Where an occurrence is first drawn. -/
structure Stop where
  occ : Nat
  line : Nat
  col : Nat
  /-- Whether it's a place with no width: a point between things. -/
  point : Bool := false
  deriving Inhabited

/-- Each occurrence that's drawn, where it starts, in reading order: by
line, then column; where two start together, a point before a value, and a
container before what it holds. -/
def stops (lines : Array Line) (occs : Array Occ) : Array Stop :=
  let first : Array (Option (Nat × Nat × Bool)) := Id.run do
    let mut first := Array.replicate occs.size none
    for i in [0:lines.size] do
      for span in lines[i]! do
        if span.mark > 0 && span.mark ≤ occs.size then
          if first[span.mark - 1]!.isNone then
            first := first.set! (span.mark - 1) (some (i, span.col, span.text.isEmpty && span.face != .caret))
    return first
  let found := (List.range occs.size).filterMap fun i =>
    first[i]!.map fun (line, col, point) => (⟨i, line, col, point⟩ : Stop)
  found.toArray.qsort fun a b =>
    a.line < b.line || (a.line == b.line && (a.col < b.col ||
      (a.col == b.col && ((a.point && !b.point) || (a.point == b.point && a.occ > b.occ)))))

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

/-- The stop the selection is at, as an index into the stops. -/
def here (m : Model) (occs : Array Occ) (stops : Array Stop) : Option Nat :=
  m.selection.bind fun sel => stops.findIdx? fun s => isSelected sel occs[s.occ]!

/-- The nearest stop before or after an index that `want` accepts. -/
def nextStop (occs : Array Occ) (stops : Array Stop) (from_ : Option Nat) (forward : Bool)
    (want : OccKind → Bool) : Option Stop :=
  let candidates := (List.range stops.size).filter fun i =>
    want occs[stops[i]!.occ]!.kind &&
      match from_ with
      | some at_ => if forward then i > at_ else i < at_
      | none => true
  (if forward then candidates.head? else candidates.getLast?).map (stops[·]!)

def isPlace (k : OccKind) : Bool := k == .value || k == .hole
def isTabStop (k : OccKind) : Bool := k == .hole || k == .insertion || k == .fieldEnd

/-- The selection moved to the next or previous thing drawn. -/
def step (m : Model) (forward : Bool) (want : OccKind → Bool := isPlace) : Model :=
  let (lines, occs) := m.laid
  let stops := stops lines occs
  match nextStop occs stops (m.here occs stops) forward want with
  | some s => m.select occs[s.occ]!
  | none => if want .insertion then { m with selection := none } else m

/-- The selection moved to the first thing on the line above or below. -/
def stepLine (m : Model) (down : Bool) : Model :=
  let (lines, occs) := m.laid
  let stops := stops lines occs
  match m.here occs stops with
  | none => m.step true
  | some at_ =>
    let line := stops[at_]!.line
    let others := stops.toList.filter fun s =>
      isPlace occs[s.occ]!.kind && (if down then s.line > line else s.line < line)
    let target := if down then others.head? else
      -- The first stop of the nearest line above.
      (others.getLast?).bind fun last => others.find? (·.line == last.line)
    match target with
    | some s => m.select occs[s.occ]!
    | none => m

/-- The scroll that keeps the selection's line in the window. -/
def revealed (m : Model) : Model :=
  let (lines, occs) := m.laid
  let stops := stops lines occs
  match m.here occs stops with
  | none => m
  | some at_ =>
    let top := stops[at_]!.line * lineHeight
    let room := m.height - 2 * margin
    if top < m.scroll then { m with scroll := top }
    else if top + lineHeight > m.scroll + room then { m with scroll := top + lineHeight - room }
    else m

end Model

end Progred
