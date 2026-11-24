import Progred.Display
import Deui.Lists

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

/-- A change to what the view reads of the editor's state. Each says what
changed, so what's drawn can ask whether it matters to it: a cell's
definition; an entry of the root notebook, written, added or taken away, by
where it is among the entries; the whole root, or the whole document; the
selection; the folds; what evaluations and projections gave; the scroll and
the window's size. -/
inductive Change where
  | cell (c : CellId) (definition : Option Value)
  | entry (i : Nat) (value : Value)
  | entryIn (i : Nat) (position : Position) (value : Value)
  | entryOut (i : Nat)
  | root (r : Option Value)
  | document (d : Document)
  | select (s : Option Selection)
  | folds (fs : List (Path × Bool))
  | results (rs : List (Value × Outcome))
  | layouts (ls : Shared (List (Value × Value × Value)))
  | scroll (n : Nat)
  | size (width height : Nat)

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
  /-- The changes made since the model was last taken up, latest first:
  what its edits are. What the view reads is changed only by `change`,
  which notes each here. -/
  log : List Change := []
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

/-! ## Changes

What the view reads of a model is changed by a `Change`, which the model
notes; the rest is set freely. A model's edits are the changes it noted,
then the rest: so the state the app holds, which is those edits applied, is
the model the handler made. -/

/-- A table of definitions with one written, or taken away. -/
def defined (cells : Std.TreeMap CellId Value) (c : CellId) : Option Value → Std.TreeMap CellId Value
  | some v => cells.insert c v
  | none => cells.erase c

/-- Entries with the value of the one at `i` replaced. -/
def replaceAt : List (Position × Value) → Nat → Value → List (Position × Value)
  | [], _, _ => []
  | (p, _) :: t, 0, v => (p, v) :: t
  | h :: t, i + 1, v => h :: replaceAt t i v

/-- A root notebook with its entries replaced. -/
def withEntries (root : Option Value) (items : List (Position × Value)) : Option Value :=
  match root with
  | some (.record fields) =>
    some (.record (fields.map fun f => if f.1 == Kinds.entries then (f.1, Value.list items) else f))
  | other => other

/-- The root after a change to its notebook's entries, if it's a notebook. -/
def entriesChanged (root : Option Value) (f : List (Position × Value) → List (Position × Value)) : Option Value :=
  match Display.notebookEntries? root with
  | some items => withEntries root (f items)
  | none => root

def _root_.Progred.Change.apply : Change → Model → Model
  | .cell c v, m => { m with doc := { m.doc with cells := defined m.doc.cells c v } }
  | .entry i v, m =>
    { m with doc := { m.doc with root := entriesChanged m.doc.root (fun items => replaceAt items i v) } }
  | .entryIn i p v, m =>
    { m with doc := { m.doc with
        root := entriesChanged m.doc.root (fun items => Deui.Lists.insert items (min i items.length) (p, v)) } }
  | .entryOut i, m =>
    { m with doc := { m.doc with root := entriesChanged m.doc.root (fun items => Deui.Lists.remove items i) } }
  | .root r, m => { m with doc := { m.doc with root := r } }
  | .document d, m => { m with doc := d }
  | .select s, m => { m with selection := s }
  | .folds fs, m => { m with folds := fs }
  | .results rs, m => { m with results := rs }
  | .layouts ls, m => { m with layouts := ls }
  | .scroll n, m => { m with scroll := n }
  | .size w h, m => { m with width := w, height := h }

/-- The model changed, the change noted. -/
def change (m : Model) (c : Change) : Model := { c.apply m with log := c :: m.log }

/-- An edit of the model: a change to what the view reads, or the rest of
it, which is all the view doesn't read. -/
inductive Edit where
  | change (c : Change)
  | rest (m : Model)

def Edit.apply : Edit → Model → Model
  | .change c, m => c.apply m
  | .rest new, m =>
    { new with doc := m.doc, selection := m.selection, folds := m.folds, results := m.results,
               layouts := m.layouts, scroll := m.scroll, width := m.width, height := m.height, log := [] }

/-- The model taken up to be changed: nothing noted yet. -/
def taken (m : Model) : Model := { m with log := [] }

/-- The edits that a model changed from one taken up comes to: the changes
it noted, in order, then the rest. -/
def emitted (m : Model) : List Edit := m.log.reverse.map .change ++ [.rest m.taken]

/-- The changes that a document written at a path comes to: where the write
landed says which. In a cell, the cell's definition. In an entry of the root
notebook, that entry, written, added or taken away. Elsewhere under the
root, the root. With no path, or one that leads nowhere, the document. -/
def written (old new : Document) (at_ : Option Path) : List Change :=
  match at_.bind old.location? with
  | none => [.document new]
  | some ⟨.cell c, _⟩ => [.cell c new.cells[c]?]
  | some ⟨.root, steps⟩ =>
    match steps, Display.notebookEntries? old.root, Display.notebookEntries? new.root with
    | .key k :: .element p :: _, some was, some now =>
      if k == Kinds.entries then
        match was.findIdx? (·.1 == p), now.findIdx? (·.1 == p), (now.find? (·.1 == p)).map (·.2) with
        | some i, some _, some v => [.entry i v]
        | none, some j, some v => [.entryIn j p v]
        | some i, none, _ => [.entryOut i]
        | _, _, _ => [.root new.root]
      else [.root new.root]
    | _, _, _ => [.root new.root]

/-- The model with a new document: an undo step, unless it joins a run of
typing. `at_` is the path the document was written at, and `also` are cells
written besides. -/
def write (m : Model) (doc : Document) (typing : Bool := false) (at_ : Option Path := none)
    (also : List CellId := []) : Model :=
  let changes := (also.map fun c => Change.cell c doc.cells[c]?) ++ written m.doc doc at_
  let m' := changes.foldl change m
  { m' with
    redo := [], stale := true, dirty := true, typingRun := typing,
    undo := if typing && m.typingRun then m.undo else m.snapshot :: m.undo }

def restore (m : Model) (s : Snapshot) : Model :=
  { ((m.change (.document s.doc)).change (.select (s.selection.map ({ path := · })))).change (.folds s.folds) with
    stale := true, dirty := true, typingRun := false }

/-- Writing one cell's definition leaves every other cell's as it was. -/
theorem defined_other (cells : Std.TreeMap CellId Value) (c : CellId) (v : Option Value) (x : CellId)
    (h : x ≠ c) : (defined cells c v)[x]? = cells[x]? := by
  have ne : compare c x ≠ .eq := fun e => h (Std.LawfulEqCmp.eq_of_compare e).symm
  cases v with
  | some v => simp only [defined, Std.TreeMap.getElem?_insert, ne, ite_false]
  | none => simp only [defined, Std.TreeMap.getElem?_erase, ne, ite_false]

/-- A table of definitions' edits: one definition, or all. -/
inductive CellsEdit where
  | set (c : CellId) (definition : Option Value)
  | all (cells : Std.TreeMap CellId Value)

def CellsEdit.apply : CellsEdit → Std.TreeMap CellId Value → Std.TreeMap CellId Value
  | .set c v, cells => defined cells c v
  | .all new, _ => new

/-- What a model's edit does to its definitions. -/
def Edit.cells? : Edit → List CellsEdit
  | .change (.cell c v) => [.set c v]
  | .change (.document d) => [.all d.cells]
  | _ => []

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
  | .computed | .entryPoint => none

/-- The positions of the root notebook's entries, in order. -/
def entryPositions (m : Model) : List Position :=
  ((Display.notebookEntries? m.doc.root).getD []).map (·.1)

/-- Where an entry being added at a path is anchored, if the path is among
the root notebook's entries: the entry it's before, or the entries' end. -/
def anchorFor (m : Model) (path : Path) : Option Path :=
  if path.dropLast == Display.entriesPath then
    match path.getLast? with
    | some (.element p) =>
      some (((m.entryPositions.find? fun q => Position.lt p q).map Display.entryAt).getD Display.entriesPath)
    | _ => none
  else none

def select (m : Model) (o : Occ) : Model :=
  match o.kind with
  | .entryPoint =>
    -- A place to add an entry: its position is between the entry before
    -- and the one it's before, or after the last.
    let positions := m.entryPositions
    let new : Position :=
      match o.path.getLast? with
      | some (.element q) => Position.between ((positions.takeWhile fun p => Position.lt p q).getLast?) (some q)
      | _ => Position.between positions.getLast? none
    { m.change (.select (some { path := Display.entriesPath ++ [.element new], stage := .pending,
                                editing := some { text := "", caret := 0, picker := true }, anchor := some o.path })) with
      typingRun := false }
  | _ =>
    match selectionOf o with
    | some sel => { m.change (.select (some sel)) with typingRun := false }
    | none => m

/-- Where the selection is drawn: its part, and its stop there. -/
def Layout.here (l : Layout) (m : Model) : Option (Nat × Nat) :=
  m.selection.bind fun sel =>
    l.blocks.zipIdx.findSome? fun (block, b) =>
      if block.selection.isNone then none
      else (block.stops.findIdx? fun s => isSelected sel block.occs[s.occ]!).map (b, ·)

def isPlace (k : OccKind) : Bool := k == .value || k == .hole
def isTabStop (k : OccKind) : Bool := k == .hole || k == .insertion || k == .fieldEnd || k == .entryPoint

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
  -- The first of the parts that has one, in the order they're given.
  let others (blocks : List Block) : Option (Block × Stop) :=
    blocks.findSome? fun block => pick block (wanted block fun _ => true)
  match from_ with
  | some (b, i) =>
    ((l.blocks[b]?).bind fun block => pick block (wanted block fun j => if forward then j > i else j < i)).orElse
      fun _ => others (if forward then l.blocks.drop (b + 1) else (l.blocks.take b).reverse)
  | none => others (if forward then l.blocks else l.blocks.reverse)

/-- The selection moved to the next or previous thing drawn. -/
def step (laid : Model → Layout) (m : Model) (forward : Bool) (want : OccKind → Bool := isPlace) : Model :=
  let l := laid m
  match l.next (l.here m) forward want with
  | some (block, s) => m.select block.occs[s.occ]!
  | none => if want .insertion then m.change (.select none) else m

/-- The selection moved to the nearest line above or below with something
on it, to what starts nearest the column it's at. -/
def stepLine (laid : Model → Layout) (m : Model) (down : Bool) : Model :=
  let l := laid m
  match l.here m with
  | none => m.step laid true
  | some (b, i) =>
    match l.blocks[b]? with
    | none => m
    | some block =>
      let here := block.stops[i]!
      -- The places of a part, among those `keep` accepts.
      let places (block : Block) (keep : Stop → Bool) : List Stop :=
        block.stops.toList.filter fun s => isPlace block.occs[s.occ]!.kind && keep s
      let away (s : Stop) : Nat := if s.col < here.col then here.col - s.col else s.col - here.col
      let nearest (block : Block) (stops : List Stop) : Option (Block × Stop) :=
        ((if down then stops.head? else stops.getLast?).map fun near =>
          (stops.filter (·.line == near.line)).foldl (fun best s => if away s < away best then s else best) near).map
          (block, ·)
      let target :=
        (nearest block (places block fun s => if down then s.line > here.line else s.line < here.line)).orElse
          fun _ => (if down then l.blocks.drop (b + 1) else (l.blocks.take b).reverse).findSome? fun other =>
            nearest other (places other fun _ => true)
      match target with
      | some (block, s) => m.select block.occs[s.occ]!
      | none => m

/-- The scroll that keeps the selection's line in the window. -/
def revealed (l : Layout) (m : Model) : Model :=
  match l.here m with
  | none => m
  | some (b, i) =>
    let top := (l.lineOf b + ((l.blocks[b]?).map (·.stops[i]!.line)).getD 0) * lineHeight
    let room := m.height - 2 * margin
    if top < m.scroll then m.change (.scroll top)
    else if top + lineHeight > m.scroll + room then m.change (.scroll (top + lineHeight - room))
    else m

end Model

end Progred
