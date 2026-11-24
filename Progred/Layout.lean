import Deui.Fit
import Progred.Gid

/-!
Layout, in characters: text is monospace, so a place is a line and a column.
What's laid out is spans, each with how it looks and the occurrence it
shows, so a click or an arrow key finds its way back. A doc says how spans
may go: side by side, one under another, indented, or the first of two
ways that fits the ribbon; `Deui/Fit.lean` lays it out, and lays it out
again where it changes.
-/

namespace Progred

/-- How a span looks. -/
inductive Face where
  | ink | name | label | string | number | dim | delimiter | result | error
  /-- The caret of a line being typed in: no text, drawn as a bar. -/
  | caret
  deriving DecidableEq, Inhabited, Repr

inductive OccKind where
  /-- A value, where it is drawn. -/
  | value
  /-- A place for a value, with none. -/
  | hole
  /-- A place between a list's elements; its path is where a new element
  would go. -/
  | insertion
  /-- The end of a record, where a field is added; its path is the record's. -/
  | fieldEnd
  /-- A field's label; its path is the field's value's. -/
  | label
  /-- A result: computed, not stored. -/
  | computed
  /-- A place to add an entry of the root notebook: before the entry at its
  path, or at the entries' end for their path. -/
  | entryPoint
  deriving DecidableEq, Inhabited, Repr

/-- Something drawn that can be chosen: where it is in the document, and
what kind of thing. -/
structure Occ where
  path : Path
  kind : OccKind
  /-- Whether an evaluation's error is about this value. -/
  failed : Bool := false
  /-- The cell it is: a value that's a cell, or a label. -/
  cell : Option CellId := none
  deriving DecidableEq, Inhabited

structure Span where
  text : String
  face : Face
  /-- The occurrence it shows, if any. -/
  occ : Option Occ := none
  /-- Whether it's where its occurrence starts: where an arrow key stops
  for it. -/
  start : Bool := false
  deriving DecidableEq, Inhabited

abbrev Doc := Deui.Fit.Doc Span

/-- A line: its indent, and its spans one after another. -/
abbrev Line := Deui.Text.Line Span

/-- A span's width is its characters; `n` columns of nothing are `n` spaces. -/
def measure : Deui.Fit.Measure Span :=
  ⟨fun s => s.text.length, fun n => { text := "".pushn ' ' n, face := .ink }⟩

def t (s : String) (face : Face := .ink) : Doc := .text { text := s, face }
def delim (s : String) : Doc := .text { text := s, face := .delimiter }
def dim (s : String) : Doc := .text { text := s, face := .dim }

/-- Nothing, but a place: an insertion point, or a caret. -/
def point (face : Face) : Doc := .text { text := "", face }

namespace Doc

open Deui.Fit (Doc)

mutual
/-- A doc with its spans that show nothing yet showing `o`, the first of
them marked as where `o` starts, unless one before was. -/
def markFrom (o : Occ) : Deui.Fit.Doc Span → Bool → Deui.Fit.Doc Span × Bool
  | .text s, started =>
    if s.occ.isSome then (.text s, started) else (.text { s with occ := some o, start := !started }, true)
  | .row parts, started =>
    let made := markAll o parts started
    (.row made.1, made.2)
  | .col parts, started =>
    let made := markAll o parts started
    (.col made.1, made.2)
  | .indent n d, started =>
    let made := markFrom o d started
    (.indent n made.1, made.2)
  | .hang n d, started =>
    let made := markFrom o d started
    (.hang n made.1, made.2)
  | .alt flat stacked, started =>
    let a := markFrom o flat started
    let b := markFrom o stacked started
    (.alt a.1 b.1, a.2 || b.2)
  | .slot i, started => (.slot i, started)

def markAll (o : Occ) : List (Deui.Fit.Doc Span) → Bool → List (Deui.Fit.Doc Span) × Bool
  | [], started => ([], started)
  | d :: ds, started =>
    let first := markFrom o d started
    let rest := markAll o ds first.2
    (first.1 :: rest.1, rest.2)
end

/-- A doc, as an occurrence: everything in it shows `o`, unless it shows
something deeper. -/
def marked (o : Occ) (d : Deui.Fit.Doc Span) : Deui.Fit.Doc Span := (markFrom o d false).1

/-- Parts side by side with a separator between them. -/
def sep (separator : Deui.Fit.Doc Span) : List (Deui.Fit.Doc Span) → List (Deui.Fit.Doc Span)
  | [] => []
  | [d] => [d]
  | d :: rest => d :: separator :: sep separator rest

end Doc

/-- A line as plain text, its spans after its indent. -/
def Line.plain (l : Line) : String :=
  l.cells.foldl (fun acc s => acc ++ s.text) ("".pushn ' ' l.indent)

/-- A line's spans, each with the column it starts at. -/
def Line.placed (l : Line) : List (Nat × Span) :=
  let rec go (col : Nat) : List Span → List (Nat × Span)
    | [] => []
    | s :: rest => (col, s) :: go (col + s.text.length) rest
  go l.indent l.cells

end Progred
