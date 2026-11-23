/-!
Layout, in characters: text is monospace, so a place is a line and a column.
A `Doc` says how something may be laid out: pieces side by side, one under
another, indented, and alternatives, the first taken when it fits on the
line within the ribbon, else the second. Laying one out gives lines of
spans, each marked with what it shows, so a click or a selection finds its
way back.
-/

namespace Progred

/-- How a span looks. -/
inductive Face where
  | ink | name | label | string | number | dim | delimiter | result | error
  /-- The caret of a line being typed in: no text, drawn as a bar. -/
  | caret
  deriving BEq, Inhabited, Repr

structure Span where
  col : Nat
  text : String
  face : Face
  /-- What the span shows: an occurrence's number, 0 for none. -/
  mark : Nat
  deriving Inhabited, Repr

def Span.stop (s : Span) : Nat := s.col + s.text.length

abbrev Line := Array Span

inductive Doc where
  | text (s : String) (face : Face)
  /-- Nothing, but a place: an insertion point, or a caret. -/
  | point (face : Face)
  /-- Side by side: each part starts where the one before ended; a part's
  later lines start at the row's base column. -/
  | row (parts : List Doc)
  /-- One under another. -/
  | col (parts : List Doc)
  | indent (n : Nat) (d : Doc)
  /-- `flat` if it's one line and fits the ribbon, else `stacked`. -/
  | alt (flat stacked : Doc)
  /-- Everything inside shows occurrence `id`, unless marked deeper. -/
  | mark (id : Nat) (d : Doc)
  deriving Inhabited

namespace Doc

/-- The width of a doc on one line, if its first choices put it on one. -/
def width? : Doc → Option Nat
  | .text s _ => some s.length
  | .point _ => some 0
  | .row parts => parts.foldlM (fun acc p => (width? p).map (acc + ·)) 0
  | .col [] => some 0
  | .col [d] => width? d
  | .col _ => none
  | .indent n d => (width? d).map (n + ·)
  | .alt flat _ => width? flat
  | .mark _ d => width? d

/-- Where a line ends. -/
def lineStop (start : Nat) (l : Line) : Nat :=
  l.foldl (fun acc s => max acc s.stop) start

/-- A doc's lines: the first from column `first`, later ones from the base
column `col`, marked `mark` unless marked deeper, within a ribbon `ribbon`
columns wide. Never empty: a doc is at least one line. -/
partial def lines (ribbon : Nat) (first col : Nat) (mark : Nat) : Doc → Array Line
  | .text s face => #[#[⟨first, s, face, mark⟩]]
  | .point face => #[#[⟨first, "", face, mark⟩]]
  | .row parts =>
    parts.foldl (fun (acc : Array Line) p =>
      let last := acc.back!
      let next := lines ribbon (lineStop first last) col mark p
      (acc.pop.push (last ++ next[0]!)) ++ next.extract 1 next.size) #[#[]]
  | .col [] => #[#[]]
  | .col (d :: rest) => rest.foldl (fun acc p => acc ++ lines ribbon col col mark p) (lines ribbon first col mark d)
  | .indent n d => lines ribbon (first + n) (col + n) mark d
  | .alt flat stacked =>
    match width? flat with
    | some w => if first + w ≤ ribbon then lines ribbon first col mark flat else lines ribbon first col mark stacked
    | none => lines ribbon first col mark stacked
  | .mark id d => lines ribbon first col id d

/-- Parts side by side with a separator between them. -/
def sep (separator : Doc) : List Doc → List Doc
  | [] => []
  | [d] => [d]
  | d :: rest => d :: separator :: sep separator rest

end Doc

/-- A line as plain text, its spans at their columns. -/
def Line.plain (l : Line) : String :=
  l.foldl (fun acc s => acc.pushn ' ' (s.col - acc.length) ++ s.text) ""

end Progred
