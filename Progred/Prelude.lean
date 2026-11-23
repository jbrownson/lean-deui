import Progred.Builtin

/-!
Skinny's prelude: what a document's code is run against, besides Lean's
own library. It's loaded into the environment the code is elaborated in,
and it's in this program too, so the values the code gives are this
program's values. A layout is a value: a call of a layout function, the
same whether a document holds it or a function gives it.
-/

namespace Progred.Prelude

open Progred Builtin

/-- A call of a function, as a value. -/
def call (function : CellId) (args : List (CellId × Value)) : Value :=
  Value.ofKind Kinds.call ((Kinds.function, .cell function) :: args)

/-- A list, as a value. -/
def items (vs : List Value) : Value := .list ((Position.spread vs.length).zip vs)

def row (children : List Value) : Value := call Layout.row [(Layout.rowChildren, items children)]
def column (children : List Value) : Value := call Layout.column [(Layout.columnChildren, items children)]
def indent (child : Value) : Value := call Layout.indent [(Layout.indentChild, child)]
def either (children : List Value) : Value := call Layout.either [(Layout.eitherChildren, items children)]
def words (content : String) : Value := call Layout.words [(Layout.wordsContent, Value.text content)]
def faint (content : String) : Value := call Layout.faint [(Layout.faintContent, Value.text content)]

/-- The part of the record at a field, drawn in place, given the field's id. -/
def part (label : String) : Value := call Layout.part [(Layout.partField, .cell (cell! label))]

/-- A record's field, given the field's id: an empty record if it has none. -/
def field (v : Value) (label : String) : Value := (v.field? (cell! label)).getD (.record [])

/-- A value as a number: 0 if it isn't one. -/
def number (v : Value) : Float :=
  match v.f64? with
  | some x => x
  | none => ((v.u64?).map (·.toFloat)).getD 0

/-- A value as a whole number: 0 if it isn't a number. -/
def count (v : Value) : Nat :=
  match v.u64? with
  | some n => n
  | none => ((v.f64?).map (·.toUInt64.toNat)).getD 0

/-- A value as text: empty if it isn't text. -/
def content (v : Value) : String := v.text?.getD ""

end Progred.Prelude
