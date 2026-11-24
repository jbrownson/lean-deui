import Progred.Gid

/-!
The table of definitions, and its edits: one definition written or taken
away, or all of them at once.
-/

namespace Progred.Model

/-- A table of definitions with one written, or taken away. -/
def defined (cells : Std.TreeMap CellId Value) (c : CellId) : Option Value → Std.TreeMap CellId Value
  | some v => cells.insert c v
  | none => cells.erase c

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

end Progred.Model
