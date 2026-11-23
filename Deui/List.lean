import Deui.Change

/-!
A list's own edits: insert, delete, and update an element in place, as its
elements' edit structure says. Positions count from 0; past the end, an
insert appends, and a delete or an update does nothing.
-/

namespace Deui

/-- `x` put at position `i`; past the end, at the end. -/
def insertAt {α : Type} : List α → Nat → α → List α
  | [], _, x => [x]
  | h :: t, 0, x => x :: h :: t
  | h :: t, i + 1, x => h :: insertAt t i x

/-- The element at position `i` taken out. -/
def removeAt {α : Type} : List α → Nat → List α
  | [], _ => []
  | _ :: t, 0 => t
  | h :: t, i + 1 => h :: removeAt t i

/-- An edit to a list whose elements are edited as `ce` says. -/
inductive ListEdit (ce : EditStructure) where
  | insert (i : Nat) (x : ce.Value)
  | delete (i : Nat)
  | update (i : Nat) (d : ce.Edit)

def ListEdit.apply {ce : EditStructure} : ListEdit ce → List ce.Value → List ce.Value
  | .insert i x, xs => insertAt xs i x
  | .delete i, xs => removeAt xs i
  | .update i d, xs => xs.modify i (ce.apply d)

/-- A list's edit structure, given how its elements are edited. -/
abbrev listEdits (ce : EditStructure) : EditStructure :=
  ⟨List ce.Value, ListEdit ce, ListEdit.apply⟩

end Deui
