import Deui.Scene

/-!
A column: rows stacked from the top, each as tall as it says. Its derivative
turns an edit to the rows into a few edits to the column's scene, without
laying the column out again.
-/

namespace Deui.Column

open Deui

/-- A row: how tall it is, and what's in it, drawn from the row's top. -/
structure Row where
  h : Int32
  s : Scene

/-- Rows are replaced whole; the rows change as a list does. -/
abbrev rowEdits : EditStructure := whole (plain Row)
abbrev rowsEdits : EditStructure := Lists.editStructure rowEdits

/-- A row at `y`: its scene, in a group placed at the row's top. -/
def placed (y : Int32) (s : Scene) : Scene := .group 0 y [s]

/-- The rows placed from `y` down, each below the one before. -/
def place : List Row → Int32 → List Scene
  | [], _ => []
  | r :: t, y => placed y r.s :: place t (y + r.h)

/-- The column's scene. -/
def view (rows : List Row) : Scene := .group 0 0 (place rows 0)

/-- Where the row at position `i` starts, the rows placed from `y`; past the
end, where the column ends. -/
def top : List Row → Nat → Int32 → Int32
  | [], _, y => y
  | _ :: _, 0, y => y
  | r :: t, i + 1, y => top t i (y + r.h)

/-- How tall the row at position `i` is; past the end, nothing. -/
def height : List Row → Nat → Int32
  | [], _ => 0
  | r :: _, 0 => r.h
  | _ :: t, i + 1 => height t i

/-- The edits inserting a row at `i` makes: the row, placed where it goes,
and the rows after it moved down by its height. -/
def insertEdits (rows : List Row) (i : Nat) (r : Row) : List SceneEdit :=
  [.insert i (placed (top rows i 0) r.s), .shift (i + 1) 0 r.h]

/-- The edits deleting the row at `i` makes: the row goes, and the rows
after it move up by its height. -/
def deleteEdits (rows : List Row) (i : Nat) : List SceneEdit :=
  [.delete i, .shift i 0 (0 - height rows i)]

/-- The edits replacing the row at `i` makes, if there's a row there: with
one as tall, the row goes and the new one goes where it was, the rows after
it staying where they are; with one of another height, deleting it and
inserting the new one. Past the end, nothing. -/
def replaceEdits (rows : List Row) (i : Nat) (r : Row) : List SceneEdit :=
  if i < rows.length then
    if height rows i = r.h then [.delete i, .insert i (placed (top rows i 0) r.s)]
    else deleteEdits rows i ++ insertEdits (Lists.remove rows i) i r
  else []

/-- The edits one edit to the rows makes to the column's scene. -/
def edit (rows : List Row) : Lists.Edit.of rowEdits → List SceneEdit
  | .insert i r => insertEdits rows i r
  | .delete i => deleteEdits rows i
  | .update i (.replace r) => replaceEdits rows i r
  | .update _ (.apply e) => nomatch e

/-- The column, for one edit at a time. -/
def one : Inc rowsEdits (runs sceneEdits) := ⟨view, edit⟩

/-- The column, for runs of edits. -/
def inc : Inc (runs rowsEdits) (runs sceneEdits) := lift one

/-! ## Proofs -/

theorem add_right_comm (a b c : Int32) : a + b + c = a + c + b := by
  rw [Int32.add_assoc, Int32.add_comm b, ← Int32.add_assoc]

theorem add_sub_cancel' (a b : Int32) : a + b + (0 - b) = a := by
  rw [Int32.add_assoc, Int32.sub_eq_add_neg 0, Int32.zero_add, ← Int32.sub_eq_add_neg,
    Int32.sub_self, Int32.add_zero]

/-- Placing rows from `y`, then moving them all down by `h`, is placing them
from `y + h`. -/
theorem shift_place (rows : List Row) (y h : Int32) :
    shifted 0 h (place rows y) 0 = place rows (y + h) := by
  induction rows generalizing y with
  | nil => rfl
  | cons r t ih =>
    simp only [place, shifted, ih, placed, Scene.translate, Int32.add_zero, add_right_comm]

theorem insert_core (rows : List Row) (i : Nat) (y h : Int32) (s : Scene) :
    shifted 0 h (Lists.insert (place rows y) i (placed (top rows i y) s)) (i + 1) =
      place (Lists.insert rows i ⟨h, s⟩) y := by
  induction rows generalizing i y with
  | nil => rfl
  | cons r t ih =>
    cases i with
    | zero =>
      show placed y s :: shifted 0 h (place (r :: t) y) 0 = place (⟨h, s⟩ :: r :: t) y
      rw [shift_place]; rfl
    | succ i => simp only [place, top, Lists.insert, shifted, ih]

theorem delete_core (rows : List Row) (i : Nat) (y : Int32) :
    shifted 0 (0 - height rows i) (Lists.remove (place rows y) i) i = place (Lists.remove rows i) y := by
  induction rows generalizing i y with
  | nil => rfl
  | cons r t ih =>
    cases i with
    | zero => simp only [place, height, Lists.remove, shift_place, add_sub_cancel']
    | succ i => simp only [place, height, Lists.remove, shifted, ih]

theorem swap_core (rows : List Row) (i : Nat) (y : Int32) (r : Row)
    (hi : i < rows.length) (hh : height rows i = r.h) :
    Lists.insert (Lists.remove (place rows y) i) i (placed (top rows i y) r.s) =
      place (Lists.update rowEdits rows i (.replace r)) y := by
  induction rows generalizing i y with
  | nil => simp at hi
  | cons r0 t ih =>
    cases i with
    | zero =>
      simp only [height] at hh
      cases t <;> simp_all [place, top, Lists.remove, Lists.insert, Lists.update, whole.apply]
    | succ i =>
      simp only [List.length_cons] at hi
      simp only [place, top, height, Lists.remove, Lists.insert, Lists.update] at hh ⊢
      rw [ih i (y + r0.h) (by omega) hh]

theorem update_replace (rows : List Row) (i : Nat) (r : Row) (hi : i < rows.length) :
    Lists.update rowEdits rows i (.replace r) = Lists.insert (Lists.remove rows i) i r := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons r0 t ih =>
    cases i with
    | zero => cases t <;> rfl
    | succ i =>
      simp only [List.length_cons] at hi
      simp only [Lists.update, Lists.remove, Lists.insert, ih i (by omega)]
      rfl

/-- Past the end, replacing a row leaves the rows as they are. -/
theorem update_past (rows : List Row) (i : Nat) (r : Row) (hi : ¬ i < rows.length) :
    Lists.update rowEdits rows i (.replace r) = rows :=
  Lists.update_past (ca := rowEdits) rows i (Nat.le_of_not_lt hi) (.replace r)

theorem insert_ok (rows : List Row) (i : Nat) (r : Row) :
    run sceneEdits (insertEdits rows i r) (view rows) = view (Lists.insert rows i r) := by
  simp only [insertEdits, run, view, sceneEdits, SceneEdit.apply]
  rw [insert_core]

theorem delete_ok (rows : List Row) (i : Nat) :
    run sceneEdits (deleteEdits rows i) (view rows) = view (Lists.remove rows i) := by
  simp only [deleteEdits, run, view, sceneEdits, SceneEdit.apply]
  rw [delete_core]

theorem replace_ok (rows : List Row) (i : Nat) (r : Row) :
    run sceneEdits (replaceEdits rows i r) (view rows) =
      view (Lists.update rowEdits rows i (.replace r)) := by
  unfold replaceEdits
  split
  · rename_i hi
    split
    · rename_i hh
      simp only [run, view, sceneEdits, SceneEdit.apply]
      rw [swap_core rows i 0 r hi hh]
    · rw [run_append, delete_ok, insert_ok, update_replace rows i r hi]
  · rename_i hi
    rw [update_past rows i r hi]
    rfl

/-- One edit's edits give the column of the edited rows. -/
theorem edit_ok (rows : List Row) (e : Lists.Edit.of rowEdits) :
    run sceneEdits (edit rows e) (view rows) = view (Lists.edit rowEdits e rows) := by
  match e with
  | .insert i r => exact insert_ok rows i r
  | .delete i => exact delete_ok rows i
  | .update i (.replace r) => exact replace_ok rows i r
  | .update i (.apply e) => exact nomatch e

theorem one_ok : one.ok := edit_ok

/-- And for runs of edits. -/
theorem inc_ok : inc.ok := lift_ok one one_ok

end Deui.Column
