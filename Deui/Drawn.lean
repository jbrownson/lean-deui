import Deui.Drawing
import Deui.Column

/-!
A drawing on the screen: a drawing's rows (`Deui/Drawing.lean`), each
scene-drawn by `f` and placed at its top, as a column's children. Its
derivative turns each drawing edit into scene edits, without needing the
drawing: moving rows shifts them, a row entering or leaving is inserted or
deleted, and a row changing swaps what's in its group, which keeps its top.
-/

namespace Deui.Drawing

open Deui

variable {R : Type} (f : R → Scene)

/-- A placed row, as a group at its top holding its scene. -/
def placedScene (p : Placed R) : Scene := Column.placed (Int32.ofInt p.top) (f p.row)

/-- A drawing, as a group at the origin holding its rows. -/
def scene (ps : List (Placed R)) : Scene := .group 0 0 (ps.map (placedScene f))

/-- The scene edits one drawing edit makes. -/
def sceneEdits : Edit R → List SceneEdit
  | .translate dy => [.shift 0 0 (Int32.ofInt dy)]
  | .shift k dy => [.shift k 0 (Int32.ofInt dy)]
  | .insert k p => [.insert k (placedScene f p)]
  | .delete k => [.delete k]
  | .update k r => [.update k (.delete 0), .update k (.insert 0 (f r))]

/-- A drawing on the screen, for one edit at a time. -/
def one : Inc (editStructure R) (runs Deui.sceneEdits) := ⟨scene f, fun _ e => sceneEdits f e⟩

/-- A drawing on the screen, for runs of edits. -/
def inc : Inc (runs (editStructure R)) (runs Deui.sceneEdits) := lift (one f)

/-! ## Proofs -/

theorem placed_move (p : Placed R) (dy : Int) :
    (placedScene f p).translate 0 (Int32.ofInt dy) = placedScene f (p.move dy) := by
  simp only [placedScene, Column.placed, Scene.translate, Placed.move, Int32.ofInt_add, Int32.add_zero]

theorem shift_map (dy : Int) (k : Nat) (ps : List (Placed R)) :
    shifted 0 (Int32.ofInt dy) (ps.map (placedScene f)) k = (shiftFrom dy k ps).map (placedScene f) := by
  induction ps generalizing k with
  | nil => cases k <;> rfl
  | cons p ps ih =>
    cases k with
    | zero =>
      simp only [List.map, shifted, shiftFrom, placed_move]
      rw [ih 0]
      simp [shiftFrom]
    | succ k => simp only [List.map, shifted, shiftFrom, ih k]

theorem update_map (r : R) (k : Nat) (ps : List (Placed R)) :
    ((ps.map (placedScene f)).modify k (SceneEdit.apply (.delete 0))).modify k (SceneEdit.apply (.insert 0 (f r))) =
      (setRow r k ps).map (placedScene f) := by
  induction ps generalizing k with
  | nil => cases k <;> rfl
  | cons p ps ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [List.map, setRow] at ih ⊢
      simp [List.modify_succ_cons, ih k]

/-- One edit's scene edits give the scene of the edited drawing. -/
theorem one_ok : (one f).ok := by
  intro ps e
  show run Deui.sceneEdits (sceneEdits f e) (scene f ps) = scene f (Drawing.edit e ps)
  cases e with
  | translate dy =>
    show Scene.group 0 0 (shifted 0 (Int32.ofInt dy) (ps.map (placedScene f)) 0) = _
    rw [shift_map]; rfl
  | shift k dy =>
    show Scene.group 0 0 (shifted 0 (Int32.ofInt dy) (ps.map (placedScene f)) k) = _
    rw [shift_map]; rfl
  | insert k p =>
    show Scene.group 0 0 (Lists.insert (ps.map (placedScene f)) k (placedScene f p)) = _
    rw [← Lists.map_insert]; rfl
  | delete k =>
    show Scene.group 0 0 (Lists.remove (ps.map (placedScene f)) k) = _
    rw [← Lists.map_remove]; rfl
  | update k r =>
    show Scene.group 0 0 (((ps.map (placedScene f)).modify k (SceneEdit.apply (.delete 0))).modify k
      (SceneEdit.apply (.insert 0 (f r)))) = _
    rw [update_map]; rfl

/-- And for runs of edits. -/
theorem inc_ok : (inc f).ok := lift_ok (one f) (one_ok f)

end Deui.Drawing
