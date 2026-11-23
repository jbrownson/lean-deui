import Deui.Scene

/-!
Any view, redrawn: rows given as a function of the state, with the
derivative that takes every row off the screen and puts the new ones on. It
is to scenes what `recompute` is to values: always correct, and as much
work as drawing again, so it's where a view starts before it has a
derivative of its own.
-/

namespace Deui.Redraw

open Deui

/-- The edits that take `n` rows off, front first. -/
def clear : Nat → List SceneEdit
  | 0 => []
  | n + 1 => .delete 0 :: clear n

/-- The edits that put `rows` on an empty scene: its tail, then its head at
the front. -/
def fill : List Scene → List SceneEdit
  | [] => []
  | r :: rs => fill rs ++ [.insert 0 r]

/-- The scene: the rows, in a group at the origin. -/
def scene (rows : List Scene) : Scene := .group 0 0 rows

variable {cs : EditStructure} (rows : cs.Value → List Scene)

/-- `rows`, as a view whose derivative redraws: it keeps the state and how
many rows are on the screen. -/
def redraw : Cached (runs cs) (runs sceneEdits) where
  Cache := cs.Value × Nat
  f s := (scene (rows s), s, (rows s).length)
  df c es :=
    let s := run cs es c.1
    (clear c.2 ++ fill (rows s), s, (rows s).length)

theorem clear_ok (rs : List Scene) : run sceneEdits (clear rs.length) (scene rs) = scene [] := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact ih

theorem fill_ok (rs : List Scene) : run sceneEdits (fill rs) (scene []) = scene rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    show run sceneEdits (fill rs ++ [.insert 0 r]) (scene []) = scene (r :: rs)
    rw [run_append, ih]
    cases rs <;> rfl

/-- Redrawing is correct, for any rows. -/
theorem redraw_ok : (redraw rows).ok := by
  intro s es
  show (run sceneEdits (clear (rows s).length ++ fill (rows (run cs es s))) (scene (rows s)), _, _) = _
  rw [run_append, clear_ok, fill_ok]
  rfl

end Deui.Redraw
