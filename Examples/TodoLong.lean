import Examples.Todo
import Deui.Screen

/-! The to-do list with 10,000 items, in a window: only the rows that show
are in the scene, so typing, ticking and scrolling cost the same as with
two. -/

open Examples.Todo

def many : Nat → List Item
  | 0 => []
  | n + 1 => ⟨s!"item {10000 - n}", false⟩ :: many n

def main : IO Unit :=
  Deui.Screen.run app "deui" "/usr/share/fonts/liberation/LiberationSans-Regular.ttf" 360 400 1579292
    ⟨[], many 10000, 0⟩
