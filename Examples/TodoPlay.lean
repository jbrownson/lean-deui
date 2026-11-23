import Examples.Todo

/-! Plays events through the to-do list, then prints the items left and
whether the scene on screen is their view, drawn again. -/

open Deui Examples.Todo

def click (x y : Float) : App.Event := .press x y 0 true

/-- A new item, typed in; tick the second item's box; delete the third. -/
def events : List App.Event :=
  [.key 13 true, .text "Ship deui", click 20 58, click 340 100]

def main : IO Unit := do
  let m := App.play app (App.start app items) events
  IO.println "done? item:"
  for it in m.state.rows do
    IO.println s!"{if it.done then "yes" else "no"} {it.text}"
  let same := m.scene == (view.f m.state).1
  IO.println s!"the scene on screen is the view of the items: {if same then "yes" else "no"}"
