import Examples.Todo
import Deui.Screen

/-! The to-do list in a window. The font is Liberation Sans where Arch puts
it; another path works too. -/

open Examples.Todo

def main : IO Unit :=
  Deui.Screen.run app "deui" "/usr/share/fonts/liberation/LiberationSans-Regular.ttf" 360 400 1579292 items
