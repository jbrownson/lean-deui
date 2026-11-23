import Progred.Outside

/-! Plays keys through the editor with no window, printing what it would
show: the lines, the selection, and the offers. -/

open Progred Deui

abbrev M := App.Model Editor.app

def show_ (m : M) : IO Unit := do
  let model := m.state
  let (lines, occs) := model.laid
  for l in lines do IO.println ("  | " ++ l.plain)
  match model.selection with
  | some sel =>
    let stops := Model.stops lines occs
    let at_ := (model.here occs stops).map fun i => s!"line {stops[i]!.line} col {stops[i]!.col}"
    let typing := sel.editing.map fun e => s!" typing \"{e.text}\"{if e.picker then " (query)" else ""}"
    IO.println s!"  selection: {repr sel.stage} at {at_.getD "?"}{typing.getD ""}"
    let offers := Model.offers model
    if !offers.isEmpty then
      IO.println ("  offers: " ++ ", ".intercalate ((offers.take 6).map fun o => (if o.isNew then "new " else "") ++ o.text ++ " (" ++ o.detail ++ ")"))
  | none => IO.println "  selection: none"

def play (m : M) (es : List App.Event) : M := App.play Editor.app m es

def type (s : String) : List App.Event := [.text s]
def key (code : UInt32) (mods : UInt32 := 0) : List App.Event := [.key code true mods]
def enter := key 13
def tab := key 9
def back := key 127

unsafe def main : IO Unit := do
  let rt ← Run.Runtime.load
  let memo ← IO.mkRef []
  let mut m : M := App.start Editor.app {}
  let left := key 63234
  let steps : List (String × List App.Event) := [
    ("a notebook with an evaluation of 1 + 2", tab ++ type "note" ++ enter ++ type "eva" ++ enter ++ type "add" ++ enter
      ++ type "1" ++ enter ++ tab ++ type "2" ++ enter),
    ("a lambda named double, with a parameter x", tab ++ type "lam" ++ enter ++ type "double" ++ enter ++ tab ++ type "x" ++ enter),
    ("its body: multiply x by 2", tab ++ tab ++ type "mult" ++ enter ++ type "x" ++ enter ++ tab ++ type "2" ++ enter),
    ("an evaluation calling double on 21", tab ++ type "eva" ++ enter ++ type "doub" ++ enter ++ type "21" ++ enter),
    ("an evaluation mapping double over a list", tab ++ type "eva" ++ enter ++ type "map" ++ enter ++ type "double" ++ key 63233 ++ enter
      ++ tab ++ type "[" ++ type "1" ++ enter ++ tab ++ type "2" ++ enter ++ tab ++ type "3" ++ enter),
    ("a mistake: adding text to a number", tab ++ tab ++ type "eva" ++ enter ++ type "add" ++ enter ++ type "1" ++ enter ++ tab ++ type "\"no" ++ enter),
    ("left twice, then undo twice and redo", left ++ left ++ key 'z'.toNat.toUInt32 2 ++ key 'z'.toNat.toUInt32 2 ++ key 'z'.toNat.toUInt32 3)]
  for (name, es) in steps do
    for e in es do
      m := App.step Editor.app m e
      m := (App.edited Editor.app m (← Outside.edits rt memo none m.state)).1
    IO.println s!"-- {name}"
    show_ m
  IO.println "-- as a file"
  IO.println (GidText.write m.state.doc m.state.library)
