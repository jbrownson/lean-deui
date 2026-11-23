import Progred.Editor

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

def main : IO Unit := do
  let ids ← (List.range 200).mapM fun _ => CellId.new
  let mut m : M := App.start Editor.app { ids }
  let steps : List (String × List App.Event) := [
    ("start", []),
    ("Tab", tab),
    ("type note", type "note"),
    ("Enter", enter),
    ("type eva, Enter", type "eva" ++ enter),
    ("type add, Enter", type "add" ++ enter),
    ("type 1, Enter", type "1" ++ enter),
    ("Tab, type 2, Enter", tab ++ type "2" ++ enter),
    ("Tab (after the evaluation), type val, Enter", tab ++ type "val" ++ enter),
    ("type double, Enter", type "double" ++ enter),
    ("type lam, Enter", type "lam" ++ enter),
    ("Tab, type x, Enter", tab ++ type "x" ++ enter),
    ("Left ×4, undo ×2, redo", key 63234 ++ key 63234 ++ key 'z'.toNat.toUInt32 2 ++ key 'z'.toNat.toUInt32 2 ++ key 'z'.toNat.toUInt32 3)]
  for (name, es) in steps do
    m := play m es
    IO.println s!"-- {name}"
    show_ m
  IO.println "-- as a file"
  IO.println (GidText.write m.state.doc m.state.library)
