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
  let _right := key 63235
  let up := key 63232
  let steps : List (String × List App.Event) := [
    ("a notebook; a text entry", tab ++ type "note" ++ enter ++ type "\"hello" ++ enter),
    ("typing on the text edits it in place", type " world"),
    ("Enter ends typing; Enter again adds an entry after; a record", enter ++ enter ++ type "{"),
    ("a new label, size, and its value", type "size" ++ enter ++ type "12" ++ enter),
    ("Enter on the value adds a field: color, red", enter ++ type "color" ++ enter ++ type "\"red" ++ enter),
    ("Backspace deletes the value, leaving the record", back),
    ("Left to the record; Ctrl+Enter adds a field within", left ++ key 13 2 ++ type "tags" ++ enter ++ type "["
      ++ type "1" ++ enter ++ enter ++ type "2" ++ enter),
    ("Shift+Enter adds before; Backspace on the hole removes it", key 13 1 ++ type "0" ++ enter ++ enter ++ back),
    ("up to the first entry, and delete it: a hole, then gone", up ++ back ++ back),
    ("a named value, and an evaluation of it; Space folds the entry", tab ++ tab ++ tab ++ tab ++ tab ++ type "val" ++ enter ++ type "answer" ++ enter ++ tab ++ type "42" ++ enter
      ++ tab ++ type "eva" ++ enter ++ type "answ" ++ enter),
    ("undo three times", key 'z'.toNat.toUInt32 2 ++ key 'z'.toNat.toUInt32 2 ++ key 'z'.toNat.toUInt32 2)]
  for (name, es) in steps do
    for e in es do
      m := App.step Editor.app m e
      m := (App.edited Editor.app m (← Outside.edits rt memo none m.state)).1
    IO.println s!"-- {name}"
    show_ m
  IO.println "-- as a file"
  IO.println (GidText.write m.state.doc m.state.library)
