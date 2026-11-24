import Progred.Outside

/-! Plays keys through the editor with no window, printing what it would
show: the lines, the selection, and the offers. -/

open Progred Deui

abbrev M := App.Model Editor.app

def show_ (m : M) : IO Unit := do
  let model := m.state
  -- The layout the view keeps, which is what the editor reads.
  let l : Model.Layout := ⟨(Editor.laidOf m.shown.2).2⟩
  for lines in l.parts do
    for line in lines do
      IO.println ("  | " ++ line.plain)
      let failed := line.cells.filter fun s => (s.occ.map (·.failed)).getD false
      if !failed.isEmpty then IO.println ("  ! " ++ String.join (failed.map (·.text)))
  -- What's kept is what working it all out again gives: the laws say so,
  -- and this looks.
  if l.plain != (Model.Layout.of model).plain then IO.println "  !! the layout kept isn't the model's layout"
  if !(m.shown.1 == (Editor.view.f model).1) then IO.println "  !! the scene kept isn't the model's view"
  -- The edits said every change that was noted: none is left.
  if !model.log.isEmpty then IO.println "  !! changes noted that no edit said"
  match model.selection with
  | some sel =>
    let at_ := (l.here model).map fun (b, here) => s!"line {l.lineOf b + here.line} col {here.col}"
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

/-- A step written out: words apart by spaces, each typed as it is, or a
key in angle brackets: `<enter>`, `<tab>`, `<c-z>`, `<s-enter>`. -/
def script (s : String) : List App.Event :=
  (s.splitOn " ").flatMap fun word =>
    if word.startsWith "<" && word.endsWith ">" && word.length > 2 then
      let inner := ((word.drop 1).dropEnd 1).toString
      let (mods, name) : UInt32 × String :=
        if inner.startsWith "c-s-" then (3, (inner.drop 4).toString)
        else if inner.startsWith "c-" then (2, (inner.drop 2).toString)
        else if inner.startsWith "s-" then (1, (inner.drop 2).toString)
        else (0, inner)
      match name with
      | "enter" => key 13 mods
      | "tab" => key 9 mods
      | "back" => key 127 mods
      | "esc" => key 27 mods
      | "up" => key 63232 mods
      | "down" => key 63233 mods
      | "left" => key 63234 mods
      | "right" => key 63235 mods
      | "space" => type " "
      | other => match other.toList with
        | [c] => key c.toNat.toUInt32 mods
        | _ => []
    else type word

/-- With arguments, plays each as a step, from an empty document, or from
the file that's the first argument; with none, plays the walk below. -/
unsafe def main (args : List String) : IO Unit := do
  let rt ← Run.Runtime.load
  let memo ← IO.mkRef []
  let functions ← IO.mkRef []
  let clipboard ← Outside.Clipboard.inMemory
  -- A first argument that's a file is the document to start from.
  let (doc, args) ← match args with
    | path :: rest =>
      if path.endsWith ".gid" then
        match ← GidText.parse (← IO.FS.readFile path) with
        | .ok d => pure (d, "" :: rest)
        | .error e => throw (IO.userError s!"{path}: {e}")
      else pure (({} : Document), args)
    | [] => pure (({} : Document), args)
  let mut m : M := App.start Editor.app { doc }
  if !args.isEmpty then
    for step in args do
      -- A step that starts with `>` writes the document to the file named after it.
      if step.startsWith ">" then
        IO.FS.writeFile (step.drop 1).toString (GidText.write m.state.doc m.state.library)
        continue
      for e in script step do
        m := App.step Editor.app m e
        m := (App.applied Editor.app m (← Outside.edits rt memo functions none clipboard m.state)).1
      IO.println s!"-- {step}"
      show_ m
    return
  let _right := key 63235
  let up := key 63232
  let steps : List (String × List App.Event) := [
    ("a notebook; a text entry", tab ++ type "note" ++ enter ++ type "\"hello" ++ enter),
    ("typing on the text edits it in place", type " world"),
    ("Enter ends typing; Enter again adds an entry after; a record", enter ++ enter ++ type "{"),
    ("a new label, size, and its value", type "size" ++ enter ++ type "12" ++ enter),
    ("Enter on the value adds a field: color, red", enter ++ type "color" ++ enter ++ type "\"red" ++ enter),
    ("Backspace deletes the value, leaving the record", back),
    ("Ctrl+Enter on the record adds a field within", key 13 2 ++ type "tags" ++ enter ++ type "["
      ++ type "1" ++ enter ++ enter ++ type "2" ++ enter),
    ("Shift+Enter adds before; Backspace on the hole removes it", key 13 1 ++ type "0" ++ enter ++ enter ++ back),
    ("up to the first entry, and delete it: a hole, then gone", up ++ back ++ back),
    ("Enter adds an entry: an evaluation of a call", enter ++ type "eva" ++ enter ++ type "add" ++ enter
      ++ type "1" ++ enter ++ tab ++ type "2" ++ enter),
    ("the second argument replaced by a text: the error, and what it's about", back ++ type "\"no" ++ enter),
    ("undo", key 'z'.toNat.toUInt32 2),
    ("copy the first argument, and paste it as the second", key 63234 ++ key 63234 ++ key 'c'.toNat.toUInt32 2 ++ tab ++ key 'v'.toNat.toUInt32 2),
    ("up into the record; its 12 cut, and pasted as an entry after the record", up ++ key 'x'.toNat.toUInt32 2
      ++ enter ++ key 'v'.toNat.toUInt32 2)]
  let steps := steps ++ [
    ("a function that calls itself, with its types", script
      "<enter> lam <enter> fact <enter> <tab> n <enter> : Nat <enter> <left> <left> : Nat <enter> <tab> if <enter> equ <enter> n <enter> <tab> 0 <enter> <tab> 1 <enter> <tab> mul <enter> n <enter> <tab> fact <enter> sub <enter> n <enter> <tab> 1 <enter>"),
    ("and an evaluation of it", script "<up> <enter> eva <enter> fact <enter> 10 <enter>")]
  for (name, es) in steps do
    for e in es do
      m := App.step Editor.app m e
      m := (App.applied Editor.app m (← Outside.edits rt memo functions none clipboard m.state)).1
    IO.println s!"-- {name}"
    show_ m
  clipboard.set "from elsewhere"
  for e in enter ++ key 'v'.toNat.toUInt32 2 do
    m := App.step Editor.app m e
    m := (App.applied Editor.app m (← Outside.edits rt memo functions none clipboard m.state)).1
  IO.println "-- text from elsewhere pasted as a new entry"
  show_ m
  IO.println "-- as a file"
  IO.println (GidText.write m.state.doc m.state.library)
