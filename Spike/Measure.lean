import Progred.Editor
open Progred Deui

abbrev M := App.Model Editor.app

/-- The time events take, each: in microseconds. -/
def timed (name : String) (m : M) (events : List App.Event) : IO M := do
  let t0 ← IO.monoNanosNow
  let mut m := m
  let mut edits := 0
  for e in events do
    let t := App.turn Editor.app m e
    m := t.1
    edits := edits + t.2.length
  let t1 ← IO.monoNanosNow
  IO.println s!"  {name}: {(t1 - t0) / events.length / 1000} µs an event, {edits / events.length} scene edits"
  return m

/-- Ten cells that entries refer to: each a named value. -/
def shared : List CellId :=
  ["0a11b6dc2ad3a4f3b1c9d0a53c7f2e01", "1b22c7ed3be4b5a4c2dae1b64d8a3f12", "2c33d8fe4cf5c6b5d3ebf2c75e9b4a23",
   "3d44e9af5da6d7c6e4fca3d86fac5b34", "4e55fab06eb7e8d7f5adb4e97abd6c45", "5f66abc17fc8f9e8a6bec5fa8bce7d56",
   "6a77bcd28ad9aaf9b7cfd6ab9cdf8e67", "7b88cde39beabbaac8dae7bcadea9f78", "8c99def4acfbccbbd9ebf8cdbefbaa89",
   "9daaefa5bdacddccEafca9decfacbb9a".toLower].map cell!

def sharedValue (k n : Nat) : Value :=
  Value.ofKind Kinds.valueWrapper [(Kinds.name, Value.text s!"shared {k}"), (Kinds.value, Value.u64 n)]

/-- A notebook of `n` entries, each a record of a few fields and a list, and
a reference to one of ten shared cells, which it shows. -/
def notebook (n : Nat) : Document :=
  let entry (i : Nat) : Value :=
    .record [(Kinds.name, Value.text s!"entry {i}"),
      (Kinds.fields, .list ((Position.spread 12).zip ((List.range 12).map fun j => Value.u64 (i * j)))),
      (Kinds.function, .cell (shared[i % 10]!)),
      (Kinds.body, .record [(Kinds.name, Value.text "some words that make the line long enough to wrap around"),
        (Kinds.value, Value.u64 i), (Kinds.params, Value.text "and a second field of text, to be sure it does")])]
  { root := some (Value.ofKind Kinds.notebook [(Kinds.entries, .list ((Position.spread n).zip ((List.range n).map entry)))]),
    cells := (List.range 10).foldl (fun cells k => cells.insert shared[k]! (sharedValue k 0)) {} }

/-- The same entries as a list at the root, which is one part. -/
def single (n : Nat) : Document :=
  let d := notebook n
  { d with root := match d.root.bind (·.field? Kinds.entries) with
      | some entries => some entries
      | none => d.root }

/-- The time edits take, each run of them: in microseconds. -/
def timedEdits (name : String) (m : M) (runs : List (List Model.Edit)) : IO M := do
  let t0 ← IO.monoNanosNow
  let mut m := m
  let mut edits := 0
  for es in runs do
    let t := App.applied Editor.app m es
    m := t.1
    edits := edits + t.2.length
  let t1 ← IO.monoNanosNow
  IO.println s!"  {name}: {(t1 - t0) / runs.length / 1000} µs each, {edits / runs.length} scene edits"
  return m

/-- How long a document takes: laid out from nothing, and for each kind of
event, with what the view keeps. Files, or with a number, a notebook of
that many entries. -/
def main (args : List String) : IO Unit := do
  for path in args.filter fun a => a.toNat?.isSome || a.endsWith ".gid" do
    let parsed ← match path.toNat? with
      | some n => pure (.ok (if args.contains "one" then single n else notebook n))
      | none => do GidText.parse (← IO.FS.readFile path)
    match parsed with
    | .error e => IO.println s!"{path}: {e}"
    | .ok d =>
      let model : Model := { doc := d }
      let t0 ← IO.monoNanosNow
      let mut lines := 0
      for i in [0:10] do
        lines := lines + (Model.Layout.of { model with scroll := i }).lineCount
      let t1 ← IO.monoNanosNow
      let l := Model.Layout.of model
      IO.println s!"{path}: {l.lineCount} lines in {l.parts.length} parts"
      IO.println s!"  laid out from nothing: {(t1 - t0) / 10 / 1000} µs"
      let t2 ← IO.monoNanosNow
      let m : M := App.start Editor.app model
      let t3 ← IO.monoNanosNow
      IO.println s!"  the first view: {(t3 - t2) / 1000} µs"
      let key (code : UInt32) : App.Event := .key code true 0
      let m ← timed "the wheel" m (List.replicate 20 (.scroll 0 0 0 (-1)))
      if args.contains "wheel" then
        let _ ← timed "the wheel, 3000 times" m ((List.replicate 1500 (.scroll 0 0 0 (-1))) ++ List.replicate 1500 (.scroll 0 0 0 1))
        return
      let m ← timed "an arrow key" m (List.replicate 20 (key 63233))
      if args.contains "arrow" then
        let _ ← timed "an arrow key, 1000 times" m ((List.replicate 500 (key 63233)) ++ List.replicate 500 (key 63232))
        return
      let m ← timed "the wheel, with something selected" m (List.replicate 20 (.scroll 0 0 0 (-1)))
      let m ← timed "a new entry, typed" m ([key 13] ++ ("\"some words".toList.map fun c => .text c.toString) ++ [key 13])
      let m ← timed "typing in it" m ("and more".toList.map fun c => App.Event.text c.toString)
      if args.contains "typing" then
        let _ ← timed "typing, 600 times" m ((List.replicate 300 (App.Event.text "x")) ++ List.replicate 300 (key 127))
        return
      let m ← timed "a function added" m [key 13, .text "l", .text "a", .text "m", key 13]
      let m ← timed "typing in its definition" m ("named".toList.map fun c => App.Event.text c.toString)
      if args.contains "line" then
        let _ ← timed "typing in a line, 600 times" m ((List.replicate 300 (App.Event.text "x")) ++ List.replicate 300 (key 127))
        return
      let m ← timed "undo, and redo" m ((List.range 10).flatMap fun _ => [.key 'z'.toNat.toUInt32 true 2, .key 'z'.toNat.toUInt32 true 3])
      let m ← if path.toNat?.isSome then do
          let m ← timedEdits "a definition a tenth of the entries reach, written" m
            ((List.range 20).map fun j => [Model.Edit.change (.cell shared[3]! (some (sharedValue 3 (j + 1))))])
          let m ← timedEdits "every definition written at once" m
            ((List.range 5).map fun j => [Model.Edit.change (.document
              { m.state.doc with cells :=
                  (List.range 10).foldl (fun cells k => cells.insert shared[k]! (sharedValue k (100 + j))) {} })])
          pure m
        else pure m
      if !(m.shown.1 == (Editor.view.f m.state).1) then IO.println "  !! the scene kept isn't the model's view"
