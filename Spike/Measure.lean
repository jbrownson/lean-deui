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

/-- A notebook of `n` entries, each a record of a few fields and a list. -/
def notebook (n : Nat) : Document :=
  let entry (i : Nat) : Value :=
    .record [(Kinds.name, Value.text s!"entry {i}"),
      (Kinds.fields, .list ((Position.spread 12).zip ((List.range 12).map fun j => Value.u64 (i * j)))),
      (Kinds.body, .record [(Kinds.name, Value.text "some words that make the line long enough to wrap around"),
        (Kinds.value, Value.u64 i), (Kinds.params, Value.text "and a second field of text, to be sure it does")])]
  { root := some (Value.ofKind Kinds.notebook [(Kinds.entries, .list ((Position.spread n).zip ((List.range n).map entry)))]) }

/-- How long a document takes: laid out from nothing, and for each kind of
event, with what the view keeps. Files, or with a number, a notebook of
that many entries. -/
def main (args : List String) : IO Unit := do
  for path in args do
    let parsed ← match path.toNat? with
      | some n => pure (.ok (notebook n))
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
      IO.println s!"{path}: {l.lineCount} lines in {l.blocks.length} parts"
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
      let m ← timed "the wheel, with something selected" m (List.replicate 20 (.scroll 0 0 0 (-1)))
      let m ← timed "a new entry, typed" m ([key 13] ++ ("\"some words".toList.map fun c => .text c.toString) ++ [key 13])
      let m ← timed "typing in it" m ("and more".toList.map fun c => App.Event.text c.toString)
      if !(m.shown.1 == (Editor.view.f m.state).1) then IO.println "  !! the scene kept isn't the model's view"
