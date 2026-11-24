import Progred.Editor
import Progred.Derived.Forms

/-!
The view drawn by derivative (`Progred/Derived/`), beside the view as it
is: `progred_derived 300` times the same edits through both, checking
each keeps the lines it would draw from nothing; `progred_derived` with
files says which of their parts the two draw the same.
-/

open Deui

/-! ## Measured against the view as it is -/

open Progred

/-- Ten cells that entries refer to, each with a name and no more. -/
def shared : List CellId :=
  ["0a11b6dc2ad3a4f3b1c9d0a53c7f2e01", "1b22c7ed3be4b5a4c2dae1b64d8a3f12", "2c33d8fe4cf5c6b5d3ebf2c75e9b4a23",
   "3d44e9af5da6d7c6e4fca3d86fac5b34", "4e55fab06eb7e8d7f5adb4e97abd6c45", "5f66abc17fc8f9e8a6bec5fa8bce7d56",
   "6a77bcd28ad9aaf9b7cfd6ab9cdf8e67", "7b88cde39beabbaac8dae7bcadea9f78", "8c99def4acfbccbbd9ebf8cdbefbaa89",
   "9daaefa5bdacddcceafca9decfacbb9a"].map cell!

/-- A label the document defines, which every entry has a field of. -/
def tag : CellId := cell! "c0ffee5bdacddcceafca9decfacbb9a0"

/-- A cell nothing shows. -/
def unseen : CellId := cell! "deadbee5dacddcceafca9decfacbb9a1"

def nameOnly (n : String) : Value := .record [(Kinds.name, Value.text n)]

def rec (fields : List (CellId × Value)) : Value :=
  .record (fields.foldl (fun acc (l, v) => Value.setField acc l v) [])

def entry (i : Nat) : Value :=
  rec [(Kinds.name, Value.text s!"entry {i}"),
    (Kinds.fields, .list ((Position.spread 12).zip ((List.range 12).map fun j => Value.u64 (i * j)))),
    (Kinds.function, .cell (shared[i % 10]!)), (tag, Value.u64 i),
    (Kinds.body, rec [(Kinds.name, Value.text "some words that make the line long enough to wrap around"),
      (Kinds.value, Value.u64 i), (Kinds.params, Value.text "and a second field of text, to be sure it does")])]

def positions (n : Nat) : List Position := Position.spread n

def root (n : Nat) : Value := .list ((positions n).zip ((List.range n).map entry))

/-- A definition that's more than a name, so the cell is drawn open where
it's a field of a record with no kind. -/
def more (n : String) (k : Nat) : Value := rec [(Kinds.name, Value.text n), (Kinds.value, Value.u64 k)]

def cells0 : Editor.Cells :=
  ((List.range 10).foldl (fun (cells : Editor.Cells) k => cells.insert shared[k]! (more s!"shared {k}" k)) {}).insert
    tag (nameOnly "tag")

/-- One step of a measurement: definitions written, and writes in the
value. -/
structure Step' where
  ces : List Model.CellsEdit := []
  writes : List (List Step × Option Value) := []
  /-- The folds in effect from this step. -/
  folds : List (Path × Bool) := []

abbrev OldCache := Editor.part.Cache
/-- The derived lines of a value at the root. -/
def derived : Cached (prod Derived.Under (runs Derived.Writes)) Derived.Lines :=
  Derived.lines {} [] (.value false)

abbrev NewCache := derived.Cache

structure State where
  cells : Editor.Cells
  folds : List (Path × Bool)
  value : Value
  old : OldCache
  new : NewCache
  oldLines : List Line
  newLines : List Line

def seen : Display.Seen := {}

def oldF (cells : Editor.Cells) (value : Value) : List Line × OldCache :=
  Editor.part.f ((seen, cells), .whole (some value))

def newF (cells : Editor.Cells) (value : Value) (folds : List (Path × Bool) := []) : List Line × NewCache :=
  derived.f ((((80 : Nat), folds), cells), value)

def oldDf (k : OldCache) (step : Step') : Editor.PartLines.Edit × OldCache :=
  Editor.part.df k ((({ folds := step.folds } : Display.Seen), step.ces), step.writes.map fun (rel, w) => .write rel w)

def newDf (k : NewCache) (step : Step') : Editor.PartLines.Edit × NewCache :=
  derived.df k ((((80 : Nat), step.folds), step.ces), step.writes)

def applied (es : Editor.PartLines.Edit) (ls : List Line) : List Line := Editor.PartLines.apply es ls

def start (n : Nat) : IO State := do
  let value := root n
  let t0 ← IO.monoNanosNow
  let old ← IO.lazyPure fun _ => oldF cells0 value
  let t1 ← IO.monoNanosNow
  let new ← IO.lazyPure fun _ => newF cells0 value
  let t2 ← IO.monoNanosNow
  IO.println s!"{old.1.length} lines; from nothing: as it is {(t1 - t0) / 1000} µs, derived {(t2 - t1) / 1000} µs"
  if !(decide (old.1 = new.1)) then IO.println "  !! the two draw different lines"
  return ⟨cells0, [], value, old.2, new.2, old.1, new.1⟩

/-- Runs steps through both, timing each, and checks what each keeps
against its lines from nothing. -/
def timed (name : String) (s : State) (steps : List Step') : IO State := do
  let mut s := s
  let mut oldTime := 0
  let mut newTime := 0
  let mut oldEdits := 0
  let mut newEdits := 0
  for step in steps do
    let t0 ← IO.monoNanosNow
    let old ← IO.lazyPure fun _ => oldDf s.old step
    let t1 ← IO.monoNanosNow
    let new ← IO.lazyPure fun _ => newDf s.new step
    let t2 ← IO.monoNanosNow
    oldTime := oldTime + (t1 - t0)
    newTime := newTime + (t2 - t1)
    oldEdits := oldEdits + old.1.length
    newEdits := newEdits + new.1.length
    s := { cells := run Editor.cellsEdits step.ces s.cells, folds := step.folds,
           value := run Derived.Writes step.writes s.value,
           old := old.2, new := new.2, oldLines := applied old.1 s.oldLines, newLines := applied new.1 s.newLines }
  let n := steps.length
  IO.println s!"  {name}: as it is {oldTime / n / 1000} µs ({oldEdits / n} line edits), derived {newTime / n / 1000} µs ({newEdits / n})"
  let fresh := (newF s.cells s.value s.folds).1
  if !(decide (s.newLines = fresh)) then IO.println "  !! derived: the lines kept aren't the lines from nothing"
  if !(decide (s.oldLines = fresh)) then IO.println "  !! as it is: the lines kept aren't the derived lines from nothing"
  return s

/-- A part of its own for each entry: what each keeps. -/
structure Part where
  value : Value
  old : OldCache
  new : NewCache
  oldLines : List Line
  newLines : List Line

/-- Runs steps through a part for each entry: a write goes to the entry
it's in, and a write of a definition to every part. -/
def timedParts (name : String) (ps : List Position) (cells : Editor.Cells) (parts : Array Part)
    (steps : List Step') : IO (Editor.Cells × Array Part) := do
  let mut parts := parts
  let mut cells := cells
  let mut oldTime := 0
  let mut newTime := 0
  let mut oldEdits := 0
  let mut newEdits := 0
  for step in steps do
    -- The parts the step reaches, and what it is to each.
    let reached : List (Nat × Step') :=
      match step.writes with
      | [(.element p :: rel, w)] => [(ps.idxOf p, { step with writes := [(rel, w)] })]
      | _ => (List.range parts.size).map fun i => (i, step)
    let t0 ← IO.monoNanosNow
    let held := parts
    let olds ← IO.lazyPure fun _ => reached.filterMap fun (i, st) => (held[i]?).map fun part => oldDf part.old st
    let t1 ← IO.monoNanosNow
    let news ← IO.lazyPure fun _ => reached.filterMap fun (i, st) => (held[i]?).map fun part => newDf part.new st
    let t2 ← IO.monoNanosNow
    oldTime := oldTime + (t1 - t0)
    newTime := newTime + (t2 - t1)
    cells := run Editor.cellsEdits step.ces cells
    for ((i, st), (old, new)) in reached.zip (olds.zip news) do
      oldEdits := oldEdits + old.1.length
      newEdits := newEdits + new.1.length
      match parts[i]? with
      | some part =>
        let updated : Part :=
          ⟨run Derived.Writes st.writes part.value, old.2, new.2, applied old.1 part.oldLines, applied new.1 part.newLines⟩
        parts := parts.set! i updated
      | none => pure ()
  let n := steps.length
  IO.println s!"  {name}: as it is {oldTime / n / 1000} µs ({oldEdits / n} line edits), derived {newTime / n / 1000} µs ({newEdits / n})"
  for part in parts do
    let fresh := (newF cells part.value).1
    if !(decide (part.newLines = fresh)) then IO.println "  !! derived: the lines kept aren't the lines from nothing"
    if !(decide (part.oldLines = fresh)) then IO.println "  !! as it is: the lines kept aren't the derived lines from nothing"
  return (cells, parts)

/-- A part's lines as the view draws them now, with nothing selected. -/
def oldPart (cells : Editor.Cells) (entry : Display.Entry) : List Line :=
  Display.part (Display.input {} (Display.item (Editor.look cells) entry))

/-- A part's lines, derived; none for a part with no value. -/
def newPart (cells : Editor.Cells) : Display.Entry → Option (List Line)
  | .entry p v => some ((Derived.lines {} Display.entriesPath (.entry p)).f ((((80 : Nat), ([] : List (Path × Bool))), cells), .list [(p, v)])).1
  | .end_ => some ((Derived.lines {} Display.entriesPath .end_).f ((((80 : Nat), ([] : List (Path × Bool))), cells), .list [])).1
  | .whole (some v) => some ((Derived.lines {} [] (.value false)).f ((((80 : Nat), ([] : List (Path × Bool))), cells), v)).1
  | .whole none => none

/-- Which parts of a file the two draw the same, and where the first of
the rest part ways. -/
def compare (path : String) (verbose : Bool) : IO Unit := do
  let text ← IO.FS.readFile path
  match ← GidText.parse text with
  | .error e => IO.println s!"{path}: {e}"
  | .ok d =>
    let parts := Display.entries d.root
    let mut same := 0
    let mut shown := 0
    for part in parts do
      let old := oldPart d.cells part
      match newPart d.cells part with
      | some new =>
        if decide (old = new) then same := same + 1
        else if verbose && shown < 3 then
          shown := shown + 1
          match (old.zip new).find? fun (a, b) => !decide (a = b) with
          | some (a, b) => IO.println s!"    as it is: {a.plain}\n    derived:  {b.plain}"
          | none => IO.println s!"    {old.length} lines as it is, {new.length} derived"
      | none => pure ()
    IO.println s!"{path}: {same} of {parts.length} parts drawn the same"

def main (args : List String) : IO Unit := do
  let files := args.filter (·.endsWith ".gid")
  if !files.isEmpty then
    for f in files do compare f (args.contains "where")
    return
  let n := (args.head?.bind (·.toNat?)).getD 300
  let ps := positions n
  let at_ (j : Nat) : Position := ps[(j * (if args.contains "top" then 0 else 37)) % n]!
  -- `x200` runs each step 200 times; `only:` and a word runs the steps named with it; `derived` skips the view as it is.
  let reps := List.range (((args.find? (·.startsWith "x")).bind fun a => (a.drop 1).toString.toNat?).getD 20)
  let only := ((args.find? (·.startsWith "only:")).map fun a => (a.drop 5).toString).getD ""
  let last := (Position.spread 12).getLast!
  let added := Position.between (some last) none
  let news := reps.map fun j => Position.between (some (ps[j * 11 % (n - 1)]!)) (some (ps[j * 11 % (n - 1) + 1]!))
  let steps : List (String × List Step') := [
    ("typing in a text", reps.map fun j =>
      { writes := [([.element (at_ j), .key Kinds.name, .key Kinds.bytes], some (.blob s!"entry, typed {j}".toUTF8.toList))] }),
    ("an element added to a list", reps.map fun j =>
      { writes := [([.element (at_ j), .key Kinds.fields, .element added], some (Value.u64 7))] }),
    ("an element taken away", reps.map fun j =>
      { writes := [([.element (at_ j), .key Kinds.fields, .element added], none)] }),
    ("a field added to a record", reps.map fun j =>
      { writes := [([.element (at_ j), .key Kinds.value], some (Value.u64 5))] }),
    ("a field taken away", reps.map fun j => { writes := [([.element (at_ j), .key Kinds.value], none)] }),
    ("a field's value replaced", reps.map fun j =>
      { writes := [([.element (at_ j), .key Kinds.body], some (Value.text s!"now text {j}"))] }),
    ("an entry added", (reps.zip news).map fun (j, p) => { writes := [([.element p], some (entry (1000 + j)))] }),
    ("an entry taken away", news.map fun p => { writes := [([.element p], none)] }),
    ("a label every entry has, renamed", reps.map fun j => { ces := [.set tag (some (nameOnly s!"tag {j}"))] }),
    ("a definition a tenth of the entries show open, written", reps.map fun j =>
      { ces := [.set shared[3]! (some (more s!"shared, renamed {j}" j))] }),
    ("a cell folded shut, and the last opened", reps.map fun j =>
      { folds := [([.element (at_ j), .key Kinds.function], true)] }),
    ("a cell nothing shows, written", reps.map fun j => { ces := [.set unseen (some (nameOnly s!"unseen {j}"))] })]
  let steps := steps.filter fun (name, _) => (name.splitOn only).length > 1 || only.isEmpty
  if args.contains "parts" then
    -- A part for each entry, as the notebook has.
    let entries := (List.range n).map entry
    let t0 ← IO.monoNanosNow
    let olds ← IO.lazyPure fun _ => entries.map (oldF cells0)
    let t1 ← IO.monoNanosNow
    let news ← IO.lazyPure fun _ => entries.map (newF cells0)
    let t2 ← IO.monoNanosNow
    let lineCount := (olds.map (·.1.length)).foldl (· + ·) 0
    IO.println s!"{lineCount} lines in {n} parts; from nothing: as it is {(t1 - t0) / 1000} µs, derived {(t2 - t1) / 1000} µs"
    let mut parts : Array Part := #[]
    for (v, (old, new)) in entries.zip (olds.zip news) do
      if !(decide (old.1 = new.1)) then IO.println "  !! the two draw different lines"
      parts := parts.push ⟨v, old.2, new.2, old.1, new.1⟩
    let mut cells := cells0
    for (name, run) in steps do
      if !name.startsWith "an entry" && !name.startsWith "a cell folded" then
        (cells, parts) ← timedParts name ps cells parts run
  else
    let mut s ← start n
    for (name, run) in steps do
      s ← timed name s run
