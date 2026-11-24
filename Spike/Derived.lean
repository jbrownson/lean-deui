import Progred.Derived.Part

/-!
The forms the view is drawn by (`Progred/Derived/`), against the forms it
was first grown from (`Progred/Display.lean`): `progred_derived` with
files says which of their parts the two draw the same, with nothing
selected, with each of the selections their occurrences give, and with
what their evaluations might have given; with `where`, where the first of
the rest part ways.
-/

open Deui Progred

/-- A part's lines by the forms the view was first grown from. -/
def oldPart (cells : Derived.Cells) (entry : Display.Entry) (seen : Display.Seen := {}) : List Line :=
  Display.part (Display.input seen (Display.item ((fun c => cells[c]?)) entry))

/-- A part's lines as the view draws them. -/
def newPart (cells : Derived.Cells) (entry : Display.Entry) (seen : Display.Seen := {}) : List Line :=
  Derived.partLines seen cells entry

/-- Whether two parts' lines are the same, but for this: where a label is
being typed for a new field, the forms the view was grown from draw the
`: _` after it in a frame of its own, as no occurrence, and now it's the
record's own. -/
def agree (label : Bool) (old new : List Line) : Bool :=
  if !label then decide (old = new)
  else
    old.length == new.length && (old.zip new).all fun (a, b) =>
      a.indent == b.indent && a.cells.length == b.cells.length && (a.cells.zip b.cells).all fun (x, y) =>
        if x.occ.isNone then x.text == y.text && decide (x.face = y.face) else decide (x = y)

/-- The selections to try at an occurrence: typing over a value, a hole
being filled, an element, a field or an entry being added, a label typed. -/
def selectionsAt (o : Occ) : List Selection :=
  let typed (picker : Bool) : Editing := { text := "ab", caret := 1, picker }
  let fresh : CellId := cell! "5e1ec7ed00000000000000000000abcd"
  match o.kind with
  | .value => [{ path := o.path, editing := some (typed false) }, { path := o.path, editing := some (typed true) }]
  | .hole =>
    [{ path := o.path, stage := .pending, editing := some (typed true) },
     { path := o.path, editing := some (typed true) }, { path := o.path, stage := .pending }]
  | .insertion => [{ path := o.path, stage := .pending }, { path := o.path, stage := .pending, editing := some (typed true) }]
  | .fieldEnd =>
    [{ path := o.path, stage := .label, editing := some (typed false) },
     { path := o.path ++ [.key fresh], stage := .pending },
     { path := o.path ++ [.key Kinds.returns], stage := .pending, editing := some (typed true) },
     { path := o.path ++ [.key Kinds.type_], stage := .pending }]
  | .label => [{ path := o.path, stage := .pending }]
  | .entryPoint =>
    [{ path := Display.entriesPath ++ [.element [7, 7, 7]], stage := .pending, anchor := some o.path },
     { path := Display.entriesPath ++ [.element [7, 7, 7]], stage := .pending, anchor := some o.path,
       editing := some (typed true) }]
  | .computed => []

/-- Which parts of a file the two draw the same: with nothing selected,
with each of the selections its occurrences give, and with what its
evaluations might have given; and where the first of the rest part ways. -/
def compare (path : String) (verbose : Bool) : IO Unit := do
  let text ← IO.FS.readFile path
  match ← GidText.parse text with
  | .error e => IO.println s!"{path}: {e}"
  | .ok d =>
    let parts := Display.entries d.root
    let mut same := 0
    let mut shown := 0
    let mut tried := 0
    let mut agreed := 0
    let mut given := 0
    let mut gave := 0
    for part in parts do
      let old := oldPart d.cells part
      let new := newPart d.cells part
      if decide (old = new) then same := same + 1
      else if verbose && shown < 3 then
        shown := shown + 1
        match (old.zip new).find? fun (a, b) => !decide (a = b) with
        | some (a, b) => IO.println s!"    grown:    {a.plain}\n    drawn:    {b.plain}"
        | none => IO.println s!"    {old.length} lines grown, {new.length} drawn"
      -- The selections its occurrences give: the first forty places, each kind of occurrence there.
      let occs := (old.flatMap fun l => l.cells.filterMap (·.occ)).foldl
        (fun (acc : List Occ) o => if acc.any (fun x => x.path == o.path && x.kind == o.kind) then acc else o :: acc) []
      for o in occs.reverse.take 40 do
        for sel in selectionsAt o do
          let oldS := oldPart d.cells part { selection := some sel }
          let newS := newPart d.cells part { selection := some sel }
          tried := tried + 1
          if agree (sel.stage == .label) oldS newS then agreed := agreed + 1
          else if verbose && shown < 6 then
            shown := shown + 1
            IO.println s!"    selected {repr sel.stage} at {sel.path.length} steps, {repr o.kind}:"
            match (oldS.zip newS).find? fun (a, b) => !decide (a = b) with
            | some (a, b) => IO.println s!"    grown:    {a.plain}\n    drawn:    {b.plain}"
            | none => IO.println s!"    {oldS.length} lines grown, {newS.length} drawn"
      -- What its evaluations might have given: a value, an error, an error about the expression, or a step in it.
      let expressions := (Display.item ((fun c => d.cells[c]?)) part).expressions
      if !expressions.isEmpty then
        for outcome in [Outcome.value "42" "Nat", .failed "it went wrong\n  here" none, .failed "wrong" (some []),
            .failed "wrong" (some [.key Kinds.function]), .failed "wrong" (some [.follow])] do
          let seen : Display.Seen := { results := expressions.map (·, outcome) }
          given := given + 1
          if decide (oldPart d.cells part seen = newPart d.cells part seen) then gave := gave + 1
          else if verbose && shown < 9 then
            shown := shown + 1
            match ((oldPart d.cells part seen).zip (newPart d.cells part seen)).find? fun (a, b) => !decide (a = b) with
            | some (a, b) => IO.println s!"    with results:\n    grown:    {a.plain}\n    drawn:    {b.plain}"
            | none => IO.println "    with results: other lines"
    IO.println s!"{path}: {same} of {parts.length} parts drawn the same; {agreed} of {tried} with something selected; {gave} of {given} with results"

def main (args : List String) : IO Unit := do
  for f in args.filter (·.endsWith ".gid") do compare f (args.contains "where")
