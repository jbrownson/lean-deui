import Progred.Model
open Progred
def main (args : List String) : IO Unit := do
  for path in args do
    match ← GidText.parse (← IO.FS.readFile path) with
    | .error e => IO.println s!"{path}: {e}"
    | .ok d =>
      let l := Model.Layout.of { doc := d, width := 752 }
      let occs := l.parts.foldl (fun n p => n + (Model.stops p).length) 0
      IO.println s!"== {path}: {l.lineCount} lines in {l.parts.length} parts, {occs} occurrences"
      for line in l.plain.take 45 do IO.println line
