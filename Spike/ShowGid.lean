import Progred.Display
open Progred
def main (args : List String) : IO Unit := do
  for path in args do
    match ← GidText.parse (← IO.FS.readFile path) with
    | .error e => IO.println s!"{path}: {e}"
    | .ok d =>
      let (lines, occs) := Display.laid { doc := d, library := Builtin.library } 80
      IO.println s!"== {path}: {lines.size} lines, {occs.size} occurrences"
      for l in lines.toList.take 45 do IO.println l.plain
