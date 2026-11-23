import Progred.Editor
open Progred
/-- How long laying a file out, and making its rows, takes. -/
def main (args : List String) : IO Unit := do
  for path in args do
    match ← GidText.parse (← IO.FS.readFile path) with
    | .error e => IO.println s!"{path}: {e}"
    | .ok d =>
      let m : Model := { doc := d }
      let t0 ← IO.monoNanosNow
      let mut lines := 0
      let mut rows := 0
      for i in [0:20] do
        let m := { m with scroll := i }
        lines := lines + m.laid.1.size
        rows := rows + (Editor.rows m).length
      let t1 ← IO.monoNanosNow
      IO.println s!"{path}: {lines / 20} lines; layout and rows {(t1 - t0) / 20 / 1000} µs per event"
