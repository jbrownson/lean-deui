import Progred.GidText
open Progred
def main (args : List String) : IO Unit := do
  for path in args do
    let text ← IO.FS.readFile path
    match ← GidText.parse text with
    | .error e => IO.println s!"{path}: {e}"
    | .ok d =>
      let out := GidText.write d []
      match ← GidText.parse out with
      | .error e => IO.println s!"{path}: reread failed: {e}"
      | .ok d2 =>
        let same := d.root == d2.root && d.cells.toList == d2.cells.toList
        IO.println s!"{path}: {d.cells.size} cells, {out.length} characters, round trip {if same then "same" else "DIFFERENT"}"
