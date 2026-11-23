import Progred.Run

/-! Lean built as data and run at run time, through `Progred.Run`. -/

open Lean Progred.Run

unsafe def main : IO Unit := do
  let t0 ← IO.monoMsNow
  let rt ← Runtime.load
  let t1 ← IO.monoMsNow
  IO.println s!"loaded Init in {t1 - t0} ms"
  let f := mkIdent `f
  let x := mkIdent `x
  let built ← run rt.env do
    let defn ← `(command| def $f ($x : Nat) : Nat := $x + 1)
    let call ← `($f 41)
    let list ← `([1, 2, 3].map $f)
    let bad : TSyntax `term := ⟨tagOuter 3 (← `(Nat.add 1 $(⟨tagged 7 (Syntax.mkStrLit "no")⟩)))⟩
    return (defn, call, list, bad)
  let (.ok (defn, call, list, bad), _) := built | throw (IO.userError "couldn't build the syntax")
  for t in [call.raw, list.raw, f.raw, bad.raw] do
    match ← rt.eval #[defn] t with
    | .ok s => IO.println s!"{s.value} : {s.type}"
    | .error ps => for p in ps do IO.println s!"error at node {p.node}: {((p.message.take 50).toString.replace "\n" " ")}"
  IO.println s!"built, elaborated and ran in {(← IO.monoMsNow) - t1} ms"
