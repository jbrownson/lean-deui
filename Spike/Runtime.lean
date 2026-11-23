import Lean

/-! A spike: Lean syntax built as data (no text), elaborated and run at run
time, with errors traced back to node ids carried as source positions. -/

open Lean Elab Command Term Meta

/-- Runs a command action in an environment, giving its result, the new
environment and the messages it logged. -/
def runCommand (env : Environment) (x : CommandElabM α) :
    IO (Except String α × Environment × List Message) := do
  -- One long line stands in for a source file, so a position's column is
  -- the node id it was tagged with.
  let ctx : Command.Context :=
    { fileName := "<progred>", fileMap := FileMap.ofString ("".pushn ' ' 100000), snap? := none, cancelTk? := none }
  let st : Command.State := Command.mkState env {} {}
  match (← (x ctx |>.run st).toBaseIO) with
  | .ok (a, st) => return (.ok a, st.env, st.messages.toList)
  | .error e => return (.error (← e.toMessageData.toString), st.env, [])

/-- A syntax tree with every node's position set to `id`: the node's id in
the editor, in place of a place in a file. -/
partial def tagged (id : Nat) (stx : Syntax) : Syntax :=
  let info := SourceInfo.synthetic ⟨id⟩ ⟨id⟩
  match stx with
  | .node _ k args => .node info k (args.map (tagged id))
  | .atom _ v => .atom info v
  | .ident _ r v p => .ident info r v p
  | .missing => .missing

unsafe def main : IO Unit := do
  let t0 ← IO.monoMsNow
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {} (loadExts := true)
  let t1 ← IO.monoMsNow
  IO.println s!"loaded Init in {t1 - t0} ms"
  -- `def f (x : Nat) : Nat := x + 1`, built from pieces, no text parsed.
  let name := mkIdent `f
  let arg := mkIdent `x
  let body ← runCommand env do
    let one : TSyntax `term := Syntax.mkNumLit "1"
    let sum ← `($arg + $one)
    `(command| def $name ($arg : Nat) : Nat := $sum)
  let (.ok defn, _, _) := body | throw (IO.userError "couldn't build the definition")
  let (r, env, msgs) ← runCommand env (elabCommand defn)
  for m in msgs do IO.println s!"message: {← m.toString}"
  let .ok () := r | throw (IO.userError "couldn't elaborate the definition")
  -- Evaluate `f 41`.
  let (r, _, _) ← runCommand env <| liftTermElabM do
    let stx ← `($name 41)
    let e ← elabTerm stx (some (mkConst ``Nat))
    let e ← instantiateMVars e
    evalExpr Nat (mkConst ``Nat) e
  match r with
  | .ok n => IO.println s!"f 41 = {n}"
  | .error e => IO.println s!"evaluation failed: {e}"
  let t2 ← IO.monoMsNow
  IO.println s!"built, elaborated and ran in {t2 - t1} ms"
  -- A type error, with node ids as positions: the string literal is node 7.
  let bad ← runCommand env do
    let s : TSyntax `term := ⟨tagged 7 (Syntax.mkStrLit "no")⟩
    let lhs : TSyntax `term := ⟨tagged 5 (Syntax.mkNumLit "1")⟩
    let sum : TSyntax `term := ⟨tagged 3 (← `(Nat.add $lhs $s))⟩
    `(command| def $(mkIdent `g) : Nat := $sum)
  let (.ok badDef, _, _) := bad | throw (IO.userError "couldn't build the bad definition")
  let (_, _, msgs) ← runCommand env (elabCommand badDef)
  for m in msgs do
    IO.println s!"error at node {m.pos.column}: {((← m.data.toString).take 60).toString.replace "\n" " "}"
