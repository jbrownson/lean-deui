import Lean

/-!
Running Lean at run time, from syntax built as data: no text is parsed.
Definitions are elaborated into an environment loaded once, and a term is
evaluated to its value and type as text. A syntax node carries the id of
the editor node it came from in place of a place in a file, so an error
comes back with the id of the node it's about.
-/

namespace Progred.Run

open Lean Elab Command Term Meta

/-- An error, at the editor node whose syntax it's about (0 if none). -/
structure Problem where
  node : Nat
  message : String
  deriving Repr, Inhabited

/-- A syntax tree with every node's position set to `id`. -/
partial def tagged (id : Nat) (stx : Syntax) : Syntax :=
  let info := SourceInfo.synthetic ⟨id⟩ ⟨id⟩
  match stx with
  | .node _ k args => .node info k (args.map (tagged id))
  | .atom _ v => .atom info v
  | .ident _ r v p => .ident info r v p
  | .missing => .missing

/-- A syntax tree's nodes with no position yet, given `id`; nodes that
already have one keep it, so a part tagged earlier stays its own. -/
partial def tagOuter (id : Nat) (stx : Syntax) : Syntax :=
  let info := SourceInfo.synthetic ⟨id⟩ ⟨id⟩
  let fresh : SourceInfo → SourceInfo
    | .none => info
    | i => i
  match stx with
  | .node i k args => .node (fresh i) k (args.map (tagOuter id))
  | .atom i v => .atom (fresh i) v
  | .ident i r v p => .ident (fresh i) r v p
  | .missing => .missing

/-- Lean's core library, loaded. -/
structure Runtime where
  env : Environment

/-- Loads Lean's core library, from the toolchain this program was built
with. Takes a few hundred milliseconds. -/
unsafe def Runtime.load : IO Runtime := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  return ⟨← importModules #[{ module := `Init }] {} (loadExts := true)⟩

/-- One long line stands in for a source file, so a position's column is the
node id it was tagged with. -/
def context : Command.Context :=
  { fileName := "<progred>", fileMap := FileMap.ofString ("".pushn ' ' 1000000), snap? := none, cancelTk? := none }

def problems (msgs : List Message) : IO (List Problem) :=
  msgs.filterMapM fun m => do
    if m.severity matches .error then
      return some ⟨m.pos.column, ← m.data.toString⟩
    else return none

/-- Runs a command action in an environment: its result, or the problems it
logged or threw, and the environment after. -/
def run (env : Environment) (x : CommandElabM α) : IO (Except (List Problem) α × Environment) := do
  let st : Command.State := Command.mkState env {} {}
  match (← (x context |>.run st).toBaseIO) with
  | .ok (a, st) =>
    let ps ← problems st.messages.toList
    return (if ps.isEmpty then .ok a else .error ps, st.env)
  | .error e =>
    let pos := (e.getRef.getPos?.map (·.byteIdx)).getD 0
    return (.error [⟨pos, ← e.toMessageData.toString⟩], env)

/-- A value and its type, as text. -/
structure Shown where
  value : String
  type : String
  deriving Repr, Inhabited

/-- Elaborates the commands in order, then evaluates the term: its value,
by its `Repr` or `ToString`, and its type. A function has no value to show,
only its type. -/
unsafe def Runtime.eval (rt : Runtime) (commands : Array Syntax) (term : Syntax) :
    IO (Except (List Problem) Shown) := do
  let mut env := rt.env
  for c in commands do
    let (r, env') ← run env (elabCommand c)
    match r with
    | .ok () => env := env'
    | .error ps => return .error ps
  let (r, _) ← run env <| liftTermElabM <| withoutErrToSorry do
    let t : TSyntax `term := ⟨term⟩
    let e ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasExprMVar then
      throwErrorAt term "this doesn't have a definite type: its parts don't fit together"
    let type ← instantiateMVars (← inferType e)
    let typeText := toString (← ppExpr type)
    if (← whnf type).isForall then
      return (⟨"", typeText⟩ : Shown)
    -- By Repr if there is one, else by ToString.
    let shown ←
      try
        let s ← elabTerm (← `(toString (repr $t))) (some (mkConst ``String))
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars s
      catch _ =>
        let s ← elabTerm (← `(toString $t)) (some (mkConst ``String))
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars s
    return ⟨← evalExpr String (mkConst ``String) shown, typeText⟩
  return r

end Progred.Run
