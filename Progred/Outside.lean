import Progred.Editor
import Progred.Lean

/-!
What reaches the editor from outside its pure update: fresh cell ids, what
evaluations give, and the file written when a save is asked. The window's
loop asks for these after each batch of events, and they go into the model
as edits like any other.
-/

namespace Progred.Outside

open Progred Deui

/-- What an expression gave, remembered by the Lean it became, so an edit
elsewhere doesn't run it again. -/
abbrev Memo := IO.Ref (List (String × Outcome))

/-- What each evaluation in the document gives. -/
unsafe def evaluate (rt : Run.Runtime) (memo : Memo) (m : Model) : IO (List (Value × Outcome)) := do
  let known ← memo.get
  let mut results := []
  let mut kept := []
  for e in ToLean.expressions m.doc do
    match ToLean.convert m.doc m.library e with
    | .error f => results := results ++ [(e, Outcome.failed f.message)]
    | .ok (commands, term) =>
      let key := String.join (commands.toList.map toString) ++ " ⊢ " ++ toString term
      let outcome ← match known.find? (·.1 == key) with
        | some (_, o) => pure o
        | none =>
          match ← rt.eval commands term with
          | .ok s => pure (Outcome.value s.value s.type)
          | .error ps => pure (Outcome.failed ((ps.head?.map (·.message)).getD "it failed"))
      results := results ++ [(e, outcome)]
      kept := (key, outcome) :: kept
  memo.set kept
  return results

/-- The edits from outside, for a model: ids topped up, evaluations run if
the document changed, the file written if a save was asked. -/
unsafe def edits (rt : Run.Runtime) (memo : Memo) (file : Option System.FilePath) (m : Model) :
    IO (List (Whole (plain Model))) := do
  let mut m' := m
  let mut changed := false
  if m.ids.length < 32 then
    let more ← (List.range 64).mapM fun _ => CellId.new
    m' := { m' with ids := m'.ids ++ more }
    changed := true
  if m.stale then
    m' := { m' with results := ← evaluate rt memo m, stale := false }
    changed := true
  if m.saveAsked then
    if let some path := file then
      IO.FS.writeFile path (GidText.write m.doc m.library)
      m' := { m' with dirty := false }
    m' := { m' with saveAsked := false }
    changed := true
  return if changed then [.replace m'] else []

end Progred.Outside
