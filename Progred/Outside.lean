import Progred.Editor
import Progred.Skinny

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

/-- A message with the Lean names of the document's cells, `p_` or `d_` and
the cell's id, as the cells are shown. -/
def named (m : Model) (message : String) : String := Id.run do
  let chars := message.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < chars.size do
    let c := chars[i]!
    let boundary := i == 0 || !(chars[i - 1]!.isAlphanum || chars[i - 1]! == '_')
    if boundary && (c == 'p' || c == 'd') && chars[i + 1]? == some '_' && i + 34 ≤ chars.size then
      match CellId.ofHex? (String.ofList (chars.extract (i + 2) (i + 34)).toList) with
      | some id =>
        out := out ++ m.doc.shown m.library id
        i := i + 34
        continue
      | none => pure ()
    out := out.push c
    i := i + 1
  return out

/-- What each evaluation in the document gives. -/
unsafe def evaluate (rt : Run.Runtime) (memo : Memo) (m : Model) : IO (List (Value × Outcome)) := do
  let known ← memo.get
  let mut results := []
  let mut kept := []
  for e in Skinny.expressions m.doc do
    match Skinny.convert m.doc m.library e with
    | .error f => results := results ++ [(e, Outcome.failed f.message)]
    | .ok (commands, term, nodes) =>
      let key := String.join (commands.toList.map toString) ++ " ⊢ " ++ toString term
      let outcome ← match known.find? (·.1 == key) with
        | some (_, o) => pure o
        | none =>
          match ← rt.eval commands term with
          | .ok s => pure (Outcome.value s.value s.type)
          | .error ps =>
            let at_ := (ps.head?.bind fun p => nodes[p.node - 1]?).join
            pure (Outcome.failed (named m ((ps.head?.map (·.message)).getD "it failed")) (if (ps.head?.map (·.node)).getD 0 == 0 then none else at_))
      results := results ++ [(e, outcome)]
      kept := (key, outcome) :: kept
  memo.set kept
  return results

/-- A clipboard: the window's, or one that stands in for it. -/
structure Clipboard where
  set : String → IO Unit
  get : IO String

/-- A clipboard that's only a place in memory, for running with no window. -/
def Clipboard.inMemory : IO Clipboard := do
  let held ← IO.mkRef ""
  return ⟨held.set, held.get⟩

/-- The edits from outside, for a model: ids topped up, what was copied put
on the clipboard, a paste asked for read from it, evaluations run if the
document changed, the file written if a save was asked. -/
unsafe def edits (rt : Run.Runtime) (memo : Memo) (file : Option System.FilePath) (clipboard : Clipboard)
    (m : Model) : IO (List (Whole (plain Model))) := do
  let mut m' := m
  let mut changed := false
  if m.ids.length < 32 then
    let more ← (List.range 64).mapM fun _ => CellId.new
    m' := { m' with ids := m'.ids ++ more }
    changed := true
  if let some text := m.copied then
    clipboard.set text
    m' := { m' with copied := none }
    changed := true
  if m.pasteAsked then
    let text ← clipboard.get
    let clip ←
      if text.trimAscii.startsWith "{" then
        match ← GidText.parse text with
        | .ok d => pure (some d)
        | .error _ => pure none
      else pure none
    m' := { Model.pasted { m' with pasteAsked := false } text clip with reveal := true }
    changed := true
  if m'.stale then
    m' := { m' with results := ← evaluate rt memo m', stale := false }
    changed := true
  if m.saveAsked then
    if let some path := file then
      IO.FS.writeFile path (GidText.write m.doc m.library)
      m' := { m' with dirty := false }
    m' := { m' with saveAsked := false }
    changed := true
  return if changed then [.replace m'] else []

end Progred.Outside
