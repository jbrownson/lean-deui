import Progred.Model
import Deui.Scroll

/-!
The document's parts, as a list that the model's edits edit: an entry
written is its part replaced, an entry added or taken away is a part
inserted or deleted, where it is among the entries, and a new root is the
parts taken out and the new ones put in. Nothing is compared: an edit says
which part it's of.
-/

namespace Progred.Entries

open Progred Deui Display

/-- The parts' edit structure: a part is replaced whole. -/
abbrev Parts : EditStructure := whole (plain Entry)

def part (x : Position × Value) : Entry := .entry x.1 x.2

theorem entries_some (root : Option Value) (items : List (Position × Value))
    (h : notebookEntries? root = some items) : entries root = items.map part ++ [.end_] := by
  have e : (fun x : Position × Value => match x with | (p, w) => Entry.entry p w) = part := by
    funext x; cases x; rfl
  simp only [entries, h]
  rw [e]

theorem entries_none (root : Option Value) (h : notebookEntries? root = none) : entries root = [.whole root] := by
  simp only [entries, h]

/-- Fields with one rewritten keep their labels, so a field found by its
label is the rewritten one found. -/
theorem find_map (fields : List (CellId × Value)) (f : CellId × Value → CellId × Value)
    (hf : ∀ x, (f x).1 = x.1) (k : CellId) :
    (fields.map f).find? (·.1 == k) = (fields.find? (·.1 == k)).map f := by
  induction fields with
  | nil => rfl
  | cons x t ih =>
    simp only [List.map, List.find?, hf]
    cases x.1 == k <;> simp [ih]

theorem entries_ne_isa : (Kinds.entries == Kinds.isa) = false := by decide

/-- A value is a notebook with entries: its kind is notebook, and its
entries field is that list. -/
theorem notebook_iff (v : Value) (items : List (Position × Value)) :
    notebookEntries? (some v) = some items ↔
      v.kind? = some Kinds.notebook ∧ v.field? Kinds.entries = some (.list items) := by
  simp only [notebookEntries?]
  constructor
  · intro h
    by_cases hk : (v.kind? == some Kinds.notebook) = true
    · simp only [hk, ite_true] at h
      cases hf : v.field? Kinds.entries with
      | none => simp [hf] at h
      | some w =>
        cases w with
        | list its =>
          simp only [hf, Option.some.injEq] at h
          exact ⟨by simpa using hk, by rw [h]⟩
        | cell _ => simp [hf] at h
        | blob _ => simp [hf] at h
        | record _ => simp [hf] at h
    · simp [hk] at h
  · intro ⟨hk, hf⟩
    simp [hk, hf]

/-- A root notebook with its entries replaced is a notebook with those
entries. -/
theorem notebookEntries_withEntries (root : Option Value) (old items : List (Position × Value))
    (h : notebookEntries? root = some old) : notebookEntries? (Model.withEntries root items) = some items := by
  cases root with
  | none => simp [notebookEntries?] at h
  | some v =>
    obtain ⟨hk0, hf0⟩ := (notebook_iff v old).mp h
    cases v with
    | record fields =>
      let f : CellId × Value → CellId × Value := fun x => if x.1 == Kinds.entries then (x.1, Value.list items) else x
      have hf : ∀ x, (f x).1 = x.1 := by intro x; simp only [f]; split <;> rfl
      -- The kind is found as it was, and the entries are the new ones.
      have hk : ((fields.map f).find? (·.1 == Kinds.isa)).map (·.2) = (fields.find? (·.1 == Kinds.isa)).map (·.2) := by
        rw [find_map fields f hf]
        cases hfound : fields.find? (·.1 == Kinds.isa) with
        | none => rfl
        | some x =>
          have hx : (x.1 == Kinds.isa) = true :=
            List.find?_some (p := fun y : CellId × Value => y.1 == Kinds.isa) hfound
          have : x.1 = Kinds.isa := by simpa using hx
          simp only [Option.map, f, this, show (Kinds.isa == Kinds.entries) = false by decide]
          rfl
      have he : ((fields.map f).find? (·.1 == Kinds.entries)).map (·.2) = some (Value.list items) := by
        rw [find_map fields f hf]
        cases hfound : fields.find? (·.1 == Kinds.entries) with
        | none => simp [Value.field?, hfound] at hf0
        | some x =>
          have hx : (x.1 == Kinds.entries) = true :=
            List.find?_some (p := fun y : CellId × Value => y.1 == Kinds.entries) hfound
          simp only [Option.map, f, hx, ite_true]
      have hkind : (Value.record (fields.map f)).kind? = some Kinds.notebook := by
        rw [← hk0]
        simp only [Value.kind?, Value.field?, hk]
      show notebookEntries? (some (Value.record (fields.map f))) = some items
      exact (notebook_iff _ items).mpr ⟨hkind, by simp only [Value.field?, he]⟩
    | cell _ => simp [Value.field?] at hf0
    | blob _ => simp [Value.field?] at hf0
    | list _ => simp [Value.field?] at hf0

theorem entries_changed (root : Option Value) (items : List (Position × Value))
    (f : List (Position × Value) → List (Position × Value)) (h : notebookEntries? root = some items) :
    entries (Model.entriesChanged root f) = (f items).map part ++ [.end_] := by
  simp only [Model.entriesChanged, h]
  exact entries_some _ _ (notebookEntries_withEntries root items (f items) h)

theorem entries_unchanged (root : Option Value) (f : List (Position × Value) → List (Position × Value))
    (h : notebookEntries? root = none) : Model.entriesChanged root f = root := by
  simp only [Model.entriesChanged, h]

theorem replaceAt_map (items : List (Position × Value)) (i : Nat) (v : Value) (x : Position × Value)
    (h : items[i]? = some x) (tail : List Entry) :
    (Model.replaceAt items i v).map part ++ tail =
      Lists.update Parts (items.map part ++ tail) i (.replace (.entry x.1 v)) := by
  induction items generalizing i with
  | nil => simp at h
  | cons y t ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      cases y
      rfl
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      cases y
      simp only [Model.replaceAt, List.map, List.cons_append, Lists.update]
      exact congrArg (_ :: ·) (ih i h)

theorem replaceAt_none (items : List (Position × Value)) (i : Nat) (v : Value) (h : items[i]? = none) :
    Model.replaceAt items i v = items := by
  induction items generalizing i with
  | nil => rfl
  | cons y t ih =>
    cases i with
    | zero => simp at h
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      cases y
      simp only [Model.replaceAt, ih i h]

/-- The edits one edit of the model makes to the parts, from the model
before it. -/
def edits (m : Model) : Model.Edit → List (Lists.Edit.of Parts)
  | .change (.entry i v) =>
    match notebookEntries? m.doc.root with
    | some items =>
      match items[i]? with
      | some x => [.update i (.replace (.entry x.1 v))]
      | none => []
    | none => []
  | .change (.entryIn i p v) =>
    match notebookEntries? m.doc.root with
    | some items => [.insert (min i items.length) (.entry p v)]
    | none => []
  | .change (.entryOut i) =>
    match notebookEntries? m.doc.root with
    | some items => if i < items.length then [.delete i] else []
    | none => []
  | .change (.root r) => Lists.diff Parts (entries m.doc.root) (entries r)
  | .change (.document d) => Lists.diff Parts (entries m.doc.root) (entries d.root)
  | _ => []

/-- They take the parts to the parts of the edited model. -/
theorem edits_ok (m : Model) (e : Model.Edit) :
    Lists.patch Parts (edits m e) (entries m.doc.root) = entries (e.apply m).doc.root := by
  cases e with
  | rest new => rfl
  | change c =>
    cases c with
    | entry i v =>
      show Lists.patch Parts (edits m (.change (.entry i v))) (entries m.doc.root) =
        entries (Model.entriesChanged m.doc.root fun items => Model.replaceAt items i v)
      cases hn : notebookEntries? m.doc.root with
      | none => simp only [edits, hn, entries_unchanged _ _ hn]; rfl
      | some items =>
        rw [entries_changed _ items _ hn, entries_some _ _ hn]
        cases hi : items[i]? with
        | none => simp only [edits, hn, hi, replaceAt_none items i v hi]; rfl
        | some x =>
          simp only [edits, hn, hi]
          exact (replaceAt_map items i v x hi [.end_]).symm
    | entryIn i p v =>
      show Lists.patch Parts (edits m (.change (.entryIn i p v))) (entries m.doc.root) =
        entries (Model.entriesChanged m.doc.root fun items => Lists.insert items (min i items.length) (p, v))
      cases hn : notebookEntries? m.doc.root with
      | none => simp only [edits, hn, entries_unchanged _ _ hn]; rfl
      | some items =>
        rw [entries_changed _ items _ hn, entries_some _ _ hn]
        simp only [edits, hn]
        show Lists.insert (items.map part ++ [.end_]) (min i items.length) (.entry p v) = _
        rw [Lists.Scrolled.insert_append_of_le _ _ _ _ (by simp; omega), Lists.map_insert]
        rfl
    | entryOut i =>
      show Lists.patch Parts (edits m (.change (.entryOut i))) (entries m.doc.root) =
        entries (Model.entriesChanged m.doc.root fun items => Lists.remove items i)
      cases hn : notebookEntries? m.doc.root with
      | none => simp only [edits, hn, entries_unchanged _ _ hn]; rfl
      | some items =>
        rw [entries_changed _ items _ hn, entries_some _ _ hn]
        by_cases hi : i < items.length
        · simp only [edits, hn, hi, ite_true]
          show Lists.remove (items.map part ++ [.end_]) i = _
          rw [Lists.Scrolled.remove_append_of_lt _ _ _ (by simpa using hi), Lists.map_remove]
        · simp only [edits, hn, hi, ite_false]
          rw [Lists.Scrolled.remove_past items i (by omega)]
          rfl
    | root r => exact Lists.diff_ok Parts _ _
    | document d => exact Lists.diff_ok Parts _ _
    | cell _ _ => rfl
    | select _ => rfl
    | folds _ => rfl
    | results _ => rfl
    | layouts _ => rfl
    | scroll _ => rfl
    | size _ _ => rfl

end Progred.Entries
