import Progred.Gid

/-!
What a write does to a value, a step at a time: the value a step in is the
one written, and every other step leads where it did. It's what lets a
write be followed down to the one place it lands.
-/

namespace Progred.Value

/-- A value with what's along steps written, or taken away with none to
write; none if the steps lead nowhere. -/
def put (v : Value) (rel : List Step) : Option Value → Option Value
  | some new => v.set rel new
  | none => v.without rel

/-- The value after a write, or as it was if the steps led nowhere. -/
def written (v : Value) (rel : List Step) (w : Option Value) : Value := (v.put rel w).getD v

theorem find_setField_same (fields : List (CellId × Value)) (label : CellId) (x : Value) :
    (setField fields label x).find? (·.1 == label) = some (label, x) := by
  induction fields with
  | nil => simp [setField]
  | cons f rest ih =>
    obtain ⟨l, w⟩ := f
    simp only [setField]
    cases h : compare label l with
    | lt => simp
    | eq => simp
    | gt =>
      have ne : l ≠ label := fun e => by
        have := (Std.LawfulEqCmp.compare_eq_iff_eq (cmp := (compare : CellId → CellId → Ordering))
          (a := label) (b := l)).mpr e.symm
        rw [this] at h
        cases h
      simp [ne, ih]

theorem find_setField_other (fields : List (CellId × Value)) (label : CellId) (x : Value) (l : CellId)
    (hne : l ≠ label) : (setField fields label x).find? (·.1 == l) = fields.find? (·.1 == l) := by
  induction fields with
  | nil => simp [setField, Ne.symm hne]
  | cons f rest ih =>
    obtain ⟨l0, w⟩ := f
    simp only [setField]
    cases h : compare label l0 with
    | lt => simp [Ne.symm hne]
    | eq =>
      have e : label = l0 := Std.LawfulEqCmp.eq_of_compare h
      subst e
      simp [Ne.symm hne]
    | gt =>
      by_cases e : l0 = l
      · simp [e]
      · simp [e, ih]

theorem find_setElement_same (items : List (Position × Value)) (p : Position) (x : Value) :
    (setElement items p x).find? (·.1 == p) = some (p, x) := by
  induction items with
  | nil => simp [setElement]
  | cons f rest ih =>
    obtain ⟨q, w⟩ := f
    simp only [setElement]
    by_cases h : (p == q) = true
    · simp [h]
    · have h' : (p == q) = false := by simpa using h
      have hne : q ≠ p := fun e => h (by simp [e])
      simp only [h']
      by_cases hlt : Position.lt p q = true
      · simp [hlt]
      · simp [hlt, hne, ih]

theorem find_setElement_other (items : List (Position × Value)) (p : Position) (x : Value) (r : Position)
    (hne : r ≠ p) : (setElement items p x).find? (·.1 == r) = items.find? (·.1 == r) := by
  induction items with
  | nil => simp [setElement, Ne.symm hne]
  | cons f rest ih =>
    obtain ⟨q, w⟩ := f
    simp only [setElement]
    by_cases h : (p == q) = true
    · have e : p = q := by simpa using h
      subst e
      simp [Ne.symm hne]
    · have h' : (p == q) = false := by simpa using h
      simp only [h']
      by_cases hlt : Position.lt p q = true
      · simp [hlt, Ne.symm hne]
      · by_cases e : q = r
        · subst e
          simp [hlt]
        · simp [hlt, e, ih]

/-- After a step is set, the value that step in is the one set. -/
theorem step_setStep_same (v : Value) (s : Step) (x v' : Value) (h : v.setStep s x = some v') :
    v'.step? s = some x := by
  cases v <;> cases s <;> simp only [setStep, Option.some.injEq, reduceCtorEq] at h
  · subst h
    simp [step?, find_setElement_same]
  · subst h
    simp [step?, field?, find_setField_same]

/-- And every other step leads where it did. -/
theorem step_setStep_other (v : Value) (s : Step) (x v' : Value) (h : v.setStep s x = some v') (st : Step)
    (hne : st ≠ s) : v'.step? st = v.step? st := by
  cases v <;> cases s <;> simp only [setStep, Option.some.injEq, reduceCtorEq] at h
  · subst h
    cases st with
    | key l => rfl
    | element q => simp [step?, find_setElement_other _ _ _ q (fun e => hne (by rw [e]))]
    | follow => rfl
  · subst h
    cases st with
    | key l => simp [step?, field?, find_setField_other _ _ _ l (fun e => hne (by rw [e]))]
    | element q => rfl
    | follow => rfl

/-- A value a step can be set in isn't a cell, before or after. -/
theorem setStep_not_cell (v : Value) (s : Step) (x v' : Value) (h : v.setStep s x = some v') :
    (∀ c, v ≠ .cell c) ∧ ∀ c, v' ≠ .cell c := by
  cases v <;> cases s <;> simp only [setStep, Option.some.injEq, reduceCtorEq] at h
  · subst h
    refine ⟨?_, ?_⟩ <;> intro c e <;> cases e
  · subst h
    refine ⟨?_, ?_⟩ <;> intro c e <;> cases e

/-- A write more than a step in is a write in the value a step in, set
back where it was. -/
theorem put_deep (v : Value) (s r : Step) (rest : List Step) (w : Option Value) (v' : Value)
    (h : v.put (s :: r :: rest) w = some v') :
    ∃ c c', v.step? s = some c ∧ c.put (r :: rest) w = some c' ∧ v.setStep s c' = some v' := by
  cases w with
  | some new =>
    simp only [put, set, bind, Option.bind] at h
    cases hc : v.step? s with
    | none => simp [hc] at h
    | some c =>
      rw [hc] at h
      simp only at h
      cases hi : c.set (r :: rest) new with
      | none => simp [hi] at h
      | some c' =>
        rw [hi] at h
        exact ⟨c, c', rfl, by simp [put, hi], h⟩
  | none =>
    simp only [put, without, bind, Option.bind] at h
    cases hc : v.step? s with
    | none => simp [hc] at h
    | some c =>
      rw [hc] at h
      simp only at h
      cases hi : c.without (r :: rest) with
      | none => simp [hi] at h
      | some c' =>
        rw [hi] at h
        exact ⟨c, c', rfl, by simp [put, hi], h⟩

end Progred.Value
