import Deui.Diff

/-!
A list of lists, joined: each element gives a list by `f`, and the lists are
joined end to end. Inserting an element inserts its list where the lists
before it end; deleting one deletes its list from there.
-/

namespace Deui.Lists

open Deui

variable {A B : Type}

theorem insert_take_drop (xs : List A) (i : Nat) (x : A) : insert xs i x = xs.take i ++ x :: xs.drop i := by
  induction xs generalizing i with
  | nil => simp [insert]
  | cons h t ih =>
    cases i with
    | zero => rfl
    | succ i => simp [insert, ih]

theorem remove_take_drop (xs : List A) (i : Nat) (b : A) (h : xs[i]? = some b) :
    xs = xs.take i ++ b :: xs.drop (i + 1) ∧ remove xs i = xs.take i ++ xs.drop (i + 1) := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x t ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨h1, h2⟩ := ih i h
      refine ⟨?_, ?_⟩
      · simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
        exact congrArg (x :: ·) h1
      · simp only [remove, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
        exact congrArg (x :: ·) h2

theorem inserts_ok' (ca : EditStructure) (pre ys suf l l' : List ca.Value) (h1 : l = pre ++ suf)
    (h2 : l' = pre ++ ys ++ suf) : patch ca (inserts ca pre.length ys) l = l' := by
  subst h1; subst h2; exact inserts_ok ca pre ys suf

theorem deletes_ok' (ca : EditStructure) (pre mid suf l l' : List ca.Value) (h1 : l = pre ++ mid ++ suf)
    (h2 : l' = pre ++ suf) : patch ca (deletes ca pre.length mid.length) l = l' := by
  subst h1; subst h2; exact deletes_ok ca pre mid suf

variable (f : B → List A)

/-- The edits to the joined list that one edit of the list of elements
makes, given the elements before it. -/
def flat.edit (xss : List B) : Edit.of (plain B) → List (Edit.of (plain A))
  | .insert i b => inserts (plain A) ((xss.take i).flatMap f).length (f b)
  | .delete i =>
    match xss[i]? with
    | .none => []
    | .some b => deletes (plain A) ((xss.take i).flatMap f).length (f b).length
  | .update _ d => nomatch d

/-- Joining, for one edit at a time. -/
def flat.one : Inc (editStructure (plain B)) (runs (editStructure (plain A))) :=
  ⟨fun xss => xss.flatMap f, flat.edit f⟩

/-- Joining, as an incremental function of runs of edits. -/
def flat.inc : Inc (runs (editStructure (plain B))) (runs (editStructure (plain A))) :=
  lift (flat.one f)

theorem flat_insert (xss : List B) (i : Nat) (b : B) :
    patch (plain A) (inserts (plain A) ((xss.take i).flatMap f).length (f b)) (xss.flatMap f) =
      (insert xss i b).flatMap f := by
  have hs : xss.flatMap f = (xss.take i).flatMap f ++ (xss.drop i).flatMap f := by
    rw [← List.flatMap_append, List.take_append_drop]
  have ht : (insert xss i b).flatMap f = (xss.take i).flatMap f ++ f b ++ (xss.drop i).flatMap f := by
    rw [insert_take_drop, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  exact inserts_ok' (plain A) _ _ _ _ _ hs ht

theorem flat_delete (xss : List B) (i : Nat) :
    patch (plain A) (flat.edit f xss (.delete i)) (xss.flatMap f) = (remove xss i).flatMap f := by
  cases hb : xss[i]? with
  | none =>
    have hl : xss.length ≤ i := by
      rcases Nat.lt_or_ge i xss.length with hlt | hge
      · simp [List.getElem?_eq_getElem hlt] at hb
      · exact hge
    simp only [flat.edit, hb]
    rw [Scrolled.remove_past xss i hl]
    rfl
  | some b =>
    obtain ⟨h1, h2⟩ := remove_take_drop xss i b hb
    have hs : xss.flatMap f = (xss.take i).flatMap f ++ f b ++ (xss.drop (i + 1)).flatMap f := by
      conv => lhs; rw [h1]
      rw [List.flatMap_append, List.flatMap_cons, List.append_assoc]
    have ht : (remove xss i).flatMap f = (xss.take i).flatMap f ++ (xss.drop (i + 1)).flatMap f := by
      rw [h2, List.flatMap_append]
    simp only [flat.edit, hb]
    exact deletes_ok' (plain A) _ _ _ _ _ hs ht

theorem flat_one_ok : (flat.one f).ok := by
  intro xss e
  cases e with
  | insert i b => exact flat_insert f xss i b
  | delete i => exact flat_delete f xss i
  | update _ d => exact nomatch d

theorem flat_inc_ok : (flat.inc f).ok := lift_ok _ (flat_one_ok f)

/-! ## Joining, by what changed -/

section
variable {cb : EditStructure} {A : Type} (f : cb.Value → List A)
variable (sameB : cb.Value → cb.Value → Bool) (reflB : ∀ b, sameB b b = true) (sameA : A → A → Bool)

/-- The edits to the joined list for a run of edits to the elements, from
the elements before it, and the elements after. The elements that changed
are found by comparing the lists, and their joined lists compared in turn:
an element replaced by one whose list is mostly the same makes edits only
where the lists differ, and no element changed is no work. -/
def flatChange.df (xss : List cb.Value) (es : List (Edit.of cb)) : List (Edit.of (plain A)) × List cb.Value :=
  let yss := patch cb es xss
  if alike sameB reflB xss yss then ([], yss)
  else
    let r := frame sameB xss yss
    (changeAt (plain A) sameA (r.1.map fun b => (f b).length).sum (r.2.1.flatMap f) (r.2.2.1.flatMap f), yss)

/-- Joining, with a derivative that compares: it keeps the elements. -/
def flatChange : Cached (runs (editStructure cb)) (runs (editStructure (plain A))) :=
  ⟨List cb.Value, fun xss => (xss.flatMap f, xss), flatChange.df f sameB reflB sameA⟩

theorem flatChange_df (soundB : ∀ a b, sameB a b = true → a = b) (soundA : ∀ a b, sameA a b = true → a = b)
    (xss : List cb.Value) (es : List (Edit.of cb)) :
    patch (plain A) (flatChange.df f sameB reflB sameA xss es).1 (xss.flatMap f) =
        (patch cb es xss).flatMap f ∧
      (flatChange.df f sameB reflB sameA xss es).2 = patch cb es xss := by
  obtain ⟨fx, fy⟩ := frame_ok sameB soundB xss (patch cb es xss)
  have hx : xss.flatMap f = (frame sameB xss (patch cb es xss)).1.flatMap f ++
      (frame sameB xss (patch cb es xss)).2.1.flatMap f ++
      (frame sameB xss (patch cb es xss)).2.2.2.flatMap f := by
    conv => lhs; rw [fx]
    rw [List.flatMap_append, List.flatMap_append]
  have hy : (patch cb es xss).flatMap f = (frame sameB xss (patch cb es xss)).1.flatMap f ++
      (frame sameB xss (patch cb es xss)).2.2.1.flatMap f ++
      (frame sameB xss (patch cb es xss)).2.2.2.flatMap f := by
    conv => lhs; rw [fy]
    rw [List.flatMap_append, List.flatMap_append]
  have hl : ((frame sameB xss (patch cb es xss)).1.map fun b => (f b).length).sum =
      ((frame sameB xss (patch cb es xss)).1.flatMap f).length := by
    rw [List.length_flatMap]
  by_cases hc : alike sameB reflB xss (patch cb es xss) = true
  · have e : flatChange.df f sameB reflB sameA xss es = ([], patch cb es xss) := by
      simp only [flatChange.df, hc, ite_true]
    rw [e]
    refine ⟨?_, rfl⟩
    show xss.flatMap f = (patch cb es xss).flatMap f
    exact congrArg (List.flatMap f) (alike_sound sameB reflB soundB _ _ hc)
  · have e : flatChange.df f sameB reflB sameA xss es =
        (changeAt (plain A) sameA ((frame sameB xss (patch cb es xss)).1.map fun b => (f b).length).sum
          ((frame sameB xss (patch cb es xss)).2.1.flatMap f)
          ((frame sameB xss (patch cb es xss)).2.2.1.flatMap f), patch cb es xss) := by
      simp only [flatChange.df, hc]
      rfl
    rw [e]
    exact ⟨changeAt_ok' (plain A) sameA soundA _ _ _ _ _ _ _ hl hx hy, rfl⟩

theorem flatChange_ok (soundB : ∀ a b, sameB a b = true → a = b) (soundA : ∀ a b, sameA a b = true → a = b) :
    (flatChange f sameB reflB sameA).ok := by
  intro xss es
  obtain ⟨h1, h2⟩ := flatChange_df f sameB reflB sameA soundB soundA xss es
  exact Prod.ext h1 h2

end

/-! ## Joining, element by element -/

section
variable {cb : EditStructure} {A : Type} (f : cb.Value → List A) (sameA : A → A → Bool)

/-- How many joined elements come before the element at `i`. -/
def flatBy.offset (xss : List cb.Value) (i : Nat) : Nat := ((xss.take i).map fun b => (f b).length).sum

theorem flatBy.offset_eq (xss : List cb.Value) (i : Nat) :
    flatBy.offset f xss i = ((xss.take i).flatMap f).length := by
  rw [flatBy.offset, List.length_flatMap]

/-- The edits to the joined list that one edit of the elements makes: an
element inserted or deleted takes its list with it, and an element edited
makes the edits between the list it gave and the one it gives, where its
list is. -/
def flatBy.edit (xss : List cb.Value) : Edit.of cb → List (Edit.of (plain A))
  | .insert i b => inserts (plain A) (flatBy.offset f xss i) (f b)
  | .delete i =>
    match xss[i]? with
    | .none => []
    | .some b => deletes (plain A) (flatBy.offset f xss i) (f b).length
  | .update i d =>
    match xss[i]? with
    | .none => []
    | .some b => changeAt (plain A) sameA (flatBy.offset f xss i) (f b) (f (cb.apply d b))

/-- Joining, element by element, for one edit at a time. -/
def flatBy.one : Inc (editStructure cb) (runs (editStructure (plain A))) :=
  ⟨fun xss => xss.flatMap f, flatBy.edit f sameA⟩

/-- Joining, element by element, for runs of edits. -/
def flatBy.inc : Inc (runs (editStructure cb)) (runs (editStructure (plain A))) :=
  lift (flatBy.one f sameA)

theorem update_take_drop (xss : List cb.Value) (i : Nat) (b : cb.Value) (d : cb.Edit) (h : xss[i]? = some b) :
    update cb xss i d = xss.take i ++ cb.apply d b :: xss.drop (i + 1) := by
  induction xss generalizing i with
  | nil => simp at h
  | cons x t ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rfl
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      simp only [update, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      exact congrArg (x :: ·) (ih i h)

theorem length_le_of_getElem?_none (xss : List cb.Value) (i : Nat) (h : xss[i]? = none) : xss.length ≤ i := by
  rcases Nat.lt_or_ge i xss.length with hlt | hge
  · simp [List.getElem?_eq_getElem hlt] at h
  · exact hge

theorem flatBy_one_ok (sound : ∀ a b, sameA a b = true → a = b) : (flatBy.one f sameA).ok := by
  intro xss e
  cases e with
  | insert i b =>
    show patch (plain A) (inserts (plain A) (flatBy.offset f xss i) (f b)) (xss.flatMap f) =
      (insert xss i b).flatMap f
    have hs : xss.flatMap f = (xss.take i).flatMap f ++ (xss.drop i).flatMap f := by
      rw [← List.flatMap_append, List.take_append_drop]
    have ht : (insert xss i b).flatMap f = (xss.take i).flatMap f ++ f b ++ (xss.drop i).flatMap f := by
      rw [insert_take_drop, List.flatMap_append, List.flatMap_cons, List.append_assoc]
    rw [flatBy.offset_eq]
    exact inserts_ok' (plain A) _ _ _ _ _ hs ht
  | delete i =>
    show patch (plain A) (flatBy.edit f sameA xss (.delete i)) (xss.flatMap f) = (remove xss i).flatMap f
    cases hb : xss[i]? with
    | none =>
      simp only [flatBy.edit, hb]
      rw [Scrolled.remove_past xss i (length_le_of_getElem?_none xss i hb)]
      rfl
    | some b =>
      obtain ⟨h1, h2⟩ := remove_take_drop xss i b hb
      have hs : xss.flatMap f = (xss.take i).flatMap f ++ f b ++ (xss.drop (i + 1)).flatMap f := by
        conv => lhs; rw [h1]
        rw [List.flatMap_append, List.flatMap_cons, List.append_assoc]
      have ht : (remove xss i).flatMap f = (xss.take i).flatMap f ++ (xss.drop (i + 1)).flatMap f := by
        rw [h2, List.flatMap_append]
      simp only [flatBy.edit, hb]
      rw [flatBy.offset_eq]
      exact deletes_ok' (plain A) _ _ _ _ _ hs ht
  | update i d =>
    show patch (plain A) (flatBy.edit f sameA xss (.update i d)) (xss.flatMap f) = (update cb xss i d).flatMap f
    cases hb : xss[i]? with
    | none =>
      simp only [flatBy.edit, hb]
      rw [update_past xss i (length_le_of_getElem?_none xss i hb)]
      rfl
    | some b =>
      obtain ⟨h1, _⟩ := remove_take_drop xss i b hb
      have hs : xss.flatMap f = (xss.take i).flatMap f ++ f b ++ (xss.drop (i + 1)).flatMap f := by
        conv => lhs; rw [h1]
        rw [List.flatMap_append, List.flatMap_cons, List.append_assoc]
      have ht : (update cb xss i d).flatMap f =
          (xss.take i).flatMap f ++ f (cb.apply d b) ++ (xss.drop (i + 1)).flatMap f := by
        rw [update_take_drop xss i b d hb, List.flatMap_append, List.flatMap_cons, List.append_assoc]
      simp only [flatBy.edit, hb]
      exact changeAt_ok' (plain A) sameA sound _ _ _ _ _ _ _ (flatBy.offset_eq f xss i) hs ht

theorem flatBy_inc_ok (sound : ∀ a b, sameA a b = true → a = b) : (flatBy.inc f sameA).ok :=
  lift_ok _ (flatBy_one_ok f sameA sound)

end

end Deui.Lists
