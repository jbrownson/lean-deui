import Deui.Spans

/-!
A list of lists, joined: each element gives a list by `f`, and the lists are
joined end to end. Inserting an element inserts its list where the lists
before it end; deleting one deletes its list from there; and an element
edited has its list taken out and the one it gives now put in.
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

section
variable {cb : EditStructure} {A : Type} (f : cb.Value → List A)

/-- How many joined elements come before the element at `i`. -/
def flatBy.offset (xss : List cb.Value) (i : Nat) : Nat := ((xss.take i).map fun b => (f b).length).sum

theorem flatBy.offset_eq (xss : List cb.Value) (i : Nat) :
    flatBy.offset f xss i = ((xss.take i).flatMap f).length := by
  rw [flatBy.offset, List.length_flatMap]

/-- The edits to the joined list that one edit of the elements makes: an
element inserted or deleted takes its list with it, and an element edited
has its list taken out and the list it gives now put in its place. -/
def flatBy.edit (xss : List cb.Value) : Edit.of cb → List (Edit.of (plain A))
  | .insert i b => inserts (plain A) (flatBy.offset f xss i) (f b)
  | .delete i =>
    match xss[i]? with
    | .none => []
    | .some b => deletes (plain A) (flatBy.offset f xss i) (f b).length
  | .update i d =>
    match xss[i]? with
    | .none => []
    | .some b =>
      deletes (plain A) (flatBy.offset f xss i) (f b).length ++
        inserts (plain A) (flatBy.offset f xss i) (f (cb.apply d b))

/-- Joining, element by element, for one edit at a time. -/
def flatBy.one : Inc (editStructure cb) (runs (editStructure (plain A))) :=
  ⟨fun xss => xss.flatMap f, flatBy.edit f⟩

/-- Joining, element by element, for runs of edits. -/
def flatBy.inc : Inc (runs (editStructure cb)) (runs (editStructure (plain A))) :=
  lift (flatBy.one f)

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

theorem flatBy_one_ok : (flatBy.one f).ok := by
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
    show patch (plain A) (flatBy.edit f xss (.delete i)) (xss.flatMap f) = (remove xss i).flatMap f
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
    show patch (plain A) (flatBy.edit f xss (.update i d)) (xss.flatMap f) = (update cb xss i d).flatMap f
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
      have hm : (xss.take i).flatMap f ++ (xss.drop (i + 1)).flatMap f =
          (xss.take i).flatMap f ++ (xss.drop (i + 1)).flatMap f := rfl
      have ht : (update cb xss i d).flatMap f =
          (xss.take i).flatMap f ++ f (cb.apply d b) ++ (xss.drop (i + 1)).flatMap f := by
        rw [update_take_drop xss i b d hb, List.flatMap_append, List.flatMap_cons, List.append_assoc]
      simp only [flatBy.edit, hb]
      show run (editStructure (plain A)) (_ ++ _) (xss.flatMap f) = _
      rw [run_append, flatBy.offset_eq]
      have out := deletes_ok' (plain A) ((xss.take i).flatMap f) (f b) ((xss.drop (i + 1)).flatMap f) _ _ hs hm
      have back := inserts_ok' (plain A) ((xss.take i).flatMap f) (f (cb.apply d b))
        ((xss.drop (i + 1)).flatMap f) _ _ hm ht
      exact (congrArg (patch (plain A) _) out).trans back

theorem flatBy_inc_ok : (flatBy.inc f).ok := lift_ok _ (flatBy_one_ok f)

end

end Deui.Lists
