import Deui.Scroll

/-!
Runs of elements in a list: deleting a run at a position, and inserting one
there. What a list joined from others is edited by, when one of them goes
or comes.
-/

namespace Deui.Lists

open Deui

variable {A : Type}

/-- Deletes `n` elements at `p`. -/
def deletes (ca : EditStructure) (p : Nat) : Nat → List (Edit.of ca)
  | 0 => []
  | n + 1 => .delete p :: deletes ca p n

/-- Inserts `ys` at `p`, in order. -/
def inserts (ca : EditStructure) (p : Nat) : List ca.Value → List (Edit.of ca)
  | [] => []
  | y :: ys => .insert p y :: inserts ca (p + 1) ys

theorem deletes_ok (ca : EditStructure) (pre mid suf : List ca.Value) :
    patch ca (deletes ca pre.length mid.length) (pre ++ mid ++ suf) = pre ++ suf := by
  induction mid with
  | nil => simp [deletes, patch, run]
  | cons m mid ih =>
    show patch ca (deletes ca pre.length mid.length) (remove (pre ++ (m :: mid) ++ suf) pre.length) = _
    have : pre ++ (m :: mid) ++ suf = pre ++ m :: (mid ++ suf) := by simp
    rw [this, Scrolled.remove_append_length, ← List.append_assoc]
    exact ih

theorem inserts_ok (ca : EditStructure) (pre ys suf : List ca.Value) :
    patch ca (inserts ca pre.length ys) (pre ++ suf) = pre ++ ys ++ suf := by
  induction ys generalizing pre with
  | nil => simp [inserts, patch, run]
  | cons y ys ih =>
    show patch ca (inserts ca (pre.length + 1) ys) (insert (pre ++ suf) pre.length y) = _
    rw [Scrolled.insert_append_length]
    have h := ih (pre ++ [y])
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, List.append_assoc,
      List.cons_append, List.nil_append] at h
    simpa using h

theorem inserts_ok' (ca : EditStructure) (pre ys suf l l' : List ca.Value) (h1 : l = pre ++ suf)
    (h2 : l' = pre ++ ys ++ suf) : patch ca (inserts ca pre.length ys) l = l' := by
  subst h1; subst h2; exact inserts_ok ca pre ys suf

theorem deletes_ok' (ca : EditStructure) (pre mid suf l l' : List ca.Value) (h1 : l = pre ++ mid ++ suf)
    (h2 : l' = pre ++ suf) : patch ca (deletes ca pre.length mid.length) l = l' := by
  subst h1; subst h2; exact deletes_ok ca pre mid suf

theorem update_at {B : Type} (pre : List B) (x : B) (xs : List B) (y : B) :
    update (whole (plain B)) (pre ++ x :: xs) pre.length (.replace y) = pre ++ y :: xs := by
  have h := Scrolled.update_append_add (whole (plain B)) pre (x :: xs) (.replace y) 0
  simp only [Nat.add_zero, update, whole.apply] at h
  exact h

/-- Inserts `ys` at `p`, last first: each goes in at `p`, so none costs the
ones before it. -/
def puts (ca : EditStructure) (p : Nat) (ys : List ca.Value) : List (Edit.of ca) :=
  ys.reverse.map (.insert p)

theorem inserts_at_ok (ca : EditStructure) (pre : List ca.Value) (zs suf : List ca.Value) :
    patch ca (zs.map (.insert pre.length)) (pre ++ suf) = pre ++ zs.reverse ++ suf := by
  induction zs generalizing suf with
  | nil => simp [patch, run]
  | cons z t ih =>
    show patch ca (t.map (.insert pre.length)) (insert (pre ++ suf) pre.length z) = _
    rw [Scrolled.insert_append_length, ih (z :: suf)]
    simp

theorem puts_ok (ca : EditStructure) (pre ys suf : List ca.Value) :
    patch ca (puts ca pre.length ys) (pre ++ suf) = pre ++ ys ++ suf := by
  have h := inserts_at_ok ca pre ys.reverse suf
  rw [List.reverse_reverse] at h
  exact h

/-- How many elements are replaced one by one before it's cheaper to take
them all out and put the new ones in. -/
def fewSwaps : Nat := 16

/-- Puts `new` where `old` is, at `p`. A few are replaced one for one,
then what's left of `new` inserted, or of `old` deleted; many are taken
out and the new put in, which costs no more for there being many. -/
def swaps {B : Type} (p : Nat) (old new : List B) : List (Edit.of (whole (plain B))) :=
  if old.length > fewSwaps || new.length > fewSwaps then
    deletes (whole (plain B)) p old.length ++ puts (whole (plain B)) p new
  else swaps.few p old new
where
  few (p : Nat) : List B → List B → List (Edit.of (whole (plain B)))
    | _ :: os, n :: ns => .update p (.replace n) :: few (p + 1) os ns
    | [], ns => inserts (whole (plain B)) p ns
    | os, [] => deletes (whole (plain B)) p os.length

theorem swaps_few_ok {B : Type} (pre old new suf : List B) :
    patch (whole (plain B)) (swaps.few pre.length old new) (pre ++ old ++ suf) = pre ++ new ++ suf := by
  induction old generalizing pre new with
  | nil =>
    have h : swaps.few pre.length ([] : List B) new = inserts (whole (plain B)) pre.length new := by
      cases new <;> rfl
    rw [h]
    exact inserts_ok' (whole (plain B)) pre new suf _ _ (by rw [List.append_nil]; rfl) rfl
  | cons o os ih =>
    cases new with
    | nil => exact deletes_ok' (whole (plain B)) pre (o :: os) suf _ _ rfl (by rw [List.append_nil]; rfl)
    | cons n ns =>
      show patch (whole (plain B)) (swaps.few (pre.length + 1) os ns)
        (update (whole (plain B)) (pre ++ o :: os ++ suf) pre.length (.replace n)) = _
      have e : pre ++ o :: os ++ suf = pre ++ o :: (os ++ suf) := by simp
      rw [e, update_at]
      have h := ih (pre ++ [n]) ns
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, List.append_assoc,
        List.cons_append, List.nil_append] at h
      simpa using h

theorem swaps_ok {B : Type} (pre old new suf : List B) :
    patch (whole (plain B)) (swaps pre.length old new) (pre ++ old ++ suf) = pre ++ new ++ suf := by
  unfold swaps
  split
  · have out := deletes_ok (whole (plain B)) pre old suf
    have back := puts_ok (whole (plain B)) pre new suf
    exact (run_append (editStructure (whole (plain B))) _ _ _).trans
      ((congrArg (patch (whole (plain B)) _) out).trans back)
  · exact swaps_few_ok pre old new suf

/-! ## A list about one position -/

section
variable {A : Type}

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

end

section
variable {cb : EditStructure}

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

end

end Deui.Lists
