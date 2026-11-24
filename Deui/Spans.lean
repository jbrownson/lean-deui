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

/-- Puts `new` where `old` is, at `p`: each element replaced where both
have one, then what's left of `new` inserted, or of `old` deleted. -/
def swaps {B : Type} (p : Nat) : List B → List B → List (Edit.of (whole (plain B)))
  | _ :: os, n :: ns => .update p (.replace n) :: swaps (p + 1) os ns
  | [], ns => inserts (whole (plain B)) p ns
  | os, [] => deletes (whole (plain B)) p os.length

theorem swaps_ok {B : Type} (pre old new suf : List B) :
    patch (whole (plain B)) (swaps pre.length old new) (pre ++ old ++ suf) = pre ++ new ++ suf := by
  induction old generalizing pre new with
  | nil =>
    have h : swaps pre.length ([] : List B) new = inserts (whole (plain B)) pre.length new := by
      cases new <;> rfl
    rw [h]
    exact inserts_ok' (whole (plain B)) pre new suf _ _ (by rw [List.append_nil]; rfl) rfl
  | cons o os ih =>
    cases new with
    | nil => exact deletes_ok' (whole (plain B)) pre (o :: os) suf _ _ rfl (by rw [List.append_nil]; rfl)
    | cons n ns =>
      show patch (whole (plain B)) (swaps (pre.length + 1) os ns)
        (update (whole (plain B)) (pre ++ o :: os ++ suf) pre.length (.replace n)) = _
      have e : pre ++ o :: os ++ suf = pre ++ o :: (os ++ suf) := by simp
      rw [e, update_at]
      have h := ih (pre ++ [n]) ns
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, List.append_assoc,
        List.cons_append, List.nil_append] at h
      simpa using h

end Deui.Lists
