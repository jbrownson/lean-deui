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

end Deui.Lists
