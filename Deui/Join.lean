import Deui.Flatten

/-!
A list of lists, joined, where each list is edited as a list: an edit
within one of them is the same edit of the joined list, moved past the
lists before it. So a change to one line of one part is a change to one
line of the whole.
-/

namespace Deui.Lists

open Deui

section
variable (cb : EditStructure)

/-- One edit of a list among those joined, as an edit of the joined list:
its position moved past the `off` elements before the list. A position past
the list's end is where the edit itself would put it: an insert at the end,
a delete or an update nowhere. -/
def join.inner (off : Nat) (xs : List cb.Value) : Edit.of cb → List (Edit.of cb)
  | .insert j x => [.insert (off + min j xs.length) x]
  | .delete j => if j < xs.length then [.delete (off + j)] else []
  | .update j d => if j < xs.length then [.update (off + j) d] else []

/-- A run of edits of one list, each from the list before it. -/
def join.inners (off : Nat) : List (Edit.of cb) → List cb.Value → List (Edit.of cb)
  | [], _ => []
  | e :: es, xs => join.inner cb off xs e ++ join.inners off es (edit cb e xs)

/-- How many joined elements come before the list at `i`. -/
def join.offset (xss : List (List cb.Value)) (i : Nat) : Nat := ((xss.take i).map List.length).sum

/-- The edits to the joined list that one edit of the lists makes. -/
def join.edit (xss : List (List cb.Value)) : Edit.of (runs (editStructure cb)) → List (Edit.of cb)
  | .insert i xs => inserts cb (join.offset cb xss i) xs
  | .delete i =>
    match xss[i]? with
    | .none => []
    | .some xs => deletes cb (join.offset cb xss i) xs.length
  | .update i es =>
    match xss[i]? with
    | .none => []
    | .some xs => join.inners cb (join.offset cb xss i) es xs

def join.one : Inc (editStructure (runs (editStructure cb))) (runs (editStructure cb)) :=
  ⟨fun xss => xss.flatMap id, join.edit cb⟩

/-- Lists joined, as an incremental function of the lists and their edits. -/
def join : Inc (runs (editStructure (runs (editStructure cb)))) (runs (editStructure cb)) :=
  lift (join.one cb)

theorem join.offset_eq (xss : List (List cb.Value)) (i : Nat) :
    join.offset cb xss i = ((xss.take i).flatMap id).length := by
  rw [join.offset, List.length_flatMap]
  rfl

theorem insert_past {A : Type} (xs : List A) (j : Nat) (x : A) (h : xs.length ≤ j) :
    insert xs j x = insert xs xs.length x := by
  induction xs generalizing j with
  | nil => cases j <;> rfl
  | cons y ys ih =>
    cases j with
    | zero => simp at h
    | succ j => simp [insert, ih j (by simpa using h)]

theorem insert_min {A : Type} (xs : List A) (j : Nat) (x : A) : insert xs (min j xs.length) x = insert xs j x := by
  rcases Nat.le_total j xs.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, insert_past xs j x h]

theorem join_inner_ok (pre xs suf : List cb.Value) (e : Edit.of cb) :
    patch cb (join.inner cb pre.length xs e) (pre ++ (xs ++ suf)) = pre ++ (edit cb e xs ++ suf) := by
  cases e with
  | insert j x =>
    show insert (pre ++ (xs ++ suf)) (pre.length + min j xs.length) x = pre ++ (insert xs j x ++ suf)
    rw [Scrolled.insert_append_add, Scrolled.insert_append_of_le _ _ _ _ (Nat.min_le_right _ _), insert_min]
  | delete j =>
    by_cases h : j < xs.length
    · simp only [join.inner, h, ite_true]
      show remove (pre ++ (xs ++ suf)) (pre.length + j) = pre ++ (remove xs j ++ suf)
      rw [Scrolled.remove_append_add, Scrolled.remove_append_of_lt _ _ _ h]
    · simp only [join.inner, h, ite_false]
      show pre ++ (xs ++ suf) = pre ++ (remove xs j ++ suf)
      rw [Scrolled.remove_past xs j (by omega)]
  | update j d =>
    by_cases h : j < xs.length
    · simp only [join.inner, h, ite_true]
      show update cb (pre ++ (xs ++ suf)) (pre.length + j) d = pre ++ (update cb xs j d ++ suf)
      rw [Scrolled.update_append_add, Scrolled.update_append_of_lt _ _ _ _ _ h]
    · simp only [join.inner, h, ite_false]
      show pre ++ (xs ++ suf) = pre ++ (update cb xs j d ++ suf)
      rw [update_past xs j (by omega)]

theorem join_inners_ok (pre suf : List cb.Value) (es : List (Edit.of cb)) (xs : List cb.Value) :
    patch cb (join.inners cb pre.length es xs) (pre ++ (xs ++ suf)) = pre ++ (patch cb es xs ++ suf) := by
  induction es generalizing xs with
  | nil => rfl
  | cons e es ih =>
    show run (editStructure cb) (join.inner cb pre.length xs e ++ join.inners cb pre.length es (edit cb e xs))
      (pre ++ (xs ++ suf)) = _
    rw [run_append]
    have h := join_inner_ok cb pre xs suf e
    exact (congrArg (patch cb _) h).trans (ih (edit cb e xs))

theorem join_one_ok : (join.one cb).ok := by
  intro xss e
  cases e with
  | insert i xs =>
    show patch cb (inserts cb (join.offset cb xss i) xs) (xss.flatMap id) = (insert xss i xs).flatMap id
    have hs : xss.flatMap id = (xss.take i).flatMap id ++ (xss.drop i).flatMap id := by
      rw [← List.flatMap_append, List.take_append_drop]
    have ht : (insert xss i xs).flatMap id = (xss.take i).flatMap id ++ xs ++ (xss.drop i).flatMap id := by
      rw [insert_take_drop, List.flatMap_append, List.flatMap_cons, List.append_assoc]
      rfl
    rw [join.offset_eq]
    exact inserts_ok' cb _ _ _ _ _ hs ht
  | delete i =>
    show patch cb (join.edit cb xss (.delete i)) (xss.flatMap id) = (remove xss i).flatMap id
    cases hb : xss[i]? with
    | none =>
      simp only [join.edit, hb]
      rw [Scrolled.remove_past xss i (length_le_of_getElem?_none (cb := runs (editStructure cb)) xss i hb)]
      rfl
    | some xs =>
      obtain ⟨h1, h2⟩ := remove_take_drop xss i xs hb
      have hs : xss.flatMap id = (xss.take i).flatMap id ++ xs ++ (xss.drop (i + 1)).flatMap id := by
        conv => lhs; rw [h1]
        rw [List.flatMap_append, List.flatMap_cons, List.append_assoc]
        rfl
      have ht : (remove xss i).flatMap id = (xss.take i).flatMap id ++ (xss.drop (i + 1)).flatMap id := by
        rw [h2, List.flatMap_append]
      simp only [join.edit, hb]
      rw [join.offset_eq]
      exact deletes_ok' cb _ _ _ _ _ hs ht
  | update i es =>
    show patch cb (join.edit cb xss (.update i es)) (xss.flatMap id) =
      (update (runs (editStructure cb)) xss i es).flatMap id
    cases hb : xss[i]? with
    | none =>
      simp only [join.edit, hb]
      rw [update_past (ca := runs (editStructure cb)) xss i
        (length_le_of_getElem?_none (cb := runs (editStructure cb)) xss i hb)]
      rfl
    | some xs =>
      obtain ⟨h1, _⟩ := remove_take_drop xss i xs hb
      have hs : xss.flatMap id = (xss.take i).flatMap id ++ (xs ++ (xss.drop (i + 1)).flatMap id) := by
        conv => lhs; rw [h1]
        rw [List.flatMap_append, List.flatMap_cons]
        rfl
      have ht : (update (runs (editStructure cb)) xss i es).flatMap id =
          (xss.take i).flatMap id ++ (patch cb es xs ++ (xss.drop (i + 1)).flatMap id) := by
        rw [update_take_drop (cb := runs (editStructure cb)) xss i xs es hb, List.flatMap_append, List.flatMap_cons]
        rfl
      simp only [join.edit, hb]
      rw [join.offset_eq, hs, ht]
      exact join_inners_ok cb _ _ es xs

theorem join_ok : (join cb).ok := lift_ok _ (join_one_ok cb)

end

end Deui.Lists
