import Deui.Scroll

/-!
Getting from one list to another by the edits between them: what the two
start with in common and what they end with in common stays, and only the
middle is deleted and inserted. `same` says which elements are the same; it
has to be sound (what it calls the same is equal), and needn't be complete:
a difference it imagines only costs an edit.
-/

namespace Deui.Lists

open Deui

variable {A : Type}

/-- How many elements two lists start with in common, as `same` sees it. -/
def common (same : A → A → Bool) : List A → List A → Nat
  | x :: xs, y :: ys => if same x y then common same xs ys + 1 else 0
  | _, _ => 0

/-- Deletes `n` elements at `p`. -/
def deletes (ca : EditStructure) (p : Nat) : Nat → List (Edit.of ca)
  | 0 => []
  | n + 1 => .delete p :: deletes ca p n

/-- Inserts `ys` at `p`, in order. -/
def inserts (ca : EditStructure) (p : Nat) : List ca.Value → List (Edit.of ca)
  | [] => []
  | y :: ys => .insert p y :: inserts ca (p + 1) ys

/-- A run that gets from `xs` to `ys`, leaving what they start and end with
in common: the middle of `xs` deleted, then the middle of `ys` inserted. -/
def change (ca : EditStructure) (same : ca.Value → ca.Value → Bool) (xs ys : List ca.Value) :
    List (Edit.of ca) :=
  let p := common same xs ys
  let xm := xs.drop p
  let ym := ys.drop p
  let s := common same xm.reverse ym.reverse
  deletes ca p (xm.length - s) ++ inserts ca p (ym.take (ym.length - s))

/-- Two lists are what they start with in common, then the rest of each. -/
theorem common_split (same : A → A → Bool) (sound : ∀ a b, same a b = true → a = b) (xs ys : List A) :
    ∃ pre xr yr, xs = pre ++ xr ∧ ys = pre ++ yr ∧ pre.length = common same xs ys := by
  induction xs generalizing ys with
  | nil => exact ⟨[], [], ys, rfl, rfl, by cases ys <;> rfl⟩
  | cons x xs ih =>
    cases ys with
    | nil => exact ⟨[], x :: xs, [], rfl, rfl, rfl⟩
    | cons y ys =>
      by_cases hs : same x y = true
      · obtain ⟨pre, xr, yr, hx, hy, hl⟩ := ih ys
        refine ⟨x :: pre, xr, yr, by rw [hx]; rfl, by rw [hy, sound x y hs]; rfl, ?_⟩
        simp only [common, hs, ite_true, List.length_cons, hl]
      · exact ⟨[], x :: xs, y :: ys, rfl, rfl, by simp [common, hs]⟩

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

/-- `change` gets from `xs` to `ys`. -/
theorem change_ok (ca : EditStructure) (same : ca.Value → ca.Value → Bool)
    (sound : ∀ a b, same a b = true → a = b) (xs ys : List ca.Value) :
    patch ca (change ca same xs ys) xs = ys := by
  obtain ⟨pre, xm, ym, hx, hy, hp⟩ := common_split same sound xs ys
  obtain ⟨rsuf, xr, yr, hxm, hym, hs⟩ := common_split same sound xm.reverse ym.reverse
  have hxm' : xm = xr.reverse ++ rsuf.reverse := by
    have := congrArg List.reverse hxm
    simpa using this
  have hym' : ym = yr.reverse ++ rsuf.reverse := by
    have := congrArg List.reverse hym
    simpa using this
  have dx : xs.drop pre.length = xm := by rw [hx]; simp
  have dy : ys.drop pre.length = ym := by rw [hy]; simp
  unfold change
  simp only [← hp, dx, dy, ← hs]
  have lx : xm.length - rsuf.length = xr.reverse.length := by rw [hxm']; simp
  have ty : ym.take (ym.length - rsuf.length) = yr.reverse := by rw [hym']; simp
  rw [lx, ty]
  show run (editStructure ca) (_ ++ _) xs = ys
  rw [run_append]
  show patch ca (inserts ca pre.length yr.reverse) (patch ca (deletes ca pre.length xr.reverse.length) xs) = ys
  have ex : xs = pre ++ xr.reverse ++ rsuf.reverse := by rw [hx, hxm', List.append_assoc]
  rw [ex, deletes_ok, inserts_ok, hy, hym', List.append_assoc]

/-! ## Lists that are the same -/

/-- Whether two lists are the same, element by element, as `same` sees it. -/
def all2 (same : A → A → Bool) : List A → List A → Bool
  | [], [] => true
  | x :: xs, y :: ys => same x y && all2 same xs ys
  | _, _ => false

theorem all2_refl (same : A → A → Bool) (refl : ∀ a, same a a = true) (xs : List A) : all2 same xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [all2, refl, ih]

theorem all2_sound (same : A → A → Bool) (sound : ∀ a b, same a b = true → a = b) (xs ys : List A)
    (h : all2 same xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => simp [all2] at h
  | cons x xs ih => cases ys with
    | nil => simp [all2] at h
    | cons y ys =>
      simp only [all2, Bool.and_eq_true] at h
      rw [sound x y h.1, ih ys h.2]

/-- Lists whose elements give the same by `g`, one by one, give the same
list by it. -/
theorem all2_map {B : Type} [DecidableEq B] (g : A → B) (xs ys : List A)
    (h : all2 (fun x y => decide (g x = g y)) xs ys = true) : xs.map g = ys.map g := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => simp [all2] at h
  | cons x xs ih => cases ys with
    | nil => simp [all2] at h
    | cons y ys =>
      simp only [all2, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [List.map, h.1, ih ys h.2]

/-- Whether two lists are the same: at once if they're the one object, as a
list is that was kept rather than made again. -/
def alike (same : A → A → Bool) (refl : ∀ a, same a a = true) (xs ys : List A) : Bool :=
  withPtrEq xs ys (fun _ => all2 same xs ys) (by intro h; subst h; exact all2_refl same refl xs)

theorem alike_sound (same : A → A → Bool) (refl : ∀ a, same a a = true)
    (sound : ∀ a b, same a b = true → a = b) (xs ys : List A) (h : alike same refl xs ys = true) : xs = ys :=
  all2_sound same sound xs ys h

/-- `change`, with nothing to do for a list that's the same. -/
def changed (ca : EditStructure) (same : ca.Value → ca.Value → Bool) (refl : ∀ a, same a a = true)
    (xs ys : List ca.Value) : List (Edit.of ca) :=
  if alike same refl xs ys then [] else change ca same xs ys

theorem changed_ok (ca : EditStructure) (same : ca.Value → ca.Value → Bool) (refl : ∀ a, same a a = true)
    (sound : ∀ a b, same a b = true → a = b) (xs ys : List ca.Value) :
    patch ca (changed ca same refl xs ys) xs = ys := by
  unfold changed
  split
  · rename_i h
    exact alike_sound same refl sound xs ys h
  · exact change_ok ca same sound xs ys

/-! ## The middle, in a longer list -/

/-- Two lists, framed: what they start with in common, the middle of each,
and what they end with in common. -/
def frame (same : A → A → Bool) (xs ys : List A) : List A × List A × List A × List A :=
  let p := common same xs ys
  let xm := xs.drop p
  let ym := ys.drop p
  let s := common same xm.reverse ym.reverse
  (xs.take p, xm.take (xm.length - s), ym.take (ym.length - s), xm.drop (xm.length - s))

/-- Each list is the common start, its middle, and the common end. -/
theorem frame_ok (same : A → A → Bool) (sound : ∀ a b, same a b = true → a = b) (xs ys : List A) :
    xs = (frame same xs ys).1 ++ (frame same xs ys).2.1 ++ (frame same xs ys).2.2.2 ∧
      ys = (frame same xs ys).1 ++ (frame same xs ys).2.2.1 ++ (frame same xs ys).2.2.2 := by
  obtain ⟨pre, xm, ym, hx, hy, hp⟩ := common_split same sound xs ys
  obtain ⟨rsuf, xr, yr, hxm, hym, hs⟩ := common_split same sound xm.reverse ym.reverse
  have hxm' : xm = xr.reverse ++ rsuf.reverse := by
    have := congrArg List.reverse hxm
    simpa using this
  have hym' : ym = yr.reverse ++ rsuf.reverse := by
    have := congrArg List.reverse hym
    simpa using this
  have dx : xs.drop pre.length = xm := by rw [hx]; simp
  have dy : ys.drop pre.length = ym := by rw [hy]; simp
  have tx : xs.take pre.length = pre := by rw [hx]; simp
  unfold frame
  simp only [← hp, dx, dy, tx, ← hs]
  have l1 : xm.take (xm.length - rsuf.length) = xr.reverse := by rw [hxm']; simp
  have l2 : xm.drop (xm.length - rsuf.length) = rsuf.reverse := by rw [hxm']; simp
  have l3 : ym.take (ym.length - rsuf.length) = yr.reverse := by rw [hym']; simp
  rw [l1, l2, l3]
  exact ⟨by rw [hx, hxm', List.append_assoc], by rw [hy, hym', List.append_assoc]⟩

/-- `change`, for lists that are the middle of longer ones, `offset`
elements in. -/
def changeAt (ca : EditStructure) (same : ca.Value → ca.Value → Bool) (offset : Nat) (xs ys : List ca.Value) :
    List (Edit.of ca) :=
  let r := frame same xs ys
  deletes ca (offset + r.1.length) r.2.1.length ++ inserts ca (offset + r.1.length) r.2.2.1

/-- `changeAt` gets from `xs` to `ys`, between what's before and after. -/
theorem changeAt_ok (ca : EditStructure) (same : ca.Value → ca.Value → Bool)
    (sound : ∀ a b, same a b = true → a = b) (before xs ys after l l' : List ca.Value)
    (h1 : l = before ++ xs ++ after) (h2 : l' = before ++ ys ++ after) :
    patch ca (changeAt ca same before.length xs ys) l = l' := by
  obtain ⟨fx, fy⟩ := frame_ok same sound xs ys
  unfold changeAt
  generalize frame same xs ys = r at fx fy ⊢
  obtain ⟨pre, xm, ym, suf⟩ := r
  simp only at fx fy
  subst h1; subst h2
  show run (editStructure ca) (deletes ca (before.length + pre.length) xm.length ++
    inserts ca (before.length + pre.length) ym) (before ++ xs ++ after) = before ++ ys ++ after
  rw [run_append]
  have e1 : before ++ xs ++ after = (before ++ pre) ++ xm ++ (suf ++ after) := by rw [fx]; simp
  have e2 : before ++ ys ++ after = (before ++ pre) ++ ym ++ (suf ++ after) := by rw [fy]; simp
  have hl : before.length + pre.length = (before ++ pre).length := by simp
  rw [hl]
  show patch ca (inserts ca (before ++ pre).length ym)
    (patch ca (deletes ca (before ++ pre).length xm.length) (before ++ xs ++ after)) = before ++ ys ++ after
  rw [e1, e2, deletes_ok, inserts_ok]

theorem changeAt_ok' (ca : EditStructure) (same : ca.Value → ca.Value → Bool)
    (sound : ∀ a b, same a b = true → a = b) (offset : Nat) (before xs ys after l l' : List ca.Value)
    (ho : offset = before.length) (h1 : l = before ++ xs ++ after) (h2 : l' = before ++ ys ++ after) :
    patch ca (changeAt ca same offset xs ys) l = l' := by
  subst ho
  exact changeAt_ok ca same sound before xs ys after l l' h1 h2

end Deui.Lists
