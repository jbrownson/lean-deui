import Deui.Combine
import Deui.Scroll

/-!
A list mapped under a context: each element's result is a function of the
context and the element. When the context is edited, each element says
whether the edit touches it, given what it gave before; one that says no
gives what it gave, and makes no edit. It's how a view finds the few things
an edit matters to without working the rest out again: what makes it right
is the law that an element untouched gives the same under the edited
context.
-/

namespace Deui.Lists

open Deui

section
variable {A B : Type}

/-- The results after a context edit, from the elements and what they gave:
`g` gives an element's result under the new context, and `t` says whether
the edit touches an element. An element touched is worked out again, and
is an update at its position, counted from `i`. -/
def sift.refresh (g : A → B) (t : A → B → Bool) :
    Nat → List A → List B → List (Edit B (Whole (plain B))) × List B
  | i, a :: as, b :: bs =>
    if t a b then
      (.update i (.replace (g a)) :: (sift.refresh g t (i + 1) as bs).1, g a :: (sift.refresh g t (i + 1) as bs).2)
    else ((sift.refresh g t (i + 1) as bs).1, b :: (sift.refresh g t (i + 1) as bs).2)
  | _, _, bs => ([], bs)

theorem update_at (pre : List B) (x : B) (xs : List B) (y : B) :
    update (whole (plain B)) (pre ++ x :: xs) pre.length (.replace y) = pre ++ y :: xs := by
  have h := Scrolled.update_append_add (whole (plain B)) pre (x :: xs) (.replace y) 0
  simp only [Nat.add_zero, update, whole.apply] at h
  exact h

/-- The refreshed results are the elements' results under the new context,
and the edits take the old results to them. -/
theorem refresh_ok (f0 g : A → B) (t : A → B → Bool) (law : ∀ a, t a (f0 a) = false → g a = f0 a)
    (xs : List A) (pre : List B) :
    (sift.refresh g t pre.length xs (xs.map f0)).2 = xs.map g ∧
      patch (whole (plain B)) (sift.refresh g t pre.length xs (xs.map f0)).1 (pre ++ xs.map f0) =
        pre ++ xs.map g := by
  induction xs generalizing pre with
  | nil => exact ⟨rfl, rfl⟩
  | cons a as ih =>
    have hi := ih (pre ++ [g a])
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at hi
    have hi2 : patch (whole (plain B)) (sift.refresh g t (pre.length + 1) as (as.map f0)).1
        (pre ++ g a :: as.map f0) = pre ++ g a :: as.map g := by
      have := hi.2
      simpa using this
    by_cases ht : t a (f0 a) = true
    · simp only [List.map, sift.refresh, ht, ite_true]
      refine ⟨by rw [hi.1], ?_⟩
      show patch (whole (plain B)) (sift.refresh g t (pre.length + 1) as (as.map f0)).1
        (update (whole (plain B)) (pre ++ f0 a :: as.map f0) pre.length (.replace (g a))) = _
      rw [update_at]
      exact hi2
    · have hf : t a (f0 a) = false := by simpa using ht
      have eg := law a hf
      simp only [List.map, sift.refresh, hf]
      refine ⟨by rw [hi.1, eg]; rfl, ?_⟩
      show patch (whole (plain B)) (sift.refresh g t (pre.length + 1) as (as.map f0)).1
        (pre ++ f0 a :: as.map f0) = _
      rw [← eg]
      exact hi2

end

section
variable {cc ca : EditStructure} {B : Type}

/-- A list mapped under a context, as an incremental function of the
context's edits and the list's. `under c` is an element's result under the
context `c`, with what an element's own edit makes of it. `touched c d a b`
says whether the context edit `d`, from the context `c`, touches the
element `a`, which gave `b`; `still c d` says the edit touches nothing, and
then no element is asked. It keeps the context, the elements and their
results. -/
def siftedWith (under : cc.Value → Inc ca (whole (plain B)))
    (touched : cc.Value → cc.Edit → ca.Value → B → Bool) (still : cc.Value → cc.Edit → Bool) :
    Cached (prod cc (runs (editStructure ca))) (runs (editStructure (whole (plain B)))) where
  Cache := cc.Value × List ca.Value × List B
  f a := (a.2.map (under a.1).f, (a.1, a.2, a.2.map (under a.1).f))
  df k d :=
    let c := cc.apply d.1 k.1
    let r := if still k.1 d.1 then ([], k.2.2) else sift.refresh (under c).f (touched k.1 d.1) 0 k.2.1 k.2.2
    let ins : List (Edit B (Whole (plain B))) := (map.inc (under c)).df k.2.1 d.2
    (r.1 ++ ins, (c, patch ca d.2 k.2.1, patch (whole (plain B)) ins r.2))

theorem siftedWith_ok (under : cc.Value → Inc ca (whole (plain B)))
    (touched : cc.Value → cc.Edit → ca.Value → B → Bool) (still : cc.Value → cc.Edit → Bool)
    (hunder : ∀ c, (under c).ok)
    (law : ∀ c d a, touched c d a ((under c).f a) = false → (under (cc.apply d c)).f a = (under c).f a)
    (quiet : ∀ c d, still c d = true → ∀ a, touched c d a ((under c).f a) = false) :
    (siftedWith under touched still).ok := by
  intro a d
  obtain ⟨c, xs⟩ := a
  obtain ⟨dc, es⟩ := d
  -- What the context edit makes of the results, asked of each element or not.
  have hr : ∃ r : List (Edit B (Whole (plain B))) × List B,
      (if still c dc then ([], xs.map (under c).f) else
        sift.refresh (under (cc.apply dc c)).f (touched c dc) 0 xs (xs.map (under c).f)) = r ∧
      r.2 = xs.map (under (cc.apply dc c)).f ∧
      run (editStructure (whole (plain B))) r.1 (xs.map (under c).f) = xs.map (under (cc.apply dc c)).f := by
    by_cases hs : still c dc = true
    · have same : xs.map (under (cc.apply dc c)).f = xs.map (under c).f :=
        List.map_congr_left fun x _ => law c dc x (quiet c dc hs x)
      exact ⟨([], xs.map (under c).f), by simp only [hs, ite_true]; rfl, same.symm, same.symm⟩
    · obtain ⟨h2, h1⟩ := refresh_ok (under c).f (under (cc.apply dc c)).f (touched c dc) (law c dc) xs []
      simp only [List.length_nil, List.nil_append] at h1 h2
      exact ⟨_, by simp [hs], h2, h1⟩
  obtain ⟨r, er, h2, h1'⟩ := hr
  have hm : patch (whole (plain B)) ((map.inc (under (cc.apply dc c))).df xs es)
      (xs.map (under (cc.apply dc c)).f) = (patch ca es xs).map (under (cc.apply dc c)).f :=
    map_inc_ok (under (cc.apply dc c)) (hunder _) xs es
  have hm' : run (editStructure (whole (plain B))) ((map.inc (under (cc.apply dc c))).df xs es)
      (xs.map (under (cc.apply dc c)).f) = (patch ca es xs).map (under (cc.apply dc c)).f := hm
  have out : run (editStructure (whole (plain B)))
      (List.append r.1 (lift.run (map.one (under (cc.apply dc c))) es xs))
      (xs.map (under c).f) = (patch ca es xs).map (under (cc.apply dc c)).f :=
    (run_append (editStructure (whole (plain B))) _ _ _).trans
      ((congrArg (run (editStructure (whole (plain B))) _) h1').trans hm')
  have kept : patch (whole (plain B)) ((map.inc (under (cc.apply dc c))).df xs es) r.2 =
      (patch ca es xs).map (under (cc.apply dc c)).f := by
    rw [h2]
    exact hm
  show (run (editStructure (whole (plain B)))
      (List.append (if still c dc then ([], xs.map (under c).f) else
          sift.refresh (under (cc.apply dc c)).f (touched c dc) 0 xs (xs.map (under c).f)).1
        (lift.run (map.one (under (cc.apply dc c))) es xs)) (xs.map (under c).f),
      (cc.apply dc c, patch ca es xs,
        patch (whole (plain B)) ((map.inc (under (cc.apply dc c))).df xs es)
          (if still c dc then ([], xs.map (under c).f) else
            sift.refresh (under (cc.apply dc c)).f (touched c dc) 0 xs (xs.map (under c).f)).2)) = _
  rw [er]
  exact Prod.ext out (Prod.ext rfl (Prod.ext rfl kept))

end

section
variable {cc : EditStructure} {A B : Type}

/-- An element's result under a fixed context, for elements with no edits
of their own. -/
def sift.under (f : cc.Value → A → B) (c : cc.Value) : Inc (plain A) (whole (plain B)) :=
  ⟨f c, fun _ e => nomatch e⟩

/-- And for elements that are replaced whole. -/
def sift.underWhole (f : cc.Value → A → B) (c : cc.Value) : Inc (whole (plain A)) (whole (plain B)) :=
  whole.lift ⟨f c, fun _ e => nomatch e⟩

/-- `siftedWith`, for a list whose elements are inserted and deleted. -/
def sifted (f : cc.Value → A → B) (touched : cc.Value → cc.Edit → A → B → Bool)
    (still : cc.Value → cc.Edit → Bool) :
    Cached (prod cc (runs (editStructure (plain A)))) (runs (editStructure (whole (plain B)))) :=
  siftedWith (sift.under f) touched still

theorem sifted_ok (f : cc.Value → A → B) (touched : cc.Value → cc.Edit → A → B → Bool)
    (still : cc.Value → cc.Edit → Bool)
    (law : ∀ c d a, touched c d a (f c a) = false → f (cc.apply d c) a = f c a)
    (quiet : ∀ c d, still c d = true → ∀ a, touched c d a (f c a) = false) :
    (sifted f touched still).ok :=
  siftedWith_ok _ _ _ (fun _ _ e => nomatch e) law quiet

/-- `siftedWith`, for a list whose elements are also replaced. -/
def siftedWhole (f : cc.Value → A → B) (touched : cc.Value → cc.Edit → A → B → Bool)
    (still : cc.Value → cc.Edit → Bool) :
    Cached (prod cc (runs (editStructure (whole (plain A))))) (runs (editStructure (whole (plain B)))) :=
  siftedWith (sift.underWhole f) touched still

theorem siftedWhole_ok (f : cc.Value → A → B) (touched : cc.Value → cc.Edit → A → B → Bool)
    (still : cc.Value → cc.Edit → Bool)
    (law : ∀ c d a, touched c d a (f c a) = false → f (cc.apply d c) a = f c a)
    (quiet : ∀ c d, still c d = true → ∀ a, touched c d a (f c a) = false) :
    (siftedWhole f touched still).ok :=
  siftedWith_ok _ _ _ (fun _ => whole_lift_ok _ (fun _ e => nomatch e)) law quiet

end

end Deui.Lists
