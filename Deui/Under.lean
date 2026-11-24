import Deui.Combine
import Deui.Flatten

/-!
A list mapped under a context by a function that keeps what it needs: each
element's result is a function of the context and the element, and each
element has its own kept state. A context edit is given to every element,
and each says what it makes of it; one it doesn't touch says nothing, and
nothing is made for it. An element's own edit goes to that element alone.
What makes it right is the function's own law, for each element.
-/

namespace Deui.Lists

open Deui

section
variable {cc ca cb : EditStructure}

/-- A context edit given to each element: what each makes of it, at its
position counted from `i`, and what each keeps. An element that makes
nothing of it makes no edit. -/
def under.refresh (g : Cached (prod cc (runs ca)) (runs cb)) (d : cc.Edit) :
    Nat → List g.Cache → List (Edit.of (runs cb)) × List g.Cache
  | _, [] => ([], [])
  | i, k :: ks =>
    (if (g.df k (d, [])).1.isEmpty then (under.refresh g d (i + 1) ks).1
      else .update i (g.df k (d, [])).1 :: (under.refresh g d (i + 1) ks).1,
      (g.df k (d, [])).2 :: (under.refresh g d (i + 1) ks).2)

/-- One edit of the list, under a context: an element put in is worked out
from nothing, and one edited is given its edit with a context edit that
changes nothing. -/
def under.edit (g : Cached (prod cc (runs ca)) (runs cb)) (c : cc.Value) (idle : cc.Edit) (ks : List g.Cache) :
    Edit.of (runs ca) → List (Edit.of (runs cb)) × List g.Cache
  | .insert i x => ([.insert i (g.f (c, x)).1], insert ks i (g.f (c, x)).2)
  | .delete i => ([.delete i], remove ks i)
  | .update i es =>
    match ks[i]? with
    | .none => ([], ks)
    | .some k => ([.update i (g.df k (idle, es)).1], update (latest g.Cache) ks i (g.df k (idle, es)).2)

/-- A run of edits of the list. -/
def under.edits (g : Cached (prod cc (runs ca)) (runs cb)) (c : cc.Value) (idle : cc.Edit) :
    List (Edit.of (runs ca)) → List g.Cache → List (Edit.of (runs cb)) × List g.Cache
  | [], ks => ([], ks)
  | e :: es, ks =>
    ((under.edit g c idle ks e).1 ++ (under.edits g c idle es (under.edit g c idle ks e).2).1,
      (under.edits g c idle es (under.edit g c idle ks e).2).2)

/-- A list mapped under a context by `g`, which keeps what it needs for
each element. `idle c` is a context edit that leaves `c` as it is, and
`quiet c d` says the context edit `d` changes nothing any element reads:
then none is asked. It keeps the context and each element's kept state. -/
def mapUnder (g : Cached (prod cc (runs ca)) (runs cb)) (idle : cc.Value → cc.Edit)
    (quiet : cc.Value → cc.Edit → Bool) :
    Cached (prod cc (runs (editStructure (runs ca)))) (runs (editStructure (runs cb))) where
  Cache := cc.Value × List g.Cache
  f a := (a.2.map fun x => (g.f (a.1, x)).1, (a.1, a.2.map fun x => (g.f (a.1, x)).2))
  df k d :=
    let r := if quiet k.1 d.1 then ([], k.2) else under.refresh g d.1 0 k.2
    let l := under.edits g (cc.apply d.1 k.1) (idle (cc.apply d.1 k.1)) d.2 r.2
    (r.1 ++ l.1, (cc.apply d.1 k.1, l.2))

theorem update_cons_append {ce : EditStructure} (pre : List ce.Value) (x : ce.Value) (xs : List ce.Value)
    (d : ce.Edit) : update ce (pre ++ x :: xs) pre.length d = pre ++ ce.apply d x :: xs := by
  have h := Scrolled.update_append_add ce pre (x :: xs) d 0
  simp only [Nat.add_zero, update] at h
  exact h

/-- An element of a mapped list updated, when the update takes its image
to another element's. -/
theorem update_map_at {ce : EditStructure} {A : Type} (f : A → ce.Value) (xs : List A) (i : Nat) (x x' : A)
    (d : ce.Edit) (hx : xs[i]? = some x) (h : ce.apply d (f x) = f x') :
    update ce (xs.map f) i d = (xs.take i ++ x' :: xs.drop (i + 1)).map f := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons y t ih =>
    cases i with
    | zero =>
      simp at hx
      subst hx
      simp [update, h]
    | succ p =>
      simp at hx
      simp [update, ih p hx]

theorem under_refresh_ok (g : Cached (prod cc (runs ca)) (runs cb)) (hg : g.ok) (c : cc.Value) (d : cc.Edit)
    (ys : List ca.Value) (pre : List cb.Value) :
    (under.refresh g d pre.length (ys.map fun x => (g.f (c, x)).2)).2 =
        ys.map (fun x => (g.f (cc.apply d c, x)).2) ∧
      patch (runs cb) (under.refresh g d pre.length (ys.map fun x => (g.f (c, x)).2)).1
          (pre ++ ys.map fun x => (g.f (c, x)).1) =
        pre ++ ys.map fun x => (g.f (cc.apply d c, x)).1 := by
  induction ys generalizing pre with
  | nil => exact ⟨rfl, rfl⟩
  | cons y ys ih =>
    have e := hg (c, y) (d, [])
    have e1 : run cb (g.df (g.f (c, y)).2 (d, [])).1 (g.f (c, y)).1 = (g.f (cc.apply d c, y)).1 :=
      congrArg Prod.fst e
    have e2 : (g.df (g.f (c, y)).2 (d, [])).2 = (g.f (cc.apply d c, y)).2 := congrArg Prod.snd e
    have hi := ih (pre ++ [(g.f (cc.apply d c, y)).1])
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, List.append_assoc,
      List.cons_append, List.nil_append] at hi
    simp only [List.map_cons, under.refresh]
    refine ⟨by rw [e2, hi.1], ?_⟩
    by_cases hem : (g.df (g.f (c, y)).2 (d, [])).1.isEmpty = true
    · have hn : (g.df (g.f (c, y)).2 (d, [])).1 = [] := List.isEmpty_iff.mp hem
      rw [hn] at e1
      have same : (g.f (c, y)).1 = (g.f (cc.apply d c, y)).1 := e1
      simp only [hem, ite_true]
      rw [same]
      exact hi.2
    · simp only [hem]
      show patch (runs cb) _ (update (runs cb) (pre ++ (g.f (c, y)).1 :: ys.map fun x => (g.f (c, x)).1)
        pre.length (g.df (g.f (c, y)).2 (d, [])).1) = _
      rw [update_cons_append]
      show patch (runs cb) _ (pre ++ run cb (g.df (g.f (c, y)).2 (d, [])).1 (g.f (c, y)).1 :: _) = _
      rw [e1]
      exact hi.2

theorem under_edit_ok (g : Cached (prod cc (runs ca)) (runs cb)) (hg : g.ok) (c : cc.Value) (idle : cc.Edit)
    (hidle : cc.apply idle c = c) (xs : List ca.Value) (e : Edit.of (runs ca)) :
    (under.edit g c idle (xs.map fun x => (g.f (c, x)).2) e).2 =
        (edit (runs ca) e xs).map (fun x => (g.f (c, x)).2) ∧
      patch (runs cb) (under.edit g c idle (xs.map fun x => (g.f (c, x)).2) e).1
          (xs.map fun x => (g.f (c, x)).1) =
        (edit (runs ca) e xs).map fun x => (g.f (c, x)).1 := by
  cases e with
  | insert i x =>
    exact ⟨(map_insert _ xs i x).symm, (map_insert (fun x => (g.f (c, x)).1) xs i x).symm⟩
  | delete i =>
    exact ⟨(map_remove _ xs i).symm, (map_remove (fun x => (g.f (c, x)).1) xs i).symm⟩
  | update i es =>
    cases hx : xs[i]? with
    | none =>
      have hk : (xs.map fun x => (g.f (c, x)).2)[i]? = none := by simp [hx]
      have hp := update_past (ca := runs ca) xs i (length_le_of_getElem?_none (cb := runs ca) xs i hx) es
      simp only [under.edit, hk]
      show _ = (update (runs ca) xs i es).map _ ∧ _ = (update (runs ca) xs i es).map _
      rw [hp]
      exact ⟨rfl, rfl⟩
    | some x =>
      have hk : (xs.map fun x => (g.f (c, x)).2)[i]? = some (g.f (c, x)).2 := by simp [hx]
      have e := hg (c, x) (idle, es)
      have e1 : run cb (g.df (g.f (c, x)).2 (idle, es)).1 (g.f (c, x)).1 = (g.f (c, run ca es x)).1 := by
        have := congrArg Prod.fst e
        simpa [prod, hidle] using this
      have e2 : (g.df (g.f (c, x)).2 (idle, es)).2 = (g.f (c, run ca es x)).2 := by
        have := congrArg Prod.snd e
        simpa [prod, hidle] using this
      have hu := update_take_drop (cb := runs ca) xs i x es hx
      simp only [under.edit, hk]
      show update (latest g.Cache) (xs.map fun x => (g.f (c, x)).2) i _ = (update (runs ca) xs i es).map _ ∧
        update (runs cb) (xs.map fun x => (g.f (c, x)).1) i _ = (update (runs ca) xs i es).map _
      rw [hu]
      exact ⟨update_map_at (ce := latest g.Cache) (fun x => (g.f (c, x)).2) xs i x (run ca es x) _ hx e2,
        update_map_at (ce := runs cb) (fun x => (g.f (c, x)).1) xs i x (run ca es x) _ hx e1⟩

theorem under_edits_ok (g : Cached (prod cc (runs ca)) (runs cb)) (hg : g.ok) (c : cc.Value) (idle : cc.Edit)
    (hidle : cc.apply idle c = c) (es : List (Edit.of (runs ca))) (xs : List ca.Value) :
    (under.edits g c idle es (xs.map fun x => (g.f (c, x)).2)).2 =
        (patch (runs ca) es xs).map (fun x => (g.f (c, x)).2) ∧
      patch (runs cb) (under.edits g c idle es (xs.map fun x => (g.f (c, x)).2)).1
          (xs.map fun x => (g.f (c, x)).1) =
        (patch (runs ca) es xs).map fun x => (g.f (c, x)).1 := by
  induction es generalizing xs with
  | nil => exact ⟨rfl, rfl⟩
  | cons e es ih =>
    obtain ⟨h1, h2⟩ := under_edit_ok g hg c idle hidle xs e
    simp only [under.edits, h1]
    obtain ⟨i1, i2⟩ := ih (edit (runs ca) e xs)
    refine ⟨i1, ?_⟩
    show run (editStructure (runs cb)) (_ ++ _) _ = _
    rw [run_append]
    exact (congrArg (patch (runs cb) _) h2).trans i2

/-- Mapping under a context is right, if the function is, `idle` leaves the
context as it is, and a quiet context edit changes nothing of any element. -/
theorem mapUnder_ok (g : Cached (prod cc (runs ca)) (runs cb)) (idle : cc.Value → cc.Edit)
    (quiet : cc.Value → cc.Edit → Bool) (hg : g.ok) (hidle : ∀ c, cc.apply (idle c) c = c)
    (hquiet : ∀ c d, quiet c d = true → ∀ x, g.f (cc.apply d c, x) = g.f (c, x)) :
    (mapUnder g idle quiet).ok := by
  intro a d
  obtain ⟨c, xs⟩ := a
  obtain ⟨dc, es⟩ := d
  -- What the context edit makes of the elements, asked or not.
  have hr : ∃ r : List (Edit.of (runs cb)) × List g.Cache,
      (if quiet c dc then ([], xs.map fun x => (g.f (c, x)).2)
        else under.refresh g dc 0 (xs.map fun x => (g.f (c, x)).2)) = r ∧
      r.2 = xs.map (fun x => (g.f (cc.apply dc c, x)).2) ∧
      patch (runs cb) r.1 (xs.map fun x => (g.f (c, x)).1) = xs.map fun x => (g.f (cc.apply dc c, x)).1 := by
    by_cases hq : quiet c dc = true
    · have same : ∀ x, g.f (cc.apply dc c, x) = g.f (c, x) := hquiet c dc hq
      refine ⟨([], xs.map fun x => (g.f (c, x)).2), by simp [hq], ?_, ?_⟩
      · exact List.map_congr_left fun x _ => by rw [same x]
      · exact List.map_congr_left fun x _ => by rw [same x]
    · obtain ⟨h2, h1⟩ := under_refresh_ok g hg c dc xs []
      simp only [List.length_nil, List.nil_append] at h1 h2
      exact ⟨_, by simp [hq], h2, h1⟩
  obtain ⟨r, er, h2, h1⟩ := hr
  obtain ⟨l2, l1⟩ := under_edits_ok g hg (cc.apply dc c) (idle (cc.apply dc c)) (hidle _) es xs
  show (run (editStructure (runs cb))
      ((if quiet c dc then ([], xs.map fun x => (g.f (c, x)).2)
          else under.refresh g dc 0 (xs.map fun x => (g.f (c, x)).2)).1 ++
        (under.edits g (cc.apply dc c) (idle (cc.apply dc c)) es
          (if quiet c dc then ([], xs.map fun x => (g.f (c, x)).2)
            else under.refresh g dc 0 (xs.map fun x => (g.f (c, x)).2)).2).1)
      (xs.map fun x => (g.f (c, x)).1),
    (cc.apply dc c, (under.edits g (cc.apply dc c) (idle (cc.apply dc c)) es
      (if quiet c dc then ([], xs.map fun x => (g.f (c, x)).2)
        else under.refresh g dc 0 (xs.map fun x => (g.f (c, x)).2)).2).2)) = _
  rw [er, h2, run_append]
  refine Prod.ext ?_ (Prod.ext rfl l2)
  exact (congrArg (patch (runs cb) _) h1).trans l1

end

end Deui.Lists
