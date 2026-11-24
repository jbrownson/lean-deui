import Progred.Display
import Progred.Writes

/-!
Growing frames again, where a change says to. Two changes are followed
down to where they land, each frame on the way asked only whether what it
sees is as it was: a selection that changes, which is seen at its own path
and a step above; and a write within a value, which is seen by the frame
it's a step inside of. A frame that sees the same is left as it is, with
the kids the change isn't on the way to; one that sees something new is
grown again, with all under it.
-/

namespace Progred.Display

open Deui

/-- What the projection is of, with another selection. -/
def _root_.Progred.Shown.select (s : Shown) (sel : Option Selection) : Shown := { s with selection := sel }

/-- Whether a path is on the way to the selection: its own, or above it. -/
def onPath (s : Shown) (path : Path) : Bool :=
  match s.selection with
  | some sel => path.isPrefixOf sel.path
  | none => false

/-- Whether a frame is on the way to the selection: at it, or above it. -/
def onWay (s : Shown) (seed : Seed) : Bool := onPath s seed.path

/-- The edits that take a seed's frames, grown under `s`, to those grown
under `s'`, which differs in its selection. A frame that sees the same of
both is as it was, and so are its kids that neither selection is under,
which aren't looked at; one that sees a difference is grown again. -/
def reselect (s s' : Shown) : Nat → Seed → List (Fit.Edit Span)
  | 0, _ => []
  | fuel + 1, seed =>
    if sees s seed = sees s' seed then
      if onWay s seed || onWay s' seed then
        (framed s seed).2.zipIdx.flatMap fun p =>
          (if onPath s (seed.path ++ p.1.step.toList) || onPath s' (seed.path ++ p.1.step.toList) then
            reselect s s' fuel (seed.kid s p.1)
          else []).map (.kid p.2)
      else []
    else [.replace (grow s' (fuel + 1) seed)]

theorem prefix_of_isPrefixOf_append (p q x : Path) (h : (p ++ q).isPrefixOf x = true) : p.isPrefixOf x = true := by
  rw [List.isPrefixOf_iff_prefix] at h ⊢
  exact (List.prefix_append p q).trans h

/-- A frame that isn't on the way to the selection sees none of it. -/
theorem sees_off (s : Shown) (seed : Seed) (h : onWay s seed = false) : sees s seed = none := by
  unfold sees
  cases hs : s.selection with
  | none => rfl
  | some sel =>
    simp only [onWay, onPath, hs] at h
    have notPrefix : ¬ seed.path <+: sel.path := by
      rw [← List.isPrefixOf_iff_prefix]
      simp [h]
    have h1 : sel.path ≠ seed.path := fun e => notPrefix (e ▸ List.prefix_refl _)
    have h2 : sel.path.dropLast ≠ seed.path := fun e => notPrefix (e ▸ List.dropLast_prefix _)
    simp [seen, h1, h2]

theorem deepOf_select (s : Shown) (sel : Option Selection) (v : Option Value) :
    deepOf (s.select sel) v = deepOf s v := rfl

theorem kid_select (s : Shown) (sel : Option Selection) (seed : Seed) (k : Kid) :
    seed.kid (s.select sel) k = seed.kid s k := rfl

/-- A frame that sees the same selection under another is drawn the same. -/
theorem framed_select (s : Shown) (sel : Option Selection) (seed : Seed)
    (h : sees s seed = sees (s.select sel) seed) : framed (s.select sel) seed = framed s seed := by
  unfold framed
  rw [← h, deepOf_select]
  rfl

theorem kid_path (s : Shown) (seed : Seed) (k : Kid) : (seed.kid s k).path = seed.path ++ k.step.toList := rfl

theorem onWay_kid (s : Shown) (seed : Seed) (k : Kid) (h : onWay s seed = false) : onWay s (seed.kid s k) = false := by
  unfold onWay onPath at h ⊢
  cases hs : s.selection with
  | none => rfl
  | some sel =>
    rw [hs] at h
    simp only at h ⊢
    rw [kid_path]
    apply Bool.eq_false_iff.mpr
    intro e
    rw [prefix_of_isPrefixOf_append _ _ _ e] at h
    cases h

/-- Frames that neither selection is under are the same under both. -/
theorem grow_off (s : Shown) (sel : Option Selection) : ∀ (fuel : Nat) (seed : Seed),
    onWay s seed = false → onWay (s.select sel) seed = false → grow (s.select sel) fuel seed = grow s fuel seed
  | 0, _, _, _ => rfl
  | fuel + 1, seed, h, h' => by
    have same : sees s seed = sees (s.select sel) seed := by rw [sees_off s seed h, sees_off _ seed h']
    simp only [grow, framed_select s sel seed same]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    rw [kid_select]
    exact grow_off s sel fuel _ (onWay_kid s seed k h) (by
      have := onWay_kid (s.select sel) seed k h'
      rwa [kid_select] at this)

/-- Growing again for a selection is right: the edits take the frames grown
under one selection to the frames grown under the other. -/
theorem reselect_ok (s : Shown) (sel : Option Selection) : ∀ (fuel : Nat) (seed : Seed),
    run (Fit.edits Span) (reselect s (s.select sel) fuel seed) (grow s fuel seed) = grow (s.select sel) fuel seed
  | 0, _ => rfl
  | fuel + 1, seed => by
    simp only [reselect]
    split
    · next same =>
      split
      · have h := Fit.run_kids (framed s seed).1 (fun k => grow s fuel (seed.kid s k))
          (fun k => grow (s.select sel) fuel (seed.kid s k))
          (fun k => if onPath s (seed.path ++ k.step.toList) || onPath (s.select sel) (seed.path ++ k.step.toList)
            then reselect s (s.select sel) fuel (seed.kid s k) else []) (framed s seed).2 []
          (fun k _ => by
            split
            · exact reselect_ok s sel fuel (seed.kid s k)
            · next off =>
              simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at off
              exact (grow_off s sel fuel (seed.kid s k) off.1 off.2).symm)
        simp only [grow, framed_select s sel seed same]
        simpa [kid_select] using h
      · next off =>
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at off
        exact (grow_off s sel (fuel + 1) seed off.1 off.2).symm
    · rfl

/-! ## A write -/

/-- Whether a value's frame reads nothing of the whole of it: no
evaluation's result, and no layout of its kind's. -/
def quietDeep (s : Shown) (v : Value) : Bool :=
  (deepOf s (some v)).outcome.isNone && (deepOf s (some v)).node.isNone

theorem deepOf_quiet (s : Shown) (v v' : Value) (h : quietDeep s v = true) (h' : quietDeep s v' = true) :
    deepOf s (some v') = deepOf s (some v) := by
  simp only [quietDeep, Bool.and_eq_true, Option.isNone_iff_eq_none] at h h'
  cases hd : deepOf s (some v)
  cases hd' : deepOf s (some v')
  rw [hd] at h
  rw [hd'] at h'
  simp only at h h'
  simp [h.1, h.2, h'.1, h'.2]

/-- The edits that take a seed's frames to its frames with its value
written at `rel`. A frame the write is more than a step inside of, whose
view of its value is as it was, is as it was, and the write goes on to the
kid it's in; else the frame is grown again. -/
def rewrite (s : Shown) : Nat → Seed → List Step → Option Value → List (Fit.Edit Span)
  | 0, _, _, _ => []
  | fuel + 1, seed, rel, w =>
    match seed.value with
    | none => []
    | some v =>
      match v.put rel w with
      | none => []
      | some v' =>
        match rel with
        | step :: r :: rest =>
          if shallow v' = shallow v ∧ quietDeep s v = true ∧ quietDeep s v' = true then
            (framed s seed).2.zipIdx.flatMap fun p =>
              (if p.1.step = some step then rewrite s fuel (seed.kid s p.1) (r :: rest) w
                else if p.1.step = none then rewrite s fuel (seed.kid s p.1) (step :: r :: rest) w
                else []).map (.kid p.2)
          else [.replace (grow s (fuel + 1) { seed with value := some v' })]
        | _ => [.replace (grow s (fuel + 1) { seed with value := some v' })]

/-- A seed with its value written. -/
def Seed.written (seed : Seed) (rel : List Step) (w : Option Value) : Seed :=
  { seed with value := seed.value.map fun v => v.written rel w }

theorem Seed.written_none (seed : Seed) (rel : List Step) (w : Option Value) (h : seed.value = none) :
    seed.written rel w = seed := by
  cases seed
  simp only at h
  subst h
  rfl

theorem Seed.written_same (seed : Seed) (rel : List Step) (w : Option Value) (v : Value) (h : seed.value = some v)
    (hp : v.put rel w = none) : seed.written rel w = seed := by
  cases seed
  simp only at h
  subst h
  simp [Seed.written, Value.written, hp]

theorem Seed.written_some (seed : Seed) (rel : List Step) (w : Option Value) (v v' : Value)
    (h : seed.value = some v) (hp : v.put rel w = some v') :
    seed.written rel w = { seed with value := some v' } := by
  cases seed
  simp only at h
  subst h
  simp [Seed.written, Value.written, hp]

/-- Growing again for a write is right: the edits take a seed's frames to
the frames of the seed with its value written. -/
theorem rewrite_ok (s : Shown) : ∀ (fuel : Nat) (seed : Seed) (rel : List Step) (w : Option Value),
    run (Fit.edits Span) (rewrite s fuel seed rel w) (grow s fuel seed) = grow s fuel (seed.written rel w)
  | 0, _, _, _ => rfl
  | fuel + 1, seed, rel, w => by
    cases hv : seed.value with
    | none =>
      rw [Seed.written_none seed rel w hv]
      simp [rewrite, hv, run]
    | some v =>
      cases hp : v.put rel w with
      | none =>
        rw [Seed.written_same seed rel w v hv hp]
        simp [rewrite, hv, hp, run]
      | some v' =>
        rw [Seed.written_some seed rel w v v' hv hp]
        match rel, hp with
        | [], hp => simp [rewrite, hv, hp, run]; rfl
        | [_], hp => simp [rewrite, hv, hp, run]; rfl
        | step :: r :: rest, hp =>
          simp only [rewrite, hv, hp]
          split
          · next cond =>
            obtain ⟨hsh, hq, hq'⟩ := cond
            obtain ⟨c, c', hc, hcp, hset⟩ := Value.put_deep v step r rest w v' hp
            obtain ⟨notCell, notCell'⟩ := Value.setStep_not_cell v step c' v' hset
            -- The frame itself is drawn the same.
            have hframed : framed s { seed with value := some v' } = framed s seed := by
              unfold framed sees
              simp only [hv, Option.map_some, hsh, deepOf_quiet s v v' hq hq']
            -- Each kid's frames, after its edits, are the written seed's kid's.
            have each : ∀ k ∈ (framed s seed).2,
                run (Fit.edits Span)
                  (if k.step = some step then rewrite s fuel (seed.kid s k) (r :: rest) w
                    else if k.step = none then rewrite s fuel (seed.kid s k) (step :: r :: rest) w
                    else [])
                  (grow s fuel (seed.kid s k)) =
                  grow s fuel (Seed.kid s { seed with value := some v' } k) := by
              intro k _
              by_cases h1 : k.step = some step
              · simp only [h1, ite_true]
                rw [rewrite_ok s fuel (seed.kid s k) (r :: rest) w]
                congr 1
                have hstep : step ≠ .follow := by
                  intro e
                  subst e
                  cases v <;> simp [Value.step?] at hc
                have old : (seed.kid s k).value = some c := by
                  cases step <;> simp_all [Seed.kid]
                have new : (Seed.kid s { seed with value := some v' } k).value = some c' := by
                  have := Value.step_setStep_same v step c' v' hset
                  cases step <;> simp_all [Seed.kid]
                rw [Seed.written_some _ _ _ c c' old hcp]
                cases hk : Seed.kid s { seed with value := some v' } k
                rw [hk] at new
                simp only at new
                subst new
                simp [Seed.kid] at hk ⊢
                simp [hk]
              · by_cases h2 : k.step = none
                · simp only [h2, reduceCtorEq, ite_true, ite_false]
                  rw [rewrite_ok s fuel (seed.kid s k) (step :: r :: rest) w]
                  congr 1
                  have old : (seed.kid s k).value = some v := by simp [Seed.kid, h2, hv]
                  rw [Seed.written_some _ _ _ v v' old hp]
                  simp [Seed.kid, h2]
                · simp only [h1, h2, ite_false]
                  show grow s fuel (seed.kid s k) = _
                  congr 1
                  cases hst : k.step with
                  | none => exact absurd hst h2
                  | some st =>
                    have ne : st ≠ step := fun e => h1 (by rw [hst, e])
                    cases st with
                    | follow =>
                      cases v with
                      | cell c0 => exact absurd rfl (notCell c0)
                      | blob _ | list _ | record _ =>
                        cases v' with
                        | cell c1 => exact absurd rfl (notCell' c1)
                        | blob _ | list _ | record _ => simp [Seed.kid, hst, hv]
                    | key l =>
                      have := Value.step_setStep_other v step c' v' hset (.key l) ne
                      simp [Seed.kid, hst, hv, this]
                    | element q =>
                      have := Value.step_setStep_other v step c' v' hset (.element q) ne
                      simp [Seed.kid, hst, hv, this]
            have h := Fit.run_kids (framed s seed).1 (fun k => grow s fuel (seed.kid s k))
              (fun k => grow s fuel (Seed.kid s { seed with value := some v' } k))
              (fun k => if k.step = some step then rewrite s fuel (seed.kid s k) (r :: rest) w
                else if k.step = none then rewrite s fuel (seed.kid s k) (step :: r :: rest) w
                else []) (framed s seed).2 [] each
            simp only [grow, hframed]
            simpa using h
          · rfl

/-! ## A part's edits -/

/-- An edit of a part: a new one, or its value written at a path within it. -/
inductive Entry.Edit where
  | replace (e : Entry)
  | write (rel : List Step) (value : Option Value)

def Entry.Edit.apply : Entry.Edit → Entry → Entry
  | .replace e, _ => e
  | .write rel w, .entry p v => .entry p (v.written rel w)
  | .write rel w, .whole root => .whole (root.map fun v => v.written rel w)
  | .write _ _, .end_ => .end_

abbrev Entry.edits : Deui.EditStructure := ⟨Entry, Entry.Edit, Entry.Edit.apply⟩

/-- Where a write within a part is, from the part's seed: an entry is held
as a list of the one, so a step on. -/
def Entry.rel : Entry → List Step → List Step
  | .entry p _, rel => .element p :: rel
  | _, rel => rel

/-- A part with a write within it is its seed with its value written: for a
write more than nowhere in, which would be the part replaced. -/
theorem partSeed_written (e : Entry) (r : Step) (rest : List Step) (w : Option Value) :
    partSeed (Entry.Edit.apply (.write (r :: rest) w) e) = (partSeed e).written (e.rel (r :: rest)) w ∨ e = .end_ := by
  cases e with
  | end_ => exact Or.inr rfl
  | whole root => cases root <;> exact Or.inl rfl
  | entry p v =>
    refine Or.inl ?_
    simp only [Entry.Edit.apply, partSeed, Seed.written, Entry.rel, Option.map_some]
    congr 2
    have hstep : (Value.list [(p, v)]).step? (.element p) = some v := by simp [Value.step?]
    cases hp : v.put (r :: rest) w with
    | none =>
      have : (Value.list [(p, v)]).put (.element p :: r :: rest) w = none := by
        cases w <;> simp_all [Value.put, Value.set, Value.without, bind, Option.bind]
      simp [Value.written, hp, this]
    | some c' =>
      have : (Value.list [(p, v)]).put (.element p :: r :: rest) w = some (.list [(p, c')]) := by
        cases w <;> simp_all [Value.put, Value.set, Value.without, bind, Option.bind, Value.setStep, Value.setElement]
      simp [Value.written, hp, this]

/-- The edits that take a part's frames to its frames with a write within
it. -/
def Entry.rewrite (s : Shown) (e : Entry) (rel : List Step) (w : Option Value) : List (Fit.Edit Span) :=
  match e with
  | .end_ => []
  | e => Display.rewrite s depth (partSeed e) (e.rel rel) w

theorem Entry.rewrite_ok (s : Shown) (e : Entry) (r : Step) (rest : List Step) (w : Option Value) :
    run (Fit.edits Span) (Entry.rewrite s e (r :: rest) w) (grow s depth (partSeed e)) =
      grow s depth (partSeed (Entry.Edit.apply (.write (r :: rest) w) e)) := by
  rcases partSeed_written e r rest w with h | h
  · rw [h]
    cases e with
    | end_ => simp [partSeed, Entry.rewrite, Seed.written, Entry.rel, Entry.Edit.apply] at h ⊢; rw [← h]; rfl
    | whole root => exact Display.rewrite_ok s depth (partSeed (.whole root)) (r :: rest) w
    | entry p v => exact Display.rewrite_ok s depth (partSeed (.entry p v)) (.element p :: r :: rest) w
  · subst h
    rfl

/-- Two inputs that differ at most in their part and selection are drawn
from the same, but for the selection. -/
theorem Input.shown_select (i i' : Input) (h : i'.item.reached = i.item.reached) (hf : i'.folds = i.folds)
    (hr : i'.results = i.results) (hl : i'.layouts = i.layouts) (hn : i'.named = i.named) :
    i'.shown = i.shown.select i'.selection := by
  simp only [Input.shown, Shown.select, h, hf, hr, hl, hn]

end Progred.Display
