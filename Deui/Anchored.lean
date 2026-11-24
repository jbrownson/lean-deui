import Deui.Combine
import Deui.Scroll

/-!
A list at an offset: rows, and how far their top is above a window's top,
each edited on its own. `anchored` gives the scrolled list it is
(`Deui/Scroll.lean`), and for each edit the scrolled list's edits: a list
edit, then a scroll back to the offset, since a scrolled list keeps what
shows in place when a row above it changes; or a scroll to a new offset.
It's how rows worked out from a state that holds the offset meet the scroll
view.
-/

namespace Deui.Lists.Scrolled

open Deui

section
variable {R : Type} (h : R → Nat)

/-- A normalized scrolled list is its rows and its offset: two with the
same rows at the same offset are the same. -/
theorem normal_unique (n₁ n₂ : Scroll R) (h₁ : normalShape h n₁) (h₂ : normalShape h n₂)
    (hr : n₁.rows = n₂.rows) (ho : n₁.offset h = n₂.offset h) : n₁ = n₂ := by
  obtain ⟨a1, r1, o1⟩ := n₁
  obtain ⟨a2, r2, o2⟩ := n₂
  simp only [Scroll.rows] at hr
  simp only [Scroll.offset] at ho
  simp only [normalShape] at h₁ h₂
  have core : ∀ (a1 r1 : List R) (o1 : Int) (a2 r2 : List R) (o2 : Int) (c : List R),
      0 ≤ o2 → (∀ r rs, r1 = r :: rs → o1 < h r) → a2.reverse = a1.reverse ++ c → r1 = c ++ r2 →
      (height h a1 : Int) + o1 = height h a2 + o2 → a1 = a2 ∧ r1 = r2 ∧ o1 = o2 := by
    intro a1 r1 o1 a2 r2 o2 c hp2 hs1 ha hrr hoo
    have hh : height h a2 = height h a1 + height h c := by
      rw [← height_reverse h a2, ha, height_append, height_reverse]
    cases c with
    | nil =>
      simp only [List.append_nil] at ha
      have : a2 = a1 := List.reverse_inj.mp ha
      subst this
      simp only [height, Nat.add_zero] at hh
      exact ⟨rfl, by simpa using hrr, by omega⟩
    | cons x c' =>
      have := hs1 x (c' ++ r2) (by simpa using hrr)
      simp only [height] at hh
      omega
  rcases h₁ with ⟨p1, s1⟩ | ⟨q1, e1⟩ <;> rcases h₂ with ⟨p2, s2⟩ | ⟨q2, e2⟩
  · rcases List.append_eq_append_iff.mp hr with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
    · obtain ⟨ea, er, eo⟩ := core a1 r1 o1 a2 r2 o2 c p2 s1 hc1 hc2 ho
      subst ea; subst er; subst eo; rfl
    · obtain ⟨ea, er, eo⟩ := core a2 r2 o2 a1 r1 o1 c p1 s2 hc1 hc2 ho.symm
      subst ea; subst er; subst eo; rfl
  · subst e2
    simp only [height] at ho
    omega
  · subst e1
    simp only [height] at ho
    omega
  · subst e1; subst e2
    simp only [height, List.reverse_nil, List.nil_append] at ho hr
    subst hr
    have : o1 = o2 := by omega
    subst this
    rfl

end

/-- Rows at an offset: how far their top is above the window's top. -/
structure At (R : Type) where
  rows : List R
  offset : Int

/-- An edit of rows at an offset: an edit of the rows, which leaves the
offset, or a new offset. -/
inductive At.Edit (ca : EditStructure) where
  | list (e : Lists.Edit.of ca)
  | to (offset : Int)

def At.apply (ca : EditStructure) : At.Edit ca → At ca.Value → At ca.Value
  | .list e, a => ⟨Lists.edit ca e a.rows, a.offset⟩
  | .to y, a => ⟨a.rows, y⟩

abbrev At.edits (ca : EditStructure) : EditStructure :=
  ⟨At ca.Value, At.Edit ca, At.apply ca⟩

theorem At.run_lists (ca : EditStructure) (es : List (Lists.Edit.of ca)) (a : At ca.Value) :
    run (At.edits ca) (es.map .list) a = ⟨Lists.patch ca es a.rows, a.offset⟩ := by
  induction es generalizing a with
  | nil => rfl
  | cons e t ih => exact ih _

/-- Rows that are an incremental function of a value, at an offset that's a
function of it: the rows' edits, then the offset of the edited value, if
it's a new one. -/
def At.inc (ca : EditStructure) {cb : EditStructure} (g : Inc cb (runs (Lists.editStructure ca)))
    (offset : cb.Value → Int) : Inc cb (runs (At.edits ca)) :=
  ⟨fun b => ⟨g.f b, offset b⟩, fun b d =>
    (g.df b d).map .list ++ (if offset (cb.apply d b) = offset b then [] else [.to (offset (cb.apply d b))])⟩

theorem At.inc_ok (ca : EditStructure) {cb : EditStructure} (g : Inc cb (runs (Lists.editStructure ca)))
    (offset : cb.Value → Int) (h : g.ok) : (At.inc ca g offset).ok := by
  intro b d
  show run (At.edits ca) ((g.df b d).map .list ++
      (if offset (cb.apply d b) = offset b then [] else [.to (offset (cb.apply d b))])) ⟨g.f b, offset b⟩ =
    ⟨g.f (cb.apply d b), offset (cb.apply d b)⟩
  rw [run_append, At.run_lists]
  have e : Lists.patch ca (g.df b d) (g.f b) = g.f (cb.apply d b) := h b d
  by_cases ho : offset (cb.apply d b) = offset b
  · simp only [ho, ite_true]
    show (⟨Lists.patch ca (g.df b d) (g.f b), offset b⟩ : At ca.Value) = _
    rw [e]
  · simp only [ho, ite_false]
    show (⟨Lists.patch ca (g.df b d) (g.f b), offset (cb.apply d b)⟩ : At ca.Value) = _
    rw [e]

variable (ca : EditStructure) (h : ca.Value → Nat)

/-- The scrolled list rows at an offset are. -/
def anchor (a : At ca.Value) : Scroll ca.Value :=
  Scroll.normalize h ⟨[], a.rows, a.offset⟩

/-- The scrolled list's edits for one edit of rows at an offset, and the
scrolled list after them, from the one before. -/
def anchored.df (z : Scroll ca.Value) : At.Edit ca → List (Scroll.Edit ca) × Scroll ca.Value
  | .list e =>
    let z1 := Scroll.apply ca h (.list e) z
    let dy := z.offset h - z1.offset h
    ([.list e, .scroll dy], Scroll.apply ca h (.scroll dy) z1)
  | .to y =>
    let dy := y - z.offset h
    ([.scroll dy], Scroll.apply ca h (.scroll dy) z)

/-- Rows at an offset, as the scrolled list they are, one edit at a time:
it keeps the scrolled list. -/
def anchored.one : Cached (At.edits ca) (runs (Scroll.editStructure ca h)) :=
  ⟨Scroll ca.Value, fun a => (anchor ca h a, anchor ca h a), anchored.df ca h⟩

/-- And for runs of edits. -/
def anchored : Cached (runs (At.edits ca)) (runs (Scroll.editStructure ca h)) :=
  Cached.lift (anchored.one ca h)

theorem anchor_rows (a : At ca.Value) : (anchor ca h a).rows = a.rows := by
  unfold anchor
  rw [rows_normalize]
  rfl

theorem anchor_offset (a : At ca.Value) : (anchor ca h a).offset h = a.offset := by
  unfold anchor
  rw [offset_normalize]
  simp [Scroll.offset, height]

theorem anchored_one_ok : (anchored.one ca h).ok := by
  intro a d
  cases d with
  | list e =>
    have hz : Scroll.apply ca h (.scroll ((anchor ca h a).offset h -
        (Scroll.apply ca h (.list e) (anchor ca h a)).offset h)) (Scroll.apply ca h (.list e) (anchor ca h a)) =
        anchor ca h ⟨Lists.edit ca e a.rows, a.offset⟩ := by
      apply normal_unique h
      · exact normalize_shape h _
      · exact normalize_shape h _
      · rw [rows_apply_scroll, rows_apply_list, anchor_rows, anchor_rows]
      · rw [offset_apply_scroll, anchor_offset, anchor_offset]
        dsimp only
        omega
    exact congrArg (fun z => (z, z)) hz
  | to y =>
    have hz : Scroll.apply ca h (.scroll (y - (anchor ca h a).offset h)) (anchor ca h a) =
        anchor ca h ⟨a.rows, y⟩ := by
      apply normal_unique h
      · exact normalize_shape h _
      · exact normalize_shape h _
      · rw [rows_apply_scroll, anchor_rows, anchor_rows]
      · rw [offset_apply_scroll, anchor_offset, anchor_offset]
        dsimp only
        omega
    exact congrArg (fun z => (z, z)) hz

theorem anchored_ok : (anchored ca h).ok := Cached.lift_ok _ (anchored_one_ok ca h)

end Deui.Lists.Scrolled
