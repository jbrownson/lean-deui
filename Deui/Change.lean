/-
Edits to any value, and incremental functions: the change structures of
bend-deui's `deui/change/`, from lean-puri's port of them, with `Cached` and
`compose` added.
-/

namespace Deui

/-- How values are edited: values of type `Value`, edits of type `Edit`, and
`apply`, which applies one. These are the edits a type supplies; they needn't
get from every value to every other. `runs` and `whole` add ways to get
further. -/
structure EditStructure where
  Value : Type
  Edit : Type
  apply : Edit → Value → Value

/-- One edit gets from any value to any other, and which edit it is. -/
def reaches (ce : EditStructure) : Type :=
  (a b : ce.Value) → { d : ce.Edit // ce.apply d a = b }

/-- A change structure: an edit structure, with the proof that one edit gets
from any value to any other. -/
structure ChangeStructure where
  edits : EditStructure
  reach : reaches edits

/-- The edits of values that have none of their own. -/
def none (A : Type) : EditStructure :=
  ⟨A, Empty, fun e _ => nomatch e⟩

/-- The value a run of edits leaves, applied in order. -/
def run (ce : EditStructure) : List ce.Edit → ce.Value → ce.Value
  | [], a => a
  | e :: t, a => run ce t (ce.apply e a)

/-- Runs of `ce`'s edits, applied in order: no edits leaves a value as it
is, and one run then another is the two joined. -/
abbrev runs (ce : EditStructure) : EditStructure :=
  ⟨ce.Value, List ce.Edit, run ce⟩

/-- Running joined runs runs the first, then the second. -/
theorem run_append (ce : EditStructure) (xs ys : List ce.Edit) (a : ce.Value) :
    run ce (xs ++ ys) a = run ce ys (run ce xs a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons e t ih => exact ih _

/-- An edit of a value: a whole new one, or one of its own edits. -/
inductive Whole (ce : EditStructure) where
  | replace (x : ce.Value)
  | apply (e : ce.Edit)

def whole.apply (ce : EditStructure) : Whole ce → ce.Value → ce.Value
  | .replace x, _ => x
  | .apply e, a => ce.apply e a

/-- `ce`'s edits, and replacing the whole value. -/
abbrev whole (ce : EditStructure) : EditStructure :=
  ⟨ce.Value, Whole ce, whole.apply ce⟩

/-- `whole ce`, which is a change structure whatever `ce` is: replacing gets
from any value to any other. -/
def whole.changeStructure (ce : EditStructure) : ChangeStructure :=
  ⟨whole ce, fun _ b => ⟨.replace b, rfl⟩⟩

/-- An incremental function, from values edited as `ca` says to values
edited as `cb` says: a function `f`, and its derivative `df`, which gives the
edit to `f`'s result from a value and the value's edit. -/
structure Inc (ca cb : EditStructure) where
  f : ca.Value → cb.Value
  df : ca.Value → ca.Edit → cb.Edit

/-- `g`'s derivative is correct: applying its edit to `f a` gives `f` of the
edited value. -/
def Inc.ok {ca cb : EditStructure} (g : Inc ca cb) : Prop :=
  ∀ a d, cb.apply (g.df a d) (g.f a) = g.f (ca.apply d a)

/-- `lift`'s derivative, for a run of edits from the value before them: `g`'s
run for each edit, joined in order. -/
def lift.run {ca cb : EditStructure} (g : Inc ca (runs cb)) : List ca.Edit → ca.Value → List cb.Edit
  | [], _ => []
  | e :: t, a => g.df a e ++ lift.run g t (ca.apply e a)

/-- Lifts `g`, whose derivative gives a run for one edit, to an `Inc` whose
derivative handles runs. -/
def lift {ca cb : EditStructure} (g : Inc ca (runs cb)) : Inc (runs ca) (runs cb) :=
  ⟨g.f, fun a es => lift.run g es a⟩

/-- Lifting a correct `Inc` gives a correct one. -/
theorem lift_ok {ca cb : EditStructure} (g : Inc ca (runs cb)) (h : g.ok) : (lift g).ok := by
  intro a es
  induction es generalizing a with
  | nil => rfl
  | cons e t ih =>
    show run cb (g.df a e ++ lift.run g t (ca.apply e a)) (g.f a) = g.f (run ca t (ca.apply e a))
    rw [run_append]
    exact (congrArg (run cb (lift.run g t (ca.apply e a))) (h a e)).trans (ih _)

/-- `whole.lift`'s derivative: replacing the input replaces the result with
`f` of the new value, and an edit gives `g`'s edit. -/
def whole.lift.df {ca cb : EditStructure} (g : Inc ca cb) : ca.Value → Whole ca → Whole cb
  | _, .replace x => .replace (g.f x)
  | a, .apply e => .apply (g.df a e)

/-- Lifts `g` to values that can also be replaced. -/
def whole.lift {ca cb : EditStructure} (g : Inc ca cb) : Inc (whole ca) (whole cb) :=
  ⟨g.f, whole.lift.df g⟩

theorem whole_lift_ok {ca cb : EditStructure} (g : Inc ca cb) (h : g.ok) : (whole.lift g).ok := by
  intro a w
  cases w with
  | replace x => rfl
  | apply e => exact h a e

/-- `f`, with the derivative that recomputes: whatever the edit, replace the
result. -/
def recompute {ca cb : EditStructure} (f : ca.Value → cb.Value) : Inc ca (whole cb) :=
  ⟨f, fun a e => .replace (f (ca.apply e a))⟩

theorem recompute_ok {ca cb : EditStructure} (f : ca.Value → cb.Value) : (recompute (cb := cb) f).ok :=
  fun _ _ => rfl


/-! ## Keeping

An `Inc`'s derivative takes the value before the edit, so one `Inc` after
another would have to run the first again to give the second its input. A
`Cached` function keeps what its derivative needs instead. -/

/-- An incremental function that keeps what its derivative needs: `f` gives
its result and a cache, and `df`, from the cache and an edit, gives the edit
to the result and the cache for the edited value. -/
structure Cached (ca cb : EditStructure) where
  Cache : Type
  f : ca.Value → cb.Value × Cache
  df : Cache → ca.Edit → cb.Edit × Cache

/-- `g`'s derivative is correct: its answer, from what `f` kept for `a`, gives
what `f` gives for the edited value, result and cache alike. -/
def Cached.ok {ca cb : EditStructure} (g : Cached ca cb) : Prop :=
  ∀ a d, (cb.apply (g.df (g.f a).2 d).1 (g.f a).1, (g.df (g.f a).2 d).2) = g.f (ca.apply d a)

/-- An `Inc`, keeping its input for its derivative. -/
def cached {ca cb : EditStructure} (g : Inc ca cb) : Cached ca cb :=
  ⟨ca.Value, fun a => (g.f a, a), fun a d => (g.df a d, ca.apply d a)⟩

/-- A cached `Inc` is correct, if the `Inc` is. -/
theorem cached_ok {ca cb : EditStructure} (g : Inc ca cb) (h : g.ok) : (cached g).ok := by
  intro a d
  simp only [cached, h a d]

/-- `g` after `f`: `f`'s result goes to `g`, and the cache is both of
theirs. Its derivative gives `f`'s edit for the input's, from `f`'s cache,
then `g`'s for that, from `g`'s. -/
def compose {ca cb cc : EditStructure} (f : Cached ca cb) (g : Cached cb cc) : Cached ca cc where
  Cache := f.Cache × g.Cache
  f a := ((g.f (f.f a).1).1, (f.f a).2, (g.f (f.f a).1).2)
  df c d := ((g.df c.2 (f.df c.1 d).1).1, (f.df c.1 d).2, (g.df c.2 (f.df c.1 d).1).2)

/-- `g` after `f` is correct, if `f` and `g` are. -/
theorem compose_ok {ca cb cc : EditStructure} (f : Cached ca cb) (g : Cached cb cc)
    (hf : f.ok) (hg : g.ok) : (compose f g).ok := by
  intro a d
  have ef := hf a d
  have eg := hg (f.f a).1 (f.df (f.f a).2 d).1
  simp only [compose]
  rw [← ef, ← eg]

end Deui
