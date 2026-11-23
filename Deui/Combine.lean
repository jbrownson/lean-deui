import Deui.Diff
import Deui.Scene

/-!
Ways of putting incremental functions together, besides one after another:
values in pairs, a value carried along beside a list that's edited, a list
tracked by comparing it with what it was, scenes in layers, and a view
rebuilt when its key changes. Each is correct if its parts are.
-/

namespace Deui

/-- A value edited by being set: an edit is the new value. -/
def latest (A : Type) : EditStructure :=
  ⟨A, A, fun new _ => new⟩

/-- Two values, each edited its own way: an edit is an edit of each. -/
def prod (ca cb : EditStructure) : EditStructure :=
  ⟨ca.Value × cb.Value, ca.Edit × cb.Edit, fun d a => (ca.apply d.1 a.1, cb.apply d.2 a.2)⟩

namespace Cached

variable {ca cb cc : EditStructure}

/-- `g` on the second of a pair, the first carried along as it is. -/
def second (g : Cached cb cc) : Cached (prod ca cb) (prod ca cc) where
  Cache := g.Cache
  f a := ((a.1, (g.f a.2).1), (g.f a.2).2)
  df c d := ((d.1, (g.df c d.2).1), (g.df c d.2).2)

theorem second_ok (g : Cached cb cc) (h : g.ok) : (second (ca := ca) g).ok := by
  intro a d
  have e := h a.2 d.2
  show ((ca.apply d.1 a.1, cc.apply (g.df (g.f a.2).2 d.2).1 (g.f a.2).1), (g.df (g.f a.2).2 d.2).2) =
    ((ca.apply d.1 a.1, (g.f (cb.apply d.2 a.2)).1), (g.f (cb.apply d.2 a.2)).2)
  rw [← e]

/-- `g`, with something of the first of the pair carried beside its result. -/
def carrying {D : Type} (h : ca.Value → D) (g : Cached (prod ca cb) cc) : Cached (prod ca cb) (prod (latest D) cc) where
  Cache := ca.Value × g.Cache
  f a := ((h a.1, (g.f a).1), (a.1, (g.f a).2))
  df k d := ((h (ca.apply d.1 k.1), (g.df k.2 d).1), (ca.apply d.1 k.1, (g.df k.2 d).2))

theorem carrying_ok {D : Type} (h : ca.Value → D) (g : Cached (prod ca cb) cc) (hg : g.ok) :
    (carrying h g).ok := by
  intro a d
  have e := hg a d
  show ((h (ca.apply d.1 a.1), cc.apply (g.df (g.f a).2 d).1 (g.f a).1), (ca.apply d.1 a.1, (g.df (g.f a).2 d).2)) =
    ((h (ca.apply d.1 a.1), (g.f ((prod ca cb).apply d a)).1), (ca.apply d.1 a.1, (g.f ((prod ca cb).apply d a)).2))
  rw [← e]

/-- `g`, with what it's of kept beside its result, edited as it's edited. -/
def beside (g : Cached ca cb) : Cached ca (prod ca cb) where
  Cache := g.Cache
  f a := ((a, (g.f a).1), (g.f a).2)
  df k d := ((d, (g.df k d).1), (g.df k d).2)

theorem beside_ok (g : Cached ca cb) (hg : g.ok) : (beside g).ok := by
  intro a d
  have e := hg a d
  show ((ca.apply d a, cb.apply (g.df (g.f a).2 d).1 (g.f a).1), (g.df (g.f a).2 d).2) =
    ((ca.apply d a, (g.f (ca.apply d a)).1), (g.f (ca.apply d a)).2)
  rw [← e]

/-- A pair whose first is `g` of the pair, and whose second is as it was,
edited as it's edited. -/
def newFirst (g : Cached (prod ca cb) cc) : Cached (prod ca cb) (prod cc cb) where
  Cache := g.Cache
  f a := (((g.f a).1, a.2), (g.f a).2)
  df k d := (((g.df k d).1, d.2), (g.df k d).2)

theorem newFirst_ok (g : Cached (prod ca cb) cc) (hg : g.ok) : (newFirst g).ok := by
  intro a d
  have e := hg a d
  show ((cc.apply (g.df (g.f a).2 d).1 (g.f a).1, cb.apply d.2 a.2), (g.df (g.f a).2 d).2) =
    (((g.f ((prod ca cb).apply d a)).1, cb.apply d.2 a.2), (g.f ((prod ca cb).apply d a)).2)
  rw [← e]

/-- `g`, without the first of the pair it gives. -/
def dropFirst (g : Cached ca (prod cb cc)) : Cached ca cc where
  Cache := g.Cache
  f a := ((g.f a).1.2, (g.f a).2)
  df k d := ((g.df k d).1.2, (g.df k d).2)

theorem dropFirst_ok (g : Cached ca (prod cb cc)) (hg : g.ok) : (dropFirst g).ok := by
  intro a d
  have e := hg a d
  show (cc.apply (g.df (g.f a).2 d).1.2 (g.f a).1.2, (g.df (g.f a).2 d).2) =
    ((g.f (ca.apply d a)).1.2, (g.f (ca.apply d a)).2)
  rw [← e]
  rfl

/-- `g`'s derivative for a run of edits: each edit's run, joined, the cache
passed from one to the next. -/
def runsDf (g : Cached ca (runs cb)) : g.Cache → List ca.Edit → List cb.Edit × g.Cache
  | c, [] => ([], c)
  | c, e :: t => ((g.df c e).1 ++ (runsDf g (g.df c e).2 t).1, (runsDf g (g.df c e).2 t).2)

/-- Lifts `g`, whose derivative gives a run for one edit, to runs of edits. -/
def lift (g : Cached ca (runs cb)) : Cached (runs ca) (runs cb) :=
  ⟨g.Cache, g.f, g.runsDf⟩

theorem lift_ok (g : Cached ca (runs cb)) (h : g.ok) : (lift g).ok := by
  intro a es
  induction es generalizing a with
  | nil => rfl
  | cons e t ih =>
    have he := h a e
    have h1 : run cb (g.df (g.f a).2 e).1 (g.f a).1 = (g.f (ca.apply e a)).1 := congrArg Prod.fst he
    have h2 : (g.df (g.f a).2 e).2 = (g.f (ca.apply e a)).2 := congrArg Prod.snd he
    have ht := ih (ca.apply e a)
    show (run cb ((g.df (g.f a).2 e).1 ++ (runsDf g (g.df (g.f a).2 e).2 t).1) (g.f a).1,
      (runsDf g (g.df (g.f a).2 e).2 t).2) = g.f (run ca t (ca.apply e a))
    rw [run_append, h1, h2]
    exact ht

end Cached

namespace Inc

variable {ca cb cc : EditStructure}

/-- A value as it is, edited as it's edited. -/
def identity : Inc ca ca := ⟨fun a => a, fun _ d => d⟩

theorem identity_ok : (identity (ca := ca)).ok := fun _ _ => rfl

/-- `g` of the second of a pair, the first left behind. -/
def onSecond (g : Inc cb cc) : Inc (prod ca cb) cc :=
  ⟨fun a => g.f a.2, fun a d => g.df a.2 d.2⟩

theorem onSecond_ok (g : Inc cb cc) (h : g.ok) : (onSecond (ca := ca) g).ok :=
  fun a d => h a.2 d.2

end Inc

/-- A function of a value that's set, as a value that's set. -/
def latestMap {A B : Type} (h : A → B) : Cached (latest A) (latest B) :=
  ⟨Unit, fun a => (h a, ()), fun _ a => (h a, ())⟩

theorem latestMap_ok {A B : Type} (h : A → B) : (latestMap h).ok := fun _ _ => rfl

/-! ## A function, kept -/

section
variable {ca : EditStructure} {B : Type}

/-- A function of a value, worked out again only when the value isn't the
same as it was, as `same` sees it; the value goes along beside it. For what
depends on a part of the value that most edits leave alone. -/
def memo (g : ca.Value → B) (same : ca.Value → ca.Value → Bool) : Cached ca (latest (ca.Value × B)) where
  Cache := ca.Value × B
  f a := ((a, g a), (a, g a))
  df c d :=
    let a := ca.apply d c.1
    let b := if same c.1 a then c.2 else g a
    ((a, b), (a, b))

theorem memo_ok (g : ca.Value → B) (same : ca.Value → ca.Value → Bool)
    (sound : ∀ a b, same a b = true → g a = g b) : (memo g same).ok := by
  intro a d
  have hb : (if same a (ca.apply d a) then g a else g (ca.apply d a)) = g (ca.apply d a) := by
    by_cases h : same a (ca.apply d a) = true
    · simp only [h, ite_true]; exact sound _ _ h
    · simp only [h]; rfl
  show (((ca.apply d a, if same a (ca.apply d a) then g a else g (ca.apply d a)) : ca.Value × B),
    ((ca.apply d a, if same a (ca.apply d a) then g a else g (ca.apply d a)) : ca.Value × B)) = _
  rw [hb]
  rfl

end

/-! ## A list, tracked -/

section
variable {ca : EditStructure} {C A : Type}

/-- A list that's a function of a value, as an incremental function of the
value's edits: its derivative works the list out again and gives the edits
from what it was, by `change`. What `carry` gives of the value goes along
beside it. The edits are as few as `same` sees, so what follows does its
work only where the list changed. -/
def tracked (carry : ca.Value → C) (f : ca.Value → List A) (same : A → A → Bool)
    (refl : ∀ a, same a a = true) : Cached ca (prod (latest C) (runs (Lists.editStructure (plain A)))) where
  Cache := ca.Value × List A
  f a := ((carry a, f a), (a, f a))
  df c d :=
    let a := ca.apply d c.1
    ((carry a, Lists.changed (plain A) same refl c.2 (f a)), (a, f a))

theorem tracked_ok (carry : ca.Value → C) (f : ca.Value → List A) (same : A → A → Bool)
    (refl : ∀ a, same a a = true) (sound : ∀ a b, same a b = true → a = b) :
    (tracked carry f same refl).ok := by
  intro a d
  have hx : Lists.patch (plain A) (Lists.changed (plain A) same refl (f a) (f (ca.apply d a))) (f a) =
      f (ca.apply d a) := Lists.changed_ok (plain A) same refl sound (f a) (f (ca.apply d a))
  exact congrArg (fun l => ((carry (ca.apply d a), l), (ca.apply d a, f (ca.apply d a)))) hx

end

/-! ## Scenes -/

theorem run_update_head (es : List SceneEdit) (x y : Int32) (s : Scene) (rest : List Scene) :
    run sceneEdits (es.map (.update 0)) (.group x y (s :: rest)) = .group x y (run sceneEdits es s :: rest) := by
  induction es generalizing s with
  | nil => rfl
  | cons e t ih => exact ih (e.apply s)

theorem run_update_second (es : List SceneEdit) (x y : Int32) (a s : Scene) (rest : List Scene) :
    run sceneEdits (es.map (.update 1)) (.group x y (a :: s :: rest)) =
      .group x y (a :: run sceneEdits es s :: rest) := by
  induction es generalizing s with
  | nil => rfl
  | cons e t ih => exact ih (e.apply s)

section
variable {ca : EditStructure}

/-- Two views, one over the other: a group of the two scenes, the second
drawn on top. -/
def layers (g h : Cached ca (runs sceneEdits)) : Cached ca (runs sceneEdits) where
  Cache := g.Cache × h.Cache
  f a := (.group 0 0 [(g.f a).1, (h.f a).1], (g.f a).2, (h.f a).2)
  df c d := ((g.df c.1 d).1.map (.update 0) ++ (h.df c.2 d).1.map (.update 1), (g.df c.1 d).2, (h.df c.2 d).2)

theorem layers_ok (g h : Cached ca (runs sceneEdits)) (hg : g.ok) (hh : h.ok) : (layers g h).ok := by
  intro a d
  have eg := hg a d
  have eh := hh a d
  have g1 : run sceneEdits (g.df (g.f a).2 d).1 (g.f a).1 = (g.f (ca.apply d a)).1 := congrArg Prod.fst eg
  have g2 : (g.df (g.f a).2 d).2 = (g.f (ca.apply d a)).2 := congrArg Prod.snd eg
  have h1 : run sceneEdits (h.df (h.f a).2 d).1 (h.f a).1 = (h.f (ca.apply d a)).1 := congrArg Prod.fst eh
  have h2 : (h.df (h.f a).2 d).2 = (h.f (ca.apply d a)).2 := congrArg Prod.snd eh
  show (run sceneEdits ((g.df (g.f a).2 d).1.map (.update 0) ++ (h.df (h.f a).2 d).1.map (.update 1))
      (.group 0 0 [(g.f a).1, (h.f a).1]), (g.df (g.f a).2 d).2, (h.df (h.f a).2 d).2) = _
  rw [run_append, run_update_head, run_update_second, g1, g2, h1, h2]
  rfl

variable {K : Type} [DecidableEq K]

/-- A view chosen by a key of the value, in a group of its own: while the
key stays, the chosen view's derivative; when it changes, the view of the
new key takes the old one's place whole. It's how a view follows something
its derivative doesn't, like the window's size. And where `big` says an
edit is one the derivative would spend more on than drawing again, the
view is drawn again in the same way. -/
def keyed (key : ca.Value → K) (g : K → Cached ca (runs sceneEdits))
    (big : ca.Value → ca.Edit → Bool := fun _ _ => false) : Cached ca (runs sceneEdits) where
  Cache := ca.Value × ((k : K) × (g k).Cache)
  f a := (.group 0 0 [((g (key a)).f a).1], a, ⟨key a, ((g (key a)).f a).2⟩)
  df c d :=
    let a := ca.apply d c.1
    if key a = c.2.1 ∧ big c.1 d = false then
      (((g c.2.1).df c.2.2 d).1.map (.update 0), a, ⟨c.2.1, ((g c.2.1).df c.2.2 d).2⟩)
    else
      ([.delete 0, .insert 0 ((g (key a)).f a).1], a, ⟨key a, ((g (key a)).f a).2⟩)

theorem keyed_ok (key : ca.Value → K) (g : K → Cached ca (runs sceneEdits))
    (big : ca.Value → ca.Edit → Bool) (hg : ∀ k, (g k).ok) : (keyed key g big).ok := by
  intro a d
  by_cases hk : key (ca.apply d a) = key a ∧ big a d = false
  · have e := hg (key a) a d
    have e1 : run sceneEdits ((g (key a)).df ((g (key a)).f a).2 d).1 ((g (key a)).f a).1 =
        ((g (key a)).f (ca.apply d a)).1 := congrArg Prod.fst e
    have e2 : ((g (key a)).df ((g (key a)).f a).2 d).2 = ((g (key a)).f (ca.apply d a)).2 :=
      congrArg Prod.snd e
    simp only [keyed, hk, and_self, ite_true]
    show (run sceneEdits (((g (key a)).df ((g (key a)).f a).2 d).1.map (.update 0))
      (.group 0 0 [((g (key a)).f a).1]), _, _) = _
    rw [run_update_head, e1, e2, hk.1]
  · simp only [keyed, hk, ite_false]
    rfl

end

end Deui
