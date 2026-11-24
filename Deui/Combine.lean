import Deui.Lists
import Deui.Scene

/-!
Ways of putting incremental functions together, besides one after another:
values in pairs, a value carried along beside what's worked out from it,
scenes in layers, and a view drawn afresh when its key changes. Each is
correct if its parts are.
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

/-- `g`, with the first of the pair kept beside its result, for what comes
after to read too. -/
def keeping (g : Cached (prod ca cb) cc) : Cached (prod ca cb) (prod ca cc) where
  Cache := g.Cache
  f a := ((a.1, (g.f a).1), (g.f a).2)
  df c d := ((d.1, (g.df c d).1), (g.df c d).2)

theorem keeping_ok (g : Cached (prod ca cb) cc) (h : g.ok) : (keeping g).ok := by
  intro a d
  have e := h a d
  show ((ca.apply d.1 a.1, cc.apply (g.df (g.f a).2 d).1 (g.f a).1), (g.df (g.f a).2 d).2) =
    ((ca.apply d.1 a.1, (g.f ((prod ca cb).apply d a)).1), (g.f ((prod ca cb).apply d a)).2)
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

/-- A pair whose first is set, with a function of it in its place. -/
def mapFirst {A B : Type} (h : A → B) : Cached (prod (latest A) cb) (prod (latest B) cb) :=
  ⟨Unit, fun a => ((h a.1, a.2), ()), fun _ d => ((h d.1, d.2), ())⟩

theorem mapFirst_ok {A B : Type} (h : A → B) : (mapFirst (cb := cb) h).ok := fun _ _ => rfl

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

/-- A view that's always the one scene, whatever the value. -/
def still (scene : Scene) : Cached ca (runs sceneEdits) :=
  ⟨Unit, fun _ => (scene, ()), fun _ _ => ([], ())⟩

theorem still_ok (scene : Scene) : (still (ca := ca) scene).ok := fun _ _ => rfl

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
