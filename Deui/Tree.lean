import Deui.Fit
import Deui.Combine

/-!
A tree drawn node by node: each node's own doc from its label and a
context, its kids in the doc's slots. The frames are an incremental
function of the context and the tree. An edit of the tree is the same edit
of the frames. An edit of the context draws again the nodes it makes
stale, and no others: a node says whether an edit of the context could
change its doc, and what it says is held to a law. Nothing is recorded
while drawing; a node drawn from what it looks up by key is stale when one
of its keys is touched.
-/

namespace Deui

/-- A tree: a label, and kids. -/
inductive Tree (L : Type) where
  | node (label : L) (kids : List (Tree L))

namespace Tree

variable {L S : Type}

/-- Where a kid comes from, when a node is given a new label and kids: one
it had, or a new one. -/
inductive Source (L : Type) where
  | kept (j : Nat)
  | fresh (t : Tree L)

/-- The kid a source gives; none for a kid the node never had. -/
def Source.tree? (olds : List (Tree L)) : Source L → Option (Tree L)
  | .kept j => olds[j]?
  | .fresh t => some t

/-- An edit of a tree: a new tree; an edit of a kid; or a new label, with
kids kept and new. -/
inductive Edit (L : Type) where
  | replace (t : Tree L)
  | kid (i : Nat) (e : Edit L)
  | reshape (label : L) (kids : List (Source L))
  /-- Runs of edits, a run for each kid, in the kids' order: what many
  `kid` edits come to, as one. -/
  | each (runs : List (List (Edit L)))

mutual
def Edit.apply : Edit L → Tree L → Tree L
  | .replace t, _ => t
  | .kid i e, .node l kids => .node l (kids.modify i (Edit.apply e))
  | .reshape l sources, .node _ kids => .node l (sources.filterMap (Source.tree? kids))
  | .each runs, .node l kids => .node l (Edit.applyEach runs kids)

/-- A run of edits, applied in order. -/
def Edit.applyRun : List (Edit L) → Tree L → Tree L
  | [], t => t
  | e :: es, t => Edit.applyRun es (Edit.apply e t)

/-- Each kid with its run applied. -/
def Edit.applyEach : List (List (Edit L)) → List (Tree L) → List (Tree L)
  | es :: runs, k :: ks => Edit.applyRun es k :: Edit.applyEach runs ks
  | _, ks => ks
end

abbrev edits (L : Type) : EditStructure := ⟨Tree L, Edit L, Edit.apply⟩

theorem Edit.applyRun_eq : ∀ (es : List (Edit L)) (t : Tree L), Edit.applyRun es t = run (edits L) es t
  | [], _ => rfl
  | e :: es, t => by
    rw [Edit.applyRun]
    exact Edit.applyRun_eq es (Edit.apply e t)

theorem Edit.applyEach_nil (ks : List (Tree L)) : Edit.applyEach [] ks = ks := by
  cases ks <;> rfl

/-- A run of edits of one kid. -/
theorem run_kid (l : L) (pre : List (Tree L)) (x : Tree L) (post : List (Tree L)) (es : List (Edit L)) :
    run (edits L) (es.map (.kid pre.length)) (.node l (pre ++ x :: post)) =
      .node l (pre ++ run (edits L) es x :: post) := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
    show run (edits L) (es.map (.kid pre.length)) (Edit.apply (.kid pre.length e) (.node l (pre ++ x :: post))) = _
    simp only [Edit.apply, Fit.modify_append_cons]
    exact ih (Edit.apply e x)

/-- Kids kept, one after another, are the kids there. -/
theorem kept_range (kids : List (Tree L)) : ∀ (n i : Nat), i + n ≤ kids.length →
    ((List.range' i n).map Source.kept).filterMap (Source.tree? kids) = (kids.drop i).take n
  | 0, _, _ => by simp
  | n + 1, i, h => by
    have hi : i < kids.length := by omega
    rw [List.range'_succ, List.map_cons, List.filterMap_cons]
    simp only [Source.tree?, List.getElem?_eq_getElem hi]
    rw [kept_range kids n (i + 1) (by omega), List.drop_eq_getElem_cons hi, List.take_succ_cons]

/-! ## Frames -/

mutual
/-- A tree's frames: each node's doc from its label, its kids' frames in
the doc's slots. -/
def frame (own : L → Fit.Doc S) : Tree L → Fit.Frame S
  | .node l kids => .node (own l) (frames own kids)

def frames (own : L → Fit.Doc S) : List (Tree L) → List (Fit.Frame S)
  | [] => []
  | k :: ks => frame own k :: frames own ks
end

theorem frames_eq (own : L → Fit.Doc S) (ks : List (Tree L)) : frames own ks = ks.map (frame own) := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [frames, ih]

theorem frame_node (own : L → Fit.Doc S) (l : L) (kids : List (Tree L)) :
    frame own (.node l kids) = .node (own l) (kids.map (frame own)) := by
  rw [frame, frames_eq]

/-- A source of a kid, as a source of its frame; none for a kid the node
never had. -/
def Source.frame (own : L → Fit.Doc S) (n : Nat) : Source L → Option (Fit.Source S)
  | .kept j => if j < n then some (.kept j) else none
  | .fresh t => some (.fresh (Tree.frame own t))

mutual
/-- An edit of a tree, as the edit of its frames: the same, node for node.
It takes the tree as it was for how many kids each node had. -/
def Edit.frame (own : L → Fit.Doc S) : Edit L → Tree L → Fit.Edit S
  | .replace t, _ => .replace (Tree.frame own t)
  | .kid i e, .node _ kids =>
    match kids[i]? with
    | some k => .kid i (Edit.frame own e k)
    | none => .kid i (.replace (.node (.row []) []))
  | .reshape l sources, .node _ kids => .reshape (own l) (sources.filterMap (Source.frame own kids.length))
  | .each runs, .node _ kids => .each (Edit.frameEach own runs kids)

/-- A run of edits, each as the edit of the frames of the tree it finds. -/
def Edit.frameRun (own : L → Fit.Doc S) : List (Edit L) → Tree L → List (Fit.Edit S)
  | [], _ => []
  | e :: es, t => Edit.frame own e t :: Edit.frameRun own es (Edit.apply e t)

def Edit.frameEach (own : L → Fit.Doc S) : List (List (Edit L)) → List (Tree L) → List (List (Fit.Edit S))
  | es :: runs, k :: ks => Edit.frameRun own es k :: Edit.frameEach own runs ks
  | _, _ => []
end

theorem modify_map {α β : Type} (f : α → β) (g : β → β) (h : α → α) :
    ∀ (xs : List α) (i : Nat), (∀ x, xs[i]? = some x → g (f x) = f (h x)) →
      (xs.map f).modify i g = (xs.modify i h).map f
  | [], _, _ => by simp
  | x :: xs, 0, hx => by simp [List.modify_cons, hx x]
  | x :: xs, i + 1, hx => by
    simp only [List.map_cons, List.modify_succ_cons]
    rw [modify_map f g h xs i fun y hy => hx y (by simpa using hy)]

mutual
/-- An edit of the tree is the same edit of its frames. -/
theorem Edit.frame_ok (own : L → Fit.Doc S) : ∀ (e : Edit L) (t : Tree L),
    Fit.Edit.apply (e.frame own t) (Tree.frame own t) = Tree.frame own (e.apply t)
  | .replace _, _ => rfl
  | .kid i e, .node l kids => by
    simp only [Edit.apply, frame_node]
    cases hk : kids[i]? with
    | none =>
      simp only [Edit.frame, hk, Fit.Edit.apply]
      have out : kids.length ≤ i := by
        rcases Nat.lt_or_ge i kids.length with h | h
        · simp [List.getElem?_eq_getElem h] at hk
        · exact h
      rw [List.modify_eq_self (by simpa using out), List.modify_eq_self out]
    | some k =>
      simp only [Edit.frame, hk, Fit.Edit.apply]
      rw [modify_map (Tree.frame own) _ (Edit.apply e) kids i fun x hx => by
        rw [hk] at hx
        cases hx
        exact Edit.frame_ok own e k]
  | .reshape l sources, .node l0 kids => by
    simp only [Edit.apply, Edit.frame, frame_node, Fit.Edit.apply]
    congr 1
    induction sources with
    | nil => rfl
    | cons s rest ih =>
      cases s with
      | fresh t => simp [Source.frame, Source.tree?, Fit.Source.frame, ih]
      | kept j =>
        by_cases hj : j < kids.length
        · simp [Source.frame, Source.tree?, Fit.Source.frame, hj, ih]
        · simp [Source.frame, Source.tree?, hj, ih]
  | .each runs, .node l kids => by
    simp only [Edit.apply, Edit.frame, frame_node, Fit.Edit.apply]
    rw [Edit.frameEach_ok own runs kids]

theorem Edit.frameRun_ok (own : L → Fit.Doc S) : ∀ (es : List (Edit L)) (t : Tree L),
    Fit.Edit.applyRun (Edit.frameRun own es t) (Tree.frame own t) = Tree.frame own (Edit.applyRun es t)
  | [], _ => rfl
  | e :: es, t => by
    simp only [Edit.frameRun, Fit.Edit.applyRun, Edit.applyRun]
    rw [Edit.frame_ok own e t]
    exact Edit.frameRun_ok own es (Edit.apply e t)

theorem Edit.frameEach_ok (own : L → Fit.Doc S) : ∀ (runs : List (List (Edit L))) (ks : List (Tree L)),
    Fit.Edit.applyEach (Edit.frameEach own runs ks) (ks.map (Tree.frame own)) =
      (Edit.applyEach runs ks).map (Tree.frame own)
  | [], ks => by
    cases ks <;> simp [Edit.frameEach, Edit.applyEach, Fit.Edit.applyEach]
  | es :: runs, [] => by simp [Edit.frameEach, Edit.applyEach, Fit.Edit.applyEach]
  | es :: runs, k :: ks => by
    simp only [Edit.frameEach, Edit.applyEach, List.map_cons, Fit.Edit.applyEach]
    rw [Edit.frameRun_ok own es k, Edit.frameEach_ok own runs ks]
end

/-- A tree's frames, as an incremental function of the tree. -/
def framed (own : L → Fit.Doc S) : Inc (edits L) (runs (Fit.edits S)) :=
  ⟨frame own, fun t e => [e.frame own t]⟩

theorem framed_ok (own : L → Fit.Doc S) : (framed own).ok := fun t e => Edit.frame_ok own e t

/-! ## A new context -/

mutual
/-- The edits that draw again each node that's stale, its kids kept: the
node's own, then its kids' runs as one edit, so the layout walks each
frame once however many of its kids changed. A subtree with nothing stale
gives none. -/
def refresh (own : L → Fit.Doc S) (stale : L → Bool) : Tree L → List (Fit.Edit S)
  | .node l kids =>
    let runs := refreshKids own stale kids
    let below := if runs.isEmpty then [] else [Fit.Edit.each runs]
    if stale l then .reshape (own l) ((List.range kids.length).map .kept) :: below else below

/-- Each kid's run, as far as the last kid that has one. -/
def refreshKids (own : L → Fit.Doc S) (stale : L → Bool) : List (Tree L) → List (List (Fit.Edit S))
  | [] => []
  | k :: ks =>
    let run := refresh own stale k
    let rest := refreshKids own stale ks
    if run.isEmpty && rest.isEmpty then [] else run :: rest
end

theorem kept_all {α : Type} (d : α) (xs : List α) :
    (List.range xs.length).map (fun j => (xs[j]?).getD d) = xs := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp at h1
    simp [h1]

theorem applyEach_nil (ks : List (Fit.Frame S)) : Fit.Edit.applyEach [] ks = ks := by
  cases ks <;> rfl

mutual
/-- Drawing the stale nodes again takes the frames to the ones the new way
of drawing gives, if every node that isn't stale is drawn the same by it. -/
theorem refresh_ok (own own' : L → Fit.Doc S) (stale : L → Bool) (h : ∀ l, stale l = false → own' l = own l) :
    ∀ t : Tree L, run (Fit.edits S) (refresh own' stale t) (frame own t) = frame own' t
  | .node l kids => by
    have below := refreshKids_ok own own' stale h kids
    -- The kids' runs, on a node with any doc.
    have deep : ∀ doc : Fit.Doc S,
        run (Fit.edits S) (if (refreshKids own' stale kids).isEmpty then []
          else [Fit.Edit.each (refreshKids own' stale kids)]) (.node doc (frames own kids)) =
          .node doc (frames own' kids) := by
      intro doc
      cases hr : (refreshKids own' stale kids).isEmpty with
      | true =>
        have none_ : refreshKids own' stale kids = [] := by simpa using hr
        rw [none_, applyEach_nil] at below
        simp only [ite_true]
        show Fit.Frame.node doc (frames own kids) = _
        rw [below]
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        show Fit.Edit.apply (.each (refreshKids own' stale kids)) (.node doc (frames own kids)) = _
        simp only [Fit.Edit.apply, below]
    simp only [refresh, frame]
    cases hs : stale l with
    | true =>
      simp only [ite_true]
      show run (Fit.edits S) _
        (Fit.Edit.apply (.reshape (own' l) ((List.range kids.length).map .kept)) (.node (own l) (frames own kids))) = _
      have all : ((List.range kids.length).map Fit.Source.kept).map (Fit.Source.frame (frames own kids)) =
          frames own kids := by
        have := kept_all (Fit.Frame.node (.row []) []) (frames own kids)
        rw [frames_eq, List.length_map] at this
        rw [frames_eq, List.map_map]
        exact this
      simp only [Fit.Edit.apply, all]
      exact deep (own' l)
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [← h l hs]
      exact deep (own' l)

theorem refreshKids_ok (own own' : L → Fit.Doc S) (stale : L → Bool) (h : ∀ l, stale l = false → own' l = own l) :
    ∀ ks : List (Tree L), Fit.Edit.applyEach (refreshKids own' stale ks) (frames own ks) = frames own' ks
  | [] => rfl
  | k :: ks => by
    have first := refresh_ok own own' stale h k
    have rest := refreshKids_ok own own' stale h ks
    simp only [refreshKids, frames]
    cases hn : ((refresh own' stale k).isEmpty && (refreshKids own' stale ks).isEmpty) with
    | true =>
      obtain ⟨h1, h2⟩ : refresh own' stale k = [] ∧ refreshKids own' stale ks = [] := by simpa using hn
      rw [h1] at first
      rw [h2, applyEach_nil] at rest
      simp only [ite_true, applyEach_nil]
      rw [← rest]
      exact congrArg (· :: frames own ks) first
    | false =>
      simp only [Bool.false_eq_true, ite_false, Fit.Edit.applyEach, Fit.Edit.applyRun_eq]
      rw [first, rest]
end

/-! ## Under a context -/

variable {cc : EditStructure}

/-- The frames' edits for a new way of drawing and a run of edits of the
tree: the stale nodes drawn again, unless the new way is the old, then the
tree's edits as the frames'. -/
def redraw (own' : L → Fit.Doc S) (stale : L → Bool) (calm : Bool) (t : Tree L) (es : List (Edit L)) :
    List (Fit.Edit S) :=
  let after := lift.run (framed own') es t
  if calm then after else refresh own' stale t ++ after

/-- A tree's frames, as an incremental function of a context and the tree.
`prepare` works out once what an edit of the context is; `stale` says
from that whether the edit could change a node's own doc, and `calm`
whether an edit of a context changes none. An edit of the tree is the same
edit of the frames; an edit of the context that isn't calm draws the stale
nodes again, and walks the rest. -/
def drawn {P : Type} (own : cc.Value → L → Fit.Doc S) (prepare : cc.Value → cc.Edit → P) (stale : P → L → Bool)
    (calm : cc.Value → cc.Edit → Bool) : Inc (prod cc (runs (edits L))) (runs (Fit.edits S)) where
  f a := frame (own a.1) a.2
  df a d := redraw (own (cc.apply d.1 a.1)) (stale (prepare a.1 d.1)) (calm a.1 d.1) a.2 d.2

/-- Drawing under a context is right, if a calm edit changes no node's
doc, and an edit changes only the docs of nodes it makes stale. -/
theorem drawn_ok {P : Type} (own : cc.Value → L → Fit.Doc S) (prepare : cc.Value → cc.Edit → P)
    (stale : P → L → Bool) (calm : cc.Value → cc.Edit → Bool)
    (hcalm : ∀ c d l, calm c d = true → own (cc.apply d c) l = own c l)
    (hstale : ∀ c d l, stale (prepare c d) l = false → own (cc.apply d c) l = own c l) :
    (drawn (S := S) own prepare stale calm).ok := by
  intro a d
  have after := lift_ok (framed (S := S) (own (cc.apply d.1 a.1))) (framed_ok _) a.2 d.2
  show run (Fit.edits S) _ (frame (own a.1) a.2) = frame (own (cc.apply d.1 a.1)) (run (edits L) d.2 a.2)
  simp only [drawn, redraw]
  cases hc : calm a.1 d.1 with
  | true =>
    have same : own (cc.apply d.1 a.1) = own a.1 := funext fun l => hcalm a.1 d.1 l hc
    simp only [ite_true]
    rw [same] at after ⊢
    exact after
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [run_append, refresh_ok (own a.1) (own (cc.apply d.1 a.1)) (stale (prepare a.1 d.1)) (hstale a.1 d.1) a.2]
    exact after

/-! ## Drawn from what's looked up -/

variable {K A : Type}

/-- A node drawn from its label and what its keys look up in the context:
the context reaches the doc only through the answers. -/
def reading (get : cc.Value → K → A) (keys : L → List K) (draw : L → List A → Fit.Doc S) :
    cc.Value → L → Fit.Doc S :=
  fun c l => draw l ((keys l).map (get c))

/-- Whether an edit touches one of a node's keys. -/
def touched (touches : cc.Edit → K → Bool) (keys : L → List K) : cc.Value → cc.Edit → L → Bool :=
  fun _ d l => (keys l).any (touches d)

/-- A node none of whose keys an edit touches is drawn as it was, if a key
an edit doesn't touch looks up what it did. -/
theorem reading_touched (get : cc.Value → K → A) (keys : L → List K) (draw : L → List A → Fit.Doc S)
    (touches : cc.Edit → K → Bool) (h : ∀ c d k, touches d k = false → get (cc.apply d c) k = get c k)
    (c : cc.Value) (d : cc.Edit) (l : L) (hl : touched touches keys c d l = false) :
    reading get keys draw (cc.apply d c) l = reading get keys draw c l := by
  simp only [reading]
  congr 1
  apply List.map_congr_left
  intro k hk
  apply h
  simp only [touched, List.any_eq_false] at hl
  simpa using hl k hk

/-! ### Looked up through what's looked up -/

/-- A context as a node sees it: what its keys look up, and nothing for
any other key. -/
def only (get : cc.Value → K → Option A) [BEq K] (keys : List K) (c : cc.Value) (k : K) : Option A :=
  if keys.contains k then get c k else none

/-- A node drawn from its label and a lookup that answers only for its
keys: the keys its label gives, and the keys those answers give. A node
that reads through a first answer to a second lists both; a key left out
looks up nothing, whatever the context holds. -/
def reading2 [BEq K] (get : cc.Value → K → Option A) (keys1 : L → List K)
    (keys2 : L → (K → Option A) → List K) (draw : L → (K → Option A) → Fit.Doc S) : cc.Value → L → Fit.Doc S :=
  fun c l => draw l (only get (keys1 l ++ keys2 l (only get (keys1 l) c)) c)

/-- Whether an edit touches one of a node's keys, first or second. -/
def touched2 [BEq K] (get : cc.Value → K → Option A) (touches : cc.Edit → K → Bool) (keys1 : L → List K)
    (keys2 : L → (K → Option A) → List K) : cc.Value → cc.Edit → L → Bool :=
  fun c d l => (keys1 l).any (touches d) || (keys2 l (only get (keys1 l) c)).any (touches d)

theorem only_untouched [BEq K] [LawfulBEq K] (get : cc.Value → K → Option A) (touches : cc.Edit → K → Bool)
    (h : ∀ c d k, touches d k = false → get (cc.apply d c) k = get c k) (keys : List K) (c : cc.Value)
    (d : cc.Edit) (hk : keys.any (touches d) = false) : only get keys (cc.apply d c) = only get keys c := by
  funext k
  simp only [only]
  split
  · next hc =>
    apply h
    simp only [List.any_eq_false] at hk
    simpa using hk k (by simpa using hc)
  · rfl

/-- A node none of whose keys an edit touches is drawn as it was. -/
theorem reading2_touched [BEq K] [LawfulBEq K] (get : cc.Value → K → Option A) (keys1 : L → List K)
    (keys2 : L → (K → Option A) → List K) (draw : L → (K → Option A) → Fit.Doc S)
    (touches : cc.Edit → K → Bool) (h : ∀ c d k, touches d k = false → get (cc.apply d c) k = get c k)
    (c : cc.Value) (d : cc.Edit) (l : L) (hl : touched2 get touches keys1 keys2 c d l = false) :
    reading2 get keys1 keys2 draw (cc.apply d c) l = reading2 get keys1 keys2 draw c l := by
  simp only [touched2, Bool.or_eq_false_iff] at hl
  have first := only_untouched get touches h (keys1 l) c d hl.1
  simp only [reading2, first]
  rw [only_untouched get touches h _ c d (by simpa [List.any_append] using hl)]

end Tree

end Deui
