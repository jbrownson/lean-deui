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

def Edit.apply : Edit L → Tree L → Tree L
  | .replace t, _ => t
  | .kid i e, .node l kids => .node l (kids.modify i (Edit.apply e))
  | .reshape l sources, .node _ kids => .node l (sources.filterMap (Source.tree? kids))

abbrev edits (L : Type) : EditStructure := ⟨Tree L, Edit L, Edit.apply⟩

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

/-- An edit of a tree, as the edit of its frames: the same, node for node.
It takes the tree as it was for how many kids each node had. -/
def Edit.frame (own : L → Fit.Doc S) : Edit L → Tree L → Fit.Edit S
  | .replace t, _ => .replace (Tree.frame own t)
  | .kid i e, .node _ kids =>
    match kids[i]? with
    | some k => .kid i (Edit.frame own e k)
    | none => .kid i (.replace (.node (.row []) []))
  | .reshape l sources, .node _ kids => .reshape (own l) (sources.filterMap (Source.frame own kids.length))

theorem modify_map {α β : Type} (f : α → β) (g : β → β) (h : α → α) :
    ∀ (xs : List α) (i : Nat), (∀ x, xs[i]? = some x → g (f x) = f (h x)) →
      (xs.map f).modify i g = (xs.modify i h).map f
  | [], _, _ => by simp
  | x :: xs, 0, hx => by simp [List.modify_cons, hx x]
  | x :: xs, i + 1, hx => by
    simp only [List.map_cons, List.modify_succ_cons]
    rw [modify_map f g h xs i fun y hy => hx y (by simpa using hy)]

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

/-- A tree's frames, as an incremental function of the tree. -/
def framed (own : L → Fit.Doc S) : Inc (edits L) (runs (Fit.edits S)) :=
  ⟨frame own, fun t e => [e.frame own t]⟩

theorem framed_ok (own : L → Fit.Doc S) : (framed own).ok := fun t e => Edit.frame_ok own e t

/-! ## A new context -/

mutual
/-- The edits that draw again each node that's stale, its kids kept. A
subtree with nothing stale gives none. -/
def refresh (own : L → Fit.Doc S) (stale : L → Bool) : Tree L → List (Fit.Edit S)
  | .node l kids =>
    let below := refreshKids own stale kids 0
    if stale l then .reshape (own l) ((List.range kids.length).map .kept) :: below else below

def refreshKids (own : L → Fit.Doc S) (stale : L → Bool) : List (Tree L) → Nat → List (Fit.Edit S)
  | [], _ => []
  | k :: ks, i => (refresh own stale k).map (.kid i) ++ refreshKids own stale ks (i + 1)
end

theorem kept_all {α : Type} (d : α) (xs : List α) :
    (List.range xs.length).map (fun j => (xs[j]?).getD d) = xs := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp at h1
    simp [h1]

mutual
/-- Drawing the stale nodes again takes the frames to the ones the new way
of drawing gives, if every node that isn't stale is drawn the same by it. -/
theorem refresh_ok (own own' : L → Fit.Doc S) (stale : L → Bool) (h : ∀ l, stale l = false → own' l = own l) :
    ∀ t : Tree L, run (Fit.edits S) (refresh own' stale t) (frame own t) = frame own' t
  | .node l kids => by
    have below := refreshKids_ok own own' stale h kids [] (own' l)
    simp only [List.length_nil, List.nil_append] at below
    simp only [refresh, frame]
    cases hs : stale l with
    | true =>
      simp only [ite_true]
      show run (Fit.edits S) (refreshKids own' stale kids 0)
        (Fit.Edit.apply (.reshape (own' l) ((List.range kids.length).map .kept)) (.node (own l) (frames own kids))) = _
      have all : ((List.range kids.length).map Fit.Source.kept).map (Fit.Source.frame (frames own kids)) =
          frames own kids := by
        have := kept_all (Fit.Frame.node (.row []) []) (frames own kids)
        rw [frames_eq, List.length_map] at this
        rw [frames_eq, List.map_map]
        exact this
      simp only [Fit.Edit.apply, all]
      exact below
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [← h l hs]
      exact below

theorem refreshKids_ok (own own' : L → Fit.Doc S) (stale : L → Bool) (h : ∀ l, stale l = false → own' l = own l) :
    ∀ (ks : List (Tree L)) (pre : List (Fit.Frame S)) (doc : Fit.Doc S),
      run (Fit.edits S) (refreshKids own' stale ks pre.length) (.node doc (pre ++ frames own ks)) =
        .node doc (pre ++ frames own' ks)
  | [], _, _ => rfl
  | k :: ks, pre, doc => by
    simp only [refreshKids, frames]
    rw [run_append, Fit.run_kid, refresh_ok own own' stale h k]
    have rest := refreshKids_ok own own' stale h ks (pre ++ [frame own' k]) doc
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, List.append_assoc,
      List.cons_append, List.nil_append] at rest
    exact rest
end

/-! ## Under a context -/

variable {cc : EditStructure}

/-- A tree's frames, as an incremental function of a context and the tree.
`stale` says whether an edit of the context could change a node's own doc,
and `calm` whether an edit of the context changes none. An edit of the tree
is the same edit of the frames; an edit of the context that isn't calm
draws the stale nodes again, and walks the rest. -/
def drawn (own : cc.Value → L → Fit.Doc S) (stale : cc.Value → cc.Edit → L → Bool) (calm : cc.Edit → Bool) :
    Inc (prod cc (runs (edits L))) (runs (Fit.edits S)) where
  f a := frame (own a.1) a.2
  df a d :=
    let after := lift.run (framed (own (cc.apply d.1 a.1))) d.2 a.2
    if calm d.1 then after else refresh (own (cc.apply d.1 a.1)) (stale a.1 d.1) a.2 ++ after

/-- Drawing under a context is right, if a calm edit changes no node's
doc, and an edit changes only the docs of nodes it makes stale. -/
theorem drawn_ok (own : cc.Value → L → Fit.Doc S) (stale : cc.Value → cc.Edit → L → Bool) (calm : cc.Edit → Bool)
    (hcalm : ∀ c d l, calm d = true → own (cc.apply d c) l = own c l)
    (hstale : ∀ c d l, stale c d l = false → own (cc.apply d c) l = own c l) :
    (drawn (S := S) own stale calm).ok := by
  intro a d
  have after := lift_ok (framed (S := S) (own (cc.apply d.1 a.1))) (framed_ok _) a.2 d.2
  show run (Fit.edits S) _ (frame (own a.1) a.2) = frame (own (cc.apply d.1 a.1)) (run (edits L) d.2 a.2)
  simp only [drawn]
  cases hc : calm d.1 with
  | true =>
    have same : own (cc.apply d.1 a.1) = own a.1 := funext fun l => hcalm a.1 d.1 l hc
    simp only [ite_true]
    rw [same] at after ⊢
    exact after
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [run_append, refresh_ok (own a.1) (own (cc.apply d.1 a.1)) (stale a.1 d.1) (hstale a.1 d.1) a.2]
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

end Tree

end Deui
