import Progred.Display
import Progred.Writes
import Deui.Tree

/-!
A value as a tree, for the view drawn by derivative: a node for each list,
record, cell, blob and literal, its kids its elements' and fields' nodes in
the order the value holds them. A node's label is all its own doc is drawn
from: where it is, how its place asks it to be drawn, and its value without
what's inside its elements and fields. A node drawn from more than that
(an evaluation, by what its expression gave; a record of a kind a function
may draw) has its whole value too.

A write is an edit of the tree where it lands: `rewrite` goes down the
steps as the write does, and `rewrite_ok` says its edits take the tree to
the tree of the value after.
-/

open Deui

namespace Progred.Derived

open Display (Hint emptied shallow)

structure Label where
  path : Path
  hint : Hint
  /-- The node's value, without what's inside its elements and fields. -/
  value : Value
  /-- Its whole value, if it's drawn from more than that. -/
  deep : Option Value
  /-- Whether it's drawn whole, with no kids: worked out once, as the tree
  is made. -/
  leaf : Bool

/-- Whether a value is drawn whole, with no kids: a literal. It reads no
further than the value's fields. -/
def whole : Value → Bool
  | .record fields =>
    ((Value.record fields).text?.isSome || (Value.record fields).u64?.isSome ||
        (Value.record fields).f64?.isSome) && fields.length == 2 ||
      (Value.record fields).literal? Kinds.bool == some [1] || (Value.record fields).literal? Kinds.bool == some [0]
  | _ => false

/-- The kinds with a form of their own, which no projection draws. -/
def special (k : CellId) : Bool :=
  k == Kinds.notebook || k == Kinds.section_ || k == Kinds.lambda || k == Kinds.call || k == Kinds.valueWrapper

/-- Whether a value is drawn from more than its fields' own: an
evaluation, and a record of a kind a projection may draw. -/
def reads (v : Value) : Bool :=
  match v.kind? with
  | some k => !special k
  | none => false

/-- A node's label, from its value and that value without what's inside. -/
def labelOf (path : Path) (hint : Hint) (sv v : Value) : Label :=
  ⟨path, hint, sv, if reads sv then some v else none, whole sv⟩

def label (path : Path) (hint : Hint) (v : Value) : Label := labelOf path hint (shallow v) v

/-- How a list's elements are drawn, by how the list is. -/
def itemHint : Hint → Hint
  | .params => .param
  | _ => .value false

def isList : Value → Bool
  | .list _ => true
  | _ => false

/-- How a record's field is drawn: by how the record is, its kind, the
field's label, and whether the field holds a list. -/
def fieldHint (hint : Hint) (kind : Option CellId) (l : CellId) (kid : Value) : Hint :=
  match hint with
  | .name _ => .value false
  | .paramType => .value false
  | _ =>
    match kind with
    | none => .value true
    | some k =>
      if k == Kinds.notebook then (if l == Kinds.entries && isList kid then .entries else .value false)
      else if k == Kinds.section_ then
        if l == Kinds.name then .name "section"
        else if l == Kinds.sectionBody && isList kid then .body
        else .value false
      else if k == Kinds.lambda then
        if l == Kinds.name then .name "λ" else if l == Kinds.params then .params else .value false
      else if k == Kinds.evaluation || k == Kinds.call then .value false
      else if l == Kinds.name then .name "name"
      else .value false

mutual
/-- A value's tree, from where it is and how it's drawn there. -/
def tree (path : Path) (hint : Hint) : Value → Tree Label
  | .cell c => .node (label path hint (.cell c)) []
  | .blob b => .node (label path hint (.blob b)) []
  | .list items => .node (label path hint (.list items)) (itemTrees path (itemHint hint) items)
  | .record fields =>
    let lab := label path hint (.record fields)
    .node lab (if lab.leaf then [] else fieldTrees path hint (Value.record fields).kind? fields)

def itemTrees (path : Path) (hint : Hint) : List (Position × Value) → List (Tree Label)
  | [] => []
  | (p, x) :: rest => tree (path ++ [.element p]) hint x :: itemTrees path hint rest

def fieldTrees (path : Path) (hint : Hint) (kind : Option CellId) : List (CellId × Value) → List (Tree Label)
  | [] => []
  | (l, x) :: rest =>
    tree (path ++ [.key l]) (fieldHint hint kind l (emptied x)) x :: fieldTrees path hint kind rest
end

/-! ## Writes, as edits of the tree -/

/-- A write: what's along steps set, or taken away. -/
abbrev Writes : EditStructure := ⟨Value, List Step × Option Value, fun d v => v.written d.1 d.2⟩

/-- Where a field set lands among a record's fields, and whether it takes
the place of one there. -/
def fieldLanding (label : CellId) : List (CellId × Value) → Nat × Bool
  | [] => (0, false)
  | (l, _) :: rest =>
    match compare label l with
    | .lt => (0, false)
    | .eq => (0, true)
    | .gt =>
      let r := fieldLanding label rest
      (r.1 + 1, r.2)

/-- Where an element set lands among a list's, and whether it takes the
place of one there. -/
def itemLanding (p : Position) : List (Position × Value) → Nat × Bool
  | [] => (0, false)
  | (q, _) :: rest =>
    if p == q then (0, true)
    else if Position.lt p q then (0, false)
    else
      let r := itemLanding p rest
      (r.1 + 1, r.2)

/-- A node's kids, if its value is drawn kid by kid: how many, and where a
step set lands among them. -/
def landing : Value → Step → Option (Nat × Nat × Bool)
  | .record fields, .key l =>
    if whole (shallow (.record fields)) then none else some (fields.length, fieldLanding l fields)
  | .list items, .element p => some (items.length, itemLanding p items)
  | _, _ => none

/-- How the value a step in is drawn. -/
def stepHint (hint : Hint) (v : Value) (s : Step) (x : Value) : Hint :=
  match v, s with
  | .record _, .key l => fieldHint hint v.kind? l (emptied x)
  | .list _, _ => itemHint hint
  | _, _ => .value false

/-- The kids from `i` on, `n` of them, kept. -/
def keptFrom (i n : Nat) : List (Tree.Source Label) := (List.range' i n).map .kept

/-- The edits of a node's tree for a step set in its value: `v` before,
`v'` after, `x` what the step leads to now, and `inner` the edits that took
the kid there to `x`'s tree, if it was edited and not put in. A kid edited
is that kid's edits, and the node's label again if it's drawn from its
whole value. A kid put in, over one or between two, is the node's label
and kids again, the others kept. -/
def setEdits (path : Path) (hint : Hint) (v v' : Value) (s : Step) (x : Value)
    (inner : Option (List (Tree.Edit Label))) : List (Tree.Edit Label) :=
  if whole (shallow v') then [.replace (tree path hint v')]
  else
    match landing v s with
    | some (n, i, true) =>
      match inner with
      | some es =>
        es.map (.kid i) ++ (if reads (shallow v') then [.reshape (label path hint v') (keptFrom 0 n)] else [])
      | none =>
        [.reshape (label path hint v')
          (keptFrom 0 i ++ .fresh (tree (path ++ [s]) (stepHint hint v' s x) x) :: keptFrom (i + 1) (n - (i + 1)))]
    | some (n, i, false) =>
      [.reshape (label path hint v')
        (keptFrom 0 i ++ .fresh (tree (path ++ [s]) (stepHint hint v' s x) x) :: keptFrom i (n - i))]
    | none => [.replace (tree path hint v')]

/-- The kids kept, of those a test keeps. -/
def keptWhere {α : Type} (keep : α → Bool) : List α → Nat → List (Tree.Source Label)
  | [], _ => []
  | x :: xs, j => if keep x then .kept j :: keptWhere keep xs (j + 1) else keptWhere keep xs (j + 1)

/-- The edits of a node's tree for a step taken away: the node's label and
kids again, without the kid. -/
def removeEdits (path : Path) (hint : Hint) (v v' : Value) (s : Step) : List (Tree.Edit Label) :=
  if whole (shallow v) || whole (shallow v') then [.replace (tree path hint v')]
  else
    match v, s with
    | .record fields, .key l => [.reshape (label path hint v') (keptWhere (·.1 != l) fields 0)]
    | .list items, .element p => [.reshape (label path hint v') (keptWhere (·.1 != p) items 0)]
    | _, _ => [.replace (tree path hint v')]

/-- A value after a write, with the edits that take its tree there; none
where the write declines. It goes down the steps as the write does. A
record's kind set or taken away is the record's tree again: its fields are
drawn by its kind. -/
def rewrite (path : Path) (hint : Hint) (v : Value) :
    List Step → Option Value → Option (Value × List (Tree.Edit Label))
  | [], some new => some (new, [.replace (tree path hint new)])
  | [], none => none
  | [s], some new =>
    (v.setStep s new).map fun v' =>
      (v', if s == .key Kinds.isa then [.replace (tree path hint v')] else setEdits path hint v v' s new none)
  | [s], none =>
    (v.withoutStep s).map fun v' =>
      (v', if s == .key Kinds.isa then [.replace (tree path hint v')] else removeEdits path hint v v' s)
  | s :: r :: rest, w =>
    match v.step? s with
    | none => none
    | some c =>
      match rewrite (path ++ [s]) (stepHint hint v s c) c (r :: rest) w with
      | none => none
      | some (c', es) => (v.setStep s c').map fun v' => (v', setEdits path hint v v' s c' (some es))

/-- A value's tree, as an incremental function of the value under writes:
it keeps the value. -/
def treed (path : Path) (hint : Hint) : Cached Writes (runs (Tree.edits Label)) where
  Cache := Value
  f v := (tree path hint v, v)
  df v d :=
    match rewrite path hint v d.1 d.2 with
    | some (v', es) => (es, v')
    | none => ([], v)

/-! ### The edits are right -/

theorem fieldTrees_eq (path : Path) (hint : Hint) (kind : Option CellId) (fields : List (CellId × Value)) :
    fieldTrees path hint kind fields =
      fields.map fun f => tree (path ++ [.key f.1]) (fieldHint hint kind f.1 (emptied f.2)) f.2 := by
  induction fields with
  | nil => rfl
  | cons f rest ih =>
    obtain ⟨l, x⟩ := f
    simp [fieldTrees, ih]

theorem itemTrees_eq (path : Path) (hint : Hint) (items : List (Position × Value)) :
    itemTrees path hint items = items.map fun f => tree (path ++ [.element f.1]) hint f.2 := by
  induction items with
  | nil => rfl
  | cons f rest ih =>
    obtain ⟨p, x⟩ := f
    simp [itemTrees, ih]

theorem tree_record (path : Path) (hint : Hint) (fields : List (CellId × Value))
    (h : whole (shallow (.record fields)) = false) :
    tree path hint (.record fields) = .node (label path hint (.record fields))
      (fields.map fun f =>
        tree (path ++ [.key f.1]) (fieldHint hint (Value.record fields).kind? f.1 (emptied f.2)) f.2) := by
  have leaf : (label path hint (.record fields)).leaf = false := h
  rw [tree]
  simp only [leaf, Bool.false_eq_true, ite_false, fieldTrees_eq]

theorem tree_list (path : Path) (hint : Hint) (items : List (Position × Value)) :
    tree path hint (.list items) = .node (label path hint (.list items))
      (items.map fun f => tree (path ++ [.element f.1]) (itemHint hint) f.2) := by
  rw [tree, itemTrees_eq]

theorem split_at {α : Type} (xs : List α) (i : Nat) (a : α) (h : xs[i]? = some a) :
    xs = xs.take i ++ a :: xs.drop (i + 1) ∧ (xs.take i).length = i := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  refine ⟨?_, by simp [Nat.le_of_lt hi]⟩
  rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]

theorem set_inner' {κ : Type} (T : κ × Value → Tree Label) (lab : Label) (pre post : List (κ × Value)) (k : κ)
    (c x : Value) (es : List (Tree.Edit Label)) (h : run (Tree.edits Label) es (T (k, c)) = T (k, x)) :
    run (Tree.edits Label) (es.map (.kid pre.length)) (.node lab ((pre ++ (k, c) :: post).map T)) =
      .node lab ((pre ++ (k, x) :: post).map T) := by
  have := Tree.run_kid lab (pre.map T) (T (k, c)) (post.map T) es
  rw [List.length_map] at this
  simp only [List.map_append, List.map_cons]
  rw [this, h]

/-- Edits of the kid at `i` are edits of what's there. -/
theorem set_inner {κ : Type} (T : κ × Value → Tree Label) (lab : Label) (xs : List (κ × Value)) (i : Nat) (k : κ)
    (c x : Value) (hi : xs[i]? = some (k, c)) (es : List (Tree.Edit Label))
    (h : run (Tree.edits Label) es (T (k, c)) = T (k, x)) :
    run (Tree.edits Label) (es.map (.kid i)) (.node lab (xs.map T)) =
      .node lab ((xs.take i ++ (k, x) :: xs.drop (i + 1)).map T) := by
  obtain ⟨hx, hl⟩ := split_at xs i (k, c) hi
  have := set_inner' T lab (xs.take i) (xs.drop (i + 1)) k c x es h
  rw [hl, ← hx] at this
  exact this

/-- A kid put in at `i`, the kids up to it and from `j` on kept, is the
kids with it between them. -/
theorem set_between {κ : Type} (T : κ × Value → Tree Label) (lab lab' : Label) (xs : List (κ × Value)) (i j : Nat)
    (hi : i ≤ xs.length) (hj : j ≤ xs.length) (t : Tree Label) :
    Tree.Edit.apply (.reshape lab' (keptFrom 0 i ++ .fresh t :: keptFrom j (xs.length - j)))
        (.node lab (xs.map T)) =
      .node lab' ((xs.take i).map T ++ t :: (xs.drop j).map T) := by
  simp only [Tree.Edit.apply, keptFrom, List.filterMap_append, List.filterMap_cons, Tree.Source.tree?]
  rw [Tree.kept_range (xs.map T) i 0 (by simpa using hi),
    Tree.kept_range (xs.map T) (xs.length - j) j (by simp; omega)]
  have all : ((xs.map T).drop j).take (xs.length - j) = (xs.map T).drop j := List.take_of_length_le (by simp)
  simp [all, List.map_take, List.map_drop]

/-- Every kid kept is the kids as they are, under a new label. -/
theorem relabel (lab lab' : Label) (kids : List (Tree Label)) :
    Tree.Edit.apply (.reshape lab' (keptFrom 0 kids.length)) (.node lab kids) = .node lab' kids := by
  simp only [Tree.Edit.apply, keptFrom]
  rw [Tree.kept_range kids kids.length 0 (by simp)]
  simp

theorem keptWhere_ok {κ : Type} (T : κ × Value → Tree Label) (keep : κ × Value → Bool) :
    ∀ (xs : List (κ × Value)) (pre : List (Tree Label)),
      (keptWhere keep xs pre.length).filterMap (Tree.Source.tree? (pre ++ xs.map T)) = (xs.filter keep).map T
  | [], _ => rfl
  | x :: xs, pre => by
    have ih := keptWhere_ok T keep xs (pre ++ [T x])
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, List.append_assoc,
      List.cons_append, List.nil_append] at ih
    simp only [keptWhere, List.map_cons, List.filter_cons]
    cases hk : keep x with
    | true =>
      simp only [ite_true, List.filterMap_cons, Tree.Source.tree?, List.map_cons]
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem?_cons_zero]
      rw [ih]
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact ih

/-- Where a field set lands: the fields with it there, in place of the one
of its label if it takes one's place, which is then the first of that
label. -/
theorem fieldLanding_ok (l : CellId) (x : Value) : ∀ fields : List (CellId × Value),
    (fieldLanding l fields).1 ≤ fields.length ∧
      Value.setField fields l x = fields.take (fieldLanding l fields).1 ++ (l, x) ::
        fields.drop ((fieldLanding l fields).1 + if (fieldLanding l fields).2 then 1 else 0) ∧
      ((fieldLanding l fields).2 = true → ∃ c, fields[(fieldLanding l fields).1]? = some (l, c) ∧
        fields.find? (·.1 == l) = some (l, c))
  | [] => by simp [fieldLanding, Value.setField]
  | (l0, w) :: rest => by
    have ih := fieldLanding_ok l x rest
    have hl : fieldLanding l ((l0, w) :: rest) = (match compare l l0 with
      | .lt => (0, false)
      | .eq => (0, true)
      | .gt => ((fieldLanding l rest).1 + 1, (fieldLanding l rest).2)) := rfl
    have hs : Value.setField ((l0, w) :: rest) l x = (match compare l l0 with
      | .lt => (l, x) :: (l0, w) :: rest
      | .eq => (l, x) :: rest
      | .gt => (l0, w) :: Value.setField rest l x) := rfl
    cases h : compare l l0 with
    | lt =>
      rw [h] at hl hs
      simp [hl, hs]
    | eq =>
      rw [h] at hl hs
      have e : l = l0 := Std.LawfulEqCmp.eq_of_compare h
      subst e
      simp [hl, hs]
    | gt =>
      rw [h] at hl hs
      rw [hl, hs]
      have ne : l0 ≠ l := fun e => by
        have := (Std.LawfulEqCmp.compare_eq_iff_eq (cmp := (compare : CellId → CellId → Ordering))
          (a := l) (b := l0)).mpr e.symm
        rw [this] at h
        cases h
      obtain ⟨h1, h2, h3⟩ := ih
      refine ⟨by simpa using h1, ?_, ?_⟩
      · simp only [List.take_succ_cons, List.cons_append, List.cons.injEq, true_and]
        rw [h2]
        simp
        rw [Nat.add_right_comm, List.drop_succ_cons]
      · intro hr
        obtain ⟨c, hc, hf⟩ := h3 hr
        exact ⟨c, by simpa using hc, by simp [ne, hf]⟩

theorem itemLanding_ok (p : Position) (x : Value) : ∀ items : List (Position × Value),
    (itemLanding p items).1 ≤ items.length ∧
      Value.setElement items p x = items.take (itemLanding p items).1 ++ (p, x) ::
        items.drop ((itemLanding p items).1 + if (itemLanding p items).2 then 1 else 0) ∧
      ((itemLanding p items).2 = true → ∃ c, items[(itemLanding p items).1]? = some (p, c) ∧
        items.find? (·.1 == p) = some (p, c))
  | [] => by simp [itemLanding, Value.setElement]
  | (q, w) :: rest => by
    have ih := itemLanding_ok p x rest
    simp only [itemLanding, Value.setElement]
    by_cases h : (p == q) = true
    · have e : p = q := by simpa using h
      subst e
      simp
    · have h' : (p == q) = false := by simpa using h
      have ne : q ≠ p := fun e => h (by simp [e])
      simp only [h']
      by_cases hlt : Position.lt p q = true
      · simp [hlt]
      · simp only [hlt, Bool.false_eq_true, ite_false]
        obtain ⟨h1, h2, h3⟩ := ih
        refine ⟨by simpa using h1, ?_, ?_⟩
        · simp only [List.take_succ_cons, List.cons_append, List.cons.injEq, true_and]
          rw [h2]
          simp
          rw [Nat.add_right_comm, List.drop_succ_cons]
        · intro hr
          obtain ⟨c, hc, hf⟩ := h3 hr
          exact ⟨c, by simpa using hc, by simp [ne, hf]⟩

theorem map_replace {κ β : Type} (f : κ × Value → β) (xs : List (κ × Value)) (i : Nat) (a b : κ × Value)
    (hi : xs[i]? = some a) (h : f b = f a) : (xs.take i ++ b :: xs.drop (i + 1)).map f = xs.map f := by
  conv => rhs; rw [(split_at xs i a hi).1]
  simp [h]

/-- A step set leaves a value the kind of thing it was. -/
theorem emptied_setStep (v : Value) (s : Step) (x v' : Value) (h : v.setStep s x = some v') :
    emptied v' = emptied v := by
  cases v <;> cases s <;> simp only [Value.setStep, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem emptied_withoutStep (v : Value) (s : Step) (v' : Value) (h : v.withoutStep s = some v') :
    emptied v' = emptied v := by
  cases v <;> cases s <;> simp only [Value.withoutStep, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-- And so does a write a step or more in. -/
theorem emptied_put (v : Value) (s : Step) (rest : List Step) (w : Option Value) (v' : Value)
    (h : v.put (s :: rest) w = some v') : emptied v' = emptied v := by
  cases rest with
  | nil =>
    cases w with
    | some x => exact emptied_setStep v s x v' h
    | none => exact emptied_withoutStep v s v' h
  | cons r rest =>
    obtain ⟨c, c', _, _, hset⟩ := Value.put_deep v s r rest w v' h
    exact emptied_setStep v s c' v' hset

theorem kind_of_step (v v' : Value) (h : v'.step? (.key Kinds.isa) = v.step? (.key Kinds.isa)) :
    v'.kind? = v.kind? := by
  simp only [Value.kind?]
  have : v'.field? Kinds.isa = v.field? Kinds.isa := h
  rw [this]

/-- A step set other than the kind's leaves the kind. -/
theorem kind_setStep (v : Value) (s : Step) (x v' : Value) (h : v.setStep s x = some v')
    (hs : s ≠ .key Kinds.isa) : v'.kind? = v.kind? :=
  kind_of_step v v' (Value.step_setStep_other v s x v' h _ (Ne.symm hs))

theorem kind_withoutStep (v : Value) (s : Step) (v' : Value) (h : v.withoutStep s = some v')
    (hs : s ≠ .key Kinds.isa) : v'.kind? = v.kind? :=
  kind_of_step v v' (Value.step_withoutStep_other v s v' h _ (Ne.symm hs))

/-- A value that isn't a cell set where one that isn't a cell was leaves
the kind: neither is a kind. -/
theorem kind_setStep_deep (v : Value) (s : Step) (c c' v' : Value) (hc : v.step? s = some c)
    (h : v.setStep s c' = some v') (nc : ∀ k, c ≠ .cell k) (nc' : ∀ k, c' ≠ .cell k) : v'.kind? = v.kind? := by
  by_cases hs : s = .key Kinds.isa
  · subst hs
    have h' := Value.step_setStep_same v _ c' v' h
    have e : v.field? Kinds.isa = some c := hc
    have e' : v'.field? Kinds.isa = some c' := h'
    simp only [Value.kind?, e, e']
    cases c <;> cases c' <;> first | rfl | exact absurd rfl (nc _) | exact absurd rfl (nc' _)
  · exact kind_setStep v s c' v' h hs

theorem run_single (e : Tree.Edit Label) (t : Tree Label) :
    run (Tree.edits Label) [e] t = Tree.Edit.apply e t := rfl

theorem run_append_single (es : List (Tree.Edit Label)) (e : Tree.Edit Label) (t : Tree Label) :
    run (Tree.edits Label) (es ++ [e]) t = Tree.Edit.apply e (run (Tree.edits Label) es t) := by
  rw [run_append]
  rfl

/-- The edits for a step set take the tree to the tree of the value after,
if the set leaves the value's kind: `inner`, if there is one, takes the
kid the step led to to the tree of what it leads to now, which is the kind
of thing it was. -/
theorem setEdits_ok (path : Path) (hint : Hint) (v v' : Value) (s : Step) (x : Value)
    (hset : v.setStep s x = some v') (hkind : v'.kind? = v.kind?) (inner : Option (List (Tree.Edit Label)))
    (hinner : ∀ es, inner = some es → ∃ c, v.step? s = some c ∧ emptied x = emptied c ∧
      run (Tree.edits Label) es (tree (path ++ [s]) (stepHint hint v s c) c) =
        tree (path ++ [s]) (stepHint hint v s c) x) :
    run (Tree.edits Label) (setEdits path hint v v' s x inner) (tree path hint v) = tree path hint v' := by
  unfold setEdits
  cases hw : whole (shallow v') with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    cases v <;> cases s <;> simp only [Value.setStep, Option.some.injEq, reduceCtorEq] at hset
    · -- A list, an element set.
      rename_i items p
      subst hset
      obtain ⟨h1, h2, h3⟩ := itemLanding_ok p x items
      simp only [landing]
      rw [tree_list, tree_list]
      generalize itemLanding p items = land at h1 h2 h3
      obtain ⟨i, rep⟩ := land
      cases rep with
      | false =>
        simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at h2 ⊢
        rw [h2]
        have := set_between (fun f => tree (path ++ [.element f.1]) (itemHint hint) f.2)
          (label path hint (.list items)) (label path hint (.list (items.take i ++ (p, x) :: items.drop i)))
          items i i h1 h1 (tree (path ++ [.element p]) (itemHint hint) x)
        show Tree.Edit.apply _ _ = _
        simpa [stepHint] using this
      | true =>
        obtain ⟨c, hc, hf⟩ := h3 rfl
        have hlt : i < items.length := (List.getElem?_eq_some_iff.mp hc).1
        simp only [ite_true] at h2 ⊢
        rw [h2]
        cases inner with
        | none =>
          have := set_between (fun f => tree (path ++ [.element f.1]) (itemHint hint) f.2)
            (label path hint (.list items))
            (label path hint (.list (items.take i ++ (p, x) :: items.drop (i + 1))))
            items i (i + 1) h1 hlt (tree (path ++ [.element p]) (itemHint hint) x)
          show Tree.Edit.apply _ _ = _
          simpa [stepHint] using this
        | some es =>
          obtain ⟨c0, hstep, hemp, hrun⟩ := hinner es rfl
          have same : c0 = c := by
            simp only [Value.step?, hf, Option.map_some, Option.some.injEq] at hstep
            exact hstep.symm
          subst same
          have hlab : label path hint (.list (items.take i ++ (p, x) :: items.drop (i + 1))) =
              label path hint (.list items) := by
            have : shallow (.list (items.take i ++ (p, x) :: items.drop (i + 1))) = shallow (.list items) := by
              simp only [shallow]
              rw [map_replace (fun f : Position × Value => (f.1, emptied f.2)) items i (p, c0) (p, x) hc
                (by simp [hemp])]
            have nr : reads (shallow (Value.list items)) = false := rfl
            simp only [label, labelOf, this, nr, Bool.false_eq_true, ite_false]
          have noreads : reads (shallow (.list (items.take i ++ (p, x) :: items.drop (i + 1)))) = false := rfl
          simp only [noreads, Bool.false_eq_true, ite_false, List.append_nil, hlab]
          exact set_inner (fun f => tree (path ++ [.element f.1]) (itemHint hint) f.2) _ items i p c0 x hc es
            (by simpa [stepHint] using hrun)
    · -- A record, a field set.
      rename_i fields l
      subst hset
      obtain ⟨h1, h2, h3⟩ := fieldLanding_ok l x fields
      simp only [landing]
      cases hwv : whole (shallow (.record fields)) with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        rw [tree_record _ _ _ hwv, tree_record _ _ _ hw, hkind]
        generalize hT : (fun f : CellId × Value =>
          tree (path ++ [.key f.1]) (fieldHint hint (Value.record fields).kind? f.1 (emptied f.2)) f.2) = T
        have hfresh : tree (path ++ [.key l]) (stepHint hint (.record (Value.setField fields l x)) (.key l) x) x =
            T (l, x) := by
          rw [← hT]
          simp only [stepHint, hkind]
        rw [hfresh]
        generalize fieldLanding l fields = land at h1 h2 h3
        obtain ⟨i, rep⟩ := land
        cases rep with
        | false =>
          simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at h2 ⊢
          have := set_between T (label path hint (.record fields))
            (label path hint (.record (Value.setField fields l x))) fields i i h1 h1 (T (l, x))
          rw [h2] at this ⊢
          show Tree.Edit.apply _ _ = _
          simpa using this
        | true =>
          obtain ⟨c, hc, hf⟩ := h3 rfl
          have hlt : i < fields.length := (List.getElem?_eq_some_iff.mp hc).1
          simp only [ite_true] at h2 ⊢
          cases inner with
          | none =>
            have := set_between T (label path hint (.record fields))
              (label path hint (.record (Value.setField fields l x))) fields i (i + 1) h1 hlt (T (l, x))
            rw [h2] at this ⊢
            show Tree.Edit.apply _ _ = _
            simpa using this
          | some es =>
            obtain ⟨c0, hstep, hemp, hrun⟩ := hinner es rfl
            have same : c0 = c := by
              simp only [Value.step?, Value.field?, hf, Option.map_some, Option.some.injEq] at hstep
              exact hstep.symm
            subst same
            have hsh : shallow (.record (Value.setField fields l x)) = shallow (.record fields) := by
              simp only [shallow]
              rw [h2, map_replace (fun f : CellId × Value => (f.1, emptied f.2)) fields i (l, c0) (l, x) hc
                (by simp [hemp])]
            have hrun' : run (Tree.edits Label) es (T (l, c0)) = T (l, x) := by
              rw [← hT]
              simp only [stepHint] at hrun
              simp only [hemp]
              exact hrun
            have inner_ := set_inner T (label path hint (.record fields)) fields i l c0 x hc es hrun'
            have len : ((fields.take i ++ (l, x) :: fields.drop (i + 1)).map T).length = fields.length := by
              simp
              omega
            cases hr : reads (shallow (.record (Value.setField fields l x))) with
            | true =>
              simp only [ite_true]
              rw [run_append_single, inner_, h2, ← len]
              exact relabel _ _ _
            | false =>
              have hlab : label path hint (.record (Value.setField fields l x)) =
                  label path hint (.record fields) := by
                simp only [label, labelOf, hsh] at hr ⊢
                simp [hr]
              simp only [Bool.false_eq_true, ite_false, List.append_nil, hlab]
              rw [inner_, h2]

/-- The edits for a step taken away take the tree to the tree of the value
after, if taking it away leaves the value's kind. -/
theorem removeEdits_ok (path : Path) (hint : Hint) (v v' : Value) (s : Step) (hw : v.withoutStep s = some v')
    (hkind : v'.kind? = v.kind?) :
    run (Tree.edits Label) (removeEdits path hint v v' s) (tree path hint v) = tree path hint v' := by
  unfold removeEdits
  cases hwh : (whole (shallow v) || whole (shallow v')) with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    obtain ⟨hv, hv'⟩ : whole (shallow v) = false ∧ whole (shallow v') = false := by simpa using hwh
    cases v <;> cases s <;> simp only [Value.withoutStep, Option.some.injEq, reduceCtorEq] at hw
    · rename_i items p
      subst hw
      show Tree.Edit.apply _ _ = _
      rw [tree_list, tree_list]
      simp only [Tree.Edit.apply]
      have := keptWhere_ok (fun f => tree (path ++ [.element f.1]) (itemHint hint) f.2)
        (fun f : Position × Value => f.1 != p) items []
      simp only [List.length_nil, List.nil_append] at this
      rw [this]
    · rename_i fields l
      subst hw
      show Tree.Edit.apply _ _ = _
      rw [tree_record _ _ _ hv, tree_record _ _ _ hv', hkind]
      simp only [Tree.Edit.apply]
      have := keptWhere_ok
        (fun f => tree (path ++ [.key f.1]) (fieldHint hint (Value.record fields).kind? f.1 (emptied f.2)) f.2)
        (fun f : CellId × Value => f.1 != l) fields []
      simp only [List.length_nil, List.nil_append] at this
      rw [this]

/-- A write more than a step in, as the write a step in, set back. -/
theorem put_deep_eq (v : Value) (s r : Step) (rest : List Step) (w : Option Value) :
    v.put (s :: r :: rest) w =
      (v.step? s).bind fun c => (c.put (r :: rest) w).bind fun c' => v.setStep s c' := by
  cases w <;> simp only [Value.put, Value.set, Value.without, bind, Option.bind] <;>
    cases v.step? s <;> rfl

/-- Rewriting is right: it gives the value the write does, with edits that
take the tree to that value's; and it declines where the write does. -/
theorem rewrite_ok : ∀ (rel : List Step) (path : Path) (hint : Hint) (v : Value) (w : Option Value),
    match rewrite path hint v rel w with
    | some (v', es) => v.put rel w = some v' ∧ run (Tree.edits Label) es (tree path hint v) = tree path hint v'
    | none => v.put rel w = none
  | [], _, _, _, some _ => ⟨rfl, rfl⟩
  | [], _, _, _, none => rfl
  | [s], path, hint, v, some new => by
    simp only [rewrite]
    rcases h : v.setStep s new with _ | v'
    · exact h
    · simp only [Option.map_some]
      refine ⟨h, ?_⟩
      by_cases hs : s = .key Kinds.isa
      · simp only [hs, beq_self_eq_true, ite_true]
        rfl
      · have hb : (s == Step.key Kinds.isa) = false := by simpa using hs
        simp only [hb, Bool.false_eq_true, ite_false]
        exact setEdits_ok path hint v v' s new h (kind_setStep v s new v' h hs) none (fun _ e => by cases e)
  | [s], path, hint, v, none => by
    simp only [rewrite]
    rcases h : v.withoutStep s with _ | v'
    · exact h
    · simp only [Option.map_some]
      refine ⟨h, ?_⟩
      by_cases hs : s = .key Kinds.isa
      · simp only [hs, beq_self_eq_true, ite_true]
        rfl
      · have hb : (s == Step.key Kinds.isa) = false := by simpa using hs
        simp only [hb, Bool.false_eq_true, ite_false]
        exact removeEdits_ok path hint v v' s h (kind_withoutStep v s v' h hs)
  | s :: r :: rest, path, hint, v, w => by
    simp only [rewrite]
    rw [put_deep_eq]
    cases hs : v.step? s with
    | none => rfl
    | some c =>
      have ih := rewrite_ok (r :: rest) (path ++ [s]) (stepHint hint v s c) c w
      rcases hr : rewrite (path ++ [s]) (stepHint hint v s c) c (r :: rest) w with _ | ⟨c', es⟩
      · simp only [hr] at ih ⊢
        simp [ih]
      · simp only [hr] at ih ⊢
        obtain ⟨hput, hrun⟩ := ih
        simp only [Option.bind_some, hput]
        rcases h : v.setStep s c' with _ | v'
        · simp only [Option.map_none]
        · simp only [Option.map_some]
          obtain ⟨_, nc, nc'⟩ := Value.put_other c r rest w c' hput
          exact ⟨trivial, setEdits_ok path hint v v' s c' h (kind_setStep_deep v s c c' v' hs h nc nc') (some es)
            fun es' e => by
              cases e
              exact ⟨c, hs, emptied_put c r rest w c' hput, hrun⟩⟩

theorem treed_ok (path : Path) (hint : Hint) : (treed path hint).ok := by
  intro v d
  have h := rewrite_ok d.1 path hint v d.2
  show (run (Tree.edits Label) _ (tree path hint v), _) = (tree path hint (v.written d.1 d.2), v.written d.1 d.2)
  simp only [treed, Value.written]
  cases hr : rewrite path hint v d.1 d.2 with
  | none =>
    rw [hr] at h
    simp only [h, Option.getD_none]
    rfl
  | some made =>
    obtain ⟨v', es⟩ := made
    rw [hr] at h
    simp only [h.1, Option.getD_some, h.2]

end Progred.Derived
