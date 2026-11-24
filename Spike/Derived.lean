import Progred.Editor
import Deui.Tree

/-!
A spike: lists, records and names drawn as composed derivatives, measured
against the view as it is.

A value is a tree, a node for each list, record, cell and literal, labelled
with what the node itself shows: a list's positions, a record's labels.
Each node's doc is drawn from its label and the names its keys look up:
a record's labels, a cell's own id. So a write of a definition draws again
the nodes with that key and no others (`Deui/Tree.lean`), and a write in the
value is an edit of the tree at the same place. Nothing is recorded while
drawing, and no part is grown again to find out what changed.

Left out: the selection, holes, folds, kinds and their projections, cells
drawn open, results.
-/

open Deui

namespace Progred.Derived

/-! ## The tree -/

/-- What a node itself shows. -/
inductive Shape where
  | cell (c : CellId)
  | blob (bytes : List UInt8)
  /-- A literal drawn as a line: text, or a number. -/
  | line (v : Value)
  | truth (b : Bool)
  | list (positions : List Position)
  | record (labels : List CellId)

structure Label where
  path : Path
  shape : Shape

/-- How a record that's drawn whole is drawn; none for one drawn field by
field. -/
def literal? (v : Value) (count : Nat) : Option Shape :=
  if (v.text?.isSome || v.u64?.isSome || v.f64?.isSome) && count == 2 then some (.line v)
  else if v.literal? Kinds.bool == some [1] then some (.truth true)
  else if v.literal? Kinds.bool == some [0] then some (.truth false)
  else none

mutual
/-- A value's tree, from the path it's at. -/
def tree (path : Path) : Value → Tree Label
  | .cell c => .node ⟨path, .cell c⟩ []
  | .blob b => .node ⟨path, .blob b⟩ []
  | .list items => .node ⟨path, .list (items.map (·.1))⟩ (itemTrees path items)
  | .record fields =>
    match literal? (.record fields) fields.length with
    | some s => .node ⟨path, s⟩ []
    | none => .node ⟨path, .record (fields.map (·.1))⟩ (fieldTrees path fields)

def itemTrees (path : Path) : List (Position × Value) → List (Tree Label)
  | [] => []
  | (p, x) :: rest => tree (path ++ [.element p]) x :: itemTrees path rest

def fieldTrees (path : Path) : List (CellId × Value) → List (Tree Label)
  | [] => []
  | (l, x) :: rest => tree (path ++ [.key l]) x :: fieldTrees path rest
end

/-! ## A node's own doc -/

def occ (path : Path) (kind : OccKind) (d : Doc) (cell : Option CellId := none) : Doc :=
  Doc.marked ⟨path, kind, false, cell⟩ d

def insertion (path : Path) (before after : Option Position) : Doc :=
  occ (path ++ [.element (Position.between before after)]) .insertion (point .ink)

/-- A list's elements, each in its slot, with a place to insert before each
and after the last. -/
def elements (path : Path) : Option Position → List Position → Nat → List Doc
  | _, [], _ => []
  | prev, p :: rest, i =>
    .row [insertion path prev (some p), .slot i, if rest.isEmpty then insertion path (some p) none else .row []] ::
      elements path (some p) rest (i + 1)

def list (path : Path) (positions : List Position) : Doc :=
  let parts := if positions.isEmpty then [insertion path none none] else elements path none positions 0
  Display.container "[" "]" parts parts

/-- A field: its label by name, then its value's slot. -/
def field (path : Path) (l : CellId) (name : Option String) (slot : Nat) : Doc :=
  .row [occ (path ++ [.key l]) .label (t (name.getD l.short) .label) (some l), dim ": ", .slot slot]

/-- A record's fields in the order they show: named labels by name, then
the rest. -/
def ordered (fields : List (CellId × Option String × Nat)) : List (CellId × Option String × Nat) :=
  let named := fields.filter (·.2.1.isSome)
  let unnamed := fields.filter (·.2.1.isNone)
  (named.toArray.qsort (fun a b => a.2.1.getD "" < b.2.1.getD "")).toList ++ unnamed

/-- The labels with their names, each with the slot its value is in. -/
def slotted : List CellId → List (Option String) → Nat → List (CellId × Option String × Nat)
  | l :: ls, n :: ns, i => (l, n, i) :: slotted ls ns (i + 1)
  | _, _, _ => []

def record (path : Path) (labels : List CellId) (names : List (Option String)) : Doc :=
  let parts := (ordered (slotted labels names 0)).map fun (l, n, i) => field path l n i
  let end_ := [occ path .fieldEnd (point .ink)]
  let flat : Doc := .row ([delim "{"] ++ Doc.sep (dim ", ") parts ++ end_ ++ [delim "}"])
  let lines : List Doc := match parts.reverse with
    | last :: before => before.reverse ++ [.row (last :: end_)]
    | [] => end_
  .alt flat (.col [delim "{", .indent 2 (.col lines), delim "}"])

/-- The cells whose names a node shows. -/
def keys (l : Label) : List CellId :=
  match l.shape with
  | .cell c => [c]
  | .record labels => labels
  | _ => []

/-- A node's own doc, from its label and its keys' names. -/
def draw (l : Label) (names : List (Option String)) : Doc :=
  match l.shape with
  | .cell c =>
    occ l.path .value (match names with
      | some n :: _ => t n .name
      | _ => dim c.short) (some c)
  | .blob b => occ l.path .value (t (GidText.hex b) .number)
  | .line v => occ l.path .value (Display.line v none)
  | .truth b => occ l.path .value (t (if b then "true" else "false") .name)
  | .list positions => occ l.path .value (list l.path positions)
  | .record labels => occ l.path .value (record l.path labels names)

/-! ## Names, looked up -/

/-- What a node is drawn under: the ribbon, and the definitions. -/
abbrev Under : EditStructure := prod (latest Nat) (runs Editor.cellsEdits)

def named (cells : Editor.Cells) (c : CellId) : Option String :=
  match (((cells[c]?).orElse fun _ => (Builtin.library.find? (·.1 == c)).map (·.2)).bind
      (·.field? Kinds.name)).bind Value.text? with
  | some "" => none
  | n => n

def get (u : Under.Value) (c : CellId) : Option String := named u.2 c

/-- Whether an edit of the definitions writes a cell. -/
def writes (c : CellId) : Model.CellsEdit → Bool
  | .set x _ => x == c
  | .all _ => true

def touches (d : Under.Edit) (c : CellId) : Bool := d.2.any (writes c)

def calm (d : Under.Edit) : Bool := d.2.isEmpty

/-- A cell no edit of a run writes has the name it had. -/
theorem get_untouched (u : Under.Value) (d : Under.Edit) (c : CellId) (h : touches d c = false) :
    get (Under.apply d u) c = get u c := by
  obtain ⟨r, cells⟩ := u
  obtain ⟨r', ces⟩ := d
  show named (run Editor.cellsEdits ces cells) c = named cells c
  simp only [touches] at h
  induction ces generalizing cells with
  | nil => rfl
  | cons ce rest ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    show named (run Editor.cellsEdits rest (Model.CellsEdit.apply ce cells)) c = _
    rw [ih _ h.2]
    cases ce with
    | all new => simp [writes] at h
    | set x v =>
      have ne : c ≠ x := fun e => by simp [writes, e] at h
      simp only [named, Model.CellsEdit.apply, Model.defined_other cells x v c ne]

/-- A node's own doc, under the definitions. -/
def own : Under.Value → Label → Doc := Tree.reading get keys draw

def stale : Under.Value → Under.Edit → Label → Bool := Tree.touched touches keys

/-- A value's frames, as an incremental function of the definitions and
the value's tree. -/
def drawn : Inc (prod Under (runs (Tree.edits Label))) (runs (Fit.edits Span)) := Tree.drawn own stale calm

theorem drawn_ok : drawn.ok := by
  apply Tree.drawn_ok
  · intro c d l hc
    obtain ⟨r, cells⟩ := c
    obtain ⟨r', ces⟩ := d
    cases ces with
    | nil => rfl
    | cons _ _ => simp [calm] at hc
  · exact Tree.reading_touched get keys draw touches get_untouched

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
    match literal? (.record fields) fields.length with
    | some _ => none
    | none => some (fields.length, fieldLanding l fields)
  | .list items, .element p => some (items.length, itemLanding p items)
  | _, _ => none

/-- Whether a value's node has no kids of its own: a literal. -/
def whole (v : Value) : Bool :=
  match v with
  | .record fields => (literal? v fields.length).isSome
  | .list _ => false
  | _ => true

/-- A node's label. -/
def label (path : Path) (v : Value) : Label :=
  match v with
  | .cell c => ⟨path, .cell c⟩
  | .blob b => ⟨path, .blob b⟩
  | .list items => ⟨path, .list (items.map (·.1))⟩
  | .record fields => ⟨path, (literal? v fields.length).getD (.record (fields.map (·.1)))⟩

/-- The kids from `i` on, `n` of them, kept. -/
def keptFrom (i n : Nat) : List (Tree.Source Label) := (List.range' i n).map .kept

/-- The edits of a node's tree for a step set in its value: `v` before,
`v'` after, `x` what the step leads to now, and `inner` the edits that took
the kid there to `x`'s tree, if it was edited and not put in. A kid edited
or replaced is that kid's edit; one put in is the node's label and kids
again, the others kept. -/
def setEdits (path : Path) (v v' : Value) (s : Step) (x : Value) (inner : Option (List (Tree.Edit Label))) :
    List (Tree.Edit Label) :=
  if whole v' then [.replace (tree path v')]
  else
    match landing v s with
    | some (_, i, true) =>
      match inner with
      | some es => es.map (.kid i)
      | none => [.kid i (.replace (tree (path ++ [s]) x))]
    | some (n, i, false) =>
      [.reshape (label path v') (keptFrom 0 i ++ .fresh (tree (path ++ [s]) x) :: keptFrom i (n - i))]
    | none => [.replace (tree path v')]

/-- The kids kept, of those a test keeps. -/
def keptWhere {α : Type} (keep : α → Bool) : List α → Nat → List (Tree.Source Label)
  | [], _ => []
  | x :: xs, j => if keep x then .kept j :: keptWhere keep xs (j + 1) else keptWhere keep xs (j + 1)

/-- The edits of a node's tree for a step taken away: the node's label and
kids again, without the kid. -/
def removeEdits (path : Path) (v v' : Value) (s : Step) : List (Tree.Edit Label) :=
  if whole v || whole v' then [.replace (tree path v')]
  else
    match v, s with
    | .record fields, .key l => [.reshape (label path v') (keptWhere (·.1 != l) fields 0)]
    | .list items, .element p => [.reshape (label path v') (keptWhere (·.1 != p) items 0)]
    | _, _ => [.replace (tree path v')]

/-- A value after a write, with the edits that take its tree there; none
where the write declines. It goes down the steps as the write does. -/
def rewrite (path : Path) (v : Value) : List Step → Option Value → Option (Value × List (Tree.Edit Label))
  | [], some new => some (new, [.replace (tree path new)])
  | [], none => none
  | [s], some new => (v.setStep s new).map fun v' => (v', setEdits path v v' s new none)
  | [s], none => (v.withoutStep s).map fun v' => (v', removeEdits path v v' s)
  | s :: r :: rest, w =>
    match v.step? s with
    | none => none
    | some c =>
      match rewrite (path ++ [s]) c (r :: rest) w with
      | none => none
      | some (c', es) => (v.setStep s c').map fun v' => (v', setEdits path v v' s c' (some es))

/-- A value's tree, as an incremental function of the value under writes:
it keeps the value. -/
def treed : Cached Writes (runs (Tree.edits Label)) where
  Cache := Value
  f v := (tree [] v, v)
  df v d :=
    match rewrite [] v d.1 d.2 with
    | some (v', es) => (es, v')
    | none => ([], v)

/-! ### The edits are right -/

theorem fieldTrees_eq (path : Path) (fields : List (CellId × Value)) :
    fieldTrees path fields = fields.map fun f => tree (path ++ [.key f.1]) f.2 := by
  induction fields with
  | nil => rfl
  | cons f rest ih =>
    obtain ⟨l, x⟩ := f
    simp [fieldTrees, ih]

theorem itemTrees_eq (path : Path) (items : List (Position × Value)) :
    itemTrees path items = items.map fun f => tree (path ++ [.element f.1]) f.2 := by
  induction items with
  | nil => rfl
  | cons f rest ih =>
    obtain ⟨p, x⟩ := f
    simp [itemTrees, ih]

theorem tree_record (path : Path) (fields : List (CellId × Value))
    (h : literal? (.record fields) fields.length = none) :
    tree path (.record fields) =
      .node ⟨path, .record (fields.map (·.1))⟩ (fields.map fun f => tree (path ++ [.key f.1]) f.2) := by
  rw [tree, h, fieldTrees_eq]

theorem tree_list (path : Path) (items : List (Position × Value)) :
    tree path (.list items) =
      .node ⟨path, .list (items.map (·.1))⟩ (items.map fun f => tree (path ++ [.element f.1]) f.2) := by
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

/-- A kid put in at `i`, the others kept, is the kids with it there. -/
theorem set_insert {κ : Type} (T : κ × Value → Tree Label) (lab lab' : Label) (xs : List (κ × Value)) (i : Nat)
    (hi : i ≤ xs.length) (a : κ × Value) :
    Tree.Edit.apply (.reshape lab' (keptFrom 0 i ++ .fresh (T a) :: keptFrom i (xs.length - i)))
        (.node lab (xs.map T)) =
      .node lab' ((xs.take i ++ a :: xs.drop i).map T) := by
  simp only [Tree.Edit.apply, keptFrom, List.filterMap_append, List.filterMap_cons, Tree.Source.tree?]
  rw [Tree.kept_range (xs.map T) i 0 (by simpa using hi),
    Tree.kept_range (xs.map T) (xs.length - i) i (by simp; omega)]
  have all : ((xs.map T).drop i).take (xs.length - i) = (xs.map T).drop i := List.take_of_length_le (by simp)
  simp [all, List.map_take, List.map_drop]

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

theorem map_fst_replace {κ : Type} (xs : List (κ × Value)) (i : Nat) (k : κ) (c x : Value)
    (hi : xs[i]? = some (k, c)) : (xs.take i ++ (k, x) :: xs.drop (i + 1)).map (·.1) = xs.map (·.1) := by
  conv => rhs; rw [(split_at xs i (k, c) hi).1]
  simp

theorem run_replace (t t0 : Tree Label) : run (Tree.edits Label) [.replace t] t0 = t := rfl

/-- The edits for a step set take the tree to the tree of the value after:
`inner`, if there is one, takes the kid the step led to to the tree of what
it leads to now. -/
theorem setEdits_ok (path : Path) (v v' : Value) (s : Step) (x : Value) (hset : v.setStep s x = some v')
    (inner : Option (List (Tree.Edit Label)))
    (hinner : ∀ es, inner = some es → ∃ c, v.step? s = some c ∧
      run (Tree.edits Label) es (tree (path ++ [s]) c) = tree (path ++ [s]) x) :
    run (Tree.edits Label) (setEdits path v v' s x inner) (tree path v) = tree path v' := by
  unfold setEdits
  cases hw : whole v' with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    cases v <;> cases s <;> simp only [Value.setStep, Option.some.injEq, reduceCtorEq] at hset
    · -- A list, an element set.
      rename_i items p
      subst hset
      obtain ⟨h1, h2, h3⟩ := itemLanding_ok p x items
      simp only [landing]
      rw [tree_list, tree_list, h2]
      generalize itemLanding p items = land at h1 h2 h3
      obtain ⟨i, rep⟩ := land
      cases rep with
      | false =>
        simp only [label, Bool.false_eq_true, ite_false, Nat.add_zero] at h2 ⊢
        exact set_insert (fun f => tree (path ++ [.element f.1]) f.2) ⟨path, .list (items.map (·.1))⟩ _ items i h1
          (p, x)
      | true =>
        obtain ⟨c, hc, hf⟩ := h3 rfl
        simp only [ite_true]
        rw [map_fst_replace items i p c x hc]
        cases inner with
        | none =>
          exact set_inner (fun f => tree (path ++ [.element f.1]) f.2) _ items i p c x hc [.replace _] rfl
        | some es =>
          obtain ⟨c0, hstep, hrun⟩ := hinner es rfl
          have same : c0 = c := by
            simp only [Value.step?, hf, Option.map_some, Option.some.injEq] at hstep
            exact hstep.symm
          subst same
          exact set_inner (fun f => tree (path ++ [.element f.1]) f.2) _ items i p c0 x hc es hrun
    · -- A record, a field set.
      rename_i fields l
      subst hset
      have hlit' : literal? (.record (Value.setField fields l x)) (Value.setField fields l x).length = none := by
        simpa [whole] using hw
      obtain ⟨h1, h2, h3⟩ := fieldLanding_ok l x fields
      simp only [landing]
      cases hlit : literal? (.record fields) fields.length with
      | some sh => rfl
      | none =>
        simp only
        rw [tree_record _ _ hlit, tree_record _ _ hlit']
        have hlabel : label path (.record (Value.setField fields l x)) =
            ⟨path, .record ((Value.setField fields l x).map (·.1))⟩ := by
          simp only [label, hlit', Option.getD_none]
        rw [hlabel, h2]
        generalize fieldLanding l fields = land at h1 h2 h3
        obtain ⟨i, rep⟩ := land
        cases rep with
        | false =>
          simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
          exact set_insert (fun f => tree (path ++ [.key f.1]) f.2) ⟨path, .record (fields.map (·.1))⟩ _ fields i h1
            (l, x)
        | true =>
          obtain ⟨c, hc, hf⟩ := h3 rfl
          simp only [ite_true]
          rw [map_fst_replace fields i l c x hc]
          cases inner with
          | none =>
            exact set_inner (fun f => tree (path ++ [.key f.1]) f.2) _ fields i l c x hc [.replace _] rfl
          | some es =>
            obtain ⟨c0, hstep, hrun⟩ := hinner es rfl
            have same : c0 = c := by
              simp only [Value.step?, Value.field?, hf, Option.map_some, Option.some.injEq] at hstep
              exact hstep.symm
            subst same
            exact set_inner (fun f => tree (path ++ [.key f.1]) f.2) _ fields i l c0 x hc es hrun

/-- The edits for a step taken away take the tree to the tree of the value
after. -/
theorem removeEdits_ok (path : Path) (v v' : Value) (s : Step) (hw : v.withoutStep s = some v') :
    run (Tree.edits Label) (removeEdits path v v' s) (tree path v) = tree path v' := by
  unfold removeEdits
  cases hwh : (whole v || whole v') with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    obtain ⟨hv, hv'⟩ : whole v = false ∧ whole v' = false := by simpa using hwh
    cases v <;> cases s <;> simp only [Value.withoutStep, Option.some.injEq, reduceCtorEq] at hw
    · rename_i items p
      subst hw
      show Tree.Edit.apply _ _ = _
      rw [tree_list, tree_list]
      simp only [Tree.Edit.apply, label]
      have := keptWhere_ok (fun f => tree (path ++ [.element f.1]) f.2) (fun f : Position × Value => f.1 != p)
        items []
      simp only [List.length_nil, List.nil_append] at this
      rw [this]
    · rename_i fields l
      subst hw
      have hlit : literal? (.record fields) fields.length = none := by simpa [whole] using hv
      have hlit' : literal? (.record (fields.filter (·.1 != l))) (fields.filter (·.1 != l)).length = none := by
        simpa [whole] using hv'
      show Tree.Edit.apply _ _ = _
      rw [tree_record _ _ hlit, tree_record _ _ hlit']
      simp only [Tree.Edit.apply, label, hlit', Option.getD_none]
      have := keptWhere_ok (fun f => tree (path ++ [.key f.1]) f.2) (fun f : CellId × Value => f.1 != l)
        fields []
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
theorem rewrite_ok : ∀ (rel : List Step) (path : Path) (v : Value) (w : Option Value),
    match rewrite path v rel w with
    | some (v', es) => v.put rel w = some v' ∧ run (Tree.edits Label) es (tree path v) = tree path v'
    | none => v.put rel w = none
  | [], _, _, some _ => ⟨rfl, rfl⟩
  | [], _, _, none => rfl
  | [s], path, v, some new => by
    simp only [rewrite]
    cases h : v.setStep s new with
    | none => exact h
    | some v' => exact ⟨h, setEdits_ok path v v' s new h none (fun _ e => by cases e)⟩
  | [s], path, v, none => by
    simp only [rewrite]
    cases h : v.withoutStep s with
    | none => exact h
    | some v' => exact ⟨h, removeEdits_ok path v v' s h⟩
  | s :: r :: rest, path, v, w => by
    simp only [rewrite]
    rw [put_deep_eq]
    cases hs : v.step? s with
    | none => rfl
    | some c =>
      have ih := rewrite_ok (r :: rest) (path ++ [s]) c w
      rcases hr : rewrite (path ++ [s]) c (r :: rest) w with _ | ⟨c', es⟩
      · simp only [hr] at ih ⊢
        simp [ih]
      · simp only [hr] at ih ⊢
        obtain ⟨hput, hrun⟩ := ih
        simp only [Option.bind_some, hput]
        rcases h : v.setStep s c' with _ | v'
        · simp only [Option.map_none]
        · simp only [Option.map_some]
          exact ⟨trivial, setEdits_ok path v v' s c' h (some es) fun es' e => by
            cases e
            exact ⟨c, hs, hrun⟩⟩

theorem treed_ok : treed.ok := by
  intro v d
  have h := rewrite_ok d.1 [] v d.2
  show (run (Tree.edits Label) _ (tree [] v), _) = (tree [] (v.written d.1 d.2), v.written d.1 d.2)
  simp only [treed, Value.written]
  cases hr : rewrite [] v d.1 d.2 with
  | none =>
    rw [hr] at h
    simp only [h, Option.getD_none]
    rfl
  | some made =>
    obtain ⟨v', es⟩ := made
    rw [hr] at h
    simp only [h.1, Option.getD_some, h.2]

/-! ## The pipeline -/

/-- A value's frames within the ribbon. -/
def framed : Cached (prod Under (runs Writes)) Editor.Framed :=
  Cached.carrying (·.1) (compose (Cached.second (Cached.lift treed)) (cached drawn))

theorem framed_ok : framed.ok :=
  Cached.carrying_ok _ _ (compose_ok _ _ (Cached.second_ok _ (Cached.lift_ok _ treed_ok)) (cached_ok _ drawn_ok))

/-- A value's lines. -/
def lines : Cached (prod Under (runs Writes)) Editor.PartLines :=
  compose framed (compose (Fit.fit measure) (cached (lift Text.rows)))

/-- The lines' derivative is right: its edits take the lines to those of
the value after its writes, under the definitions after theirs. -/
theorem lines_ok : lines.ok :=
  compose_ok _ _ framed_ok (compose_ok _ _ (Fit.fit_ok measure) (cached_ok _ (lift_ok _ Text.rows_ok)))

/-- info: 'Progred.Derived.lines_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lines_ok

end Progred.Derived

/-! ## Measured against the view as it is -/

open Progred

/-- Ten cells that entries refer to, each with a name and no more. -/
def shared : List CellId :=
  ["0a11b6dc2ad3a4f3b1c9d0a53c7f2e01", "1b22c7ed3be4b5a4c2dae1b64d8a3f12", "2c33d8fe4cf5c6b5d3ebf2c75e9b4a23",
   "3d44e9af5da6d7c6e4fca3d86fac5b34", "4e55fab06eb7e8d7f5adb4e97abd6c45", "5f66abc17fc8f9e8a6bec5fa8bce7d56",
   "6a77bcd28ad9aaf9b7cfd6ab9cdf8e67", "7b88cde39beabbaac8dae7bcadea9f78", "8c99def4acfbccbbd9ebf8cdbefbaa89",
   "9daaefa5bdacddcceafca9decfacbb9a"].map cell!

/-- A label the document defines, which every entry has a field of. -/
def tag : CellId := cell! "c0ffee5bdacddcceafca9decfacbb9a0"

/-- A cell nothing shows. -/
def unseen : CellId := cell! "deadbee5dacddcceafca9decfacbb9a1"

def nameOnly (n : String) : Value := .record [(Kinds.name, Value.text n)]

def rec (fields : List (CellId × Value)) : Value :=
  .record (fields.foldl (fun acc (l, v) => Value.setField acc l v) [])

def entry (i : Nat) : Value :=
  rec [(Kinds.name, Value.text s!"entry {i}"),
    (Kinds.fields, .list ((Position.spread 12).zip ((List.range 12).map fun j => Value.u64 (i * j)))),
    (Kinds.function, .cell (shared[i % 10]!)), (tag, Value.u64 i),
    (Kinds.body, rec [(Kinds.name, Value.text "some words that make the line long enough to wrap around"),
      (Kinds.value, Value.u64 i), (Kinds.params, Value.text "and a second field of text, to be sure it does")])]

def positions (n : Nat) : List Position := Position.spread n

def root (n : Nat) : Value := .list ((positions n).zip ((List.range n).map entry))

def cells0 : Editor.Cells :=
  ((List.range 10).foldl (fun (cells : Editor.Cells) k => cells.insert shared[k]! (nameOnly s!"shared {k}")) {}).insert
    tag (nameOnly "tag")

/-- One step of a measurement: definitions written, and writes in the
value. -/
structure Step' where
  ces : List Model.CellsEdit := []
  writes : List (List Step × Option Value) := []

abbrev OldCache := Editor.part.Cache
abbrev NewCache := Derived.lines.Cache

structure State where
  cells : Editor.Cells
  value : Value
  old : OldCache
  new : NewCache
  oldLines : List Line
  newLines : List Line

def seen : Display.Seen := {}

def oldF (cells : Editor.Cells) (value : Value) : List Line × OldCache :=
  Editor.part.f ((seen, cells), .whole (some value))

def newF (cells : Editor.Cells) (value : Value) : List Line × NewCache :=
  Derived.lines.f (((80 : Nat), cells), value)

def oldDf (k : OldCache) (step : Step') : Editor.PartLines.Edit × OldCache :=
  Editor.part.df k ((seen, step.ces), step.writes.map fun (rel, w) => .write rel w)

def newDf (k : NewCache) (step : Step') : Editor.PartLines.Edit × NewCache :=
  Derived.lines.df k (((80 : Nat), step.ces), step.writes)

def applied (es : Editor.PartLines.Edit) (ls : List Line) : List Line := Editor.PartLines.apply es ls

def start (n : Nat) : IO State := do
  let value := root n
  let t0 ← IO.monoNanosNow
  let old ← IO.lazyPure fun _ => oldF cells0 value
  let t1 ← IO.monoNanosNow
  let new ← IO.lazyPure fun _ => newF cells0 value
  let t2 ← IO.monoNanosNow
  IO.println s!"{old.1.length} lines; from nothing: as it is {(t1 - t0) / 1000} µs, derived {(t2 - t1) / 1000} µs"
  if !(decide (old.1 = new.1)) then IO.println "  !! the two draw different lines"
  return ⟨cells0, value, old.2, new.2, old.1, new.1⟩

/-- Runs steps through both, timing each, and checks what each keeps
against its lines from nothing. -/
def timed (name : String) (s : State) (steps : List Step') : IO State := do
  let mut s := s
  let mut oldTime := 0
  let mut newTime := 0
  let mut oldEdits := 0
  let mut newEdits := 0
  for step in steps do
    let t0 ← IO.monoNanosNow
    let old ← IO.lazyPure fun _ => oldDf s.old step
    let t1 ← IO.monoNanosNow
    let new ← IO.lazyPure fun _ => newDf s.new step
    let t2 ← IO.monoNanosNow
    oldTime := oldTime + (t1 - t0)
    newTime := newTime + (t2 - t1)
    oldEdits := oldEdits + old.1.length
    newEdits := newEdits + new.1.length
    s := { cells := run Editor.cellsEdits step.ces s.cells, value := run Derived.Writes step.writes s.value,
           old := old.2, new := new.2, oldLines := applied old.1 s.oldLines, newLines := applied new.1 s.newLines }
  let n := steps.length
  IO.println s!"  {name}: as it is {oldTime / n / 1000} µs ({oldEdits / n} line edits), derived {newTime / n / 1000} µs ({newEdits / n})"
  let fresh := (newF s.cells s.value).1
  if !(decide (s.newLines = fresh)) then IO.println "  !! derived: the lines kept aren't the lines from nothing"
  if !(decide (s.oldLines = fresh)) then IO.println "  !! as it is: the lines kept aren't the derived lines from nothing"
  return s

/-- A part of its own for each entry: what each keeps. -/
structure Part where
  value : Value
  old : OldCache
  new : NewCache
  oldLines : List Line
  newLines : List Line

/-- Runs steps through a part for each entry: a write goes to the entry
it's in, and a write of a definition to every part. -/
def timedParts (name : String) (ps : List Position) (cells : Editor.Cells) (parts : Array Part)
    (steps : List Step') : IO (Editor.Cells × Array Part) := do
  let mut parts := parts
  let mut cells := cells
  let mut oldTime := 0
  let mut newTime := 0
  let mut oldEdits := 0
  let mut newEdits := 0
  for step in steps do
    -- The parts the step reaches, and what it is to each.
    let reached : List (Nat × Step') :=
      match step.writes with
      | [(.element p :: rel, w)] => [(ps.idxOf p, { step with writes := [(rel, w)] })]
      | _ => (List.range parts.size).map fun i => (i, step)
    let t0 ← IO.monoNanosNow
    let held := parts
    let olds ← IO.lazyPure fun _ => reached.filterMap fun (i, st) => (held[i]?).map fun part => oldDf part.old st
    let t1 ← IO.monoNanosNow
    let news ← IO.lazyPure fun _ => reached.filterMap fun (i, st) => (held[i]?).map fun part => newDf part.new st
    let t2 ← IO.monoNanosNow
    oldTime := oldTime + (t1 - t0)
    newTime := newTime + (t2 - t1)
    cells := run Editor.cellsEdits step.ces cells
    for ((i, st), (old, new)) in reached.zip (olds.zip news) do
      oldEdits := oldEdits + old.1.length
      newEdits := newEdits + new.1.length
      match parts[i]? with
      | some part =>
        let updated : Part :=
          ⟨run Derived.Writes st.writes part.value, old.2, new.2, applied old.1 part.oldLines, applied new.1 part.newLines⟩
        parts := parts.set! i updated
      | none => pure ()
  let n := steps.length
  IO.println s!"  {name}: as it is {oldTime / n / 1000} µs ({oldEdits / n} line edits), derived {newTime / n / 1000} µs ({newEdits / n})"
  for part in parts do
    let fresh := (newF cells part.value).1
    if !(decide (part.newLines = fresh)) then IO.println "  !! derived: the lines kept aren't the lines from nothing"
    if !(decide (part.oldLines = fresh)) then IO.println "  !! as it is: the lines kept aren't the derived lines from nothing"
  return (cells, parts)

def main (args : List String) : IO Unit := do
  let n := (args.head?.bind (·.toNat?)).getD 300
  let ps := positions n
  let at_ (j : Nat) : Position := ps[(j * (if args.contains "top" then 0 else 37)) % n]!
  -- `x200` runs each step 200 times; `only:` and a word runs the steps named with it; `derived` skips the view as it is.
  let reps := List.range (((args.find? (·.startsWith "x")).bind fun a => (a.drop 1).toString.toNat?).getD 20)
  let only := ((args.find? (·.startsWith "only:")).map fun a => (a.drop 5).toString).getD ""
  let last := (Position.spread 12).getLast!
  let added := Position.between (some last) none
  let news := reps.map fun j => Position.between (some (ps[j * 11 % (n - 1)]!)) (some (ps[j * 11 % (n - 1) + 1]!))
  let steps : List (String × List Step') := [
    ("typing in a text", reps.map fun j =>
      { writes := [([.element (at_ j), .key Kinds.name, .key Kinds.bytes], some (.blob s!"entry, typed {j}".toUTF8.toList))] }),
    ("an element added to a list", reps.map fun j =>
      { writes := [([.element (at_ j), .key Kinds.fields, .element added], some (Value.u64 7))] }),
    ("an element taken away", reps.map fun j =>
      { writes := [([.element (at_ j), .key Kinds.fields, .element added], none)] }),
    ("a field added to a record", reps.map fun j =>
      { writes := [([.element (at_ j), .key Kinds.value], some (Value.u64 5))] }),
    ("a field taken away", reps.map fun j => { writes := [([.element (at_ j), .key Kinds.value], none)] }),
    ("a field's value replaced", reps.map fun j =>
      { writes := [([.element (at_ j), .key Kinds.body], some (Value.text s!"now text {j}"))] }),
    ("an entry added", (reps.zip news).map fun (j, p) => { writes := [([.element p], some (entry (1000 + j)))] }),
    ("an entry taken away", news.map fun p => { writes := [([.element p], none)] }),
    ("a label every entry has, renamed", reps.map fun j => { ces := [.set tag (some (nameOnly s!"tag {j}"))] }),
    ("a cell a tenth of the entries show, renamed", reps.map fun j =>
      { ces := [.set shared[3]! (some (nameOnly s!"shared, renamed {j}"))] }),
    ("a cell nothing shows, written", reps.map fun j => { ces := [.set unseen (some (nameOnly s!"unseen {j}"))] })]
  let steps := steps.filter fun (name, _) => (name.splitOn only).length > 1 || only.isEmpty
  if args.contains "parts" then
    -- A part for each entry, as the notebook has.
    let entries := (List.range n).map entry
    let t0 ← IO.monoNanosNow
    let olds ← IO.lazyPure fun _ => entries.map (oldF cells0)
    let t1 ← IO.monoNanosNow
    let news ← IO.lazyPure fun _ => entries.map (newF cells0)
    let t2 ← IO.monoNanosNow
    let lineCount := (olds.map (·.1.length)).foldl (· + ·) 0
    IO.println s!"{lineCount} lines in {n} parts; from nothing: as it is {(t1 - t0) / 1000} µs, derived {(t2 - t1) / 1000} µs"
    let mut parts : Array Part := #[]
    for (v, (old, new)) in entries.zip (olds.zip news) do
      if !(decide (old.1 = new.1)) then IO.println "  !! the two draw different lines"
      parts := parts.push ⟨v, old.2, new.2, old.1, new.1⟩
    let mut cells := cells0
    for (name, run) in steps do
      if !name.startsWith "an entry" then
        (cells, parts) ← timedParts name ps cells parts run
  else
    let mut s ← start n
    for (name, run) in steps do
      s ← timed name s run
