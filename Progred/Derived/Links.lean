import Progred.Derived.Tree
import Progred.Model

/-!
A value's tree, hung with definitions: under a cell that's drawn open, its
definition's tree; under a parameter, its definition's, of which its type
is drawn. So the tree is a function of the value, the definitions and the
folds, and an edit of any of them is an edit of the tree.

A write goes where it lands (`rewrite`). An edit of the definitions or the
folds walks the tree for its cells (`relink`): one that opens or closes, or
whose definition is written, has what hangs under it made again; one that
stays as it is is walked on into. `treed_ok` is the law.
-/

open Deui

namespace Progred.Derived

open Display (Hint emptied shallow)

/-! ## Definitions -/

abbrev Cells := Std.TreeMap CellId Value

abbrev cellsEdits : EditStructure := ⟨Cells, Model.CellsEdit, Model.CellsEdit.apply⟩

/-- The library's definitions, by cell. -/
def table : Cells := Builtin.library.foldr (fun (c, v) m => m.insert c v) {}

/-- A cell's definition: the document's, else the library's. -/
def lookup (cells : Cells) (c : CellId) : Option Value := (cells[c]?).orElse fun _ => table[c]?

/-- Whether an edit of the definitions writes a cell. -/
def writes (c : CellId) : Model.CellsEdit → Bool
  | .set x _ => x == c
  | .all _ => true

/-- A cell no edit of a run writes has the definition it had. -/
theorem cells_untouched (ces : List Model.CellsEdit) (cells : Cells) (c : CellId)
    (h : ces.any (writes c) = false) : (run cellsEdits ces cells)[c]? = cells[c]? := by
  induction ces generalizing cells with
  | nil => rfl
  | cons ce rest ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    show (run cellsEdits rest (Model.CellsEdit.apply ce cells))[c]? = _
    rw [ih _ h.2]
    cases ce with
    | all new => simp [writes] at h
    | set x v =>
      have ne : c ≠ x := fun e => by simp [writes, e] at h
      simp only [Model.CellsEdit.apply, Model.defined_other cells x v c ne]

/-! ## What hangs under a cell -/

/-- What a tree is hung with: the definitions, and the folds the user set,
by path, true for closed. -/
structure Links where
  cells : Cells
  folds : List (Path × Bool)

/-- Whether a cell is drawn open at a path: as the user set it, else open
when it has a definition of the document's that's more than a name, isn't
inside another cell's definition, and is the root, a list's element, an
evaluation's expression, or a field of a record with no kind. -/
def isOpen (ln : Links) (path : Path) (c : CellId) (plain : Bool) : Bool :=
  match ln.folds.find? (·.1 == path) with
  | some (_, closed) => !closed && (lookup ln.cells c).isSome
  | none =>
    let more := match ln.cells[c]? with
      | some (.record [(l, _)]) => l != Kinds.name
      | some _ => true
      | none => false
    more && !(path.contains .follow) &&
      match path.getLast? with
      | none | some (.element _) => true
      | some (.key l) => l == Kinds.expression || (l != Kinds.isa && plain)
      | some .follow => false

/-- Whether a cell has its definition hung under it, by how it's drawn: a
parameter always, for its type; a value where it's drawn open. -/
def opens (ln : Links) (path : Path) (hint : Hint) (c : CellId) : Bool :=
  match hint with
  | .param => true
  | .value plain => isOpen ln path c plain
  | .params => isOpen ln path c false
  | .entries => isOpen ln path c false
  | .body => isOpen ln path c false
  | _ => false

/-- How a definition hung under a cell is drawn. -/
def linkHint : Hint → Hint
  | .param => .paramType
  | _ => .value false

/-- The definition hung under a cell, if one is. -/
def target (ln : Links) (path : Path) (hint : Hint) (c : CellId) : Option Value :=
  if opens ln path hint c then lookup ln.cells c else none

/-- What hangs under a cell: its definition's tree, with what hangs under
the cells in that, as far as `n` definitions in. -/
def linked (ln : Links) : Nat → Path → Hint → CellId → List (Tree Label)
  | 0, _, _, _ => []
  | n + 1, path, hint, c =>
    match target ln path hint c with
    | some d => [tree (linked ln n) (path ++ [.follow]) (linkHint hint) d]
    | none => []

/-- How many definitions in a tree goes: more than cells are opened
inside one another. -/
def follows : Nat := 32

/-- A value's tree, hung with definitions. -/
def grown (ln : Links) (path : Path) (hint : Hint) (v : Value) : Tree Label := tree (linked ln follows) path hint v

/-! ## Links made again -/

section relink

variable (inner : Label → List (Tree Label) → List (Tree.Edit Label))

mutual
/-- The edits of a tree for its cells, each as `inner` says, from the
cell's label and what hangs under it. A subtree with no cell edited gives
none. -/
def relinkTree : Tree Label → List (Tree.Edit Label)
  | .node l kids =>
    match l.value with
    | .cell _ => inner l kids
    | _ =>
      let runs := relinkKids kids
      if runs.isEmpty then [] else [.each runs]

def relinkKids : List (Tree Label) → List (List (Tree.Edit Label))
  | [] => []
  | k :: ks =>
    let run := relinkTree k
    let rest := relinkKids ks
    if run.isEmpty && rest.isEmpty then [] else run :: rest
end

variable (hang hang' : Path → Hint → CellId → List (Tree Label))

/-- A kid's run and the runs of the kids after it, applied, where each
takes its own where it goes. -/
theorem relinkKids_cons (k k' : Tree Label) (ks ks' : List (Tree Label))
    (hk : run (Tree.edits Label) (relinkTree inner k) k = k')
    (ih : Tree.Edit.applyEach (relinkKids inner ks) ks = ks') :
    Tree.Edit.applyEach (relinkKids inner (k :: ks)) (k :: ks) = k' :: ks' := by
  simp only [relinkKids]
  cases hn : ((relinkTree inner k).isEmpty && (relinkKids inner ks).isEmpty) with
  | true =>
    obtain ⟨h1, h2⟩ : relinkTree inner k = [] ∧ relinkKids inner ks = [] := by simpa using hn
    rw [h1] at hk
    rw [h2, Tree.Edit.applyEach_nil] at ih
    simp only [ite_true, Tree.Edit.applyEach_nil]
    rw [← ih]
    exact congrArg (· :: ks) hk
  | false =>
    simp only [Bool.false_eq_true, ite_false, Tree.Edit.applyEach, Tree.Edit.applyRun_eq]
    rw [hk, ih]

/-- A node that isn't a cell, with its kids' runs applied. -/
theorem relink_node (l : Label) (ks ks' : List (Tree Label)) (hl : ∀ c, l.value ≠ .cell c)
    (h : Tree.Edit.applyEach (relinkKids inner ks) ks = ks') :
    run (Tree.edits Label) (relinkTree inner (.node l ks)) (.node l ks) = .node l ks' := by
  have step : relinkTree inner (.node l ks) =
      if (relinkKids inner ks).isEmpty then [] else [.each (relinkKids inner ks)] := by
    rw [relinkTree]
    cases hv : l.value with
    | cell c => exact absurd hv (hl c)
    | blob _ => rfl
    | list _ => rfl
    | record _ => rfl
  rw [step]
  cases he : (relinkKids inner ks).isEmpty with
  | true =>
    have none_ : relinkKids inner ks = [] := by simpa using he
    rw [none_, Tree.Edit.applyEach_nil] at h
    simp only [ite_true]
    show Tree.node l ks = _
    rw [h]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    show Tree.Edit.apply (.each (relinkKids inner ks)) (.node l ks) = _
    simp only [Tree.Edit.apply, h]

theorem label_not_cell (path : Path) (hint : Hint) (v : Value) (hv : ∀ c, v ≠ .cell c) :
    ∀ c, (label path hint v).value ≠ .cell c := by
  intro c
  cases v with
  | cell x => exact absurd rfl (hv x)
  | blob _ => intro e; cases e
  | list _ => intro e; cases e
  | record _ => intro e; cases e

mutual
/-- Relinking takes a value's tree hung one way to its tree hung another,
if `inner` takes each cell there. -/
theorem relinkTree_ok
    (hinner : ∀ path hint c, run (Tree.edits Label)
        (relinkTree inner (tree hang path hint (.cell c))) (tree hang path hint (.cell c)) =
      tree hang' path hint (.cell c)) :
    ∀ (v : Value) (path : Path) (hint : Hint),
      run (Tree.edits Label) (relinkTree inner (tree hang path hint v)) (tree hang path hint v) =
        tree hang' path hint v
  | .cell c, path, hint => hinner path hint c
  | .blob b, path, hint => by
    rw [tree, tree]
    exact relink_node inner _ [] [] (label_not_cell path hint (.blob b) (fun c e => by cases e)) rfl
  | .list items, path, hint => by
    rw [tree, tree]
    exact relink_node inner _ _ _ (label_not_cell path hint (.list items) (fun c e => by cases e))
      (relinkItems_ok hinner items path (itemHint hint))
  | .record fields, path, hint => by
    rw [tree, tree]
    cases hleaf : (label path hint (.record fields)).leaf with
    | true =>
      simp only [ite_true]
      exact relink_node inner _ [] [] (label_not_cell path hint (.record fields) (fun c e => by cases e)) rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact relink_node inner _ _ _ (label_not_cell path hint (.record fields) (fun c e => by cases e))
        (relinkFields_ok hinner fields path hint _)

theorem relinkItems_ok
    (hinner : ∀ path hint c, run (Tree.edits Label)
        (relinkTree inner (tree hang path hint (.cell c))) (tree hang path hint (.cell c)) =
      tree hang' path hint (.cell c)) :
    ∀ (items : List (Position × Value)) (path : Path) (hint : Hint),
      Tree.Edit.applyEach (relinkKids inner (itemTrees hang path hint items)) (itemTrees hang path hint items) =
        itemTrees hang' path hint items
  | [], _, _ => by
    simp only [itemTrees]
    rfl
  | (p, x) :: rest, path, hint => by
    simp only [itemTrees]
    exact relinkKids_cons inner _ _ _ _ (relinkTree_ok hinner x _ _) (relinkItems_ok hinner rest path hint)

theorem relinkFields_ok
    (hinner : ∀ path hint c, run (Tree.edits Label)
        (relinkTree inner (tree hang path hint (.cell c))) (tree hang path hint (.cell c)) =
      tree hang' path hint (.cell c)) :
    ∀ (fields : List (CellId × Value)) (path : Path) (hint : Hint) (kind : Option CellId),
      Tree.Edit.applyEach (relinkKids inner (fieldTrees hang path hint kind fields))
          (fieldTrees hang path hint kind fields) =
        fieldTrees hang' path hint kind fields
  | [], _, _, _ => by
    simp only [fieldTrees]
    rfl
  | (l, x) :: rest, path, hint, kind => by
    simp only [fieldTrees]
    exact relinkKids_cons inner _ _ _ _ (relinkTree_ok hinner x _ _) (relinkFields_ok hinner rest path hint kind)
end

end relink

/-- The edits of a cell's node when what the tree is hung with changes:
`touched` says whether a cell's definition was written. A cell that's hung
before and after with the definition it had is walked on into; any other
whose hanging changes has it made again. -/
def relinkCell (ln ln' : Links) (touched : CellId → Bool) :
    Nat → Label → List (Tree Label) → List (Tree.Edit Label)
  | 0, _, _ => []
  | n + 1, l, kids =>
    match l.value with
    | .cell c =>
      match target ln l.path l.hint c, target ln' l.path l.hint c, kids with
      | none, none, _ => []
      | some _, some _, [kid] =>
        if touched c then [.replace (tree (linked ln' (n + 1)) l.path l.hint (.cell c))]
        else (relinkTree (relinkCell ln ln' touched n) kid).map (.kid 0)
      | _, _, _ => [.replace (tree (linked ln' (n + 1)) l.path l.hint (.cell c))]
    | _ => []

theorem cell_tree (hang : Path → Hint → CellId → List (Tree Label)) (path : Path) (hint : Hint) (c : CellId) :
    tree hang path hint (.cell c) =
      .node { label path hint (.cell c) with opened := !(hang path hint c).isEmpty } (hang path hint c) := by
  rw [tree]

/-- A cell's node, relinked, is the node hung the new way: if a cell that
isn't touched has the definition it had. -/
theorem relinkCell_ok (ln ln' : Links) (touched : CellId → Bool)
    (hsame : ∀ c, touched c = false → lookup ln'.cells c = lookup ln.cells c) :
    ∀ (n : Nat) (path : Path) (hint : Hint) (c : CellId),
      run (Tree.edits Label)
          (relinkTree (relinkCell ln ln' touched n) (tree (linked ln n) path hint (.cell c)))
          (tree (linked ln n) path hint (.cell c)) =
        tree (linked ln' n) path hint (.cell c)
  | 0, path, hint, c => by
    rw [cell_tree, cell_tree, relinkTree]
    rfl
  | n + 1, path, hint, c => by
    have ih := relinkTree_ok (relinkCell ln ln' touched n) (linked ln n) (linked ln' n)
      (relinkCell_ok ln ln' touched hsame n)
    rw [cell_tree (linked ln (n + 1)), relinkTree]
    simp only [label, labelOf, shallow, relinkCell]
    cases ht : target ln path hint c with
    | none =>
      have lk : linked ln (n + 1) path hint c = [] := by simp only [linked, ht]
      rw [lk]
      cases ht' : target ln' path hint c with
      | none =>
        have lk' : linked ln' (n + 1) path hint c = [] := by simp only [linked, ht']
        rw [cell_tree (linked ln' (n + 1)), lk']
        rfl
      | some d' => rfl
    | some d =>
      have lk : linked ln (n + 1) path hint c = [tree (linked ln n) (path ++ [.follow]) (linkHint hint) d] := by
        simp only [linked, ht]
      rw [lk]
      cases ht' : target ln' path hint c with
      | none => rfl
      | some d' =>
        cases htc : touched c with
        | true => rfl
        | false =>
          have same : d' = d := by
            simp only [target] at ht ht'
            split at ht <;> split at ht' <;> simp_all [hsame c htc]
          subst same
          have lk' : linked ln' (n + 1) path hint c =
              [tree (linked ln' n) (path ++ [.follow]) (linkHint hint) d'] := by simp only [linked, ht']
          rw [cell_tree (linked ln' (n + 1)), lk']
          have step := Tree.run_kid
            ({ label path hint (.cell c) with opened := true } : Label)
            [] (tree (linked ln n) (path ++ [.follow]) (linkHint hint) d') []
            (relinkTree (relinkCell ln ln' touched n) (tree (linked ln n) (path ++ [.follow]) (linkHint hint) d'))
          rw [ih d' (path ++ [Step.follow]) (linkHint hint)] at step
          exact step

/-! ## The tree, as an incremental function -/

/-- What a part is drawn under: what of the editor's state it's drawn
with, and the definitions. -/
abbrev Under : EditStructure := prod (latest Display.Seen) (runs cellsEdits)

def links (u : Under.Value) : Links := ⟨u.2, u.1.folds⟩

/-- A run of writes, as the value after and the edits of its tree. -/
def rewrites (hang : Path → Hint → CellId → List (Tree Label)) (path : Path) (hint : Hint) :
    List (List Step × Option Value) → Value → List (Tree.Edit Label) × Value
  | [], v => ([], v)
  | w :: ws, v =>
    match rewrite hang path hint v w.1 w.2 with
    | some (v', es) =>
      let rest := rewrites hang path hint ws v'
      (es ++ rest.1, rest.2)
    | none => rewrites hang path hint ws v

theorem rewrites_ok (hang : Path → Hint → CellId → List (Tree Label)) (path : Path) (hint : Hint) :
    ∀ (ws : List (List Step × Option Value)) (v : Value),
      (rewrites hang path hint ws v).2 = run Writes ws v ∧
        run (Tree.edits Label) (rewrites hang path hint ws v).1 (tree hang path hint v) =
          tree hang path hint (run Writes ws v)
  | [], _ => ⟨rfl, rfl⟩
  | w :: ws, v => by
    have h := rewrite_ok hang w.1 path hint v w.2
    have e : run Writes (w :: ws) v = run Writes ws (v.written w.1 w.2) := rfl
    rw [e]
    simp only [rewrites]
    cases hr : rewrite hang path hint v w.1 w.2 with
    | none =>
      rw [hr] at h
      have same : v.written w.1 w.2 = v := by simp [Value.written, h]
      rw [same]
      exact rewrites_ok hang path hint ws v
    | some made =>
      obtain ⟨v', es⟩ := made
      rw [hr] at h
      have to : v.written w.1 w.2 = v' := by simp [Value.written, h.1]
      rw [to]
      obtain ⟨r1, r2⟩ := rewrites_ok hang path hint ws v'
      refine ⟨r1, ?_⟩
      show run (Tree.edits Label) (es ++ _) _ = _
      rw [run_append, h.2, r2]

/-- Whether a run of edits of the definitions writes a cell. -/
def touchedBy (ces : List Model.CellsEdit) (c : CellId) : Bool := ces.any (writes c)

/-- The tree's edits and the value after, for an edit of what it's under
and a run of writes: its cells relinked, unless neither the definitions
nor the folds change; then the writes, where they land. -/
def treed.df (path : Path) (hint : Hint) (u : Under.Value) (v : Value) (t : Tree Label) (d : Under.Edit)
    (ws : List (List Step × Option Value)) : List (Tree.Edit Label) × Value :=
  let u' := Under.apply d u
  let first :=
    if d.2.isEmpty && decide (d.1.folds = u.1.folds) then []
    else relinkTree (relinkCell (links u) (links u') (touchedBy d.2) follows) t
  let made := rewrites (linked (links u') follows) path hint ws v
  (first ++ made.1, made.2)

/-- A value's tree hung with definitions, as an incremental function of
what it's under and the value. It keeps them, and the tree. -/
def treed (path : Path) (hint : Hint) : Cached (prod Under (runs Writes)) (runs (Tree.edits Label)) where
  Cache := Under.Value × Value × Tree Label
  f a := (grown (links a.1) path hint a.2, (a.1, a.2, grown (links a.1) path hint a.2))
  df k d :=
    let made := treed.df path hint k.1 k.2.1 k.2.2 d.1 d.2
    (made.1, (Under.apply d.1 k.1, made.2, run (Tree.edits Label) made.1 k.2.2))

theorem treed_df_ok (path : Path) (hint : Hint) (u : Under.Value) (v : Value) (d : Under.Edit)
    (ws : List (List Step × Option Value)) :
    (treed.df path hint u v (grown (links u) path hint v) d ws).2 = run Writes ws v ∧
      run (Tree.edits Label) (treed.df path hint u v (grown (links u) path hint v) d ws).1
          (grown (links u) path hint v) =
        grown (links (Under.apply d u)) path hint (run Writes ws v) := by
  obtain ⟨r1, r2⟩ := rewrites_ok (linked (links (Under.apply d u)) follows) path hint ws v
  refine ⟨r1, ?_⟩
  simp only [treed.df]
  rw [run_append]
  have first : run (Tree.edits Label)
      (if d.2.isEmpty && decide (d.1.folds = u.1.folds) then []
        else relinkTree (relinkCell (links u) (links (Under.apply d u)) (touchedBy d.2) follows)
          (grown (links u) path hint v)) (grown (links u) path hint v) =
      grown (links (Under.apply d u)) path hint v := by
    cases hc : (d.2.isEmpty && decide (d.1.folds = u.1.folds)) with
    | true =>
      obtain ⟨h1, h2⟩ : d.2 = [] ∧ d.1.folds = u.1.folds := by simpa using hc
      obtain ⟨seen, cells⟩ := u
      obtain ⟨seen', ces⟩ := d
      cases h1
      show grown ⟨cells, seen.folds⟩ path hint v = grown ⟨cells, seen'.folds⟩ path hint v
      rw [h2]
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact relinkTree_ok _ _ _
        (relinkCell_ok (links u) (links (Under.apply d u)) (touchedBy d.2)
          (fun c hc => by
            show ((run cellsEdits d.2 u.2)[c]?).orElse _ = (u.2[c]?).orElse _
            rw [cells_untouched d.2 u.2 c hc]) follows) v path hint
  rw [first]
  exact r2

theorem treed_ok (path : Path) (hint : Hint) : (treed path hint).ok := by
  intro a d
  obtain ⟨h1, h2⟩ := treed_df_ok path hint a.1 a.2 d.1 d.2
  show (run (Tree.edits Label) _ (grown (links a.1) path hint a.2), _) =
    (grown (links (Under.apply d.1 a.1)) path hint (run Writes d.2 a.2), _)
  simp only [treed, h1, h2]
  rfl

end Progred.Derived
