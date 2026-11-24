import Progred.Derived.Links

/-!
A node's own doc, for the view drawn by derivative: every form, drawn from
the node's label and what its keys look up, its kids in the doc's slots.
A slot is the kid's place among the value's own elements or fields; where
a value has none, the node draws the hole itself.

A node reads the definitions only through `look`, which answers for its
keys and no others (`Tree.reading2`): the cells its own value names, and
the cells their definitions name. So a definition written draws again the
nodes with that key, and that needs no proof form by form.

Not here yet: the selection (typing, holes being filled, fields being
added), errors marked.
-/

open Deui

namespace Progred.Derived

open Display (Hint emptied shallow container)

/-- What docs are drawn with besides the definitions. -/
structure Around where
  /-- Evaluations' outcomes, by expression. -/
  results : List (Value × Outcome) := []
  /-- What projections that are functions gave: the function, the record,
  and its layout. -/
  layouts : List (Value × Value × Value) := []

section forms

variable (look : CellId → Option Value)

/-- A cell's name, if its definition has one that isn't empty. -/
def name? (c : CellId) : Option String :=
  match ((look c).bind (·.field? Kinds.name)).bind Value.text? with
  | some "" => none
  | n => n

def shown (c : CellId) : String := (name? look c).getD c.short

def occ (path : Path) (kind : OccKind) (d : Doc) (cell : Option CellId := none) : Doc :=
  Doc.marked ⟨path, kind, false, cell⟩ d

/-- A hole: a place with no value. -/
def hole (path : Path) : Doc := occ path .hole (dim "_")

/-- Where a field's value is among a record's kids. -/
def slotOf (fields : List (CellId × Value)) (l : CellId) : Option Nat := fields.findIdx? (·.1 == l)

/-- A field's value: its kid's slot, or the hole where it has none. -/
def at_ (path : Path) (fields : List (CellId × Value)) (l : CellId) : Doc :=
  match slotOf fields l with
  | some i => .slot i
  | none => hole (path ++ [.key l])

/-- A record's name: its kid's slot, or `missing` where it has none. -/
def nameAt (path : Path) (fields : List (CellId × Value)) (missing : String) : Doc :=
  match slotOf fields Kinds.name with
  | some i => .slot i
  | none => occ (path ++ [.key Kinds.name]) .hole (dim missing)

/-- A field: its label, then its value beside it. -/
def field (path : Path) (fields : List (CellId × Value)) (l : CellId) : Doc :=
  .row [occ (path ++ [.key l]) .label (t (shown look l) .label) (some l), dim ": ", at_ path fields l]

/-- A record's fields in the order raw shows them: named labels by name,
then the rest. Each label's name is looked up once. -/
def ordered (fields : List (CellId × Value)) : List (CellId × Value) :=
  let withNames := fields.map fun f => (name? look f.1, f)
  let named := withNames.filter (·.1.isSome)
  let unnamed := withNames.filter (·.1.isNone)
  ((named.toArray.qsort (fun a b => a.1.getD "" < b.1.getD "")).toList ++ unnamed).map (·.2)

/-- A cell: open, its definition, hung under it, in parentheses; closed,
its name, or its kind and short id. -/
def cell (opened : Bool) (c : CellId) : Doc :=
  if opened then .row [delim "(", .slot 0, delim ")"]
  else
  match name? look c with
  | some n => t n .name
  | none =>
    match (look c).bind (·.kind?) with
    | some k => .row [delim "(", t (shown look k) .name, dim (" " ++ c.short), delim ")"]
    | none => dim c.short

def insertion (path : Path) (before after : Option Position) : Doc :=
  occ (path ++ [.element (Position.between before after)]) .insertion (point .ink)

/-- A list's elements, each in its slot, with a place to insert before each
and after the last. -/
def elementsFrom (path : Path) : Option Position → List Position → Nat → List Doc
  | _, [], _ => []
  | prev, p :: rest, i =>
    .row [insertion path prev (some p), .slot i, if rest.isEmpty then insertion path (some p) none else .row []] ::
      elementsFrom path (some p) rest (i + 1)

def elements (path : Path) (items : List (Position × Value)) : List Doc :=
  if items.isEmpty then [insertion path none none] else elementsFrom path none (items.map (·.1)) 0

def list (path : Path) (items : List (Position × Value)) : Doc :=
  let parts := elements path items
  container "[" "]" parts parts

/-- A raw record: `{label: value, …}`, with a place at its end to add a
field. -/
def record (path : Path) (fields : List (CellId × Value)) : Doc :=
  let parts := (ordered look fields).map fun (l, _) => field look path fields l
  let end_ := [occ path .fieldEnd (point .ink)]
  let flat : Doc := .row ([delim "{"] ++ Doc.sep (dim ", ") parts ++ end_ ++ [delim "}"])
  let lines : List Doc := match parts.reverse with
    | last :: before => before.reverse ++ [.row (last :: end_)]
    | [] => end_
  .alt flat (.col [delim "{", .indent 2 (.col lines), delim "}"])

/-- The cells a list of cells holds. -/
def cellsOf : Option Value → List CellId
  | some (.list items) => items.filterMap fun (_, v) => match v with | .cell c => some c | _ => none
  | _ => []

/-- The fields a kind's records show: its definition's, in order. -/
def fieldsOf (k : CellId) : List CellId := cellsOf ((look k).bind (·.field? Kinds.fields))

/-- A record of a kind: `kind name {fields}`, its kind's fields first, each
a hole where missing, then the rest. -/
def kinded (path : Path) (k : CellId) (fields : List (CellId × Value)) : Doc :=
  let declared := (fieldsOf look k).filter (· != Kinds.name)
  let hasName := (fieldsOf look k).contains Kinds.name || (slotOf fields Kinds.name).isSome
  let rest := (ordered look fields).filter fun (l, _) =>
    l != Kinds.isa && l != Kinds.name && !declared.contains l
  let parts := declared.map (field look path fields) ++ rest.map fun (l, _) => field look path fields l
  let name := if hasName then [t " ", nameAt path fields "name"] else []
  let head := [t (shown look k) .name] ++ name
  let flat : Doc := .row (head ++ [delim " {"] ++ Doc.sep (dim ", ") parts ++ [delim "}"])
  let stacked : Doc := .col [.row (head ++ [delim " {"]), .indent 2 (.col parts), delim "}"]
  if parts.isEmpty then .row head else .alt flat stacked

/-- A notebook: its entries; one with no list of them, as a field. -/
def notebook (path : Path) (fields : List (CellId × Value)) : Doc :=
  match (Value.record fields).field? Kinds.entries with
  | some (.list _) => at_ path fields Kinds.entries
  | _ => .row [t "notebook " .name, field look path fields Kinds.entries]

/-- A section: its name over its body, indented. -/
def section_ (path : Path) (fields : List (CellId × Value)) : Doc :=
  .col [.row [dim "▾ ", nameAt path fields "section"], .indent 2 (at_ path fields Kinds.sectionBody)]

/-- An evaluation: its expression, then what it gives. -/
def evaluation (path : Path) (fields : List (CellId × Value)) (outcome : Option Outcome) : Doc :=
  let expression := at_ path fields Kinds.expression
  let result : Doc :=
    match outcome with
    | some (.value shown type) =>
      if shown.isEmpty then .row [t type .dim] else .row [t shown .result, t (" : " ++ type) .dim]
    | some (.failed message _) => t (Display.brief message) .error
    | none => dim "…"
  let marked := occ (path ++ [.key Kinds.evaluation]) .computed result
  .alt (.row [expression, dim " → ", marked]) (.col [expression, .indent 2 (.row [dim "→ ", marked])])

/-- A lambda: `name [params] → body`, with what it returns after the
parameters if it says. -/
def lambda (path : Path) (fields : List (CellId × Value)) : Doc :=
  let returns :=
    if (slotOf fields Kinds.returns).isSome then [dim " : ", at_ path fields Kinds.returns] else []
  let body := at_ path fields Kinds.body
  let head := [nameAt path fields "λ", t " ", at_ path fields Kinds.params] ++ returns
  .alt (.row (head ++ [dim " → ", body])) (.col [.row (head ++ [dim " →"]), .indent 2 body])

/-- A call: the function, then its arguments by parameter; a function
written between two arguments goes between them. -/
def call (path : Path) (fields : List (CellId × Value)) : Doc :=
  let fn := (Value.record fields).field? Kinds.function
  let params : List CellId :=
    match fn with
    | some (.cell c) => cellsOf ((look c).bind (·.field? Kinds.params))
    | _ => []
  let symbol := match fn with
    | some (.cell c) => (Builtin.function? c).bind (·.symbol)
    | _ => none
  match symbol, params with
  | some sym, [a, b] =>
    let op := occ (path ++ [.key Kinds.function]) .value (dim (" " ++ sym ++ " "))
    .row [delim "(", at_ path fields a, op, at_ path fields b, delim ")"]
  | _, _ =>
    let head := at_ path fields Kinds.function
    let extra := (ordered look fields).filter fun (l, _) =>
      l != Kinds.isa && l != Kinds.function && !params.contains l
    let parts := params.map (field look path fields) ++ extra.map fun (l, _) => field look path fields l
    let flat : Doc := .row ([head, delim " {"] ++ Doc.sep (dim ", ") parts ++ [delim "}"])
    let stacked : Doc := .col [.row [head, delim " {"], .indent 2 (.col parts), delim "}"]
    if parts.isEmpty then .row [head, delim " {}"] else .alt flat stacked

/-- A record, drawn by a layout: its parts are the record's own, at their
fields. -/
partial def layout (path : Path) (fields : List (CellId × Value)) : Node → Doc
  | .row children => .row (children.map (layout path fields))
  | .column children => .col (children.map (layout path fields))
  | .indent child => .indent 2 (layout path fields child)
  | .either children =>
    match (children.map (layout path fields)).reverse with
    | [] => .row []
    | last :: before => before.foldl (fun rest d => .alt d rest) last
  | .words content => t content
  | .faint content => dim content
  | .part field => at_ path fields field

/-- The layout a kind's records are drawn with, for a record: its def's
projection, if that's a layout, or a function that has given this record
one. -/
def projection (layouts : List (Value × Value × Value)) (k : CellId) (v : Value) : Option Node :=
  match look k with
  | some d =>
    if d.kind? != some Kinds.def_ then none
    else
      (d.field? Kinds.projection).bind fun p =>
        let source := match p with
          | .cell c => (look c).getD p
          | _ => p
        (Node.read source).orElse fun _ =>
          (layouts.find? fun l => l.1 == source && l.2.1 == v).bind fun l => Node.read l.2.2
  | none => none

/-- A value, by the first form that takes it. -/
def drawn (around : Around) (l : Label) : Doc :=
  match l.value with
  | .cell c => cell look l.opened c
  | .blob b => t (GidText.hex b) .number
  | .list items => list l.path items
  | .record fields =>
    let v := l.value
    if (v.text?.isSome || v.u64?.isSome || v.f64?.isSome) && fields.length == 2 then Display.line v none
    else if v.literal? Kinds.bool == some [1] then t "true" .name
    else if v.literal? Kinds.bool == some [0] then t "false" .name
    else
      match v.kind? with
      | some k =>
        if k == Kinds.notebook then notebook look l.path fields
        else if k == Kinds.section_ then section_ l.path fields
        else if k == Kinds.evaluation then
          evaluation l.path fields
            ((l.deep.bind (·.field? Kinds.expression)).bind fun e => (around.results.find? (·.1 == e)).map (·.2))
        else if k == Kinds.lambda then lambda l.path fields
        else if k == Kinds.call then call look l.path fields
        else if k == Kinds.valueWrapper then
          .row [nameAt l.path fields "name", t " = ", at_ l.path fields Kinds.value]
        else
          match projection look around.layouts k (l.deep.getD v) with
          | some node => layout l.path fields node
          | none => kinded look l.path k fields
      | none => record look l.path fields

/-- A value at its path, as an occurrence. -/
def value (around : Around) (l : Label) : Doc :=
  occ l.path .value (drawn look around l) (match l.value with
    | .cell c => some c
    | _ => none)

/-- A node's own doc, as its place asks. -/
def shape (around : Around) (l : Label) : Doc :=
  match l.hint with
  | .value _ => value look around l
  | .name missing =>
    match l.value.text? with
    | some n => if n.isEmpty then occ l.path .value (dim missing) else occ l.path .value (t n .name)
    | none => occ l.path .hole (dim missing)
  | .param =>
    match l.value with
    | .cell c =>
      occ l.path .value (.row [t (shown look c) .name, if l.opened then .slot 0 else .row []]) (some c)
    | _ => value look around l
  | .entries =>
    match l.value with
    | .list items =>
      let parts := elements l.path items
      let numbered := (List.range parts.length).zip parts |>.map fun (i, d) =>
        (.row [dim (toString (i + 1) ++ (if i < 9 then "  " else " ")), d] : Doc)
      .col (Doc.sep (t "") numbered)
    | _ => value look around l
  | .body =>
    match l.value with
    | .list items => .col (elements l.path items)
    | _ => value look around l
  | .entry p => .col [.row [occ (Display.entryAt p) .entryPoint (point .ink), .slot 0], t ""]
  | .end_ => occ Display.entriesPath .entryPoint (point .ink)
  | .label => .row []
  | .params => value look around l
  | .paramType =>
    -- A parameter's definition, as its type: drawn if it has one.
    match l.value with
    | .record fields =>
      match slotOf fields Kinds.type_ with
      | some i => .row [dim ": ", .slot i]
      | none => .row []
    | _ => .row []

end forms

/-! ## What a node looks up -/

/-- The cell a value is, if it's one. -/
def cellOf : Option Value → List CellId
  | some (.cell c) => [c]
  | _ => []

/-- The cells a node's own value names, whose definitions it may read:
itself if it's a cell; a record's labels, for their names, and the cells
its fields hold. A literal reads none. -/
def keys1 (l : Label) : List CellId :=
  match l.value with
  | .cell c => [c]
  | .record fields =>
    if l.leaf then []
    else fields.map (·.1) ++ fields.filterMap fun (_, x) => match x with | .cell c => some c | _ => none
  | _ => []

/-- The cells a definition names, in its fields and the lists they hold. -/
def mentions : Value → List CellId
  | .record fields => fields.flatMap fun (_, x) => match x with
    | .cell c => [c]
    | .list items => items.filterMap fun (_, y) => match y with | .cell c => some c | _ => none
    | _ => []
  | _ => []

/-- The cells whose definitions a node reads further into than a name: a
cell itself, for its kind; a record's kind, for its fields and its
projection; a call's function, for its parameters. -/
def through (l : Label) : List CellId :=
  match l.value with
  | .cell c => [c]
  | .record _ =>
    if l.leaf then [] else cellOf (l.value.field? Kinds.isa) ++ cellOf (l.value.field? Kinds.function)
  | _ => []

/-- The cells those definitions name. -/
def keys2 (l : Label) (look : CellId → Option Value) : List CellId :=
  (through l).flatMap fun k => match look k with
    | some d => mentions d
    | none => []

/-! ## Under the definitions -/

/-- A cell's definition, under what a part is drawn under. -/
def get (u : Under.Value) (c : CellId) : Option Value := lookup u.2 c

def touches (d : Under.Edit) (c : CellId) : Bool := d.2.any (writes c)

/-- An edit that writes no definition changes no doc: the folds reach the
docs only through the tree. -/
def calm (d : Under.Edit) : Bool := d.2.isEmpty

/-- A cell no edit of a run writes has the definition it had. -/
theorem get_untouched (u : Under.Value) (d : Under.Edit) (c : CellId) (h : touches d c = false) :
    get (Under.apply d u) c = get u c := by
  show ((run cellsEdits d.2 u.2)[c]?).orElse _ = (u.2[c]?).orElse _
  rw [cells_untouched d.2 u.2 c h]

/-- A node's own doc, under the definitions: it reads them through its
keys. -/
def own (around : Around) : Under.Value → Label → Doc :=
  Tree.reading2 get keys1 keys2 fun l look => shape look around l

def stale : Under.Value → Under.Edit → Label → Bool := Tree.touched2 get touches keys1 keys2

/-- A tree's frames, as an incremental function of the definitions and the
tree. -/
def drawn' (around : Around) : Inc (prod Under (runs (Tree.edits Label))) (runs (Fit.edits Span)) :=
  Tree.drawn (own around) stale calm

theorem drawn'_ok (around : Around) : (drawn' around).ok := by
  apply Tree.drawn_ok
  · intro c d l hc
    obtain ⟨r, cells⟩ := c
    obtain ⟨r', ces⟩ := d
    cases ces with
    | nil => rfl
    | cons _ _ => simp [calm] at hc
  · exact Tree.reading2_touched get keys1 keys2 _ touches get_untouched

/-! ## A part's lines -/

/-- Frames within their ribbon. -/
abbrev Framed : EditStructure := prod (latest Nat) (runs (Fit.edits Span))

/-- A part's lines, edited line by line. -/
abbrev Lines : EditStructure := runs (Lists.editStructure (Deui.whole (plain Line)))

/-- The frames of a value at a path, drawn as its place asks. -/
def framed (around : Around) (path : Path) (hint : Hint) : Cached (prod Under (runs Writes)) Framed :=
  Cached.carrying (·.1.1) (compose (Cached.keeping (treed path hint)) (cached (drawn' around)))

theorem framed_ok (around : Around) (path : Path) (hint : Hint) : (framed around path hint).ok :=
  Cached.carrying_ok _ _
    (compose_ok _ _ (Cached.keeping_ok _ (treed_ok path hint)) (cached_ok _ (drawn'_ok around)))

/-- Its lines. -/
def lines (around : Around) (path : Path) (hint : Hint) : Cached (prod Under (runs Writes)) Lines :=
  compose (framed around path hint) (compose (Fit.fit measure) (Cached.lift (cached Text.rows)))

/-- The lines' derivative is right: its edits take the lines to those of
the value after its writes, under the definitions after theirs. -/
theorem lines_ok (around : Around) (path : Path) (hint : Hint) : (lines around path hint).ok :=
  compose_ok _ _ (framed_ok around path hint)
    (compose_ok _ _ (Fit.fit_ok measure) (Cached.lift_ok _ (cached_ok _ Text.rows_ok)))

end Progred.Derived
