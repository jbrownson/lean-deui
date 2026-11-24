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

-/

open Deui

namespace Progred.Derived

open Display (Hint emptied shallow container)

/-- What a node sees besides its label and the definitions: the selection,
where it's at the node or a step in; for an evaluation, what its
expression gave; for a record of a kind a function may draw, what
functions gave for it. -/
structure View where
  selection : Option Selection := none
  /-- The values an evaluation's error is about, of the node's own and
  those a step in. -/
  failing : List Path := []
  outcome : Option Outcome := none
  /-- The function, the record, and its layout. -/
  layouts : List (Value × Value × Value) := []
  deriving DecidableEq

section forms

variable (look : CellId → Option Value) (w : View)

/-- A cell's name, if its definition has one that isn't empty. -/
def name? (c : CellId) : Option String :=
  match ((look c).bind (·.field? Kinds.name)).bind Value.text? with
  | some "" => none
  | n => n

def shown (c : CellId) : String := (name? look c).getD c.short

/-- A doc, as an occurrence: a value an error is about is marked so. -/
def occ (path : Path) (kind : OccKind) (d : Doc) (cell : Option CellId := none) : Doc :=
  Doc.marked ⟨path, kind, kind == .value && w.failing.contains path, cell⟩ d

/-- The editing at a path, if the selection is typing there in `stage`. -/
def editingAt (path : Path) (stage : Stage) : Option Editing :=
  match w.selection with
  | some s => if s.path == path && s.stage == stage then s.editing else none
  | none => none

/-- Whether a pending selection sits at a path. -/
def pendingAt (path : Path) : Bool :=
  match w.selection with
  | some s => s.path == path && s.stage == .pending
  | none => false

/-- The step a pending selection is at, one step in from a path. -/
def pendingIn (path : Path) : Option Step :=
  match w.selection with
  | some s => if s.stage == .pending && s.path.dropLast == path then s.path.getLast? else none
  | none => none

/-- A hole: a place with no value, or the query being typed into it. -/
def hole (path : Path) : Doc :=
  match editingAt w path .pending with
  | some e => occ w path .hole (.row [Display.typing e .ink])
  | none =>
    match editingAt w path .edge with
    | some e => occ w path .hole (.row [Display.typing e .ink])
    | none => occ w path .hole (dim "_")

/-- A record's name where it has none: `missing`, or what's being typed. -/
def nameHole (path : Path) (missing : String) : Doc :=
  match editingAt w path .edge, editingAt w path .pending with
  | some e, _ => occ w path .value (Display.typing e .name)
  | _, some e => occ w path .hole (Display.typing e .name)
  | none, none => occ w path .hole (dim missing)

/-- Where a field's value is among a record's kids. -/
def slotOf (fields : List (CellId × Value)) (l : CellId) : Option Nat := fields.findIdx? (·.1 == l)

/-- A field's value: its kid's slot, or the hole where it has none. -/
def at_ (path : Path) (fields : List (CellId × Value)) (l : CellId) : Doc :=
  match slotOf fields l with
  | some i => .slot i
  | none => hole w (path ++ [.key l])

/-- A record's name: its kid's slot, or `missing` where it has none. -/
def nameAt (path : Path) (fields : List (CellId × Value)) (missing : String) : Doc :=
  match slotOf fields Kinds.name with
  | some i => .slot i
  | none => nameHole w (path ++ [.key Kinds.name]) missing

/-- A field: its label, then its value beside it. -/
def field (path : Path) (fields : List (CellId × Value)) (l : CellId) : Doc :=
  .row [occ w (path ++ [.key l]) .label (t (shown look l) .label) (some l), dim ": ", at_ w path fields l]

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
  occ w (path ++ [.element (Position.between before after)]) .insertion (point .ink)

/-- A list's elements, each in its slot, with a place to insert before each
and after the last. `places` are the positions in order, each with whether
an element is there: one that isn't is the hole of an element being added,
which is its own place, with no insertion point beside it. -/
def elementsFrom (path : Path) : Option (Position × Bool) → List (Position × Bool) → Nat → List Doc
  | _, [], _ => []
  | prev, (p, there) :: rest, i =>
    let beside := !there || (prev.map (·.2)).getD false
    let point : Doc := if beside then .row [] else insertion w path (prev.map (·.1)) (some p)
    let item : Doc := if there then .slot i else hole w (path ++ [.element p])
    let last : Doc := if rest.isEmpty && there then insertion w path (some p) none else .row []
    .row [point, item, last] :: elementsFrom path (some (p, !there)) rest (if there then i + 1 else i)

def elements (path : Path) (items : List (Position × Value)) : List Doc :=
  -- The element being added, if the selection is pending in this list.
  let pending : Option Position :=
    match pendingIn w path with
    | some (.element p) => if items.any (·.1 == p) then none else some p
    | _ => none
  let places : List (Position × Bool) :=
    match pending with
    | some p =>
      (items.filter fun (q, _) => Position.lt q p).map (fun (q, _) => (q, true)) ++ [(p, false)] ++
        (items.filter fun (q, _) => !Position.lt q p).map fun (q, _) => (q, true)
    | none => items.map fun (q, _) => (q, true)
  if places.isEmpty then [insertion w path none none] else elementsFrom w path none places 0

def list (path : Path) (items : List (Position × Value)) : Doc :=
  let parts := elements w path items
  container "[" "]" parts parts

/-- The label being typed for a new field, if the selection is adding one
to the record at a path. -/
def newLabel (path : Path) : List Doc :=
  match editingAt w path .label with
  | some e => [.row [occ w path .fieldEnd (Display.typing e .label), dim ": ", dim "_"]]
  | none => []

/-- The field whose value is being given, if the selection is pending at a
field the record at a path doesn't have yet: its label, and the hole. -/
def pendingField (path : Path) (fields : List (CellId × Value)) : List Doc :=
  match pendingIn w path with
  | some (.key l) => if fields.any (·.1 == l) then [] else [field look w path fields l]
  | _ => []

/-- Whether the selection is at one of some fields of the record at a path. -/
def selectedAmong (path : Path) (labels : List CellId) : Bool :=
  labels.any fun l => w.selection.any fun s => s.path == path ++ [.key l]

/-- A raw record: `{label: value, …}`, with a place at its end to add a
field. -/
def record (path : Path) (fields : List (CellId × Value)) : Doc :=
  let adding := pendingField look w path fields ++ newLabel w path
  let parts := ((ordered look fields).map fun (l, _) => field look w path fields l) ++ adding
  let end_ := if adding.isEmpty then [occ w path .fieldEnd (point .ink)] else []
  let flat : Doc := .row ([delim "{"] ++ Doc.sep (dim ", ") parts ++ end_ ++ [delim "}"])
  -- Stacked, the place to add a field rides at the end of the last field's line.
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
  let pending := if selectedAmong w path declared then [] else pendingField look w path fields
  let parts := declared.map (field look w path fields) ++ (rest.map fun (l, _) => field look w path fields l) ++
    pending ++ newLabel w path
  let name := if hasName then [t " ", nameAt w path fields "name"] else []
  let head := [t (shown look k) .name] ++ name
  let flat : Doc := .row (head ++ [delim " {"] ++ Doc.sep (dim ", ") parts ++ [delim "}"])
  let stacked : Doc := .col [.row (head ++ [delim " {"]), .indent 2 (.col parts), delim "}"]
  if parts.isEmpty then .row head else .alt flat stacked

/-- A notebook: its entries; one with no list of them, as a field. -/
def notebook (path : Path) (fields : List (CellId × Value)) : Doc :=
  match (Value.record fields).field? Kinds.entries with
  | some (.list _) => at_ w path fields Kinds.entries
  | _ => .row [t "notebook " .name, field look w path fields Kinds.entries]

/-- A section: its name over its body, indented. -/
def section_ (path : Path) (fields : List (CellId × Value)) : Doc :=
  .col [.row [dim "▾ ", nameAt w path fields "section"], .indent 2 (at_ w path fields Kinds.sectionBody)]

/-- An evaluation: its expression, then what it gives. -/
def evaluation (path : Path) (fields : List (CellId × Value)) (outcome : Option Outcome) : Doc :=
  let expression := at_ w path fields Kinds.expression
  let result : Doc :=
    match outcome with
    | some (.value shown type) =>
      if shown.isEmpty then .row [t type .dim] else .row [t shown .result, t (" : " ++ type) .dim]
    | some (.failed message _) => t (Display.brief message) .error
    | none => dim "…"
  let marked := occ w (path ++ [.key Kinds.evaluation]) .computed result
  .alt (.row [expression, dim " → ", marked]) (.col [expression, .indent 2 (.row [dim "→ ", marked])])

/-- A lambda: `name [params] → body`, with what it returns after the
parameters if it says, or is being told. -/
def lambda (path : Path) (fields : List (CellId × Value)) : Doc :=
  let returns :=
    if (slotOf fields Kinds.returns).isSome || pendingAt w (path ++ [.key Kinds.returns]) then
      [dim " : ", at_ w path fields Kinds.returns]
    else []
  let body := at_ w path fields Kinds.body
  let head := [nameAt w path fields "λ", t " ", at_ w path fields Kinds.params] ++ returns
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
    let op := occ w (path ++ [.key Kinds.function]) .value (dim (" " ++ sym ++ " "))
    .row [delim "(", at_ w path fields a, op, at_ w path fields b, delim ")"]
  | _, _ =>
    let head := at_ w path fields Kinds.function
    let extra := (ordered look fields).filter fun (l, _) =>
      l != Kinds.isa && l != Kinds.function && !params.contains l
    let pending := if selectedAmong w path params then [] else pendingField look w path fields
    let parts := params.map (field look w path fields) ++ (extra.map fun (l, _) => field look w path fields l) ++
      pending ++ newLabel w path
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
  | .part field => at_ w path fields field

/-- The layout a kind's records are drawn with, for a record: its def's
projection, if that's a layout, or a function that has given this record
one; `layouts` are what functions gave for the record. -/
def projection (layouts : List (Value × Value × Value)) (k : CellId) : Option Node :=
  match look k with
  | some d =>
    if d.kind? != some Kinds.def_ then none
    else
      (d.field? Kinds.projection).bind fun p =>
        let source := match p with
          | .cell c => (look c).getD p
          | _ => p
        (Node.read source).orElse fun _ =>
          (layouts.find? fun l => l.1 == source).bind fun l => Node.read l.2.2
  | none => none

/-- A value, by the first form that takes it. -/
def drawn (l : Label) : Doc :=
  match l.value with
  | .cell c => cell look l.opened c
  | .blob b => t (GidText.hex b) .number
  | .list items => list w l.path items
  | .record fields =>
    let v := l.value
    if (v.text?.isSome || v.u64?.isSome || v.f64?.isSome) && fields.length == 2 then Display.line v none
    else if v.literal? Kinds.bool == some [1] then t "true" .name
    else if v.literal? Kinds.bool == some [0] then t "false" .name
    else
      match v.kind? with
      | some k =>
        if k == Kinds.notebook then notebook look w l.path fields
        else if k == Kinds.section_ then section_ w l.path fields
        else if k == Kinds.evaluation then
          evaluation w l.path fields
            w.outcome
        else if k == Kinds.lambda then lambda w l.path fields
        else if k == Kinds.call then call look w l.path fields
        else if k == Kinds.valueWrapper then
          .row [nameAt w l.path fields "name", t " = ", at_ w l.path fields Kinds.value]
        else
          match projection look w.layouts k with
          | some node => layout w l.path fields node
          | none => kinded look w l.path k fields
      | none => record look w l.path fields

/-- A value at its path, as an occurrence; one being typed over shows
what's typed in its place: a picker's query, or its own line. -/
def value (l : Label) : Doc :=
  let cell := match l.value with
    | .cell c => some c
    | _ => none
  match editingAt w l.path .edge with
  | some e =>
    if e.picker then occ w l.path .value (.row [Display.typing e .ink]) cell
    else occ w l.path .value (Display.line l.value (some e)) cell
  | none => occ w l.path .value (drawn look w l) cell

/-- The hole of an entry being added before the entry at a path, or at the
entries' end for their path: the selection is pending and anchored there. -/
def adding (at_ : Path) : Option Path :=
  match w.selection with
  | some s => if s.stage == .pending && s.anchor == some at_ then some s.path else none
  | none => none

/-- A node's own doc, as its place asks. -/
def shape (l : Label) : Doc :=
  match l.hint with
  | .value _ => value look w l
  | .name missing =>
    let bare (e : Option Editing) (shown : String) : Doc :=
      match e with
      | some e => Display.typing e .name
      | none => t shown .name
    match editingAt w l.path .edge, editingAt w l.path .pending with
    | some e, _ => occ w l.path .value (bare (some e) "")
    | _, some e => occ w l.path .hole (bare (some e) "")
    | none, none =>
      match l.value.text? with
      | some n => if n.isEmpty then occ w l.path .value (dim missing) else occ w l.path .value (bare none n)
      | none => occ w l.path .hole (dim missing)
  | .param =>
    match l.value, editingAt w l.path .edge with
    | .cell c, none =>
      occ w l.path .value (.row [t (shown look c) .name, if l.opened then .slot 0 else .row []]) (some c)
    | _, _ => value look w l
  | .entries =>
    match l.value with
    | .list items =>
      let parts := elements w l.path items
      let numbered := (List.range parts.length).zip parts |>.map fun (i, d) =>
        (.row [dim (toString (i + 1) ++ (if i < 9 then "  " else " ")), d] : Doc)
      .col (Doc.sep (t "") numbered)
    | _ => value look w l
  | .body =>
    match l.value with
    | .list items => .col (elements w l.path items)
    | _ => value look w l
  | .entry p =>
    match adding w (Display.entryAt p) with
    | some at_ => .col [hole w at_, t "", .slot 0, t ""]
    | none => .col [.row [occ w (Display.entryAt p) .entryPoint (point .ink), .slot 0], t ""]
  | .end_ =>
    match adding w Display.entriesPath with
    | some at_ => hole w at_
    | none => occ w Display.entriesPath .entryPoint (point .ink)
  | .label =>
    -- Where there's no value at all: the root of a document with none.
    hole w l.path
  | .params => value look w l
  | .paramType =>
    -- A parameter's definition, as its type: drawn if it has one, or one is being given.
    match l.value with
    | .record fields =>
      if (slotOf fields Kinds.type_).isSome || pendingAt w (l.path ++ [.key Kinds.type_]) then
        .row [dim ": ", at_ w l.path fields Kinds.type_]
      else .row []
    | _ => .row []

end forms

/-! ## What a node looks up -/

/-- The cell a value is, if it's one. -/
def cellOf : Option Value → List CellId
  | some (.cell c) => [c]
  | _ => []

/-- The cells a node's own value names, whose definitions it may read:
itself if it's a cell; a record's labels, for their names, and the cells
its fields hold; and the label of a field the selection is adding to it.
A literal reads none. -/
def keys1 (sel : Option Selection) (l : Label) : List CellId :=
  match l.value with
  | .cell c => [c]
  | .record fields =>
    if l.leaf then []
    else
      -- The label of a field being given a value, which the record doesn't hold yet.
      (match pendingIn { selection := sel } l.path with
        | some (.key k) => [k]
        | _ => []) ++
      fields.map (·.1) ++ fields.filterMap fun (_, x) => match x with | .cell c => some c | _ => none
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

/-- A cell no edit of a run writes has the definition it had. -/
theorem get_untouched (u : Under.Value) (d : Under.Edit) (c : CellId) (h : touches d c = false) :
    get (Under.apply d u) c = get u c := by
  show ((run cellsEdits d.2 u.2)[c]?).orElse _ = (u.2[c]?).orElse _
  rw [cells_untouched d.2 u.2 c h]

/-- Whether a path is one step in from another. -/
def stepIn : Path → Path → Bool
  | [_], [] => true
  | a :: as, b :: bs => a == b && stepIn as bs
  | _, _ => false

/-- Whether a selection is at a node, or one step in. `depth` is how long
the selection's path is, worked out once for a walk: most nodes are at
another depth, by their labels, and are told so by two comparisons of
numbers. -/
def near (depth : Nat) (sel : Option Selection) (l : Label) : Bool :=
  match sel with
  | some s => (depth == l.depth && s.path == l.path) || (depth == l.depth + 1 && stepIn s.path l.path)
  | none => false

/-- The selection, as a node sees it: only if it's at the node, or one step
in, and as deep as the node's label says that is. One step in, at a kid
the node has, the kid shows what's typed, and the node sees only that
something is. -/
def seenBy (l : Label) (sel : Option Selection) : Option Selection :=
  match sel with
  | some s =>
    if s.path.length == l.depth && s.path == l.path then some s
    else if s.path.length == l.depth + 1 && stepIn s.path l.path then
      match s.path.getLast? with
      | some step =>
        if (l.value.step? step).isSome then
          some { s with editing := s.editing.map fun e => { text := "", caret := 0, picker := e.picker } }
        else some s
      | none => none
    else none
  | none => none

/-- How long a selection's path is. -/
def depthOf (sel : Option Selection) : Nat := (sel.map (·.path.length)).getD 0

theorem seenBy_far (l : Label) (sel : Option Selection) (h : near (depthOf sel) sel l = false) :
    seenBy l sel = none := by
  cases sel with
  | none => rfl
  | some s =>
    simp only [near, depthOf, Option.map_some, Option.getD_some, Bool.or_eq_false_iff] at h
    simp only [seenBy, h.1, h.2, Bool.false_eq_true, ite_false]

/-- What an evaluation's expression gave, for an evaluation's node. -/
def outcomeFor (results : List (Value × Outcome)) (l : Label) : Option Outcome :=
  match l.deep with
  | some v =>
    if v.kind? == some Kinds.evaluation then
      (v.field? Kinds.expression).bind fun e => (results.find? (·.1 == e)).map (·.2)
    else none
  | none => none

/-- What functions gave for a record, for the node of a record of a kind
a function may draw. -/
def layoutsFor (layouts : List (Value × Value × Value)) (l : Label) : List (Value × Value × Value) :=
  match l.deep with
  | some v => if v.kind? == some Kinds.evaluation then [] else layouts.filter (·.2.1 == v)
  | none => []

/-- The values errors are about, as a node sees them: its own, and those a
step in, which it may draw a mark for. -/
def failingFor (failing : List Path) (l : Label) : List Path :=
  failing.filter fun p => p == l.path || stepIn p l.path

/-- What a node sees of what a part is drawn with. -/
def view (seen : Display.Seen) (l : Label) : View :=
  ⟨seenBy l seen.selection, failingFor seen.failing l, outcomeFor seen.results l, layoutsFor seen.layouts.val l⟩

/-- What an edit of what a part is drawn under is, worked out once for a
walk: the states before and after, how deep each one's selection is,
whether what evaluations and functions gave is the very same, and whether
any definition is written. -/
structure Edited where
  before : Under.Value
  edit : Under.Edit
  depth : Nat
  depth' : Nat
  same : Bool
  sameFailing : Bool
  written : Bool

def edited (c : Under.Value) (d : Under.Edit) : Edited :=
  ⟨c, d, depthOf c.1.selection, depthOf d.1.selection,
    equal d.1.results c.1.results && equal d.1.layouts c.1.layouts, equal d.1.failing c.1.failing, !d.2.isEmpty⟩

/-- Whether what a node sees could differ across an edit. A node nowhere
near either selection sees neither; one not drawn from its whole value
sees no result; and where the results and what functions gave are the very
same, no node sees them differ. -/
def differs (p : Edited) (l : Label) : Bool :=
  ((near p.depth p.before.1.selection l || near p.depth' p.edit.1.selection l) &&
      decide (seenBy l p.edit.1.selection ≠ seenBy l p.before.1.selection)) ||
    (!p.sameFailing && decide (failingFor p.edit.1.failing l ≠ failingFor p.before.1.failing l)) ||
    (l.deep.isSome && !p.same &&
      (decide (outcomeFor p.edit.1.results l ≠ outcomeFor p.before.1.results l) ||
        decide (layoutsFor p.edit.1.layouts.val l ≠ layoutsFor p.before.1.layouts.val l)))

theorem same_of_decide {α : Type} [DecidableEq α] (a b : α) (h : decide (a ≠ b) = false) : a = b :=
  Decidable.not_not.mp (of_decide_eq_false h)

theorem view_of_not_differs (c : Under.Value) (d : Under.Edit) (l : Label) (h : differs (edited c d) l = false) :
    view d.1 l = view c.1 l := by
  simp only [differs, edited, Bool.or_eq_false_iff] at h
  obtain ⟨⟨hsel, hfail⟩, hdeep⟩ := h
  have e0 : failingFor d.1.failing l = failingFor c.1.failing l := by
    cases he : equal d.1.failing c.1.failing with
    | true => rw [equal_sound _ _ he]
    | false =>
      have := hfail
      simp only [he, Bool.not_false, Bool.true_and] at this
      exact same_of_decide _ _ this
  have e1 : seenBy l d.1.selection = seenBy l c.1.selection := by
    cases hn : (near (depthOf c.1.selection) c.1.selection l || near (depthOf d.1.selection) d.1.selection l) with
    | false =>
      simp only [Bool.or_eq_false_iff] at hn
      rw [seenBy_far l _ hn.1, seenBy_far l _ hn.2]
    | true =>
      have := hsel
      simp only [hn, Bool.true_and] at this
      exact same_of_decide _ _ this
  have e23 : outcomeFor d.1.results l = outcomeFor c.1.results l ∧
      layoutsFor d.1.layouts.val l = layoutsFor c.1.layouts.val l := by
    cases hd : l.deep with
    | none => simp [outcomeFor, layoutsFor, hd]
    | some v =>
      cases he : (equal d.1.results c.1.results && equal d.1.layouts c.1.layouts) with
      | true =>
        simp only [Bool.and_eq_true] at he
        rw [equal_sound _ _ he.1, equal_sound _ _ he.2]
        exact ⟨rfl, rfl⟩
      | false =>
        have := hdeep
        simp only [hd, he, Option.isSome_some, Bool.not_false, Bool.true_and, Bool.or_eq_false_iff] at this
        exact ⟨same_of_decide _ _ this.1, same_of_decide _ _ this.2⟩
  simp only [view, e0, e1, e23.1, e23.2]

/-- A node's own doc, from what nodes see by `seen`, under the
definitions of `u`: it reads those through its keys. -/
def ownBy (seen : Display.Seen) (u : Under.Value) (l : Label) : Doc :=
  Tree.reading2 get (fun l' => keys1 (seenBy l' seen.selection) l') keys2
    (fun l' look => shape look (view seen l') l') u l

/-- A node's own doc, under what a part is drawn under. -/
def own (u : Under.Value) (l : Label) : Doc := ownBy u.1 u l

/-- Whether an edit could change a node's own doc: it changes what the
node sees, or writes one of its keys. -/
def stale (p : Edited) (l : Label) : Bool :=
  differs p l ||
    (p.written &&
      Tree.touched2 get touches (fun l' => keys1 (seenBy l' p.before.1.selection) l') keys2 p.before p.edit l)

/-- An edit that changes no doc: it writes no definition, and leaves the
selection, what evaluations gave, what functions gave and what errors are
about as they were. -/
def calm (c : Under.Value) (d : Under.Edit) : Bool :=
  d.2.isEmpty && decide (d.1.selection = c.1.selection) && decide (d.1.results = c.1.results) &&
    decide (d.1.layouts = c.1.layouts) && decide (d.1.failing = c.1.failing)

/-- A tree's frames, as an incremental function of what a part is drawn
under and the tree. -/
def drawn' : Inc (prod Under (runs (Tree.edits Label))) (runs (Fit.edits Span)) :=
  Tree.drawn own edited stale calm

/-- A node that sees the same by two states is drawn the same by them,
under the same definitions. -/
theorem ownBy_view (seen seen' : Display.Seen) (u : Under.Value) (l : Label) (h : view seen' l = view seen l) :
    ownBy seen' u l = ownBy seen u l := by
  have hs : seenBy l seen'.selection = seenBy l seen.selection := congrArg View.selection h
  simp only [ownBy, Tree.reading2, h, hs]

theorem drawn'_ok : drawn'.ok := by
  apply Tree.drawn_ok
  · intro c d l hc
    obtain ⟨seen, cells⟩ := c
    obtain ⟨seen', ces⟩ := d
    simp only [calm, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hc
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
    cases h1
    have hv : view seen' l = view seen l := by simp only [view, h2, h3, h4, h5]
    exact ownBy_view seen seen' (seen', cells) l hv
  · intro c d l hs
    simp only [stale, Bool.or_eq_false_iff] at hs
    show ownBy d.1 (Under.apply d c) l = ownBy c.1 c l
    rw [ownBy_view c.1 d.1 _ l (view_of_not_differs c d l hs.1)]
    -- With no definition written, no key is touched.
    have untouched : Tree.touched2 get touches (fun l' => keys1 (seenBy l' c.1.selection) l') keys2 c d l = false := by
      cases he : d.2.isEmpty with
      | false => simpa [edited, he] using hs.2
      | true =>
        have none_ : d.2 = [] := by simpa using he
        simp [Tree.touched2, touches, none_]
    exact Tree.reading2_touched get _ keys2 _ touches get_untouched c d l untouched

/-! ## A part's lines -/

/-- Frames within their ribbon. -/
abbrev Framed : EditStructure := prod (latest Nat) (runs (Fit.edits Span))

/-- A part's lines, edited line by line. -/
abbrev Lines : EditStructure := runs (Lists.editStructure (Deui.whole (plain Line)))

/-- A seed's frames within the ribbon, as an incremental function of what
a part is drawn under and the seed: its tree hung with definitions, and
each node's own doc. It keeps what it's under, the seed and the tree, and
works out what it's under after an edit once for both. -/
def framed : Cached (prod Under (runs Seeds)) Framed where
  Cache := Under.Value × Seed × Tree Label
  f a := ((a.1.1.ribbon, Tree.frame (own a.1) (a.2.tree (linked (links a.1) follows))),
    (a.1, a.2, a.2.tree (linked (links a.1) follows)))
  df k d :=
    let u' := Under.apply d.1 k.1
    let made := treed.dfWith u' k.1 k.2.1 k.2.2 d.1 d.2
    ((d.1.1.ribbon, Tree.redraw (own u') (stale (edited k.1 d.1)) (calm k.1 d.1) k.2.2 made.1),
      (u', made.2, run (Tree.edits Label) made.1 k.2.2))

theorem framed_ok : framed.ok := by
  intro a d
  obtain ⟨h1, h2⟩ := treed_df_ok a.1 a.2 d.1 d.2
  have h3 := drawn'_ok (a.1, a.2.tree (linked (links a.1) follows))
    (d.1, (treed.df a.1 a.2 (a.2.tree (linked (links a.1) follows)) d.1 d.2).1)
  have h3' : run (Fit.edits Span)
      (Tree.redraw (own (Under.apply d.1 a.1)) (stale (edited a.1 d.1)) (calm a.1 d.1)
        (a.2.tree (linked (links a.1) follows)) (treed.df a.1 a.2 (a.2.tree (linked (links a.1) follows)) d.1 d.2).1)
      (Tree.frame (own a.1) (a.2.tree (linked (links a.1) follows))) =
      Tree.frame (own (Under.apply d.1 a.1)) ((run Seeds d.2 a.2).tree (linked (links (Under.apply d.1 a.1)) follows)) := by
    rw [← h2]
    exact h3
  show ((d.1.1.ribbon, run (Fit.edits Span) _ _), (Under.apply d.1 a.1, _, _)) = _
  have e1 : treed.dfWith (Under.apply d.1 a.1) a.1 a.2 (a.2.tree (linked (links a.1) follows)) d.1 d.2 =
      treed.df a.1 a.2 (a.2.tree (linked (links a.1) follows)) d.1 d.2 := rfl
  simp only [framed, e1, h1, h2, h3']
  rfl

/-- Its lines. -/
def lines : Cached (prod Under (runs Seeds)) Lines :=
  compose framed (compose (Fit.fit measure) (Cached.lift (cached Text.rows)))

/-- The lines' derivative is right: its edits take the lines to those of
the seed after its edits, under what it's drawn under after its edit. -/
theorem lines_ok : lines.ok :=
  compose_ok _ _ framed_ok (compose_ok _ _ (Fit.fit_ok measure) (Cached.lift_ok _ (cached_ok _ Text.rows_ok)))

end Progred.Derived
