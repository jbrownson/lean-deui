import Std.Data.TreeSet
import Progred.Writes
import Progred.Builtin
import Progred.GidText
import Progred.Layout

/-!
The projection: a document as a tree of frames, each a value drawn where it
is, with the values inside it as its kids. Every drawn thing is an
occurrence, so a selection, an arrow key or a click finds its place. A
value is drawn by the first form that takes it: a literal, the form of its
kind (notebook, section, evaluation, lambda, call, value wrapper), the
generic `kind name {fields}`, else raw: `(cell)`, `[list]`, `{record}`,
`0xblob`.

A frame is drawn from little: its value with what's inside its lists and
records left out, the definitions it looks up, and what of the selection
is at it. So a change deep in a value leaves the frames above it as they
were, and what's typed changes the one frame it's typed in.
-/

namespace Progred

/-- What a selection is of: a value, a value being written where there is
none, or a new field's label, at the record that will hold it. -/
inductive Stage where
  | edge | pending | label
  deriving DecidableEq, Inhabited, Repr

/-- Text being typed at the selection: a line of the value's own (text, a
number), or a query a picker answers. -/
structure Editing where
  text : String
  caret : Nat
  picker : Bool
  choice : Nat := 0
  deriving DecidableEq, Inhabited

structure Selection where
  path : Path
  stage : Stage := .edge
  editing : Option Editing := none
  /-- For an entry being added to the root notebook: the path of the entry
  it's before, or of the entries for one at their end. Its part draws it. -/
  anchor : Option Path := none
  deriving DecidableEq, Inhabited

/-- What an evaluation gave: a value and its type, or what went wrong, and
the value it's about, as a path from the expression, if it's in it. -/
inductive Outcome where
  | value (shown type : String)
  | failed (message : String) (at_ : Option Path := none)
  deriving Inhabited, DecidableEq

/-- What the projection is of, besides the document. -/
structure Shown where
  doc : Document
  library : Library
  selection : Option Selection := none
  /-- Folds the user set, by path: true is closed. -/
  folds : List (Path × Bool) := []
  /-- Evaluations' outcomes, by expression. -/
  results : List (Value × Outcome) := []
  /-- What projections that are functions gave: the function, the record,
  and its layout. -/
  layouts : List (Value × Value × Value) := []

/-- A layout: what a projection draws a record with. It's read from a
value, a call of a layout function, whether a document holds it or a
function gave it. -/
inductive Node where
  | row (children : List Node)
  | column (children : List Node)
  | indent (child : Node)
  /-- The first of its children that fits. -/
  | either (children : List Node)
  | words (content : String)
  | faint (content : String)
  /-- The record's part at a field, drawn in place, where it's edited. -/
  | part (field : CellId)
  deriving Inhabited

/-- A layout, read from a value; none if the value isn't one all through. -/
partial def Node.read (v : Value) : Option Node := do
  guard (v.kind? == some Kinds.call)
  let function ← match v.field? Kinds.function with
    | some (.cell c) => some c
    | _ => none
  let children (label : CellId) : Option (List Node) :=
    match v.field? label with
    | some (.list items) => items.mapM fun (_, w) => Node.read w
    | _ => none
  let text (label : CellId) : Option String := (v.field? label).bind Value.text?
  if function == Builtin.Layout.row then .row <$> children Builtin.Layout.rowChildren
  else if function == Builtin.Layout.column then .column <$> children Builtin.Layout.columnChildren
  else if function == Builtin.Layout.either then .either <$> children Builtin.Layout.eitherChildren
  else if function == Builtin.Layout.indent then .indent <$> ((v.field? Builtin.Layout.indentChild).bind Node.read)
  else if function == Builtin.Layout.words then .words <$> text Builtin.Layout.wordsContent
  else if function == Builtin.Layout.faint then .faint <$> text Builtin.Layout.faintContent
  else if function == Builtin.Layout.part then
    match v.field? Builtin.Layout.partField with
    | some (.cell c) => some (.part c)
    | _ => none
  else none

namespace Display

/-- How a kid is drawn, as its place asks. -/
inductive Hint where
  /-- A value; `plain` if it's a field of a record with no kind, where a
  cell opens. -/
  | value (plain : Bool := false)
  /-- A record's name, typed in place; without one, `missing`. -/
  | name (missing : String)
  /-- A lambda's parameters, and one of them. -/
  | params
  | param
  /-- A parameter's definition, of which its type is drawn. -/
  | paramType
  /-- A notebook's entries, and a section's body. -/
  | entries
  | body
  /-- The label being typed for a new field, at the record it's added to. -/
  | label
  /-- A part of the document: an entry of the root notebook, held as a
  list of the one; and the end of its entries. -/
  | entry (position : Position)
  | end_
  deriving DecidableEq, Inhabited

/-- Whether a frame drawn this way is where a selection at its path, in a
stage, is typed. -/
def Hint.listens : Hint → Stage → Bool
  | .label, .label => true
  | .label, _ => false
  | _, .label => false
  | _, _ => true

/-- A frame's kid: the step to it, none for one at the frame's own path;
how it's drawn; and the paths errors are about, among which it may be. -/
structure Kid where
  step : Option Step
  hint : Hint := .value
  errors : List Path := []
  deriving DecidableEq, Inhabited

/-- What a frame is of: where it is, how it's drawn, and its value. -/
structure Seed where
  path : Path
  hint : Hint := .value
  errors : List Path := []
  value : Option Value
  deriving Inhabited

/-- What a frame reads of its whole value, where a form needs it: what an
evaluation gave, and the layout a record's kind draws it with. -/
structure Deep where
  outcome : Option Outcome := none
  node : Option Node := none

/-- A value with what's inside it left out. -/
def emptied : Value → Value
  | .list _ => .list []
  | .record _ => .record []
  | v => v

/-- A value with what's inside its elements and fields left out: all of
its value that a frame is drawn from. -/
def shallow : Value → Value
  | .list items => .list (items.map fun (p, v) => (p, emptied v))
  | .record fields => .record (fields.map fun (l, v) => (l, emptied v))
  | v => v

/-- The selection, as a frame sees it: only if it's at the frame or one
step in, and with what's being typed only where it's typed. Elsewhere a
frame sees that something is typed, and no more; and a frame further up
sees nothing of it. -/
def seen (sel : Selection) (path : Path) (hint : Hint) : Option Selection :=
  if sel.path == path || sel.path.dropLast == path then
    some { sel with editing :=
      if sel.path == path && hint.listens sel.stage then sel.editing
      else sel.editing.map fun e => { text := "", caret := 0, picker := e.picker } }
  else none

/-- A frame's doc is built with its kids gathered as they're placed. -/
abbrev B := StateM (Array Kid)

variable (s : Shown) (errors : List Path)

/-- A kid a step in: a slot in the doc, for the frame drawn there. -/
def kid (step : Step) (hint : Hint := .value) (about : List Path := errors) : B Doc :=
  modifyGet fun kids => (.slot kids.size, kids.push { step := some step, hint, errors := about })

/-- A kid at the frame's own path. -/
def kidHere (hint : Hint) : B Doc :=
  modifyGet fun kids => (.slot kids.size, kids.push { step := none, hint, errors })

/-- A doc, as an occurrence. -/
def occ (path : Path) (kind : OccKind) (d : Doc) (cell : Option CellId := none) : Doc :=
  Doc.marked ⟨path, kind, kind == .value && errors.contains path, cell⟩ d

/-- The text being typed, with its caret. -/
def typing (e : Editing) (face : Face) : Doc :=
  .row [t (e.text.take e.caret).toString face, point .caret, t (e.text.drop e.caret).toString face]

/-- The editing at a path, if the selection is typing there in `stage`. -/
def editingAt (path : Path) (stage : Stage) : Option Editing :=
  match s.selection with
  | some sel => if sel.path == path && sel.stage == stage then sel.editing else none
  | none => none

/-- Whether a pending selection sits at a path. -/
def pendingAt (path : Path) : Bool :=
  match s.selection with
  | some sel => sel.path == path && sel.stage == .pending
  | none => false

/-- A hole: a place with no value, or the query being typed into it. -/
def hole (path : Path) : Doc :=
  match editingAt s path .pending with
  | some e => occ errors path .hole (.row [typing e .ink])
  | none =>
    match editingAt s path .edge with
    | some e => occ errors path .hole (.row [typing e .ink])
    | none => occ errors path .hole (dim "_")

/-- The layout a kind's records are drawn with, for a record: its def's
projection, if that's a layout, or a function that has given this record
one. -/
def projection (k : CellId) (v : Value) : Option Node :=
  match s.doc.lookup? s.library k with
  | some d =>
    if d.kind? != some Kinds.def_ then none
    else
      (d.field? Kinds.projection).bind fun p =>
        let source := match p with
          | .cell c => (s.doc.lookup? s.library c).getD p
          | _ => p
        (Node.read source).orElse fun _ =>
          (s.layouts.find? fun l => l.1 == source && l.2.1 == v).bind fun l => Node.read l.2.2
  | none => none

/-- Whether a cell is drawn open at a path: as the user set it, else open
when it has a definition of the document's that's more than a name, isn't
inside another cell's definition, and is the root, a list's element, an
evaluation's expression, or a field of a record with no kind. Elsewhere, as
a call's function or argument or a kind, it shows as its name. -/
def isOpen (path : Path) (c : CellId) (plain : Bool) : Bool :=
  match s.folds.find? (·.1 == path) with
  | some (_, closed) => !closed && (s.doc.lookup? s.library c).isSome
  | none =>
    let more := match s.doc.definition? c with
      | some (.record [(l, _)]) => l != Kinds.name
      | some _ => true
      | none => false
    more && !(path.contains .follow) &&
      match path.getLast? with
      | none | some (.element _) => true
      | some (.key l) => l == Kinds.expression || (l != Kinds.isa && plain)
      | some .follow => false

/-- A record's fields in the order raw shows them: named labels by name,
then the rest by id. -/
def ordered (fields : List (CellId × Value)) : List (CellId × Value) :=
  let named := fields.filter fun (l, _) => (s.doc.name? s.library l).isSome
  let unnamed := fields.filter fun (l, _) => (s.doc.name? s.library l).isNone
  (named.toArray.qsort (fun a b => s.doc.shown s.library a.1 < s.doc.shown s.library b.1)).toList ++ unnamed

/-- A number as it's typed: no trailing zeros, and no point if it's whole. -/
def number (x : Float) : String :=
  let text := toString x
  if text.contains '.' && !text.contains 'e' then
    let trimmed := (text.dropEndWhile (· == '0')).toString
    if trimmed.endsWith "." then (trimmed.dropEnd 1).toString else trimmed
  else text

/-- A container: on one line if it fits, else its parts one under another,
indented between its delimiters. -/
def container (open_ close : String) (flat stacked : List Doc) : Doc :=
  .alt (.row ([delim open_] ++ Doc.sep (dim ", ") flat ++ [delim close]))
    (.col [delim open_, .indent 2 (.col stacked), delim close])

/-- A message's first line and the indented lines that continue it, on one
line, cut short if it's long. -/
def brief (message : String) : String :=
  let line := match message.splitOn "\n" with
    | [] => ""
    | first :: rest =>
      let more := rest.takeWhile fun l => l.startsWith " " && !l.trimAscii.isEmpty
      " ".intercalate ((first :: more).map (·.trimAscii.toString))
  if line.length > 140 then (line.take 139).toString ++ "…" else line

/-- A value drawn as a line, being typed in or not: text in quotes, a
number as its digits. -/
def line (v : Value) (e : Option Editing) : Doc :=
  let content (face : Face) (shown : String) : Doc :=
    match e with
    | some e => typing e face
    | none => t shown face
  match v.text? with
  | some str => .row [t "\"" .string, content .string str, t "\"" .string]
  | none =>
    match v.u64? with
    | some n => content .number (toString n)
    | none =>
      match v.f64? with
      | some x => .row [content .number (number x), dim "f64"]
      | none => content .ink ""

/-- A cell: open, its definition in parentheses; closed, its name, or its
kind and short id. -/
def cell (path : Path) (c : CellId) (plain : Bool) : B Doc := do
  if isOpen s path c plain then
    return .row [delim "(", ← kid errors .follow, delim ")"]
  else
    match s.doc.name? s.library c with
    | some n => return t n .name
    | none =>
      match (s.doc.lookup? s.library c).bind (·.kind?) with
      | some k => return .row [delim "(", t (s.doc.shown s.library k) .name, dim (" " ++ c.short), delim ")"]
      | none => return dim c.short

/-- A list's elements, each a kid drawn as `hint` asks, with a place to
insert before each and after the last, and the hole of an element being
added. -/
def elements (path : Path) (items : List (Position × Value)) (hint : Hint := .value) : B (List Doc) := do
  -- The element being added, if the selection is pending in this list.
  let pending : Option Position :=
    match s.selection with
    | some sel =>
      if sel.stage == .pending && sel.path.dropLast == path then
        match sel.path.getLast? with
        | some (.element p) => if items.any (·.1 == p) then none else some p
        | _ => none
      else none
    | none => none
  -- Each position, and whether an element is there.
  let all : List (Position × Bool) :=
    match pending with
    | some p =>
      let before := items.filter fun (q, _) => Position.lt q p
      let after := items.filter fun (q, _) => !Position.lt q p
      before.map (fun (q, _) => (q, true)) ++ [(p, false)] ++ after.map fun (q, _) => (q, true)
    | none => items.map fun (q, _) => (q, true)
  let insertion (before after : Option Position) : Doc :=
    occ errors (path ++ [.element (Position.between before after)]) .insertion (point .ink)
  -- The hole of an element being added is its own place: no insertion
  -- point is drawn beside it.
  let rec go (prev : Option (Position × Bool)) : List (Position × Bool) → B (List Doc)
    | [] => return []
    | (p, there) :: rest => do
      let none_ : Doc := .row []
      let beside := !there || (prev.map (·.2)).getD false
      let point := if beside then none_ else insertion (prev.map (·.1)) (some p)
      let item ← kid errors (.element p) hint
      let last := if rest.isEmpty && there then insertion (some p) none else none_
      return .row [point, item, last] :: (← go (some (p, !there)) rest)
  if all.isEmpty then return [insertion none none]
  else go none all

def list (path : Path) (items : List (Position × Value)) : B Doc := do
  let parts ← elements s errors path items
  return container "[" "]" parts parts

/-- A field: its label, then its value beside it. -/
def field (path : Path) (label : CellId) (plain : Bool := false) : B Doc := do
  let at_ := path ++ [.key label]
  let name := occ errors at_ .label (t (s.doc.shown s.library label) .label) (some label)
  return .row [name, dim ": ", ← kid errors (.key label) (.value plain)]

/-- The label being typed for a new field, if the selection is adding one
to the record at a path: a kid at the record's own path. -/
def newLabel (path : Path) : B (List Doc) := do
  if (editingAt s path .label).isSome then return [← kidHere errors .label] else return []

/-- The field whose value is being given, if the selection is pending at a
field the record at a path doesn't have yet: its label, and the hole. -/
def pendingField (path : Path) (fields : List (CellId × Value)) : B (List Doc) := do
  match s.selection with
  | some sel =>
    if sel.stage == .pending && sel.path.dropLast == path then
      match sel.path.getLast? with
      | some (.key l) => if fields.any (·.1 == l) then return [] else return [← field s errors path l]
      | _ => return []
    else return []
  | none => return []

/-- A raw record: `{label: value, …}`, with a place at its end to add a
field. -/
def record (path : Path) (fields : List (CellId × Value)) : B Doc := do
  let shown ← (ordered s fields).mapM fun (l, _) => field s errors path l (plain := true)
  let adding := (← pendingField s errors path fields) ++ (← newLabel s errors path)
  let end_ := if adding.isEmpty then [occ errors path .fieldEnd (point .ink)] else []
  let parts := shown ++ adding
  let flat : Doc := .row ([delim "{"] ++ Doc.sep (dim ", ") parts ++ end_ ++ [delim "}"])
  -- Stacked, the place to add a field rides at the end of the last field's line.
  let lines : List Doc := match parts.reverse with
    | last :: before => before.reverse ++ [.row (last :: end_)]
    | [] => end_
  let stacked : Doc := .col [delim "{", .indent 2 (.col lines), delim "}"]
  return .alt flat stacked

/-- A record's name, typed in place: a kid. -/
def nameOf (missing : String) : B Doc := kid errors (.key Kinds.name) (.name missing)

/-- The fields a kind's records show: its definition's, in order. -/
def fieldsOf (k : CellId) : List CellId :=
  match (s.doc.lookup? s.library k).bind (·.field? Kinds.fields) with
  | some (.list items) => items.filterMap fun (_, v) => match v with | .cell c => some c | _ => none
  | _ => []

/-- A record of a kind: `kind name {fields}`, its kind's fields first, each
a hole where missing, then the rest. -/
def kinded (path : Path) (k : CellId) (fields : List (CellId × Value)) : B Doc := do
  let v := Value.record fields
  let declared := (fieldsOf s k).filter (· != Kinds.name)
  let hasName := (fieldsOf s k).contains Kinds.name || (v.field? Kinds.name).isSome
  let rest := (ordered s fields).filter fun (l, _) =>
    l != Kinds.isa && l != Kinds.name && !declared.contains l
  let slots ← declared.mapM fun l => field s errors path l
  let others ← rest.mapM fun (l, _) => field s errors path l
  let pending ← if declared.any (fun l => s.selection.any fun sel => sel.path == path ++ [.key l]) then pure []
    else pendingField s errors path fields
  let adding := pending ++ (← newLabel s errors path)
  let parts := slots ++ others ++ adding
  let name ← if hasName then pure [t " ", ← nameOf errors "name"] else pure []
  let head := [t (s.doc.shown s.library k) .name] ++ name
  let flat : Doc := .row (head ++ [delim " {"] ++ Doc.sep (dim ", ") parts ++ [delim "}"])
  let stacked : Doc := .col [.row (head ++ [delim " {"]), .indent 2 (.col parts), delim "}"]
  if parts.isEmpty then return .row head else return .alt flat stacked

/-- A notebook: its entries, a kid; one with no list of them, as a field. -/
def notebook (path : Path) (v : Value) : B Doc := do
  match v.field? Kinds.entries with
  | some (.list _) => kid errors (.key Kinds.entries) .entries
  | _ => return .row [t "notebook " .name, ← field s errors path Kinds.entries]

/-- A section: its name over its body, indented. -/
def section_ (v : Value) : B Doc := do
  let head : Doc := .row [dim "▾ ", ← nameOf errors "section"]
  match v.field? Kinds.sectionBody with
  | some (.list _) => return .col [head, .indent 2 (← kid errors (.key Kinds.sectionBody) .body)]
  | _ => return .col [head, .indent 2 (← kid errors (.key Kinds.sectionBody))]

/-- An evaluation: its expression, then what it gives. -/
def evaluation (path : Path) (outcome : Option Outcome) : B Doc := do
  let at_ := path ++ [.key Kinds.expression]
  let about := match outcome with
    | some (Outcome.failed _ (some rel)) => (at_ ++ rel) :: errors
    | _ => errors
  let expression ← kid errors (.key Kinds.expression) .value about
  let result : Doc :=
    match outcome with
    | some (.value shown type) =>
      if shown.isEmpty then .row [t type .dim] else .row [t shown .result, t (" : " ++ type) .dim]
    | some (.failed message _) => t (brief message) .error
    | none => dim "…"
  let marked := occ errors (path ++ [.key Kinds.evaluation]) .computed result
  let flat : Doc := .row [expression, dim " → ", marked]
  let stacked : Doc := .col [expression, .indent 2 (.row [dim "→ ", marked])]
  return .alt flat stacked

/-- A lambda: `name [params] → body`, with what it returns after the
parameters if it says, or is being told. -/
def lambda (path : Path) (v : Value) : B Doc := do
  let name ← nameOf errors "λ"
  let params ← kid errors (.key Kinds.params) .params
  let returnsPath := path ++ [.key Kinds.returns]
  let returns ←
    if (v.field? Kinds.returns).isSome || pendingAt s returnsPath then
      pure [dim " : ", ← kid errors (.key Kinds.returns)]
    else pure []
  let body ← kid errors (.key Kinds.body)
  let head := [name, t " ", params] ++ returns
  let flat : Doc := .row (head ++ [dim " → ", body])
  let stacked : Doc := .col [.row (head ++ [dim " →"]), .indent 2 body]
  return .alt flat stacked

/-- A call: the function, then its arguments by parameter; a function
written between two arguments goes between them. -/
def call (path : Path) (v : Value) : B Doc := do
  let fn := v.field? Kinds.function
  let params : List CellId :=
    match fn with
    | some (.cell c) =>
      match (s.doc.lookup? s.library c).bind (·.field? Kinds.params) with
      | some (.list items) => items.filterMap fun (_, p) => match p with | .cell c => some c | _ => none
      | _ => []
    | _ => []
  let symbol := match fn with
    | some (.cell c) => (Builtin.function? c).bind (·.symbol)
    | _ => none
  match symbol, params with
  | some sym, [a, b] =>
    let left ← kid errors (.key a)
    let right ← kid errors (.key b)
    let op := occ errors (path ++ [.key Kinds.function]) .value (dim (" " ++ sym ++ " "))
    return .row [delim "(", left, op, right, delim ")"]
  | _, _ =>
    let head ← kid errors (.key Kinds.function)
    let args ← params.mapM fun p => field s errors path p
    let extra : List (CellId × Value) := match v with
      | .record fields => (ordered s fields).filter fun (l, _) =>
          l != Kinds.isa && l != Kinds.function && !params.contains l
      | _ => []
    let others ← extra.mapM fun (l, _) => field s errors path l
    let pending ← if params.any (fun l => s.selection.any fun sel => sel.path == path ++ [.key l]) then pure []
      else match v with
        | .record fields => pendingField s errors path fields
        | _ => pure []
    let adding := pending ++ (← newLabel s errors path)
    let parts := args ++ others ++ adding
    let flat : Doc := .row ([head, delim " {"] ++ Doc.sep (dim ", ") parts ++ [delim "}"])
    let stacked : Doc := .col [.row [head, delim " {"], .indent 2 (.col parts), delim "}"]
    if parts.isEmpty then return .row [head, delim " {}"] else return .alt flat stacked

/-- A record, drawn by a layout: its parts are the record's own, at their
fields, so they're edited where they're drawn. -/
partial def layout : Node → B Doc
  | .row children => return .row (← children.mapM layout)
  | .column children => return .col (← children.mapM layout)
  | .indent child => return .indent 2 (← layout child)
  | .either children => do
    let drawn ← children.mapM layout
    return match drawn.reverse with
      | [] => .row []
      | last :: before => before.foldl (fun rest d => .alt d rest) last
  | .words content => return t content
  | .faint content => return dim content
  | .part field => kid errors (.key field)

/-- A value, by the first form that takes it. -/
def drawn (path : Path) (v : Value) (plain : Bool) (deep : Deep) : B Doc := do
  match v with
  | .cell c => cell s errors path c plain
  | .blob b => return t (GidText.hex b) .number
  | .list items => list s errors path items
  | .record fields =>
    if (v.text?.isSome || v.u64?.isSome || v.f64?.isSome) && fields.length == 2 then return line v none
    else if v.literal? Kinds.bool == some [1] then return t "true" .name
    else if v.literal? Kinds.bool == some [0] then return t "false" .name
    else
      match v.kind? with
      | some k =>
        if k == Kinds.notebook then notebook s errors path v
        else if k == Kinds.section_ then section_ errors v
        else if k == Kinds.evaluation then evaluation errors path deep.outcome
        else if k == Kinds.lambda then lambda s errors path v
        else if k == Kinds.call then call s errors path v
        else if k == Kinds.valueWrapper then
          return .row [← nameOf errors "name", t " = ", ← kid errors (.key Kinds.value)]
        else
          match deep.node with
          | some node => layout errors node
          | none => kinded s errors path k fields
      | none => record s errors path fields

/-- A value at a path, or the hole where there is none. -/
def value (path : Path) (v? : Option Value) (plain : Bool) (deep : Deep) : B Doc := do
  match v? with
  | none => return hole s errors path
  | some v =>
    let cell := match v with
      | .cell c => some c
      | _ => none
    -- A picker over a value shows its query in the value's place.
    match editingAt s path .edge with
    | some e =>
      if e.picker then return occ errors path .value (.row [typing e .ink]) cell
      else return occ errors path .value (line v (some e)) cell
    | none => return occ errors path .value (← drawn s errors path v plain deep) cell

/-- A record's name, at its own path: typed in place; without one,
`missing` in its place. -/
def nameShape (path : Path) (v? : Option Value) (missing : String) : Doc :=
  let bare (e : Option Editing) (shown : String) : Doc :=
    match e with
    | some e => typing e .name
    | none => t shown .name
  match editingAt s path .edge, editingAt s path .pending with
  | some e, _ => occ errors path .value (bare (some e) "")
  | _, some e => occ errors path .hole (bare (some e) "")
  | none, none =>
    match v?.bind Value.text? with
    | some n => if n.isEmpty then occ errors path .value (dim missing) else occ errors path .value (bare none n)
    | none => occ errors path .hole (dim missing)

/-- A parameter: its name, and its definition, a kid, of which its type
is drawn. -/
def paramShape (path : Path) (v? : Option Value) (deep : Deep) : B Doc := do
  match v?, editingAt s path .edge with
  | some (.cell c), none =>
    return occ errors path .value (.row [t (s.doc.shown s.library c) .name, ← kid errors .follow .paramType]) (some c)
  | _, _ => value s errors path v? false deep

/-- A parameter's definition, as its type: drawn if it has one, or one is
being given. -/
def paramTypeShape (path : Path) (v? : Option Value) : B Doc := do
  if ((v?.bind (·.field? Kinds.type_)).isSome || pendingAt s (path ++ [.key Kinds.type_])) then
    return .row [dim ": ", ← kid errors (.key Kinds.type_)]
  else return .row []

/-- A lambda's parameters: each drawn as a parameter, unless the list is
being replaced. -/
def paramsShape (path : Path) (v? : Option Value) (deep : Deep) : B Doc := do
  match v?, editingAt s path .edge with
  | some (.list items), none =>
    let parts ← elements s errors path items .param
    return occ errors path .value (container "[" "]" parts parts)
  | _, _ => value s errors path v? false deep

/-- A notebook's entries, one under another, numbered. -/
def entriesShape (path : Path) (v? : Option Value) (deep : Deep) : B Doc := do
  match v? with
  | some (.list items) =>
    let parts ← elements s errors path items
    let numbered := (List.range parts.length).zip parts |>.map fun (i, d) =>
      (.row [dim (toString (i + 1) ++ (if i < 9 then "  " else " ")), d] : Doc)
    return .col (Doc.sep (t "") numbered)
  | _ => value s errors path v? false deep

/-- A section's body, one under another. -/
def bodyShape (path : Path) (v? : Option Value) (deep : Deep) : B Doc := do
  match v? with
  | some (.list items) => return .col (← elements s errors path items)
  | _ => value s errors path v? false deep

/-- The label being typed for a new field. -/
def labelShape (path : Path) : Doc :=
  match editingAt s path .label with
  | some e => .row [occ errors path .fieldEnd (typing e .label), dim ": ", dim "_"]
  | none => .row []

/-- The path of the root notebook's entries, and of an entry at a position. -/
def entriesPath : Path := [.key Kinds.entries]

def entryAt (p : Position) : Path := entriesPath ++ [.element p]

/-- The hole of an entry being added before the entry at a path, or at the
entries' end for their path: the selection is pending and anchored there. -/
def adding (at_ : Path) : Option Path :=
  match s.selection with
  | some sel => if sel.stage == .pending && sel.anchor == some at_ then some sel.path else none
  | none => none

/-- The hole of an entry being added, as a kid: the step to it is its
path's last. -/
def addingKid (hole : Path) : B Doc :=
  match hole.getLast? with
  | some step => kid errors step
  | none => return .row []

/-- A part of the document that's an entry of the root notebook: the place
to add an entry before it, and the entry. An entry being added before it
is a line of its own, and takes that place. -/
def entryShape (p : Position) : B Doc := do
  let path := entryAt p
  match adding s path with
  | some hole =>
    let h ← addingKid errors hole
    let item ← kid errors (.element p)
    return .col [h, t "", item, t ""]
  | none =>
    let point := occ errors path .entryPoint (point .ink)
    let item ← kid errors (.element p)
    return .col [.row [point, item], t ""]

/-- The end of the root notebook's entries: the place to add one after the
last, or the one being added there. -/
def endShape : B Doc :=
  match adding s entriesPath with
  | some hole => addingKid errors hole
  | none => return occ errors entriesPath .entryPoint (point .ink)

end Display

open Display in
/-- A frame's doc and kids: what's drawn at a path for a value, as its hint
asks. `s` is what the frame sees, and `v` its value without what's inside
its elements and fields. -/
def Display.shape (s : Shown) (path : Path) (hint : Hint) (errors : List Path) (deep : Deep) (v : Option Value) :
    Doc × List Kid :=
  let built : B Doc :=
    match hint with
    | .value plain => value s errors path v plain deep
    | .name missing => pure (nameShape s errors path v missing)
    | .param => paramShape s errors path v deep
    | .paramType => paramTypeShape s errors path v
    | .params => paramsShape s errors path v deep
    | .entries => entriesShape s errors path v deep
    | .body => bodyShape s errors path v deep
    | .label => pure (labelShape s errors path)
    | .entry p => entryShape s errors p
    | .end_ => endShape s errors
  let (doc, kids) := built.run #[]
  (doc, kids.toList)

namespace Display

/-- What a frame reads of its whole value: what its evaluation gave, and
the layout its kind draws it with. -/
def deepOf (s : Shown) (v : Option Value) : Deep :=
  match v with
  | some v =>
    match v.kind? with
    | some k =>
      if k == Kinds.evaluation then
        { outcome := (v.field? Kinds.expression).bind fun e => (s.results.find? (·.1 == e)).map (·.2) }
      else if k == Kinds.notebook || k == Kinds.section_ || k == Kinds.lambda || k == Kinds.call ||
          k == Kinds.valueWrapper then {}
      else { node := projection s k v }
    | none => {}
  | none => {}

/-- A kid's seed: its path a step on, and its value a step in; through a
cell, the cell's definition. -/
def Seed.kid (s : Shown) (seed : Seed) (k : Kid) : Seed :=
  { path := seed.path ++ k.step.toList, hint := k.hint, errors := k.errors,
    value := match k.step with
      | none => seed.value
      | some .follow =>
        match seed.value with
        | some (.cell c) => s.doc.lookup? s.library c
        | _ => none
      | some step => seed.value.bind (·.step? step) }

/-- What a frame sees of the selection. -/
def sees (s : Shown) (seed : Seed) : Option Selection :=
  s.selection.bind fun sel => seen sel seed.path seed.hint

/-- A frame's doc and kids, for a seed: drawn from the selection as it's
seen there, and the value without what's inside it. -/
def framed (s : Shown) (seed : Seed) : Doc × List Kid :=
  shape { s with selection := sees s seed } seed.path seed.hint seed.errors (deepOf s seed.value)
    (seed.value.map shallow)

/-- The frames of a seed: its own, and its kids', as deep as `fuel`. -/
def grow (s : Shown) : Nat → Seed → Deui.Fit.Frame Span
  | 0, _ => .node (dim "…") []
  | fuel + 1, seed =>
    let made := framed s seed
    .node made.1 (made.2.map fun k => grow s fuel (seed.kid s k))

/-- How deep frames go before they stop: deeper than a document's values. -/
def depth : Nat := 1000

/-- Every evaluation's expression in a value, after those gathered. -/
partial def expressionsInto (found : Array Value) : Value → Array Value
  | .cell _ | .blob _ => found
  | .list items => items.foldl (fun found (_, v) => expressionsInto found v) found
  | v@(.record fields) =>
    let found := if v.kind? == some Kinds.evaluation then
        match v.field? Kinds.expression with
        | some e => found.push e
        | none => found
      else found
    fields.foldl (fun found (_, w) => expressionsInto found w) found

/-- Every evaluation's expression in a value. -/
def expressionsIn (v : Value) : List Value := (expressionsInto #[] v).toList

/-- Every cell a value mentions, after those gathered. -/
partial def mentionsInto (found : Array CellId) : Value → Array CellId
  | .cell c => found.push c
  | .blob _ => found
  | .list items => items.foldl (fun found (_, v) => mentionsInto found v) found
  | .record fields => fields.foldl (fun found (l, v) => mentionsInto (found.push l) v) found

/-- The definitions cells reach, each once, and every cell asked for on the
way, defined or not: what's asked is all the answer depends on. `look`
gives a cell's definition; `todo` are the cells still to ask for, `seen`
those asked, `found` the definitions. It stops when `fuel` runs out, which
a document's cells don't reach. -/
def reach (look : CellId → Option Value) :
    Nat → List CellId → List CellId → List (CellId × Value) → List CellId × List (CellId × Value)
  | 0, _, seen, found => (seen, found)
  | _ + 1, [], seen, found => (seen, found)
  | fuel + 1, c :: rest, seen, found =>
    if seen.contains c then reach look fuel rest seen found
    else match look c with
      | some v => reach look fuel ((mentionsInto #[] v).toList ++ rest) (c :: seen) ((c, v) :: found)
      | none => reach look fuel rest (c :: seen) found

/-- What was asked stays asked. -/
theorem reach_seen (look : CellId → Option Value) (fuel : Nat) (todo seen : List CellId)
    (found : List (CellId × Value)) (x : CellId) (h : x ∈ seen) : x ∈ (reach look fuel todo seen found).1 := by
  induction fuel generalizing todo seen found with
  | zero => exact h
  | succ fuel ih =>
    cases todo with
    | nil => exact h
    | cons c rest =>
      simp only [reach]
      split
      · exact ih _ _ _ h
      · split
        · exact ih _ _ _ (List.mem_cons_of_mem _ h)
        · exact ih _ _ _ (List.mem_cons_of_mem _ h)

/-- Two tables of definitions that agree on every cell asked for give the
same: the cells asked for are all that's read. -/
theorem reach_agree (look look' : CellId → Option Value) (fuel : Nat) (todo seen : List CellId)
    (found : List (CellId × Value))
    (h : ∀ x ∈ (reach look fuel todo seen found).1, x ∉ seen → look' x = look x) :
    reach look' fuel todo seen found = reach look fuel todo seen found := by
  induction fuel generalizing todo seen found with
  | zero => rfl
  | succ fuel ih =>
    cases todo with
    | nil => rfl
    | cons c rest =>
      simp only [reach] at h ⊢
      by_cases hc : seen.contains c = true
      · simp only [hc, ite_true] at h ⊢
        exact ih _ _ _ h
      · simp only [hc] at h ⊢
        have hnot : c ∉ seen := fun hm => hc (by simpa using hm)
        -- The cell asked for here is among those asked, and wasn't before.
        have agree : look' c = look c := by
          cases hl : look c with
          | some v =>
            rw [hl] at h
            have := h c (reach_seen look fuel _ _ _ c (List.mem_cons_self ..)) hnot
            rw [this, hl]
          | none =>
            rw [hl] at h
            have := h c (reach_seen look fuel _ _ _ c (List.mem_cons_self ..)) hnot
            rw [this, hl]
        rw [agree]
        cases hl : look c with
        | some v =>
          rw [hl] at h
          exact ih _ _ _ fun x hx hn => h x hx fun hs => hn (List.mem_cons_of_mem _ hs)
        | none =>
          rw [hl] at h
          exact ih _ _ _ fun x hx hn => h x hx fun hs => hn (List.mem_cons_of_mem _ hs)

/-- What a part of the document is of: an entry of the root notebook; the
end of its entries, where one is added after the last; or the whole root. -/
inductive Entry where
  | entry (position : Position) (value : Value)
  | end_
  | whole (root : Option Value)
  deriving DecidableEq, Inhabited

/-- The root notebook's entries, if the root is one. -/
def notebookEntries? (root : Option Value) : Option (List (Position × Value)) :=
  match root with
  | some v =>
    if v.kind? == some Kinds.notebook then
      match v.field? Kinds.entries with
      | some (.list items) => some items
      | _ => none
    else none
  | none => none

/-- An edit of a part: a new one, or its value written at a path within it. -/
inductive Entry.Edit where
  | replace (e : Entry)
  | write (rel : List Step) (value : Option Value)

def Entry.Edit.apply : Entry.Edit → Entry → Entry
  | .replace e, _ => e
  | .write rel w, .entry p v => .entry p (v.written rel w)
  | .write rel w, .whole root => .whole (root.map fun v => v.written rel w)
  | .write _ _, .end_ => .end_

abbrev Entry.edits : Deui.EditStructure := ⟨Entry, Entry.Edit, Entry.Edit.apply⟩

/-- The document's parts: the root notebook's entries and their end, or the
whole root. -/
def entries (root : Option Value) : List Entry :=
  match notebookEntries? root with
  | some items => items.map (fun (p, w) => Entry.entry p w) ++ [.end_]
  | none => [.whole root]

/-- A part of the document, with what it reaches: the definitions, the
evaluations' expressions in it, whether any kind in it is drawn by a
function, and every cell that was asked for to find these out. -/
structure Item where
  entry : Entry
  reached : Shared (List (CellId × Value))
  expressions : List Value
  functions : Bool
  reads : List CellId
  deriving DecidableEq, Inhabited

/-- Whether any of the definitions is a def whose projection is a function:
what's drawn then depends on what the functions gave. -/
def anyFunctions (reached : List (CellId × Value)) : Bool :=
  reached.any fun (_, d) =>
    d.kind? == some Kinds.def_ &&
      match d.field? Kinds.projection with
      | some (.cell c) => ((reached.find? (·.1 == c)).map fun (_, p) => (Node.read p).isNone).getD false
      | some p => (Node.read p).isNone
      | none => false

/-- How far reaching goes before it stops: further than a document's cells. -/
def reachFuel : Nat := 1000000

/-- The value a part is of, if it has one. -/
def Entry.value? : Entry → Option Value
  | .entry _ v => some v
  | .whole root => root
  | .end_ => Option.none

/-- A part with what a value in it reaches, by a table of definitions. -/
def itemOf (look : CellId → Option Value) (e : Entry) (v : Value) : Item :=
  ⟨e, ⟨(reach look reachFuel (mentionsInto #[] v).toList [] []).2⟩, expressionsIn v,
    anyFunctions (reach look reachFuel (mentionsInto #[] v).toList [] []).2,
    (reach look reachFuel (mentionsInto #[] v).toList [] []).1⟩

/-- A part with what it reaches, by a table of definitions. -/
def item (look : CellId → Option Value) (e : Entry) : Item :=
  match e.value? with
  | some v => itemOf look e v
  | none => ⟨e, ⟨[]⟩, [], false, []⟩

/-- An item is of the part it was made from. -/
theorem item_entry (look : CellId → Option Value) (e : Entry) : (item look e).entry = e := by
  unfold item
  cases e.value? <;> rfl

/-- A part is the same by two tables that agree on the cells it asked for. -/
theorem item_agree (look look' : CellId → Option Value) (e : Entry)
    (h : ∀ x ∈ (item look e).reads, look' x = look x) : item look' e = item look e := by
  unfold item at h ⊢
  cases hv : e.value? with
  | none => rfl
  | some v =>
    rw [hv] at h
    have hr := reach_agree look look' reachFuel (mentionsInto #[] v).toList [] [] fun x hx _ => h x hx
    simp only [itemOf, hr]

/-- All a part's layout depends on: the part with what it reaches, and what
of the editor's state it's drawn with. -/
structure Input where
  item : Item
  selection : Option Selection
  folds : List (Path × Bool)
  results : List (Value × Outcome)
  layouts : Shared (List (Value × Value × Value))
  /-- The definition of the label of a field the selection is giving a
  value, which the part may not reach yet. -/
  named : List (CellId × Value)
  ribbon : Nat
  deriving DecidableEq

/-- What a part's frames are grown from. -/
def partSeed : Entry → Seed
  | .whole root => { path := [], value := root }
  | .entry p v => { path := entriesPath, hint := .entry p, value := some (.list [(p, v)]) }
  | .end_ => { path := entriesPath, hint := .end_, value := some (.list []) }

/-- What a part is drawn from, as what the projection is of. -/
def Input.shown (i : Input) : Shown :=
  { doc := { root := none, cells := Std.TreeMap.ofList (i.named ++ i.item.reached.val) }, library := Builtin.library,
    selection := i.selection, folds := i.folds, results := i.results, layouts := i.layouts.val }

/-- A part's frames. -/
def frame (i : Input) : Deui.Fit.Frame Span := grow i.shown depth (partSeed i.item.entry)

/-- A part, laid out from nothing: its lines. -/
def part (i : Input) : List Line :=
  Deui.Text.lines (Deui.Fit.Frame.lay measure i.ribbon (frame i) 0 0).tokens

/-- Whether a selection covers an occurrence: it, and what's drawn inside
it; not the label of the field it's the value of. -/
def covers (sel : Selection) (o : Occ) : Bool :=
  match sel.stage with
  | .label => o.kind == .fieldEnd && o.path == sel.path
  | _ => sel.path.isPrefixOf o.path && !(o.kind == .label && o.path == sel.path) && o.kind != .fieldEnd

/-- Whether a selection changes what's drawn: one being typed in, and one
where there's no value yet, which has a hole or a label drawn for it. A
selection that rests on a value is washed over what's drawn, and changes
none of it. -/
def drawnSelection (sel : Selection) : Bool := sel.stage != .edge || sel.editing.isSome

/-- What of the editor's state the parts are drawn with: of the selection,
only one that changes what's drawn. -/
structure Seen where
  selection : Option Selection := none
  folds : List (Path × Bool) := []
  results : List (Value × Outcome) := []
  layouts : Shared (List (Value × Value × Value)) := ⟨[]⟩
  /-- The definition of the label of a field the selection is giving a
  value. -/
  named : List (CellId × Value) := []
  ribbon : Nat := 80
  /-- The paths of the values evaluations' errors are about, for the view
  drawn by derivative, which a part is given them by. -/
  failing : List Path := []
  deriving DecidableEq

namespace Item

/-- Whether a path is an entry's, or under it. -/
def under (p : Position) : Path → Bool
  | .key k :: .element q :: _ => k == Kinds.entries && q == p
  | _ => false

/-- Whether a path is an entry's, or above it. -/
def over (p : Position) : Path → Bool
  | [] => true
  | [.key k] => k == Kinds.entries
  | [.key k, .element q] => k == Kinds.entries && q == p
  | _ => false

/-- Whether a selection is in a part, or the part in it, or it's of an
entry being added that the part draws. -/
def touches (i : Item) (sel : Selection) : Bool :=
  match i.entry with
  | .whole _ => true
  | .entry p _ =>
    under p sel.path || over p sel.path ||
      match sel.anchor with
      | some [.key k, .element q] => k == Kinds.entries && q == p
      | _ => false
  | .end_ =>
    (match sel.anchor with
      | some [.key k] => k == Kinds.entries
      | _ => false) ||
    match sel.path with
    | [] => true
    | [.key k] => k == Kinds.entries
    | _ => false

/-- What of each thing the editor's state holds a part is drawn with: the
selection if it's in the part, the folds in it, the results of its
evaluations, and what functions gave if it has kinds they draw. -/
def selection (i : Item) (s : Option Selection) : Option Selection := s.filter i.touches

def folds (i : Item) (fs : List (Path × Bool)) : List (Path × Bool) :=
  match i.entry with
  | .whole _ => fs
  | .entry p _ => fs.filter fun fold => (entryAt p).isPrefixOf fold.1
  | .end_ => []

def results (i : Item) (rs : List (Value × Outcome)) : List (Value × Outcome) :=
  if i.expressions.isEmpty then [] else rs.filter fun r => i.expressions.contains r.1

def layouts (i : Item) (ls : Shared (List (Value × Value × Value))) : Shared (List (Value × Value × Value)) :=
  if i.functions then ls else ⟨[]⟩

/-- The selection, with the definition it names, if the selection is in
the part. -/
def naming (i : Item) (sn : Option Selection × List (CellId × Value)) :
    Option Selection × List (CellId × Value) :=
  match i.selection sn.1 with
  | some sel => (some sel, sn.2)
  | none => (none, [])

end Item

/-- A part's input: the part, with what of the editor's state it's drawn
with. -/
def input (c : Seen) (i : Item) : Input :=
  { item := i, selection := (i.naming (c.selection, c.named)).1, folds := i.folds c.folds,
    results := i.results c.results, layouts := i.layouts c.layouts, named := (i.naming (c.selection, c.named)).2,
    ribbon := c.ribbon }

/-- Whether one thing a part is drawn with differs, between two states:
not if the two hold the same thing, nor if what the part takes of each is
the same. -/
def differs {α β : Type} [DecidableEq α] [DecidableEq β] (g : α → β) (a a' : α) : Bool :=
  !(equal a a' || decide (g a = g a'))

theorem same_of_not_differs {α β : Type} [DecidableEq α] [DecidableEq β] (g : α → β) (a a' : α)
    (h : differs g a a' = false) : g a = g a' := by
  simp only [differs, Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · rw [equal_sound a a' h]
  · exact h

/-- Whether a change of the editor's state, from `c` to `c'`, touches a
part: whether anything the part is drawn with differs. A selection that
moves touches the parts it leaves and enters, and no other. -/
def touched (c c' : Seen) (i : Item) : Bool :=
  c.ribbon != c'.ribbon || differs i.naming (c.selection, c.named) (c'.selection, c'.named) ||
    differs i.folds c.folds c'.folds ||
    differs i.results c.results c'.results || differs i.layouts c.layouts c'.layouts

/-- Whether a change of the editor's state leaves all the parts are drawn
with as it was: then no part is touched, and none is asked. -/
def still (c c' : Seen) : Bool :=
  c.ribbon == c'.ribbon && equal c.selection c'.selection && equal c.folds c'.folds &&
    equal c.results c'.results && equal c.layouts c'.layouts && equal c.named c'.named &&
    equal c.failing c'.failing

/-- A change that's still leaves the state the parts are drawn with as it
was. -/
theorem eq_of_still (c c' : Seen) (h : still c c' = true) : c' = c := by
  simp only [still, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hr, hs⟩, hf⟩, hres⟩, hl⟩, hn⟩, hfl⟩ := h
  cases c; cases c'
  simp only [Seen.mk.injEq]
  exact ⟨(equal_sound _ _ hs).symm, (equal_sound _ _ hf).symm, (equal_sound _ _ hres).symm,
    (equal_sound _ _ hl).symm, (equal_sound _ _ hn).symm, hr.symm, (equal_sound _ _ hfl).symm⟩

theorem not_touched_of_still (c c' : Seen) (h : still c c' = true) (i : Item) : touched c c' i = false := by
  rw [eq_of_still c c' h]
  simp [touched, differs, equal_refl]

/-- A part that a change doesn't touch has the input it had. -/
theorem input_of_not_touched (c c' : Seen) (i : Item) (h : touched c c' i = false) : input c' i = input c i := by
  simp only [touched, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at h
  obtain ⟨⟨⟨⟨hr, hs⟩, hf⟩, hres⟩, hl⟩ := h
  simp only [input, hr, same_of_not_differs _ _ _ hs, same_of_not_differs _ _ _ hf,
    same_of_not_differs _ _ _ hres, same_of_not_differs _ _ _ hl]

/-- A document's parts, laid out: all of it, worked out from nothing. -/
def lines (d : Document) (c : Seen) : List (List Line) :=
  (((entries d.root).map (item fun x => d.cells[x]?)).map (input c)).map part

end Display

end Progred
