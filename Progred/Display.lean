import Std.Data.TreeSet
import Progred.Builtin
import Progred.GidText
import Progred.Layout

/-!
The projection: a document as a `Doc`, with every drawn thing an
occurrence, so a selection, an arrow key or a click finds its place. A
value is drawn by the first form that takes it: a literal, the form of its
kind (notebook, section, evaluation, lambda, call, value wrapper), the
generic `kind name {fields}`, else raw: `(cell)`, `[list]`, `{record}`,
`0xblob`.
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
  deriving DecidableEq, Inhabited

inductive OccKind where
  /-- A value, where it is drawn. -/
  | value
  /-- A place for a value, with none. -/
  | hole
  /-- A place between a list's elements; its path is where a new element
  would go. -/
  | insertion
  /-- The end of a record, where a field is added; its path is the record's. -/
  | fieldEnd
  /-- A field's label; its path is the field's value's. -/
  | label
  /-- A result: computed, not stored. -/
  | computed
  deriving DecidableEq, Inhabited, Repr

structure Occ where
  path : Path
  kind : OccKind
  /-- Whether an evaluation's error is about this value. -/
  failed : Bool := false
  /-- The cell it is: a value that's a cell, or a label. -/
  cell : Option CellId := none
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

/-- What drawing gathers: the occurrences, and the paths evaluations'
errors are about, noted before what's there is drawn. -/
structure Drawn where
  occs : Array Occ := #[]
  errors : List Path := []
  /-- Whether the value about to be drawn is a field of a record with no
  kind, where a cell opens. -/
  inPlain : Bool := false

abbrev M := StateM Drawn

/-- A doc, marked as an occurrence. -/
def occ (path : Path) (kind : OccKind) (d : Doc) (cell : Option CellId := none) : M Doc := do
  modify fun st => { st with occs := st.occs.push ⟨path, kind, kind == .value && st.errors.contains path, cell⟩ }
  return .mark (← get).occs.size d

def t (s : String) (face : Face := .ink) : Doc := .text s face
def delim (s : String) : Doc := .text s .delimiter
def dim (s : String) : Doc := .text s .dim

/-- The text being typed, with its caret. -/
def typing (e : Editing) (face : Face) : Doc :=
  .row [.text (e.text.take e.caret).toString face, .point .caret, .text (e.text.drop e.caret).toString face]

variable (s : Shown)

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
def hole (path : Path) : M Doc :=
  match editingAt s path .pending with
  | some e => occ path .hole (.row [typing e .ink])
  | none =>
    match editingAt s path .edge with
    | some e => occ path .hole (.row [typing e .ink])
    | none => occ path .hole (dim "_")

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

mutual

/-- A value at a path, or the hole where there is none. -/
partial def value (path : Path) (v? : Option Value) : M Doc := do
  let plain ← modifyGet fun st => (st.inPlain, { st with inPlain := false })
  match v? with
  | none => hole s path
  | some v =>
    let cell := match v with
      | .cell c => some c
      | _ => none
    -- A picker over a value shows its query in the value's place.
    match editingAt s path .edge with
    | some e =>
      if e.picker then occ path .value (.row [typing e .ink]) cell
      else
        let inner ← line path v (some e)
        occ path .value inner cell
    | none =>
      let inner ← drawn path v plain
      occ path .value inner cell

/-- A value drawn as a line, being typed in or not: text in quotes, a
number as its digits. -/
partial def line (_path : Path) (v : Value) (e : Option Editing) : M Doc := do
  let content (face : Face) (shown : String) : Doc :=
    match e with
    | some e => typing e face
    | none => .text shown face
  match v.text? with
  | some str => return .row [.text "\"" .string, content .string str, .text "\"" .string]
  | none =>
    match v.u64? with
    | some n => return content .number (toString n)
    | none =>
      match v.f64? with
      | some x => return .row [content .number (number x), dim "f64"]
      | none => return content .ink ""

partial def drawn (path : Path) (v : Value) (plain : Bool) : M Doc := do
  match v with
  | .cell c => cell path c plain
  | .blob b => return .text (GidText.hex b) .number
  | .list items => list path items
  | .record fields =>
    if (v.text?.isSome || v.u64?.isSome || v.f64?.isSome) && fields.length == 2 then line path v none
    else if v.literal? Kinds.bool == some [1] then return t "true" .name
    else if v.literal? Kinds.bool == some [0] then return t "false" .name
    else
      match v.kind? with
      | some k =>
        if k == Kinds.notebook then notebook path v
        else if k == Kinds.section_ then section_ path v
        else if k == Kinds.evaluation then evaluation path v
        else if k == Kinds.lambda then lambda path v
        else if k == Kinds.call then call path v
        else if k == Kinds.valueWrapper then
          return .row [← nameOf path v "name", t " = ", ← value (path ++ [.key Kinds.value]) (v.field? Kinds.value)]
        else
          match projection s k v with
          | some node => layout path v node
          | none => kinded path k fields
      | none => record path fields

/-- A record, drawn by a layout: its parts are the record's own, at their
fields, so they're edited where they're drawn. -/
partial def layout (path : Path) (v : Value) : Node → M Doc
  | .row children => return .row (← children.mapM (layout path v))
  | .column children => return .col (← children.mapM (layout path v))
  | .indent child => return .indent 2 (← layout path v child)
  | .either children => do
    let drawn ← children.mapM (layout path v)
    return match drawn.reverse with
      | [] => .row []
      | last :: before => before.foldl (fun rest d => .alt d rest) last
  | .words content => return t content
  | .faint content => return dim content
  | .part field => value (path ++ [.key field]) (v.field? field)

/-- A cell: open, its definition in parentheses; closed, its name, or its
kind and short id. -/
partial def cell (path : Path) (c : CellId) (plain : Bool) : M Doc := do
  if isOpen s path c plain then
    let inner ← value (path ++ [.follow]) (s.doc.lookup? s.library c)
    return .row [delim "(", inner, delim ")"]
  else
    match s.doc.name? s.library c with
    | some n => return t n .name
    | none =>
      match (s.doc.lookup? s.library c).bind (·.kind?) with
      | some k => return .row [delim "(", t (s.doc.shown s.library k) .name, dim (" " ++ c.short), delim ")"]
      | none => return dim c.short

/-- A list's elements, each drawn by `draw`, with a place to insert before
each and after the last, and the hole of an element being added. -/
partial def elements (path : Path) (items : List (Position × Value)) (draw : Path → Option Value → M Doc) :
    M (List Doc) := do
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
  let all : List (Position × Option Value) :=
    match pending with
    | some p =>
      let before := items.filter fun (q, _) => Position.lt q p
      let after := items.filter fun (q, _) => !Position.lt q p
      before.map (fun (q, v) => (q, some v)) ++ [(p, none)] ++ after.map fun (q, v) => (q, some v)
    | none => items.map fun (q, v) => (q, some v)
  let positions := all.map (·.1)
  let insertion (before after : Option Position) : M Doc :=
    occ (path ++ [.element (Position.between before after)]) .insertion (.point .ink)
  -- The hole of an element being added is its own place: no insertion
  -- point is drawn beside it.
  let rec go (prev : Option (Position × Bool)) : List (Position × Option Value) → M (List Doc)
    | [] => return []
    | (p, v) :: rest => do
      let none_ := Doc.row []
      let beside := v.isNone || (prev.map (·.2)).getD false
      let point ← if beside then pure none_ else insertion (prev.map (·.1)) (some p)
      let item ← draw (path ++ [.element p]) v
      let last ← if rest.isEmpty && v.isSome then insertion (some p) none else pure none_
      return .row [point, item, last] :: (← go (some (p, v.isNone)) rest)
  if all.isEmpty then return [← insertion none none]
  else
    let _ := positions
    go none all

partial def list (path : Path) (items : List (Position × Value)) : M Doc := do
  let parts ← elements path items value
  return container "[" "]" parts parts

/-- A field: its label, then its value beside it, or below it indented. -/
partial def field (path : Path) (label : CellId) (v : Option Value) (plain : Bool := false) : M Doc := do
  let at_ := path ++ [.key label]
  let name ← occ at_ .label (t (s.doc.shown s.library label) .label) (some label)
  if plain then modify fun st => { st with inPlain := true }
  let inner ← value at_ v
  return .row [name, dim ": ", inner]

/-- The label being typed for a new field, if the selection is adding one
to the record at a path. -/
partial def newLabel (path : Path) : M (List Doc) := do
  match editingAt s path .label with
  | some e => return [.row [← occ path .fieldEnd (typing e .label), dim ": ", dim "_"]]
  | none => return []

/-- A raw record: `{label: value, …}`, with a place at its end to add a
field. -/
partial def record (path : Path) (fields : List (CellId × Value)) : M Doc := do
  let shown ← (ordered s fields).mapM fun (l, v) => field path l (some v) (plain := true)
  let adding ← newLabel path
  let end_ ← if adding.isEmpty then pure [← occ path .fieldEnd (.point .ink)] else pure []
  let parts := shown ++ adding
  let flat := Doc.row ([delim "{"] ++ Doc.sep (dim ", ") parts ++ end_ ++ [delim "}"])
  -- Stacked, the place to add a field rides at the end of the last field's line.
  let lines := match parts.reverse with
    | last :: before => before.reverse ++ [Doc.row (last :: end_)]
    | [] => end_
  let stacked := Doc.col [delim "{", .indent 2 (.col lines), delim "}"]
  return .alt flat stacked

/-- A record's name, typed in place; without one, `missing` in its place. -/
partial def nameOf (path : Path) (v : Value) (missing : String) : M Doc := do
  let at_ := path ++ [.key Kinds.name]
  let bare (e : Option Editing) (shown : String) : Doc :=
    match e with
    | some e => typing e .name
    | none => .text shown .name
  match editingAt s at_ .edge, editingAt s at_ .pending with
  | some e, _ => occ at_ .value (bare (some e) "")
  | _, some e => occ at_ .hole (bare (some e) "")
  | none, none =>
    match (v.field? Kinds.name).bind Value.text? with
    | some n => if n.isEmpty then occ at_ .value (dim missing) else occ at_ .value (bare none n)
    | none => occ at_ .hole (dim missing)

/-- The fields a kind's records show: its definition's, in order. -/
partial def fieldsOf (k : CellId) : List CellId :=
  match (s.doc.lookup? s.library k).bind (·.field? Kinds.fields) with
  | some (.list items) => items.filterMap fun (_, v) => match v with | .cell c => some c | _ => none
  | _ => []

/-- A record of a kind: `kind name {fields}`, its kind's fields first, each
a hole where missing, then the rest. -/
partial def kinded (path : Path) (k : CellId) (fields : List (CellId × Value)) : M Doc := do
  let v := Value.record fields
  let declared := (fieldsOf k).filter (· != Kinds.name)
  let hasName := (fieldsOf k).contains Kinds.name || (v.field? Kinds.name).isSome
  let rest := (ordered s fields).filter fun (l, _) =>
    l != Kinds.isa && l != Kinds.name && !declared.contains l
  let slots ← declared.mapM fun l => field path l (v.field? l)
  let others ← rest.mapM fun (l, w) => field path l (some w)
  let adding ← newLabel path
  let parts := slots ++ others ++ adding
  let name ← if hasName then pure [t " ", ← nameOf path v "name"] else pure []
  let head := [t (s.doc.shown s.library k) .name] ++ name
  let flat := Doc.row (head ++ [delim " {"] ++ Doc.sep (dim ", ") parts ++ [delim "}"])
  let stacked := Doc.col [.row (head ++ [delim " {"]), .indent 2 (.col parts), delim "}"]
  if parts.isEmpty then return .row head else return .alt flat stacked

/-- A notebook: its entries one under another, numbered. -/
partial def notebook (path : Path) (v : Value) : M Doc := do
  let at_ := path ++ [.key Kinds.entries]
  match v.field? Kinds.entries with
  | some (.list items) =>
    let parts ← elements at_ items value
    let numbered := (List.range parts.length).zip parts |>.map fun (i, d) =>
      Doc.row [dim (toString (i + 1) ++ (if i < 9 then "  " else " ")), d]
    return .col (Doc.sep (t "") numbered)
  | other => return .row [t "notebook " .name, ← field path Kinds.entries other]

/-- A section: its name over its body, indented. -/
partial def section_ (path : Path) (v : Value) : M Doc := do
  let head := Doc.row [dim "▾ ", ← nameOf path v "section"]
  let at_ := path ++ [.key Kinds.sectionBody]
  match v.field? Kinds.sectionBody with
  | some (.list items) =>
    return .col [head, .indent 2 (.col (← elements at_ items value))]
  | other => return .col [head, .indent 2 (← value at_ other)]

/-- An evaluation: its expression, then what it gives. -/
partial def evaluation (path : Path) (v : Value) : M Doc := do
  let at_ := path ++ [.key Kinds.expression]
  let outcome : Option Outcome :=
    (v.field? Kinds.expression).bind fun e => (s.results.find? (·.1 == e)).map (·.2)
  match outcome with
  | some (Outcome.failed _ (some rel)) => modify fun st => { st with errors := (at_ ++ rel) :: st.errors }
  | _ => pure ()
  let expression ← value at_ (v.field? Kinds.expression)
  let result : Doc :=
    match outcome with
    | some (.value shown type) =>
      if shown.isEmpty then .row [.text type .dim] else .row [.text shown .result, .text (" : " ++ type) .dim]
    | some (.failed message _) => .text (brief message) .error
    | none => dim "…"
  let marked ← occ (path ++ [.key Kinds.evaluation]) .computed result
  let flat := Doc.row [expression, dim " → ", marked]
  let stacked := Doc.col [expression, .indent 2 (.row [dim "→ ", marked])]
  return .alt flat stacked

/-- A parameter: its name, and its type if it has one, or one is being
given. -/
partial def param (path : Path) (v : Option Value) : M Doc := do
  match v, editingAt s path .edge with
  | some (.cell c), none =>
    modify fun st => { st with inPlain := false }
    let typePath := path ++ [.follow, .key Kinds.type_]
    let type := (s.doc.lookup? s.library c).bind (·.field? Kinds.type_)
    let typed ← if type.isSome || pendingAt s typePath then pure [dim ": ", ← value typePath type] else pure []
    occ path .value (.row (t (s.doc.shown s.library c) .name :: typed)) (some c)
  | _, _ => value path v

/-- A lambda: `name [params] → body`, with what it returns after the
parameters if it says, or is being told. -/
partial def lambda (path : Path) (v : Value) : M Doc := do
  let name ← nameOf path v "λ"
  let paramsPath := path ++ [.key Kinds.params]
  let params ← match v.field? Kinds.params with
    | some (.list items) =>
      if (editingAt s paramsPath .edge).isSome then value paramsPath (v.field? Kinds.params)
      else
        let parts ← elements paramsPath items param
        occ paramsPath .value (container "[" "]" parts parts)
    | other => value paramsPath other
  let returnsPath := path ++ [.key Kinds.returns]
  let returns ←
    if (v.field? Kinds.returns).isSome || pendingAt s returnsPath then
      pure [dim " : ", ← value returnsPath (v.field? Kinds.returns)]
    else pure []
  let body ← value (path ++ [.key Kinds.body]) (v.field? Kinds.body)
  let head := [name, t " ", params] ++ returns
  let flat := Doc.row (head ++ [dim " → ", body])
  let stacked := Doc.col [.row (head ++ [dim " →"]), .indent 2 body]
  return .alt flat stacked

/-- A call: the function, then its arguments by parameter; a function
written between two arguments goes between them. -/
partial def call (path : Path) (v : Value) : M Doc := do
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
    let left ← value (path ++ [.key a]) (v.field? a)
    let right ← value (path ++ [.key b]) (v.field? b)
    let op ← occ (path ++ [.key Kinds.function]) .value (dim (" " ++ sym ++ " "))
    return .row [delim "(", left, op, right, delim ")"]
  | _, _ =>
    let head ← value (path ++ [.key Kinds.function]) fn
    let args ← params.mapM fun p => field path p (v.field? p)
    let extra : List (CellId × Value) := match v with
      | .record fields => (ordered s fields).filter fun (l, _) =>
          l != Kinds.isa && l != Kinds.function && !params.contains l
      | _ => []
    let others ← extra.mapM fun (l, w) => field path l (some w)
    let adding ← newLabel path
    let parts := args ++ others ++ adding
    let flat := Doc.row ([head, delim " {"] ++ Doc.sep (dim ", ") parts ++ [delim "}"])
    let stacked := Doc.col [.row [head, delim " {"], .indent 2 (.col parts), delim "}"]
    if parts.isEmpty then return .row [head, delim " {}"] else return .alt flat stacked

end

/-! ## Parts

The document is drawn in parts, one under another: each entry of a notebook
at the root is one, and any other root is one on its own. A part is laid
out from an `Input`, which holds all the part depends on: its value, the
definitions it reaches, and the selection, folds and results that touch
it. So a part whose input is as it was is as it was, and is laid out again
only when its input changes. -/

/-- Where an occurrence is first drawn, within its part. -/
structure Stop where
  occ : Nat
  line : Nat
  col : Nat
  /-- Whether it's a place with no width: a point between things. -/
  point : Bool := false
  deriving DecidableEq, Inhabited

/-- Each occurrence that's drawn, where it starts, in reading order: by
line, then column; where two start together, a point before a value, and a
container before what it holds. -/
def stops (lines : Array Line) (occs : Array Occ) : Array Stop :=
  let first : Array (Option (Nat × Nat × Bool)) := Id.run do
    let mut first := Array.replicate occs.size none
    for i in [0:lines.size] do
      for span in lines[i]! do
        if span.mark > 0 && span.mark ≤ occs.size then
          if first[span.mark - 1]!.isNone then
            first := first.set! (span.mark - 1) (some (i, span.col, span.text.isEmpty && span.face != .caret))
    return first
  let found := (List.range occs.size).filterMap fun i =>
    first[i]!.map fun (line, col, point) => (⟨i, line, col, point⟩ : Stop)
  found.toArray.qsort fun a b =>
    a.line < b.line || (a.line == b.line && (a.col < b.col ||
      (a.col == b.col && ((a.point && !b.point) || (a.point == b.point && a.occ > b.occ)))))

/-- A span as it goes on the screen: with whether the selection covers it,
whether an error is about it, and whether it's another place the selected
cell is. -/
structure Piece where
  col : Nat
  text : String
  face : Face
  mark : Nat
  selected : Bool := false
  failed : Bool := false
  other : Bool := false
  deriving DecidableEq, Inhabited

/-- A line as it goes on the screen: all a row of the scene is made from,
so a line that's the same after an edit is a row left alone. -/
abbrev Row := Shared (Array Piece)

/-- A part, laid out: its lines, the occurrences their spans are marked
with (mark `n` is occurrence `n - 1`), where each is first drawn, the
selection it was drawn with, and its lines as they go on the screen. -/
structure Block where
  lines : Array Line
  occs : Array Occ
  stops : Array Stop
  selection : Option Selection
  rows : List Row
  deriving DecidableEq, Inhabited

/-- Whether two parts are the same: at once if they're the one object, as a
part is that wasn't laid out again. -/
def Block.same (a b : Block) : Bool :=
  withPtrEq a b (fun _ => decide (a = b)) (by intro h; simp [h])

theorem Block.same_sound (a b : Block) (h : Block.same a b = true) : a = b :=
  of_decide_eq_true h

theorem Block.same_refl (a : Block) : Block.same a a = true :=
  decide_eq_true rfl

/-- Whether a selection covers an occurrence: it, and what's drawn inside
it; not the label of the field it's the value of. -/
def covers (sel : Selection) (o : Occ) : Bool :=
  match sel.stage with
  | .label => o.kind == .fieldEnd && o.path == sel.path
  | _ => sel.path.isPrefixOf o.path && !(o.kind == .label && o.path == sel.path) && o.kind != .fieldEnd

/-- What a part is of. -/
inductive Shape where
  /-- The whole document: its root, or the hole of an empty one. -/
  | whole (root : Option Value)
  /-- A notebook's entry at a path, numbered; the places to add an entry
  before it, and after it if it's the last; and the hole of an entry being
  added before it, if it's the first, or after it. -/
  | entry (number : Nat) (path : Path) (value : Value) (before after holeBefore holeAfter : Option Path)
  /-- A notebook with no entries: the place to add the first. -/
  | empty (point : Path)
  deriving DecidableEq

/-- A part before the editor's state reaches it: what it's of, and what it
reaches. -/
structure Frame where
  shape : Shape
  /-- The definitions it reaches, in the document. -/
  cells : Shared (List (CellId × Value))
  /-- The evaluations' expressions in it. -/
  expressions : List Value
  /-- Whether any kind in it is drawn by a function. -/
  functions : Bool
  deriving DecidableEq

/-- All a part's layout depends on: the part, and what of the editor's
state it's drawn with. -/
structure Input where
  frame : Frame
  selection : Option Selection
  folds : List (Path × Bool)
  results : List (Value × Outcome)
  layouts : Shared (List (Value × Value × Value))
  /-- The selected cell, if this part may show it elsewhere. -/
  marked : Option CellId
  ribbon : Nat
  deriving DecidableEq

def partDoc : Shape → M Doc
  | .whole root => value s [] root
  | .entry number path v before after holeBefore holeAfter => do
    let point (p : Option Path) : M Doc :=
      match p with
      | some p => occ p .insertion (.point .ink)
      | none => pure (.row [])
    -- An entry being added is a line of its own, with no number yet.
    let adding (p : Option Path) : M (List Doc) :=
      match p with
      | some p => do return [.row [dim "·  ", .hang 3 (← value s p none)], t ""]
      | none => pure []
    let hb ← adding holeBefore
    let b ← point before
    let item ← value s path (some v)
    let a ← point after
    let ha ← adding holeAfter
    return .col (hb ++
      [.row [dim (toString number ++ (if number < 10 then "  " else " ")), .hang 3 (.row [b, item, a])], t ""] ++ ha)
  | .empty point => if pendingAt s point then value s point none else occ point .insertion (.point .ink)

end Display

open Display in
/-- A part, laid out. -/
def Display.part (i : Input) : Block :=
  let s : Shown :=
    { doc := { root := none, cells := Std.TreeMap.ofList i.frame.cells.val }, library := Builtin.library,
      selection := i.selection, folds := i.folds, results := i.results, layouts := i.layouts.val }
  let (doc, drawn) := (partDoc s i.frame.shape).run {}
  let lines := Doc.lines i.ribbon 0 0 0 doc
  let occs := drawn.occs
  let piece (s : Span) : Piece :=
    match occs[s.mark - 1]? with
    | some o =>
      if s.mark == 0 then { col := s.col, text := s.text, face := s.face, mark := 0 }
      else
        let selected := match i.selection with
          | some sel => covers sel o
          | none => false
        { col := s.col, text := s.text, face := s.face, mark := s.mark, selected, failed := o.failed,
          other := !selected && !s.text.isEmpty && (o.kind == .value || o.kind == .label) && o.cell.isSome &&
            o.cell == i.marked }
    | none => { col := s.col, text := s.text, face := s.face, mark := 0 }
  { lines, occs, stops := stops lines occs, selection := i.selection, rows := lines.toList.map fun l => ⟨l.map piece⟩ }

namespace Display

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

/-- What a part of the document is of: an entry of the root notebook, the
whole root, or a root notebook with no entries. -/
inductive Entry where
  | entry (position : Position) (value : Value)
  | whole (root : Option Value)
  | empty
  deriving DecidableEq, Inhabited

/-- The document's root, split: the root notebook's entries, or the whole
root. -/
def entries (root : Option Value) : List Entry :=
  match root with
  | some v =>
    if v.kind? == some Kinds.notebook then
      match v.field? Kinds.entries with
      | some (.list []) => [.empty]
      | some (.list items) => items.map fun (p, w) => .entry p w
      | _ => [.whole root]
    else [.whole root]
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
  | .empty => Option.none

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

/-- What of the editor's state the parts are drawn with. -/
structure Seen where
  selection : Option Selection := none
  folds : List (Path × Bool) := []
  results : List (Value × Outcome) := []
  layouts : Shared (List (Value × Value × Value)) := ⟨[]⟩
  /-- The cell the selection is on, and whether the document defines it. -/
  marked : Option CellId := none
  markedDefined : Bool := false
  ribbon : Nat := 80
  deriving DecidableEq

/-- The path of the root notebook's entries. -/
def entriesPath : Path := [.key Kinds.entries]

/-- The entry being added, if the selection is pending among the root
notebook's entries: where it would go. -/
def pendingEntry (selection : Option Selection) : Option Position :=
  match selection with
  | some sel =>
    if sel.stage == .pending && sel.path.dropLast == entriesPath then
      match sel.path.getLast? with
      | some (.element p) => some p
      | _ => none
    else none
  | none => none

/-- The path of an entry at a position. -/
def entryAt (p : Position) : Path := entriesPath ++ [.element p]

/-- What an entry's place among the entries gives its part: its number,
the places to add an entry beside it, and the hole of an entry being added
beside it. It's all a part takes from the other entries. -/
structure Slot where
  number : Nat := 0
  before : Option Path := none
  after : Option Path := none
  holeBefore : Option Path := none
  holeAfter : Option Path := none
  deriving DecidableEq, Inhabited

/-- Where an item is among the entries, if it's one. -/
def Item.place (i : Item) : Option Position :=
  match i.entry with
  | .entry p _ => some p
  | _ => none

/-- Each entry's slot, by its position, in order. An entry being added,
where no entry is, is a hole after the entry before it, or before the
first; and there's no place to add an entry beside the hole. -/
def slotsOf (places : List (Option Position)) (pending : Option Position) : Array (Position × Slot) :=
  let positions := places.filterMap id
  let pending := pending.filter fun p => !positions.contains p
  let rec go (number : Nat) (prev : Option Position) (holeBefore : Bool) :
      List Position → List (Position × Slot)
    | [] => []
    | p :: rest =>
      let next := rest.head?
      -- The hole is before this entry if this is the first and it sorts first.
      let hb := if number == 1 then pending.filter fun h => Position.lt h p else none
      let ha := pending.filter fun h => Position.lt p h && (next.map fun n => Position.lt h n).getD true
      let beside := holeBefore || hb.isSome
      (p, { number,
            before := if beside then none else some (entryAt (Position.between prev (some p))),
            after := if rest.isEmpty && ha.isNone then some (entryAt (Position.between (some p) none)) else none,
            holeBefore := hb.map entryAt, holeAfter := ha.map entryAt }) :: go (number + 1) (some p) ha.isSome rest
  (go 1 none false positions).toArray

/-- The slots, held as one object while the entries' positions are. -/
abbrev Slots := Shared (Array (Position × Slot))

/-- An entry's slot, by its position. -/
def slotAt (slots : Slots) (p : Position) : Slot :=
  ((slots.val.binSearch (p, default) fun a b => Position.lt a.1 b.1).map (·.2)).getD {}

/-- An item's part: for an entry, with its slot. -/
def frameOf (slots : Slots) (i : Item) : Frame :=
  match i.entry with
  | .whole root => ⟨.whole root, i.reached, i.expressions, i.functions⟩
  | .entry p v =>
    let slot := slotAt slots p
    ⟨.entry slot.number (entryAt p) v slot.before slot.after slot.holeBefore slot.holeAfter, i.reached,
      i.expressions, i.functions⟩
  | .empty => ⟨.empty (entryAt (Position.between none none)), ⟨[]⟩, [], false⟩

namespace Frame

/-- Whether a path is in a part, or the part in it, or it's the hole of an
entry being added that the part draws. -/
def touches (f : Frame) (q : Path) : Bool :=
  match f.shape with
  | .whole _ => true
  | .entry _ path _ _ _ holeBefore holeAfter =>
    path.isPrefixOf q || q.isPrefixOf path || holeBefore == some q || holeAfter == some q
  | .empty point => q == point

/-- What of each thing the editor's state holds a part is drawn with: the
selection if it's in the part, the folds in it, the results of its
evaluations, what functions gave if it has kinds they draw, and the
selected cell if it reaches it. -/
def selection (f : Frame) (s : Option Selection) : Option Selection := s.filter fun sel => f.touches sel.path

def folds (f : Frame) (fs : List (Path × Bool)) : List (Path × Bool) :=
  match f.shape with
  | .whole _ => fs
  | .entry _ path _ _ _ _ _ => fs.filter fun fold => path.isPrefixOf fold.1
  | .empty _ => []

def results (f : Frame) (rs : List (Value × Outcome)) : List (Value × Outcome) :=
  if f.expressions.isEmpty then [] else rs.filter fun r => f.expressions.contains r.1

def layouts (f : Frame) (ls : Shared (List (Value × Value × Value))) : Shared (List (Value × Value × Value)) :=
  if f.functions then ls else ⟨[]⟩

def marked (f : Frame) (m : Option CellId × Bool) : Option CellId :=
  match f.shape with
  | .whole _ => m.1
  | .entry _ _ _ _ _ _ _ => m.1.filter fun cell => !m.2 || f.cells.val.any (·.1 == cell)
  | .empty _ => none

end Frame

/-- A part's input: the part, with what of the editor's state it's drawn
with. -/
def input (c : Seen) (f : Frame) : Input :=
  { frame := f, selection := f.selection c.selection, folds := f.folds c.folds,
    results := f.results c.results, layouts := f.layouts c.layouts, marked := f.marked (c.marked, c.markedDefined),
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
def touched (c c' : Seen) (f : Frame) : Bool :=
  c.ribbon != c'.ribbon || differs f.selection c.selection c'.selection || differs f.folds c.folds c'.folds ||
    differs f.results c.results c'.results || differs f.layouts c.layouts c'.layouts ||
    differs f.marked (c.marked, c.markedDefined) (c'.marked, c'.markedDefined)

/-- Whether a change of the editor's state leaves all the parts are drawn
with as it was: then no part is touched, and none is asked. -/
def still (c c' : Seen) : Bool :=
  c.ribbon == c'.ribbon && equal c.selection c'.selection && equal c.folds c'.folds &&
    equal c.results c'.results && equal c.layouts c'.layouts &&
    decide ((c.marked, c.markedDefined) = (c'.marked, c'.markedDefined))

theorem not_touched_of_still (c c' : Seen) (h : still c c' = true) (f : Frame) : touched c c' f = false := by
  simp only [still, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hr, hs⟩, hf⟩, hres⟩, hl⟩, hm⟩ := h
  simp [touched, differs, hr, hs, hf, hres, hl, hm, equal_refl]

/-- A part that a change doesn't touch has the input it had. -/
theorem input_of_not_touched (c c' : Seen) (f : Frame) (h : touched c c' f = false) : input c' f = input c f := by
  simp only [touched, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hr, hs⟩, hf⟩, hres⟩, hl⟩, hm⟩ := h
  simp only [input, hr, same_of_not_differs _ _ _ hs, same_of_not_differs _ _ _ hf,
    same_of_not_differs _ _ _ hres, same_of_not_differs _ _ _ hl, same_of_not_differs _ _ _ hm]

/-- What a part's input is made from, besides its item: what the editor's
state shows, and the entries' slots. -/
structure Around where
  seen : Seen
  slots : Slots

/-- A part's input, of its item. -/
def inputOf (a : Around) (i : Item) : Input := input a.seen (frameOf a.slots i)

/-- Whether a change of what's around touches a part, given the input it
had: whether its slot differs, or what it's drawn with. -/
def touchedAround (a a' : Around) (i : Item) (was : Input) : Bool :=
  differs (fun slots => frameOf slots i) a.slots a'.slots || touched a.seen a'.seen was.frame

def stillAround (a a' : Around) : Bool := equal a.slots a'.slots && still a.seen a'.seen

theorem inputOf_of_not_touched (a a' : Around) (i : Item) (h : touchedAround a a' i (inputOf a i) = false) :
    inputOf a' i = inputOf a i := by
  simp only [touchedAround, Bool.or_eq_false_iff] at h
  have hf : frameOf a.slots i = frameOf a'.slots i := same_of_not_differs _ _ _ h.1
  have ht : touched a.seen a'.seen (frameOf a.slots i) = false := h.2
  simp only [inputOf, ← hf]
  exact input_of_not_touched a.seen a'.seen _ ht

theorem not_touchedAround_of_still (a a' : Around) (h : stillAround a a' = true) (i : Item) (was : Input) :
    touchedAround a a' i was = false := by
  simp only [stillAround, Bool.and_eq_true] at h
  simp [touchedAround, differs, h.1, not_touched_of_still a.seen a'.seen h.2]

/-- A document's parts, laid out: all of it, worked out from nothing. -/
def blocks (d : Document) (c : Seen) : List Block :=
  let items := (entries d.root).map (item fun x => d.cells[x]?)
  let around : Around := ⟨c, ⟨slotsOf (items.map Item.place) (pendingEntry c.selection)⟩⟩
  (items.map (inputOf around)).map part

end Display

end Progred
