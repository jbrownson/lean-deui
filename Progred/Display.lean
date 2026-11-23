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
  deriving BEq, Inhabited, Repr

/-- Text being typed at the selection: a line of the value's own (text, a
number), or a query a picker answers. -/
structure Editing where
  text : String
  caret : Nat
  picker : Bool
  choice : Nat := 0
  deriving BEq, Inhabited

structure Selection where
  path : Path
  stage : Stage := .edge
  editing : Option Editing := none
  deriving Inhabited

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
  deriving BEq, Inhabited, Repr

structure Occ where
  path : Path
  kind : OccKind
  deriving Inhabited

/-- What an evaluation gave: a value and its type, or what went wrong. -/
inductive Outcome where
  | value (shown type : String)
  | failed (message : String)
  deriving Inhabited, BEq

/-- What the projection is of, besides the document. -/
structure Shown where
  doc : Document
  library : Library
  selection : Option Selection := none
  /-- Folds the user set, by path: true is closed. -/
  folds : List (Path × Bool) := []
  /-- Evaluations' outcomes, by expression. -/
  results : List (Value × Outcome) := []

namespace Display

abbrev M := StateM (Array Occ)

/-- A doc, marked as an occurrence. -/
def occ (path : Path) (kind : OccKind) (d : Doc) : M Doc := do
  modify (·.push ⟨path, kind⟩)
  return .mark (← get).size d

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

/-- Whether a cell is drawn open at a path: as the user set it, else open
when it has a definition of the document's that's more than a name, is the
root or a list's element, an entry, and isn't inside another cell's
definition. As a field's value, a function called or a kind, it shows as
its name. -/
def isOpen (path : Path) (c : CellId) : Bool :=
  match s.folds.find? (·.1 == path) with
  | some (_, closed) => !closed && (s.doc.lookup? s.library c).isSome
  | none =>
    match s.doc.definition? c with
    | some (.record [(l, _)]) => l != Kinds.name
    | some _ =>
      !(path.contains .follow) && (match path.getLast? with | some (.element _) | .none => true | _ => false)
    | none => false

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

mutual

/-- A value at a path, or the hole where there is none. -/
partial def value (path : Path) : Option Value → M Doc
  | none => hole s path
  | some v =>
    -- A picker over a value shows its query in the value's place.
    match editingAt s path .edge with
    | some e =>
      if e.picker then occ path .value (.row [typing e .ink])
      else do
        let inner ← line path v (some e)
        occ path .value inner
    | none => do
      let inner ← drawn path v
      occ path .value inner

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

partial def drawn (path : Path) (v : Value) : M Doc := do
  match v with
  | .cell c => cell path c
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
        else kinded path k fields
      | none => record path fields

/-- A cell: open, its definition in parentheses; closed, its name, or its
kind and short id. -/
partial def cell (path : Path) (c : CellId) : M Doc := do
  if isOpen s path c then
    let inner ← value (path ++ [.follow]) (s.doc.lookup? s.library c)
    return .row [delim "(", inner, delim ")"]
  else
    match s.doc.name? s.library c with
    | some n => return t n .name
    | none =>
      match (s.doc.lookup? s.library c).bind (·.kind?) with
      | some k => return .row [delim "(", t (s.doc.shown s.library k) .name, dim (" " ++ c.short), delim ")"]
      | none => return dim c.short

/-- A list's elements, with a place to insert before each and after the
last, and the hole of an element being added. -/
partial def elements (path : Path) (items : List (Position × Value)) : M (List Doc) := do
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
      let item ← value (path ++ [.element p]) v
      let last ← if rest.isEmpty && v.isSome then insertion (some p) none else pure none_
      return .row [point, item, last] :: (← go (some (p, v.isNone)) rest)
  if all.isEmpty then return [← insertion none none]
  else
    let _ := positions
    go none all

partial def list (path : Path) (items : List (Position × Value)) : M Doc := do
  let parts ← elements path items
  return container "[" "]" parts parts

/-- A field: its label, then its value beside it, or below it indented. -/
partial def field (path : Path) (label : CellId) (v : Option Value) : M Doc := do
  let at_ := path ++ [.key label]
  let name ← occ at_ .label (t (s.doc.shown s.library label) .label)
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
  let shown ← (ordered s fields).mapM fun (l, v) => field path l (some v)
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
    let parts ← elements at_ items
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
    return .col [head, .indent 2 (.col (← elements at_ items))]
  | other => return .col [head, .indent 2 (← value at_ other)]

/-- An evaluation: its expression, then what it gives. -/
partial def evaluation (path : Path) (v : Value) : M Doc := do
  let at_ := path ++ [.key Kinds.expression]
  let expression ← value at_ (v.field? Kinds.expression)
  let result : Doc :=
    match (v.field? Kinds.expression).bind fun e => s.results.find? (·.1 == e) with
    | some (_, .value shown type) =>
      if shown.isEmpty then .row [.text type .dim] else .row [.text shown .result, .text (" : " ++ type) .dim]
    | some (_, .failed message) => .text ((message.splitOn "\n").headD "") .error
    | none => dim "…"
  let marked ← occ (path ++ [.key Kinds.evaluation]) .computed result
  let flat := Doc.row [expression, dim " → ", marked]
  let stacked := Doc.col [expression, .indent 2 (.row [dim "→ ", marked])]
  return .alt flat stacked

/-- A lambda: `name [params] → body`. -/
partial def lambda (path : Path) (v : Value) : M Doc := do
  let name ← nameOf path v "λ"
  let params ← value (path ++ [.key Kinds.params]) (v.field? Kinds.params)
  let body ← value (path ++ [.key Kinds.body]) (v.field? Kinds.body)
  let flat := Doc.row [name, t " ", params, dim " → ", body]
  let stacked := Doc.col [.row [name, t " ", params, dim " →"], .indent 2 body]
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

/-- The whole document: its root, or the hole of an empty one. -/
def document : M Doc := value s [] s.doc.root

/-- The document laid out: its lines, and the occurrences their spans are
marked with (mark `n` is occurrence `n - 1`). -/
def laid (ribbon : Nat) : Array Line × Array Occ :=
  let (doc, occs) := (document s).run #[]
  (Doc.lines ribbon 0 0 0 doc, occs)

end Display

end Progred
