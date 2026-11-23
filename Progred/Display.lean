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
        else kinded path k fields
      | none => record path fields

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
  /-- A notebook's entry at a path, numbered: its value, or the hole of one
  being added; and the places to add an entry before it, and after it if
  it's the last. -/
  | entry (number : Nat) (path : Path) (value : Option Value) (before after : Option Path)
  /-- A notebook with no entries: the place to add the first. -/
  | empty (point : Path)
  deriving DecidableEq

/-- All a part's layout depends on. -/
structure Input where
  shape : Shape
  /-- The definitions it reaches, in the document. -/
  cells : Shared (List (CellId × Value))
  selection : Option Selection
  folds : List (Path × Bool)
  results : List (Value × Outcome)
  /-- The selected cell, if this part may show it elsewhere. -/
  marked : Option CellId
  ribbon : Nat
  deriving DecidableEq

def partDoc : Shape → M Doc
  | .whole root => value s [] root
  | .entry number path v before after => do
    let point (p : Option Path) : M Doc :=
      match p with
      | some p => occ p .insertion (.point .ink)
      | none => pure (.row [])
    let b ← point before
    let item ← value s path v
    let a ← point after
    return .col [.row [dim (toString number ++ (if number < 10 then "  " else " ")), .hang 3 (.row [b, item, a])], t ""]
  | .empty point => occ point .insertion (.point .ink)

end Display

open Display in
/-- A part, laid out. -/
def Display.part (i : Input) : Block :=
  let s : Shown :=
    { doc := { root := none, cells := Std.TreeMap.ofList i.cells.val }, library := Builtin.library,
      selection := i.selection, folds := i.folds, results := i.results }
  let (doc, drawn) := (partDoc s i.shape).run {}
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

/-- The document's definitions, in order: one object while the document's
definitions are, so that what's worked out from them is compared at once. -/
abbrev Cells := Shared (Array (CellId × Value))

def Cells.of (d : Document) : Cells := ⟨d.cells.toList.toArray⟩

/-- A definition, among definitions in order. -/
def definitionIn (cells : Array (CellId × Value)) (c : CellId) : Option Value :=
  (cells.binSearch (c, default) fun a b => compare a.1 b.1 == .lt).map (·.2)

/-- The definitions cells reach, each once, in the order they're reached. -/
partial def reachIn (cells : Array (CellId × Value)) (todo : List CellId)
    (seen : Std.TreeSet CellId := {}) (found : Array (CellId × Value) := #[]) : List (CellId × Value) :=
  match todo with
  | [] => found.toList
  | c :: rest =>
    if seen.contains c then reachIn cells rest seen found
    else match definitionIn cells c with
      | some v => reachIn cells ((mentionsInto #[] v).toList ++ rest) (seen.insert c) (found.push (c, v))
      | none => reachIn cells rest (seen.insert c) found

/-- What a part of the document is worked out from: an entry of the root
notebook, or the whole root, with the document's definitions. -/
inductive ItemKey where
  | entry (position : Position) (value : Value) (cells : Cells)
  | whole (root : Option Value) (cells : Cells)
  deriving DecidableEq

/-- The document, split: the root notebook's entries, or the whole root. -/
def itemKeys (root : Option Value) (cells : Cells) : List ItemKey :=
  match root with
  | some v =>
    if v.kind? == some Kinds.notebook then
      match v.field? Kinds.entries with
      | some (.list items) => items.map fun (p, w) => .entry p w cells
      | _ => [.whole root cells]
    else [.whole root cells]
  | none => [.whole root cells]

/-- A part of the document, with what it reaches: the definitions, and the
evaluations' expressions in it. -/
inductive Item where
  | entry (position : Position) (value : Value) (reached : Shared (List (CellId × Value)))
      (expressions : List Value)
  | whole (root : Option Value) (reached : Shared (List (CellId × Value))) (expressions : List Value)
  deriving DecidableEq, Inhabited

def item : ItemKey → Item
  | .entry position value cells =>
    .entry position value ⟨reachIn cells.val (mentionsInto #[] value).toList⟩ (expressionsIn value)
  | .whole root cells =>
    match root with
    | some v => .whole root ⟨reachIn cells.val (mentionsInto #[] v).toList⟩ (expressionsIn v)
    | none => .whole root ⟨[]⟩ []

/-- What of the editor's state the parts are drawn with. -/
structure Seen where
  selection : Option Selection := none
  folds : List (Path × Bool) := []
  results : List (Value × Outcome) := []
  /-- The cell the selection is on, and whether the document defines it. -/
  marked : Option CellId := none
  markedDefined : Bool := false
  ribbon : Nat := 80
  deriving DecidableEq

/-- The path of the root notebook's entries. -/
def entriesPath : Path := [.key Kinds.entries]

/-- The parts' inputs: one for each entry, in order, with the hole of an
entry being added among them, and no place to add an entry beside the hole;
or one for the whole root. -/
def assemble (items : List Item) (c : Seen) : List Input :=
  match items with
  | [.whole root cells expressions] =>
    [{ shape := .whole root, cells, selection := c.selection, folds := c.folds,
       results := c.results.filter fun r => expressions.contains r.1, marked := c.marked, ribbon := c.ribbon }]
  | _ =>
    -- The root notebook's entries: an item that isn't one is no entry.
    let items : List (Position × Value × Shared (List (CellId × Value)) × List Value) :=
      items.filterMap fun
        | .entry p v reached expressions => some (p, v, reached, expressions)
        | .whole .. => none
    -- The entry being added, if the selection is pending among the entries.
    let pending : Option Position :=
      match c.selection with
      | some sel =>
        if sel.stage == .pending && sel.path.dropLast == entriesPath then
          match sel.path.getLast? with
          | some (.element p) => if items.any (·.1 == p) then none else some p
          | _ => none
        else none
      | none => none
    let all : List (Position × Option (Value × Shared (List (CellId × Value)) × List Value)) :=
      match pending with
      | some p =>
        (items.filter fun i => Position.lt i.1 p).map (fun i => (i.1, some i.2)) ++ [(p, none)] ++
          (items.filter fun i => !Position.lt i.1 p).map fun i => (i.1, some i.2)
      | none => items.map fun i => (i.1, some i.2)
    let at_ (p : Position) : Path := entriesPath ++ [.element p]
    let rec go (number : Nat) (prev : Option (Position × Bool)) :
        List (Position × Option (Value × Shared (List (CellId × Value)) × List Value)) → List Input
      | [] => []
      | (p, item) :: rest =>
        let beside := item.isNone || (prev.map (·.2)).getD false
        let before := if beside then none else some (at_ (Position.between (prev.map (·.1)) (some p)))
        let after := if rest.isEmpty && item.isSome then some (at_ (Position.between (some p) none)) else none
        let path := at_ p
        let touches (q : Path) : Bool := path.isPrefixOf q || q.isPrefixOf path
        let cells : Shared (List (CellId × Value)) := (item.map (·.2.1)).getD ⟨[]⟩
        let expressions := (item.map (·.2.2)).getD []
        { shape := .entry number path (item.map (·.1)) before after, cells,
          selection := c.selection.filter fun sel => touches sel.path,
          folds := c.folds.filter fun f => path.isPrefixOf f.1,
          results := c.results.filter fun r => expressions.contains r.1,
          marked := c.marked.filter fun cell => !c.markedDefined || cells.val.any (·.1 == cell),
          ribbon := c.ribbon } :: go (number + 1) (some (p, item.isNone)) rest
    if all.isEmpty then
      [{ shape := .empty (at_ (Position.between none none)), cells := ⟨[]⟩, selection := none, folds := [],
         results := [], marked := none, ribbon := c.ribbon }]
    else go 1 none all

/-- A document's parts, laid out: all of it, worked out from nothing. -/
def blocks (d : Document) (c : Seen) : List Block :=
  (assemble ((itemKeys d.root (Cells.of d)).map item) c).map part

end Display

end Progred
