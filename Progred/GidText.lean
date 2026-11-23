import Progred.Kinds

/-!
GID text: a document as a file. One envelope, `{ "binders": {…}, "cells":
{…}, "root": value }`, each part optional. A value is quoted text, a blob
`0x…`, a cell (32 hex digits, or a binder's name), a record `{label: value,
…}` or a list `[value, …]`, an element optionally led by its position
`0x…:`. `binders` gives names to cell ids, for this file only; a name not
bound there gets a fresh id.
-/

namespace Progred.GidText

open Progred

/-! ## Reading -/

structure Reader where
  input : Array Char
  at_ : Nat := 0
  binders : List (String × CellId) := []

abbrev Read := StateT Reader (ExceptT String IO)

def fail {α : Type} (message : String) : Read α := do
  throw s!"{message}, at character {(← get).at_}"

def peek : Read (Option Char) := do
  let r ← get
  return r.input[r.at_]?

def advance : Read Unit := modify fun r => { r with at_ := r.at_ + 1 }

partial def space : Read Unit := do
  match ← peek with
  | some c => if c.isWhitespace then advance; space
  | none => pure ()

def expect (c : Char) : Read Unit := do
  space
  if (← peek) == some c then advance else fail s!"expected '{c}'"

/-- Whether the next character, past spaces, is `c`; takes it if so. -/
def take? (c : Char) : Read Bool := do
  space
  if (← peek) == some c then advance; return true else return false

partial def bare : Read String := do
  let rec go (acc : String) : Read String := do
    match ← peek with
    | some c => if c.isAlphanum || c == '_' then advance; go (acc.push c) else return acc
    | none => return acc
  go ""

partial def quoted : Read String := do
  expect '"'
  let rec go (acc : String) : Read String := do
    match ← peek with
    | none => fail "text has no closing quote"
    | some '"' => advance; return acc
    | some '\\' =>
      advance
      match ← peek with
      | some 'n' => advance; go (acc.push '\n')
      | some 't' => advance; go (acc.push '\t')
      | some '"' => advance; go (acc.push '"')
      | some '\\' => advance; go (acc.push '\\')
      | _ => fail "an escape is one of \\\" \\\\ \\n \\t"
    | some '\n' => fail "text can't hold a raw new line"
    | some c => advance; go (acc.push c)
  go ""

def hexBytes (s : String) : Option (List UInt8) :=
  let rec go : List Char → Option (List UInt8)
    | [] => some []
    | a :: b :: rest => do
      let x ← CellId.digit? a
      let y ← CellId.digit? b
      return (x * 16 + y).toUInt8 :: (← go rest)
    | [_] => none
  go s.toList

/-- The cell a bare token names: an id of 32 hex digits, else a binder,
bound to a fresh id the first time it's met unbound. -/
def cellOf (token : String) : Read CellId := do
  if let some id := CellId.ofHex? token then return id
  if let some (_, id) := (← get).binders.find? (·.1 == token) then return id
  let id ← (CellId.new : IO CellId)
  modify fun r => { r with binders := (token, id) :: r.binders }
  return id

/-- A record of one field, a literal kind holding a blob, is the older way
of writing a literal. -/
def legacy : Value → Value
  | .record [(k, .blob b)] =>
    if k == Kinds.f64 || k == Kinds.u64 || k == Kinds.text || k == Kinds.bool then Value.literal k b
    else .record [(k, .blob b)]
  | v => v

mutual
partial def value : Read Value := do
  space
  match ← peek with
  | some '"' => return Value.text (← quoted)
  | some '{' =>
    advance
    let fields ← record []
    return legacy (.record fields)
  | some '[' =>
    advance
    let items ← list []
    let positions := items.filterMap (·.1)
    if positions.length == items.length then
      return .list (items.filterMap fun (p, v) => p.map (·, v))
    else if positions.isEmpty then
      return .list ((Position.spread items.length).zip (items.map (·.2)))
    else fail "a list's elements all have positions, or none do"
  | some _ =>
    let token ← bare
    if token.isEmpty then fail "expected a value"
    if token.startsWith "0x" && CellId.ofHex? token == none then
      match hexBytes (token.drop 2).toString with
      | some b => return .blob b
      | none => fail "a blob is 0x and an even number of hex digits"
    else return .cell (← cellOf token)
  | none => fail "expected a value"

partial def record (acc : List (CellId × Value)) : Read (List (CellId × Value)) := do
  if ← take? '}' then return acc
  space
  let label ← cellOf (← bare)
  expect ':'
  let v ← value
  if acc.any (·.1 == label) then fail "a record has a label twice"
  let _ ← take? ','
  record (Value.setField acc label v)

partial def list (acc : List (Option Position × Value)) : Read (List (Option Position × Value)) := do
  if ← take? ']' then return acc
  let v ← value
  if ← take? ':' then
    match v with
    | .blob p =>
      let w ← value
      let _ ← take? ','
      list (acc ++ [(some p, w)])
    | _ => fail "a position is a blob"
  else
    let _ ← take? ','
    list (acc ++ [(none, v)])
end

partial def binders : Read Unit := do
  expect '{'
  let rec go : Read Unit := do
    if ← take? '}' then return
    space
    let name ← quoted
    expect ':'
    space
    match CellId.ofHex? (← bare) with
    | some id => modify fun r => { r with binders := (name, id) :: r.binders }
    | none => fail "a binder's id is 32 hex digits"
    let _ ← take? ','
    go
  go

partial def cells (acc : Std.TreeMap CellId Value) : Read (Std.TreeMap CellId Value) := do
  if ← take? '}' then return acc
  space
  let id ← cellOf (← bare)
  expect ':'
  let v ← value
  if acc.contains id then fail "a cell is defined twice"
  let _ ← take? ','
  cells (acc.insert id v)

partial def envelope (d : Document) : Read Document := do
  if ← take? '}' then return d
  space
  let key ← quoted
  expect ':'
  let d ← match key with
    | "binders" => binders; pure d
    | "cells" => expect '{'; pure { d with cells := ← cells d.cells }
    | "root" => pure { d with root := some (← value) }
    | k => fail s!"an envelope has binders, cells and root, not {k}"
  let _ ← take? ','
  envelope d

/-- A document, from its text. -/
def parse (text : String) : IO (Except String Document) := do
  let read : Read Document := do expect '{'; envelope {}
  match ← (read.run { input := text.toList.toArray }).run with
  | .ok (d, _) => return .ok d
  | .error e => return .error e

/-! ## Writing -/

def hexByte (b : UInt8) : String :=
  String.ofList [CellId.hexDigit (b.toUInt64 >>> 4), CellId.hexDigit (b.toUInt64 &&& 15)]

def hex (bytes : List UInt8) : String := "0x" ++ String.join (bytes.map hexByte)

def escape (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\t' => acc ++ "\\t"
    | c => acc.push c) ""

/-- Every cell a value mentions. -/
partial def mentions : Value → List CellId
  | .cell c => [c]
  | .blob _ => []
  | .list items => items.flatMap fun (_, v) => mentions v
  | .record fields => fields.flatMap fun (l, v) => l :: mentions v

/-- A name as a binder can be written: its letters, digits and underscores,
others as underscores, not starting with a digit. -/
def sanitized (name : String) : String :=
  let s := name.map fun c => if c.isAlphanum || c == '_' then c else '_'
  if s.isEmpty || (s.front.isDigit) then "_" ++ s else s

/-- A binder for each cell: its sanitized name, else `_` and its last 5 hex
digits, with `_2`, `_3` on a clash, and never 32 hex digits. -/
def bindersFor (d : Document) (lib : Library) (ids : List CellId) : List (CellId × String) :=
  ids.foldl (fun acc id =>
    let base := match d.name? lib id with
      | some n => sanitized n
      | none => "_" ++ (id.hex.drop 27).toString
    let base := if (CellId.ofHex? base).isSome then "_" ++ base else base
    let taken (s : String) := acc.any (·.2 == s)
    let rec pick (n : Nat) (fuel : Nat) : String :=
      let candidate := if n == 1 then base else s!"{base}_{n}"
      match fuel with
      | 0 => candidate
      | fuel + 1 => if taken candidate then pick (n + 1) fuel else candidate
    acc ++ [(id, pick 1 acc.length)]) []

partial def print (binder : CellId → String) (indent : String) : Value → String
  | .cell c => binder c
  | .blob b => hex b
  | .list [] => "[]"
  | .list items =>
    let inner := indent ++ "  "
    "[\n" ++ String.join (items.map fun (p, v) => s!"{inner}{hex p}: {print binder inner v},\n") ++ indent ++ "]"
  | .record [] => "{}"
  | .record fields =>
    match (Value.record fields).text? with
    | some s =>
      if fields.length == 2 then "\"" ++ escape s ++ "\"" else block fields
    | none => block fields
where
  block (fields : List (CellId × Value)) : String :=
    let inner := indent ++ "  "
    "{\n" ++ String.join (fields.map fun (l, v) => s!"{inner}{binder l}: {print binder inner v},\n") ++ indent ++ "}"

/-- A document, as text: binders by name, cells named first, by name. -/
def write (d : Document) (lib : Library) : String :=
  let defined := d.cells.toList
  let ids := ((d.root.map mentions).getD [] ++ defined.flatMap fun (c, v) => c :: mentions v).eraseDups
  let table := bindersFor d lib ids
  let binder (c : CellId) : String := ((table.find? (·.1 == c)).map (·.2)).getD c.hex
  let sortedBinders := table.toArray.qsort (fun a b => a.2 < b.2) |>.toList
  let named := defined.filter fun (c, _) => (d.name? lib c).isSome
  let unnamed := defined.filter fun (c, _) => (d.name? lib c).isNone
  let key (c : CellId) : String := d.shown lib c ++ " " ++ c.hex
  let namedSorted := named.toArray.qsort (fun a b => key a.1 < key b.1) |>.toList
  "{\n  \"binders\": {\n"
    ++ String.join (sortedBinders.map fun (c, n) => s!"    \"{n}\": {c.hex},\n")
    ++ "  },\n  \"cells\": {\n"
    ++ String.join ((namedSorted ++ unnamed).map fun (c, v) => s!"    {binder c}: {print binder "    " v},\n")
    ++ "  },\n"
    ++ (match d.root with
      | some r => s!"  \"root\": {print binder "  " r},\n"
      | none => "")
    ++ "}\n"

end Progred.GidText
