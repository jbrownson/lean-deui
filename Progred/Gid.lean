import Std.Data.TreeMap

/-!
GID: the data Progred edits. A document is one optional root value and a
table from cells to their definitions. A value is a reference to a cell,
a blob of bytes, a list, or a record whose labels are cells. There are no
string or number atoms: text and numbers are records of a kind, with their
bytes (`Progred/Kinds.lean`).
-/

namespace Progred

/-- A cell's id: 128 random bits, written as 32 lowercase hex digits. Minted
only from the system's random numbers (`CellId.new`), never from a name. -/
structure CellId where
  hi : UInt64
  lo : UInt64
  deriving BEq, Hashable, DecidableEq, Ord, Inhabited

namespace CellId

def hexDigit (n : UInt64) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

def hex64 (v : UInt64) : String :=
  String.ofList ((List.range 16).map fun i => hexDigit ((v >>> (60 - 4 * i).toUInt64) &&& 15))

/-- The id as 32 lowercase hex digits. -/
def hex (c : CellId) : String := hex64 c.hi ++ hex64 c.lo

def digit? (c : Char) : Option UInt64 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48).toUInt64
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87).toUInt64
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55).toUInt64
  else none

def word? (cs : List Char) : Option UInt64 :=
  cs.foldlM (fun acc c => (digit? c).map (acc * 16 + ·)) 0

/-- The id written as exactly 32 hex digits, in either case. -/
def ofHex? (s : String) : Option CellId :=
  let cs := s.toList
  if cs.length = 32 then do
    return ⟨← word? (cs.take 16), ← word? (cs.drop 16)⟩
  else none

/-- How an unnamed cell shows: `…` and its last 5 hex digits. -/
def short (c : CellId) : String := "…" ++ (c.hex.drop 27).toString

/-- A new id, from the system's random numbers. -/
def new : IO CellId := do
  let bytes ← IO.getRandomBytes 16
  let word (from_ : Nat) : UInt64 :=
    (List.range 8).foldl (fun acc i => acc <<< 8 ||| (bytes.get! (from_ + i)).toUInt64) 0
  return ⟨word 0, word 8⟩

instance : ToString CellId := ⟨hex⟩

end CellId

/-- Where an element is in a list: a non-empty byte string whose last byte
isn't zero, read as a binary fraction, so there is always one between any
two. Ordered byte by byte. -/
abbrev Position := List UInt8

namespace Position

def lt : Position → Position → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lt as bs)

/-- A position after `low`, with no upper bound: `low`'s bytes while they
are 255, then one halfway from the next byte to the top. -/
def above : Position → Position
  | [] => [128]
  | a :: as => if a = 255 then 255 :: above as else [((a.toNat + 256) / 2).toUInt8]

/-- A position strictly between `low` and `high`, taken as the least and
the greatest when absent. -/
def between : Option Position → Option Position → Position
  | low, none => above (low.getD [])
  | low, some high => go (low.getD []) high
where
  go : Position → Position → Position
    | _, [] => [128]  -- no room: `high` should be greater than `low`
    | [], b :: bs =>
      if b ≥ 2 then [b / 2]
      else if b = 1 then 0 :: above []
      else 0 :: go [] bs
    | a :: as, b :: bs =>
      if b.toNat ≥ a.toNat + 2 then [((a.toNat + b.toNat) / 2).toUInt8]
      else if b.toNat = a.toNat + 1 then a :: above as
      else a :: go as bs

/-- `n` positions, evenly spread, in order. -/
def spread (n : Nat) : List Position :=
  (List.range n).map fun i =>
    let v := 65536 * (i + 1) / (n + 1)
    let hi := (v / 256).toUInt8
    let lo := (v % 256).toUInt8
    if lo = 0 then [hi] else [hi, lo]

end Position

inductive Value where
  | cell (id : CellId)
  | blob (bytes : List UInt8)
  | list (items : List (Position × Value))
  | record (fields : List (CellId × Value))
  deriving BEq, Inhabited

/-- A step from a value to one inside it: a record's field, a list's
element, or from a cell to its definition. -/
inductive Step where
  | key (label : CellId)
  | element (position : Position)
  | follow
  deriving BEq, Inhabited

abbrev Path := List Step

namespace Value

/-- A record's field. -/
def field? : Value → CellId → Option Value
  | .record fields, label => (fields.find? (·.1 == label)).map (·.2)
  | _, _ => none

/-- A record with a field set, its fields kept in label order. -/
def setField (fields : List (CellId × Value)) (label : CellId) (v : Value) : List (CellId × Value) :=
  match fields with
  | [] => [(label, v)]
  | (l, w) :: rest =>
    match compare label l with
    | .lt => (label, v) :: (l, w) :: rest
    | .eq => (label, v) :: rest
    | .gt => (l, w) :: setField rest label v

/-- A list with an element set at a position, its elements kept in order. -/
def setElement (items : List (Position × Value)) (p : Position) (v : Value) : List (Position × Value) :=
  match items with
  | [] => [(p, v)]
  | (q, w) :: rest =>
    if p == q then (p, v) :: rest
    else if Position.lt p q then (p, v) :: (q, w) :: rest
    else (q, w) :: setElement rest p v

/-- The value one step in, within one definition: a `follow` isn't taken
here. -/
def step? : Value → Step → Option Value
  | v, .key label => v.field? label
  | .list items, .element p => (items.find? (·.1 == p)).map (·.2)
  | _, _ => none

/-- The value along steps that stay in one definition. -/
def at? (v : Value) : List Step → Option Value
  | [] => some v
  | s :: rest => (v.step? s).bind (·.at? rest)

/-- The value with the one a step in set: a field or an element is added
or replaced; a step that doesn't fit declines. -/
def setStep : Value → Step → Value → Option Value
  | .record fields, .key label, new => some (.record (setField fields label new))
  | .list items, .element p, new => some (.list (setElement items p new))
  | _, _, _ => none

/-- The value without the one a step in. -/
def withoutStep : Value → Step → Option Value
  | .record fields, .key label => some (.record (fields.filter (·.1 != label)))
  | .list items, .element p => some (.list (items.filter (·.1 != p)))
  | _, _ => none

/-- The value with the one along the steps set: the last step adds or
replaces; a container missing on the way declines. -/
def set (v : Value) : List Step → Value → Option Value
  | [], new => some new
  | [s], new => v.setStep s new
  | s :: rest, new => do
    let inner ← (← v.step? s).set rest new
    v.setStep s inner

/-- The value without the one along the steps; nothing there declines. -/
def without (v : Value) : List Step → Option Value
  | [] => none
  | [s] => v.withoutStep s
  | s :: rest => do
    let inner ← (← v.step? s).without rest
    v.setStep s inner

end Value

instance : Ord CellId := inferInstance

structure Document where
  root : Option Value := none
  cells : Std.TreeMap CellId Value := {}
  deriving Inhabited

/-- A place a write lands: the root, or a cell's definition, then steps that
stay within it. -/
inductive Start where
  | root
  | cell (id : CellId)
  deriving BEq, Inhabited

structure Location where
  start : Start
  steps : List Step
  deriving BEq, Inhabited

namespace Document

/-- A cell's definition, if it has one. -/
def definition? (d : Document) (c : CellId) : Option Value := d.cells.get? c

/-- The value along a path from the root, following cells to their
definitions where the path says. -/
def at? (d : Document) (path : Path) : Option Value :=
  go d.root path
where
  go : Option Value → Path → Option Value
    | v, [] => v
    | some (.cell c), .follow :: rest => go (d.definition? c) rest
    | some v, s :: rest => go (v.step? s) rest
    | none, _ :: _ => none

/-- Splits a path at its last `follow`: the steps to the cell it follows,
and the steps after, within that cell's definition. -/
def splitLast (path : Path) : Option (Path × List Step) :=
  let rec go (before : Path) : Path → Option (Path × List Step) → Option (Path × List Step)
    | [], found => found
    | .follow :: rest, _ => go (before ++ [.follow]) rest (some (before, rest))
    | s :: rest, found => go (before ++ [s]) rest found
  go [] path none

/-- Where a write along a path lands: in the definition of the last cell
the path follows, or under the root. -/
def location? (d : Document) (path : Path) : Option Location :=
  match splitLast path with
  | none => some ⟨.root, path⟩
  | some (toCell, steps) =>
    match d.at? toCell with
    | some (.cell c) => some ⟨.cell c, steps⟩
    | _ => none

/-- The value at a location's start. -/
def startValue? (d : Document) : Start → Option Value
  | .root => d.root
  | .cell c => d.definition? c

def setStart (d : Document) : Start → Option Value → Document
  | .root, v => { d with root := v }
  | .cell c, some v => { d with cells := d.cells.insert c v }
  | .cell c, none => { d with cells := d.cells.erase c }

/-- The document with the value at a location set. -/
def setAt (d : Document) (l : Location) (v : Value) : Option Document :=
  match l.steps with
  | [] => some (d.setStart l.start (some v))
  | steps => do
    let inner ← (← d.startValue? l.start).set steps v
    return d.setStart l.start (some inner)

/-- The document without the value at a location: an element or a field
goes; at a cell, its definition goes; at the root, the document empties. -/
def deleteAt (d : Document) (l : Location) : Option Document :=
  match l.steps with
  | [] => some (d.setStart l.start none)
  | steps => do
    let inner ← (← d.startValue? l.start).without steps
    return d.setStart l.start (some inner)

/-- Sets the value along a path from the root. -/
def set (d : Document) (path : Path) (v : Value) : Option Document :=
  (d.location? path).bind (d.setAt · v)

/-- Deletes the value along a path from the root. -/
def delete (d : Document) (path : Path) : Option Document :=
  (d.location? path).bind d.deleteAt

end Document

end Progred
