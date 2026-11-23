import Progred.Gid

/-!
The conventions on top of GID: kinds, literals and names, as fixed cells.
The ids are the Rust Progred's, so its files read here. A record's kind is
its `isa` field. A literal is a record of a kind with its `bytes`: text is
UTF-8, a number 8 little-endian bytes. A cell's name is the `name` field of
its definition.
-/

namespace Progred

/-- A fixed cell, from its 32 hex digits. -/
def cell! (hex : String) : CellId := (CellId.ofHex? hex).getD default

namespace Kinds

def isa := cell! "dbd7e1a38e30425fb1b408b2e446bb1b"
def bytes := cell! "fe06bf0459d2598aa29b30302e3b29b8"
def text := cell! "332529b8ea83a7ba10fd7f6d942e5016"
def f64 := cell! "ed11fde03b7c2c1ba2fccc3cdba5d561"
def u64 := cell! "fc77282178c2fa31b80aed2b8b6f7888"
def bool := cell! "b2d13b64336a9e808133d0c7d5e4981e"
def true_ := cell! "04831f9b704935059231eb111770e62e"
def false_ := cell! "8fcc0a2e5f26c72efd9e917a28919801"
def name := cell! "02e562654d6d0828d3a7559e6f75fffe"
def def_ := cell! "a9a53af4187f4715f1eebdf58e0c65c0"
def fields := cell! "003bb68cfb673326a483cd31b03ba27f"
def library := cell! "6a2a379c9d9553cedafcb3987e7891b7"
def defs := cell! "9c1a4dd291087eef39ac1d4020380ed0"
def functions := cell! "6a6a803312ecf3a652470a7cd2a9abcf"
def notebook := cell! "9111dde9a00f4106a817720187b45645"
def entries := cell! "26b6e7f1fc0d482da89e2a4835d2f789"
def section_ := cell! "9d30242da6ce9d5736c24e2adbd820ff"
def sectionBody := cell! "ac7cc432940c7cc64b315a5581108930"
def lambda := cell! "e4a0653134ca48379cab2e008bed03e7"
def params := cell! "195b378d0d31d90ab0d7366c15346b70"
def body := cell! "986143866eda2e2fbf9ab8484357a0c9"
def call := cell! "8dd318828a4c42cf9f2d5d1ba9b068fe"
def function := cell! "751fca4373debdd0b7e6eb73e08d684b"
def valueWrapper := cell! "f615f8d777294ffd9e5296faf34edd9d"
def value := cell! "5adde9ececa6ad57c81a3b2907e75e08"
def evaluation := cell! "549dd85073474d6296d773c8df9c0526"
def expression := cell! "ccc55b0eb63b9f564ea74436094d4014"

/-- A function Lean supplies, which the document calls by its cell
(`Progred/Skinny.lean`): `{isa: lean function, name, params}`. New here. -/
def leanFunction := cell! "b8932235933f5a00e98a063a3ff6311d"
/-- How a kind's records are drawn, on the kind's def: a layout, or a
function of the record that gives one. The Rust version's cell. -/
def projection := cell! "873503e2e37a1722a0dd21399be9ee7f"
/-- A parameter's type, on the parameter's definition, and what a lambda
returns, on the lambda: Skinny expressions that are types. New here. -/
def type_ := cell! "c66b9576e877d337b605e9dea35a2c11"
def returns := cell! "6f67b36c0228799e333f2ec9e075a555"

end Kinds

namespace Value

/-- A record's kind: the cell its `isa` holds. -/
def kind? (v : Value) : Option CellId :=
  match v.field? Kinds.isa with
  | some (.cell k) => some k
  | _ => none

/-- A record of a kind, from its other fields. -/
def ofKind (kind : CellId) (fields : List (CellId × Value)) : Value :=
  .record (fields.foldl (fun acc (l, v) => setField acc l v) [(Kinds.isa, .cell kind)])

/-- A literal: a record of a kind with its bytes. -/
def literal (kind : CellId) (bytes : List UInt8) : Value :=
  ofKind kind [(Kinds.bytes, .blob bytes)]

/-- A literal's bytes, if the value is a literal of the kind. -/
def literal? (v : Value) (kind : CellId) : Option (List UInt8) :=
  if v.kind? == some kind then
    match v.field? Kinds.bytes with
    | some (.blob b) => some b
    | _ => none
  else none

def text (s : String) : Value := literal Kinds.text s.toUTF8.toList

def text? (v : Value) : Option String :=
  (v.literal? Kinds.text).bind fun b => String.fromUTF8? (ByteArray.mk b.toArray)

def bytes8 (n : UInt64) : List UInt8 := (List.range 8).map fun i => (n >>> (8 * i).toUInt64).toUInt8

def word8 (b : List UInt8) : UInt64 :=
  ((b.take 8).reverse).foldl (fun acc x => acc <<< 8 ||| x.toUInt64) 0

def u64 (n : Nat) : Value := literal Kinds.u64 (bytes8 n.toUInt64)

def u64? (v : Value) : Option Nat := (v.literal? Kinds.u64).map fun b => (word8 b).toNat

def f64 (x : Float) : Value := literal Kinds.f64 (bytes8 x.toBits)

def f64? (v : Value) : Option Float := (v.literal? Kinds.f64).map fun b => Float.ofBits (word8 b)

end Value

/-- Definitions the program supplies, read-only: cells the document can
refer to but doesn't hold. -/
abbrev Library := List (CellId × Value)

namespace Document

/-- A cell's definition: the document's, else the library's. -/
def lookup? (d : Document) (lib : Library) (c : CellId) : Option Value :=
  (d.definition? c).orElse fun _ => (lib.find? (·.1 == c)).map (·.2)

/-- A cell's name, if its definition has one that isn't empty. -/
def name? (d : Document) (lib : Library) (c : CellId) : Option String :=
  match ((d.lookup? lib c).bind (·.field? Kinds.name)).bind Value.text? with
  | some "" => none
  | n => n

/-- How a cell shows: its name, else `…` and its last 5 hex digits. -/
def shown (d : Document) (lib : Library) (c : CellId) : String :=
  (d.name? lib c).getD c.short

/-- The value along a path from the root, following cells to their
definitions, the library's too. -/
def find? (d : Document) (lib : Library) (path : Path) : Option Value :=
  go d.root path
where
  go : Option Value → Path → Option Value
    | v, [] => v
    | some (.cell c), .follow :: rest => go (d.lookup? lib c) rest
    | some v, s :: rest => go (v.step? s) rest
    | none, _ :: _ => none

/-- Whether a write along a path lands in the document: not in a cell the
library defines. -/
def writable (d : Document) (lib : Library) (path : Path) : Bool :=
  match splitLast path with
  | none => true
  | some (toCell, _) =>
    match d.find? lib toCell with
    | some (.cell c) => !(lib.any (·.1 == c))
    | _ => false

end Document

end Progred
