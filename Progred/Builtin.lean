import Progred.Kinds

/-!
The library every document can refer to: names for the vocabulary's cells,
the kinds with their fields in order, the booleans, and the functions Lean
supplies, each with its parameters as cells of its own, since a call labels
its arguments by them.
-/

namespace Progred.Builtin

open Progred

/-- A function Lean supplies: its cell, name, parameters, and the symbol it
is written with between two arguments, if it has one. What it means is in
`Progred/Skinny.lean`. -/
structure Function where
  id : CellId
  name : String
  params : List (CellId × String)
  symbol : Option String := none

/-! The layout functions' cells: a projection is written with them, and a
layout is read by them. -/
namespace Layout
def row := cell! "87d4e055430f84ab00140f2934f1d77f"
def rowChildren := cell! "d23374931e8a0492a265f0a872b515a8"
def column := cell! "2e90a071a682ebdd84ed6593b81538a8"
def columnChildren := cell! "d887d8d49571e6040a69e35e0e27fd0d"
def indent := cell! "c0e58ffb89f6e2713e40bff7475e8b73"
def indentChild := cell! "402c8c7f1c0d1e103ab3044a7ae93729"
def either := cell! "e24ae9b61d89db4f2b470dfcf317ffd2"
def eitherChildren := cell! "c070b8abdd234f8729e424cd01030ef0"
def words := cell! "fa6f68b37b42c5e9ed2fd9a7dbb91bc3"
def wordsContent := cell! "a8c7d9ed588d9a78dc2293c3d0e57052"
def faint := cell! "709f8d0e2fbed1e7c95b11adcbebbae3"
def faintContent := cell! "c5888843bed3e0f22edda8c069dee4e5"
def part := cell! "649d359c0bed68672c1f858fcbead6e6"
def partField := cell! "3fc73f4c701f738a54d287f7c68c5c76"
def field := cell! "bb9223322426dfef9326bdb5338de48f"
def fieldOf := cell! "9881f391f8fa5680968816745943b9b1"
def fieldLabel := cell! "36fb69343d13af3580e93157be400755"
end Layout

/-- The parameters that take a field's label, the cell itself, and not a
value. -/
def labelParams : List CellId := [Layout.partField, Layout.fieldLabel]

def functions : List Function := [
  ⟨cell! "6f49af7620696d771b7a9d00550795aa", "add",
    [(cell! "558b23a7bb86b251e9510f6da7aab770", "a"), (cell! "42cec7db784ab28ee617b5479bc46b7f", "b")], some "+"⟩,
  ⟨cell! "5c243e29c0dc824d2a78d8b46e5a42af", "subtract",
    [(cell! "f872895549eae8966eac4e46304b15dd", "a"), (cell! "292c41a1c52e76eb5f04464b19b20dac", "b")], some "-"⟩,
  ⟨cell! "a5e0524516e0966327d76d7dfee47ee3", "multiply",
    [(cell! "64965964de931ab59e57d658d7cbb1d2", "a"), (cell! "8c3a3aa08880dc6fa7e111a73a8af08f", "b")], some "×"⟩,
  ⟨cell! "d4b512c569b9a748aa2abf6c598fe557", "divide",
    [(cell! "b0acc6bc69597e0aabffce6d15e72eb0", "a"), (cell! "a9f66532b69243e9fd5c9ac80dbac051", "b")], some "/"⟩,
  ⟨cell! "cddd1a74c114f674ec71b2d166982832", "remainder",
    [(cell! "0ad69228f7509b12b3e1cd66e3056f92", "a"), (cell! "66f4f001840177dbe7028e46ea0f2a32", "b")], some "%"⟩,
  ⟨cell! "5a3d7f2620768e2f4091ea5a3c5945b9", "equals",
    [(cell! "3efad80789625401ff13e7ebb4073278", "a"), (cell! "e31588c22413a8762b8ca8447ee8a52a", "b")], some "="⟩,
  ⟨cell! "52f0e07d1cfc16566cca1312eea62a61", "less",
    [(cell! "c24095f003029f925b615adc8f66e6b4", "a"), (cell! "314686a255eec23af4a3c8b912e7b9f4", "b")], some "<"⟩,
  ⟨cell! "c9bcba42f991272425a1f4cf1788e989", "and",
    [(cell! "e5035be822167e31cee1b026a2dd605b", "a"), (cell! "c0f47ec864102b44ba9fe384612fcbab", "b")], some "and"⟩,
  ⟨cell! "859d55aa612c190a1d8726857ea8086d", "or",
    [(cell! "af74d4d3a05e494eac2603f649e9b19a", "a"), (cell! "f8b892d5a002345e9fc81b29163b9ed4", "b")], some "or"⟩,
  ⟨cell! "7cdb7721dd7cdab5a936c6c7f3f48f3e", "not",
    [(cell! "9a3431318c7d41497b3fb7d8374d9c2a", "a")], none⟩,
  ⟨cell! "640c5b08f987c238366e77fee5743ebb", "if",
    [(cell! "05c1e64859ace06f98dbd9c21ebc18a6", "condition"), (cell! "1bbb65fdb0cd0cf0ca52394fb183c326", "then"),
     (cell! "dd4b95c3fd1396cd3eca153d02c91008", "else")], none⟩,
  ⟨cell! "ecfc5e40505d0629ac72576b5f381a0c", "append",
    [(cell! "a7fa3cd2d952b21bd9100f99c1d9e35b", "a"), (cell! "13caac88fb91f667f28bfaf5676e8912", "b")], some "++"⟩,
  ⟨cell! "9ce08ff224e0b963a8b060cd1258c5d5", "length",
    [(cell! "7615d405f260010be701d4a33773f22e", "list")], none⟩,
  ⟨cell! "141f511e9c2c741398dd28668cd91715", "map",
    [(cell! "da3c469b81babc2555d0c2aaf69ec39e", "function"), (cell! "a8a1c1760627334080e14cd7dce042f8", "list")], none⟩,
  ⟨cell! "bec32089f717db8d14931ec15fa582be", "filter",
    [(cell! "e42324c9d9af0a20dc4642b0a9e0cd94", "function"), (cell! "71a7837f86039fd6930f9be5e3df2e25", "list")], none⟩,
  ⟨cell! "e9c4b25db76c04691a03a96d1abb953e", "fold",
    [(cell! "0d78bdc8be6d0ec4b92039afe99b249a", "function"), (cell! "cf06b748880156e3700e11f5afccf072", "start"),
     (cell! "a01cd4f036ff25feee0e4a253220a697", "list")], none⟩,
  ⟨cell! "9111cd7fd2e79bff65af8a17bd502b43", "range",
    [(cell! "bebdfe51128bddbdbb8fd42be24f28d8", "count")], none⟩,
  ⟨cell! "c8347cfca879562783d426f91328b1b8", "show",
    [(cell! "1b0a5cf30adcf0547bf4c6f7efffeec8", "value")], none⟩,
  ⟨cell! "8be94c0287981cd16f6d25f77b85e93c", "Nat", [], none⟩,
  ⟨cell! "0d405b903c2338e928fff8e976d74621", "Int", [], none⟩,
  ⟨cell! "4cfc5800e5940f5dea841a236f283576", "Float", [], none⟩,
  ⟨cell! "f953a0df54162c0d6fdb690320968553", "Text", [], none⟩,
  ⟨cell! "7ee4139cae4cf234fba954832c22a407", "Bool", [], none⟩,
  ⟨cell! "c49f205d823111a4b541e0f0063b64d6", "List", [(cell! "59295ade0021750cc016eadbaec6ea5b", "of")], none⟩,
  ⟨cell! "81b580321520669dd1221762362c250e", "Function",
    [(cell! "1d7791fc69fd20edc9d50a4e4b447125", "from"), (cell! "50d7adfc82af458f8422c320398b9781", "to")], some "→"⟩,
  ⟨Layout.row, "row", [(Layout.rowChildren, "children")], none⟩,
  ⟨Layout.column, "column", [(Layout.columnChildren, "children")], none⟩,
  ⟨Layout.indent, "indent", [(Layout.indentChild, "child")], none⟩,
  ⟨Layout.either, "either", [(Layout.eitherChildren, "children")], none⟩,
  ⟨Layout.words, "words", [(Layout.wordsContent, "content")], none⟩,
  ⟨Layout.faint, "faint", [(Layout.faintContent, "content")], none⟩,
  ⟨Layout.part, "part", [(Layout.partField, "field")], none⟩,
  ⟨Layout.field, "field", [(Layout.fieldOf, "of"), (Layout.fieldLabel, "field")], none⟩,
  ⟨cell! "317149e7a11a128fcf663593380515ed", "number", [(cell! "c356e0d7e31a4859fa5b10c9b2cc2675", "of")], none⟩,
  ⟨cell! "a8e0ae90f569e8485cf51e759233a475", "count", [(cell! "51c60f7e8df75bfb1cd1b7c8a8011323", "of")], none⟩,
  ⟨cell! "1f69ef36f064749137baf0e16c170696", "content", [(cell! "afc20324d18afae369e9409eba08b433", "of")], none⟩,
  ⟨cell! "162cdf43aabfe4ec36ec8925f59067a2", "repeat",
    [(cell! "44e5289c4c5811d5642389a427b22afe", "text"), (cell! "c126ee6e7b3a61db2f83596c8cf17ecc", "count")], none⟩]

/-- Whether a function is a type, or makes one. -/
def Function.isType (f : Function) : Bool :=
  ["Nat", "Int", "Float", "Text", "Bool", "List", "Function"].contains f.name

def function? (c : CellId) : Option Function := functions.find? (·.id == c)

def named (name : String) : Value := .record [(Kinds.name, Value.text name)]

/-- A kind's definition: its name and its fields, in the order its records
show them. -/
def kind (name : String) (fields : List CellId) : Value :=
  Value.ofKind Kinds.def_
    [(Kinds.name, Value.text name), (Kinds.fields, .list ((Position.spread fields.length).zip (fields.map .cell)))]

/-- The kinds, in the order a new value's offers list them. -/
def kinds : List (CellId × Value) := [
  (Kinds.evaluation, kind "evaluation" [Kinds.expression]),
  (Kinds.valueWrapper, kind "value wrapper" [Kinds.name, Kinds.value]),
  (Kinds.lambda, kind "lambda" [Kinds.name, Kinds.params, Kinds.body]),
  (Kinds.call, kind "call" [Kinds.function]),
  (Kinds.section_, kind "section" [Kinds.name, Kinds.sectionBody]),
  (Kinds.notebook, kind "notebook" [Kinds.entries]),
  (Kinds.def_, kind "def" [Kinds.name, Kinds.fields, Kinds.projection]),
  (Kinds.library, kind "library" [Kinds.name, Kinds.defs, Kinds.functions])]

def library : Library :=
  kinds ++ [
    (Kinds.isa, named "isa"), (Kinds.bytes, named "bytes"), (Kinds.name, named "name"),
    (Kinds.text, named "text"), (Kinds.f64, named "f64"), (Kinds.u64, named "u64"), (Kinds.bool, named "bool"),
    (Kinds.fields, named "fields"), (Kinds.defs, named "defs"), (Kinds.functions, named "functions"),
    (Kinds.entries, named "entries"), (Kinds.sectionBody, named "body"),
    (Kinds.params, named "params"), (Kinds.body, named "body"), (Kinds.function, named "function"),
    (Kinds.value, named "value"), (Kinds.expression, named "expression"),
    (Kinds.leanFunction, named "lean function"), (Kinds.type_, named "type"), (Kinds.returns, named "returns"),
    (Kinds.projection, named "projection"),
    (Kinds.true_, Value.ofKind Kinds.valueWrapper
      [(Kinds.name, Value.text "true"), (Kinds.value, Value.literal Kinds.bool [1])]),
    (Kinds.false_, Value.ofKind Kinds.valueWrapper
      [(Kinds.name, Value.text "false"), (Kinds.value, Value.literal Kinds.bool [0])])]
  ++ functions.flatMap fun f =>
    (f.id, Value.ofKind Kinds.leanFunction
      [(Kinds.name, Value.text f.name),
       (Kinds.params, .list ((Position.spread f.params.length).zip (f.params.map (.cell ·.1))))])
    :: f.params.map fun (c, n) => (c, named n)

end Progred.Builtin
