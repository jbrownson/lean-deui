import Lean
import Progred.Builtin
import Progred.Display
import Progred.Run

/-!
The document's expressions as Lean: a value becomes Lean `Syntax`, built
with quotations, never text. A text, a number or a boolean is its literal;
a list is a list; a lambda is `fun`; a call applies its function to its
arguments in its parameters' order; a cell that is a lambda's parameter is
its variable; a cell defined as a lambda or a value wrapper is a
definition, elaborated before what uses it; a function Lean supplies is
its Lean. Each node is tagged with a number, so an error comes back at the
value it's about.
-/

namespace Progred.ToLean

open Lean Progred

/-- What went wrong, at a node: 0 for none. -/
structure Failure where
  node : Nat
  message : String

structure State where
  /-- How many nodes have been numbered. -/
  nodes : Nat := 0
  /-- The definitions needed, in the order they're elaborated. -/
  commands : Array Syntax := #[]
  defined : List CellId := []
  defining : List CellId := []

abbrev M := StateT State (ExceptT Failure Unhygienic)

def fail {α : Type} (node : Nat) (message : String) : M α := throw ⟨node, message⟩

def node : M Nat := modifyGet fun s => (s.nodes + 1, { s with nodes := s.nodes + 1 })

def ident (pre : String) (c : CellId) : Ident := mkIdent (Name.mkSimple (pre ++ c.hex))

/-- What a function Lean supplies is, of its arguments. -/
def supplied (name : String) (args : Array Term) : M Term := do
  match name, args with
  | "add", #[a, b] => `(($a + $b))
  | "subtract", #[a, b] => `(($a - $b))
  | "multiply", #[a, b] => `(($a * $b))
  | "divide", #[a, b] => `(($a / $b))
  | "remainder", #[a, b] => `(($a % $b))
  | "equals", #[a, b] => `(($a == $b))
  | "less", #[a, b] => `((decide ($a < $b)))
  | "and", #[a, b] => `(($a && $b))
  | "or", #[a, b] => `(($a || $b))
  | "not", #[a] => `((!$a))
  | "if", #[c, t, e] => `((if $c then $t else $e))
  | "append", #[a, b] => `(($a ++ $b))
  | "length", #[l] => `((List.length $l))
  | "map", #[f, l] => `((List.map $f $l))
  | "filter", #[f, l] => `((List.filter $f $l))
  | "fold", #[f, s, l] => `((List.foldl $f $s $l))
  | "range", #[n] => `((List.range $n))
  | "show", #[v] => `((toString $v))
  | _, _ => fail 0 s!"Lean has no function {name} of {args.size} arguments"

variable (doc : Document) (lib : Library)

def cellsOf : Option Value → List CellId
  | some (.list items) => items.filterMap fun (_, v) => match v with | .cell c => some c | _ => none
  | _ => []

mutual

/-- A value as a Lean term. `bound` are the parameters in scope. -/
partial def term (bound : List CellId) (v : Value) : M Term := do
  let n ← node
  let tagged (t : Term) : Term := ⟨Run.tagOuter n t.raw⟩
  match v with
  | .cell c =>
    if bound.contains c then return tagged (ident "p_" c)
    match doc.lookup? lib c with
    | none => fail n s!"{doc.shown lib c} has no definition"
    | some d =>
      if d.kind? == some Kinds.lambda || d.kind? == some Kinds.valueWrapper then
        define c d
        return tagged (ident "d_" c)
      else if d.kind? == some Kinds.leanFunction then
        -- A supplied function, as a value: a function of its parameters.
        match Builtin.function? c with
        | some f =>
          let params := f.params.map fun (p, _) => ident "p_" p
          let body ← supplied f.name (params.map fun (p : Ident) => (⟨p.raw⟩ : Term)).toArray
          return tagged (← `(fun $(params.toArray)* => $body))
        | none => fail n s!"{doc.shown lib c} isn't a function Lean supplies"
      else
        match d with
        | .record [(l, _)] =>
          if l == Kinds.name then fail n s!"{doc.shown lib c} is only a name: it has no value" else term bound d
        | _ => term bound d
  | .blob _ => fail n "a blob isn't an expression"
  | .list items => do
    let parts ← items.mapM fun (_, x) => term bound x
    return tagged (← `([$(parts.toArray),*]))
  | .record _ =>
    if let some s := v.text? then return tagged ⟨Syntax.mkStrLit s⟩
    if let some k := v.u64? then return tagged ⟨Syntax.mkNumLit (toString k)⟩
    if let some x := v.f64? then
      return tagged (← `((Float.ofBits $(⟨Syntax.mkNumLit (toString x.toBits.toNat)⟩))))
    if v.literal? Kinds.bool == some [1] then return tagged (← `(true))
    if v.literal? Kinds.bool == some [0] then return tagged (← `(false))
    match v.kind? with
    | some k =>
      if k == Kinds.lambda then
        let params := cellsOf (v.field? Kinds.params)
        match v.field? Kinds.body with
        | none => fail n "a lambda needs a body"
        | some b =>
          let body ← term (params ++ bound) b
          if params.isEmpty then return tagged body
          return tagged (← `(fun $((params.map (ident "p_")).toArray)* => $body))
      else if k == Kinds.call then call bound n v
      else if k == Kinds.valueWrapper then
        match v.field? Kinds.value with
        | some x => term bound x
        | none => fail n "this has no value yet"
      else if k == Kinds.evaluation then
        match v.field? Kinds.expression with
        | some x => term bound x
        | none => fail n "an evaluation needs an expression"
      else fail n s!"a {doc.shown lib k} isn't an expression"
    | none => fail n "a record isn't an expression"

/-- A call: its function applied to its arguments, in the order of the
function's parameters. -/
partial def call (bound : List CellId) (n : Nat) (v : Value) : M Term := do
  let tagged (t : Term) : Term := ⟨Run.tagOuter n t.raw⟩
  match v.field? Kinds.function with
  | none => fail n "a call needs a function"
  | some fn =>
    let target := match fn with
      | .cell c => (doc.lookup? lib c).map (c, ·)
      | _ => none
    let params := match target with
      | some (_, d) => cellsOf (d.field? Kinds.params)
      | none => []
    let args ← params.mapM fun p =>
      match v.field? p with
      | some a => term bound a
      | none => fail n s!"no {doc.shown lib p} given"
    match target with
    | some (c, d) =>
      if d.kind? == some Kinds.leanFunction then
        match Builtin.function? c with
        | some f => return tagged (← supplied f.name args.toArray)
        | none => fail n s!"{doc.shown lib c} isn't a function Lean supplies"
      else
        let f ← term bound fn
        return tagged (← `(($f $(args.toArray)*)))
    | none =>
      let f ← term bound fn
      return tagged f

/-- A cell's definition as a Lean definition, elaborated once, before what
uses it. -/
partial def define (c : CellId) (d : Value) : M Unit := do
  let s ← get
  if s.defined.contains c then return
  if s.defining.contains c then
    fail 0 s!"{doc.shown lib c} is defined by way of itself, which isn't supported yet"
  modify fun s => { s with defining := c :: s.defining }
  let body ← term [] d
  let command ← `(command| def $(ident "d_" c) := $body)
  modify fun s => { s with commands := s.commands.push command, defined := c :: s.defined }

end

/-- An expression as Lean: the definitions it needs, in order, and its
term; or what's wrong with it. -/
def convert (expression : Value) : Except Failure (Array Syntax × Syntax) :=
  match Unhygienic.run ((term doc lib [] expression).run {}).run with
  | .ok (t, s) => .ok (s.commands, t.raw)
  | .error f => .error f

/-- Every evaluation's expression in a value. -/
partial def expressionsIn : Value → List Value
  | .cell _ | .blob _ => []
  | .list items => items.flatMap fun (_, v) => expressionsIn v
  | v@(.record fields) =>
    (if v.kind? == some Kinds.evaluation then (v.field? Kinds.expression).toList else []) ++
      fields.flatMap fun (_, w) => expressionsIn w

/-- Every evaluation's expression in a document. -/
def expressions : List Value :=
  ((doc.root.map expressionsIn).getD [] ++ doc.cells.toList.flatMap fun (_, v) => expressionsIn v).eraseDups

end Progred.ToLean
