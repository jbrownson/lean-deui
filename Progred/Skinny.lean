import Lean
import Progred.Builtin
import Progred.Display
import Progred.Run
import Progred.Prelude

/-!
Skinny: the subset of Lean a document is written in. A value becomes Lean
`Syntax`, built with quotations, never text. A text, a number or a boolean is its literal;
a list is a list; a lambda is `fun`; a call applies its function to its
arguments in its parameters' order; a cell that is a lambda's parameter is
its variable; a cell defined as a lambda or a value wrapper is a
definition, elaborated before what uses it; a function Lean supplies is
its Lean. A parameter may have a type and a lambda what it returns, which
are expressions like any other; a definition that refers to itself needs
them, and is a `partial def`. Each node is tagged with a number, so an
error comes back at the value it's about.
-/

namespace Progred.Skinny

open Lean Progred

/-- What went wrong, at a node: 0 for none. -/
structure Failure where
  node : Nat
  message : String

/-- Where a node's value is: its path from the expression, if it's in the
expression and not in a definition it uses. -/
abbrev Where := Option Path

structure State where
  /-- Where each numbered node's value is: node `n` is at `nodes[n - 1]`. -/
  nodes : Array Where := #[]
  /-- The definitions needed, in the order they're elaborated. -/
  commands : Array Syntax := #[]
  defined : List CellId := []
  /-- The definitions being made, innermost first, and those found to refer
  to themselves. -/
  defining : List CellId := []
  recursive : List CellId := []

abbrev M := StateT State (ExceptT Failure Unhygienic)

def fail {α : Type} (node : Nat) (message : String) : M α := throw ⟨node, message⟩

def node (at_ : Where) : M Nat := modifyGet fun s => (s.nodes.size + 1, { s with nodes := s.nodes.push at_ })

/-- A step further in, where there's a path. -/
def into (at_ : Where) (steps : List Step) : Where := at_.map (· ++ steps)

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
  | "Nat", #[] => `(Nat)
  | "Int", #[] => `(Int)
  | "Float", #[] => `(Float)
  | "Text", #[] => `(String)
  | "Bool", #[] => `(Bool)
  | "List", #[a] => `((List $a))
  | "Function", #[a, b] => `(($a → $b))
  | "row", #[c] => `((Progred.Prelude.row $c))
  | "column", #[c] => `((Progred.Prelude.column $c))
  | "indent", #[c] => `((Progred.Prelude.indent $c))
  | "either", #[c] => `((Progred.Prelude.either $c))
  | "words", #[t] => `((Progred.Prelude.words $t))
  | "faint", #[t] => `((Progred.Prelude.faint $t))
  | "part", #[l] => `((Progred.Prelude.part $l))
  | "field", #[v, l] => `((Progred.Prelude.field $v $l))
  | "number", #[v] => `((Progred.Prelude.number $v))
  | "count", #[v] => `((Progred.Prelude.count $v))
  | "content", #[v] => `((Progred.Prelude.content $v))
  | "repeat", #[t, n] => `((String.join (List.replicate $n $t)))
  | _, _ => fail 0 s!"Lean has no function {name} of {args.size} arguments"

variable (doc : Document) (lib : Library)

def cellsOf : Option Value → List CellId
  | some (.list items) => items.filterMap fun (_, v) => match v with | .cell c => some c | _ => none
  | _ => []

mutual

/-- A value as a Lean term. `bound` are the parameters in scope. -/
partial def term (bound : List CellId) (at_ : Where) (v : Value) : M Term := do
  let n ← node at_
  let tagged (t : Term) : Term := ⟨Run.tagOuter n t.raw⟩
  match v with
  | .cell c =>
    if bound.contains c then return tagged (ident "p_" c)
    match doc.lookup? lib c with
    | none => fail n s!"{doc.shown lib c} has no definition"
    | some d =>
      if d.kind? == some Kinds.lambda || d.kind? == some Kinds.valueWrapper then
        let s ← get
        if s.defining.head? == some c then
          -- The definition being made, within itself.
          modify fun s => { s with recursive := c :: s.recursive }
        else if s.defining.contains c then
          fail n s!"{doc.shown lib c} is defined by way of another definition that uses it, which isn't supported yet"
        else define c d
        return tagged (ident "d_" c)
      else if d.kind? == some Kinds.leanFunction then
        -- A supplied function, as a value: a function of its parameters.
        match Builtin.function? c with
        | some f =>
          let params := f.params.map fun (p, _) => ident "p_" p
          let body ← supplied f.name (params.map fun (p : Ident) => (⟨p.raw⟩ : Term)).toArray
          if params.isEmpty then return tagged body
          return tagged (← `(fun $(params.toArray)* => $body))
        | none => fail n s!"{doc.shown lib c} isn't a function Lean supplies"
      else
        match d with
        | .record [(l, _)] =>
          if l == Kinds.name then fail n s!"{doc.shown lib c} is only a name: it has no value"
          else term bound (into at_ [.follow]) d
        | _ => term bound (into at_ [.follow]) d
  | .blob _ => fail n "a blob isn't an expression"
  | .list items => do
    let parts ← items.mapM fun (p, x) => term bound (into at_ [.element p]) x
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
          let body ← term (params ++ bound) (into at_ [.key Kinds.body]) b
          let body ← match v.field? Kinds.returns with
            | some r => do
              let type ← term bound (into at_ [.key Kinds.returns]) r
              `(($body : $type))
            | none => pure body
          if params.isEmpty then return tagged body
          let binders ← params.mapM fun p => do
            match ← paramType bound p with
            | some type => `(Lean.Parser.Term.funBinder| ($(ident "p_" p) : $type))
            | none => `(Lean.Parser.Term.funBinder| $(ident "p_" p):ident)
          return tagged (← `(fun $(binders.toArray)* => $body))
      else if k == Kinds.call then call bound at_ n v
      else if k == Kinds.valueWrapper then
        match v.field? Kinds.value with
        | some x => term bound (into at_ [.key Kinds.value]) x
        | none => fail n "this has no value yet"
      else if k == Kinds.evaluation then
        match v.field? Kinds.expression with
        | some x => term bound (into at_ [.key Kinds.expression]) x
        | none => fail n "an evaluation needs an expression"
      else fail n s!"a {doc.shown lib k} isn't an expression"
    | none => fail n "a record isn't an expression"

/-- A call: its function applied to its arguments, in the order of the
function's parameters. -/
partial def call (bound : List CellId) (at_ : Where) (n : Nat) (v : Value) : M Term := do
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
      | some a =>
        if Builtin.labelParams.contains p then
          -- A field's label is the cell itself: its id goes across.
          match a with
          | .cell c => pure (⟨Syntax.mkStrLit c.hex⟩ : Term)
          | _ => fail n s!"{doc.shown lib p} takes a field's label"
        else term bound (into at_ [.key p]) a
      | none => fail n s!"no {doc.shown lib p} given"
    match target with
    | some (c, d) =>
      if d.kind? == some Kinds.leanFunction then
        match Builtin.function? c with
        | some f => return tagged (← supplied f.name args.toArray)
        | none => fail n s!"{doc.shown lib c} isn't a function Lean supplies"
      else
        let f ← term bound (into at_ [.key Kinds.function]) fn
        return tagged (← `(($f $(args.toArray)*)))
    | none =>
      let f ← term bound (into at_ [.key Kinds.function]) fn
      return tagged f

/-- A parameter's type, if its definition gives one. -/
partial def paramType (bound : List CellId) (p : CellId) : M (Option Term) := do
  match (doc.lookup? lib p).bind (·.field? Kinds.type_) with
  | some type => return some (← term bound none type)
  | none => return none

/-- A cell's definition as a Lean definition, elaborated once, before what
uses it. One that refers to itself is a `partial def`, which needs its
parameters' types and what it returns. -/
partial def define (c : CellId) (d : Value) : M Unit := do
  if (← get).defined.contains c then return
  modify fun s => { s with defining := c :: s.defining }
  let body ← term [] none d
  let command ←
    if (← get).recursive.contains c then
      let params := cellsOf (d.field? Kinds.params)
      let types ← params.mapM fun p => paramType [] p
      let returns ← match d.field? Kinds.returns with
        | some r => some <$> term [] none r
        | none => pure none
      match returns, d.field? Kinds.body, d.kind? == some Kinds.lambda && types.all (·.isSome) with
      | some returns, some b, true =>
        let inner ← term params none b
        let binders ← (params.zip types).mapM fun (p, type) =>
          `(Lean.Parser.Term.bracketedBinderF| ($(ident "p_" p) : $(type.getD ⟨.missing⟩)))
        `(command| partial def $(ident "d_" c) $(binders.toArray)* : $returns := $inner)
      | _, _, _ =>
        fail 0 s!"{doc.shown lib c} refers to itself, so its parameters and what it returns need types"
    else `(command| def $(ident "d_" c) := $body)
  modify fun s =>
    { s with commands := s.commands.push command, defined := c :: s.defined, defining := s.defining.erase c }

end

/-- An expression as Lean: the definitions it needs, in order, its term,
and where each numbered node's value is; or what's wrong with it. -/
def convert (expression : Value) : Except Failure (Array Syntax × Syntax × Array Where) :=
  match Unhygienic.run ((term doc lib [] (some []) expression).run {}).run with
  | .ok (t, s) => .ok (s.commands, t.raw, s.nodes)
  | .error f => .error f

/-- A projection that's a function, as Lean: the definitions it needs, and
its term, a function from a record to its layout. -/
def function (projection : Value) : Except Failure (Array Syntax × Syntax) :=
  let made : M Term := do
    let f ← term doc lib [] none projection
    `(($f : Progred.Value → Progred.Value))
  match Unhygienic.run (made.run {}).run with
  | .ok (t, s) => .ok (s.commands, t.raw)
  | .error f => .error f

/-- Every evaluation's expression in a document. -/
def expressions : List Value :=
  ((doc.root.map Display.expressionsIn).getD [] ++ doc.cells.toList.flatMap fun (_, v) => Display.expressionsIn v).eraseDups

end Progred.Skinny
