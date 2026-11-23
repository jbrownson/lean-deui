import Progred.Model
import Progred.GidText
import Deui.App

/-!
Editing: what keys, typing and clicks do to the model. A place with no
value takes what's typed as a query, answered by offers: a number or text
the query reads as, a list, a record or a new cell, a new record of a kind,
or a cell by name. A value drawn as a line (text, a number, a name) is typed
in place. Enter adds a peer, Tab goes to the next place a value can go,
Backspace leaves a hole and then removes it.
-/

namespace Progred.Model

open Progred

/-- One way to fill the place being typed into. -/
structure Offer where
  text : String
  detail : String := ""
  isNew : Bool := false
  /-- The model with the offer taken at the selection. -/
  take : Model → Model

def picker (text : String := "") : Editing := { text, caret := text.length, picker := true }

/-- The model resting on the value at a path. -/
def rest (m : Model) (path : Path) : Model :=
  { m with selection := some { path }, typingRun := false }

/-- The model with a hole open at a path, to be typed into. -/
def openAt (m : Model) (path : Path) (stage : Stage := .pending) (text : String := "") : Model :=
  { m with selection := some { path, stage, editing := some (picker text) }, typingRun := false }

/-- The fields a kind's records show. -/
def fieldsOf (m : Model) (k : CellId) : List CellId :=
  match (m.doc.lookup? m.library k).bind (·.field? Kinds.fields) with
  | some (.list items) => items.filterMap fun (_, v) => match v with | .cell c => some c | _ => none
  | _ => []

/-- A call's function's parameters. -/
def paramsOf (m : Model) (v : Value) : List CellId :=
  match v.field? Kinds.function with
  | some (.cell c) =>
    match (m.doc.lookup? m.library c).bind (·.field? Kinds.params) with
    | some (.list items) => items.filterMap fun (_, p) => match p with | .cell c => some c | _ => none
    | _ => []
  | _ => []

/-- The fields a record has places for: its kind's, and a call's
parameters. -/
def places (m : Model) (v : Value) : List CellId :=
  match v.kind? with
  | some k => if k == Kinds.call then [Kinds.function] ++ paramsOf m v else fieldsOf m k
  | none => []

/-- After a value is written at a path, where the selection goes: into its
first empty place, if it has one, else resting on it. -/
partial def settle (m : Model) (path : Path) : Model :=
  match m.at? path with
  | some (.cell c) =>
    if (m.doc.definition? c).isSome then settle { m with folds := (path, false) :: m.folds } (path ++ [.follow])
    else m.rest path
  | some (.list []) => m.openAt (path ++ [.element (Position.between none none)])
  | some v@(.record fields) =>
    match v.kind? with
    | some _ =>
      match (places m v).find? fun l => (v.field? l).isNone with
      | some l => m.openAt (path ++ [.key l])
      | none =>
        -- A place that's there but empty: a list to fill, as a lambda's body isn't.
        match (places m v).find? fun l => v.field? l == some (.list []) && l != Kinds.params with
        | some l => settle m (path ++ [.key l])
        | none => m.rest path
    | none => if fields.isEmpty then m.openAt path .label else m.rest path
  | _ => m.rest path

/-- The model with a value written at a path, the selection settled in it. -/
def put (m : Model) (path : Path) (v : Value) : Model :=
  match m.doc.set path v with
  | some doc => (m.write doc).settle path
  | none => m

/-- A new record of a kind at a path. A kind that's referred to by name, a
lambda, a value wrapper or a def, is a new cell with the record as its
definition. -/
def putNew (m : Model) (path : Path) (kind : CellId) : Model :=
  let extra : List (CellId × Value) :=
    if kind == Kinds.notebook then [(Kinds.entries, .list [])]
    else if kind == Kinds.section_ then [(Kinds.sectionBody, .list [])]
    else if kind == Kinds.lambda then [(Kinds.params, .list [])]
    else []
  let record := Value.ofKind kind extra
  if kind == Kinds.lambda || kind == Kinds.valueWrapper || kind == Kinds.def_ then
    let (id, m) := m.fresh
    match m.doc.set path (.cell id) with
    | some doc => (m.write { doc with cells := doc.cells.insert id record }).settle path
    | none => m
  else m.put path record

def parseNat? (s : String) : Option Nat := if s.isEmpty then none else s.toNat?

/-- A number with a point, or a sign: `-1`, `2.5`. -/
def parseFloat? (s : String) : Option Float :=
  let (negative, body) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  match body.splitOn "." with
  | [whole] => if negative then (parseNat? whole).map fun n => -(n.toFloat) else none
  | [whole, fraction] =>
    match parseNat? (if whole.isEmpty then "0" else whole), parseNat? (if fraction.isEmpty then "0" else fraction) with
    | some w, some f =>
      let x := w.toFloat + f.toFloat / (10.0 ^ fraction.length.toFloat)
      some (if negative then -x else x)
    | _, _ => none
  | _ => none

/-- Whether an offer's text answers a query: 0 for a prefix, 1 for holding
it, ignoring case, else none. -/
def matchRank (query text : String) : Option Nat :=
  let q := query.toLower
  let t := text.toLower
  if q.isEmpty then some 1
  else if t.startsWith q then some 0
  else if (t.splitOn q).length > 1 then some 1
  else none

/-- The cells a value can refer to by name: the document's named cells, and
the library's values and functions. -/
def namedCells (m : Model) : List (CellId × String × Value) :=
  let doc := m.doc.cells.toList.filterMap fun (c, v) => (m.doc.name? m.library c).map (c, ·, v)
  let lib := m.library.filterMap fun (c, v) =>
    if v.kind? == some Kinds.valueWrapper || v.kind? == some Kinds.leanFunction then
      (m.doc.name? m.library c).map (c, ·, v)
    else none
  doc ++ lib

/-- The kinds a new record can be of: the library's, and the document's
defs. -/
def kindsOffered (m : Model) : List (CellId × String) :=
  (Builtin.kinds.map fun (k, _) => (k, m.doc.shown m.library k)) ++
    m.doc.cells.toList.filterMap fun (c, v) =>
      if v.kind? == some Kinds.def_ then some (c, m.doc.shown m.library c) else none

/-- The offers for a value at a path, answering a query. -/
def valueOffers (m : Model) (path : Path) (query : String) : List Offer :=
  let text (s : String) : Offer := ⟨"\"" ++ s ++ "\"", "text", false, fun m => m.put path (Value.text s)⟩
  if path.getLast? == some (.key Kinds.name) then [text query]
  else if query.startsWith "\"" then [text ((query.drop 1).toString.replace "\"" "")]
  else if path.getLast? == some (.key Kinds.isa) then
    (kindsOffered m).filterMap fun (k, name) =>
      (matchRank query name).map fun _ => ⟨name, "kind", false, fun m => m.put path (.cell k)⟩
  else
    let readings : List Offer :=
      (match parseNat? query with
        | some n => [⟨query, "u64", false, fun m => m.put path (Value.u64 n)⟩]
        | none => []) ++
      (match parseFloat? query with
        | some x => [⟨query, "f64", false, fun m => m.put path (Value.f64 x)⟩]
        | none => [])
    let makers : List Offer := [
      ⟨"list", "[", true, fun m => m.put path (.list [])⟩,
      ⟨"record", "{", true, fun m => m.put path (.record [])⟩,
      ⟨"cell", "(", true, fun m => let (id, m) := m.fresh; m.put path (.cell id)⟩]
    let kinds : List Offer := (kindsOffered m).map fun (k, name) =>
      ⟨name, "kind", true, fun m => m.putNew path k⟩
    let cells : List Offer := (namedCells m).flatMap fun (c, name, v) =>
      let reference : Offer := ⟨name, (v.kind?.map (m.doc.shown m.library)).getD "cell", false,
        fun m => match m.doc.set path (.cell c) with
          | some doc => (m.write doc).rest path
          | none => m⟩
      -- A function with no parameters is a type: there's nothing to call.
      let isType := ((Builtin.function? c).map (·.params.isEmpty)).getD false
      if isType then [{ reference with detail := "type" }]
      else if v.kind? == some Kinds.lambda || v.kind? == some Kinds.leanFunction then
        [⟨name, "call", false, fun m => m.put path (Value.ofKind Kinds.call [(Kinds.function, .cell c)])⟩, reference]
      else [reference]
    -- What's named exactly as typed comes first: a parameter `n` before `notebook`.
    let exact := if query.isEmpty then [] else (cells ++ kinds ++ makers).filter (·.text == query)
    let ranked (rank : Nat) := (makers ++ kinds ++ cells).filter fun o =>
      matchRank query o.text == some rank && (query.isEmpty || o.text != query)
    -- A new cell with the query as its name: how a parameter is made.
    let named : List Offer :=
      if query.isEmpty then []
      else [⟨query, "cell", true, fun m =>
        let (id, m) := m.fresh
        match m.doc.set path (.cell id) with
        | some doc => (m.write { doc with cells := doc.cells.insert id (Builtin.named query) }).rest path
        | none => m⟩]
    -- Among a lambda's parameters, what's typed is first a new parameter's name.
    let inParams := path.dropLast.getLast? == some (.key Kinds.params)
    (if inParams then named ++ exact ++ ranked 0 ++ ranked 1
      else readings ++ exact ++ ranked 0 ++ ranked 1 ++ named) ++
      (if query.isEmpty then [] else [text query])

/-- The offers for a new field's label on the record at a path: its kind's
fields it lacks, the document's cells that are only names, and a new label
named as typed. -/
def labelOffers (m : Model) (path : Path) (query : String) : List Offer :=
  match m.at? path with
  | some v@(.record fields) =>
    let lacks (l : CellId) := !fields.any (·.1 == l)
    let offer (l : CellId) (detail : String) : Option Offer :=
      (matchRank query (m.doc.shown m.library l)).map fun _ =>
        ⟨m.doc.shown m.library l, detail, false, fun m => m.openAt (path ++ [.key l])⟩
    let declared := (places m v).filter lacks |>.filterMap (offer · "field")
    let labels := m.doc.cells.toList.filterMap fun (c, d) =>
      match d with
      | .record [(l, _)] => if l == Kinds.name && lacks c && !(places m v).contains c then offer c "label" else none
      | _ => none
    let common := ([Kinds.name, Kinds.isa].filter fun l => lacks l && !(places m v).contains l).filterMap (offer · "field")
    let new : List Offer :=
      if query.isEmpty then []
      else [⟨query, "label", true, fun m =>
        let (id, m) := m.fresh
        let m := { m with doc := { m.doc with cells := m.doc.cells.insert id (Builtin.named query) } }
        m.openAt (path ++ [.key id])⟩]
    declared ++ labels ++ common ++ new
  | _ => []

/-- The offers for what's being typed, if it's a query. -/
def offers (m : Model) : List Offer :=
  match m.selection with
  | some { path, stage, editing := some e } =>
    if !e.picker then []
    else if stage == .label then labelOffers m path e.text
    else valueOffers m path e.text
  | _ => []

/-- The chosen offer taken. -/
def commit (m : Model) : Model :=
  match m.selection with
  | some { editing := some e, .. } =>
    match (offers m)[e.choice]? with
    | some o => o.take m
    | none => m
  | _ => m

/-! ## Lines -/

/-- Whether a value is drawn as a line that's typed in place, and its text. -/
def lineOf (v : Value) : Option String :=
  match v with
  | .record fields =>
    if fields.length != 2 then none
    else match v.text?, v.u64?, v.f64? with
      | some s, _, _ => some s
      | _, some n, _ => some (toString n)
      | _, _, some x => some (Display.number x)
      | _, _, _ => none
  | _ => none

/-- The document with a line's text written through: text as it is, a
number when it reads as one; otherwise the document stays and the line
shows what's typed. -/
def writeLine (m : Model) (path : Path) (text : String) : Model :=
  let bytes : Option (List UInt8) :=
    match m.at? path with
    | some v =>
      if v.text?.isSome then some text.toUTF8.toList
      else if v.u64?.isSome then (parseNat? text).map fun n => Value.bytes8 n.toUInt64
      else if v.f64?.isSome then
        ((parseFloat? text).orElse fun _ => (parseNat? text).map (·.toFloat)).map fun x => Value.bytes8 x.toBits
      else none
    | none => none
  match bytes.bind fun b => m.doc.set (path ++ [.key Kinds.bytes]) (.blob b) with
  | some doc => m.write doc (typing := true)
  | none => m

/-- The model with what's being typed changed: a line is written through. -/
def retype (m : Model) (sel : Selection) (e : Editing) : Model :=
  let m := { m with selection := some { sel with editing := some e } }
  if e.picker then m else writeLine m sel.path e.text

/-! ## Keys -/

def toggleFold (m : Model) (path : Path) (c : CellId) : Model :=
  let plain := ((m.at? path.dropLast).bind (·.kind?)).isNone
  let closed := Display.isOpen m.shown path c plain
  { m with folds := (path, closed) :: m.folds.filter (·.1 != path) }

/-- A character typed. -/
def typed (m : Model) (c : Char) : Model :=
  match m.selection with
  | none => m
  | some sel =>
    match sel.editing with
    | some e =>
      if e.picker && e.text.isEmpty && sel.stage != .label && (c == '[' || c == '{' || c == '(') then
        let name := if c == '[' then "list" else if c == '{' then "record" else "cell"
        match (valueOffers m sel.path "").find? (·.text == name) with
        | some o => o.take m
        | none => m
      else
        let text := (e.text.take e.caret).toString ++ c.toString ++ (e.text.drop e.caret).toString
        retype m sel { e with text, caret := e.caret + 1, choice := 0 }
    | none =>
      match m.at? sel.path with
      | some v =>
        -- A colon on a parameter is its type, and on a lambda, or its
        -- parameters, what it returns: the place opens, or is selected.
        let place (path : Path) : Model := if (m.at? path).isSome then m.rest path else m.openAt path
        let lambdaAt (path : Path) : Bool := ((m.at? path).bind (·.kind?)) == some Kinds.lambda
        let isParam := sel.path.dropLast.getLast? == some (.key Kinds.params)
        match v, c with
        | .cell id, ' ' => toggleFold m sel.path id
        | .cell _, ':' =>
          if isParam then place (sel.path ++ [.follow, .key Kinds.type_])
          else if lambdaAt (sel.path ++ [.follow]) then place (sel.path ++ [.follow, .key Kinds.returns])
          else m
        | .list _, ':' =>
          if sel.path.getLast? == some (.key Kinds.params) && lambdaAt sel.path.dropLast then
            place (sel.path.dropLast ++ [.key Kinds.returns])
          else m
        | _, _ =>
          if c == ':' && lambdaAt sel.path then place (sel.path ++ [.key Kinds.returns]) else
          if !m.doc.writable m.library sel.path then m
          else match lineOf v with
            | some text =>
              let text := text ++ c.toString
              retype m sel { text, caret := text.length, picker := false }
            | none => { m with selection := some { sel with editing := some (picker c.toString) } }
      | none =>
        if !m.doc.writable m.library sel.path then m
        else if sel.path.getLast? == some (.key Kinds.name) then
          -- A name is text: the first letter writes it, and the rest type in it.
          let m := m.put sel.path (Value.text c.toString)
          { m with selection := some { path := sel.path, editing := some { text := c.toString, caret := 1, picker := false } },
                   typingRun := true }
        else m.openAt sel.path sel.stage c.toString

/-- The place of a path in what holds it: the holder's path and the step. -/
def parent? (path : Path) : Option (Path × Step) :=
  path.getLast?.map (path.dropLast, ·)

/-- A list's positions, at a path. -/
def positionsAt (m : Model) (path : Path) : List Position :=
  match m.at? path with
  | some (.list items) => items.map (·.1)
  | _ => []

/-- A place within the selected value: a field on a record, an element at
a list's end, or its start. -/
partial def within (m : Model) (path : Path) (first : Bool) : Model :=
  match m.at? path with
  | some (.record _) => m.openAt path .label
  | some (.list items) =>
    let p := if first then Position.between none (items.head?.map (·.1))
      else Position.between (items.getLast?.map (·.1)) none
    m.openAt (path ++ [.element p])
  | some (.cell c) =>
    if (m.doc.lookup? m.library c).isSome then within { m with folds := (path, false) :: m.folds } (path ++ [.follow]) first
    else m.openAt (path ++ [.follow])
  | _ => m

/-- A peer of the selected value: an element after it in its list, or
before; a field on the plain record holding it. A value held by a record
of a kind, a call's argument or an evaluation's expression, has no peers of
its own: the peer is the record's; and a cell's definition's is the cell's. -/
partial def peer (m : Model) (path : Path) (before : Bool) : Model :=
  match parent? path with
  | some (holder, .element p) =>
    let positions := positionsAt m holder
    let earlier := (positions.filter (Position.lt · p)).getLast?
    let later := (positions.filter (Position.lt p ·)).head?
    let new := if before then Position.between earlier (some p) else Position.between (some p) later
    m.openAt (holder ++ [.element new])
  | some (holder, .key _) =>
    if ((m.at? holder).bind (·.kind?)).isSome && !holder.isEmpty then peer m holder before
    else m.openAt holder .label
  | some (holder, .follow) => peer m holder before
  | none => within m path false

/-- Whether a hole is drawn at a path with no value: a kind's field, or a
list's element being added. -/
def holeDrawn (m : Model) (path : Path) : Bool :=
  match parent? path with
  | some (holder, .key l) => ((m.at? holder).map fun v => (places m v).contains l || l == Kinds.name).getD false
  | some (_, .element _) => true
  | some (_, .follow) => true
  | none => true

/-- The selection resting on a path, or on the nearest thing above it
that's drawn. -/
partial def restDrawn (laid : Model → Layout) (m : Model) (path : Path) : Model :=
  let rested := m.rest path
  if ((laid rested).here rested).isSome || path.isEmpty then rested else restDrawn laid m path.dropLast

/-- The selected value deleted, its place left selected as a hole; on a
hole, the hole removed, the selection going to the element after it or
before, or to what held it. -/
def delete (laid : Model → Layout) (m : Model) (sel : Selection) : Model :=
  if (m.at? sel.path).isSome && sel.stage == .edge then
    match m.doc.delete sel.path with
    | some doc =>
      let m := m.write doc
      if holeDrawn m sel.path then { m with selection := some { path := sel.path, stage := .pending } }
      else restDrawn laid m sel.path.dropLast
    | none => m
  else
    match parent? sel.path with
    | some (holder, step) =>
      if sel.stage == .label then m.rest sel.path
      else
        match step with
        | .element p =>
          -- A list's hole: on to the element after it, or before.
          let positions := positionsAt m holder
          match (positions.filter (Position.lt p ·)).head? <|> (positions.filter (Position.lt · p)).getLast? with
          | some q => m.rest (holder ++ [.element q])
          | none => restDrawn laid m holder
        | _ => restDrawn laid m holder
    | none => { m with selection := none }

/-! ## The clipboard -/

/-- The definitions cells reach, from the document. -/
partial def reach (d : Document) (todo : List CellId) (seen : Std.TreeMap CellId Value := {}) :
    Std.TreeMap CellId Value :=
  match todo with
  | [] => seen
  | c :: rest =>
    if seen.contains c then reach d rest seen
    else match d.cells.get? c with
      | some v => reach d (GidText.mentions v ++ rest) (seen.insert c v)
      | none => reach d rest seen

/-- The selected value as a document of its own, as text: the value as the
root, with the definitions it reaches. -/
def clipping (m : Model) : Option String :=
  m.selection.bind fun sel => (m.at? sel.path).map fun v =>
    GidText.write { root := some v, cells := reach m.doc (GidText.mentions v) } m.library

/-- What text that isn't a document is, as a value: a number if it reads
as one, or a text. -/
def plainValue (text : String) : Value :=
  let trimmed := text.trimAscii.toString
  match parseNat? trimmed with
  | some n => Value.u64 n
  | none => match parseFloat? trimmed with
    | some x => Value.f64 x
    | none => Value.text text

/-- The clipboard's text pasted: into the line being typed; or as a value
at the selection, in place of what's there: the root of the document the
text is, with the definitions it brings that the document doesn't have, or
the text itself. -/
def pasted (m : Model) (text : String) (clip : Option Document) : Model :=
  match m.selection with
  | none => m
  | some sel =>
    let typing := match sel.editing with
      | some e => !e.picker || !e.text.isEmpty || sel.stage == Stage.label
      | none => false
    if typing then (text.toList.filter fun c => c != '\n' && c != '\r').foldl typed m
    else if sel.stage == Stage.label || !m.doc.writable m.library sel.path then m
    else
      let (v, cells) : Value × Std.TreeMap CellId Value :=
        match clip.bind fun d => d.root.map (·, d.cells) with
        | some found => found
        | none => (plainValue text, {})
      let merged := cells.foldl (init := m.doc.cells) fun (acc : Std.TreeMap CellId Value) c d =>
        if acc.contains c then acc else acc.insert c d
      match ({ m.doc with cells := merged } : Document).set sel.path v with
      | some doc => (m.write doc).rest sel.path
      | none => m

/-- Typing ended: the line keeps what was written; a query goes, leaving
the value it was over, or the hole. -/
def stopTyping (m : Model) (sel : Selection) : Model :=
  if sel.stage == .label then m.rest sel.path
  else { m with selection := some { sel with editing := none }, typingRun := false }

def keyReturn : UInt32 := 13
def keyTab : UInt32 := 9
def keyEscape : UInt32 := 27
def keyBackspace : UInt32 := 127
def keyDelete : UInt32 := 63272
def keyUp : UInt32 := 63232
def keyDown : UInt32 := 63233
def keyLeft : UInt32 := 63234
def keyRight : UInt32 := 63235

/-- A key pressed. -/
def key (laid : Model → Layout) (m : Model) (code mods : UInt32) : Model :=
  let shift := Deui.App.Mods.has mods Deui.App.Mods.shift
  let command := Deui.App.Mods.has mods Deui.App.Mods.control || Deui.App.Mods.has mods Deui.App.Mods.super
  if command && code == 'z'.toNat.toUInt32 then (if shift then m.redone else m.undone)
  else if command && code == 'y'.toNat.toUInt32 then m.redone
  else if command && code == 's'.toNat.toUInt32 then { m with saveAsked := true }
  else if command && code == 'c'.toNat.toUInt32 then { m with copied := clipping m }
  else if command && code == 'v'.toNat.toUInt32 then { m with pasteAsked := true }
  else if command && code == 'x'.toNat.toUInt32 then
    match m.selection with
    | some sel =>
      if sel.editing.isNone && sel.stage == .edge && m.doc.writable m.library sel.path then
        delete laid { m with copied := clipping m } sel
      else m
    | none => m
  else
  match m.selection with
  | none =>
    if code == keyDown || code == keyRight || code == keyTab then m.step laid true (if code == keyTab then isTabStop else isPlace)
    else m
  | some sel =>
    match sel.editing with
    | some e =>
      if code == keyLeft then
        if e.caret > 0 then { m with selection := some { sel with editing := some { e with caret := e.caret - 1 } } }
        else (stopTyping m sel).step laid false
      else if code == keyRight then
        if e.caret < e.text.length then { m with selection := some { sel with editing := some { e with caret := e.caret + 1 } } }
        else (stopTyping m sel).step laid true
      else if code == keyUp then
        if e.picker && !(offers m).isEmpty then
          { m with selection := some { sel with editing := some { e with choice := e.choice - 1 } } }
        else (stopTyping m sel).stepLine laid false
      else if code == keyDown then
        if e.picker && !(offers m).isEmpty then
          { m with selection := some { sel with editing := some { e with choice := min (e.choice + 1) ((offers m).length - 1) } } }
        else (stopTyping m sel).stepLine laid true
      else if code == keyBackspace then
        if e.caret > 0 then
          let text := (e.text.take (e.caret - 1)).toString ++ (e.text.drop e.caret).toString
          retype m sel { e with text, caret := e.caret - 1, choice := 0 }
        else if e.text.isEmpty then delete laid m { sel with editing := none }
        else m
      else if code == keyDelete then
        let text := (e.text.take e.caret).toString ++ (e.text.drop (e.caret + 1)).toString
        retype m sel { e with text, choice := 0 }
      else if code == keyReturn then
        if e.picker then
          if command then m
          else if e.text.isEmpty && e.choice == 0 then stopTyping m sel
          else commit m
        else stopTyping m sel
      else if code == keyTab then
        let m := if e.picker && !e.text.isEmpty then commit m else stopTyping m sel
        m.step laid (!shift) isTabStop
      else if code == keyEscape then
        if sel.stage == .edge && (m.at? sel.path).isSome then stopTyping m sel
        else match parent? sel.path with
          | some (holder, _) => m.rest (if sel.stage == .label then sel.path else holder)
          | none => { m with selection := none }
      else m
    | none =>
      if code == keyLeft then m.step laid false
      else if code == keyRight then m.step laid true
      else if code == keyUp then m.stepLine laid false
      else if code == keyDown then m.stepLine laid true
      else if code == keyTab then m.step laid (!shift) isTabStop
      else if code == keyEscape then { m with selection := none }
      else if code == keyBackspace || code == keyDelete then
        if m.doc.writable m.library sel.path then delete laid m sel else m
      else if code == keyReturn then
        if !m.doc.writable m.library sel.path then m
        else if sel.stage == .pending then m.openAt sel.path
        else if command then within m sel.path shift
        else peer m sel.path shift
      else m

/-- An offer's target is tagged `offerTag` and the offer's index. -/
def offerTag : UInt32 := 1000000

/-- A click on an offer takes it. -/
def clickedOffer (m : Model) (index : Nat) : Model :=
  match m.selection with
  | some sel =>
    match sel.editing with
    | some e => commit { m with selection := some { sel with editing := some { e with choice := index } } }
    | none => m
  | none => m

end Progred.Model
