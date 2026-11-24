# Progred in Lean: the port's notes

Progred is a projectional editor ([jbrownson/progred](https://github.com/jbrownson/progred),
in Rust). `Progred/` here is its core, in Lean, on deui, with Skinny, a subset
of Lean, in place of its language Grap. This file records what the Rust version does
(surveyed from its docs and code, November 2026) and what this port decides.
The Rust paths are under `progred/` in that repository.

## What the Rust version does

### Data (GID), `gid/src/`

- `CellId`: 128 random bits, written as exactly 32 lowercase hex digits. Minted
  only from the OS's random numbers, never derived from a name.
- `Value`: `Cell(CellId) | Blob(bytes) | List | Record`. No string or number
  atoms.
- `Record`: `CellId` label to `Value`, sorted by label, unique.
- `List`: values keyed by a `Position`: a non-empty byte string whose last byte
  is non-zero, read as a binary fraction, ordered lexicographically.
  `between(low, high)` mints one strictly between; `(None, None)` gives `[0x80]`;
  `spread(n)` gives n evenly spread. List equality ignores positions.
- `Document`: `root : Option Value` and `cells : CellId -> Value`. A cell with no
  entry is bare. A place with no value is a hole, never a stored value.
- `Step`: `Key(CellId) | Element(Position) | Follow`; a path is a list of steps.

Conventions, with fixed ids:

| Convention | Shape | Id |
|---|---|---|
| kind | field `isa` holding a kind cell | `isa = dbd7e1a38e30425fb1b408b2e446bb1b` |
| literal | `{isa: <kind>, bytes: <blob>}`, other fields allowed | `bytes = fe06bf0459d2598aa29b30302e3b29b8` |
| text | literal, UTF-8 | `text = 332529b8ea83a7ba10fd7f6d942e5016` |
| f64 | literal, 8 little-endian bytes | `f64 = ed11fde03b7c2c1ba2fccc3cdba5d561` |
| name | field `name` on a cell's definition; text | `name = 02e562654d6d0828d3a7559e6f75fffe` |
| kind definition | `{isa: def, name, fields: [cells], projection}` | |
| section | `{isa: section, name, body}` | `body = ac7cc432…` |
| notebook | `{isa: notebook, entries: [values]}` | |

An unnamed cell shows as `…` and its last 5 hex digits.

### GID text, `progred/src/gid_text.rs`

One envelope with optional quoted keys `"binders"`, `"cells"`, `"root"`, binders
first:

```
{
  "binders": { "name": 02e562654d6d0828d3a7559e6f75fffe, "isa": dbd7e1a3…, },
  "cells": { over: {name: "over"}, half: {isa: fraction, over: {isa: f64, bytes: 0x000000000000f03f}}, },
  "root": { isa: notebook, entries: [ half, ] },
}
```

- `value := "text" | 0x<even hex> | bare | { label: value, … } | [ (0x<pos>:)? value, … ]`
- `bare` is `[A-Za-z0-9_]+`: a cell id if exactly 32 hex digits, else a binder.
- Quoted text is sugar for `{isa: text, bytes}`; escapes `\" \\ \n \t`.
- A blob followed by `:` in a list is a position; all or none, strictly
  increasing; with none, `spread` assigns them.
- Lenient: hex case, trailing commas, missing envelope keys, unbound binders (a
  fresh id is minted on first use).
- Printer: binders sorted by name; cells named first by (name, id) then by id;
  record labels by id; list positions always written; two-space blocks with
  trailing commas; a value prints as quoted text only when it's a text literal
  with no other fields; every id gets a binder (loaded, else the sanitized name,
  else `_` and the last 5 hex digits, `_2`, `_3` on collision).

### Editor model

- `Model { doc, saved, selection, history, workspace }`; undo is whole-state
  snapshots (doc, selection, folds); an unchanged write records nothing; a run
  of line edits is one step.
- A location is a start (root or a cell) and a path; a write through a `Follow`
  lands in the followed cell's definition. An occurrence path is the path as
  drawn, from the root, so two drawings of one cell are two selections.
- Selection stages: `Edge` (a value), `Pending` (a value being authored where
  there is none), `Label` (a new field's label).
- All edits are `set_value(location, value)` and `delete_edge(location)`.

### Display

Projection choice, first that accepts: the kind's def's projection, the
projection registered for the kind, library partials, the generic kinded-record
form, Raw.

- Raw blob: `0x…` hex. Raw cell: `(definition)`; folded: `(kind name …)` or the
  short id; closed by default when it is a record's `isa`, in a cycle, or nested
  in another cell's value while holding cells. Raw list `[…]`: inline with dim
  `, `, else one per line. Raw record `{…}`: `label: value, …` inline, else a
  column; a value sits beside its label, else below it indented. Fields: named
  labels by name, then unnamed by id.
- Layout: alternatives, the first that fits a ribbon of about 70 characters,
  else stacked.
- Kinded record: `kind name {fields}`, the def's fields first, each a slot when
  missing. Text draws as `"…"`, a number as digits with a dim type tag.
- Colors: names blue (20,91,219), labels violet (123,63,199), strings orange
  (195,65,0), dim and ids grey (102,115,139), ink (33,43,65), delimiters
  (141,155,179), paper white. Selection: accent (0,122,255) wash at 0.22 with a
  ring. Read-only ground: faint blue. Absent or failed: red wash.
- Notebook: entries one under another, numbered in a dim margin. Section:
  `▾ name` over an indented body. Evaluation: `expression → result`, the result
  read-only.

### Interaction

- Arrows: every drawn occurrence is a stop, a container before its contents.
  Left/Right: the adjacent stop in reading order. Up/Down: the first stop on the
  adjacent line. In a line editor, arrows move the caret until an edge.
- Tab / Shift+Tab: only tab stops, in draw order: every writable hole, every
  list insertion point (before, between, after, and in an empty list), the end
  of each record with no `isa`, and a label being added. Arriving opens the
  place; leaving it untouched adds nothing. With text typed, Tab commits the
  chosen offer and moves on.
- Enter on a resting value adds a peer after it (Shift: before): a list sibling,
  or a new field on the record holding it. Cmd/Ctrl+Enter adds within: a field
  on a record, an element on a list (Shift: first), the first value of a bare
  cell. While typing, Enter ends typing.
- Backspace/Delete on a resting value: delete it, leaving its place selected as
  a hole; again on the empty hole: remove the hole (Backspace lands on the
  previous sibling, else the container; Delete on the next stop).
- Typing on a value drawn as a line (text, number, name, hex) edits it in
  place, written through on each valid parse. Typing on any other resting value
  opens a picker over it seeded with the character; Escape restores it.
- Picker: a card under the query, up to 8 rows; Up/Down choose; Enter or a
  click commits; rows show a dim `new` prefix, the text with matched spans, the
  kind, a detail. Ranking: prefix, substring, their case-insensitive forms,
  fuzzy. In an empty query, `(` makes a new cell, `[` a list, `{` a record. Raw
  offers: a reading that spells the query exactly, the constructors, typed
  readings (numbers when it parses), text `"query"` (for a label hole, a new
  label cell named as typed). A leading `"` forces text; `0x…` is a blob. A
  label hole offers only cells the record lacks; for a kinded record, the def's
  missing fields. An `isa` hole offers the document's defs.
- Escape: a picker returns to its origin; otherwise clears the selection.
- Space toggles the fold of the selected foldable.
- Mouse: click to select; a click on whitespace deselects; Cmd+click a value
  picks it into the open hole (how an existing cell is reused).
- Cmd/Ctrl+Z undo, +Shift redo; Cmd+C/X/V; Cmd+S save.

### What depended on Grap

Evaluation, value wrappers, the call and lambda projections, scope analysis for
completion, defs' `projection` and `offers`, handlers written in Grap.

## What this port decides

- **One repository for now.** `Progred` is a Lake library here that depends on
  `Deui`, never the reverse; it can move to its own repository.
- **Skinny in place of Grap.** A small functional subset of Lean, stored as GID
  in Grap's shapes (`lambda`, `call`, `value wrapper`, `evaluation`), is turned
  into Lean `Syntax` with quotations (`Progred/Skinny.lean`), never text,
  elaborated into an environment loaded at run time and run by Lean's
  interpreter (`Progred/Run.lean`). A syntax node's position is the number of
  the value it came from, so an error comes back at its node.
- **Types are expressions.** A parameter's `type` is on its definition and a
  lambda's `returns` on the lambda; Nat, Int, Float, Text, Bool, List and
  Function are in the library. They're optional, except that a lambda that
  refers to itself needs them, and becomes a `partial def`: Lean wants a
  recursive definition's type before its body, and without a proof that it
  ends, `partial` is what runs.
- **A projection is a layout, or a function that gives one.** A def's
  `projection` is a Skinny expression. Where it's a layout as it stands, calls
  of `row`, `column`, `indent`, `either`, `words`, `faint` and `part` with
  nothing to work out, it's read as data and no code runs, as the Rust
  version's templates are. Otherwise it's a function of the record: Lean runs
  it on each record of the kind, outside the pure update, and what it gives,
  a layout as a value, comes into the model as data (`Model.layouts`), as
  evaluations' results do. So the view stays a pure function of the model, and
  its derivative's law holds. `part` draws the record's own value at a field,
  so it's edited where it's drawn; a field with no value is a hole. A
  projection that fails leaves its records drawn as records.
- **Skinny's prelude is this program's own code.** `Progred/Prelude.lean` is
  built into the program and loaded, as the module the build made, into the
  environment code is elaborated in. A function a document defines takes and
  gives `Progred.Value`, with nothing converted between.
- **Functions Lean supplies** are cells of the built-in library, each with its
  parameters as cells, since a call labels its arguments by them: add,
  subtract, multiply, divide, remainder, equals, less, and, or, not, if,
  append, length, map, filter, fold, range, show (`Progred/Builtin.lean`).
- **Monospace text.** Layout is in characters: a doc chooses its inline or its
  stacked form against a ribbon, as the Rust layout's alternatives do.
- **The model's edits say what changed, and nothing is compared to find it.**
  What the view reads of the model is changed only by a `Change`, which the
  model notes: a cell's definition; an entry of the root notebook written,
  added or taken away, by where it is among the entries; the root or the
  document whole; the selection, the folds, what Lean gave, the scroll, the
  window's size. A handler is still a function from model to model; its edits
  are the changes it noted, then the rest, which is all the view doesn't read
  (`Model.emitted`). So the state the app holds is the model the handler made.
  `Model.write` takes the path a document was written at and works out which
  change that is.
- **The view is a derivative, and each step is sensitive to what it reads**
  (`Progred/Editor.lean`). The model's edits are sorted by what they're
  asked of: the definitions written, what of the editor's state is drawn,
  and the document's parts, where an entry written within is its part
  written at that path, and one added or taken away is a part inserted or
  deleted (`Progred/Entries.lean`, `edits_ok`). Each part keeps its own, and
  is given every edit of what it's drawn under, of which it makes what it's
  sensitive to (`Deui/Under.lean`). It keeps what it reaches, with every
  cell it asked for on the way, defined or not: a definition written grows
  the part again only if it asked for that cell (`reach_agree`,
  `item_untouched`). It keeps its frames, and how they're laid out; its
  lines are edited line by line, joined with the other parts', the window
  shows the lines that fit, and each is a row of the scene. Every step is
  one of deui's, proved, and `view_ok` is their laws composed.
- **A value is a frame, and a frame is drawn from little.** The projection
  draws each value as one frame, with the values inside it as its kids
  (`Progred/Display.lean`). A frame is drawn from its value without what's
  inside its elements and fields, the definitions it looks up, and the
  selection only when it's at the frame or a step in, with what's typed
  only where it's typed. So two changes can be followed down a part's
  frames to where they land, each frame on the way asked only whether what
  it sees is as it was (`Progred/Regrow.lean`): a selection that changes
  (`reselect_ok`), and a write within a value (`rewrite_ok`). A frame that
  sees the same is left, with every kid the change isn't on the way to;
  one that sees something new is grown again with all under it. Typing
  grows one frame again. A form that would read further into its value
  makes that a kid instead: a record's name, a lambda's parameters, a
  notebook's entries.
- **Layout is a derivative** (`Deui/Fit.lean`). A part's frames are laid
  out as text within the ribbon, and kept as they're laid: each frame with
  where it started, and each kid as it was laid there. A frame grown again
  is laid out where it stood; the frames above it are each walked once,
  taking their other kids as they stand, and if a frame comes out as it
  was but for the kid that changed, the kid's splice of the text is all
  there is. Where a frame now fits differently (it was on one line and
  isn't), that frame's text is replaced. A splice becomes edits of the
  lines it reaches.
- **A selection that rests is a wash, not a layout.** Only a selection
  being typed in, or one with a hole or a label drawn for it, is part of
  what a part is drawn with. One that rests on a value is washed under the
  text of the lines that show, a layer of its own, with the mark on the
  other places the selected cell is: an arrow key lays nothing out, and
  draws the wash of the window's lines again.
- **A part takes nothing from the parts beside it.** An entry being added is
  anchored to the entry it's before, or to the entries' end, and that part
  draws it. The place to add an entry is before each entry and at the end, and
  its position is worked out when it's chosen, from the document. Entries have
  no numbers: a number is the one thing every later entry would take from an
  entry added before it.
- **Handlers read what the view keeps.** Navigation and clicks use the lines
  the view kept for the model (`laidOf_view`), whose spans carry the
  occurrences they show: an arrow key reads on from where the selection
  starts until it finds the next. Where an edit needs the layout of a model
  it's passing through, the same derivative gives it, of the model its
  edits so far make (`relaid_view`). Scrolling to the selection follows an
  event's edits as `settle`, since it needs the layout of the new model.
- **Outside the pure update:** fresh cell ids, evaluations, the clipboard and
  saving are done by the window's loop after each batch of events and come
  back as edits (`Progred/Outside.lean`); an evaluation is remembered by the
  Lean it became, so an edit elsewhere doesn't run it again.
- **The clipboard holds GID text.** A copy is a document of its own: the
  selected value as the root, with the definitions it reaches. A paste puts
  the root at the selection and adds the definitions the document doesn't
  have, so a reference stays a reference to the same cell. Text that isn't a
  document pastes as a number or a text; into a line being typed, as typing.
- **A cell opens one level deep.** A cell with a definition draws open as the
  root, a list's element, an evaluation's expression or a field of a record
  with no kind, and not inside another cell's definition; elsewhere, as a
  call's function or argument or a kind, it's its name. Space folds either
  way. The Rust version follows cells until a cycle.

## Where it stands against the Rust version

Here, and tried (`progred_play` plays keys through the editor with no window;
the window was driven under Xvfb):

- The data, and the text format: all twelve of the Rust version's example
  files read, and read back the same after being written.
- The projection: raw cells, lists, records and blobs; text and numbers; the
  generic `kind name {fields}` with the kind's fields as places; notebook,
  section, evaluation, lambda, call (a function with a symbol goes between its
  two arguments), value wrapper. Inline where it fits, else stacked.
- Selection as a place; arrows over what's drawn; Tab over holes, list
  insertion points and records' ends; holes answered by offers as you type
  (numbers, text, list, record, cell, a new record of a kind, a cell by name,
  a call to a function, a new named cell; for a label, the kind's fields, the
  document's labels, a new label); Return, Shift+Return and Ctrl+Return;
  Backspace to a hole and then away; text, numbers and names typed in place and
  written through, a run of typing one undo step; undo and redo of the
  document, the selection and folds; Space folds a cell; clicks select, and
  take an offer; the wheel scrolls; the window resizes; Ctrl+S saves.
  Return on a call's argument or an evaluation's expression adds a peer of
  the entry they're in, not a field on the call. Up and Down go to what's
  nearest the column.
- Copy, cut and paste (Ctrl+C, Ctrl+X, Ctrl+V), through the system
  clipboard.
- With a cell selected, or its name, the other places it is are marked:
  where it's a value, and where it's a field's label.
- The language: literals, lists, lambdas, calls, named values, references, the
  supplied functions, evaluated by Lean, with the value and its type shown, or
  Lean's error, in the document's names, and the value it's about on red.
  Types on parameters and results, and a function that calls itself
  (`fact {n: 10} → 3628800 : Nat`).
- Projections defined in the document: a def's `projection` as a layout, and
  as a function of the record (`examples/projections.gid`), their parts edited
  in place.
- The view by derivative, down to a part's frames. `progred_measure`, on a
  notebook of 3,300 lines in 300 entries, a tenth of which reach each of
  ten definitions: the wheel about 25 µs, an arrow key 50 µs, a keystroke
  0.2 to 0.35 ms, a definition written 4 ms, against 20 ms to lay it out
  from nothing. On the same entries as one part, a list of 300 records at
  the root (`progred_measure 300 one`): an arrow key 50 µs, a keystroke 0.5
  to 0.65 ms, an element added to the root list 3 ms. Before a part's
  layout had a derivative, a keystroke or an arrow key there took a third
  of a second.

Not here yet:

- Panes, and the Raw, Plain and All presets; hover; Cmd+click to pick a cell
  into a hole; number scrubbing; names made of parts.
- Offers defined in the document (a field's `offers`); libraries as documents;
  the Rust layout's other nodes (`center`, `rule`, `pad`, `border`, `drawing`,
  `at`, `jump`, handlers); a place to see a projection's error, which goes to
  the terminal; a projection's fields it doesn't draw, which aren't shown.
- Definitions that refer to each other in a circle; `match`, `let`, structures:
  Skinny is expressions, lambdas, calls and types.
- Proportional text and delimiters that span their block.
- New and Open; a mark that the document has unsaved changes.
- CAM, Fidget, the web and macOS targets.
- What the view still does in proportion to more than the change:
  - Its lists are linked lists, so an edit at a position costs the
    position: patching a list of lines, counting the rows above the window,
    finding a kid among a frame's kids. A frame on the way to a change is
    drawn again to find its kids, and walked again to lay them out, so it
    costs its width: a list of 300 at the root is most of the half
    millisecond a keystroke takes in one large part. A sequence held as a
    tree would make these the logarithm.
  - A change to what a list or a record holds grows that frame again with
    all under it: an element added, a field given a value, a hole opened or
    closed. So does a write within an evaluation, or within a record drawn
    by a projection, since those read their whole value. Adding an element
    to a list that is the whole document grows everything again. Frames
    whose kids are edited as a list are the way on.
  - A write still walks its part once to find what it reaches, and a
    definition written grows again every part that asked for the cell,
    whole, though it may show only the name. Frames that say what they read,
    cell by cell, would let a definition's edit go to the frames that asked.
  - A frame that follows another on its line, when that one's width
    changes, is laid out again where it now starts, though only an
    alternative that no longer fits could change it.
  - Undo and redo replace the document, and every part is laid out again,
    twice over: once for the definitions and once for the parts, which are
    all taken out and put in. Undo that said what it undid would cost what
    it undid.
  - An arrow key reads the lines of its part from the top to where the
    selection starts, each time; the frames know where that is.
- Laying a document out from nothing takes 20 ms where it took 16, and the
  wheel 25 µs where it took 12: frames, and a layer more.
- Where a comparison remains. A change of the selection, the folds or what
  Lean gave is asked of each part by whether what the part takes of it
  differs, and a frame on the way to a change is asked whether its own view
  is as it was: of its value without what's inside it, and of the selection
  at it. They're small values compared once each; none is a search for what
  changed. After a write, a part's definitions and results are compared
  with what they were before the frames are taken as they stand.
- Entry numbers, which the Rust version shows in a margin.
- Nothing checks that a handler changes what the view reads only through
  `change`; the state follows the edits, so a field set directly shows as a
  change that didn't take.
- Laws about Progred beyond its view: `view_ok` says the scene on screen is
  the view of the model, and nothing says the editing is right. What runs
  outside the pure update (Lean, the files, the clipboard) isn't in any law,
  and Lean's results are remembered there by the code they came from.
