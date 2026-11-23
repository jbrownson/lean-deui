# Progred in Lean: the port's notes

Progred is a projectional editor ([jbrownson/progred](https://github.com/jbrownson/progred),
in Rust). `Progred/` here is its core, in Lean, on deui, with a subset of Lean
in place of its language Grap. This file records what the Rust version does
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
- **Lean in place of Grap.** A small functional subset, stored as GID in Grap's
  shapes (`lambda`, `call`, `value wrapper`, `evaluation`), is turned into Lean
  `Syntax` with quotations (`Progred/Lean.lean`), never text, elaborated into an
  environment loaded at run time and run by Lean's interpreter
  (`Progred/Run.lean`). A syntax node's position is the id of the editor node
  it came from, so an error comes back at its node.
- **Monospace text.** Layout is in characters: a pretty-printer chooses inline
  or stacked forms against a ribbon, as the Rust layout's alternatives do.
- **The view redraws.** The projection is recomputed and the screen's rows
  replaced (`Deui.Redraw`, proved correct), only the lines in the viewport.
  Sharper derivatives come later, where a profile says.
- **Not yet:** panes, the Raw/Plain/All presets, clipboard, hover and
  shared-occurrence marks, number scrubbing, name parts and subscripts,
  projections and offers defined in the document, CAM and Fidget.
