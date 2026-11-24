# deui for Lean

deui, said "dewey": dUI, the change in the UI. A view is a pure function of
one state, and deui gives it a derivative: from the state and a change to
it, the change to the screen. A law says the derivative is right, that
applying its change gives what drawing again would, and Lean checks it. The
work a frame does is then the size of the change, not the size of the view.
[Two Piles of State](https://jbrownson.github.io/two-piles/) explains why.

This began as [bend-deui](https://github.com/jbrownson/bend-deui), in Bend,
and continues here.

## Files

`Deui/`, the library. Each module's laws are its theorems, each with a
docstring saying what it promises; reading them is enough to know what the
module does.

- `Change.lean`: edits to any value. An edit structure says how a type's
  values are edited: the values (`Value`), their edits (`Edit`), and how to
  apply one. `runs` makes runs of edits, and `whole` adds replacing the
  value. An `Inc` pairs a function with its derivative, which gives the
  edit to the result from the value before and its edit (`Inc.ok` says
  it's correct); `lift`, `whole.lift` and `recompute` build them. A
  `Cached` function keeps what its derivative needs instead of taking the
  value before, so composing two (`compose`) never runs the first again;
  `cached` makes one of an `Inc` by keeping its input. The laws say that
  lifting, caching and composing correct ones gives correct ones.
- `Lists.lean`: a list's edits (insert, delete, and update an element in
  place), `patch`, `diff` from any list to any other, and `map.inc`, which
  maps an `Inc` over lists, with its derivative `dmap`. From
  [lean-puri](https://github.com/jbrownson/lean-puri)'s port.
- `Scene.lean`: what's on the screen. A scene is a tree of fills, labels,
  targets and groups, each at an offset from its group, so moving anything
  is one edit. A group's children are edited by position, and `shift`
  translates every child from a position on, so a column takes a change in
  one edit. `hit` finds the topmost target under a point, as its path
  through each group's children and its tag.
- `Column.lean`: rows stacked from the top, each as tall as it says. Its
  derivative turns an edit to the rows into a few edits to its scene:
  inserting a row inserts it and shifts the rows below down, deleting one
  shifts them back up, and replacing one with one as tall swaps it in
  place. `one_ok` and `inc_ok` say it's correct for every edit and every
  run of them.
- `Drawing.lean`, `Scroll.lean`: a long list seen through a window, from
  lean-puri: the list held split at the first row that shows, so scrolling
  touches only the rows that enter or leave, and its view, the drawing of
  the rows that show (`Lists.Scrolled.view`), with its law (`view_ok`).
- `Drawn.lean`: a drawing on the screen, as a column's children. Its
  derivative turns each drawing edit into scene edits, without needing the
  drawing (`inc_ok`).
- `Combine.lean`, `Spans.lean`, `Under.lean`, `Join.lean`,
  `Anchored.lean`: what a view is put together from, each correct if its
  parts are. `mapUnder` is a list mapped under a context by a function
  that keeps what it needs for each element: a context edit is given to
  each element, which makes of it what it's sensitive to, and nothing
  where it isn't; an element's own edit goes to it alone. `join` joins
  lists that are each edited as a list, so one line of one part changed is
  one line of the whole changed. `anchored` puts rows at an offset into
  the scrolled list; `layers` and `keyed` put scenes one over another, and
  draw one afresh when its key changes, or when an edit is large enough
  that drawing afresh costs less. Nothing here compares a list with what
  it was to find a change: a change arrives as an edit.
- `Text.lean`: text as lines of cells, made from tokens in reading order.
  Its edit is a splice: so much taken out at a place, lines down and cells
  along, and tokens put in. `splice_ok` is what makes it right: at the
  end of `A`, taking out the size of `M`, a splice turns the lines of
  `A ++ M ++ B` into the lines of `A ++ M' ++ B`. `rows` gives the lines
  as a list, edited line by line.
- `Fit.lean`: layout, by derivative. A tree of frames, each with a doc
  that says how its own pieces and its kids may go (side by side, one
  under another, indented, or the first of two ways that fits the ribbon),
  is laid out as text, and kept as it's laid: each frame with where it
  started and each kid as it was laid there. When a frame is replaced,
  only the frames above it are walked again, each taking its other kids as
  they stand. A frame can also be reshaped: given a new doc, and kids that
  are each one it had or a new one. What comes out is a splice of the
  text between what a frame's walk has in common with what was kept, at
  the front and at the end.
  `fit_ok` says the splices take the text to the edited tree's, and that
  what's kept is what laying that out from nothing keeps.
- `Tree.lean`: a tree drawn node by node, as frames for `Fit.lean`: each
  node's own doc from its label and a context, its kids in the doc's
  slots. An edit of the tree is the same edit of the frames. An edit of
  the context draws again the nodes it makes stale, their kids kept: a
  node says whether an edit could change its doc, and `drawn_ok` holds it
  to that. A node drawn from what its keys look up is stale when an edit
  touches one of its keys (`reading_touched`); nothing is recorded while
  drawing. Progred's view doesn't use it yet: `Spike/Derived.lean` tries
  it, and `docs/progred-port.md` says what came of that.
- `App.lean`: an app: a state, a `Cached` view from runs of its edits to
  runs of the scene's, and handlers, from the state and what a press hit,
  a key, text typed or the wheel, to edits; a handler also reads what the
  view keeps, and `settle` adds the edits that depend on the view of the
  new state. An event's edits go to the state, and
  through the view's derivative to the scene on screen. `play_shows` says
  that if the derivative is correct, the scene on screen is always the view
  of the state, as if it had run again. `turns` gives the scene edits a
  batch of events made, and `turns_edits` says they take the scene on
  screen before the events to the one after.
- `Screen.lean`, `native/screen.c`: a window. The screen keeps a copy of
  the scene, set at launch and then changed only by the edits `turns`
  gives, which `screen.c` applies as `SceneEdit.apply` does, reading them
  as Lean values; ThorVG keeps a paint for each part that's drawn, and a
  frame only asks it to draw them. [SDL3](https://libsdl.org) gives the
  window, its events and the clipboard, [wgpu-native](https://github.com/gfx-rs/wgpu-native)
  WebGPU, and [ThorVG](https://www.thorvg.org)'s WebGPU engine draws. Outside
  the proofs: what's proved stops at the scene edits sent to the screen.
- `Axioms.lean`: the laws' axioms, checked by `lake build`, which fails on
  a `sorry` or a new axiom.

`Examples/`:

- `Todo.lean`: a to-do list, in a window that shows what fits. Click an
  item's box to tick it and its x to delete it; Return starts a new item at
  the top, typing writes into it, Backspace takes a letter back, and the
  wheel scrolls. Its view is what shows of the scrolled list, then those
  rows on the screen, each `cached` and joined by `compose`, so its law
  (`viewOk`) follows from theirs. Only the rows that show are in the
  scene.
- `TodoPlay.lean` (`todo`): plays events through the to-do list, and prints
  the items left and whether the scene on screen is their view.
- `TodoWindow.lean` (`todo_window`): the to-do list in a window.
- `TodoLong.lean` (`todo_long`): the to-do list with 10,000 items.

## Progred

`Progred/` is a projectional editor on deui: the core of
[Progred](https://github.com/jbrownson/progred), in Lean, with Skinny, a
subset of Lean, as its language in place of Grap. It's a separate library that depends
on `Deui`, never the reverse. `docs/progred-port.md` says what the Rust
version does, what this one decides, and what isn't here yet.

- `Gid.lean`, `Kinds.lean`, `Builtin.lean`: the data. A document is a root
  value and a table of cells; a value is a cell, a blob, a list or a record
  whose labels are cells. Kinds, literals and names are conventions on top,
  with the Rust version's cell ids, and the built-in library names them and
  holds the functions Lean supplies.
- `GidText.lean`: documents as text files; the Rust version's files read.
- `Layout.lean`, `Display.lean`: the projection. A value is drawn by the
  form of its kind (text, numbers, notebook, section, evaluation, lambda,
  call, value wrapper), the generic `kind name {fields}`, else raw, in
  characters, on one line where it fits a ribbon, else stacked. Each value
  is one frame, with the values inside it as its kids, and a frame is
  drawn from little: its value without what's inside its elements and
  fields, the definitions it looks up, and what of the selection is at
  it. Every drawn thing is an occurrence, which its spans carry, so
  selections, keys and clicks find their place. The document is drawn in
  parts, an entry of the root notebook each.
- `Writes.lean`, `Regrow.lean`: what a change does to a part's frames. A
  write within a value, and a selection that changes, are each followed
  down to where they land; a frame on the way that sees what it saw is
  left as it is, and one that sees something new is drawn again with the
  kids it had (`rewrite_ok`, `reselect_ok`).
- `Model.lean`, `Editing.lean`: the editor: selection, navigation by what's
  drawn, holes answered by offers as you type, lines typed in place, and
  undo, which is the changes that take a step back (`back_ok`).
- `Skinny.lean`, `Prelude.lean`, `Run.lean`: the language, Skinny. An
  expression becomes Lean `Syntax`, built with quotations, never text, and
  is elaborated and run by Lean at run time, in an environment loaded
  once, with the prelude, so a document's code gives this program's own
  values. A parameter can have a type and a lambda what it returns; a
  lambda that calls itself needs both. Errors come back at the node
  they're about, which is drawn on red.
- `Editor.lean`, `Outside.lean`, `Main.lean`: the editor as a deui app; what
  reaches it from outside (fresh ids, evaluations' results, what
  projections that are functions give, the clipboard, saving); and the
  program. The view is deui's pieces composed, and `view_ok` follows from
  theirs: the scene on screen is the view of the model. The model's edits
  say what changed (`Model.lean`): a handler changes what the view reads
  only by a `Change`, which the model notes, so the state the app holds is
  the model the handler made. `Entries.lean` turns those edits into edits
  of the document's parts: an entry written within is its part written at
  that path. Each part keeps its own: the cells it asked for, its frames,
  and how they're laid out (`Deui/Fit.lean`). A definition written grows
  again only the parts that asked for it (`item_untouched`); typing grows
  again the one frame it's in, and what's laid out again is the frames
  above it, each walked once; a selection that only moves is a wash under
  the text, and lays nothing out.

A kind's records are drawn by its def's `projection`, written in the
document: a layout (`row`, `column`, `indent`, `either`, `words`, `faint`,
and `part`, which draws the record's own value at a field, where it's
edited), or a function of the record that gives one. A layout as it stands
is read with no code run; a function is run by Lean on each record of the
kind. `examples/projections.gid` has one of each: a fraction, and a bar as
long as its amount.

On a notebook of 3,300 lines in 300 entries (`progred_measure 300`): the
wheel takes about 25 µs, an arrow key 50 µs, a keystroke of typing 0.2 to
0.35 ms, an element added or taken away or an undo up to 0.6 ms, and
writing a definition that a tenth of the entries reach 4 ms, against 20 ms
to lay the document out from nothing. On the same entries as one part, a
list at the root (`progred_measure 300 one`): an arrow key 50 µs and a
keystroke 0.5 to 0.6 ms; before a part's layout had a derivative, each
took a third of a second.

Keys: Tab and Shift+Tab go to the next and previous place a value can go;
type to fill it, and Return takes the chosen offer (Up and Down choose).
`[`, `{` and `(` in an empty place make a list, a record and a cell; a
leading `"` makes text. The arrows move over what's drawn. Typing on text,
a number or a name edits it in place. Return on a value adds a peer after
it (Shift: before), Ctrl+Return adds within it. Backspace deletes a value,
leaving a hole, and again removes the hole. Space folds or opens a cell.
Ctrl+C, Ctrl+X and Ctrl+V copy, cut and paste a value, as GID text on the
system clipboard. Ctrl+Z undoes, Ctrl+Shift+Z redoes, Ctrl+S saves. A
colon on a parameter gives it a type, and on a lambda what it returns.

## Building

```bash
lake build                                   # checks every law
lake build todo && .lake/build/bin/todo      # plays events through the to-do list
lake build todo_window && .lake/build/bin/todo_window   # the to-do list in a window
lake build todo_long && .lake/build/bin/todo_long       # with 10,000 items
lake build progred && .lake/build/bin/progred examples/tour.gid # Progred, on a notebook that says what to try
.lake/build/bin/progred notes.gid                       # or on a file it makes or opens
lake build progred_play && .lake/build/bin/progred_play # plays keys through Progred, with no window
.lake/build/bin/progred_play '<tab> note <enter> eva <enter> add <enter> 1 <enter> <tab> 2 <enter>' # or keys of your own
.lake/build/bin/progred examples/projections.gid        # kinds drawn by projections in the document
lake build progred_measure && .lake/build/bin/progred_measure 300  # what events cost, on a notebook of 300 entries
lake build progred_derived && .lake/build/bin/progred_derived 300  # a spike: drawing as composed derivatives, against the view as it is
```

Lean comes from [elan](https://github.com/leanprover/elan), at the version
in `lean-toolchain`. Progred runs Lean at run time, so `lean` has to be on
the `PATH` when it starts: it loads the toolchain's own library from there.
Its binary is large (about 235 MB), since Lean itself is linked in. Skinny's
prelude is loaded from the build's library, beside the program
(`.lake/build/lib/lean`); moved away from it, the program runs, without
the projections that are functions.
`gid_show` prints files as Progred shows them, and `gid_round_trip` checks
that files read and write back the same.

The window needs, installed on the system, their headers to build and their
libraries to run:

- [SDL3](https://libsdl.org) (`libSDL3.so.0`), and a Vulkan driver.
- [wgpu-native](https://github.com/gfx-rs/wgpu-native) v29.0.1.1
  (`libwgpu_native.so`, and `webgpu/webgpu.h`), the version ThorVG is
  built against: its C API still changes between releases.
- [ThorVG](https://github.com/thorvg/thorvg) 1.1.4, built against that
  wgpu-native with its WebGPU engine, its TrueType loader and its C API
  (`libthorvg-1.so.1`, and `thorvg-1/thorvg_capi.h`): meson's
  `-Dengines=wg -Dloaders=ttf -Dbindings=capi`.

The to-do list's view shows what fits the window's height at launch, and
doesn't follow a resize yet; Progred's does.

The to-do list looks for Liberation Sans at
`/usr/share/fonts/liberation/LiberationSans-Regular.ttf`, and Progred for
Liberation Mono or DejaVu Sans Mono; without a font, labels are left out,
and the window says why.

Tested with Lean 4.34.0, SDL 3.4.20, wgpu-native 29.0.1.1 and ThorVG 1.1.4,
on Mesa's software Vulkan driver, under Xvfb (driven by xdotool) and
headless Weston at scale 2, where it drew the same pixels as bend-deui
before the list scrolled. Only the rows that show are drawn, so the list's
length doesn't cost anything per frame: on Mesa's software Vulkan, a
keystroke costs about 23 ms of CPU with 10,000 items and ten rows showing,
and 15 ms with two items, all of it drawing.

The approach follows Phil Freeman's
[Purview](https://github.com/paf31/purescript-purview) and
[purescript-incremental-functions](https://github.com/paf31/purescript-incremental-functions),
from the theory in Cai, Giarrusso, Rendel and Ostermann, ["A Theory of
Changes for Higher-Order Languages"](https://arxiv.org/abs/1312.0658).
`Cached` is the cache-transfer style of Giarrusso, Régis-Gianas and
Schuster's "Incremental λ-Calculus in Cache-Transfer Style".
