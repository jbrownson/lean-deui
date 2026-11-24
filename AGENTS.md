# Working here

Read `README.md` first for what the repository is.

## How work is read and decided

- **The laws are the reading surface.** A module's theorems, with their
  docstrings, are what gets read; the proofs are checked, not read. Laws
  exist for what a reader needs plus anything tricky.
- **Questions are questions.** A question asked to understand something is
  not a request to change it. When something should change, say so and
  why; for changes to what's read (laws, names, structure), wait for a
  yes. For small, clearly good fixes, decide, do it, and report.
- **Honest assessments.** Don't agree to be agreeable, and don't dress a
  weakness up as a strength. Speed matters in absolute terms, not relative
  ones.
- **Names:** prefer descriptive structure to terse names, and don't
  replace spelled-out terms with new abbreviations without asking.
- **Comments don't document Lean itself.**
- **No caches outside the proofs.** Anything kept to save work is a
  `Cached` result in Lean, with a law that keeps it in sync; the native
  side keeps only what the scene's edits say, applied as `SceneEdit.apply`
  does.

## Changes

- Commit to `main` and push; no pull requests unless asked.
- `lake build` must pass, with `Axioms.lean`'s checks, and the examples
  must run.
- For a new law, run a sabotage check: break the code or the law and
  confirm the checker rejects it.
- `native/screen.c` reads Lean values by their layout: a constructor's
  object fields, then its scalars. When a type it reads changes, check the
  layout with `set_option trace.compiler.ir.result true`.

## Progred

- `docs/progred-port.md` is the reading map for `Progred/`: what the Rust
  version does, what this port decides, and what isn't here yet. Keep its
  last section true as things land.
- `Progred` depends on `Deui`, never the reverse. Something Progred needs
  goes into `Deui` only when it's general.
- A new cell id in source is minted with `openssl rand -hex 16`, and at run
  time with `CellId.new`. Never make one up or derive one from a name.
- `progred_play` plays keys through the editor with no window and prints
  what it would show; try an editing change there first. With arguments it
  plays them as keys (`'<tab> note <enter>'`), from the `.gid` file that's
  the first if there is one; with none, its own walk, whose output is what
  to compare before and after a change. It says so if the layout or the
  scene the view keeps isn't what working it out again gives.
- The view is incremental steps composed (`Progred/Editor.lean`), and
  `view_ok` is their laws composed. A part's frames are grown from its
  `Input` (`Progred/Display.lean`), which has to hold all they read: a
  frame that read anything else would be kept when it shouldn't be.
  Something new the drawing depends on goes into `Seen` and an `Item`'s
  restriction of it, and `touched` then asks it of each part.
- A frame is drawn from its value without what's inside its elements and
  fields (`shallow`), and from the selection only when it's at the frame
  or a step in (`seen`). That's what `Progred/Regrow.lean`'s laws rest on:
  a form that needs to read further in is a kid with a `Hint`, and what a
  frame reads of its whole value goes through `deepOf`.
- A function whose result is used twice binds it once (`let made := …`).
  The compiler doesn't share a call repeated in two branches, and a
  recursive one repeated is exponential.
- The model's edits say what changed, and the view compares nothing to
  find out. What the view reads of the model (the document, the selection,
  the folds, what Lean gave, the scroll, the window's size) is changed only
  by `Model.change`, which notes the change: write the document through
  `Model.write` with the path written at, and the rest through `change`,
  `selecting`, `folding`. Setting one of those fields directly leaves the
  change out of the state the app holds. A stage that needs to know what
  changed gets an edit that says so; it doesn't compare a value with what
  it was.
- The view is being moved to `Progred/Derived/` (`docs/progred-port.md`
  says how far). A form there draws a node from its label alone and
  reads definitions only through `look`; a cell it reads is one of the
  node's keys (`keys1`, `through`). What hangs under a cell is the
  tree's to say (`Derived/Links.lean`), and a form reads only whether
  something does. `progred_derived` with the example
  files says which parts it draws as the view as it is does: that count
  goes up, not down. With a number it times both.
- `progred_measure` says what events cost; run it before and after a
  change to the view, on a notebook (`progred_measure 300`) and on the
  same entries as one part (`progred_measure 300 one`); with `structure`
  it times changes of structure one at a time.
- A record is made with `Value.setField`, which keeps its fields in label
  order, never as a literal list of fields: a write within one that isn't
  in order can't be taken back by a write.
- Skinny is the language: the subset of Lean that `Progred/Skinny.lean`
  makes from a document. A function Lean supplies is a cell in
  `Progred/Builtin.lean` and a case in `Skinny.supplied`; what code is run
  against, besides Lean's library, is `Progred/Prelude.lean`.
- Model what you mean: when something new needs saying, give it its own
  name, step or type, rather than encoding it in a mechanism that means
  something else.
