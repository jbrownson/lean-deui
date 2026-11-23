# deui for Lean

deui, said "dewey": dUI, the change in the UI. A view is a pure function of
one state, and deui gives it a derivative: from the state and a change to
it, the change to the screen. A law says the derivative is right: applying
its change gives what drawing again would.

This is a port of [bend-deui](https://github.com/jbrownson/bend-deui), to
see how the same laws read and prove in Lean. So far:

- `Deui/Change.lean`: edit structures, `Inc` and `Inc.ok`, `runs`, `whole`,
  `lift`, `whole.lift`, `recompute` (from
  [lean-puri](https://github.com/jbrownson/lean-puri)'s port), and deui's
  `Cached` (an incremental function that keeps what its derivative needs),
  `cached` and `compose`, with `cached_ok` and `compose_ok`.
- `Deui/List.lean`: a list's edits: insert, delete, update in place.
- `Deui/Scene.lean`: what's on the screen, a tree of fills, labels, targets
  and groups, each at an offset from its group, and its edits, `shift`
  among them. A group's children are a list.
- `Deui/Column.lean`: rows stacked from the top. Its derivative turns an
  edit to the rows into a few edits to its scene; `one_ok` and `inc_ok` say
  it's correct for every edit and every run of them.
- `Deui/Axioms.lean`: the laws' axioms, checked by `lake build`, which
  fails on a `sorry` or a new axiom.

## Building

```bash
lake build
```

Lean comes from [elan](https://github.com/leanprover/elan), at the version
in `lean-toolchain`. There are no other dependencies yet.
