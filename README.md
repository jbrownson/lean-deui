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
- `App.lean`: an app: a state, a `Cached` view from runs of its edits to
  runs of the scene's, and handlers, from the state and what a press hit,
  a key, text typed or the wheel, to edits. An event's edits go to the state, and
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
  window and its events, [wgpu-native](https://github.com/gfx-rs/wgpu-native)
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

## Building

```bash
lake build                                   # checks every law
lake build todo && .lake/build/bin/todo      # plays events through the to-do list
lake build todo_window && .lake/build/bin/todo_window   # the to-do list in a window
lake build todo_long && .lake/build/bin/todo_long       # with 10,000 items
```

Lean comes from [elan](https://github.com/leanprover/elan), at the version
in `lean-toolchain`.

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

The window's size is fixed: the view shows what fits its height, which it
takes at launch.

It looks for Liberation Sans at
`/usr/share/fonts/liberation/LiberationSans-Regular.ttf`; without it, labels
are left out, and it says why.

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
