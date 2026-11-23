import Lake
open Lake DSL

package «lean-deui»

/-- The library: edits, incremental functions, scenes, the column. -/
@[default_target]
lean_lib Deui

/-- The examples: the to-do list. -/
lean_lib Examples

/-- Plays events through the to-do list. -/
lean_exe todo where
  root := `Examples.TodoPlay

/-- The screen's native side (native/screen.c). SDL3, wgpu-native and ThorVG
are opened with `dlopen` when a window opens; only their headers are needed
to build. -/
target screen.o pkg : System.FilePath := do
  let src ← inputTextFile (pkg.dir / "native" / "screen.c")
  buildO (pkg.buildDir / "native" / "screen.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-fPIC", "-O2"] "cc"

target libscreen pkg : System.FilePath := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "screen") #[← screen.o.fetch]

/-- The to-do list in a window. -/
lean_exe todo_window where
  root := `Examples.TodoWindow
  moreLinkObjs := #[libscreen]
  moreLinkArgs := #["-ldl"]

/-- The to-do list with 10,000 items, in a window. -/
lean_exe todo_long where
  root := `Examples.TodoLong
  moreLinkObjs := #[libscreen]
  moreLinkArgs := #["-ldl"]

/-- Progred: a projectional editor, on deui. -/
lean_lib Progred

/-- A spike: Lean built as data and run at run time. -/
lean_exe spike where
  root := `Spike.Runtime
  supportInterpreter := true
