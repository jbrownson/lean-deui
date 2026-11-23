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
