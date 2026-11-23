import Progred.Outside
import Deui.Screen

/-! Progred, in a window: `progred [file.gid]`. Ctrl+S saves to the file. -/

open Progred

/-- A monospace font, where Arch, Debian and Fedora put one. -/
def fonts : List String := [
  "/usr/share/fonts/liberation/LiberationMono-Regular.ttf",
  "/usr/share/fonts/truetype/liberation/LiberationMono-Regular.ttf",
  "/usr/share/fonts/liberation-mono/LiberationMono-Regular.ttf",
  "/usr/share/fonts/TTF/DejaVuSansMono.ttf",
  "/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf"]

unsafe def main (args : List String) : IO Unit := do
  let file := args.head?.map System.FilePath.mk
  let doc ← match file with
    | some path =>
      if ← path.pathExists then
        match ← GidText.parse (← IO.FS.readFile path) with
        | .ok d => pure d
        | .error e => throw (IO.userError s!"{path}: {e}")
      else pure {}
    | none => pure {}
  let rt ← Run.Runtime.load
  let memo ← IO.mkRef []
  let found ← fonts.filterM fun f => (System.FilePath.mk f).pathExists
  let font := found.headD (fonts.headD "")
  let title := match file with
    | some path => s!"Progred: {path}"
    | none => "Progred"
  Deui.Screen.run Editor.app title font 1000 720 Editor.paper { doc, width := 1000, height := 720 }
    (outside := some (Outside.edits rt memo file ⟨Deui.Screen.clipboardSet, Deui.Screen.clipboardGet⟩))
