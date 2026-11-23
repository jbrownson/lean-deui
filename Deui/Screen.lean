import Deui.App

/-!
The screen: a window, its events, and the scene it keeps. `native/screen.c`
does it with SDL3 (the window and its events), wgpu-native (WebGPU, on
Vulkan) and ThorVG (drawing), each opened with `dlopen`.

The screen keeps a copy of the scene, set once, then changed only by the
scene's edits, which it applies as `SceneEdit.apply` does, reading them as
Lean values. A frame only asks ThorVG to draw what it keeps.
-/

namespace Deui.Screen

open Deui App

opaque WindowPointed : NonemptyType

/-- A window, closed when it's dropped or by `close`. -/
def Window : Type := WindowPointed.type

instance : Nonempty Window := WindowPointed.property

/-- A window of the given size, with its title. -/
@[extern "deui_window_open"]
opaque Window.open (title : @& String) (width height : UInt32) : IO Window

/-- The TrueType font labels are drawn in. -/
@[extern "deui_window_font"]
opaque Window.font (w : @& Window) (path : @& String) : IO Unit

/-- The events that came, as words, waiting up to `ms` milliseconds for the
first (4294967295: for as long as it takes). Each event is its length in
words, then its kind and fields; `readEvents` reads them. -/
@[extern "deui_window_wait"]
opaque Window.waitWords (w : @& Window) (ms : UInt32) : IO (Array UInt32)

/-- Sets the scene the screen keeps. -/
@[extern "deui_window_set_scene"]
opaque Window.setScene (w : @& Window) (s : @& Scene) : IO Unit

/-- Applies a run of edits to the scene the screen keeps. -/
@[extern "deui_window_edit"]
opaque Window.edit (w : @& Window) (es : @& List SceneEdit) : IO Unit

/-- Draws the scene the screen keeps on a background of 0xRRGGBB, and
shows it. -/
@[extern "deui_window_draw"]
opaque Window.draw (w : @& Window) (background : UInt32) : IO Unit

@[extern "deui_window_close"]
opaque Window.close (w : @& Window) : IO Unit

/-! ## Events

Each event's words, after its length: its kind, then its fields, a
coordinate as a Float's 64 bits in two words, high first.
  1 x y button down   a mouse button, W3C's numbering, down 1 or 0
  2 x y               the mouse moved
  3 code down mods    a key, and the modifiers held (App.Mods)
  4 c c ...           text typed, as code points
  5 x y dx dy         the wheel, under (x, y)
  6                   the window asked to close
  7                   the mouse left the window
  8 on                the window gained (1) or lost (0) the focus
  9 width height      the window's new size -/

def float (ws : Array UInt32) (i : Nat) : Float :=
  Float.ofBits ((ws.getD i 0).toUInt64 <<< 32 ||| (ws.getD (i + 1) 0).toUInt64)

def event (ws : Array UInt32) : Option Event :=
  let w := ws.getD
  match w 0 0 with
  | 1 => some (.press (float ws 1) (float ws 3) (w 5 0) (w 6 0 != 0))
  | 2 => some (.move (float ws 1) (float ws 3))
  | 3 => some (.key (w 1 0) (w 2 0 != 0) (w 3 0))
  | 4 => some (.text (String.ofList ((ws.extract 1 ws.size).toList.map fun c => Char.ofNat c.toNat)))
  | 5 => some (.scroll (float ws 1) (float ws 3) (float ws 5) (float ws 7))
  | 6 => some .close
  | 7 => some .leave
  | 8 => some (.focus (w 1 0 != 0))
  | 9 => some (.resize (w 1 0) (w 2 0))
  | _ => .none

/-- The events, from their words. -/
partial def readEvents (ws : Array UInt32) (at_ : Nat := 0) (acc : Array Event := #[]) : Array Event :=
  if at_ < ws.size then
    let n := (ws.getD at_ 0).toNat
    let acc := match event (ws.extract (at_ + 1) (at_ + 1 + n)) with
      | some e => acc.push e
      | .none => acc
    readEvents ws (at_ + 1 + n) acc
  else acc

def Window.events (w : @& Window) : IO (List Event) := do
  return (readEvents (← w.waitWords 4294967295)).toList

/-! ## Running an app -/

variable {cs : EditStructure}

/-- Draws the scene the screen keeps, waits for events, plays them through
the app, and sends the screen the edits they made to the scene, until the
window closes. By `turns_edits`, the scene the screen keeps stays the scene
on screen. -/
partial def loop (app : App cs) (w : Window) (background : UInt32) (m : Model app) : IO Unit := do
  w.draw background
  let es ← w.events
  let (m', edits) := turns app m es
  w.edit edits
  unless es.any (· matches .close) do
    loop app w background m'

/-- As `loop`, and after each batch of events asks `outside` for edits that
come from outside the app: results of work, something read. They go to the
state and the screen as an event's do (`edited_shows`, `edited_edits`). -/
partial def loopWith (app : App cs) (outside : cs.Value → IO (List cs.Edit)) (w : Window)
    (background : UInt32) (m : Model app) : IO Unit := do
  let (m, edits) := edited app m (← outside m.state)
  w.edit edits
  w.draw background
  let es ← w.events
  let (m, edits) := turns app m es
  w.edit edits
  unless es.any (· matches .close) do
    loopWith app outside w background m

/-- Runs an app in a window of the given size on a background of 0xRRGGBB,
its labels in the TrueType font at `font`, from `state`, until the window
closes. `outside`, if given, supplies edits from outside the app after each
batch of events. -/
def run (app : App cs) (title font : String) (width height background : UInt32)
    (state : cs.Value) (outside : Option (cs.Value → IO (List cs.Edit)) := none) : IO Unit := do
  let w ← Window.open title width height
  try w.font font catch e => IO.println s!"no font, so labels are left out: {e}"
  let m := start app state
  w.setScene m.scene
  match outside with
  | some outside => loopWith app outside w background m
  | none => loop app w background m
  w.close

end Deui.Screen
