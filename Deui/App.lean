import Deui.Scene

/-!
An app: a state, edited as its edit structure says, its view, an
incremental function from runs of the state's edits to runs of the scene's
that keeps what its derivative needs, and four handlers: from the state
and what a press hit, which key went down, what was typed, or how far the
wheel turned, to a run of edits. An event's edits go to the state, and through the view's derivative
to the scene on screen. The view itself runs once, at launch.
-/

namespace Deui.App

open Deui

/-- An event, as the screen reports it. Coordinates are in the window's
pixels from its top left. A key is Base's code for it: its character in
lower case, Return 13, Backspace 127, the arrows from 63232. Text is what
the keys typed, never a control character. -/
inductive Event where
  | press (x y : Float) (button : UInt32) (down : Bool)
  | move (x y : Float)
  | key (code : UInt32) (down : Bool)
  | text (t : String)
  | scroll (x y dx dy : Float)
  | close
  | leave
  | focus (on : Bool)

structure App (cs : EditStructure) where
  view : Cached (runs cs) (runs sceneEdits)
  press : cs.Value → Hit → List cs.Edit
  key : cs.Value → UInt32 → List cs.Edit
  text : cs.Value → String → List cs.Edit
  scroll : cs.Value → Float → List cs.Edit

/-- What an app holds between events: its state, and what's shown: the
scene on screen, with what the view keeps. -/
structure Model {cs : EditStructure} (app : App cs) where
  state : cs.Value
  shown : Scene × app.view.Cache

variable {cs : EditStructure} (app : App cs)

def Model.scene {app : App cs} (m : Model app) : Scene := m.shown.1

/-- A pointer's coordinate, in whole pixels. -/
def coordinate (v : Float) : Int32 := (max v 0).toUInt32.toInt32

/-- The edits an event makes to the state: a button pressed down, through
what it hit in the scene on screen, a key pressed down, text typed, or the
wheel turned (`dy`, toward the top). Other events make none. -/
def respond (state : cs.Value) (scene : Scene) : Event → List cs.Edit
  | .press x y _ true =>
    match scene.hit (coordinate x) (coordinate y) with
    | some h => app.press state h
    | .none => []
  | .key code true => app.key state code
  | .text t => app.text state t
  | .scroll _ _ _ dy => app.scroll state dy
  | _ => []

/-- The model at launch: the state, and its view. -/
def start (state : cs.Value) : Model app := ⟨state, app.view.f state⟩

/-- An event's turn: the model after it, and the scene edits the view's
derivative made, from what the view kept. -/
def turn (m : Model app) (e : Event) : Model app × List SceneEdit :=
  let es := respond app m.state m.scene e
  let r := app.view.df m.shown.2 es
  (⟨run cs es m.state, (run sceneEdits r.1 m.shown.1, r.2)⟩, r.1)

/-- The model after an event. -/
def step (m : Model app) (e : Event) : Model app := (turn app m e).1

/-- The turn of events, in order: the model after them, and the scene edits
they made, joined. -/
def turns : Model app → List Event → Model app × List SceneEdit
  | m, [] => (m, [])
  | m, e :: es =>
    let t := turn app m e
    let u := turns t.1 es
    (u.1, t.2 ++ u.2)

/-- The model after events, in order. -/
def play (m : Model app) (es : List Event) : Model app := es.foldl (step app) m

/-! ## Laws -/

/-- What's shown is what the view gives for the state: the scene on screen
and what the view keeps, as if the view had run again. -/
def shows (m : Model app) : Prop := m.shown = app.view.f m.state

/-- At launch, the scene on screen is the view of the state. -/
theorem start_shows (state : cs.Value) : shows app (start app state) := rfl

/-- If the view's derivative is correct, an event keeps the scene on screen
the view of the state, without running the view again. -/
theorem step_shows (ok : app.view.ok) (m : Model app) (e : Event) (h : shows app m) :
    shows app (step app m e) := by
  unfold shows at h ⊢
  simp only [step, turn]
  rw [← ok, ← h]

/-- And so does any run of events. -/
theorem play_shows (ok : app.view.ok) (es : List Event) :
    ∀ m : Model app, shows app m → shows app (play app m es) := by
  induction es with
  | nil => exact fun _ h => h
  | cons e es ih => exact fun m h => ih _ (step_shows app ok m e h)

/-- The turn of events holds the model play gives. -/
theorem turns_model (es : List Event) : ∀ m : Model app, (turns app m es).1 = play app m es := by
  induction es with
  | nil => exact fun _ => rfl
  | cons e es ih => exact fun m => ih _

/-- And its edits take the scene on screen before the events to the one
after them, so a copy kept by those edits stays the scene on screen. -/
theorem turns_edits (es : List Event) :
    ∀ m : Model app, (turns app m es).1.scene = run sceneEdits (turns app m es).2 m.scene := by
  induction es with
  | nil => exact fun _ => rfl
  | cons e es ih =>
    intro m
    simp only [turns]
    rw [run_append, ih]
    rfl

end Deui.App
