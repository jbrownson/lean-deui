import Deui.Scene

/-!
An app: a state, edited as its edit structure says, its view, an
incremental function from runs of the state's edits to runs of the scene's
that keeps what its derivative needs, and a handler: from the state, the
scene on screen and an event, to a run of edits. An event's edits go to the state, and through the view's derivative
to the scene on screen. The view itself runs once, at launch.
-/

namespace Deui.App

open Deui

/-- An event, as the screen reports it. Coordinates are in the window's
pixels from its top left. A key is its character in lower case, or Return
13, Tab 9, Escape 27, Backspace 127, Delete 63272, the arrows up, down,
left and right from 63232, Home 63273, End 63275, Page Up 63276, Page Down
63277; `mods` says which modifiers were held (`Mods`). Text is what the
keys typed, never a control character. A scroll's `dy` is toward the top.
`resize` gives the window's new size. -/
inductive Event where
  | press (x y : Float) (button : UInt32) (down : Bool)
  | move (x y : Float)
  | key (code : UInt32) (down : Bool) (mods : UInt32)
  | text (t : String)
  | scroll (x y dx dy : Float)
  | close
  | leave
  | focus (on : Bool)
  | resize (width height : UInt32)

/-! A key event's modifiers, as bits of its `mods`. -/
namespace Mods
def shift : UInt32 := 1
def control : UInt32 := 2
def alt : UInt32 := 4
def super : UInt32 := 8
/-- Whether `mods` has every bit of `m`. -/
def has (mods m : UInt32) : Bool := mods &&& m == m
end Mods

structure App (cs : EditStructure) where
  view : Cached (runs cs) (runs sceneEdits)
  /-- The edits an event makes to the state, given the scene on screen and
  what the view keeps: what it worked out for this state, there to be read
  rather than worked out again. -/
  respond : cs.Value → Scene → view.Cache → Event → List cs.Edit
  /-- Edits that follow an event's, from the state they left and what the
  view keeps for it: what depends on the view of the new state, like
  scrolling to what was just selected. -/
  settle : cs.Value → view.Cache → List cs.Edit := fun _ _ => []

/-- What an app holds between events: its state, and what's shown: the
scene on screen, with what the view keeps. -/
structure Model {cs : EditStructure} (app : App cs) where
  state : cs.Value
  shown : Scene × app.view.Cache

variable {cs : EditStructure} (app : App cs)

def Model.scene {app : App cs} (m : Model app) : Scene := m.shown.1

/-- A pointer's coordinate, in whole pixels. -/
def coordinate (v : Float) : Int32 := (max v 0).toUInt32.toInt32

/-- A handler made of four: from the state and what a press hit, which key
went down, what was typed, or how far the wheel turned. A button pressed
down goes through what it hit in the scene on screen; other events make no
edits. -/
def handlers {cs : EditStructure} {Kept : Type} (press : cs.Value → Hit → List cs.Edit)
    (key : cs.Value → UInt32 → List cs.Edit) (text : cs.Value → String → List cs.Edit)
    (scroll : cs.Value → Float → List cs.Edit) (state : cs.Value) (scene : Scene) (_ : Kept) :
    Event → List cs.Edit
  | .press x y _ true =>
    match scene.hit (coordinate x) (coordinate y) with
    | some h => press state h
    | .none => []
  | .key code true _ => key state code
  | .text t => text state t
  | .scroll _ _ _ dy => scroll state dy
  | _ => []

/-- The model at launch: the state, and its view. -/
def start (state : cs.Value) : Model app := ⟨state, app.view.f state⟩

/-- The model after a run of edits to the state (no edits leave it as it
is, and ask nothing of the view), and the scene edits the
view's derivative made of them, from what the view kept. -/
def edited (m : Model app) : List cs.Edit → Model app × List SceneEdit
  | [] => (m, [])
  | es =>
    let r := app.view.df m.shown.2 es
    (⟨run cs es m.state, (run sceneEdits r.1 m.shown.1, r.2)⟩, r.1)

/-- Edits applied, then the edits that settle them: the model after both,
and the scene edits they made. -/
def applied (m : Model app) (es : List cs.Edit) : Model app × List SceneEdit :=
  let t := edited app m es
  let u := edited app t.1 (app.settle t.1.state t.1.shown.2)
  (u.1, t.2 ++ u.2)

/-- An event's turn: the model after the edits the app answers it with,
settled, and the scene edits they made. -/
def turn (m : Model app) (e : Event) : Model app × List SceneEdit :=
  applied app m (app.respond m.state m.scene m.shown.2 e)

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

/-- If the view's derivative is correct, edits to the state keep the scene
on screen the view of the state, without running the view again. -/
theorem edited_shows (ok : app.view.ok) (m : Model app) (es : List cs.Edit) (h : shows app m) :
    shows app (edited app m es).1 := by
  cases es with
  | nil => exact h
  | cons e t =>
    unfold shows at h ⊢
    simp only [edited]
    rw [← ok, ← h]

/-- And the scene edits they made take the scene on screen before them to
the one after. -/
theorem edited_edits (m : Model app) (es : List cs.Edit) :
    (edited app m es).1.scene = run sceneEdits (edited app m es).2 m.scene := by
  cases es <;> rfl

/-- So an event keeps the scene on screen the view of the state. -/
theorem applied_shows (ok : app.view.ok) (m : Model app) (es : List cs.Edit) (h : shows app m) :
    shows app (applied app m es).1 :=
  edited_shows app ok _ _ (edited_shows app ok m _ h)

/-- Applied edits take the scene on screen before them to the one after. -/
theorem applied_edits (m : Model app) (es : List cs.Edit) :
    (applied app m es).1.scene = run sceneEdits (applied app m es).2 m.scene := by
  simp only [applied]
  rw [run_append, ← edited_edits app m es]
  exact edited_edits app _ _

theorem step_shows (ok : app.view.ok) (m : Model app) (e : Event) (h : shows app m) :
    shows app (step app m e) :=
  applied_shows app ok m _ h

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

/-- A turn's edits take the scene on screen before it to the one after. -/
theorem turn_edits (m : Model app) (e : Event) :
    (turn app m e).1.scene = run sceneEdits (turn app m e).2 m.scene :=
  applied_edits app m _

/-- And its edits take the scene on screen before the events to the one
after them, so a copy kept by those edits stays the scene on screen. -/
theorem turns_edits (es : List Event) :
    ∀ m : Model app, (turns app m es).1.scene = run sceneEdits (turns app m es).2 m.scene := by
  induction es with
  | nil => exact fun _ => rfl
  | cons e es ih =>
    intro m
    simp only [turns]
    rw [run_append, ih, turn_edits]

end Deui.App
