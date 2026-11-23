import Deui

/-!
A to-do list, as long as it gets, in a window that shows what fits. Click
an item's box to tick it and its x to delete it; Return starts a new item
at the top, typing writes into it, Backspace takes a letter back, and the
wheel scrolls. Its state is the list held scrolled (`Scroll`); its view is
what shows in a window `height` tall (`Scrolled.view.inc`), drawn as rows
on the screen (`Drawing.inc`), each `cached` and joined by `compose`, so its
derivative's law follows from theirs (`viewOk`). Only the rows that show
are in the scene.
-/

namespace Examples.Todo

open Deui

structure Item where
  text : String
  done : Bool

/-- An item changes by being replaced; the items change as a list does,
or scroll. Each item's row is 40 pixels tall. -/
abbrev itemEdits : EditStructure := whole (plain Item)
def rowHeight (_ : Item) : Nat := 40
abbrev itemsEdits : EditStructure := Lists.Scrolled.Scroll.editStructure itemEdits rowHeight

/-- The window's height, in pixels. -/
def height : Int := 400

def boxColor : Bool → UInt32
  | true => 5294180
  | false => 5592405

/-- An item's row: its box and a target over it (tag 1), its text, and an x
with a target over it (tag 2). -/
def rowOf (item : Item) : Column.Row :=
  ⟨40, .group 0 0 [
    .fill 0 0 360 38 3158326,
    .fill 10 9 20 20 (boxColor item.done),
    .target 10 9 20 20 1,
    .label 42 9 18 15132390 item.text,
    .label 334 9 18 14706771 "x",
    .target 320 0 40 38 2]⟩

/-- What shows of the items, then those rows on the screen, each keeping
its input for its derivative. -/
def view : Cached (runs itemsEdits) (runs sceneEdits) :=
  compose (cached (Lists.Scrolled.view.inc itemEdits rowHeight height))
    (cached (Drawing.inc fun it => (rowOf it).s))

/-- The view's derivative is correct: each part's is, by its law. -/
theorem viewOk : view.ok :=
  compose_ok _ _
    (cached_ok _ (Lists.Scrolled.view_inc_ok itemEdits rowHeight height))
    (cached_ok _ (Drawing.inc_ok _))

/-! ## Handlers -/

abbrev Items := Lists.Scrolled.Scroll Item
abbrev Edits := List (Lists.Scrolled.Scroll.Edit itemEdits)

/-- The position in the list of the row `k`-th from the top of what shows. -/
def position (z : Items) (k : Nat) : Nat :=
  (Lists.Scrolled.Scroll.normalize rowHeight z).above.length + k

/-- A press on a row's box ticks it, on its x deletes it: the row's place
among what shows is the first step of the path to the target. -/
def press (z : Items) : Hit → Edits
  | ⟨k :: _, 1⟩ =>
    let i := position z k
    match z.rows[i]? with
    | some it => [.list (.update i (.replace ⟨it.text, !it.done⟩))]
    | .none => []
  | ⟨k :: _, 2⟩ => [.list (.delete (position z k))]
  | _ => []

/-- The first item, rewritten by `f`. -/
def first (z : Items) (f : String → String) : Edits :=
  match z.rows with
  | it :: _ => [.list (.update 0 (.replace ⟨f it.text, it.done⟩))]
  | [] => []

/-- Return starts a new item at the top; Backspace takes a letter from it. -/
def key (z : Items) : UInt32 → Edits
  | 13 => [.list (.insert 0 ⟨"", false⟩)]
  | 127 => first z fun t => t.dropEnd 1 |>.toString
  | _ => []

/-- Typing writes into the first item. -/
def text (z : Items) (t : String) : Edits := first z (· ++ t)

/-- The wheel scrolls a row's height a notch: toward the top scrolls up. -/
def scroll (_ : Items) (dy : Float) : Edits :=
  [.scroll (-(dy * 40).toInt64.toInt)]

def app : App.App itemsEdits where
  view := view
  respond := App.handlers press key text scroll

def items : Items := ⟨[], [⟨"Buy milk", false⟩, ⟨"Write laws", false⟩], 0⟩

end Examples.Todo
