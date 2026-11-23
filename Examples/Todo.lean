import Deui

/-!
A to-do list. Click an item's box to tick it and its x to delete it; Return
starts a new item at the top, typing writes into it, and Backspace takes a
letter back. Its view is an item's row mapped over the list (`map.inc`),
then the column, each `cached` and joined by `compose`, so its derivative's
law follows from theirs (`viewOk`).
-/

namespace Examples.Todo

open Deui

structure Item where
  text : String
  done : Bool

/-- An item changes by being replaced; the items change as a list does. -/
abbrev itemEdits : EditStructure := whole (none Item)
abbrev itemsEdits : EditStructure := Lists.editStructure itemEdits

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

/-- An item's row, for items that change only by being replaced: none of
their own edits, so its derivative is never asked. -/
def rowPlain : Inc (none Item) (none Column.Row) := ⟨rowOf, fun _ e => nomatch e⟩

def row : Inc itemEdits Column.rowEdits := whole.lift rowPlain

/-- The items' rows, then the column of them, each keeping its input for
its derivative. -/
def view : Cached (runs itemsEdits) (runs sceneEdits) :=
  compose (cached (Lists.map.inc row)) (cached Column.inc)

/-- The view's derivative is correct: each part's is, by its law. -/
theorem viewOk : view.ok :=
  compose_ok _ _
    (cached_ok _ (Lists.map_inc_ok _ (whole_lift_ok _ fun _ e => nomatch e)))
    (cached_ok _ Column.inc_ok)

/-! ## Handlers -/

/-- A press on a row's box ticks it, on its x deletes it: the row's position
is the first step of the path to the target. -/
def press (items : List Item) : Hit → List (Lists.Edit.of itemEdits)
  | ⟨i :: _, 1⟩ =>
    match items[i]? with
    | some it => [.update i (.replace ⟨it.text, !it.done⟩)]
    | .none => []
  | ⟨i :: _, 2⟩ => [.delete i]
  | _ => []

/-- The first item, rewritten by `f`. -/
def first (items : List Item) (f : String → String) : List (Lists.Edit.of itemEdits) :=
  match items with
  | it :: _ => [.update 0 (.replace ⟨f it.text, it.done⟩)]
  | [] => []

/-- Return starts a new item at the top; Backspace takes a letter from it. -/
def key (items : List Item) : UInt32 → List (Lists.Edit.of itemEdits)
  | 13 => [.insert 0 ⟨"", false⟩]
  | 127 => first items fun t => t.dropEnd 1 |>.toString
  | _ => []

/-- Typing writes into the first item. -/
def text (items : List Item) (t : String) : List (Lists.Edit.of itemEdits) :=
  first items (· ++ t)

def app : App.App itemsEdits := ⟨view, press, key, text⟩

def items : List Item := [⟨"Buy milk", false⟩, ⟨"Write laws", false⟩]

end Examples.Todo
