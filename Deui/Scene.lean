import Deui.List

/-!
What's on the screen: a tree of fills, labels, targets and groups, each at
an offset from the group it's in, so moving anything is one edit. A group's
children are a list.
-/

namespace Deui

inductive Scene where
  | fill (x y w h : Int32) (color : UInt32)
  | label (x y : Int32) (size color : UInt32) (text : String)
  | target (x y w h : Int32) (tag : UInt32)
  | group (x y : Int32) (children : List Scene)

/-- A scene's edits. `translate` moves a fill, a label, a target or a group.
`insert`, `delete`, `update` and `shift` act on a group's children by
position: `update` applies an edit to the child at a position, and `shift`
translates every child from a position on. An edit that doesn't fit what it
meets leaves it as it is. -/
inductive SceneEdit where
  | translate (dx dy : Int32)
  | insert (i : Nat) (child : Scene)
  | delete (i : Nat)
  | update (i : Nat) (e : SceneEdit)
  | shift (i : Nat) (dx dy : Int32)

def Scene.translate (dx dy : Int32) : Scene → Scene
  | .fill x y w h c => .fill (x + dx) (y + dy) w h c
  | .label x y z c t => .label (x + dx) (y + dy) z c t
  | .target x y w h t => .target (x + dx) (y + dy) w h t
  | .group x y cs => .group (x + dx) (y + dy) cs

/-- The children from position `i` on, translated. -/
def shifted (dx dy : Int32) : List Scene → Nat → List Scene
  | [], _ => []
  | h :: t, 0 => h.translate dx dy :: shifted dx dy t 0
  | h :: t, i + 1 => h :: shifted dx dy t i

/-- The scene after one edit. -/
def SceneEdit.apply : SceneEdit → Scene → Scene
  | .translate dx dy, s => s.translate dx dy
  | .insert i c, .group x y cs => .group x y (insertAt cs i c)
  | .delete i, .group x y cs => .group x y (removeAt cs i)
  | .update i e, .group x y cs => .group x y (cs.modify i e.apply)
  | .shift i dx dy, .group x y cs => .group x y (shifted dx dy cs i)
  | _, s => s

abbrev sceneEdits : EditStructure := ⟨Scene, SceneEdit, SceneEdit.apply⟩

end Deui
