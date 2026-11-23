import Deui.Lists

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
  deriving BEq, Repr

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
  | .insert i c, .group x y cs => .group x y (Lists.insert cs i c)
  | .delete i, .group x y cs => .group x y (Lists.remove cs i)
  | .update i e, .group x y cs => .group x y (cs.modify i e.apply)
  | .shift i dx dy, .group x y cs => .group x y (shifted dx dy cs i)
  | _, s => s

abbrev sceneEdits : EditStructure := ⟨Scene, SceneEdit, SceneEdit.apply⟩

end Deui

namespace Deui

/-! ## Hitting -/

/-- What a point lands on: the path to the target, through each group's
children by position, and the target's tag. The path is the target's
identity: the scene's edits keep it current. -/
structure Hit where
  path : List Nat
  tag : UInt32

/-- Whether `p` is in the span from `lo`, `size` long. -/
def within (lo size p : Int32) : Bool := lo ≤ p && p < lo + size

mutual
/-- What the point `(px, py)` lands on in a scene: the topmost target
containing it. A group's offset moves the point into its children's
coordinates. -/
def Scene.hit (px py : Int32) : Scene → Option Hit
  | .target x y w h t => if within x w px && within y h py then some ⟨[], t⟩ else .none
  | .group x y cs => Scene.hitAmong (px - x) (py - y) 0 cs
  | _ => .none

/-- What the point lands on among children, the first at position `i`:
what's drawn later is on top, so later children are asked first. -/
def Scene.hitAmong (px py : Int32) (i : Nat) : List Scene → Option Hit
  | [] => .none
  | c :: cs =>
    match Scene.hitAmong px py (i + 1) cs with
    | some h => some h
    | .none => (c.hit px py).map fun h => ⟨i :: h.path, h.tag⟩
end

end Deui
