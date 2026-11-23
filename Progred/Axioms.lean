import Progred.Editor

/-! Progred's laws' axioms, checked by `lake build`: it fails on a `sorry`
or a new axiom. -/

/-- info: 'Progred.Editor.view_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Editor.view_ok

/-- info: 'Progred.Editor.relaid_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Editor.relaid_view

/-- info: 'Progred.Editor.laidOf_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Editor.laidOf_view
