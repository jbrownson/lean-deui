import Progred.Editor
import Progred.Derived.Part

/-! Progred's laws' axioms, checked by `lake build`: it fails on a `sorry`
or a new axiom. -/

/-- info: 'Progred.Editor.view_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Editor.view_ok

/-- info: 'Progred.Editor.relaid_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Editor.relaid_view

/-- info: 'Progred.Editor.laidOf_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Editor.laidOf_view

/-- info: 'Progred.Display.reach_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Progred.Display.reach_agree

/-- info: 'Progred.Model.defined_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Model.defined_other

/-- info: 'Progred.Display.input_of_not_touched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Display.input_of_not_touched

/-- info: 'Progred.Entries.edits_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Entries.edits_ok

/-- info: 'Progred.Editor.source_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Editor.source_ok

/-- info: 'Progred.Editor.part_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Editor.part_ok

/-- info: 'Progred.Model.back_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Model.back_ok

/-- info: 'Progred.Model.back_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Model.back_cells

/-- info: 'Progred.Derived.rewrite_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Derived.rewrite_ok

/-- info: 'Progred.Derived.lines_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Derived.lines_ok

/-- info: 'Progred.Derived.treed_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Derived.treed_ok

/-- info: 'Progred.Derived.part_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Derived.part_ok
