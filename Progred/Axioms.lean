import Progred.Editor
import Progred.Derived.Forms

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

/-- info: 'Progred.Editor.item_untouched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Editor.item_untouched

/-- info: 'Progred.Model.defined_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Model.defined_other

/-- info: 'Progred.Display.input_of_not_touched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Display.input_of_not_touched

/-- info: 'Progred.Entries.edits_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Entries.edits_ok

/-- info: 'Progred.Editor.source_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Editor.source_ok

/-- info: 'Progred.Editor.drawn_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Editor.drawn_ok

/-- info: 'Progred.Editor.part_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Editor.part_ok

/-- info: 'Progred.Display.reselect_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Display.reselect_ok

/-- info: 'Progred.Display.rewrite_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Display.rewrite_ok

/-- info: 'Progred.Editor.drawn_df_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Editor.drawn_df_ok

/-- info: 'Progred.Model.back_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Model.back_ok

/-- info: 'Progred.Model.back_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Model.back_cells

/-- info: 'Progred.Display.reshaped_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Progred.Display.reshaped_ok

/-- info: 'Progred.Derived.rewrite_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Derived.rewrite_ok

/-- info: 'Progred.Derived.lines_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Derived.lines_ok

/-- info: 'Progred.Derived.treed_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Progred.Derived.treed_ok
