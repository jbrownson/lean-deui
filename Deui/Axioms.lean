import Deui.Column

/-! Every law's axioms, checked by `lake build`: it fails on a `sorry` or a
new axiom. -/

/-- info: 'Deui.compose_ok' does not depend on any axioms -/
#guard_msgs in #print axioms Deui.compose_ok

/-- info: 'Deui.cached_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Deui.cached_ok

/-- info: 'Deui.inc_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Deui.inc_ok
