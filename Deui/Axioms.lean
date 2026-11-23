import Deui.Column
import Deui.Drawn
import Deui.Scroll
import Deui.App

/-! Every law's axioms, checked by `lake build`: it fails on a `sorry` or a
new axiom. -/

/-- info: 'Deui.compose_ok' does not depend on any axioms -/
#guard_msgs in #print axioms Deui.compose_ok

/-- info: 'Deui.cached_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Deui.cached_ok

/-- info: 'Deui.Column.inc_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Deui.Column.inc_ok

/-- info: 'Deui.Lists.map_inc_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Deui.Lists.map_inc_ok

/-- info: 'Deui.App.play_shows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Deui.App.play_shows

/-- info: 'Deui.App.turns_edits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Deui.App.turns_edits

/-- info: 'Deui.Lists.Scrolled.view_inc_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Deui.Lists.Scrolled.view_inc_ok

/-- info: 'Deui.Drawing.inc_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Deui.Drawing.inc_ok
