import Deui.Column
import Deui.Drawn
import Deui.Scroll
import Deui.App
import Deui.Anchored
import Deui.Fit
import Deui.Join
import Deui.Under
import Deui.Tree

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

/-- info: 'Deui.App.play_shows' depends on axioms: [propext] -/
#guard_msgs in #print axioms Deui.App.play_shows

/-- info: 'Deui.App.turns_edits' depends on axioms: [propext] -/
#guard_msgs in #print axioms Deui.App.turns_edits

/-- info: 'Deui.Lists.Scrolled.view_inc_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Deui.Lists.Scrolled.view_inc_ok

/-- info: 'Deui.Drawing.inc_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Deui.Drawing.inc_ok

/-- info: 'Deui.Cached.second_ok' does not depend on any axioms -/
#guard_msgs in #print axioms Deui.Cached.second_ok

/-- info: 'Deui.Cached.lift_ok' does not depend on any axioms -/
#guard_msgs in #print axioms Deui.Cached.lift_ok

/-- info: 'Deui.layers_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Deui.layers_ok

/-- info: 'Deui.keyed_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Deui.keyed_ok

/-- info: 'Deui.Lists.Scrolled.anchored_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Deui.Lists.Scrolled.anchored_ok

/-- info: 'Deui.Lists.Scrolled.At.inc_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Deui.Lists.Scrolled.At.inc_ok

/-- info: 'Deui.App.applied_shows' depends on axioms: [propext] -/
#guard_msgs in #print axioms Deui.App.applied_shows

/-- info: 'Deui.Text.splice_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Deui.Text.splice_ok

/-- info: 'Deui.Text.rows_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Deui.Text.rows_ok

/-- info: 'Deui.Fit.fit_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Deui.Fit.fit_ok

/-- info: 'Deui.Lists.join_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Deui.Lists.join_ok

/-- info: 'Deui.Lists.mapUnder_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Deui.Lists.mapUnder_ok

/-- info: 'Deui.Lists.swaps_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Deui.Lists.swaps_ok

/-- info: 'Deui.Tree.drawn_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Deui.Tree.drawn_ok

/-- info: 'Deui.Tree.reading_touched' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Deui.Tree.reading_touched
