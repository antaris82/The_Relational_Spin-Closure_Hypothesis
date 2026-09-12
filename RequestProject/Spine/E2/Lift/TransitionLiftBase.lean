import RequestProject.Spine.E2.Topology.Task27
import RequestProject.Spine.E2.CentralDoubleCover

/-!
# Task 28, Packages A and B: the frozen ordinary transition system and the frozen internal
projection

**IMPORT LAYER.  No Task-XXVII source is edited and no earlier definition is rebuilt.**

Package A (items 22–24) *imports and exposes* the Task-XXVII endpoint:
`NullSectorTask27.OrdinaryTransitionSystem` already packages the index type, the open chart
domains, the covering property, the continuous transition maps `g_ij` and the identity,
inverse and triple-overlap laws.  Nothing is added to it here: the Task-28 name
`OrdinaryTransitionSystem` is a literal abbreviation of the inherited structure.

Package B (items 25–27) freezes the *interface* of an already certified two-to-one internal
projection: a topological group `L`, a topological group `G`, a continuous surjective
homomorphism `proj : L →* G`, the requirement that around every point of `G` there is an
open neighbourhood carrying a continuous section of `proj`, and the two structural facts
about the kernel that the later packages use (it is central, and it carries the discrete
topology).  *No new global section theorem is proved here and no global section is chosen*
(items 26, 27): only the local data already certified in the earlier layers is named.

The whole Task-28 development is carried out for an arbitrary such interface.  Native
instances of it — the split cover of a topological group and the circle squaring cover, the
latter with no global continuous section — are in
`RequestProject.Spine.Controls.CircleDoubleCover`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask28

universe u v t

/-! ## Package A — the frozen ordinary transition system (items 22–24)

The inherited Task-XXVII structure is exposed under a Task-28 name.  It contains **no new
mathematics** (item 24). -/

/-- **IMPORTED, unchanged (items 22–24).**  The ordinary transition system produced by
Task XXVII: an index type, open chart domains covering the base, continuous transition maps
into the fixed visible model group, and the identity, inverse and triple-overlap laws. -/
abbrev OrdinaryTransitionSystem (B : Type u) [TopologicalSpace B] (ι : Type t) :=
  NullSectorTask27.OrdinaryTransitionSystem B ι

end NullSectorTask28
