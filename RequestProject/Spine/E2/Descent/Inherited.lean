import RequestProject.Spine.E2.Lift.LiftLevels

/-!
# Task 29, Package A: the frozen Task-XXVIII endpoint

**IMPORT LAYER.  No Task-XXVIII (or earlier) source is edited, no inherited statement is
changed, and no new mathematics appears in this module (items 20–22).**

The whole of Task XXIX is developed for an arbitrary frozen internal projection
`P : InternalProjection L G` and an arbitrary continuous ordinary transition system
`S : TransitionSystem B ι G`, exactly as they were fixed in Task XXVIII.  The inherited
objects that Task XXIX actually uses are, in the order in which they are used:

| Inherited object | Where it comes from |
| --- | --- |
| `NullSectorTask28.InternalProjection` | Task 28, Package B (the frozen internal projection interface) |
| `InternalProjection.Ker` | the central, discrete kernel of the frozen projection |
| `InternalProjection.IsInternalRepOn` | continuous internal representative on a subset |
| `InternalProjection.IsKerFunOn` | continuous kernel-valued function on a subset |
| `InternalProjection.relFactor` | `fun x => v x * (u x)⁻¹`, the inherited comparison convention |
| `InternalProjection.isInternalRepOn_kerFun_mul` | a kernel-valued change of a representative is a representative |
| `InternalProjection.relFactor_isKerFunOn` | two representatives of one ordinary map differ by a continuous kernel function |
| `InternalProjection.isLocallyConstant_toKerFun` | continuous kernel-valued functions are locally constant |
| `NullSectorTask28.TransitionSystem` | ordinary cover domains `U i`, transitions `g i j`, identity/inverse/triple laws |
| `TransitionSystem.tripleDom`, `incIJ`, `incJK`, `incIK` | triple-overlap domain and its three inclusions |
| `NullSectorTask28.InternalTransitionCandidate` | refined overlaps `V i j a` + stored representatives `u i j a` |
| `InternalTransitionCandidate.defect`, `defectDom` | the Task-XXVIII triple defect `δ` and its domain |
| `InternalProjection.tripleDefect` | `fun x => (u_jk x * u_ij x) * (u_ik x)⁻¹` |
| `InternalProjection.triple_defect_change_of_rep` | `δ' = (ε_jk * ε_ij * ε_ik⁻¹) * δ` |
| `InternalProjection.quadruple_defect_consistency` | the quadruple-overlap law |
| `NullSectorTask28.IsCompatibleInternalTransitionSystem` | all triple defects of a candidate are `1` |
| `NullSectorTask28.CanTrivialiseSimultaneously` | the inherited frontier predicate, isolated in Task 28 |

None of these is redefined here; Task XXIX only *uses* them.  In particular the ordinary
transition system, the internal projection, its kernel and the Task-XXVIII triple defect are
used exactly as inherited (items 3–6).
-/

namespace NullSectorTask29

open NullSectorTask28

section InheritedChecks

/-! ## Inherited declarations actually used by Task XXIX (item 21) -/

-- Package B of Task 28 — the frozen projection interface and its kernel.
#check @NullSectorTask28.InternalProjection
#check @NullSectorTask28.InternalProjection.Ker
#check @NullSectorTask28.InternalProjection.IsInternalRepOn
#check @NullSectorTask28.InternalProjection.IsKerFunOn
#check @NullSectorTask28.InternalProjection.relFactor
#check @NullSectorTask28.InternalProjection.isInternalRepOn_kerFun_mul
#check @NullSectorTask28.InternalProjection.relFactor_isKerFunOn
#check @NullSectorTask28.InternalProjection.isLocallyConstant_toKerFun

-- Package A of Task 28 — the ordinary transition system and its triple overlaps.
#check @NullSectorTask28.TransitionSystem
#check @NullSectorTask28.TransitionSystem.tripleDom
#check @NullSectorTask28.TransitionSystem.g_trans_on

-- Packages H, J, K, P of Task 28 — the defect, its change law, quadruple consistency,
-- the refined candidate interface and the isolated frontier predicate.
#check @NullSectorTask28.InternalProjection.tripleDefect
#check @NullSectorTask28.InternalProjection.triple_defect_change_of_rep
#check @NullSectorTask28.InternalProjection.quadruple_defect_consistency
#check @NullSectorTask28.InternalTransitionCandidate
#check @NullSectorTask28.InternalTransitionCandidate.defect
#check @NullSectorTask28.InternalTransitionCandidate.defectDom
#check @NullSectorTask28.IsCompatibleInternalTransitionSystem
#check @NullSectorTask28.CanTrivialiseSimultaneously

end InheritedChecks

end NullSectorTask29
