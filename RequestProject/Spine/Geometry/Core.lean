import RequestProject.Spine.Geometry.TangentInstance
import RequestProject.Spine.Geometry.Z2Class

/-!
# Spine / Geometry / Core : the Task-4 endpoint — the Lorentz-frame Spin-lift obstruction

This module is the production endpoint of the Task-4 layer.  It adds no mathematics; it names
the layer boundaries, records the interpretation boundary and audits the axioms.

Layers, in dependency order:

1. `RequestProject.Spine.Geometry.CausalAlgebra` — the causal algebra of the intrinsic
   carrier: the signature audit of `N_𝒮` (one plus, three minuses), the two causal sign
   lemmas, and the **reduction criterion** `isGLor_of_isometry_of_future_of_det_pos`
   (metric + time orientation + orientation ⟹ membership in the native proper orthochronous
   target `SpinCore.GLor`), together with the two negative controls showing that neither the
   orientation nor the time-orientation hypothesis is redundant.
2. `RequestProject.Spine.Geometry.FrameField` — oriented, time-oriented,
   Lorentz-orthonormal local frame data over an abstract family of four-dimensional real
   fibres, the derived `GLor`-valued transition functions, and the Lorentz frame transition
   cocycle as an object of the Task-3 layer (`CechSpinLift.VisibleCocycle`).
3. `RequestProject.Spine.Geometry.SpinStructure` — the Task-3 obstruction instantiated on
   that cocycle, the Čech notion of a Spin structure on the frame data, the equivalence
   `[c]_frame = 0 ↔ a Spin structure exists`, and the fixed-cover torsor statement.
4. `RequestProject.Spine.Geometry.TangentInstance` — the instantiation of the fibre family
   with the genuine Mathlib tangent spaces of a smooth four-manifold modelled on the
   intrinsic carrier.
5. `RequestProject.Spine.Geometry.Z2Class` — the canonical `{±1} ≅ ℤ/2` identification and
   the additive `ℤ₂`-valued Čech presentation of the obstruction, with the additive
   2-cocycle law, the additive coboundary law and the additive vanishing criterion.

## Status of the `w₂(TM)` identification (mandatory)

**Not proved, and not claimed.**  The pinned Mathlib contains no Stiefel–Whitney classes, no
principal bundles, no Spin structures, no orientation of manifolds, no pseudo-Riemannian or
Lorentzian metrics, and no cohomology of a topological space with `ℤ₂` coefficients in a
usable form.  The conventional class `w₂(TM) ∈ H²(M;ℤ₂)` therefore cannot even be *stated*,
so no theorem here may assert equality with it.

What *is* proved is the strongest statement available:

* the Lorentz frame transition cocycle of an oriented, time-oriented Lorentzian
  tangent-frame datum is `GLor`-valued and satisfies the exact Čech cocycle law;
* its Task-3 Spin-lift obstruction is `{±1}`-valued, independent of the chosen local Spin
  representatives, and vanishes **iff** the frame data admits a Spin structure;
* transported along the canonical isomorphism `{±1} ≅ ℤ/2`, the obstruction is an additive
  `ℤ₂`-valued Čech 2-cocycle on the chosen cover whose class vanishes iff a Spin structure
  exists — i.e. exactly the Čech description under which the classical Stiefel–Whitney
  obstruction is usually presented.

Classification of the Task-4 endpoint: **`VANISHING_EQUIVALENCE_ONLY`** (plus a canonical
`ℤ₂`-Čech presentation of the carrier); literal equality with `w₂(TM)` is **`BLOCKED`** at
library level, not for conceptual reasons.  See `TASK04_AUDIT.md`.

## Interpretation boundary (mandatory)

`[c]_frame = 0` means only that the oriented, time-oriented orthonormal frame data admits a
Spin lift.  It does **not** mean, and nothing here implies, that

* the tangent bundle is trivial or the manifold parallelizable;
* the Spin structure is unique (it is not — see
  `RequestProject.Spine.Controls.Geometry.FlatFrameControl.two_distinct_spinFrameStructures`);
* any curvature `R`, torsion `T` or connection `ω` vanishes;
* spacetime is flat, a gravitational vacuum, globally hyperbolic, or in any synchronization
  equilibrium.

No solder form, tetrad field, spin connection, Levi-Civita lift, curvature, torsion,
holonomy, Cartan geometry, field equation, matter or synchronization notion occurs anywhere
in this layer.
-/

namespace LorentzFrames

/-! ## Axiom audit of the principal Task-4 declarations -/

#print axioms SpinCore.fst_pos_of_BS_pos_of_timelike
#print axioms SpinCore.fst_nonneg_of_BS_nonneg_of_causal
#print axioms SpinCore.isGLorWide_of_isometry_of_future
#print axioms SpinCore.isGLor_of_isometry_of_future_of_det_pos
#print axioms SpinCore.spatialReflI_notMem_GLor
#print axioms SpinCore.timeReflI_not_isGLorWide
#print axioms SpinCore.timeRefl_comp_spatialRefl_notMem_GLor
#print axioms LorentzFrames.LorentzFrameData
#print axioms LorentzFrames.LorentzFrameData.comparison_mem_GLor
#print axioms LorentzFrames.LorentzFrameData.frameCocycle
#print axioms LorentzFrames.LorentzFrameData.frame_transition_laws
#print axioms LorentzFrames.LorentzFrameData.frame_defect_eq_pm_one
#print axioms LorentzFrames.LorentzFrameData.frameObstruction
#print axioms LorentzFrames.LorentzFrameData.frameObstruction_choice_independent
#print axioms LorentzFrames.SpinFrameStructure
#print axioms LorentzFrames.LorentzFrameData.nonempty_spinFrameStructure_iff_exists_coherent
#print axioms LorentzFrames.LorentzFrameData.frameObstruction_eq_trivial_iff_spinStructure
#print axioms LorentzFrames.SpinFrameStructure.spinStructure_torsor
#print axioms LorentzFrames.finrank_carrier
#print axioms LorentzFrames.finrank_tangentSpace
#print axioms LorentzFrames.tangent_frame_cocycle
#print axioms LorentzFrames.tangent_frame_spin_lift_obstruction
#print axioms LorentzFrames.zdefect_cocycle₂
#print axioms LorentzFrames.zdefect_change_of_lift
#print axioms LorentzFrames.zdefect_isCoboundary_iff_spinStructure

end LorentzFrames
