import RequestProject.Spine.Closure.IntermediateMilestone
import RequestProject.Spine.Solder.Independence
import RequestProject.Spine.Solder.WeakInsufficiency
import RequestProject.Spine.Solder.RegularGauge
import RequestProject.Spine.Emergent.NonDerivability
import RequestProject.Spine.Emergent.TangentTransition
import RequestProject.Spine.Task36.SpinFoamControl
import RequestProject.Spine.Task36.LoopTimeOrientation
import RequestProject.Spine.Task36.GaugeGroup
import RequestProject.Spine.Deformation.SmokeTestCertificate

/-!
# Task 39 / Part XI §36 : the principal axiom audit

This module runs `#print axioms` on **every** theorem that Task 39 records as a principal
endpoint in `docs/machine/THEOREM_REGISTRY.jsonl`, so that the machine-readable
`observed_axioms` field of that registry can be filled from a build artefact rather than from
memory.

The expected output for every line is

```text
    [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, no project axiom, no `native_decide` axiom and no
`Lean.ofReduceBool` anywhere in the list.  A regression shows up immediately as a changed
line in the build log.

The module proves nothing; it is an audit target only.
-/

/-! ## Local core -/

#print axioms SpinCore.lorentz_quadratic_form
#print axioms SpinCore.clifford_generator_square
#print axioms SpinCore.paravector_norm
#print axioms SpinCore.clifford_jordan
#print axioms SpinCore.adjoin_spinToCl_eq_top
#print axioms SpinCore.spin_double_cover_of_lorentz
#print axioms SpinCore.spin_double_cover_bundled
#print axioms SpinCore.spin_double_cover_topological_endpoint
#print axioms SpinCore.spin_double_cover_local_section_endpoint

/-! ## The intrinsic Lorentz-skew Lie-algebra layer (registered at Task 40; audit only) -/

#print axioms SpinCore.gB_bracket_mem
#print axioms SpinCore.gBLie_bracket
#print axioms SpinCore.bivectorEquivSkew_wedge
#print axioms SpinCore.finrank_gB

/-! ## Emergent base and smooth structure -/

#print axioms EmergentBase.base_not_determined_by_local_pieces
#print axioms EmergentBase.BaseGluingData.isManifold_of_smoothGluing
#print axioms EmergentBase.BaseGluingData.smoothEmergentManifoldCertificate
#print axioms EmergentBase.BaseGluingData.tangentTransition_eq_derivative_baseTransition

/-! ## Solder layer -/

#print axioms SpinNative.tangent_spin_base_data_do_not_force_transition_identification
#print axioms SpinNative.TangentSolderData.tangentMetric_wellDefined
#print axioms SpinNative.weak_solder_not_regular
#print axioms SpinNative.smooth_solder_iff_regular_bundle_equivalence
#print axioms SpinNative.SmoothTangentSolderData.smooth_tangent_lorentz_metric

/-! ## Task 36 : global reconvergence and adversarial controls -/

#print axioms Task36.smooth_solder_implies_orientation_compatible
#print axioms Task36.orientation_obstruction_nonzero_implies_no_solder
#print axioms Task36.smooth_solder_implies_spin_obstruction_trivial
#print axioms Task36.spin_obstruction_nonzero_implies_no_solder
#print axioms Task36.classical_reconvergence
#print axioms Task36.nonempty_regularBundleCertificate_iff
#print axioms Task36.nonempty_timeOrientationReduction_of_solder
#print axioms Task36.loop_timeOrientationReduction_isGlued
#print axioms Task36.regular_solder_is_gauge_torsor
#print axioms SpinNative.SmoothTangentSolderData.regular_solder_torsor
#print axioms Task36.one_loop_has_kernel_sign_freedom
#print axioms Task36.two_loop_spin_choice_family
#print axioms Task36.orientation_reversing_gluing_no_solder
#print axioms Task36.spin_does_not_imply_lorentz_moebius
#print axioms Task36.spin_foam_labels_do_not_determine_solder
#print axioms Task36.oneChart_positive_control
#print axioms Task36.adversarial_global_topology_certificate

/-! ## Task 37 : the deformation interface -/

#print axioms Task37.Deformation.transportState_add
#print axioms Task37.Deformation.projectedTransportState_apply
#print axioms Task37.Deformation.not_forall_regularClosureAdmissible
#print axioms Task37.Deformation.selective_family_not_admissible_of_ne
#print axioms Task37.Deformation.controlA_interface_certificate

/-! ## Task 38 : the fixed-base smoke test -/

#print axioms Task37.Deformation.controlAAdmissible_zero
#print axioms Task37.Deformation.controlAAdmissible_all
#print axioms Task37.Deformation.regularRegion_loopTransportFamily
#print axioms Task37.Deformation.controlAAdmissible_neg_iff
#print axioms Task37.Deformation.spinCocycle_gaugeEquiv
#print axioms Task37.Deformation.projectedCocycle_gaugeEquiv
#print axioms Task37.Deformation.not_kernelGaugeEquiv_of_ne_zero
#print axioms Task37.Deformation.loopParaSolder_A_comparison
#print axioms Task37.Deformation.tangentMetric_loopParaSolder_eq
#print axioms Task37.Deformation.native_transport_knob_smoketest_certificate
#print axioms Task37.Deformation.smoketest_negative_records

/-! ## Task 39 : the two strengthenings and the milestone certificate -/

#print axioms Task37.Deformation.contDiffOn_loopProjectedGauge
#print axioms Task37.Deformation.loopProjectedGauge_eq
#print axioms Task37.Deformation.loopSolderTransport
#print axioms Task37.Deformation.loopSolderEquiv
#print axioms Task37.Deformation.loopSolderTransport_involutive
#print axioms Task37.Deformation.tangentMetric_loopSolderTransport
#print axioms Task37.Deformation.loopSolderSolutionSpace_correspondence
#print axioms Closure.local_core_certificate
#print axioms Closure.global_layer_certificate
#print axioms Closure.fixed_cover_lift_freedom_certificate
#print axioms Closure.smoketest_certificate
#print axioms Closure.intermediate_milestone_certificate
