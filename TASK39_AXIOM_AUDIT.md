# TASK 39 — principal `#print axioms` audit

Source of the audit: `RequestProject/Spine/Closure/AxiomAudit.lean`, run as part of
`lake build RequestProject`.  Every principal endpoint recorded in
`docs/machine/THEOREM_REGISTRY.jsonl` appears below.

Endpoints audited: **62**.  Observed axiom set, identical for every one of them:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no project-declared axiom, no `native_decide` axiom, no `Lean.ofReduceBool`.

| # | endpoint |
| --- | --- |
| 1 | `SpinCore.lorentz_quadratic_form` |
| 2 | `SpinCore.clifford_generator_square` |
| 3 | `SpinCore.paravector_norm` |
| 4 | `SpinCore.clifford_jordan` |
| 5 | `SpinCore.adjoin_spinToCl_eq_top` |
| 6 | `SpinCore.spin_double_cover_of_lorentz` |
| 7 | `SpinCore.spin_double_cover_bundled` |
| 8 | `SpinCore.spin_double_cover_topological_endpoint` |
| 9 | `SpinCore.spin_double_cover_local_section_endpoint` |
| 10 | `EmergentBase.base_not_determined_by_local_pieces` |
| 11 | `EmergentBase.BaseGluingData.isManifold_of_smoothGluing` |
| 12 | `EmergentBase.BaseGluingData.smoothEmergentManifoldCertificate` |
| 13 | `EmergentBase.BaseGluingData.tangentTransition_eq_derivative_baseTransition` |
| 14 | `SpinNative.tangent_spin_base_data_do_not_force_transition_identification` |
| 15 | `SpinNative.TangentSolderData.tangentMetric_wellDefined` |
| 16 | `SpinNative.weak_solder_not_regular` |
| 17 | `SpinNative.smooth_solder_iff_regular_bundle_equivalence` |
| 18 | `SpinNative.SmoothTangentSolderData.smooth_tangent_lorentz_metric` |
| 19 | `Task36.smooth_solder_implies_orientation_compatible` |
| 20 | `Task36.orientation_obstruction_nonzero_implies_no_solder` |
| 21 | `Task36.smooth_solder_implies_spin_obstruction_trivial` |
| 22 | `Task36.spin_obstruction_nonzero_implies_no_solder` |
| 23 | `Task36.classical_reconvergence` |
| 24 | `Task36.nonempty_regularBundleCertificate_iff` |
| 25 | `Task36.nonempty_timeOrientationReduction_of_solder` |
| 26 | `Task36.loop_timeOrientationReduction_isGlued` |
| 27 | `Task36.regular_solder_is_gauge_torsor` |
| 28 | `SpinNative.SmoothTangentSolderData.regular_solder_torsor` |
| 29 | `Task36.one_loop_has_kernel_sign_freedom` |
| 30 | `Task36.two_loop_spin_choice_family` |
| 31 | `Task36.orientation_reversing_gluing_no_solder` |
| 32 | `Task36.spin_does_not_imply_lorentz_moebius` |
| 33 | `Task36.spin_foam_labels_do_not_determine_solder` |
| 34 | `Task36.oneChart_positive_control` |
| 35 | `Task36.adversarial_global_topology_certificate` |
| 36 | `Task37.Deformation.transportState_add` |
| 37 | `Task37.Deformation.projectedTransportState_apply` |
| 38 | `Task37.Deformation.not_forall_regularClosureAdmissible` |
| 39 | `Task37.Deformation.selective_family_not_admissible_of_ne` |
| 40 | `Task37.Deformation.controlA_interface_certificate` |
| 41 | `Task37.Deformation.controlAAdmissible_zero` |
| 42 | `Task37.Deformation.controlAAdmissible_all` |
| 43 | `Task37.Deformation.regularRegion_loopTransportFamily` |
| 44 | `Task37.Deformation.controlAAdmissible_neg_iff` |
| 45 | `Task37.Deformation.spinCocycle_gaugeEquiv` |
| 46 | `Task37.Deformation.projectedCocycle_gaugeEquiv` |
| 47 | `Task37.Deformation.not_kernelGaugeEquiv_of_ne_zero` |
| 48 | `Task37.Deformation.loopParaSolder_A_comparison` |
| 49 | `Task37.Deformation.tangentMetric_loopParaSolder_eq` |
| 50 | `Task37.Deformation.native_transport_knob_smoketest_certificate` |
| 51 | `Task37.Deformation.smoketest_negative_records` |
| 52 | `Task37.Deformation.contDiffOn_loopProjectedGauge` |
| 53 | `Task37.Deformation.loopProjectedGauge_eq` |
| 54 | `Task37.Deformation.loopSolderTransport` |
| 55 | `Task37.Deformation.loopSolderEquiv` |
| 56 | `Task37.Deformation.tangentMetric_loopSolderTransport` |
| 57 | `Task37.Deformation.loopSolderSolutionSpace_correspondence` |
| 58 | `Closure.local_core_certificate` |
| 59 | `Closure.global_layer_certificate` |
| 60 | `Closure.fixed_cover_lift_freedom_certificate` |
| 61 | `Closure.smoketest_certificate` |
| 62 | `Closure.intermediate_milestone_certificate` |
