# Provenance ledger of modules removed from the active merged tree

This ledger records **every** Lean module that was part of the merged tree before the
spine-extraction refactor and is no longer active Lean source afterwards.  Nothing recorded
here was disproved or is believed false: these modules built green in the archived state
and their results stand.  They are removed from the *active* dependency DAG because the
merged project's purpose is now the single reconstruction chain

```
derived Lorentz quadratic structure -> Clifford algebra -> Spin group and double cover
  -> Lorentzian frame geometry -> orientation and time orientation -> global Spin lift and
  its obstruction -> spinor bundle -> lifted spin connection
```

and only the modules that this chain — or its explicitly retained comparison endpoints and
negative controls — actually needs are kept as active source.

## Recoverability

Both upstream developments remain independently documented and complete in their own
repositories (see `COMBINED_PROJECT_PROVENANCE.md`):

| Upstream | Project identifier | Branch |
| --- | --- | --- |
| Experiment 1 — *Intrinsic Branching from a Derived Lorentz Structure* | `Split-Complex-Lorentzian_Kinematics` | `Intrinsic-Branching-from-a-Derived-Lorentz-Structure` |
| Experiment 2 — *Split Complex Lorentzian Dynamics* | `Split-Complex_Lorentz_Dynamics` | `main` |

Inside *this* repository every removed module is recoverable verbatim from the git history.
The merged tree before the refactor is the initial commit `5790111`; any file below can be
restored with

```
git show 5790111:<path>
```

## Classification vocabulary

| Classification | Meaning |
| --- | --- |
| `SUPERSEDED` | the proved content is carried forward, verbatim or with a rename, into a new `RequestProject.Spine.*` module; the old module is redundant |
| `COMPARISON_ONLY` | the module exists to compare the intrinsic development with a historical model; the retained comparison endpoints are the `RequestProject.Comparison.*` modules |
| `PREMATURE` | mathematically sound, but it builds structure *above* the current frontier (fields, connections, curvature, quantization) before the objects it should live on exist |
| `NEGATIVE_RESULT` | a probe or falsification test whose recorded outcome is that no new structure or obstruction was found |
| `OUT_OF_SCOPE` | a self-contained branch that the spin-reconstruction chain does not use |

## Summary

| Classification | modules |
| --- | --- |
| `OUT_OF_SCOPE` | 118 |
| `PREMATURE` | 30 |
| `SUPERSEDED` | 23 |
| `COMPARISON_ONLY` | 17 |
| `NEGATIVE_RESULT` | 7 |
| **total removed** | **195** |

| Upstream | modules removed |
| --- | --- |
| Experiment 1 | 125 |
| Experiment 2 | 70 |

## Ledger

The *module title* column reproduces the title line of the removed module's own docstring;
the *principal declarations* column names its own strongest statements as they stood when
it was removed.

| Module (original path) | Upstream | Classification | Module title | Principal declarations | Why excluded from the active DAG |
| --- | --- | --- | --- | --- | --- |
| `RequestProject.Experiment1.Ledger` | E1 | OUT_OF_SCOPE | Sections 20 and 23 : the dependency and obstruction ledger, in formal form | `hMat_eq_diag_add_offDiag`, `det_diag_add_offDiag`, `det_offDiag_zero` | 1+1 split-complex kinematics / bookkeeping, not on the spin-reconstruction path |
| `RequestProject.Experiment1.Main` | E1 | OUT_OF_SCOPE | (no module title) | — | 1+1 split-complex kinematics / bookkeeping, not on the spin-reconstruction path |
| `RequestProject.Experiment1.SplitComplexLorentz` | E1 | OUT_OF_SCOPE | Split-complex (paracomplex) algebra and `1+1` Lorentz kinematics | `Split`, `eps`, `eps_sq` | 1+1 split-complex kinematics / bookkeeping, not on the spin-reconstruction path |
| `RequestProject.Experiment1.Task10Affine` | E1 | OUT_OF_SCOPE | Task 10, Branch 1 : the intrinsic affine / Poincaré structure | `Transl`, `linMulAut`, `glorAct` | not required by the spin chain |
| `RequestProject.Experiment1.Task10Audit` | E1 | SUPERSEDED | Task 10, Part M : mechanical no-target-leakage audit | `isProjectConst`, `forbidden`, `auditDecl` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task10Base` | E1 | SUPERSEDED | Task 10, Part A : freezing the Task-9 endpoint | `NS_def`, `sip_smul_right`, `sip_add_right` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task10Bivector` | E1 | SUPERSEDED | Task 10, Branch 4 (part 1) : the exterior square and the intrinsic skew algebra | `alone`, `finrank_spin`, `finrank_extPow2` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task10Causal` | E1 | OUT_OF_SCOPE | Task 10, Branch 2 : the intrinsic order relation of the square cone | `CLe`, `CLt`, `CLe_refl` | not required by the spin chain |
| `RequestProject.Experiment1.Task10Compare` | E1 | COMPARISON_ONLY | Task 10, Part A4 : comparison of the intrinsic `G_L` with the Task-8 group | `spinHermConj`, `spinHermConj_apply`, `NS_symm_apply` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task10Final` | E1 | COMPARISON_ONLY | Task 10, Part J : the packaged branch closure | `J1_affine_branch`, `J2_causal_branch`, `J3_shell_branch` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task10Hodge` | E1 | SUPERSEDED | Task 10, optional Branch F : the Hodge operator on `Λ²𝒮` | `volS`, `volS_frame`, `volS_10` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task10Hyperbolic` | E1 | SUPERSEDED | Task 10, Branch 3 (part 1) : the unit future shell and its intrinsic boosts | `of`, `Shell`, `shell_subset_intFuture` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task10Lie` | E1 | SUPERSEDED | Task 10, Branch 4 (part 2) : `Λ²𝒮 ≅ 𝔤_B` | `sip_sub_left`, `sip_evec_right`, `vec_ext_evec` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task10LieCompare` | E1 | COMPARISON_ONLY | Task 10, Branch 4 (part 3) : STANDARD IDENTIFICATION `𝔤_B ≅ 𝔰𝔬(1,3)` | `so13Mat`, `mem_so13Mat`, `BS_eq_J4` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task10Shell` | E1 | SUPERSEDED | Task 10, Branch 3 (part 2) : homogeneity of the unit future shell, its tangent form, | `spatialRefl`, `spatialRefl_apply`, `sip_spatialRefl` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task11BivectorLie` | E1 | OUT_OF_SCOPE | Task 11, Phase I, obligation B4 : the intrinsic Lie bracket on `Λ²𝒮` | `Kend_commutator`, `Phi0_mem_gB`, `Phi0_injective` | auxiliary intrinsic branch (causal, Hodge, topology, smoothness) not required by the spin chain |
| `RequestProject.Experiment1.Task11CausalIntrinsic` | E1 | OUT_OF_SCOPE | Task 11, Phase I, obligation B1 : chronological relation versus strict causal order | `CStrict`, `calls`, `Chron` | auxiliary intrinsic branch (causal, Hodge, topology, smoothness) not required by the spin chain |
| `RequestProject.Experiment1.Task11CliffordHodgeBridge` | E1 | SUPERSEDED | Task 11, Phase IV, obligation E3 : the pseudoscalar acts as the Hodge star | `spinToCl_one`, `spinToClBar_one`, `spinToCl_bvec` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task11CliffordIso` | E1 | OUT_OF_SCOPE | Task 11, Phase IV, obligation E1 (completion) : `Cl⁰(q_N) ≅ Cl₃(ℝ)` | `spatL`, `spatL_apply`, `qN_spatL` | auxiliary intrinsic branch (causal, Hodge, topology, smoothness) not required by the spin chain |
| `RequestProject.Experiment1.Task11Compare` | E1 | COMPARISON_ONLY | Task 11 : the comparison layer (downstream only) | `spatialReflI_eq_spatialRefl`, `spatialRefl_det_crosscheck`, `det_sq_crosscheck` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task11Coords` | E1 | SUPERSEDED | Task 11, Phase I : intrinsic real coordinates, matrices and determinants | `coordFun`, `uncoordFun`, `coordFun_zero` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task11Final` | E1 | COMPARISON_ONLY | Task 11 : packaging, closure-status vocabulary, and axiom audit | `task10ClosureStatus`, `task10ClosureStatus_ne_exhaustive`, `task11_closed_obligations` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task11HodgeDim` | E1 | OUT_OF_SCOPE | Task 11, Phase III, obligation D3 (refinement) : the dimensions of the Hodge eigenspaces | `mem_LamPlus_iff`, `mem_LamMinus_iff`, `finrank_LamC` | auxiliary intrinsic branch (causal, Hodge, topology, smoothness) not required by the spin chain |
| `RequestProject.Experiment1.Task11HodgeEquivariance` | E1 | OUT_OF_SCOPE | Task 11, Phase III, obligations D1 and D2 : orientation dependence and `G_L`-equivariance | `ext_bivector`, `wedgeMap`, `wedgeMap_wedge` | auxiliary intrinsic branch (causal, Hodge, topology, smoothness) not required by the spin chain |
| `RequestProject.Experiment1.Task11HodgeSplit` | E1 | OUT_OF_SCOPE | Task 11, Phase III, obligation D3 : the complexified eigenspace split of `⋆` | `isCompl_eigenspaces_of_sq_neg_one`, `LamC`, `hodgeC` | auxiliary intrinsic branch (causal, Hodge, topology, smoothness) not required by the spin chain |
| `RequestProject.Experiment1.Task11HyperbolicMetric` | E1 | OUT_OF_SCOPE | Task 11, Phase II, obligations C4 and C5 : the induced positive metric and the | `TangentAt`, `mem_tangentAt`, `tangentAt_eq_ker` | auxiliary intrinsic branch (causal, Hodge, topology, smoothness) not required by the spin chain |
| `RequestProject.Experiment1.Task11IntrinsicDependencyAudit` | E1 | SUPERSEDED | Task 11, Phase I, obligation B3 : the strengthened dependency audit | `isProjectConst`, `forbiddenConsts`, `forbiddenConstsScalarExtension` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task11LorentzClifford` | E1 | SUPERSEDED | Task 11, Phase IV, obligations E1 and E2 : the Lorentz Clifford branch and the bivector map | `clifford_square_convention`, `bilN`, `bilN_apply` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task11OrientationBridge` | E1 | OUT_OF_SCOPE | Task 11, Phase IV, obligation E4 : are the two `ℤ₂` ambiguities the same discrete datum? | `reflV`, `reflV_apply`, `reflVIsom` | auxiliary intrinsic branch (causal, Hodge, topology, smoothness) not required by the spin chain |
| `RequestProject.Experiment1.Task11Paravector` | E1 | SUPERSEDED | Task 11, Phase V : paravector preservation and the induced action on the carrier | `spinToCl_injective`, `cle_01`, `cle_12` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task11SL2` | E1 | SUPERSEDED | Task 11, Phase V (V5) : the spin group is isomorphic to `SL(2,ℂ)` | `cconj_add`, `cconj_smul`, `cconj_cle` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task11ShellIntrinsic` | E1 | SUPERSEDED | Task 11, Phase I, obligation B2 : the shell branch without the Hermitian comparison leak | `spatialReflI`, `spatialReflI_apply`, `sip_spatialReflI` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task11SmoothShell` | E1 | OUT_OF_SCOPE | Task 11, Phase II, obligation C3 : the unit future shell as a smooth manifold | `BSlm`, `BSlm_apply`, `BSclm` | auxiliary intrinsic branch (causal, Hodge, topology, smoothness) not required by the spin chain |
| `RequestProject.Experiment1.Task11Spin` | E1 | SUPERSEDED | Task 11, Phase V (partial) : the spin branch inside the Task-9 real Clifford algebra | `cconj`, `cconj_one`, `cconj_neg` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task11SpinDet` | E1 | SUPERSEDED | Task 11, Phase V (completion) : the induced maps have determinant `1` | `spinToCl_zero`, `spinToCl_neg`, `spinToCl_sub` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task11SpinSurj` | E1 | SUPERSEDED | Task 11, Phase V (completion) : the induced action is onto the intrinsic Lorentz group | `hyperRefl`, `hyperRefl_apply`, `hyperReflProd` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task11Topology` | E1 | OUT_OF_SCOPE | Task 11, Phase II, obligations C1 and C2 : topology and smooth structure are not new input | `linear_map_continuous`, `coordHomeomorph`, `coordHomeomorph_apply` | auxiliary intrinsic branch (causal, Hodge, topology, smoothness) not required by the spin chain |
| `RequestProject.Experiment1.Task15Action` | E1 | PREMATURE | Task 15, Stage IV : the quadratic density and its nonuniqueness | `pairB`, `pairB_wedge`, `toDual_add` | field-theory branch (forms, Maxwell, gauge phase, quantization, mass selection, positive frequency) built on the carrier before any manifold exists |
| `RequestProject.Experiment1.Task15Carrier` | E1 | PREMATURE | Task 15, Stage 0 : audit of the three candidate primitive inputs | `finrank_spatial`, `finrank_carrier_split`, `carrier_isManifold` | field-theory branch (forms, Maxwell, gauge phase, quantization, mass selection, positive frequency) built on the carrier before any manifold exists |
| `RequestProject.Experiment1.Task15Final` | E1 | PREMATURE | Task 15 : packaging, dependency vocabulary, and axiom audit | `not_formalized_ne_new_input`, `dimensionStatus`, `manifoldStatus` | field-theory branch (forms, Maxwell, gauge phase, quantization, mass selection, positive frequency) built on the carrier before any manifold exists |
| `RequestProject.Experiment1.Task15Forms` | E1 | PREMATURE | Task 15, Stage I : canonical local differential structure on the affine carrier | `Form`, `IsSmoothForm`, `minSmoothness_le_infty` | field-theory branch (forms, Maxwell, gauge phase, quantization, mass selection, positive frequency) built on the carrier before any manifold exists |
| `RequestProject.Experiment1.Task15Hodge2Form` | E1 | PREMATURE | Task 15, Stage II : transporting the algebraic Hodge operator to differential 2-forms | `BflatL`, `Bflat`, `Bflat_apply` | field-theory branch (forms, Maxwell, gauge phase, quantization, mass selection, positive frequency) built on the carrier before any manifold exists |
| `RequestProject.Experiment1.Task15Maxwell` | E1 | PREMATURE | Task 15, Stage III : Maxwell-type structural audit | `scalForm`, `scalForm_smooth`, `extDeriv_scalForm` | field-theory branch (forms, Maxwell, gauge phase, quantization, mass selection, positive frequency) built on the carrier before any manifold exists |
| `RequestProject.Experiment1.Task15Null` | E1 | PREMATURE | Task 15, Stage IX : the null / transverse branch | `NullFuture`, `nullFuture_nonempty`, `nullFuture_smul` | field-theory branch (forms, Maxwell, gauge phase, quantization, mass selection, positive frequency) built on the carrier before any manifold exists |
| `RequestProject.Experiment1.Task15Phase` | E1 | PREMATURE | Task 15, Stage V : global and local phase structure | `phaseRot`, `phaseRot_apply`, `phaseRot_zero` | field-theory branch (forms, Maxwell, gauge phase, quantization, mass selection, positive frequency) built on the carrier before any manifold exists |
| `RequestProject.Experiment1.Task15Quantization` | E1 | PREMATURE | Task 15, Stages VIII and X : coupling accessibility and the quantization boundary | `coupling_absorb`, `conj_sq_neg_one`, `two_complex_structures_on_plane` | field-theory branch (forms, Maxwell, gauge phase, quantization, mass selection, positive frequency) built on the carrier before any manifold exists |
| `RequestProject.Experiment1.Task15Spinor` | E1 | SUPERSEDED | Task 15, Stages VI–VII : the spinorial branch and the first-order operator | `CliffordAction`, `sig`, `sigBar` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task16Final` | E1 | PREMATURE | Task 16 : the hardened frontier, packaged | `depClass_all_distinct`, `massVerdict`, `massClass` | field-theory branch (forms, Maxwell, gauge phase, quantization, mass selection, positive frequency) built on the carrier before any manifold exists |
| `RequestProject.Experiment1.Task16Mass` | E1 | PREMATURE | Task 16, Part A : hardening the mass classification | `IsJordanAut`, `jordanAut_fixes_unit`, `sJ_dilation` | field-theory branch (forms, Maxwell, gauge phase, quantization, mass selection, positive frequency) built on the carrier before any manifold exists |
| `RequestProject.Experiment1.Task16Phase` | E1 | PREMATURE | Task 16, Part B : what local phase covariance actually forces | `phaseOp`, `phaseOp_apply`, `phaseOp_zero` | field-theory branch (forms, Maxwell, gauge phase, quantization, mass selection, positive frequency) built on the carrier before any manifold exists |
| `RequestProject.Experiment1.Task16PositiveFrequency` | E1 | PREMATURE | Task 16, Part C : the prerequisites of a positive-frequency decomposition | `exists`, `sq_neg_one_underdetermined_on_bivectors`, `diracOp_add` | field-theory branch (forms, Maxwell, gauge phase, quantization, mass selection, positive frequency) built on the carrier before any manifold exists |
| `RequestProject.Experiment1.Task18Connection` | E1 | PREMATURE | Task 18, Part A/B/D : from the Task-16 compensator to connection data | `DirLinearAt`, `DirLinear`, `covDeriv_dirLinearAt` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task18Curvature` | E1 | PREMATURE | Task 18, Part I : the abelian curvature `f = da` | `zeroForm`, `zeroForm_apply`, `zeroForm_smooth` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task18FieldBridge` | E1 | PREMATURE | Task 18, Parts J/K/L : comparison with the Task-15 sectors | `IsExactF`, `IsPhaseConnCurvature`, `phaseCurvature_isExact` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task18Final` | E1 | PREMATURE | Task 18 : packaged verdicts, endpoint theorem and axiom audit | `connVerdict`, `connVerdict_not_local_phase_forces`, `jCompatVerdict` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task18PhaseConnection` | E1 | PREMATURE | Task 18, Parts E/F/G/H : the transformation law, `J`-compatibility, and the phase branch | `phaseOp_neg_phaseOp'`, `phaseOp_comp_neg`, `phaseOp_neg_comp` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task19Centralizer` | E1 | PREMATURE | Task 19, Part 2 : the abstract centralizer / skew-adjoint algebra | `Cent`, `mem_cent_iff`, `PhaseAlg` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task19Final` | E1 | PREMATURE | Task 19 : packaged verdicts, decision tree and axiom audit | `centVerdict`, `intersectionVerdictCanonical`, `intersectionVerdictEuclidean` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task19MetricConnection` | E1 | PREMATURE | Task 19, Part 3 : metric compatibility of a connection, and what it says about `Γ` | `fderiv_pairing`, `MetricCompat`, `metricCompat_iff_skew` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task19PairingAudit` | E1 | PREMATURE | Task 19, Part 1 : the audit of the module carrying the Task-18 phase connection | `TwoForm`, `frameMap`, `frameMap_apply` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task19Reduction` | E1 | PREMATURE | Task 19, Part 4 : the falsification test on the actual carrier | `witnessCoord`, `witnessCoord_apply`, `witnessOp` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task20Falsification` | E1 | PREMATURE | Task 20, §14 : falsification tests | `badPhi`, `hasDerivAt_badPhi`, `badPhi_zero` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task20Final` | E1 | PREMATURE | Task 20 : final packaging — the geodesics of the unit future shell | `task20_shell_geodesics` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task20PlaneUniqueness` | E1 | PREMATURE | Task 20, §§7 and 11 : derivation of the `cosh/sinh` formula inside the two-plane | `deriv_eq_zero_of_const`, `hyperbolic_ode_unique`, `plane_indep` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task20ShellConnection` | E1 | PREMATURE | Task 20, §§5–6 : the induced covariant derivative of the unit future shell | `BSlm`, `BSclm`, `BSclm` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task20ShellCurve` | E1 | PREMATURE | Task 20, §§7–9 : the explicit intrinsic curve in the two-plane `span{x,v}` | `BS_plane`, `NS_plane`, `shellSpeed` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task20ShellGeodesic` | E1 | PREMATURE | Task 20, §§10–13 : the geodesic theorem for the unit future shell | `deriv_shellGeo`, `deriv_shellGeoVel`, `shell_explicit_geodesic` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task20ShellProjection` | E1 | PREMATURE | Task 20, §4 : the canonical tangential projection of the unit future shell | `BS_self_shell`, `Pr`, `Pr_apply` | flat connection / curvature / geodesic branch on the carrier, prior to any tangent or frame bundle |
| `RequestProject.Experiment1.Task21Final` | E1 | OUT_OF_SCOPE | Task 21 : final packaging — the intrinsic path distance of the unit future shell | `shellPathLengths`, `shellPathDist`, `shellSep_mem_shellPathLengths` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task21ShellDistance` | E1 | OUT_OF_SCOPE | Task 21, §§4–5 : the candidate separation `δ(x,y) = arcosh B(x,y)` and its metric axioms | `shellSep`, `shellSep_nonneg`, `shellSep_eq_zero_iff` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task21ShellLength` | E1 | OUT_OF_SCOPE | Task 21, §§6–8 : the canonical joining geodesic, curve length, and the upper bound | `joinDir`, `BS_gt_one`, `sqrt_BS_sq_sub_one_pos` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task21ShellMinimizing` | E1 | OUT_OF_SCOPE | Task 21, §§9–10 : the lower bound for arbitrary admissible shell curves | `continuous_BS_left`, `continuous_BS_diag`, `continuous_gNorm` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task21ShellSeparation` | E1 | OUT_OF_SCOPE | Task 21, §3 : intrinsic separation of two points of the unit future shell | `shell_fst_ge_one`, `BS_ge_one`, `BS_pos` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task22Final` | E1 | OUT_OF_SCOPE | Task 22, §§14–19 : compatibility with the Task-11 smooth structure, the C¹ path metric, | `shellMetricChart`, `shellMetricChart_apply`, `shell_isManifold_unchanged` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task22ShellBasepointTopology` | E1 | OUT_OF_SCOPE | Task 22, §§7–8 : the basepoint formulas at `e = 1_𝒮` | `BS_sOne_left`, `sip_self_eq`, `fst_ge_one` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task22ShellMetricAction` | E1 | OUT_OF_SCOPE | Task 22, §§3–5 : the two Lean shell carriers, and the `G_L` action on both of them | `ShellAmb`, `ShellMet`, `toAmbientShell` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task22ShellTopologyBridge` | E1 | OUT_OF_SCOPE | Task 22, §§9–13 : the two topologies of the unit future shell coincide | `continuous_BS_right`, `continuous_shellSep_ambient`, `continuous_toMetricShell` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task23Final` | E1 | OUT_OF_SCOPE | Task 23, §§13–16 : falsification checks, statuses, packaged endpoint and axiom audit | `metricCompletenessStatus`, `geodesicCompletenessStatus`, `hopfRinowStatus` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task23ShellBoundedness` | E1 | OUT_OF_SCOPE | Task 23, §§4–6 : from a `δ`-bound to an ambient norm bound | `fst_le_cosh_of_shellSep_le`, `sip_le_sinh_sq_of_shellSep_le`, `euclidSq_shell` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task23ShellCompleteness` | E1 | OUT_OF_SCOPE | Task 23, §§10–11 : every `δ`-Cauchy sequence converges, and the `CompleteSpace` packaging | `shell_cauchySeq_converges`, `shell_cauchySeq_shellSep_tendsto_zero`, `shell_metric_complete` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task23ShellLimit` | E1 | OUT_OF_SCOPE | Task 23, §§7–9 : the ambient subsequential limit and its return to the `δ`-metric | `continuous_NS`, `exists_ambient_subseq_of_bdd`, `mem_shell_of_tendsto` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task24AlexandrovBasis` | E1 | OUT_OF_SCOPE | Task 24, Branch I (part 2): arbitrarily small intrinsic diamonds | `Equad`, `Equad_nonneg`, `sq_snd_le_sip` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task24AlexandrovOpen` | E1 | OUT_OF_SCOPE | Task 24, Branch I (part 1): openness of the intrinsic chronological sets | `chronFuture`, `chronPast`, `mem_chronFuture_iff` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task24Final` | E1 | OUT_OF_SCOPE | Task 24, Branch I (part 3): exact topology equality, status packaging, audits | `alexandrovTopology_eq_canonical`, `canonical_eq_alexandrovTopology`, `isOpen_alexandrov_iff` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task25AffineCompatibility` | E1 | OUT_OF_SCOPE | Task 25 — compatibility layer (NOT part of the intrinsic closure) | `gpCompat`, `pact_compat`, `gp25_pact_compat` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task25AffineIntrinsicBase` | E1 | OUT_OF_SCOPE | Task 25, Part 0 : a comparison-free repackaging of the intrinsic affine structure | `are`, `carrier_chartedSpace`, `carrier_isManifold` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task25Final` | E1 | OUT_OF_SCOPE | Task 25 — Affine/Poincaré Branch I : intrinsic smooth affine-group closure | `gp25MulEquivGP`, `pact_gp25MulEquivGP`, `affine_poincare_smooth_closure` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task25GLorCayley` | E1 | OUT_OF_SCOPE | Task 25, Part 2 : the intrinsic Cayley parametrization of `G_L` | `adjU`, `adjU_val`, `adj_neg` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task25GLorSmooth` | E1 | OUT_OF_SCOPE | Task 25, Part 3 : the intrinsic smooth (Lie group) structure on `G_L` | `glv`, `contDiffAt_cayE`, `contDiffAt_icayE` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task25GLorTopology` | E1 | OUT_OF_SCOPE | Task 25, Part 1 : the continuous-linear realization of `G_L` and its topology | `EndS`, `sE`, `BS_apply` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task25GPSmooth` | E1 | OUT_OF_SCOPE | Task 25, Part 4 : the intrinsic smooth affine (Poincaré) group | `ISpin`, `contMDiff_glEval`, `GP25` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task26Final` | E1 | OUT_OF_SCOPE | Task 26 — Final packaging, axiom check and dependency audit | — | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task26GLorLieAlgebra` | E1 | OUT_OF_SCOPE | Task 26 — Affine/Poincaré Branch II : intrinsic Lie-algebra identification | `GA`, `BS_neg_right`, `mem_gB_of_mem_glAlg` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task27Final` | E1 | OUT_OF_SCOPE | Task 27 — Final packaging, orientation remark, axiom check and dependency audit | `task27_hodge_sector_lie_split`, `task27_hodge_lie_centroid`, `orientation_reversal_swaps_sectors` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task27HodgeLieSectors` | E1 | OUT_OF_SCOPE | Task 27 : Hodge-sector Lie-bracket closure | `Phi0_zmap_apply_explicit`, `brCoord`, `bracketL_zmap` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task28CausalAffine` | E1 | OUT_OF_SCOPE | Task 28 — probe 1: continuity of the affine action from the causal order alone | `pact_left_inv`, `pact_right_inv`, `pact_bijective` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task28Final` | E1 | OUT_OF_SCOPE | Task 28 — packaging and audit of the three formal probes | `task28_affine_causal_continuity`, `task28_GL_acts_on_hodge_sectors` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task28HodgeGL` | E1 | OUT_OF_SCOPE | Task 28 — probe 2: the group branch acting on the Hodge sectors | `Kend_map`, `Phi0_wedgeMap_conj`, `wedgeMap_bracketL` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task28LieHodge` | E1 | OUT_OF_SCOPE | Task 28 — probe 3: a canonical complex structure on `Lie(G_L)` | `lieGLEquivBivector`, `lieGLLin`, `lieGLLin_map_lie` | shell metric geometry, completeness, Alexandrov topology, affine and Lie-theoretic branches of the carrier; not required by the spin chain |
| `RequestProject.Experiment1.Task29ComplexStructureProbe` | E1 | NEGATIVE_RESULT | Task 29 — probe 5: how large is the `J² = −1` ambiguity really?  (issue E, entry O11) | `altCoord`, `altCoord_0`, `altCoord_1` | structure probe that found no new intrinsic structure (complex structure, Nijenhuis, scale, representation, convention probes) |
| `RequestProject.Experiment1.Task29Final` | E1 | NEGATIVE_RESULT | Task 29 — packaging and axiom audit of the consistency-hardening probes | `task29_audit_endpoints` | structure probe that found no new intrinsic structure (complex structure, Nijenhuis, scale, representation, convention probes) |
| `RequestProject.Experiment1.Task29NijenhuisProbe` | E1 | NEGATIVE_RESULT | Task 29 — probe 3: the algebraic Nijenhuis condition, and normalization independence | `nijenhuis`, `nijenhuis_eq_zero_of_centroid`, `hodgeLie_nijenhuis_zero` | structure probe that found no new intrinsic structure (complex structure, Nijenhuis, scale, representation, convention probes) |
| `RequestProject.Experiment1.Task29RepresentationProbe` | E1 | NEGATIVE_RESULT | Task 29 — probe 4: packaging the sector action as a genuine representation (issue H) | `lamCMap_comp`, `lamCMap_id`, `sectorMap` | structure probe that found no new intrinsic structure (complex structure, Nijenhuis, scale, representation, convention probes) |
| `RequestProject.Experiment1.Task29ScaleProbe` | E1 | NEGATIVE_RESULT | Task 29 — probe 1: what the chronological order does *not* determine (issues A and B) | `NS_smul`, `BS_dil`, `dil_CLt_iff` | structure probe that found no new intrinsic structure (complex structure, Nijenhuis, scale, representation, convention probes) |
| `RequestProject.Experiment1.Task29ShellFormProbe` | E1 | NEGATIVE_RESULT | Task 29 — probe 2: does the shell distance determine `B_𝒮`?  (issue C) | `p0`, `p1`, `p2` | structure probe that found no new intrinsic structure (complex structure, Nijenhuis, scale, representation, convention probes) |
| `RequestProject.Experiment1.Task30ConventionProbe` | E1 | NEGATIVE_RESULT | Task 30 — convention probes for the comparative construction audit | `iotaStd`, `iotaStd_apply`, `iotaStd_one_bvec` | structure probe that found no new intrinsic structure (complex structure, Nijenhuis, scale, representation, convention probes) |
| `RequestProject.Experiment1.Task6Actions` | E1 | COMPARISON_ONLY | Task 6, Sections 10–14 : which two-sided algebraic actions can act on the carrier | `M2`, `left_mul_not_hermitian`, `A21` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task6Complex` | E1 | COMPARISON_ONLY | Task 6, Sections 29–30 : the role of the complex scalars, and the centre | `symMat`, `symMat_isSymm`, `Sym2` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task6Final` | E1 | COMPARISON_ONLY | Task 6, Sections 32–37 : the integrated dependency chain | `chainI_carrier_canonical`, `chainI_GL_is_units`, `chainI_cone_canonical` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task6MatrixUnits` | E1 | COMPARISON_ONLY | Task 6, Sections 19–28 and 31 : abstract matrix-unit reconstruction of `M₂(ℂ)` | `Data`, `eq_zero_of_smul_eq_zero`, `f` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task7ComplexStructure` | E1 | COMPARISON_ONLY | Task 7, Part D : can the complex scalars emerge from a real carrier? | `cxHom`, `cxHom_apply`, `cxHom_mul` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task7Counterexamples` | E1 | OUT_OF_SCOPE | Task 7, Part C5 : counterexamples delimiting the sector hypotheses | `Deg`, `mul_apply`, `one_apply'` | not required by the spin chain |
| `RequestProject.Experiment1.Task7Final` | E1 | COMPARISON_ONLY | Task 7 : the integrated non-circularity ledger | `reconstruction_chain`, `negative_ledger`, `reformulation_ledger` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task7Sectors` | E1 | COMPARISON_ONLY | Task 7, Part C : how much of the matrix-unit table is *derivable*? | `q_idem_of_complementary`, `star_q_of_complementary`, `orthogonal_of_complementary` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task7Star` | E1 | COMPARISON_ONLY | Task 7, Part E : can the `*`-structure be reconstructed from weaker data? | `RealForm`, `pair`, `pair_spec` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task8Audit` | E1 | SUPERSEDED | Task 8, Part J : mechanical no-target-leakage audit | `isProjectConst`, `forbidden`, `auditDecl` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task8Final` | E1 | COMPARISON_ONLY | Task 8, Parts F, G1, J and K : assembly, audit and ledger | `intrinsic_chain`, `intrinsic_structure`, `standard_comparison_layer` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task8Positivity` | E1 | OUT_OF_SCOPE | Task 8, Parts G2–G3, H and I | `StarDefinite`, `alpha_ne_zero_of_star_definite`, `alpha_pos_of_star_definite` | not required by the spin chain |
| `RequestProject.Experiment1.Task9Audit` | E1 | SUPERSEDED | Task 9, Part M : mechanical no-target-leakage audit for the *purely real* layer | `isProjectConst`, `forbidden`, `auditDecl` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task9Clifford` | E1 | SUPERSEDED | Task 9, Part E : the real Clifford envelope of the spin factor | `bil3`, `bil3_apply`, `q3` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task9Final` | E1 | COMPARISON_ONLY | Task 9 : final packaging and axiom audit | `complexToCenter_I`, `central_sq_neg_one_eq_pm_omega`, `orientation_is_a_C2_choice` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task9Pauli` | E1 | SUPERSEDED | Task 9, Parts F–H : the Pauli representation of the real Clifford envelope | `pauliMap`, `pauliMap_apply`, `hMat_scalar` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task9SpinFactor` | E1 | SUPERSEDED | Task 9, Part C : the purely real spin factor `𝒮 = ℝ ⊕ ℝ³` | `Spin`, `sip`, `sip_comm` | content extracted into the new `RequestProject.Spine.E1` core (statements unchanged; carrier renamed to `SpinCore.LorentzCarrier`) |
| `RequestProject.Experiment1.Task9Wide` | E1 | COMPARISON_ONLY | Task 9, Part B : orientation is a discrete component selection | `det_sq_of_wide`, `det_eq_one_or_neg_one_of_wide`, `detSign` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment1.Task9WideSplit` | E1 | COMPARISON_ONLY | Task 9, Part B (completion) : the wide group splits as a semidirect product | `parityY_mul_self`, `reflY_mul_self`, `reflYW` | comparison with the Hermitian carrier or a task-endpoint re-export; the retained comparison is `RequestProject.Comparison.E1Hermitian` |
| `RequestProject.Experiment2.Main` | E2 | OUT_OF_SCOPE | (no module title) | — | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask01.Boost` | E2 | OUT_OF_SCOPE | Task 01, Layer 3: longitudinal boosts and the invariant product | `B`, `B4`, `B_apply` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask01.Limits` | E2 | OUT_OF_SCOPE | Task 01, Layer 5: the two elementary boundary families and the two limiting regimes | `continuous_P`, `continuous_P_right`, `continuous_P_left` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask01.SplitComplex` | E2 | OUT_OF_SCOPE | Task 01, Layer 2: split-complex structure and null coordinates on `Long` | `mulL`, `mulL_apply`, `oneL` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask01.Strata` | E2 | OUT_OF_SCOPE | Task 01, Layer 4: the future-causal coefficient sector and its strata | `FutureCausalCoeff`, `FutureCausalVec`, `futureCausal_iff` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask01.Task01` | E2 | OUT_OF_SCOPE | Task 01: principal theorems | `task01_restriction`, `task01_idempotents`, `task01_unique_decomposition` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask02.Canonicality` | E2 | OUT_OF_SCOPE | Task 02, Layer 6: canonicality made testable | `TsymMap`, `TsymInv`, `TsymMap_apply` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask02.Comparison` | E2 | OUT_OF_SCOPE | Task 02, Layer 7: late comparison with Task 01 | `mulLBil`, `mulLBil_apply`, `oneL_eq_u` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask02.GeneralUnit` | E2 | OUT_OF_SCOPE | Task 02, Layer 5: arbitrary unit vectors | `compl`, `compl_fst`, `compl_snd` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask02.Minimality` | E2 | OUT_OF_SCOPE | Task 02, Layer 4: minimality audit — weakening the unit assumptions | `left_shape`, `leftAdmissible_dichotomy`, `twistU` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask02.Task02` | E2 | OUT_OF_SCOPE | Task 02: principal classification and obstruction theorems | `task02_polarization`, `task02_unit_normalized`, `task02_unit_normalized_left` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask03.Core` | E2 | OUT_OF_SCOPE | Task 03 core: Lorentz maps, unit orbit, product covariance, null pair | `IsLorentz`, `L2_of_isLorentz`, `isLorentz_refl` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask03.Task03` | E2 | OUT_OF_SCOPE | Task 03: principal theorems | `boostEquiv`, `boostEquiv_apply`, `boostEquiv_eq_B` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask04.Classification` | E2 | OUT_OF_SCOPE | Task 04, Layer 5: exact classification of all sector-compatible products | `mu4sym`, `mu4sym_apply`, `mu4sym_eq` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask04.Identification` | E2 | OUT_OF_SCOPE | Task 04, Layer 10: late mathematical identification — COMPARISON ONLY | `muLong_eq_mulL`, `spinFactorProduct`, `mu4sym_eq_spinFactorProduct` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask04.IdentityAudit` | E2 | OUT_OF_SCOPE | Task 04, Layer 6: identity audit for the reconstructed global products | `LeftAlternative`, `Flexible`, `PowerAssoc3` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask04.Isotropy` | E2 | OUT_OF_SCOPE | Task 04, Layer 7: the stabilizer of the chosen unit and full isotropy | `Stabilizer`, `stab_L4`, `stab_L4_e` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask04.Overlap` | E2 | OUT_OF_SCOPE | Task 04, Layer 9: sector overlaps versus cross-sector gluing | `sector_overlap_agreement`, `iotaS_time`, `sector_overlap_timelike` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask04.ProperIsotropy` | E2 | OUT_OF_SCOPE | Task 04, Layer 8: the proper stabilizer and the surviving gluing freedom | `alt3`, `alt3_apply`, `altBasis_eq_sp` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask04.Task04` | E2 | OUT_OF_SCOPE | Task 04 — principal theorems | `task04_polarization`, `task04_rest_space`, `task04_sector_embedding` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask06.ExactClassification` | E2 | OUT_OF_SCOPE | Task 06, Layer 6: the exact solution space and its coordinate formula | `properEquivariant_iff`, `smul_witDefect_injective`, `ProperSolutions` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask06.Existence` | E2 | OUT_OF_SCOPE | Task 06, Layer 5: existence, **after** rigidity | `wit3`, `wit3_apply`, `wit3_self` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask06.Identification` | E2 | OUT_OF_SCOPE | Task 06, Layer 8: late conventional identification — **COMPARISON ONLY** | `toFin3`, `toFin3_zero`, `toFin3_one` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask06.NormObstruction` | E2 | OUT_OF_SCOPE | Task 06, Phase B, Layer 2: the universal global-norm question | `Q4_add`, `Q4_sp_r`, `Q4_sp_r` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask06.OrientationReversal` | E2 | OUT_OF_SCOPE | Task 06, Layer 7: orientation reversal and the full isotropy | `reverseDefect`, `reverseDefect_apply`, `reverseDefect_involutive` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask06.ProperAction` | E2 | OUT_OF_SCOPE | Task 06, Layer 2: the proper rest-space isotropy (RE-DERIVED) | `Stab`, `stab_L4`, `stab_L4_e` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask06.Rigidity` | E2 | OUT_OF_SCOPE | Task 06, Layer 4: clean-room rigidity | `rigidity_r`, `rigidity_r`, `rigidity_r` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask06.Task04Comparison` | E2 | OUT_OF_SCOPE | Task 06, Layer 9: late comparison with Task 04 — **COMPARISON ONLY** | `det3_eq_task04`, `detRest_eq_task04`, `stab_iff_task04` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask06.Task06` | E2 | OUT_OF_SCOPE | Task 06: principal theorems and axiom report | `task06_generic_extension`, `task06_proper_isotropy`, `task06_rigidity` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask06.UniversalObstructionSummary` | E2 | OUT_OF_SCOPE | Task 06, Phase B, Layer 3: summary of the universal obstructions | `minimal_obstruction_configuration`, `associativity_universally_impossible`, `globalNorm_universally_impossible` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask06.UnknownDefect` | E2 | OUT_OF_SCOPE | Task 06, Layer 3: the unknown alternating defect | `ProperEquivariant`, `FullEquivariant`, `FullEquivariant` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask07.DirectWitness` | E2 | OUT_OF_SCOPE | Task 07, Layer 9: a direct finite-dimensional existence witness | `Wit`, `witMulFun`, `witMul` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask07.Identification` | E2 | OUT_OF_SCOPE | Task 07, Layer 12: late conventional identification — COMPARISON ONLY | `witToMat`, `matToWit`, `matToWit_witToMat` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask07.SignAudit` | E2 | OUT_OF_SCOPE | Task 07, Layer 11: generator-order and sign diagnostic | `swap_generators`, `neg_genA_mixed`, `neg_genB_mixed` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask07.Task07` | E2 | OUT_OF_SCOPE | Task 07 — principal theorems | `task07_inherited_square_law`, `task07_inherited_no_go`, `task07_polarization` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask07.Uniqueness` | E2 | OUT_OF_SCOPE | Task 07, Layer 10: uniqueness up to generator-preserving isomorphism | `witFamily`, `witFamily_eq_basisFun`, `bilinear_product_unique` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask08.Identification` | E2 | OUT_OF_SCOPE | Task 08, Layer 14: late conventional identification — COMPARISON ONLY | `toMat`, `fromMat`, `toMat_mul` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask08.SignPermutationAudit` | E2 | OUT_OF_SCOPE | Task 08, Layer 13: generator permutation and sign audit | `swapAB_channels`, `swapAC_channels`, `swapBC_channels` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask08.Task08` | E2 | OUT_OF_SCOPE | Task 08: principal theorems | `task08_old_carrier_data`, `task08_third_generator_square`, `task08_pairwise_anticommutation` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask08.Uniqueness` | E2 | OUT_OF_SCOPE | Task 08, Layer 12: uniqueness up to generator-preserving isomorphism | `witFamily8`, `witFamily8_eq_basisFun`, `bilinear_product_unique` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask09.CentralSignAudit` | E2 | OUT_OF_SCOPE | Task 09, Layer 7: the central-sign audit | `zFlip`, `zFlip_add`, `zFlip_smul` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask09.ExactClassification` | E2 | OUT_OF_SCOPE | Task 09, Layer 6: the exact classification | `exact_classification`, `exists_central_extension`, `solution_set_eq` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask09.Identification` | E2 | OUT_OF_SCOPE | Task 09, Layer 8: late conventional identification — COMPARISON ONLY | `Ncand_coord_0`, `Ncand_coord_7`, `Ncand_coord_1` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask09.Task09` | E2 | OUT_OF_SCOPE | Task 09: principal theorems | `task09_scalar_no_go`, `task09_minimal_scalar_obstruction`, `task09_central_plane` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask10.DynamicsDiagnostic` | E2 | OUT_OF_SCOPE | Task 10, Layer 9: the first dynamics diagnostic (§28) | `scaled_isAxialDerivation`, `generator_direction_fixed`, `generator_rate_not_fixed` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask10.Identification` | E2 | OUT_OF_SCOPE | Task 10, Layer 10: late conventional comparison — **COMPARISON ONLY** | `comparison_vector_weights`, `comparison_longitudinal_channel_is_fixed`, `comparison_double_valued_lift` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask10.Task10` | E2 | OUT_OF_SCOPE | Task 10 — principal theorems and axiom report | `task10_axis_decomposition`, `task10_old_axial_rotation`, `task10_algebra_extension` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask11.Identification` | E2 | OUT_OF_SCOPE | Task 11, Layer 11: late conventional comparison — **COMPARISON ONLY** | `comparison_toMat_zc`, `comparison_center_eq_scalars`, `comparison_residual_freedom` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask11.Task11` | E2 | OUT_OF_SCOPE | Task 11 — principal theorems and axiom report | `task11_center`, `task11_centralizer`, `task11_relative_lift` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask12.Identification` | E2 | OUT_OF_SCOPE | Task 12, Layer 11: late conventional comparison — **COMPARISON ONLY** | `comparison_Lgen_eq_left_ideal`, `comparison_generator_idempotent`, `comparison_minimal_dimension` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask12.Task12` | E2 | OUT_OF_SCOPE | Task 12 — principal theorems and axiom report | `task12_proper_carriers_exist`, `task12_possible_carrier_dimensions`, `task12_minimal_dimension` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask13.Identification` | E2 | OUT_OF_SCOPE | Task 13, Layer 13: late conventional identification — **COMPARISON ONLY** | `comparison_sector_factors`, `comparison_restricted_action`, `comparison_minimal_carrier` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask13.Task13` | E2 | OUT_OF_SCOPE | Task 13 — principal theorems and axiom report | `task13_minus_sector_stabilizer_exact`, `task13_minus_sector_reducible`, `task13_slices_central_stable` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask14.Identification` | E2 | OUT_OF_SCOPE | Task 14, Layer 21 (§75–§76): late conventional comparison — **COMPARISON ONLY** | `comparison_implementer_relations`, `comparison_implementer_algebra`, `comparison_bracket_relations` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask14.Task14` | E2 | OUT_OF_SCOPE | Task 14 — top module: principal theorem set and axiom report | `proved` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask15.OptionCAudit` | E2 | OUT_OF_SCOPE | Task 15, Layer 7 (§VIII): late structural comparison — **COMPARISON ONLY** | `optionC_structural_comparison` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask15.RateSeparation` | E2 | OUT_OF_SCOPE | Task 15, Layer 5 (§VI): the spatial rate and the central rates are independent | `rateFam`, `rateFam_zero`, `rateFam_group` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask15.ResidualAudit` | E2 | OUT_OF_SCOPE | Task 15, Layer 6 (§VII, §IX): exactly what remains free, and the final verdict | `regular_family_exact_parametrization`, `central_rates_not_constant`, `no_free_path_function` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask15.Task15` | E2 | OUT_OF_SCOPE | Task 15 — top module: principal theorem set and axiom report | — | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask16.Identification` | E2 | OUT_OF_SCOPE | Task 16, Layer 8: the late comparison module | `comparison_two_fold_parameter`, `comparison_global_versus_local` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask16.OptionCAudit` | E2 | OUT_OF_SCOPE | Task 16, Layer 7 (Work Package 6, second half): the Option-C dependency comparison | `optionC_comparison` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask16.RateAudit` | E2 | OUT_OF_SCOPE | Task 16, Layer 6 (Work Package 6, first half): the final rate audit and the negative | `rate_survival`, `spatial_rate_forced`, `control_no_basis_axis` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask16.Task16` | E2 | OUT_OF_SCOPE | Task 16: the principal theorems | `task16_coincidence_iff`, `task16_coincidence_coords`, `task16_coincidence_periodicity` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask17.Identification` | E2 | OUT_OF_SCOPE | Task 17, final layer: the comparison-only module | `comparison_local_pattern` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask17.Task17` | E2 | OUT_OF_SCOPE | Task 17: the principal theorems | `task17_dom_rescaling`, `task17_dom_nonempty_iff`, `task17_dom_normalized_iff` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask18.Identification` | E2 | OUT_OF_SCOPE | Task 18, final layer: the comparison-only module | `comparison_bridge_pattern` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask18.Task18` | E2 | OUT_OF_SCOPE | Task 18: the principal theorems | `task18_preconnected_admissibility`, `task18_admissibility_empty`, `task18_connected_admissibility` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask19.Identification` | E2 | OUT_OF_SCOPE | Task 19, final layer: the comparison-only module | `comparison_three_presentations` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask19.Task19` | E2 | OUT_OF_SCOPE | Task 19 — Intrinsic Global-Obstruction Decomposition: principal endpoints | `task19_primitive_bridge_exists`, `task19_primitive_bridge_normal_form`, `task19_primitive_bridge_determination` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |
| `RequestProject.Experiment2.NullSectorTask20.Task20` | E2 | OUT_OF_SCOPE | Task 20 — Intrinsic Equivalence and Structure Audit: principal endpoints | `task20_visible_quotient`, `task20_quotient_topology`, `task20_visible_group_law` | split-complex null-sector dynamics (Tasks I–XX): sector algebra, boosts, strata, identification and rate audits; the frame/lift line of Tasks XXI–XXXII does not depend on it |

## The two upstream endpoints that were *not* removed

* The Hermitian route of experiment 1 (`Herm2`, `Task6*`–`Task8*`, `Task9Freeze`,
  `SpinFinal` and their dependencies, 26 modules) is retained as the **comparison endpoint**
  reached through `RequestProject.Comparison.E1Hermitian`.  It is no longer a dependency of
  any definition of the intrinsic core.
* The Task-XXI…Task-XXV one-fibre chain of experiment 2 (193 modules) is retained as the
  **comparison endpoint** reached through `RequestProject.Comparison.E2Task26Endpoint`.  The
  Task-26 varying-family core no longer depends on it: the production chain now starts at
  `RequestProject.Spine.E2.Family.FamilyBase`, which imports `Mathlib` only.


---

## Addendum (refactoring task 03): modules removed from the active tree

| Module | Origin | Classification | Reason for exclusion |
| --- | --- | --- | --- |
| `RequestProject/Spine/E2/Model/CertifiedProjection.lean` | new-tree adapter over Experiment 2, Task 23 | REPLACED_BY_GENERIC_INTERFACE | it was the only import of a historical module left in the Spine; the theory is now generic in `InternalProjection` |
| `RequestProject/Spine/E2/Model/ModelBridge.lean` | new-tree adapter over Experiment 2, Tasks 21/26 | REPLACED_BY_GENERIC_INTERFACE | existed only to read the legacy projection over the visible model group |
| `RequestProject/Comparison/E1Hermitian.lean` | Experiment 1 (`Task9Freeze`, `SpinFinal`) | SUPERSEDED | bridge module into the historical tree; forbidden by the zero-legacy rule |
| `RequestProject/Comparison/E2OneFibreComparison.lean` | Experiment 2, Task 25 | SUPERSEDED | as above |
| `RequestProject/Comparison/E2Task26Endpoint.lean` | Experiment 2, Task 26 | SUPERSEDED | as above (it imported the one-fibre comparison) |

Modules moved rather than removed: `Spine/E2/Model/InternalTransitionInterface.lean` →
`Spine/E2/Lift/TransitionSystem.lean`, `Spine/E2/Model/Task28.lean` →
`Spine/E2/Lift/LiftLevels.lean`, `RequestProject/Control/E2/**` →
`RequestProject/Spine/Controls/E2/**` (all with `git mv`).

The full migration provenance table, including the declarations that were generalized,
reconstructed natively or deliberately not migrated, is in `LEGACY_DECOUPLING_AUDIT.md` §3.

## Task-5 addendum: external scholarly references

The Task-5 layer `RequestProject/Spine/Cohomology/**` was written natively from Mathlib
primitives, but external Lean projects were **inspected** as scholarly and engineering
references beforehand.  None of them is a dependency: there is no git requirement, no copied
file, no copied namespace, no vendored source and no external module in any import closure
(mechanical check: `SpineAudit.auditNoExternal` in `RequestProject/Spine/Audit/Firewall.lean`,
external-project imports = 0 over all Spine modules).

The complete, append-only ledger — project, owner, repository, files inspected, commit hash,
access date, licence status, concepts and implementation ideas consulted, whether local design
was influenced, and whether statements or proof architecture resemble external ones — is
`TASK05_EXTERNAL_SOURCES.md`.  It must be cited in any later publication of this work.

---

# Task 10 addendum (2026-09-08)

Task 10 imported no external project.  The only dependency remains `mathlib` at tag `v4.28.0`
(`lake-manifest.json`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`, Apache 2.0), and the
mechanical firewall reports `Spine external-project imports: 0` on the full build.

The Task-10 source ledger — every file of the pinned dependency inspected, the declarations
read, what was used and what was confirmed absent, and the influence category of each item —
is `TASK10_EXTERNAL_SOURCES.md`.  It must be cited alongside `TASK05_EXTERNAL_SOURCES.md` and
`TASK08_EXTERNAL_SOURCES.md`/`TASK09_EXTERNAL_SOURCES.md` in any later publication.

No proof block from any source was copied.  The one place where an external proof *idiom* was
consulted (Mathlib's `IsManifold.disjointUnion`, for the pattern "same chart ⟹ compatible,
different charts ⟹ empty source") is recorded there as `DESIGN_REFERENCE`; the Task-10 instance
`SpineTask10.isManifoldSigma` is an independent proof for `Σ`-indexed disjoint unions.

---

# Task 11 addendum (2026-09-09)

Task 11 imported no external project and changed no dependency.  `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json` are byte-identical to their Task-10 state: the only
dependency remains `mathlib` at tag `v4.28.0` (commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, Apache 2.0), and the mechanical firewall reports
`Spine external-project imports: 0`, `Experiment1 = 0`, `Experiment2 = 0` (direct and
transitive) on the full build.

Task 11 inspected, as **external research sources only** and without importing anything:

* upstream `leanprover-community/mathlib4` @ `076c9da2981330e0d1ba84a10afa6544faafa612`
  (2026-09-09, Lean `v4.34.0-rc2`) — audited in a scratch checkout outside the Lake project;
* `joelriou/excision` @ `7d6441e263568075b0228ca503b6976b4269906f` (Apache 2.0 headers);
* `Shamrock-Frost/BrouwerFixedPoint` @ `2883ceb0f5d461155fa1689266a7af40ff8ae671` (Lean 3, **no
  licence** — decomposition consulted, no code usable).

The complete Task-11 ledger, with files, commits, licences, theorems inspected and influence
categories, is `TASK11_EXTERNAL_SOURCES.md`; the audit itself is
`TASK11_UPSTREAM_DELTA_AUDIT.md`.  Task 11 added one Lean module,
`RequestProject/Spine/Nerve/Task11Probe.lean` (five declarations, all compile probes, axiom
audit `[propext, Classical.choice, Quot.sound]`), and two documentation corrections
(`ComparisonSpec.lean`, `ChainHomotopyComparison.lean`) plus the append-only
`TASK 11 CORRECTION SECTION` of `TASK10_AUDIT.md`.

# Task 12 addendum (2026-09-09)

Task 12 imported no external project and changed no dependency.  `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json` are byte-identical to their Task-10/Task-11 state: the
only dependency remains `mathlib` at tag `v4.28.0` (commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, Apache 2.0), and the mechanical firewall reports
`Spine external-project imports: 0`, `Experiment1 = 0`, `Experiment2 = 0` (direct and
transitive) on the full build.

Task 12 consulted, as **external research sources only** and without importing anything:
Eilenberg–MacLane, *Acyclic Models*, Amer. J. Math. 75 (1953) 189–199 (DOI 10.2307/2372628);
Rotman, *An Introduction to Algebraic Topology* (1988), ch. 9 Thm. 9.12; Barr, *Acyclic Models*
(Canad. J. Math. 48 (1996) 258–273, DOI 10.4153/CJM-1996-013-x; CRM Monograph 17, 2002);
Hatcher, *Algebraic Topology* (2002), §2.1 Thm. 2.27 (author's official PDF, read verbatim);
Milnor, Ann. of Math. 65 (1957) 357–362 (DOI 10.2307/1969967); May, *Simplicial Objects in
Algebraic Topology* (1967); and the Wikipedia article *Acyclic model* (rev. 1321158231).  No
external Lean formalisation was inspected or used.

Task 12 added one Lean module, `RequestProject/Spine/Nerve/Task12Probe.lean` (route-gate probes
and counterexamples; every declaration audited to `[propext, Classical.choice, Quot.sound]`), and
three documents: `TASK12_ACYCLIC_MODELS_APPLICABILITY.md`, `TASK12_EXTERNAL_SOURCES.md`,
`TASK12_FAILBUILDS.md`.  No existing declaration was edited, and the Task-10 map `J = C_*(η_K)`
is untouched.

# Task 34 addendum (2026-09-12)

Task 34 imported no external project and changed no dependency.  `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json` are byte-identical to their earlier state: the only
dependency remains `mathlib` at tag `v4.28.0` (commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, Apache 2.0).  No external Lean formalisation was
inspected or used; the only libraries read were the pinned Mathlib's own
`Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean` and `Mathlib/Topology/VectorBundle/Basic.lean`,
to determine the exact shape of `tangentBundleCore` and `VectorBundleCore` in the pin.

Task 34 added six Lean modules —
`Spine/Emergent/TangentTransition.lean`, `Spine/Solder/InternalLorentz.lean`,
`Spine/Solder/Independence.lean`, `Spine/Solder/Solder.lean`,
`Spine/Solder/LorentzBundle.lean`, `Spine/Comparison/SolderTangentGate.lean` — all
`sorry`-free, every principal endpoint audited to `[propext, Classical.choice, Quot.sound]`.
It edited two pre-existing Lean files: `Spine/Audit/ArchitectureDAG.lean` (firewall extension,
checks 9 and 10) and `Spine/Emergent/Symmetric.lean` (documentation only).

Documentation: `TASK34_PROVENANCE.md`, `TASK34_AUDIT.md`, `TASK34_CODE_HYGIENE.md`,
`TASK34_FAILBUILDS.md`, `TASK34_DOCUMENTATION_REPAIR.md`, plus correction notices added to
`TASK32_PROVENANCE.md`, `TASK32_AUDIT.md`, `TASK32_CODE_HYGIENE.md`, `TASK33_PROVENANCE.md`
and `TASK33_AUDIT.md`.  No historical statement was deleted or rewritten in place.

# Task 35 addendum (2026-09-12)

Task 35 imported no external project and changed no dependency.  `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json` are byte-identical to their earlier state: the only
dependency remains `mathlib` at tag `v4.28.0` (commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, Apache 2.0).  No external Lean formalisation was
inspected or used; the libraries read were the pinned Mathlib's own
`Mathlib/Topology/VectorBundle/Basic.lean`, `Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean`,
`Mathlib/Geometry/Manifold/VectorBundle/Basic.lean`, `Mathlib/Analysis/Calculus/ContDiff/*` and
`Mathlib/Analysis/Calculus/FDeriv/*`, to determine exactly which bundle, frame and smoothness
objects exist in the pin (recorded in `TASK35_AUDIT.md`).

Task 35 added eight Lean modules — `Spine/Solder/RegularSolder.lean`,
`Spine/Solder/RegularExamples.lean`, `Spine/Solder/BundleEquivalence.lean`,
`Spine/Solder/SmoothMetric.lean`, `Spine/Solder/OrientationTime.lean`,
`Spine/Solder/WeakInsufficiency.lean`, `Spine/Solder/RegularGauge.lean`,
`Spine/Comparison/SmoothSolderGate.lean` — all `sorry`-free, every endpoint audited to
`[propext, Classical.choice, Quot.sound]`.  It edited four pre-existing Lean files:
`Spine/Solder/InternalLorentz.lean` and `Spine/Solder/Independence.lean` (dependency-DAG
repair, docstrings, hygiene), `Spine/Solder/Solder.lean` (hygiene only) and
`Spine/Audit/ArchitectureDAG.lean` (firewall extension).  No pre-existing theorem statement was
changed.

Documentation: `TASK35_PROVENANCE.md`, `TASK35_AUDIT.md`, `TASK35_CODE_HYGIENE.md`,
`TASK35_FAILBUILDS.md`, updates to `DEPENDENCY_DAG.md` and `ARCHITECTURE.md`, and correction
notices appended to `TASK34_PROVENANCE.md`, `TASK34_AUDIT.md`,
`TASK34_DOCUMENTATION_REPAIR.md` and `TASK34_CODE_HYGIENE.md`.  No historical statement was
deleted or rewritten in place.

# Task 36 addendum (2026-09-12)

Task 36 imported no external project and changed no dependency.  `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json` are byte-identical to their earlier state: the only
dependency remains `mathlib` at tag `v4.28.0` (commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, Apache 2.0).  No external Lean formalisation was
inspected or used.  The pinned Mathlib was audited for the objects Task 36 would have needed —
vector-bundle morphisms, Cartan's closed-subgroup theorem, Stiefel–Whitney classes, Euler
characteristics, Lorentzian metrics, manifold Spin structures — and each absence is recorded
with the exact missing result in `TASK36_AUDIT.md`.

Task 36 added 14 Lean modules, all under `RequestProject/Spine/Task36/`:
`LoopModel.lean`, `OrientationGate.lean`, `OrientationReversing.lean`, `LoopSolder.lean`,
`LoopSpinFreedom.lean`, `TimeOrientation.lean`, `TrivialControl.lean`, `SpinObstruction.lean`,
`SmoothBundlePackaging.lean`, `GaugeGroup.lean`, `SpinNotLorentz.lean`,
`SpinFoamControl.lean`, `Certificate.lean`, `Firewall.lean` — all `sorry`-free, with 53
in-source `#print axioms` audits, every one reporting
`[propext, Classical.choice, Quot.sound]`.

It edited three pre-existing Lean files, **docstrings only**, appending correction notices
that preserve the original wording verbatim: `Spine/Solder/BundleEquivalence.lean` (Task-36
§1), `Spine/Solder/OrientationTime.lean` (Task-36 §3) and `Spine/Solder/RegularGauge.lean`
(Task-36 §4).  No pre-existing theorem statement, hypothesis or proof was changed.

Documentation: `TASK36_PROVENANCE.md`, `TASK36_AUDIT.md`, `TASK36_CODE_HYGIENE.md`,
`TASK36_FAILBUILDS.md`, `TASK36_COUNTERTEST_MATRIX.md`, updates to `DEPENDENCY_DAG.md` and
`ARCHITECTURE.md`, and correction notices appended to `TASK35_PROVENANCE.md` and
`TASK35_AUDIT.md`.  No historical statement was deleted or rewritten in place.

## Task 37 — freeze refactor and deformation-ready shared-transport interface

Task 37 froze Task 36 and prepared the interface for the next task's deformation smoke test;
it did **not** run the experiment.

*Freeze refactor.*  Eleven Task-36 import lists were rewritten so that the general layers no
longer depend on the adversarial loop models (depth to the firewall 9 → 5); the loop-specific
time-orientation control was moved verbatim into the new
`RequestProject/Spine/Task36/LoopTimeOrientation.lean`; the arbitrary-basis determinant
continuity lemma, which needed `classical`, was replaced by the `LocalModel`-specific
`Task36.continuous_det_localModel` built from the project's explicit `Fin 4` coordinates; and
the loop-model documentation was corrected to the exact proved terminology (periodic
fixed-cover loop model, two-component periodic overlap, project-native loop-sign control,
fixed-cover `ℤ₂` lift freedom) — no `S¹ × ℝ³` or `π₁` claim is made anywhere.  Every Task-36
endpoint survives unchanged.

*Deformation preparation.*  Five new modules under `RequestProject/Spine/Deformation/`
(1 189 lines, `sorry`-free, every endpoint `[propext, Classical.choice, Quot.sound]`): the one
shared native Spin-side transport state `transportState : ℝ → SpinGroup` with
`transportState 0 = 1` and the one-parameter group law, its derived Lorentz projection (which
is provably non-trivial for `λ ≠ 0`, unlike the Task-36 kernel twist), the `λ`-deformed native
Spin transition datum on the periodic fixed-cover loop model with its Čech cocycle law and its
exact regression to the frozen seed at `λ = 0`, the closure-solution object
`RegularClosureSolution` with its existence predicate `RegularClosureAdmissible`, the
CONTROL A / MAIN TEST B distinction, anti-vacuity controls showing that closure can fail at
every parameter value and that it can hold exactly at `λ = 0`, the `λ → 0±` / `λ → ±∞` regime
vocabulary, and a compile-time firewall enforcing the shared origin of the Lorentz data and
the absence of any target-geometry token.

Connection, parallel transport and holonomy remain **NOT FORMALIZED**, and this is stated
explicitly rather than papered over.  Documents: `TASK37_PROVENANCE.md`, `TASK37_AUDIT.md`,
`TASK37_CODE_HYGIENE.md`, `TASK37_FAILBUILDS.md`, `TASK37_DEFORMATION_INTERFACE.md`,
`TASK38_SHARED_TRANSPORT_SMOKETEST_HANDOFF.md`, plus updates to `DEPENDENCY_DAG.md` and
`ARCHITECTURE.md` and correction notices in the Task-36 documents.

## Task 38 — the knob turn

*The first actual experiment on the Task-37 knob.*  Five new modules inside the same leaf
branch (`ProjectedParaAction`, `FixedBaseSmokeTest`, `CocycleGaugeOrbit`,
`TangentMetricComparison`, `SmokeTestCertificate`; `sorry`-free, every endpoint
`[propext, Classical.choice, Quot.sound]`, green build with 8 352 jobs).

Proved, for the frozen periodic control base with the base gluing held fixed: the admissibility
locus of the Task-37 native Spin transition deformation is **all of `ℝ`**, with an explicitly
constructed compensating regular solder (not a choice principle, and not the identity solder);
admissibility is symmetric in the sign of the parameter; the whole family lies in **one** gauge
orbit of the full-group cocycle gauge equivalence, on the Spin side and — by projecting the same
Spin gauge — on the Lorentz side; the explicit solder witnesses differ chartwise by an element
of the intrinsic Lorentz group; and the induced tangent Lorentz metrics are **literally equal**.
At the narrower kernel-valued equivalence a nonzero deformation is *not* equivalent to the
neutral datum, which records only that the projection moves.

Scientific outcome **C / PASS-C0**: the currently formalized native Čech transition-cocycle knob
is trivialisation freedom, not a closure-sensitive geometric degree of freedom.  Transport
one-forms, parallel transport, loop transport and field strength remain NOT FORMALIZED and were
deliberately not built.  Documents: `TASK38_PROVENANCE.md`, `TASK38_AUDIT.md`,
`TASK38_CODE_HYGIENE.md`, `TASK38_FAILBUILDS.md`, `TASK38_SMOKETEST_RESULT.md`,
`TASK38_GAUGE_CLASSIFICATION.md`, `TASK39_CONNECTION_TRANSPORT_GATE_HANDOFF.md`, plus updates to
`DEPENDENCY_DAG.md` and `ARCHITECTURE.md`.

---

## Task 40 — intermediate release hardening (documentation only)

No mathematics was added, removed or weakened: the frozen Task-39 intermediate closure is the
mathematical baseline, and the only Lean edit was five additional `#print axioms` lines in the
audit-only module `RequestProject/Spine/Closure/AxiomAudit.lean`.

Six review defects were repaired: the overgeneralized reading of the Task-38 result; the false
statement that the project contains no Lie algebra (it contains the intrinsic Lorentz-skew
`SpinCore.gB` / `SpinCore.gBLie`, six-dimensional, linearly equivalent to the bivector space of
the intrinsic carrier); the type-incorrect future-connection relation applying the group-level
`SpinCore.spinCover` to a Lie-algebra-valued one-form; the conflated primitive/global/gate
taxonomy of `docs/machine/PROJECT_STATE.json`; two registry entries that presented definitions
as theorems; and the Task-39 module count (four modules, not three).  Five further defects found
during the work are listed in `TASK40_RELEASE_HARDENING_AUDIT.md` §3.

The next-phase specification now lives in `NEXT_PHASE_TRANSPORT_GATE.md`, which is part of the
validated canonical document set.  The earlier draft
`TASK39_CONNECTION_TRANSPORT_GATE_HANDOFF.md` is retained as a withdrawal stub so that the
historical Task-38/39 references above still resolve; its three incorrect statements are quoted
there only in order to withdraw them.

Documents: `TASK40_RELEASE_HARDENING_AUDIT.md`, `TASK40_FAILBUILDS.md`,
`NEXT_PHASE_TRANSPORT_GATE.md`, `docs/machine/REGISTRY_SCHEMA.md`, plus updates to
`INTERMEDIATE_MILESTONE_README.md`, `PROJECT_INTERMEDIATE_HANDOFF.md`, `ARCHITECTURE.md`,
`TASK39_AUDIT.md`, `docs/mathematics/LOCAL_MATHEMATICS.md`, `docs/paper/*.md` and the whole
machine-readable snapshot under `docs/machine/`.
