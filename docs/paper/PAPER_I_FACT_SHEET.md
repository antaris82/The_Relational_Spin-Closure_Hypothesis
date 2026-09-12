# PAPER I — fact sheet

**This is not the paper.**  It is the list of statements that are safe to use in a scientific
manuscript, each with its Claim ID, its supporting theorem IDs, the exact Lean modules, its
formal status and its scope.  A statement that is not here must not be used.

Statuses: `PROVED`, `PROVED_PROJECT_NATIVE` (proved, but about the project's own notion rather
than a standard one), `CONSTRUCTED_CONTROL` (proved on an explicitly constructed control model),
`DOCUMENTED_ONLY`, `OPEN`, `NEGATIVE_CONTROL`, `INFRASTRUCTURE_BLOCKED`.

Registries: `docs/machine/CLAIM_REGISTRY.jsonl`, `docs/machine/THEOREM_REGISTRY.jsonl`.
Machine-readable pairing: `docs/machine/PROJECT_INDEX.tsv`.

---

## 1. Primitive local starting point

| claim | statement | theorems | modules | status | scope / caveat |
| --- | --- | --- | --- | --- | --- |
| [CLAIM-L001] | The input is ℝ³ with a positive definite Euclidean form. | — | `Spine/E1/Carrier.lean`, `Spine/E1/Clifford.lean` | DOCUMENTED_ONLY | A definitional choice; no necessity or uniqueness is claimed. |
| [CLAIM-L002] | The spin-factor carrier ℝ ⊕ ℝ³ carries a quadratic form of signature (1,3). | THM-L001 | `Spine/E1/Carrier.lean`, `Spine/E1/Core.lean` | PROVED | Linear algebra of the carrier; not a statement about a manifold. |

## 2. Lorentz / Clifford / Spin reconstruction

| claim | statement | theorems | modules | status | scope / caveat |
| --- | --- | --- | --- | --- | --- |
| [CLAIM-L003] | `Cl₃` is the Clifford algebra of the positive Euclidean three-form; generators square to +1. | THM-L002 | `Spine/E1/Clifford.lean` | PROVED | Not a Lorentzian Clifford algebra. |
| [CLAIM-L004] | The paravector embedding realises the intrinsic Lorentz norm as the Clifford norm. | THM-L003 | `Spine/E1/Clifford.lean`, `Spine/E1/Core.lean` | PROVED | The bridge to Lorentz signature; no isomorphism claim. |
| [CLAIM-L005] | Clifford and Jordan structures agree on the embedded spin factor. | THM-L004 | `Spine/E1/Clifford.lean` | PROVED | No classification of Jordan algebras. |
| [CLAIM-L006] | The embedded carrier generates `Cl₃`. | THM-L005 | `Spine/E1/Clifford.lean` | PROVED | No uniqueness of the generating subspace. |
| [CLAIM-L007] | The intrinsic Spin group double covers the intrinsic Lorentz group: surjective homomorphism, central kernel of order two. | THM-L006, THM-L007 | `Spine/E1/SpinGroup.lean`, `SpinCover.lean`, `SpinKernel.lean`, `Core.lean` | PROVED | `GLor` is the project's own group; proved without `SL(2,ℂ)`. |
| [CLAIM-L008] | Both groups are Hausdorff topological groups; the cover is continuous with central discrete kernel. | THM-L008 | `Spine/E1/Topology/Core.lean` | PROVED | Topological only — see [CLAIM-B001]. |
| [CLAIM-L009] | The cover admits continuous local sections everywhere. | THM-L009 | `Spine/E1/Topology/LocalSection.lean` | PROVED | Continuous, not smooth. |
| [CLAIM-L011] | The intrinsic Lorentz sector also carries a six-dimensional Lorentz-skew Lie-algebra realization, linearly equivalent to the bivector space constructed from the Lorentz carrier. | THM-L012, THM-L013, THM-L014, THM-L015 | `Spine/E1/Bivector.lean`, `Spine/E1/LieAlgebra.lean` | PROVED | `gB`/`gBLie` are skew for the project's own form `BS`. **Not** identified with `Lie(SpinGroup)`: no such object exists here — see [CLAIM-B010], [CLAIM-B011]. |

## 3. Emergent smooth four-manifold

| claim | statement | theorems | modules | status | scope / caveat |
| --- | --- | --- | --- | --- | --- |
| [CLAIM-G001] | The base gluing is additional information, not derivable from the local core. | THM-G001 | `Spine/Emergent/NonDerivability.lean` | PROVED | Exhibits an inequivalence; no classification. |
| [CLAIM-G003] | A smooth base gluing yields a `C^∞` four-manifold. | THM-G002 | `Spine/Emergent/SmoothStructure.lean` | PROVED | Smoothness of the primitive is a hypothesis, with a counterexample if dropped. |
| [CLAIM-G004] | Emergent-manifold certificate: Hausdorff, second countable, charted, `C^∞`, four-dimensional. | THM-G003 | `Spine/Emergent/SmoothStructure.lean` | PROVED | Nothing about diffeomorphism type, compactness or homotopy type. |
| [CLAIM-G005] | The tangent transitions of the emergent atlas are the derivatives `D(φ_ij)`. | THM-G004 | `Spine/Emergent/TangentTransition.lean` | PROVED | Mathlib's genuine tangent bundle; `TM` is not trivialised. |

## 4. Regular solder and tangent Lorentz geometry

| claim | statement | theorems | modules | status | scope / caveat |
| --- | --- | --- | --- | --- | --- |
| [CLAIM-G006] | The solder is an additional coupling datum; base + Spin data do not force it. | THM-G005 | `Spine/Solder/Independence.lean` | PROVED | Does not say a solder never exists. |
| [CLAIM-G007] | A weak (fibrewise) solder is insufficient: explicit discontinuous representative and metric. | THM-G007 | `Spine/Solder/WeakInsufficiency.lean` | NEGATIVE_CONTROL | One explicit model. |
| [CLAIM-G008] | A regular solder is exactly a regular bundle equivalence internal Lorentz bundle ≃ `TM`. | THM-G008, THM-G015 | `Spine/Solder/BundleEquivalence.lean`, `Spine/Task36/SmoothBundlePackaging.lean` | PROVED | **Not** a smooth bundle equivalence in the strong sense: the total-space maps are continuous and the local representatives are `C^∞`.  The remaining limitation is an **infrastructure / packaging limitation** (the pinned Mathlib has no vector-bundle equivalence type; `IsContMDiff` is stated over the base manifold, the solder supplies `ContDiffOn` in chart coordinates), **not** "the native Spin transitions are only continuous".  **Certified:** a regular smooth solder gives smooth local/projected Lorentz transition representatives — `SmoothTangentSolderData.contDiffOn_solderLorentzRep` and `Task36.internal_bundle_coordChange_smooth_in_charts`, in `Spine/Solder/RegularSolder.lean` and `Spine/Task36/SmoothBundlePackaging.lean` — so smoothness of the native Spin cocycle is **not** required merely to obtain smooth projected Lorentz bundle data.  That smooth *projected Lorentz* data is **not** a fully packaged smooth intrinsic Spin Lie-group bundle theory; neither may be cited as evidence for the other ([CLAIM-B001]). |
| [CLAIM-G009] | A regular solder induces a `C^∞`, symmetric, nondegenerate, tensorial tangent metric of signature (1,3). | THM-G009 | `Spine/Solder/SmoothMetric.lean` | PROVED | Conditional on a solder; no connection, curvature or torsion. |
| [CLAIM-G010] | The transported form is chart independent. | THM-G006 | `Spine/Solder/Solder.lean` | PROVED | Already at the weak level. |
| [CLAIM-G016] | Solders for fixed data form a torsor under a regular gauge group. | THM-G018, THM-G019 | `Spine/Task36/GaugeGroup.lean`, `Spine/Solder/RegularGauge.lean` | PROVED | Fixed base and fixed Spin datum. |

## 5. Global reconvergence

| claim | statement | theorems | modules | status | scope / caveat |
| --- | --- | --- | --- | --- | --- |
| [CLAIM-G011] | A regular solder forces orientation compatibility of the emergent atlas. | THM-G010, THM-G014 | `Spine/Task36/OrientationGate.lean`, `SpinObstruction.lean` | PROVED_PROJECT_NATIVE | **Not** `w₁(TM) = 0`. |
| [CLAIM-G012] | A nontrivial orientation obstruction rules out every regular solder. | THM-G011 | `Spine/Task36/OrientationGate.lean` | PROVED_PROJECT_NATIVE | No characteristic class computed. |
| [CLAIM-G013] | A regular solder forces triviality of the project-native Spin-lifting obstruction. | THM-G012, THM-G014 | `Spine/Task36/SpinObstruction.lean` | PROVED_PROJECT_NATIVE | **Not** `w₂(TM) = 0` — see [CLAIM-B002]. |
| [CLAIM-G014] | A nontrivial native obstruction rules out the solder. | THM-G013 | `Spine/Task36/SpinObstruction.lean` | PROVED_PROJECT_NATIVE | Project-native. |
| [CLAIM-G015] | A regular solder yields a coherent future-cone reduction; on the control it is glued. | THM-G016, THM-G017 | `Spine/Task36/TimeOrientation.lean`, `LoopTimeOrientation.lean` | PROVED | Not standard time-orientability — see [CLAIM-B006]. |
| [CLAIM-G018] | The discrete fixed-cover Spin-lift freedom survives the construction. | THM-G020 | `Spine/Task36/LoopSpinFreedom.lean` | PROVED_PROJECT_NATIVE | Fixed cover; not `H¹(M; ℤ/2)`. |
| [CLAIM-G019] | Two independent loops give four gauge-inequivalent lifts, all soldered. | THM-G021 | `Spine/Task36/LoopSpinFreedom.lean` | PROVED_PROJECT_NATIVE | Fixed cover. |
| [CLAIM-G023] | One Lean certificate aggregates the frozen intermediate state. | THM-C001 … THM-C005 | `Spine/Closure/IntermediateMilestone.lean` | PROVED | Aggregation only. |

## 6. Adversarial topology controls

| claim | statement | theorems | modules | status |
| --- | --- | --- | --- | --- |
| [CLAIM-G017] / [CLAIM-N003] | The Möbius-type gluing admits no regular solder for any native Spin datum. | THM-G022 | `Spine/Task36/OrientationReversing.lean` | NEGATIVE_CONTROL |
| [CLAIM-N009] | Over that model native Spin data exist while no solder does. | THM-G023 | `Spine/Task36/SpinNotLorentz.lean` | NEGATIVE_CONTROL |
| [CLAIM-N008] | Combinatorial labels do not determine a solder. | THM-G024 | `Spine/Task36/SpinFoamControl.lean` | NEGATIVE_CONTROL |
| [CLAIM-N010] | One-chart positive control: the gates are not vacuously closed. | THM-G025 | `Spine/Task36/TrivialControl.lean` | NEGATIVE_CONTROL |
| [CLAIM-G020] | The two gates reject their controls independently. | THM-G011, THM-G013, THM-G022 | `Spine/Task36/Certificate.lean` | PROVED_PROJECT_NATIVE |
| [CLAIM-G021] | The battery is bundled in one certificate. | THM-G026 | `Spine/Task36/Certificate.lean` | PROVED |
| [CLAIM-N006] | The closure observable is not vacuous: no universal existence, and a selective family. | THM-S001, THM-S002 | `Spine/Deformation/ClosureAdmissibility.lean` | NEGATIVE_CONTROL |

## 7. First native deformation smoke test

All rows are **CONSTRUCTED_CONTROL**: they hold for the frozen periodic control base
`Task36.loopGluingOf κ LoopTwist.id'` and the family `Task37.Deformation.loopSharedSpin`, and
for nothing else.

**Selected control direction ([CLAIM-L010], OBJ-031).**  The Task-37/38 deformation is a
deliberately selected one-parameter subgroup generated by the chosen Clifford direction
`cle 0` (`transportElem l = cosh(l/2) + sinh(l/2) · cle 0`,
`Spine/Deformation/SharedTransport.lean`).  It is a control slice through the intrinsic Spin
structure, not a theorem that this direction is canonical, exhaustive, or the full deformation
space.  Machine-readable classification: `canonical_status: SELECTED_CONTROL`,
`exhaustive: false`.  In particular the Task-38 pure-gauge result is **not** a classification
of the native Spin deformation space and does **not** apply to every possible native Spin
deformation.

| claim | statement | theorems | modules |
| --- | --- | --- | --- |
| [CLAIM-S012] | Theorem-level interface record of what is varied, derived, fixed and solved for. | THM-S003 | `Spine/Deformation/SmokeTestCertificate.lean` |
| [CLAIM-S001] | Every finite parameter value is globally admissible, with an explicit compensating regular solder. | THM-S004, THM-S005, THM-S013 | `Spine/Deformation/FixedBaseSmokeTest.lean` |
| [CLAIM-S002] | The admissibility locus is all of ℝ, solved exactly. | THM-S006 | `Spine/Deformation/FixedBaseSmokeTest.lean` |
| [CLAIM-S003] | Admissibility is symmetric under sign reversal. | THM-S007 | `Spine/Deformation/FixedBaseSmokeTest.lean` |
| [CLAIM-S004] | The family lies in one full-Spin Čech gauge orbit (continuous gauge). | THM-S008 | `Spine/Deformation/CocycleGaugeOrbit.lean` |
| [CLAIM-S005] | The projected Lorentz cocycles are gauge related through the same Spin gauge. | THM-S009 | `Spine/Deformation/CocycleGaugeOrbit.lean` |
| [CLAIM-S006] | At the kernel-valued relation nonzero parameters are separated (lift labels only). | THM-S010, THM-S014 | `Spine/Deformation/CocycleGaugeOrbit.lean` |
| [CLAIM-S008] | Along the explicit branch the induced tangent Lorentz metric is literally equal. | THM-S011, THM-S012 | `Spine/Deformation/TangentMetricComparison.lean` |
| [CLAIM-S009] | The **projected** Lorentz gauge is `C^∞` on every chart domain; the Spin gauge is continuous only. | THM-S015, THM-S016 | `Spine/Deformation/SmoothProjectedGauge.lean` |
| [CLAIM-S010] | The regular solder solution spaces at two parameter values are in explicit bijection, with the induced tangent metric preserved. | THM-S019, THM-S020, THM-S021 (the constructions transported are THM-S017, THM-S018) | `Spine/Deformation/SolderTransport.lean` |
| [CLAIM-S011] | Scientific reading, scoped to the control. | THM-S013, THM-C004 | `Spine/Deformation/SmokeTestCertificate.lean`, `Spine/Closure/IntermediateMilestone.lean` |

**Manuscript wording for §7** (use verbatim, or weaker):

> The specific native one-parameter Spin Čech-transition deformation of the frozen periodic
> fixed-cover control base is globally admissible for all finite parameter values and lies in a
> single full-Spin Čech gauge orbit.  On that control the regular solder solution spaces at any
> two parameter values are in explicit bijection, and corresponding solutions induce exactly the
> same tangent Lorentz metric.

## 8. Exact present boundary

| claim | boundary | status |
| --- | --- | --- |
| [CLAIM-B001] | No smooth Lie-group package for the intrinsic Spin group; the Spin-side gauge is continuous. | INFRASTRUCTURE_BLOCKED |
| [CLAIM-B002] | The native obstruction is not formally compared with `w₂(TM)`; no Stiefel–Whitney classes exist here. | INFRASTRUCTURE_BLOCKED |
| [CLAIM-B003] | No connection, parallel transport, holonomy, curvature or field equation exists. | OPEN |
| [CLAIM-B004] | The control base is not proved homeomorphic to `S¹ × ℝ³`. | OPEN |
| [CLAIM-B005] | Fixed-cover lift freedom is not `H¹(M; ℤ/2)`. | OPEN |
| [CLAIM-B006] | The future-cone reduction is not proved equivalent to standard time-orientability. | OPEN |
| [CLAIM-B007] | No general existence theorem for the regular solder. | OPEN |
| [CLAIM-B008] | No gravitational dynamics has been derived. | OPEN |
| [CLAIM-B010] | The certified Lie algebra `gB`/`gBLie` is **not** identified with an infinitesimal structure of the intrinsic `SpinGroup`; there is no `Lie(SpinGroup)` and no proved `Lie(SpinGroup) ≃ gB`. | OPEN |
| [CLAIM-B011] | There is no differential `dρ_e` of the native Spin cover and no equivalent proved infinitesimal representation; `spinCover` is group-level and may not be applied to a connection one-form. | OPEN |

## 9. Next open question

[CLAIM-B009] — where the first genuinely gauge-nontrivial shared-transport deformation lives is
open.  The likely candidate is below the Čech-transition layer, at the level of connection,
parallel transport and holonomy; this is a research direction and must be written as one.  The
exact missing structures are `OP-001` … `OP-005` and `OP-012` in
`docs/machine/OPEN_PROBLEMS.jsonl`.

The next phase does **not** begin at "construct some Lie algebra": the Lorentz-skew Lie algebra
exists [CLAIM-L011].  It begins at the missing infinitesimal bridge
`Lie(SpinGroup) ≃ gB` and the missing differential `dρ_e` [CLAIM-B010], [CLAIM-B011], `OP-012`;
the exact boundary diagram is in `NEXT_PHASE_TRANSPORT_GATE.md` §4.

---

Before using any row of this sheet, check `docs/paper/PAPER_I_DO_NOT_CLAIM.md`.
