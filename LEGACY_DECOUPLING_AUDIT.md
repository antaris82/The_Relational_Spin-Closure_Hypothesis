# Complete legacy decoupling of the new Spine — audit report

**Result.** The new mathematical project under `RequestProject/Spine/**` is self-contained.
The historical trees `RequestProject/Experiment1/**` and `RequestProject/Experiment2/**` can
be deleted from the source tree without changing or breaking any theorem of the Spine; this
was verified by an isolated clean build with both trees removed (§7).

```
Spine direct legacy imports:
Experiment1 = 0
Experiment2 = 0

Spine transitive legacy imports:
Experiment1 = 0
Experiment2 = 0
```

The same holds separately for every principal endpoint (§5).

---

## 1. What the defect was

Before this refactoring the only remaining arrow from the new code into the old code was

```
Spine.E2.Model.CertifiedProjection  →  Experiment2.NullSectorTask23.Task23  →  ≈180 legacy modules
```

`CertifiedProjection` packaged the historical Task-23 two-to-one projection as a term of the
generic interface `NullSectorTask28.InternalProjection`, and `Spine.E2.Model.ModelBridge`
transported it onto the visible model group as `ModelBridge.modelInternalProjection`.  Because
the E2 chain is linear (`Family → Topology → Lift → Model → Descent → Global → Defect →
AtlasChange → Core`), that single import put the whole legacy chain into the closure of every
later module, and roughly thirty statements in the Descent/Defect/AtlasChange layers were
*specializations* of generic theorems at `modelInternalProjection`.

## 2. What was done

1. **The concrete legacy projection was deleted** from the production graph:
   `Spine/E2/Model/CertifiedProjection.lean` and `Spine/E2/Model/ModelBridge.lean` are gone,
   and with them the `Spine/E2/Model/` directory.
2. **The generic content of that directory was moved into the Lift layer**
   (`git mv`, so the provenance is in the git history):
   `Model/InternalTransitionInterface.lean → Lift/TransitionSystem.lean`,
   `Model/Task28.lean → Lift/LiftLevels.lean`.  Both now import only the generic
   `Lift/RepresentativeChange.lean` chain.
3. **Every inherited specialization was either generalized or removed.**  Definitions that
   were phrased through the legacy projection (`OrdinaryInternalLiftable`,
   `UniversalInternalLiftability`, `DirectAtlasLiftable`, `FamilyLiftable`,
   `RefinementLiftable`, `FamilyKernelDefectNeutral`, `UniversalFamilyLiftability`) now take
   an internal projection `P` as a parameter; the theorems about them were reproved in that
   generality.  Pure specializations that added nothing (`task29_inherited_*`,
   `task28_ordinary_*`) were deleted rather than migrated.
4. **The negative mechanism was made generic.**  The historical impossibility argument used
   the concrete cover's "no global section" theorem.  The generic replacement is
   `NullSectorTask31.tautSystem` (the tautological two-chart transition system of a
   topological group) together with `tautSystem_not_internalLiftable`: *whenever* the internal
   projection has no continuous internal representative of the identity over the whole group,
   the tautological system is not liftable.  The GvisModel-valued examples (`badSystem`,
   `badFamily`) were kept and their non-liftability restated under the same hypothesis.
5. **A native model was built** so that the interface and the conditional hypotheses are
   demonstrably non-vacuous (§4).
6. **The controls were moved under `Spine/Controls/**`** and rebuilt against the generic
   interfaces; production never imports them (checked mechanically).
7. **Legacy-facing bridge modules were removed** from the active project: the three modules
   of `RequestProject/Comparison/` (E1 Hermitian comparison, E2 one-fibre comparison, E2
   Task-26 endpoint) existed only to expose historical declarations and are therefore deleted
   (recoverable from git history).
8. **The build was split.**  `lake build` now builds the new project only; the historical
   trees are a separate, non-default Lake library `LegacyProvenance`.

## 3. Provenance table

Migration classes: `RECONSTRUCTED_NATIVE`, `GENERALIZED_NATIVE`,
`REPLACED_BY_GENERIC_INTERFACE`, `CONTROL_REBUILT_NATIVE`, `NOT_REQUIRED`, `SUPERSEDED`.

| New declaration / module | Historical origin | Migration type |
| --- | --- | --- |
| `NullSectorTask28.TransitionSystem`, `InternalTransitionCandidate`, `candidateOfSystem` (now `Spine/E2/Lift/TransitionSystem.lean`) | Experiment 2, Task 28 interface layer (via `Spine/E2/Model/InternalTransitionInterface.lean`) | GENERALIZED_NATIVE (moved out of the model layer; imports only the generic lift chain) |
| `NullSectorTask28.level_A_…`, `level_B_…`, `LevelC`, `CanTrivialiseSimultaneously` (now `Spine/E2/Lift/LiftLevels.lean`) | Experiment 2, Task 28 endpoints | GENERALIZED_NATIVE |
| `NullSectorTask28.Certified.certifiedInternalProjection` | Experiment 2, Task 23 certified projection | REPLACED_BY_GENERIC_INTERFACE (production now quantifies over `InternalProjection`) |
| `NullSectorTask28.Certified.no_whole_domain_internal_rep` | Experiment 2, Task 23/28 no-global-section theorem | REPLACED_BY_GENERIC_INTERFACE — the hypothesis `¬ P.HasContinuousInternalRep id univ`; witnessed natively by `SpineControls.circleDoubleCover_no_whole_domain_rep` |
| `NullSectorTask28.ModelBridge.modelInternalProjection` | Experiment 2, Task 21/23/26 bridge | REPLACED_BY_GENERIC_INTERFACE |
| `NullSectorTask28.ModelBridge.gvisMulEquiv`, `so3ToModel`, `matOfModel`, `isomOfMat`, `transport` | Experiment 2, Task 21/26 | NOT_REQUIRED (they existed only to read the legacy projection over the model group) |
| `NullSectorTask28.task28_ordinary_transition_locally_representable`, `task28_ordinary_internal_candidate_exists`, `task29_inherited_*` | Experiment 2, Tasks 28–29 inherited sections | NOT_REQUIRED (pure specializations of generic theorems that remain) |
| `NullSectorTask31.OrdinaryInternalLiftable`, `UniversalInternalLiftability`, `not_universalInternalLiftability`, `exists_ordinary_system_(not_)internalLiftable`, `internalLiftability_is_genuinely_global`, `spatialClosureVerdict_justified` | Experiment 2, Task 31 | GENERALIZED_NATIVE (projection is a parameter; the negative half carries the explicit no-global-section hypothesis) |
| `NullSectorTask31.tautSystem`, `tautTrans`, `tautSystem_not_internalLiftable` | new; generalizes the Task-31 `badSystem` argument | RECONSTRUCTED_NATIVE |
| `NullSectorTask31.Examples.badSystem`, `goodSystem`, `badFamily` | Experiment 2, Task 31 examples (already native in the Spine) | GENERALIZED_NATIVE (statements now conditional on `P`) |
| `NullSectorTask32.DirectAtlasLiftable`, `FamilyLiftable`, `RefinementLiftable`, `FamilyKernelDefectNeutral`, `familyLiftable_iff_familyKernelDefectNeutral`, `task32_verdictC_classification`, `task32_family_level_classification` | Experiment 2, Task 32 | GENERALIZED_NATIVE |
| `SpineControls.trivialDoubleCover` (split cover `G × ℤ/2 → G`) | new | RECONSTRUCTED_NATIVE (positive control: the interface is inhabited) |
| `SpineControls.circleDoubleCover`, `circle_no_global_section`, `circleDoubleCover_no_whole_domain_rep` | new; replaces the historical Task-23 cover as the *witness* that the theory is non-vacuous | RECONSTRUCTED_NATIVE |
| `SpineControls.circle_taut_not_liftable`, `circle_trivial_liftable`, `liftability_is_genuinely_global_native`, `circle_taut_defect_not_neutral` | replaces the historical local-vs-global liftability control | CONTROL_REBUILT_NATIVE |
| `NullSectorTask32.GoodBad.*` (good/bad atlas), `NullSectorTask32.task32_closure`, `presentationLevel_nonNeutral_with_familyLevel_neutral` (now `Spine/Controls/E2/`) | Experiment 2, Task 32 controls | CONTROL_REBUILT_NATIVE (parameterized by `P`; no legacy import) |
| `Counterexample.*` descent control (`Spine/Controls/E2/DescentCounterexample.lean`) | Experiment 2, Task 29 control | CONTROL_REBUILT_NATIVE (was already legacy-free; only relocated) |
| `RequestProject/Comparison/E1Hermitian.lean`, `E2OneFibreComparison.lean`, `E2Task26Endpoint.lean` | Experiment 1 `SpinFinal`/`Task9Freeze`, Experiment 2 Tasks 24–26 | SUPERSEDED — deleted; they were adapters into the historical trees and are forbidden by the zero-legacy rule |
| Everything else under `Experiment1/**`, `Experiment2/**` | — | NOT_REQUIRED (kept as historical provenance, built only by the non-default `LegacyProvenance` library) |

The E1 half required no migration: it was already legacy-free, and the mechanical audit
confirms this for `Spine.E1.Core`, `Spine.E1.SL2Comparison` and every module of the intrinsic
chain `LorentzCarrier → LorentzQuadratic → LorentzClifford → SpinGroup → spinCover →
SpinKernel`.

## 4. The native model (controls)

`RequestProject/Spine/Controls/CircleDoubleCover.lean` builds two instances of the generic
interface from Mathlib alone:

* `trivialDoubleCover G : InternalProjection (G × ℤ/2) G` for every topological group `G` —
  continuous, surjective, globally sectioned, kernel two-element central and discrete;
* `circleDoubleCover : InternalProjection Circle Circle`, the squaring map `z ↦ z²`:
  surjectivity from `Circle.exp`, continuous local sections from Mathlib's covering-map
  theorem for the power maps of the circle, kernel `{±1}` central and (being finite in a
  Hausdorff group) discrete.

`circle_no_global_section` proves that the second has **no** global continuous section: if `s`
were one, `f z = s(z²)·z⁻¹` is continuous with `f z² = 1`, hence takes values in the two-point
set `{1, −1}`; the circle is preconnected, so `f` is constant; comparing `f 1 = s 1` with
`f(−1) = s 1 · (−1)` gives `−1 = 1`.

`RequestProject/Spine/Controls/E2/NativeLiftControl.lean` uses these to obtain unconditional,
fully native controls, labelled in the source as `CONTROL`, `NEGATIVE CONTROL`,
`COUNTEREXAMPLE` and `REGRESSION TEST`.

## 5. Import audit (direct and transitive)

Produced by `python3 scripts/legacy_audit.py` (source-level) and by
`RequestProject.Spine.Audit.Firewall` (environment-level, part of the build).

```
Spine modules: 100
Spine LOC    : 20686

Spine direct legacy imports:      Experiment1 = 0   Experiment2 = 0
Spine transitive legacy imports:  Experiment1 = 0   Experiment2 = 0

endpoint                                              direct  closure   E1   E2
RequestProject.Spine.Core                                  3       91    0    0
RequestProject.Spine.E1.Core                               2       22    0    0
RequestProject.Spine.E1.SL2Comparison                      2       22    0    0
RequestProject.Spine.E2.Core                               1       65    0    0
RequestProject.Spine.E2.Topology.Task27                    1       16    0    0
RequestProject.Spine.E2.Descent.Task29                     1       34    0    0
RequestProject.Spine.E2.Global.Task30                      1       46    0    0
RequestProject.Spine.E2.Defect.Task31                      1       56    0    0
RequestProject.Spine.E2.AtlasChange.Task32                 1       64    0    0
RequestProject.Spine.Audit.Firewall                       14       98    0    0
RequestProject.Spine.Controls.CircleDoubleCover            1       20    0    0
RequestProject.Spine.Controls.E2.NativeLiftControl         2       53    0    0
RequestProject.Spine.Controls.E2.GoodBadAtlas              1       62    0    0
RequestProject.Spine.Controls.E2.FamilyDefectControl       2       66    0    0
RequestProject.Spine.Controls.E2.DescentCounterexample     1       28    0    0

RESULT: PASS
```

The Lean-level audit additionally reports `SPINE FIREWALL AUDIT: all checks passed` and fails
the build on any violation.  It checks, from the compiled environment (so aliases, re-exports
and cached artifacts cannot hide anything):

1. every module under `RequestProject.Spine` — direct imports **and** transitive closure —
   against `RequestProject.Experiment1` / `RequestProject.Experiment2`;
2. the same per endpoint, with the summary above;
3. no production module reaches `RequestProject.Spine.Controls`;
4. layer order: the intrinsic E1 spin core reaches neither `SL2Comparison` nor the matrix
   model / Pauli representation / Weyl module nor any E2 module; the E2 foundations
   (`Family`, `Topology`, `CentralDoubleCover`) reach none of `Lift`, `Descent`, `Defect`,
   `Global`, `AtlasChange`;
5. proof-closure: the dependency closure of statement *and* proof of each principal endpoint
   avoids the removed historical constants and the control-only constants.

Sensitivity is pinned by positive controls (the controls *do* import production, the
comparison layer *does* sit above `SpinKernel`, `task32_closure` *does* depend on the good/bad
atlas), by a lower bound on the number of audited modules, and by `requireModule`, which
rejects any audited module absent from the environment.

## 6. Before/after statistics

| Figure | before | after |
| --- | ---: | ---: |
| new-project modules (`Spine/**`) | 96 | 100 |
| new-project LOC (`Spine/**`) | 20 346 | 20 686 |
| modules of the active (default) build target | 323 (whole tree, incl. 486 legacy files as part of the same library) | 102 (`Spine/**`, `Main`, `CombinedDemo`) |
| `Spine.E1.Core` project-local closure | 22 (0 legacy) | 22 (0 legacy) |
| `Spine.E1.SL2Comparison` project-local closure | 22 (0 legacy) | 22 (0 legacy) |
| `Spine.E2.Core` project-local closure | 247 (**180 legacy**) | **65 (0 legacy)** |
| `Spine.E2.Descent.Task29` closure | 216 (180 legacy) | 34 (0) |
| `Spine.E2.Global.Task30` closure | 228 (180 legacy) | 46 (0) |
| `Spine.E2.Defect.Task31` closure | 238 (180 legacy) | 56 (0) |
| `Spine.E2.AtlasChange.Task32` closure | 246 (180 legacy) | 64 (0) |
| `Spine.Audit.Firewall` closure | 320 (26 + 193 legacy) | 98 (0) |
| `Spine.Core` aggregate endpoint | did not exist | 91 (0 legacy) |

Module changes: `Spine/E2/Model/` (4 modules) removed, of which 2 were moved into
`Spine/E2/Lift/` and 2 deleted; `RequestProject/Comparison/` (3 modules) deleted;
`RequestProject/Control/E2/` (3 modules) moved to `Spine/Controls/E2/`; new modules
`Spine/Core.lean`, `Spine/Controls/CircleDoubleCover.lean`,
`Spine/Controls/E2/NativeLiftControl.lean`.

Build times (this machine, 8 cores; Mathlib already built):

* incremental `lake build` after a leaf-module edit: ≈ 20–30 s;
* full `lake build` of the new project from a clean build directory: 20m51s / 102 project
  modules (measured in the isolated copy of §7, Mathlib prebuilt);
* `lake build LegacyProvenance` (the 486 historical files, provenance only): ≈ 25 min.

Cold Lake job counts are not reported as a complexity measure: they are dominated by Mathlib.

## 7. Isolated build with the historical trees removed

```
cp -a RequestProject scripts lakefile.toml lean-toolchain lake-manifest.json /tmp/iso/
cp -al .lake/packages /tmp/iso/.lake/packages      # dependencies only, no build artifacts
cd /tmp/iso
rm -rf RequestProject/Experiment1 RequestProject/Experiment2
find . -name '*.olean' -not -path './.lake/packages/*' | wc -l     # 0 — no stale artifacts
lake build
```

Result: `Build completed successfully (8128 jobs)` in `20m51s` (Mathlib was already compiled;
all 102 project modules were compiled from scratch), including
`SPINE FIREWALL AUDIT: all checks passed`; `python3 scripts/legacy_audit.py` in the isolated
copy reports `RESULT: PASS`.  The build log contains no occurrence of `sorry`, and the 387
`#print axioms` lines it emits all report exactly `propext, Classical.choice, Quot.sound`.  The build directory of the project was empty at the start, so no
cached `.olean` of a legacy module could mask a dependency.  The provenance repository was not
modified: the test is a copy.

## 8. Axiom audit

Every principal endpoint carries a `#print axioms` line in its own module; all of them report
exactly

```
[propext, Classical.choice, Quot.sound]
```

A repository-wide search confirms that `Spine/**` contains no `sorry`, no `admit`, no `axiom`
declaration, no `@[implemented_by]`, no `native_decide` and no `bv_decide`.

## 9. Fail-build / repair ledger

| # | Declaration / module | Error | Diagnosis | Repair | Status |
| --- | --- | --- | --- | --- | --- |
| 1 | `Spine.E2.AtlasChange.FamilyLiftability` | `Unknown identifier ModelBridge.modelInternalProjection`; application type mismatch on `ordinarySystem A` | the atlas layer still used the deleted legacy projection, and `OrdinaryInternalLiftable` had gained a projection parameter | added `(P : InternalProjection L GvisModel)` to the section and threaded it through `DirectAtlasLiftable`, `FamilyLiftable`, `RefinementLiftable` | fixed, green |
| 2 | `Spine.E2.Defect.Task31` | `Unknown constant exists_inherited_ordinary_system_not_internalLiftable` (and two siblings) | the endpoint aliases still referred to the pre-generalization names | renamed the aliases to the new `exists_ordinary_system_…` / `exists_frame_family_…` | fixed, green |
| 3 | `Spine.Controls.CircleDoubleCover` | `Invalid field HasContinuousInternalRep` | the predicate lives in the Lift layer, not in `CentralDoubleCover` | import `Spine.E2.Lift.LocalInternalRepresentatives` | fixed, green |
| 4 | `Spine.Controls.CircleDoubleCover` | `Unknown constant IsClopen.eq_empty_or_univ`, `Unknown identifier mul_right_eq_self` | guessed Mathlib names | `isClopen_iff.mp`; explicit `mul_left_cancel` | fixed, green |
| 5 | `Spine.Controls.CircleDoubleCover` | `simp made no progress` in the kernel-discreteness proof | the hand-rolled open-set argument was the wrong shape | replaced by `DiscreteTopology.of_continuous_injective` through the second projection | fixed, green |
| 6 | `Spine.Controls.E2.NativeLiftControl` | `failed to compile definition … depends on Circle.instCommGroup` | a `def` over `Circle` is noncomputable | marked `noncomputable` | fixed, green |
| 7 | `Spine.E2.Defect.LiftabilityPredicate` | linter: unused section variables in `tautTrans_*` | the pure-algebra lemmas do not use the topology instances | `omit [TopologicalSpace G] [IsTopologicalGroup G] in` | fixed, green |
| 8 | `Spine.Audit.Firewall` | build did not terminate within 10 min | the closure routine looked each module up by linear search in the ~5000-entry module table, per visited node | build the module-name → index map once and reuse it | fixed, audit now runs in seconds |
| 9 | `RequestProject.CombinedDemo` | application type mismatch on `FamilyLiftable F` | the smoke test used the pre-generalization signature | added the projection parameter | fixed, green |

No mathematical statement was weakened to avoid a repair; where a statement could no longer be
proved unconditionally after removing the legacy witness (the negative examples), the missing
input is now an explicit, clearly stated hypothesis on `P`, and it is discharged natively in
the controls for the circle cover.

## 10. What is deliberately *not* done

The bridge `InternalProjection SpinGroup GLor` is not attempted: no topological group
structure on the Clifford carrier, no continuity of `spinCover`, no discreteness statement for
its kernel in a topology, no local continuous sections, no frame bundles, no `w₁`, no `w₂`, no
spin structures, spinor bundles or connections.  The purpose of this task was to make sure
that, when those theorems are attempted, they are built on a completely independent codebase.
