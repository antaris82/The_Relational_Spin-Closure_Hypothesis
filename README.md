This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Spin-reconstruction spine (merged project)

This Lean 4 project holds the **active proof spine** for a single long-term target:
reconstructing, with kernel-checked Lean proofs, the dependency chain required for
Lorentzian spin geometry

```
derived Lorentz quadratic structure -> Clifford algebra -> Spin group and its double cover
  -> Lorentzian tangent/frame geometry -> manifold orientation and time orientation
  -> global Spin lift and its obstruction -> spinor bundle -> lifted spin connection
```

It was assembled from two independent upstream experiments, which are now **frozen
historical provenance**: no module of `RequestProject/Spine/**` imports, re-exports or
transitively reaches any module of `RequestProject/Experiment1/**` or
`RequestProject/Experiment2/**`, and the two trees can be deleted without breaking any
theorem of the Spine (verified by an isolated clean build; see `LEGACY_DECOUPLING_AUDIT.md`).
They remain separately documented in their own repositories:

| Upstream | Mathematical project | Project identifier / branch |
| --- | --- | --- |
| Experiment 1 | *Intrinsic Branching from a Derived Lorentz Structure* | `Split-Complex-Lorentzian_Kinematics` / `Intrinsic-Branching-from-a-Derived-Lorentz-Structure` |
| Experiment 2 | *Split Complex Lorentzian Dynamics* | `Split-Complex_Lorentz_Dynamics` / `main` |

## Layout

```
RequestProject/Spine/**            the new, self-contained project (Mathlib + Spine only)
RequestProject/Spine/Controls/**   native controls / counterexamples / regression tests
RequestProject/Spine/Audit/**      the mechanical import and layering firewall
RequestProject/Experiment1/**      historical provenance only — nothing in Spine imports it
RequestProject/Experiment2/**      historical provenance only — nothing in Spine imports it
```

Principal endpoints:

| Endpoint | What it gives |
| --- | --- |
| `RequestProject.Spine.E1.Core` | intrinsic Lorentz quadratic form, Clifford algebra, intrinsic spin group, `Spin -> Lorentz` surjective with kernel exactly `{±1}`, Clifford modules and the Weyl module |
| `RequestProject.Spine.E1.Topology.Core` | the topological qualification of the intrinsic double cover: `SpinGroup` and `GLor` are Hausdorff topological groups, `spinCover` is continuous and surjective, its `{±1}` kernel is central and discrete (see `TASK01_AUDIT.md`), and it admits **continuous local sections** around every point of `GLor`, with a two-sheet decomposition over an explicit identity neighbourhood (see `TASK02_AUDIT.md`) |
| `RequestProject.Spine.E2.SpinProjection` | the native instance `SpinCore.internalSpinProjection` of the generic central-cover interface `InternalProjection SpinGroup GLor`, built only from the intrinsic results above |
| `RequestProject.Spine.E2.SpinProjectionIntegration` | integration test: the generic lift theory consumes the native spin projection (local internal representatives, kernel ambiguity, Level-B candidates, kernel-valued locally constant triple-overlap defect) |
| `RequestProject.Spine.E1.SL2Comparison` | the proved isomorphism of the intrinsic spin group with `SL(2,ℂ)` |
| `RequestProject.Spine.E2.Core` | varying metric/oriented rank-three family, frames and transitions, generic central double-cover lift layer, triple-overlap defect, descent, and the family-level liftability classification |
| `RequestProject.Spine.Core` | the aggregate endpoint of the whole new project |
| `RequestProject.Spine.Controls.CircleDoubleCover` | native central double covers: the split cover `G × ℤ/2 → G` and the circle squaring cover, which has continuous local sections but no global one |
| `RequestProject.Spine.Controls.E2.NativeLiftControl` | native controls: local vs global liftability, presentation-dependent vs family-level defect |
| `RequestProject.Spine.Audit.Firewall` | the mechanical import/declaration firewall audit |

The intrinsic carrier is `SpinCore.LorentzCarrier`; the upstream name `Task9.Spin` is not
exposed by the new API.

## Documents

| File | Contents |
| --- | --- |
| `ARCHITECTURE.md` | the layering, the firewall rules, module-by-module description, and the explicit non-claims |
| `PROVENANCE_LEDGER.md` | every module removed from the active tree, with classification and reason |
| `DEPENDENCY_DAG.md` | before/after DAG statistics and the exact transitive closure of every principal endpoint |
| `REFACTOR_AUDIT.md` | the refactoring record: build results, failed builds with diagnosis and repair, axiom audit |
| `SPIN_CORE_EXTRACTION_AUDIT.md` | the intrinsic Spin double-cover extraction: new layering, provenance of moved declarations, import firewall, before/after dependency statistics, axiom audit, and the interface table for the generic lift machinery |
| `LEGACY_DECOUPLING_AUDIT.md` | the complete legacy decoupling: migration provenance table, import audit, before/after statistics, axiom audit, fail/repair ledger, and the isolated build with both historical trees removed |
| `TASK02_AUDIT.md` | continuous local sections of the intrinsic Spin cover: the E1 → E2 gap audit, the route classification, the identity-neighbourhood argument, the local two-sheet statement, the canonicality table, the native `InternalProjection`, the E2 integration test, the failbuild ledger, build evidence and the axiom audit |
| `COMBINED_PROJECT_PROVENANCE.md`, `NAMING_NORMALIZATION_AUDIT.md` | provenance of the original merge and of the experiment renaming |

## Discipline

No `sorry`, no `admit`, no `axiom` declaration, no `@[implemented_by]`, no `native_decide`.
Every principal endpoint carries a `#print axioms` line and reports only `propext`,
`Classical.choice`, `Quot.sound`.

## What is deliberately not claimed

No project defect is called `w₁` or `w₂`; the experiment-2 rank-three oriented family is
not the tangent bundle of a Lorentzian manifold, so its kernel-valued defect is *not*
identified with the second Stiefel–Whitney class.  No manifold orientation, global spin
structure, spinor bundle over a manifold or spin connection is constructed yet.

## Build

```
lake build                     # the new project only: Spine/**, Main, CombinedDemo
lake build LegacyProvenance    # the historical experiment trees (provenance only)
python3 scripts/legacy_audit.py   # source-level zero-legacy audit and statistics
```

The build of the new project includes the mechanical firewall
(`RequestProject.Spine.Audit.Firewall`), which fails the build if any Spine module reaches a
historical module, if a production module imports a control, or if the layer order is
violated.

## Task 10 — geometric comparison: status

The canonical map `NerveGeom.geometricHmap 𝓤 n : Hⁿ_sing(|N(𝓤)|;ℤ₂) → Ȟⁿ(𝓤;ℤ₂)` is **not**
proved bijective.  What Task 10 establishes:

* the Task-9 chain map is *exactly* the linearised adjunction unit `C_*(η : N(𝓤) → Sing|N(𝓤)|)`
  (`NerveGeom.chainMap_eq_unitChainMap`);
* transposition of `ℤ₂`-chain maps is explicit and exact, and carries the Task-9 chain data onto
  the existing cochain complexes (`NerveGeom.dualOf_simpBoundary`, `dualOf_singBoundary`,
  `dualOf_chainMap`);
* **a chain-homotopy inverse for that canonical chain map makes `geometricHmap 𝓤 n` bijective in
  every degree** (`NerveGeom.geometricHmap_bijective_of_chainHomotopyEquiv`), with no universal
  coefficient theorem and no finiteness assumption;
* so the single remaining blocker is the chain-level statement
  `NerveGeom.ChainComparisonStatement`;
* and the Task-9 claim that the Task-4 manifold layer supplies second countability /
  paracompactness is withdrawn and refuted (`SpineTask10.not_secondCountable_of_charted`).

The nerve theorem `|N(𝓤)| ≃ M` was deliberately not touched.  Full analysis, pinned-Mathlib
capability audit and route matrix: `TASK10_AUDIT.md`.

The route to that blocker has since been narrowed twice.  Current upstream Mathlib supplies no
shortening (`TASK11_UPSTREAM_DELTA_AUDIT.md`), and the Acyclic-Models route is now **closed by
proof**: the simplicial chain functor is free and acyclic on the standard-simplex models, but
the singular chain functor of the realisation is *not* free on them — nor on any countable class
of models with finitely many vertices — and finite simplicial sets are not even an acyclic model
class (`∂Δ[2]` has a mod-2 `1`-cycle that is not a boundary).  Acyclic Models therefore only
reproduces the comparison map the project already has.  The selected successor route is the
skeletal/cellular comparison.  Audit, matrices, counterexamples and the successor dependency
graph: `TASK12_ACYCLIC_MODELS_APPLICABILITY.md`; the formal probes are
`RequestProject/Spine/Nerve/Task12Probe.lean`.

## Task 13 — normalization and the skeletal route: status

The skeletal route selected by Task 12 needs degeneracy control before any cellular argument
can start, and Task 13 supplies it, unconditionally and in Lean
(`RequestProject/Spine/Nerve/Task13Normalization.lean`,
`Task13Skeletal.lean`, `Task13CanonicalMap.lean`, `Task13PinAudit.lean`, all `sorry`-free):

* the project's **unnormalized** simplicial `ℤ₂`-chain complex of any simplicial set is
  **chain-homotopy equivalent** to its normalized quotient `N_* = C_*/D_*`, with an explicit
  projection `p`, section `i` (`p ∘ i = id`) and homotopy (`∂h + h∂ = id + i∘p`), all natural
  in the simplicial set;
* `D_q` is *exactly* the chains supported on degenerate simplices, so `N_q` is free on the
  **nondegenerate** `q`-simplices;
* for the skeletal pair, `N_q(K^{(r)},K^{(r-1)}) = 0` for every `q ≠ r`, and
  `N_r(K^{(r)},K^{(r-1)})` is free on the nondegenerate `r`-simplices;
* the canonical comparison `J = C_*(η_K)` respects degeneracies and descends to the normalized
  complexes — no new map is introduced.

The comparison to singular homology is **still blocked**, now at a precisely identified
topological theorem: pinned Mathlib has no relative singular homology and, decisively, **no
excision** — hence no `H_*(|Δ^r|,|∂Δ^r|)` and no cell-attachment decomposition of `|K^{(r)}|`.
The algebraic bridge `quasi-iso ⇒ chain-homotopy equivalence` over `ℤ₂` is *not* in the pin
either, but is derivable from its K-projective machinery; that is the selected bridge (A).
Full audit, DAG, classifications and evidence:
`TASK13_NORMALIZED_SKELETAL_COMPARISON.md`; failbuilds: `TASK13_FAILBUILDS.md`; sources:
`TASK13_EXTERNAL_SOURCES.md`.

## Task 15 — standard-cell pair, realization monomorphisms, relative comparison

Outcome: **`F` — precise remaining blocker**, with more proved than in Task 14.

* **WP1 closed.** The concrete skeletal attachment square is now an actual
  `CategoryTheory.IsPushout` (`SpineTask15.skeletalIsPushout`), and its realization is a
  topological pushout, both in the raw form and with the honest coproducts
  `∐_σ |∂Δ[r]| → |K^{(r-1)}|`, `∐_σ |Δ[r]| → |K^{(r)}|`
  (`skeletalIsPushout_toTop`, `skeletalIsPushout_toTop_coprod`).
* **WP3 reduced to one statement.** `realization_skInc_injective`: injectivity of
  `|K^{(r-1)}| → |K^{(r)}|` for *every* simplicial set follows from injectivity of
  `|∂Δ[r]| → |Δ[r]|` alone; proved via the realized pushout, coproducts of injections, and
  adhesiveness of `Type`.  The case `r = 0` is proved outright.
* **WP12 base case closed and the induction assembled.** `baseCase` is unconditional;
  `skeletalInduction` and `finiteDimensional_homologyIso` prove that `J = C_*(η_K)` is a
  homology isomorphism for every finite-dimensional `K`, conditional on exactly two explicitly
  carried hypotheses (`StandardCellMono` and `RelJIsIso`).
* **Not proved:** the standard-cell homology theorem with its generator (B1), the excision
  decomposition, `H(J^rel)` iso (B3), and the cohomology bridge.  `geometricHmap` is still not
  proved bijective.
* The Task-14 phrase "full excision is genuinely required" is withdrawn; see the correction
  section in `TASK14_SPECIALIZED_CELL_ATTACHMENT.md` and `TASK15_AUDIT.md`.

## Task 34 — the tangent/solder coupling gate: status

**Outcome B.**  The certified bottom-up data (smooth emergent 4-manifold + emergent Spin
seed) do **not** determine a coupling between the tangent geometry and the internal Lorentz
structure; exactly one additional datum does, and with it the gate closes.

* **The genuine tangent transitions of the emergent manifold** are computed for the *actual*
  Task-32/33 atlas: `(tangentBundleCore …).coordChange` equals the derivative `D(φ_ij)` of the
  base-gluing primitive's identification map
  (`EmergentBase.BaseGluingData.tangentTransition_eq_derivative_baseTransition`,
  `RequestProject/Spine/Emergent/TangentTransition.lean`).
* **The internal Lorentz transition** of an emergent Spin seed acts on the four-dimensional
  local model through the native group `GLor` — no external `SO(1,3)`
  (`SpinNative.projectedLorentzTransition`, `RequestProject/Spine/Solder/InternalLorentz.lean`).
* **They are independent.**  An explicit smooth two-chart base gluing with `φ₀₁(v) = 2·v`,
  paired with the pointwise trivial Spin datum, has identity internal Lorentz transition and
  tangent transition `2·id`
  (`SpinNative.tangent_spin_base_data_do_not_force_transition_identification`).  This is
  non-derivability, **not** non-existence: the same base still carries a compatible solder
  field.
* **The missing datum** is `SpinNative.TangentSolderData`: fibrewise linear equivalences
  `LocalModel ≃ₗ[ℝ] T_x M` whose overlap law is exactly the projected Lorentz transition.
  From it follow the tangent Lorentz metric and its chart-independence, four-dimensionality,
  isometry of every solder frame, a derived orientation and time orientation, genuine
  `LorentzFrames.LorentzTangentFrameData`, the equality of its frame cocycle with the
  projected native Lorentz cocycle, and a native Spin lift of that cocycle
  (`RequestProject/Spine/Solder/Solder.lean`,
  `RequestProject/Spine/Comparison/SolderTangentGate.lean`).
* **Not canonical:** the compatible solder fields form a torsor under pointwise tangent
  automorphism fields (`TangentSolderData.exists_gauge`, `not_unique`).
* **Not claimed:** `w₁(TM)`, `w₂(TM)`, connections, curvature, torsion, dynamics; and no
  topological bundle isomorphism `InternalLorentzBundle ≃ TangentBundle`, because the solder
  datum deliberately carries no frame regularity (`TASK34_AUDIT.md` §4).
* The type-level identity `TangentSpace localModelI x = LocalModel` is recorded as an
  implementation artefact and is never used as a coupling proof (`TASK34_AUDIT.md` §2).

Reports: `TASK34_PROVENANCE.md`, `TASK34_AUDIT.md`, `TASK34_CODE_HYGIENE.md`,
`TASK34_FAILBUILDS.md`, `TASK34_DOCUMENTATION_REPAIR.md` (the repository-wide terminology
audit and the Task-32/33 corrections, with historical provenance preserved).

## Task 35 — the smooth solder / bundle-equivalence gate: status

**The Task-34 wording above is corrected.**  What Task 34 proved is that *direct/raw transition
identification is not forced*, and that the **fibrewise/algebraic** solder gate closes; the
**topological/smooth** solder gate was left open.  That gate is what Task 35 closes.

* **The decisive question is answered, as a theorem.**  A regular solder datum exists **iff**
  there is a bundle-level equivalence of the internal Lorentz bundle with the genuine tangent
  bundle of the emergent manifold: `SpinNative.smooth_solder_iff_regular_bundle_equivalence`
  (`RequestProject/Spine/Solder/BundleEquivalence.lean`).  No further geometric primitive is
  hidden between the two notions.
* **The regular datum** is `SpinNative.SmoothTangentSolderData` — local on the cover, a `C^∞`
  family `A i : LocalModel → (LocalModel ≃L[ℝ] LocalModel)` on each piece, with the exact
  intertwining square between the internal `coordChange`, `A i / A j` and the genuine tangent
  `coordChange = D(φ_ij)` (`RequestProject/Spine/Solder/RegularSolder.lean`).
* **The weak Task-34 datum is strictly weaker:** `SpinNative.weak_solder_not_regular` exhibits a
  valid weak solder whose representative — and whose fibrewise metric coefficient — is
  discontinuous in the actual chart (`RequestProject/Spine/Solder/WeakInsufficiency.lean`).
* **The metric is smooth:** symmetry, nondegeneracy, signature `(1,3)`, the tensor law across
  charts, and `C^∞` coefficient functions (`RequestProject/Spine/Solder/SmoothMetric.lean`).
* **Orientation and time orientation:** the reductions are derived and each chart carries a
  `C^∞` future-directed unit timelike field; a *global* smooth representative is classified as
  an additional theorem, with the exact gluing criterion proved
  (`RequestProject/Spine/Solder/OrientationTime.lean`).
* **Gauge freedom:** regular solder data form a genuine torsor under `C^∞` tangent-bundle
  automorphism fields — transitivity *and* freeness proved
  (`RequestProject/Spine/Solder/RegularGauge.lean`).
* **Spin endpoint:** classified as a **topological** Spin lift, not a smooth `Spin(TM)`; the
  missing datum is named exactly (a smooth local section of the intrinsic spin cover).
* **Principal certificate:**
  `SpinNative.SmoothTangentSolderData.smooth_solder_tangent_certificate`
  (`RequestProject/Spine/Comparison/SmoothSolderGate.lean`).
* **Still not claimed:** `w₁(TM)`, `w₂(TM)`, Stiefel–Whitney classes, connections, curvature,
  torsion, dynamics, quantization; and no *smooth* total-space diffeomorphism.
  **Task-36 correction of the Task-35 wording (restated in Task 41):** the reason is an
  **infrastructure / packaging limitation** — the pinned library has no vector-bundle
  morphism/equivalence type — and *not* that the native Spin transition datum is only
  continuous.  A regular smooth solder already gives smooth local/projected Lorentz transition
  representatives; see `RequestProject/Spine/Task36/SmoothBundlePackaging.lean`.

Reports: `TASK35_PROVENANCE.md`, `TASK35_AUDIT.md`, `TASK35_CODE_HYGIENE.md`,
`TASK35_FAILBUILDS.md`.

## Task 37 — freeze refactor and the deformation-ready shared-transport interface

Task 36 is frozen: the adversarial import DAG was parallelised (the general layers no longer
depend on the loop models), the loop-specific time-orientation control moved to
`RequestProject/Spine/Task36/LoopTimeOrientation.lean`, the determinant-continuity lemma was
rebuilt on the project's explicit `Fin 4` coordinates (removing a `classical`), and the
loop-model wording was corrected to the exact proved terminology — **periodic fixed-cover loop
model**, **two-component periodic overlap**, **fixed-cover `ℤ₂` lift freedom**; no `S¹ × ℝ³`
homeomorphism and no `π₁` statement is claimed. Every Task-36 endpoint survives unchanged.

A new leaf branch `RequestProject/Spine/Deformation/` prepares — but does **not** run — the
next experiment:

* one shared native Spin-side transport state `transportState : ℝ → SpinGroup` with
  `transportState 0 = 1` and `transportState (a+b) = transportState a * transportState b`;
* the Lorentz side only ever as its projection, provably non-trivial for `λ ≠ 0`;
* the `λ`-deformed native Spin transition datum on the periodic fixed-cover loop model, whose
  `λ = 0` member **is** the frozen trivial seed and is regularly soldered;
* `RegularClosureSolution` / `RegularClosureAdmissible` — closure existence as the first
  observable — with proved anti-vacuity controls (closure can fail for all `λ`, and can hold
  exactly at `λ = 0`), so no universal existence theorem is possible;
* CONTROL A (fixed base) versus MAIN TEST B (co-varying base), and the `λ → 0±` / `λ → ±∞`
  regime vocabulary, with no regime decided.

No curvature, connection, holonomy or target geometry is introduced; connection and holonomy
remain **NOT FORMALIZED** and this is stated explicitly. See `TASK37_DEFORMATION_INTERFACE.md`
and `TASK38_SHARED_TRANSPORT_SMOKETEST_HANDOFF.md`.
