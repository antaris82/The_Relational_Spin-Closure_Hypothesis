# Architecture of the merged project after the spine extraction

The merged project has a single declared purpose: to reconstruct, with kernel-checked Lean
proofs, the dependency chain required for Lorentzian spin geometry

```
derived Lorentz quadratic structure -> Clifford algebra -> Spin group and its double cover
  -> Lorentzian tangent/frame geometry -> manifold orientation and time orientation
  -> global Spin lift and its obstruction -> spinor bundle -> lifted spin connection
```

The two upstream experiments are frozen historical provenance and remain independently
documented in their own repositories.  What is active in this tree is the **minimal proof
spine** extracted from the material they already proved, plus explicitly labelled
comparison endpoints and negative controls.

## Layers

The historical experiments are **provenance only**.  No module of `RequestProject.Spine`
imports, re-exports or transitively reaches any module of `RequestProject.Experiment1` or
`RequestProject.Experiment2`; the two trees can be deleted from the source tree without
breaking a single theorem of the Spine, and this is verified by an isolated clean build
(`LEGACY_DECOUPLING_AUDIT.md`, §7).

| Layer | Module root | Rule |
| --- | --- | --- |
| production core | `RequestProject.Spine.**` except `Spine.Controls.**` and `Spine.Audit.**` | may import `Mathlib` and other production `Spine` modules only |
| native controls | `RequestProject.Spine.Controls.**` | may import production modules and `Mathlib`; **no** production module may import them |
| audit | `RequestProject.Spine.Audit.Firewall` | imports every endpoint and every control in order to check them; nothing imports it |
| historical provenance | `RequestProject.Experiment1.**`, `RequestProject.Experiment2.**` | unreachable from the Spine; a separate, non-default Lake library `LegacyProvenance` |

`lake build` builds the new project only (`Spine/**`, `Main`, `CombinedDemo`).  The
historical trees are built, if wanted, by `lake build LegacyProvenance`.

These rules are enforced mechanically by `RequestProject/Spine/Audit/Firewall.lean`, which
fails to compile on any violation and which contains positive controls proving that the
audit is sensitive.  It checks, from the compiled environment:

1. **zero legacy** — direct imports and transitive closure of *every* Spine module, and of
   each principal endpoint separately, against the two historical prefixes;
2. **controls are downstream** — no production module reaches `Spine.Controls`;
3. **layer order** — the intrinsic experiment-1 spin core (level 1b) reaches neither the
   `SL(2,ℂ)` comparison layer, nor the complex matrix model and the Pauli representation,
   nor the Weyl-spinor module, nor any experiment-2 module; the experiment-2 foundations
   (`Family`, `Topology`, `CentralDoubleCover`) reach none of `Lift`, `Descent`, `Defect`,
   `Global`, `AtlasChange`;
4. **proof closure** — the statement-and-proof closure of each principal endpoint avoids the
   removed historical constants and the control-only constants.

A source-level counterpart that can be run without Lean is `scripts/legacy_audit.py`.  See
`DEPENDENCY_DAG.md` for the exact transitive closure of every principal endpoint and
`LEGACY_DECOUPLING_AUDIT.md` for the migration provenance table.

## Experiment-1 half: the intrinsic Lorentz / Clifford / Spin core

Namespace `SpinCore`.  Carrier `SpinCore.LorentzCarrier = ℝ × (Fin 3 → ℝ)`.  The upstream
name `Task9.Spin` is **not** exposed anywhere in the new API; the firewall audit checks
that the constant `Task9.Spin` does not occur in the closure of any production endpoint.

| Module | Content |
| --- | --- |
| `Spine.E1.Carrier` | the real spin factor, its Jordan product, trace, the **intrinsic Lorentz quadratic form** `NS`, its polarization `BS`, the square cone `ConeS`, real coordinates, the Jordan centroid.  Imports `Mathlib` only. |
| `Spine.E1.MatrixModel` | the `2×2` complex matrix pattern used as a *representation target* (`M2`, `hMat`, the Clifford relation `hMat_sq`, the centre of `M₂(ℂ)`).  Imports `Mathlib` only. |
| `Spine.E1.Clifford` | the real Clifford envelope `Cl3` of the Euclidean part |
| `Spine.E1.PauliRepresentation` | the faithful representation `rho : Cl3 ≃ₐ[ℝ] M₂(ℂ)` |
| `Spine.E1.LorentzGroup`, `Bivector`, `LieAlgebra`, `Hodge`, `Hyperbolic`, `Coords`, `ShellTransitivity`, `Shell` | the intrinsic Lorentz group `GLor`, the bivector/Hodge layer, the coordinate frame and determinant machinery, transitivity on the unit shell and the stabilizer |
| `Spine.E1.LorentzClifford`, `CliffordHodgeBridge` | the **Lorentz Clifford construction** `evenToCl3` from the universal property of the even Clifford algebra |
| `Spine.E1.CliffordMonomial` | the monomial frame of `Cl₃(ℝ)`, its faithfulness in the real `4 × 4` frame, and the **exact centre** `Z(Cl₃(ℝ)) = ℝ ⊕ ℝω` — all without any complex matrix |
| `Spine.E1.SpinElement` | the **predicate** layer: Clifford conjugation, `IsSpinElem`, the twisted action |
| `Spine.E1.SpinGroup` | the **bundled** intrinsic spin group `SpinGroup : Subgroup Cl3ˣ`, the unit constructor, and the central element `-1` |
| `Spine.E1.Paravector`, `SpinDeterminant`, `DoubleCover` | the action on the carrier, membership in `GLor`, and realisability of every element of `GLor` |
| `Spine.E1.SpinCover` | the **intrinsic homomorphism** `spinCover : SpinGroup →* GLor` and its surjectivity |
| `Spine.E1.SpinKernel` | the **exact kernel** `ker spinCover = {±1}`, its centrality and its order two; bundled endpoint `spin_double_cover` |
| `Spine.E1.Topology.FiniteDimTools` | generic finite-dimensional tools (Mathlib only): uniqueness of the Hausdorff vector-space topology, Hausdorffness of the module topology, the basis-evaluation criterion for continuity into a space of linear maps |
| `Spine.E1.Topology.CliffordTopology` | the **canonical topology of `Cl₃(ℝ)`** (the module topology), its monomial basis and finite dimensionality, `IsTopologicalRing`, `T2Space`, the homeomorphism with `ℝ⁸`, and the uniqueness statement |
| `Spine.E1.Topology.LorentzTopology` | the topology of the Lorentz target: module topology of `End(𝒮)`, its unit group, the canonical identification with the linear automorphism group, and the Hausdorff topological-group structure of `GLor` |
| `Spine.E1.Topology.SpinTopology` | the inherited Hausdorff topological-group structure of `SpinGroup` as a subgroup of `Cl₃(ℝ)ˣ` |
| `Spine.E1.Topology.SpinCoverTopology` | **continuity of `spinCover`** from the twisted Clifford action, discreteness of the `{±1}` kernel, and the package `TopologicalCentralCover` / `topologicalSpinProjection` |
| `Spine.E1.Topology.LocalSection` | **continuous local sections of `spinCover`** around every point of `GLor`, constructed natively by algebraic inversion of the twisted Clifford action (contraction operator, complex centre, discriminant, branch of the square root, transport by translation), plus the local two-sheet decomposition and the homeomorphism of a sheet onto the base neighbourhood |
| `Spine.E1.Topology.Core` | endpoint of the topological layer (`spin_double_cover_topological`, `spin_double_cover_local_sections`) + axiom audit |
| `Spine.E1.WeylSpinorModule` | Clifford modules over the carrier (`CliffordAction`) and the concrete `ℤ₂`-graded Weyl module |
| `Spine.E1.Core` | **principal production endpoint** + axiom audit |
| `Spine.E1.SL2Comparison` | **comparison only**: the proved isomorphism of the intrinsic spin group with `SL(2,ℂ)` and the compatibility of the two kernel descriptions.  It imports the intrinsic core; nothing in the intrinsic core imports it |

The Hermitian route (`Herm₂(ℂ)`, the Jordan-cone automorphism group, `SpinFinal`) is no
longer the definition of anything, and it is no longer part of the project: the comparison
module that related it to the intrinsic core was an adapter into the historical tree and has
been removed (it remains in the git history and in `Experiment1/`).  The upstream coupling of the intrinsic carrier through `Task9Freeze` is gone:
`Spine.E1.Carrier` imports `Mathlib` alone.

The intrinsic spin core is `SL(2,ℂ)`-free and matrix-model-free: the chain
`Carrier → Clifford → LorentzClifford → CliffordMonomial → SpinElement → SpinGroup → … →
SpinCover → SpinKernel`, together with the whole `Spine.E1.Topology.**` layer above it,
imports neither `MatrixModel` nor `PauliRepresentation` nor `SL2Comparison`, and the
firewall audit enforces this at level 1b.  The centre theorem
`SpinCore.center_Cl3`, which the kernel argument needs, was reconstructed from the monomial
frame for exactly this reason; see `SPIN_CORE_EXTRACTION_AUDIT.md`.

Two facts that upstream were obtained through the Hermitian model are proved intrinsically
in the core instead: the determinant dichotomy of a norm-preserving carrier automorphism
(`SpinCore.det_sq_of_NS_preserving`) and the determinant `-1` of the spatial reflection
(`SpinCore.spatialReflI_det`).  Two further facts that upstream came from the Hermitian
Jordan layer are proved directly from matrix entries in `Spine.E1.MatrixModel`
(`hMat_sq`, `center_eq_complexScalars`).

## Experiment-2 half: family, transition lift, defect

| Module root | Content |
| --- | --- |
| `Spine.E2.Family` | varying metric, oriented, real rank-three fibres over an arbitrary base; fibre frames; fibrewise visible group; local trivializations; transition data.  Root module imports `Mathlib` only. |
| `Spine.E2.Topology` | topological frame family, continuity of transitions, right action, reverse reconstruction |
| `Spine.E2.CentralDoubleCover` | the **generic** central double-cover / transition-lift interface, `Mathlib` only |
| `Spine.E2.SpinProjection` | the **native instance** `SpinCore.internalSpinProjection : InternalProjection SpinGroup GLor`, assembled from the intrinsic E1 results only (no adapter to historical code) |
| `Spine.E2.SpinProjectionIntegration` | integration test: the generic lift theory (local internal representatives, kernel ambiguity, Level B candidates, triple-overlap defect) applied to the native spin projection |
| `Spine.E2.Lift` | local internal representatives, kernel-valued ambiguity, triple-overlap defect, transition systems, internal transition candidates and the Level A/B/C frontier, all for an *arbitrary* interface |
| `Spine.E2.Descent` | descent, compatible transitions, refinement behaviour |
| `Spine.E2.Global` | glued internal object and conditional global interface |
| `Spine.E2.Defect` | intrinsic defect state, liftability classification for a fixed presentation |
| `Spine.E2.AtlasChange` | atlas change and the family-level classification `FamilyLiftable ↔ FamilyKernelDefectNeutral` |
| `Spine.E2.Core` | **principal production endpoint** + axiom audit |
| `Spine.Core` | the aggregate endpoint of the whole new project (both halves) |
| `Spine.Controls` | native controls: the split cover `G × ℤ/2 → G`, the circle double cover `z ↦ z²` with no global section, and the liftability controls built on them |

Four couplings present upstream were broken:

1. the Task-26 varying-family core no longer passes through the Task-25 one-fibre
   comparison endpoint; the topology layer imports the family core directly.  The historical
   one-fibre comparison modules were adapters into the legacy tree and have been removed;
2. the reusable local-lift interface was extracted out of the Task-28 base module, which
   previously forced an import of the whole Task-27 topology endpoint to obtain it;
3. the good/bad atlas regression control was moved out of the production chain into
   `RequestProject.Spine.Controls.E2.GoodBadAtlas` and `…FamilyDefectControl`, with the
   family-level theory reproved in production without it;
4. the concrete historical projection of the frame model was removed altogether.  The whole
   E2 theory is now parameterized by an internal projection `P : InternalProjection L G`;
   the statements that previously specialized it are either generic theorems or were
   deleted as pure specializations.  Non-vacuity is witnessed natively, by the circle double
   cover of `Spine.Controls.CircleDoubleCover`.

The **presentation-level vs family-level** distinction is preserved exactly: the production
module `Spine.E2.AtlasChange.FamilyDefectNeutrality` proves family-level neutrality and its
invariance properties, and the control module proves that the presentation-level statement
is *not* family-invariant.

## Deliberate non-claims

* No project defect is called `w₁` or `w₂`.  The rank-three oriented family of `Spine.E2`
  is not the tangent bundle of a Lorentzian manifold — it is an abstract family of fibres
  over an arbitrary topological base, with a fibre orientation assumed — so its
  kernel-valued triple-overlap defect is **not** identified with the second Stiefel–Whitney
  class, and no such identification is stated anywhere in the tree.
* No manifold orientation or time orientation, no global Spin structure, no spinor bundle
  over a manifold and no spin connection are constructed.  These are the next targets
  against this cleaned architecture, not part of it.

## Discipline

* No `sorry`, no `admit`, no `axiom` declaration, no `@[implemented_by]`, no
  `native_decide`.
* Every principal endpoint carries a `#print axioms` line; all report only `propext`,
  `Classical.choice`, `Quot.sound`.
* Statements taken from the upstream experiments are carried over unchanged apart from the
  carrier rename in the experiment-1 core and the module splits recorded above; where a
  statement had to be weakened to remove a control dependency, the production version has a
  new name and the original is preserved verbatim in the control layer.

## Task-3 layer: `RequestProject.Spine.E2.Cech.**`

A further production layer sits on top of the generic lift theory: abstract Čech covers of an
abstract topological base, visible transition data with the exact 1-cocycle law, families of
local Spin lifts, the kernel-valued triple-overlap defect, its Čech 2-cocycle law, the
coboundary law under change of local representatives, the lift-choice-independent fixed-cover
obstruction class, the equivalence `[c] = 1 ↔ coherent Spin-valued transition data exists`,
and refinement naturality.  Layer rules, mechanically checked by `Spine.Audit.Firewall`:

* `Cech.Cover … Cech.Refinement` are generic: they may not reach `Spine.E2.SpinProjection`,
  any control, the `SL(2,ℂ)`/matrix/Pauli layer, or either historical experiment tree;
* only `Cech.SpinInstance` instantiates the theory, and it does so with
  `SpinCore.internalSpinProjection` alone;
* the endpoint `Cech.Core` is imported by `Spine.Core`;
* no module of this layer constructs or mentions a manifold, tangent bundle, frame bundle,
  metric, connection, curvature, `w₁` or `w₂`.

## Task-4 layer: `RequestProject.Spine.Geometry.**`

The first geometric layer: oriented, time-oriented, Lorentz-orthonormal local frame data over
a family of four-dimensional real fibres (instantiated with the tangent spaces of a smooth
manifold modelled on the intrinsic carrier), the derived `GLor`-valued frame transition
cocycle, the Task-3 obstruction instantiated on it, the Čech notion of a Spin structure, the
equivalence `[c]_frame = 0 ↔ a Spin structure exists`, the fixed-cover torsor statement, and
the canonical additive `ℤ₂`-Čech presentation of the class.  Layer rules, mechanically checked
by `Spine.Audit.Firewall`:

* no module of this layer may reach a control, the `SL(2,ℂ)`/matrix/Pauli layer, or either
  historical experiment tree;
* the layer is downstream of `Spine.E2.Cech.**` and of `Spine.E2.SpinProjection`, and upstream
  of nothing except its own endpoint and the control;
* the class constructed here is **not** identified with `w₂(TM)`, and `w₂` is never defined
  as "the obstruction being studied"; the exact status is recorded in `TASK04_AUDIT.md`.

## Task-5 layer: `RequestProject.Spine.Cohomology.**`

The native mod-2 singular cohomology layer, and the start of the `w₂` certification branch:
singular cochains `Cⁿ(X;ℤ₂)` on Mathlib's singular simplicial set, the coboundary with the
theorem `δ² = 0`, the genuine quotient `Hⁿ(X;ℤ₂) = Zⁿ/Bⁿ`, functorial pullbacks, and the
Alexander–Whitney cup product with the descended products `H¹×H¹→H²` and `H²×H²→H⁴`.  Layer
rules, mechanically checked by `Spine.Audit.Firewall`:

* the seven pure-cohomology modules (`Cochain`, `Coboundary`, `Cohomology`, `Functorial`,
  `AlexanderWhitney`, `Cup`, `CupDescent`) are built on **Mathlib alone**: they may reach no
  module of `Spine.E1`, `Spine.E2`, `Spine.Geometry` or `Spine.Controls`, and neither
  historical experiment tree;
* only `Cohomology.CechBridgeSpec` touches the Čech side, and it does so solely to state the
  *specification* of the still-missing Čech-to-singular comparison as an explicit hypothesis;
  the fixed-cover obstruction quotient is **not** identified with `H²_sing`;
* no module of the Spine may reach any inspected external project (mechanical check
  `auditNoExternal`: external-project imports = 0 over all Spine modules);
* the endpoint `Cohomology.Core` is imported by `Spine.Core` and carries the axiom audit;
* no `w₂`, no Stiefel–Whitney class, no fundamental class, no Poincaré duality, no Steenrod
  algebra and no principal bundle occurs in this layer.  Status and remaining dependencies:
  `TASK05_AUDIT.md`; provenance of the inspected external references:
  `TASK05_EXTERNAL_SOURCES.md`.

## Task-6 layer: `RequestProject.Spine.Cech.**`

The native **fixed-cover Čech `ℤ₂`-cohomology** layer, and the bridge that puts the Spin-lift
obstruction into it.  Layer rules, mechanically checked by `Spine.Audit.Firewall`:

* the Spin-independent half (`Cech.Cochain`, `Cech.Coboundary`, `Cech.Cohomology`,
  `Cech.Refinement`) is built on **Mathlib alone**: it may reach no module of `Spine.E1`,
  `Spine.E2`, `Spine.Geometry`, `Spine.Cohomology` or `Spine.Controls`, and neither historical
  experiment tree.  The Čech complex, `δ_Č² = 0`, `B̌ⁿ ⊆ Žⁿ`, the quotient `Ȟⁿ(𝓤;ℤ₂)` and the
  refinement pullback therefore exist independently of all Spin geometry;
* the bridge half (`Cech.CoverNerve`, `Cech.KernelSign`, `Cech.SpinKernelSign`,
  `Cech.SpinCocycle`, `Cech.Comparison`, `Cech.SpinInstance`) is downstream of the Task-3 Čech
  layer and of the Task-4 sign map, and it *consumes* those results — no Task-3 declaration was
  modified, weakened or removed;
* `Cech.SingularBridgeSpec` is the only module touching the Task-5 singular layer, and it does
  so solely to state the *specification* of the still-missing comparison
  `Ȟ²(𝓤;ℤ₂) → H²_sing(X;ℤ₂)` as an explicit hypothesis;
* no cover is assumed to be good, no direct limit over covers is taken, and the class
  `[z] ∈ Ȟ²(𝓤;ℤ₂)` is **not** identified with `w₂(TM)`;
* the relation to the earlier carrier is a theorem, not a naming convention: the canonical map
  `Ȟ²(𝓤;ℤ₂) → ObstructionClass P 𝓤` is injective on covers with preconnected double overlaps and
  provably not surjective in general (`EMBEDS_CANONICALLY`);
* the endpoint `Cech.Core` is imported by `Spine.Core` and carries the axiom audit.  Status,
  hypotheses and remaining dependencies: `TASK06_AUDIT.md`.

## Task-7 layer: `RequestProject.Spine.GoodCover.**`

The **good-cover / nerve** layer: the cover-side qualification of the Task-6 Čech class and the
exact specification of the still-missing comparison with Task-5 singular cohomology.  Layer
rules, mechanically checked by `Spine.Audit.Firewall`:

* `GoodCover.Presimplicial` (abstract presimplicial `ℤ₂` cochain complexes, with their own
  `δ² = 0`) reaches **no** module of this project at all — Mathlib only;
* `GoodCover.GoodCover` (the predicate `IsGoodCover` and the implication chain
  contractible ⇒ path connected ⇒ connected ⇒ preconnected) and
  `GoodCover.NerveIdentification` (the nerve as a presimplicial set, and the theorem that the
  Task-6 Čech complex *is* its simplicial complex) reach no `E1`, `E2`, `Geometry`, `Cohomology`
  or `Controls` module;
* `GoodCover.PointCohomology` (the native computation `Hⁿ⁺¹_sing(point;ℤ₂) = 0`) reaches only
  the Task-5 cochain/coboundary/cohomology modules;
* `GoodCover.AcyclicCover`, `GoodCover.ManifoldCovers`, `GoodCover.Constancy` are the
  cover-side results that consume Task-3/Task-4/Task-6 material (good cover ⇒ the Task-6
  constancy conditions; strong local contractibility and contractible-open covers of a Task-4
  manifold; injectivity into the old Task-3 carrier);
* `GoodCover.SingularComparisonSpec` and `GoodCover.W2Interface` contain **hypothesis
  structures only** — the nerve theorem, the simplicial-to-singular comparison, homotopy
  invariance, common good refinements, and the future `w₂` interface.  None is an axiom, none is
  a typeclass, and no production module consumes them;
* good-cover *existence* is not proved and not assumed; `w₂(TM)` is not defined, and the
  Spin-lift class is not called `w₂`;
* the endpoint `GoodCover.Core` is imported by `Spine.Core` and carries the axiom audit.
  Status, hypotheses, blocked edges and the failbuild ledger: `TASK07_AUDIT.md`.

## Task-9 layer: `RequestProject.Spine.Nerve.**`

The canonical simplicial model of the cover nerve, its geometric realization, and the geometric
simplicial-to-singular comparison.

* `Nerve.CoverNerveSSet` — the cover nerve as a genuine simplicial set `Δᵒᵖ ⥤ Set`: faces are
  the existing Čech face operators, degeneracies are repetition of a vertex, and every
  simplicial identity comes from the functorial structure.  Layer-wise it reaches only the
  Task-6 Čech complex and the Task-7 presimplicial layer: no Spin, no lift, no geometry, no
  singular cohomology;
* `Nerve.CochainComparison` — forgetting the degeneracies returns the *existing* presimplicial
  nerve, so the Task-6 cochain complex, cocycles, coboundaries and cohomology are unchanged;
  plus the characterisation of degenerate nerve simplices.  Same isolation as above;
* `Nerve.Realization` — `|N(𝓤)| = SSet.toTop.obj (coverNerveSSet 𝓤)`, and the canonical
  characteristic singular simplex of each nerve simplex, taken from the unit of the
  realization/singular adjunction, with face and degeneracy compatibility and its universal
  property.  Reaches the Task-5 singular layer;
* `Nerve.ChainMap`, `Nerve.CochainMap` — the chain map `J` with `∂J = J∂`, its transpose
  cochain map `J*` with `J*δ = δJ*`, and the induced map on cohomology;
* `Nerve.ComparisonSpec` — the two remaining blocked edges as **explicitly conditional
  specifications** (bijectivity of the constructed comparison map; the nerve theorem in the
  shape `|N(𝓤)| ≃ X`), the constructed canonical nerve presentation, and everything downstream
  of them, including the Spin-lift class on the realized nerve;
* the endpoint `Nerve.Core` is imported by `Spine.Core` and carries the axiom audit.  Status,
  audits, blocked edges and the failbuild ledger: `TASK09_AUDIT.md`.

---

# Task 10 — layer addendum (2026-09-08)

Four modules are added to `RequestProject.Spine.Nerve.**`; no other layer changes.

| module | role |
| --- | --- |
| `Nerve.UnitChainMap` | free `ℤ₂`-linearisation of simplicial sets; proves the Task-9 `chainMap` **is** `C_*(η_K)` |
| `Nerve.Dualization` | the explicit transpose `dualOf` of a `ℤ₂`-linear map of free modules; `dualOf ∂ = δ`, `dualOf J = J*` |
| `Nerve.ChainHomotopyComparison` | the chain-level comparison datum, and the theorem that it makes the existing `geometricHmap` bijective in every degree |
| `Nerve.ManifoldAssumptionAudit` | WP0: a counterexample refuting "charted on the Task-4 carrier ⟹ second countable" |

Layer discipline is unchanged: these are production modules, they import only `Mathlib` and
earlier Spine layers, and `RequestProject.Spine.Nerve.Core` remains the single endpoint of the
nerve layer.  The firewall reports `Spine modules audited: 171`, all legacy and external import
counts `0`.

No new hypothesis is introduced anywhere in the Spine: `ChainHomotopyEquivData` is a structure
that nothing unconditional consumes, and `ChainComparisonStatement` is a `Prop` consumed by
nothing.

# Tasks 32–34 — layer addendum: emergence, smoothness, tangent/solder (2026-09-12)

Three layers were added after the Task-10 addendum above; this section records their place in
the architecture (the mechanical counterpart is `RequestProject/Spine/Audit/ArchitectureDAG.lean`,
checks 9 and 10).

```text
Spine.Emergent.**            base-free emergence layer (Tasks 32–34)
  LocalModel → BaseGluing → Reconstruction → Symmetric → {NonDerivability, SmoothGate}
  SmoothGate → SmoothStructure → TangentTransition
  Symmetric  → SymmetricCanonical → SymmetricSmooth ;  NonDerivability → LocalPieceData
  CoverAdapter                      the *only* emergence module that sees the Čech cover
                                    interface `Spine.E2.Cech.Cover`

Spine.Solder.**              bottom-up tangent/solder layer (Task 34)
  InternalLorentz → Independence → Solder → LorentzBundle

Spine.Comparison.**          leaves of the production DAG
  EmergentSpinGate            emergence × Spin-native
  SolderTangentGate           bottom-up solder × top-down Geometry (Task 4)
```

Discipline, in addition to the rules above:

* no module of `Spine.Emergent` may reach `E2`, `Cech`, `Geometry`, `Nerve`, `GoodCover`,
  `Cohomology`, `AlgebraicTopology`, `SpinNative`, `Comparison` or `Controls` — with the single
  documented exception of the adapter `Emergent.CoverAdapter`, which may reach
  `E2.Cech.Cover` and nothing above it;
* no module of `Spine.Solder` may reach `Geometry`, `Cech`, `Nerve`, `GoodCover`,
  `Cohomology`, `AlgebraicTopology`, `Comparison`, `Controls` or an obstruction module of
  `E2.Cech`.  The top-down tangent/frame branch is a **certification target** of the solder
  layer, never an input;
* only `Comparison.SolderTangentGate` sees both branches, and the firewall requires it to
  reach both (so the separation checks are not vacuous).

# Task 35 — layer addendum: regularity and bundle equivalence (2026-09-12)

```text
Spine.Solder.**              bottom-up tangent/solder layer (Tasks 34–35)
  InternalLorentz ─┐                      native Spin → projected Lorentz transition
  (Emergent.TangentTransition) ─┐         actual atlas → tangent transition
                   └─────────────┴── Independence → Solder → LorentzBundle
                                        → RegularSolder → {RegularExamples → WeakInsufficiency,
                                                           BundleEquivalence → SmoothMetric
                                                             → OrientationTime → RegularGauge}

Spine.Comparison.**          leaves of the production DAG
  SmoothSolderGate            regular solder × tangent bundle × Spin endpoint (Task 35)
```

Two changes of discipline were made in Task 35:

* `Solder.InternalLorentz` **must not** import `Emergent.TangentTransition`.  The internal
  Lorentz transition system is independent of tangent geometry, and the architecture audit now
  rejects that edge.  The comparison of the two transition systems happens only in
  `Solder.Independence` and above.
* `Comparison.SmoothSolderGate` is the second (and last) join of the bottom-up and top-down
  branches; like `Comparison.SolderTangentGate` it is a leaf, and the firewall requires it to
  reach both branches, so the separation checks remain non-vacuous.

Everything else is unchanged: no `Spine.Solder` module reaches `Geometry`, `Cech`, `Nerve`,
`GoodCover`, `Cohomology`, `AlgebraicTopology`, `Comparison`, `Controls`, or an obstruction
module of `E2.Cech`.

---

# Task 36 addendum — the adversarial layer (2026-09-12)

Task 36 adds one new layer, `RequestProject.Spine.Task36.**`, the **adversarial /
comparison** layer.  It is a *leaf* of the Spine: no production module, no control module and
no other Spine module imports anything of it.

| Layer | Module root | Rule |
| --- | --- | --- |
| adversarial / comparison | `RequestProject.Spine.Task36.**` | may import the production layer and `Mathlib`; **no** other Spine module may import it |

Inside the layer there are two sublayers, separated mechanically:

```text
    frozen bottom-up branch  (Spine.SpinNative.**, Spine.Emergent.**, Spine.Solder.**)
              \
               →  Spine.Task36.**            adversarial battery
              /
    top-down obstruction branch (Spine.E2.Cech.Obstruction, Spine.Geometry.**,
                                 Spine.Cech.**, Spine.Comparison.**)
```

* **bottom-up Task-36 modules** — `LoopModel`, `OrientationGate`, `OrientationReversing`,
  `LoopSolder`, `LoopSpinFreedom`, `TimeOrientation`, `TrivialControl`,
  `SmoothBundlePackaging`, `GaugeGroup`, `SpinNotLorentz`, `SpinFoamControl`: these may **not**
  reach the top-down obstruction branch at all;
* **the single comparison module** — `Spine.Task36.SpinObstruction`: the only module allowed to
  use both branches, and it must reach both (positive control);
* `Spine.Task36.Certificate` bundles the proved endpoints;
* `Spine.Task36.Firewall` is the audit module for the layer.

The forbidden shape `bottom-up production module → Task36 → top-down w₁/w₂ branch` is
excluded by the leaf check and the branch check together.  Both, plus a curvature claim
firewall and a zero-legacy/zero-external audit of the layer, are enforced at compile time by
`RequestProject/Spine/Task36/Firewall.lean`; see `TASK36_AUDIT.md` §§15, 21.

---

## Task 37 — the deformation-preparation branch

```text
    frozen bottom-up branch  (Spine.SpinNative.**, Spine.Emergent.**, Spine.Solder.**)
              \
               →  Spine.Task36.**          adversarial battery (frozen)
                        \
                         →  Spine.Deformation.**   deformation preparation (leaf)
```

* `Spine.Deformation.SharedTransport` — the single shared native Spin-side transport state
  `transportState : ℝ → SpinGroup` and the two-field family interface; the Lorentz side is
  obtained only through `SpinCore.spinCover`.
* `Spine.Deformation.LoopSharedTransport` — the `λ`-deformed native Spin transition datum on
  the frozen periodic fixed-cover loop model.
* `Spine.Deformation.NeutralRegression` — exact regression at `λ = 0`, and the availability of
  the frozen Task-36 reconvergence theorem there.
* `Spine.Deformation.ClosureAdmissibility` — `RegularClosureSolution`,
  `RegularClosureAdmissible`, CONTROL A vs MAIN TEST B, the anti-vacuity controls and the
  regime vocabulary.
* `Spine.Deformation.Firewall` — leaf, legacy/external, shared-origin field-list,
  target-leakage token and sensitivity audits.

Rules enforced at compile time: the branch is a leaf of the Spine; the family structure has
exactly the fields `base` and `spin` (no independently supplied Lorentz transition); the
closure-solution structure has exactly `smoothGluing` and `solder` (no supplied compatibility
field); and no declaration of the branch may name curvature, a target geometry, a field
equation, a transport form or a loop-transport object.

Task 36's own firewall was amended in exactly one place: its leaf check now exempts
`Spine.Deformation`, which is a declared consumer of the frozen layer and is itself audited to
be a leaf.

## Task 38 — the fixed-base smoke test (inside the deformation leaf)

* `Spine.Deformation.ProjectedParaAction` — the closed form `paraMap l` of the projected shared
  transport state as a continuous linear map of the local model, identified with
  `SpinCore.spinCover (transportState l)`, smooth in the parameter.
* `Spine.Deformation.FixedBaseSmokeTest` — the CONTROL A predicate `ControlAAdmissible`, the
  explicit compensating regular solder `loopParaSolder` built from a smooth interpolation
  profile, and the admissibility locus (all of `ℝ`).
* `Spine.Deformation.CocycleGaugeOrbit` — full-group cocycle gauge equivalence (convention
  derived from the project's kernel-valued `SpinNative.GaugeEquiv`), the explicit chartwise
  Spin gauge, the single-orbit theorems on the Spin and projected Lorentz side, and the
  kernel-level separation record.
* `Spine.Deformation.TangentMetricComparison` — equality of the induced tangent Lorentz metrics
  of the explicit admissible witnesses.
* `Spine.Deformation.SmokeTestCertificate` — the interface certificate, the first-order
  parameter control and `native_transport_knob_smoketest_certificate`.

The branch firewall audits all nine modules; no check was relaxed.  The scientific outcome is
recorded in `TASK38_SMOKETEST_RESULT.md`, at its exact scope: the *tested* native one-parameter
Spin Čech-transition family is universally admissible on the frozen periodic fixed-cover
control base and lies in one full-Spin Čech gauge orbit there, so on that control it is not a
transport-geometry degree of freedom.  Nothing is proved about Čech transition deformations in
general.  Transport one-forms, parallel transport, loop transport and field strength remain
**NOT FORMALIZED**; the minimal next step is specified in `NEXT_PHASE_TRANSPORT_GATE.md`
(Task 40; it supersedes the withdrawn draft `TASK39_CONNECTION_TRANSPORT_GATE_HANDOFF.md`).
