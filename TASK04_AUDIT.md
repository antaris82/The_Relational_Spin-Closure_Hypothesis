# TASK 04 AUDIT — Lorentzian Frame Geometry and Identification of the Spin-Lift Obstruction

All statements below are theorems of the project unless explicitly marked otherwise.  The
whole layer builds green (`lake build`, 8153 jobs) with no `sorry`, no `admit`, no
project-local `axiom`, no `unsafe`, no `partial`, no `implemented_by`, and with the mechanical
legacy firewall (`RequestProject.Spine.Audit.Firewall`) extended to cover every new module.

---

## 0. Final scientific answers

**Question 1.**  *When the abstract native Spin-lift obstruction of Task 3 is instantiated on
the proper orthochronous Lorentz frame transition cocycle of an oriented and time-oriented
Lorentzian four-manifold, is it exactly the conventional second Stiefel–Whitney obstruction
`w₂(TM)`, canonically equivalent to it, or only equivalent at the level of vanishing?*

**Answer: only at the level of vanishing — and even that comparison cannot be written down
against a formal `w₂`, because `w₂` does not exist in the pinned library.**  Precisely:

* the instantiation itself is complete and theorem-level: the Lorentz frame transition
  cocycle of an oriented, time-oriented Lorentz-orthonormal tangent-frame datum on a smooth
  four-manifold is `GLor`-valued (`LorentzFrames.LorentzFrameData.comparison_mem_GLor`),
  satisfies the exact Čech laws (`frame_transition_laws`), and feeds the Task-3 machinery,
  giving a `{±1}`-valued class independent of the chosen local Spin representatives
  (`frameObstruction_choice_independent`);
* that class vanishes **iff** the frame data admits a Spin structure
  (`frameObstruction_eq_trivial_iff_spinStructure`, packaged as
  `LorentzFrames.tangent_frame_spin_lift_obstruction`);
* transported along the **canonical** isomorphism `{±1} ≅ ℤ/2`, the obstruction becomes an
  additive `ℤ₂`-valued Čech 2-cocycle on the chosen cover, satisfying the standard additive
  cocycle law (`zdefect_cocycle₂`) and the standard additive coboundary law
  (`zdefect_change_of_lift`), whose class vanishes iff a Spin structure exists
  (`zdefect_isCoboundary_iff_spinStructure`).  This is precisely the Čech shape in which
  `w₂` is conventionally presented;
* the pinned Mathlib contains **no Stiefel–Whitney classes, no classifying spaces, no
  principal bundles, no Spin structures, and no cohomology of a topological space with `ℤ₂`
  coefficients**.  So the sentence `[c]_frame = w₂(TM)` cannot be *stated*, let alone proved.
  Defining `w₂` as "the obstruction to a Spin lift" is forbidden by the task (circular) and
  was not done.

**Classification of the WP7 endpoint: `VANISHING_EQUIVALENCE_ONLY`, with a canonical
`ℤ₂`-Čech presentation of the carrier; literal equality with `w₂(TM)` is `BLOCKED` at library
level (not conceptually).**

**Question 2.**  *What additional structure is still required before the Spin bundle can
determine spacetime geometry rather than merely lift its Lorentz frame structure?*

Everything after topological admissibility.  In dependency order, the next unresolved bridge
is: (i) a **total-space** formulation — an actual principal `SO⁺(1,3)`-bundle of oriented
time-oriented orthonormal frames and its `Spin⁺(1,3)`-principal lift, which requires
principal-bundle infrastructure that does not exist in the pinned library; then (ii) a
**solder form** identifying the associated vector bundle with `TM` — this is the first place
where the Spin data ceases to be a mere lift of transition functions and starts to *carry*
geometry; and only after that (iii) a connection, its curvature and torsion, and any
dynamical or relational law.  None of (i)–(iii) is attempted here, and nothing in this task
constrains them.  The immediate next bridge to attack is (i)+(ii): *soldering*.  It is
identified, not solved.

---

## 1. WP1 — availability matrix of manifold / bundle / characteristic-class infrastructure

| item | status | source |
|---|---|---|
| topological spaces, open covers | available in Spine | `CechSpinLift.CechCover` (Task 3) |
| abstract Čech 1-/2-cochains, defect, obstruction class, refinement | available in Spine | `RequestProject.Spine.E2.Cech.**` |
| intrinsic Spin group, `GLor`, double cover, kernel `{±1}`, topology, local sections | available in Spine | `RequestProject.Spine.E1.**`, `SpinCore.internalSpinProjection` |
| intrinsic determinant dichotomy for `B_𝒮`-isometries | available in Spine | `SpinCore.det_sq_of_BS_preserving` |
| intrinsic volume form / coordinate determinant | available in Spine | `SpinCore.volS`, `SpinCore.coordEquiv` |
| charted spaces, models with corners, smooth manifolds | canonical from Mathlib | `ChartedSpace`, `ModelWithCorners`, `IsManifold` |
| tangent spaces / tangent bundle | canonical from Mathlib | `Bundle.TangentSpace`, `TangentBundle` |
| vector bundles, local frames of a vector bundle | canonical from Mathlib | `Mathlib.Geometry.Manifold.VectorBundle.**` |
| bases, determinants, top-degree alternating forms | canonical from Mathlib | `Module.Basis.det`, `AlternatingMap`, `LinearMap.det` |
| **Riemannian** metrics | canonical from Mathlib | `Mathlib.Geometry.Manifold.Riemannian.Basic` (positive definite only) |
| **pseudo-Riemannian / Lorentzian** metrics | **absent** — defined natively | field `metric` of `LorentzFrames.LorentzFrameData` |
| **orientation** of a manifold / vector bundle | **absent** — defined natively | field `vol` (fibrewise top form) + `positivelyOriented` |
| **time orientation** | **absent** — defined natively | field `timeField` + `timelike_timeField` + `futureDirected` |
| **orthonormal frames, frame bundle** | **absent** — frames defined natively | field `frame` + `orthonormal` |
| **principal bundles** | **absent**, substantial new infrastructure | — |
| **Spin structures** (total-space form) | **absent**, substantial new infrastructure | — |
| Spin structures (Čech/cocycle form) | defined natively | `LorentzFrames.SpinFrameStructure` |
| **Stiefel–Whitney classes** `w₁`, `w₂` | **absent**, substantial new infrastructure | — |
| **singular / Čech cohomology of a space with `ℤ₂` coefficients** | **absent** (only `AlgebraicTopology.SingularHomology.Basic`, and a category-theoretic Čech complex for sites) | — |
| fixed-cover `ℤ₂` Čech cochains, coboundary, vanishing criterion | defined natively | `RequestProject.Spine.Geometry.Z2Class` |

The two entries that would be needed for a literal `w₂` theorem — Stiefel–Whitney classes and
`H²(M;ℤ₂)` — are both in the "absent and requiring substantial new infrastructure" row.  No
attempt was made to force literal equality by building a large characteristic-class library;
the task explicitly forbids that.

### Dependency DAG (Task 4)

```
RequestProject.Spine.E1.Coords / ShellTransitivity      (intrinsic carrier, det dichotomy)
        │
        ▼
RequestProject.Spine.Geometry.CausalAlgebra             (WP2/WP9: causal algebra,
        │                                                reduction criterion, controls)
        ├── RequestProject.Spine.E1.Topology.LorentzTopology   (topology of GLor)
        ├── RequestProject.Spine.E2.Cech.Cover                 (Task-3 covers & cocycles)
        ▼
RequestProject.Spine.Geometry.FrameField                (WP2/WP3: frame datum,
        │                                                GLor-valued frame cocycle)
        ├── RequestProject.Spine.E2.Cech.SpinInstance          (Task-3 obstruction, native ρ)
        ▼
RequestProject.Spine.Geometry.SpinStructure             (WP4/WP5/WP8)
        ├────────────────► RequestProject.Spine.Geometry.Z2Class      (WP7)
        ▼
RequestProject.Spine.Geometry.TangentInstance           (WP1/WP3: genuine TM)
        ▼
RequestProject.Spine.Geometry.Core                      (endpoint, axiom audit)
        ▼
RequestProject.Spine.Controls.Geometry.FlatFrameControl  (controls, downstream only)
```

No module of `RequestProject.Experiment1` or `RequestProject.Experiment2` occurs in any
import closure (mechanically checked, see §10).

---

## 2. WP2 — orientation vs. time orientation, and the identification of `GLor`

The five structures the task insists on separating are separate objects here.

| # | structure | formal object | class |
|---|---|---|---|
| 1 | orientability of the fibres | existence of a `vol` with the positivity condition | existence statement |
| 2 | a chosen orientation | field `vol : ∀ x, (Fib x) [⋀^Fin 4]→ₗ[ℝ] ℝ` | `CHOICE_OF_ORIENTATION` |
| 3 | time-orientability | existence of a timelike `timeField` | existence statement |
| 4 | a chosen time orientation | field `timeField : ∀ x, Fib x` with `timelike_timeField` | `CHOICE_OF_TIME_ORIENTATION` |
| 5 | reduction to the proper orthochronous group | theorem `comparison_mem_GLor` | `DERIVED_NATIVE` |

**The identification of the conventional proper orthochronous Lorentz group with the native
`GLor` is not assumed and not needed.**  It is avoided altogether: the native
`SpinCore.GLor` *is* the target, defined intrinsically as

```
GLor = { F : 𝒮 ≃ₗ[ℝ] 𝒮 | N_𝒮 ∘ F = N_𝒮 , F preserves the square cone 𝒞 , det_ℝ F = 1 }
```

and the reduction theorem proves membership in *that* group from the geometric hypotheses.
This is the honest resolution of the WP2 subtask "do not silently identify them": no
identification with an externally presented `SO⁺(1,3)` matrix group is used anywhere in
Task 4.  (Independently, the Spine already contains the comparison with `SL(2,ℂ)` in
`RequestProject.Spine.E1.SL2Comparison`; it is *not* imported by this layer.)

Derived reduction chain (`RequestProject.Spine.Geometry.CausalAlgebra`,
`RequestProject.Spine.Geometry.FrameField`):

1. metric compatibility of two frames ⟹ the comparison map is a `B_𝒮`-isometry
   (`comparison_isometry`);
2. isometry + both frames future-directed for the *same* time-orientation field ⟹ the
   comparison map is orthochronous (`comparison_future`), via the causal sign lemma
   `fst_pos_of_BS_pos_of_timelike`;
3. isometry ⟹ `det = ±1` (inherited `det_sq_of_BS_preserving`); both frames positively
   oriented for the *same* orientation form ⟹ `det > 0` (via `vol_comp_det`); hence
   `det = 1` (`comparison_det_eq_one`);
4. therefore `comparison_mem_GLor`.

### Negative controls: the hypotheses are independent and none is redundant

| control | statement | consequence |
|---|---|---|
| `SpinCore.spatialReflI_notMem_GLor` | the spatial reflection preserves `N_𝒮` **and** the cone but has `det = -1` | orientation is not implied by metric + time orientation |
| `SpinCore.timeReflI_not_isGLorWide` | the time reflection preserves `B_𝒮` but reverses the cone | time orientation is not implied by the metric |
| `SpinCore.timeRefl_comp_spatialRefl_notMem_GLor` | a `B_𝒮`-isometry of determinant `+1` that is not orthochronous | orientation does **not** imply time orientation |

---

## 3. WP3 — the Lorentz-orthonormal frame cocycle

`LorentzFrames.LorentzFrameData` (see the table in the module docstring) carries local frames
`e i x : 𝒮 ≃ₗ[ℝ] Fib x` defined at every point but *constrained only on their patch* — no
global frame, no trivial bundle, no parallelizability is assumed anywhere.

Convention: `comparison i j x := e_i(x)⁻¹ ∘ e_j(x)`, i.e. `e_j = e_i · g_ij`, matching the
task statement; the group law on `𝒮 ≃ₗ[ℝ] 𝒮` is `(f * g) v = f (g v)`, so
`g_ij * g_jk = g_ik` is composition in the stated order.

Proved (`frame_transition_laws`, via `frameCocycle`):

* `g_ii = 1` on `U i`;
* `g_ji = g_ij⁻¹` on `U i ∩ U j`;
* `g_ij * g_jk = g_ik` on `U i ∩ U j ∩ U k` (proved directly from the frames);
* continuity of each `g_ij` on `U i ∩ U j`.

The first two are inherited from the Task-3 layer, where they are *derived* from the cocycle
law rather than assumed.  Off the double overlap the transition is set to the unit; every
statement is restricted to the overlaps.

**Regularity classification.**  Continuity of the frame comparison on double overlaps is a
*hypothesis* (field `continuousOn_comparison`), classified `REGULARITY_HYPOTHESIS`.  It is the
standard content of "the local frames are continuous sections of the frame bundle"; deriving
it from a total-space frame bundle would need the principal-bundle infrastructure listed as
absent in §1.

**Existence of Lorentz-orthonormal local frames for a given metric is not proved** and is not
assumed silently: it is part of the *given* datum.  Producing such frames from a Lorentzian
metric needs a fibrewise Gram–Schmidt process plus a shrinking argument — classified
`BLOCKED (library-level, small-to-medium)`; see §7.

---

## 4. WP4 — the Task-3 obstruction on the frame cocycle

* `LorentzFrames.FrameSpinLifts Φ` — the Task-3 `SpinLiftFamily` for
  `SpinCore.internalSpinProjection` and the frame cocycle: a choice of continuous local Spin
  representatives on the double overlaps.
* `frame_defect_eq_pm_one` — the triple-overlap defect `c_ijk = g̃_ij g̃_jk g̃_ik⁻¹` is
  `{1, negOneSpin}`-valued (kernel of the native double cover, `Nat.card = 2`).
* `frameObstruction D` — the **Lorentz-frame Spin-lift obstruction**, the Task-3 fixed-cover
  class of that defect.
* `frameObstruction_choice_independent` — independent of the chosen local Spin
  representatives.
* `frameObstruction_eq_trivial_iff_spinStructure` — vanishes **iff** coherent Spin-valued
  frame transition data exists, i.e. iff a Spin structure exists (WP5).

At this stage the object is called *only* the Lorentz-frame Spin-lift obstruction; the name
`w₂` is not used for it anywhere in the sources.

---

## 5. WP5 — Spin structures, and the four levels of nonuniqueness

`LorentzFrames.SpinFrameStructure Φ` is the Čech presentation of a Spin structure on the
oriented, time-oriented orthonormal frame data: a continuous `Spin`-valued transition cocycle
lifting the frame cocycle along the intrinsic double cover `SpinGroup → GLor`.  The
equivalence with coherent Spin-valued transition data is
`nonempty_spinFrameStructure_iff_exists_coherent`.

| level | object | class |
|---|---|---|
| choice of local frames | field `frame` of `LorentzFrameData` | `CHOICE_OF_LOCAL_FRAME` |
| choice of local Spin representatives ("local Spin frames") | a `FrameSpinLifts Φ` | choice up to kernel; the *defect* depends on it, the *class* does not |
| a Spin structure | a `SpinFrameStructure Φ` | `CHOICE_OF_SPIN_STRUCTURE` |
| existence of a Spin structure | `Nonempty (SpinFrameStructure Φ)` | the only thing the vanishing is equivalent to |
| isomorphism class of Spin structures | **not formalized** | deferred, see WP8 |

**Total-space formulation: `BLOCKED`.**  A Spin structure as a principal `Spin⁺(1,3)`-bundle
with an equivariant 2:1 map to the orthonormal frame bundle cannot be written: the pinned
library has no principal bundles.  On a fixed cover the cocycle description used here is the
standard equivalent; the equivalence between the two descriptions is exactly what the missing
infrastructure would supply.

---

## 6. WP6 — the classical `w₂` criterion

**Status: `BLOCKED` (library level).**  The classical theorem

> an oriented vector bundle admits a Spin structure ⟺ `w₂ = 0`

cannot be connected to anything formal here, because none of `w₂`, `H²(M;ℤ₂)`, principal
bundles or classifying spaces exists in the pinned Mathlib (§1).  Per the task's explicit
instruction, `w₂` was **not** defined as "the obstruction being studied": that would be
circular and would prove nothing.

What was done instead is the smallest honest bridge available: WP7 below rewrites the native
obstruction in the conventional additive `ℤ₂` Čech language, so that the object being compared
is of the correct classical shape (a `ℤ₂`-valued Čech 2-cocycle class on a cover of `M` whose
vanishing is Spin-liftability), even though the comparison partner is missing.

Minimal extra theory required to unblock WP6, in increasing order of size:
`H²(–;ℤ₂)` for topological spaces (Čech or singular) → principal bundles and their
classification → classifying spaces `BO(n)`, `BSO(n)` → Stiefel–Whitney classes with their
axioms → the classical criterion.  This is a large library, deliberately not built here.

---

## 7. WP7 — the strongest proved identification

Proved (`RequestProject.Spine.Geometry.Z2Class`):

* the canonical group isomorphism between the intrinsic kernel `{1, negOneSpin}` and `ℤ/2`
  (`spinSign`, `zToSpin`, `spinSign_mul`, `spinSign_zToSpin`, `zToSpin_spinSign`,
  `spinSign_injOn_ker`) — `CANONICAL_IDENTIFICATION`;
* `zdefect D` — the additive `ℤ₂`-valued triple-overlap cochain;
* `zdefect_cocycle₂` — the additive Čech 2-cocycle law on quadruple overlaps;
* `zdefect_change_of_lift` — the additive coboundary law, so the additive class is
  well defined;
* `zdefect_isCoboundary_iff_spinStructure` — the additive class vanishes iff a Spin structure
  exists.

**Classification of the relation between `[c]_frame` and `w₂(TM)`:**

* literal equality — **not available** (`BLOCKED`, library level);
* equality under a canonical isomorphism of carriers — **not available** (`BLOCKED`: the
  target carrier `H²(M;ℤ₂)` does not exist formally);
* equality of vanishing loci — **this is what is proved**, in the precise sense that the
  native class vanishes exactly when the frame data admits a Spin structure, which is the
  property that classically characterizes `w₂(TM) = 0`;
* the obstruction is additionally presented in the conventional `ℤ₂`-Čech form on the chosen
  cover (`CANONICAL_IDENTIFICATION` of the *carrier shape*, not of the class with `w₂`).

**Verdict: `VANISHING_EQUIVALENCE_ONLY`.**  The blockage is library-level, not conceptual.

Two further honest caveats, both inherited from Task 3 and unchanged here:

* the class is a **fixed-cover** class; refinement naturality is proved in Task 3
  (`obstruction_pullLift`), but no cover-independent direct limit is constructed;
* the existence of a lift-admissible cover (local Spin lifts on whole double overlaps) is a
  hypothesis, not a theorem, for an arbitrary base; every Task-4 statement quantifies over a
  given family of local lifts, or is conditional on one existing.

---

## 8. WP8 — Spin-structure multiplicity

**Status: proved, in the fixed-cover cocycle form.**

* `KerCocycle₁ Φ` — the continuous `{±1}`-valued Čech 1-cocycles of the cover;
* `SpinFrameStructure.ratio` — the difference of two Spin structures is such a cocycle;
* `SpinFrameStructure.twist` — twisting a Spin structure by such a cocycle is a Spin
  structure;
* `twist_ratio`, `ratio_twist`, packaged as `spinStructure_torsor` — the two operations are
  mutually inverse, i.e. the action is simply transitive.

**Deferred:** the passage from cocycles to `H¹(M;ℤ₂)` and from Spin structures to their
*isomorphism classes* — this needs the quotient by 1-coboundaries and the notion of
isomorphism of Spin structures, and, for a cover-independent statement, a direct limit over
refinements.  Classified `DEFERRED`, not blocking the primary result.

**Negative control (formal):**
`LorentzFrames.Control.two_distinct_spinFrameStructures` exhibits two *distinct* Spin
structures on the same frame data, so vanishing of the obstruction does not determine a Spin
structure.

---

## 9. WP9 — signature and component audit

| item | statement | source |
|---|---|---|
| signature | `NS sOne = 1`, `NS (0, e_k) = -1` for `k : Fin 3` — one plus, three minuses, i.e. `(1,3)` | `SpinCore.NS_sOne`, `SpinCore.NS_spatial_unit` |
| dimension | `finrank ℝ 𝒮 = 4`; every tangent space of the modelled manifold is 4-dimensional | `LorentzFrames.finrank_carrier`, `finrank_tangentSpace` |
| sign convention | `N_𝒮 x = x₀² - |x⃗|²` (mostly minus, timelike positive) | `SpinCore.NS_def` |
| properness | `det = 1` is part of `IsGLor`; the reflection with `det = -1` is excluded | `SpinCore.spatialReflI_notMem_GLor` |
| orthochronicity | cone preservation is part of `IsGLorWide`; time reversal is excluded | `SpinCore.timeReflI_not_isGLorWide` |
| component | `GLor` preserves the interior future cone | `SpinCore.GLor_intFuture` (inherited) |
| kernel | `ker ρ = {1, negOneSpin} ≅ ℤ/2`, `Nat.card = 2`, `negOneSpin ≠ 1`, central, discrete | `SpinCore.mem_ker_spinCover_iff`, `spinCover_ker_card` (inherited) |
| double-cover target | the target of the native projection **is** `GLor`, and the frame cocycle is proved to land in it | `SpinCore.internalSpinProjection`, `comparison_mem_GLor` |

The bridge therefore cannot identify the native Spin group with a cover of the wrong Lorentz
component: the frame transitions are proved to lie in the proper orthochronous group that is
literally the codomain of the native projection.

---

## 10. WP10 — canonicality table

| object | classification |
|---|---|
| intrinsic carrier `𝒮`, `N_𝒮`, `B_𝒮`, cone, `GLor`, `SpinGroup`, `spinCover` | intrinsic (inherited, Tasks 1–2) |
| Task-3 cover/cocycle/defect/obstruction machinery | canonically inherited (Task 3) |
| causal sign lemmas, reduction criterion | `DERIVED_NATIVE` |
| `carrierBasis` (coordinate basis of `𝒮`) | frame choice, used only as the argument tuple of the orientation form; no theorem depends on which basis it is beyond positivity conventions |
| the cover of the frame datum | `CHOSEN_COVER` |
| the metric field | geometric datum (input) |
| the orientation form `vol` | `CHOICE_OF_ORIENTATION` |
| the time-orientation field `timeField` | `CHOICE_OF_TIME_ORIENTATION` |
| the local frames | `CHOICE_OF_LOCAL_FRAME` |
| `comparison`, `transition`, `frameCocycle` | `DERIVED_NATIVE` from the above |
| a family of local Spin lifts | choice; the **defect depends on it** |
| `frameObstruction` | invariant under the choice of local Spin lifts (`frameObstruction_choice_independent`); depends on the frame datum and cover |
| `SpinFrameStructure` | `CHOICE_OF_SPIN_STRUCTURE` |
| `spinSign` / `zToSpin` | `CANONICAL_IDENTIFICATION` (`{±1} ≅ ℤ/2`) |
| `zdefect`, `deltaZ` | `DERIVED_NATIVE` |
| the flat control datum | control only; downstream, never imported by production |

Existence of a Spin structure, choice of a Spin structure, and choice of local Spin frames are
three different levels and are kept apart formally (§5).

---

## 11. Explicit negative controls

| rejected implication | how it is rejected |
|---|---|
| `[c]_frame = 0 ⇒ TM trivial` | not derivable: nothing in the layer produces a global frame; a global frame would be a *single-patch* frame datum, and the theory is stated for arbitrary covers.  Formally unstatable as a `w₂` statement (no bundle triviality predicate); recorded as `NOT_CLAIMED` |
| `[c]_frame = 0 ⇒ unique Spin structure` | **formally refuted**: `Control.two_distinct_spinFrameStructures`, plus the torsor theorem |
| `[c]_frame = 0 ⇒ R = 0` | no connection, no curvature exists in the layer; `NOT_CLAIMED`, stated in every module docstring |
| `[c]_frame = 0 ⇒ T = 0` | idem (no solder form, no torsion) |
| `[c]_frame = 0 ⇒ gravitational vacuum` | idem (no field equation, no action) |
| `[c]_frame = 0 ⇒ synchronization equilibrium` | idem; the hypothesis paper is motivation only and is never used as a premise |
| the class is `w₂(TM)` | **not claimed**; §7 |

---

## 12. Anti-shortcut compliance

1. no import of `RequestProject.Experiment1.**` or `RequestProject.Experiment2.**` (mechanical);
2. no historical model bridge; the `SL(2,ℂ)` comparison is not in the import closure
   (mechanical, `auditForbidden "Task-4 geometry layer"`);
3. orientation and time orientation are separate fields with separate conditions, and their
   independence is proved by two negative controls;
4. a Spin structure is never inferred from local Spin lifts: coherence is an explicit,
   separate condition, and the equivalence is a theorem;
5. the Task-3 class is never called `w₂`;
6. `w₂` is not defined circularly — it is not defined at all;
7. no trivial tangent bundle is assumed;
8. no global frame is assumed (frames are constrained only on their patches);
9. no good cover is assumed anywhere; lift-admissibility is an explicit hypothesis;
10. no global hyperbolicity, no parallelizability, no flatness, no field equations;
11. the hypothesis paper is not used as proof input.

---

## 13. Build evidence

```
lake build RequestProject.Spine.E1.Core                             OK
lake build RequestProject.Spine.E1.Topology.Core                    OK
lake build RequestProject.Spine.E2.Core                             OK
lake build RequestProject.Spine.Core                                OK
lake build RequestProject.Spine.Geometry.CausalAlgebra              OK
lake build RequestProject.Spine.Geometry.FrameField                 OK
lake build RequestProject.Spine.Geometry.SpinStructure              OK
lake build RequestProject.Spine.Geometry.TangentInstance            OK
lake build RequestProject.Spine.Geometry.Z2Class                    OK
lake build RequestProject.Spine.Geometry.Core                       OK
lake build RequestProject.Spine.Controls.Geometry.FlatFrameControl  OK
lake build RequestProject.Spine.Audit.Firewall                      OK
lake build                                                          OK (8153 jobs)
```

Firewall report for the new modules (from the audit run):

```
Spine modules audited: 123
Spine direct legacy imports:   Experiment1 = 0, Experiment2 = 0
Spine transitive legacy imports: Experiment1 = 0, Experiment2 = 0
endpoint RequestProject.Spine.Geometry.Core:        transitive legacy E1 = 0, E2 = 0
endpoint RequestProject.Spine.Geometry.FrameField:  transitive legacy E1 = 0, E2 = 0
endpoint RequestProject.Spine.Geometry.SpinStructure:   transitive legacy E1 = 0, E2 = 0
endpoint RequestProject.Spine.Geometry.TangentInstance: transitive legacy E1 = 0, E2 = 0
endpoint RequestProject.Spine.Geometry.Z2Class:         transitive legacy E1 = 0, E2 = 0
endpoint RequestProject.Spine.Controls.Geometry.FlatFrameControl: E1 = 0, E2 = 0
SPINE FIREWALL AUDIT: all checks passed
```

The firewall additionally checks that no production module imports a control, that the whole
Task-4 layer avoids the `SL(2,ℂ)` comparison, the matrix model and the Pauli representation,
and that the proof closures of the new endpoints avoid every removed or control-only
constant.

---

## 14. Axiom audit

`RequestProject/Spine/Geometry/Core.lean` runs `#print axioms` on all principal Task-4
declarations.  Every one reports exactly

```
[propext, Classical.choice, Quot.sound]
```

(or "does not depend on any axioms").  No project-local axiom exists; `rg` over the Task-4
sources finds no `sorry`, `admit`, `axiom`, `unsafe`, `partial`, or `implemented_by`.

---

## 15. Fail-build ledger (append-only)

| # | command | exact diagnostic | source | diagnosis | repair | statement change |
|---|---|---|---|---|---|---|
| 1 | `lake build` | `linarith failed to find a contradiction` (CausalAlgebra.lean:72, :84) | the two causal sign lemmas | `nlinarith` could not find the Cauchy–Schwarz product chain unaided | supplied the intermediate steps explicitly (`p·q < a²b²`, then `r² < (ab)²`, then the sign of `ab`) | none |
| 2 | `lake build` | `Unknown identifier 'pos_of_mul_pos_iff.mp'`; `rewrite failed: did not find an occurrence` (FrameField.lean:191–192) | `comparison_det_eq_one` | wrong lemma name, and the alternating-form transformation law was stated in the `compLinearMap` normal form, which does not match the frame-applied form syntactically | introduced the frame-level lemma `vol_comp_det` and matched the argument tuple by an explicit `funext` rewrite; replaced the nonexistent lemma by `nlinarith` | none |
| 3 | `lake build` | `failed to synthesize instance` (FlatFrameControl.lean:51) | `trivialCover` | `Classical.arbitrary ι` used before `[Nonempty ι]` was in scope | moved the instance binder into the section `variable` line | none |
| 4 | `lake build` | `unsolved goals` (Z2Class.lean:91, :138); `application type mismatch` (:143); `rfl failed` (:174) | `spinSign_mul`, `zdefect_cocycle₂`, `zdefect_change_of_lift` | `1 + 1 = 0` in `ZMod 2` not closed by `simp`; wrong explicit/implicit argument for `defect_delta_eq_one`; `x - y = x + y` in `ZMod 2` is not `rfl` | closed the residual `ZMod 2` goals by `decide`, corrected the argument list, and added the `sub = add` rewrite | none |

No statement was weakened at any point; every repair was to a proof, an argument list or a
binder position.

---

## 16. Deliverables map

| deliverable | where |
|---|---|
| 1. native Lean implementation | `RequestProject/Spine/Geometry/{CausalAlgebra,FrameField,SpinStructure,TangentInstance,Z2Class,Core}.lean`, `RequestProject/Spine/Controls/Geometry/FlatFrameControl.lean` |
| 2. `TASK04_AUDIT.md` | this file |
| 3. dependency DAG | §1 |
| 4. availability audit | §1 |
| 5. orientation / time-orientation model | §2, `FrameField.lean` |
| 6. Lorentz frame transition cocycle | §3, `frameCocycle`, `frame_transition_laws` |
| 7. concrete Task-3 obstruction instance | §4, `frameObstruction` |
| 8. coherent lifts ⟺ Spin structure | §5, `nonempty_spinFrameStructure_iff_exists_coherent`, `frameObstruction_eq_trivial_iff_spinStructure` |
| 9. conventional `w₂` criterion | §6 — `BLOCKED`, with the exact missing infrastructure |
| 10. strongest proved identification | §7 — `VANISHING_EQUIVALENCE_ONLY` + canonical `ℤ₂`-Čech presentation |
| 11. signature / component audit | §9 |
| 12. canonicality / nonuniqueness table | §10, §5, §8 |
| 13. explicit negative controls | §11, §2 |
| 14. fail-build ledger | §15 |
| 15. build evidence | §13 |
| 16. axiom audit | §14 |
