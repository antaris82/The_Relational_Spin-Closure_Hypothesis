# TASK 36 — Audit

Section-by-section audit of the adversarial global-topology battery.  Every classification
below is either backed by a named theorem in the tree or explicitly marked as blocked, with
the exact missing result named.

Conventions used throughout:

* **DERIVED** — proved in this project, `sorry`-free, axiom-audited.
* **BLOCKED BY INFRASTRUCTURE** — mathematically standard but not expressible/provable with
  the pinned Lean 4.28.0 + Mathlib v4.28.0 and the project's current development.
* **EXTERNAL ROBUSTNESS CASE — NOT FORMALIZED** — recorded, deliberately not modelled.

---

## §1 — Repair A: smooth Lorentz bundle equivalence does not require smooth Spin transitions

**Finding: the Task-35 wording was too strong, and is corrected.**

Task 35 stated that a smooth total-space bundle equivalence "cannot be" obtained because the
native Spin cocycle is only required to be continuous.  That conflates two different things:

| | status |
| --- | --- |
| smoothness of the **projected Lorentz** transition representatives (internal Lorentz bundle smoothness) | **DERIVED** already in Task 35: `SpinNative.SmoothTangentSolderData.contDiffOn_solderLorentzRep` |
| smoothness of the **native Spin lift** itself (smooth Spin bundle structure) | separate question, §2 below |

The first is what a smooth equivalence of the *internal Lorentz bundle* with `TM` needs, and
it holds.  So the Spin cocycle is **not** the obstruction.

**Pinned-Mathlib API audit.**  `Mathlib v4.28.0` has `VectorBundleCore`, `tangentBundleCore`,
`Trivialization`, `Bundle.TotalSpace`, `ContMDiffVectorBundle` and the mixin
`VectorBundleCore.IsContMDiff`, but **no type of vector-bundle morphisms or equivalences**,
smooth or otherwise.  In addition `VectorBundleCore.IsContMDiff` asks for smoothness of the
coordinate changes as functions on the base *manifold*, whereas this project's smooth
representatives are functions of the *chart coordinate*.  There is therefore no standard
object to package the result into.

**What is proved instead (strongest correct result).**
`RequestProject/Spine/Task36/SmoothBundlePackaging.lean`:

* `Task36.internal_coordChange_eq_solderRep` — the coordinate change of the internal Lorentz
  bundle, read in the solder frames, is the projected Lorentz representative;
* `Task36.internal_bundle_coordChange_smooth_in_charts` — hence it is `C^∞` in the chart
  coordinates, with **no** hypothesis on the smoothness of the Spin lift;
* `Task36.RegularBundleCertificate` — the project-native certificate with the six items §1
  asks for, explicitly: (i) continuous total-space equivalence, (ii) continuous inverse,
  (iii) fibrewise linearity, (iv) smooth local representatives, (v) smooth local
  representatives of the inverse, (vi) the exact transition intertwining;
* `Task36.nonempty_regularBundleCertificate_iff` — this certificate exists exactly when a
  regular solder does.

**Classification.**

```text
internal Lorentz bundle smoothness in charts : DERIVED
smooth total-space packaging                 : BLOCKED BY INFRASTRUCTURE
        (missing: a (smooth) vector-bundle morphism/equivalence type in the pinned Mathlib)
```

and explicitly **not** "requires smooth native Spin transitions".  The Task-35 docstring in
`Spine/Solder/BundleEquivalence.lean` carries the correction notice.

---

## §2 — Repair B: Spin smoothness is a theorem/infrastructure problem, not a new datum

**No new primitive datum was introduced.**  `CechSpinLift.VisibleCocycle` still requires only
continuity of the Spin cocycle, and nothing in Task 36 assumes smoothness of the native Spin
lift.

**Audit of what would be needed.**  The standard route is

```text
    (a) SpinGroup is a Lie group          (smooth manifold structure on SpinGroup ≤ Cl3ˣ)
    (b) GLor is a Lie group               (smooth manifold structure on GLor)
    (c) spinCover is a smooth homomorphism with discrete kernel
    (d) hence spinCover is a smooth covering map / local diffeomorphism
    (e) continuous Spin lift + smooth projected Lorentz map + (d)  →  smooth Spin lift.
```

Steps (a) and (b) are instances of **Cartan's closed-subgroup theorem** (a closed subgroup of
a Lie group is an embedded Lie subgroup).  Audit of the pin:

| required Mathlib object | present in `v4.28.0`? |
| --- | --- |
| `LieGroup` class | yes |
| Cartan closed-subgroup theorem (charted space / `IsManifold` structure on a closed subgroup) | **no** — no `ClosedSubgroup.isLieGroup`, `Subgroup.instLieGroup`, `LieGroup.ofClosedSubgroup` or equivalent |
| "a smooth homomorphism with discrete kernel is a smooth covering map" | **no** |

Without (a) and (b) there is no `ChartedSpace`/`IsManifold` instance on `SpinGroup` or on
`GLor` at all, so (c)–(e) cannot even be stated.  The project deliberately does **not**
substitute `SL(2,ℂ)`, a matrix model or any other external realization to obtain smoothness:
the intrinsic Spin group is kept.

**Classification.**

```text
smooth native Spin lift : BLOCKED BY INFRASTRUCTURE / ADDITIONAL THEOREM
                          (missing: Cartan's closed-subgroup theorem in the pinned Mathlib,
                           and the smooth-covering-map corollary for discrete-kernel
                           smooth homomorphisms)
                          NOT an additional geometric datum.
```

---

## §3 — Repair C: time-orientation reduction versus the distinguished time field

**Finding: `timeField_glue_iff` was being over-read.**  It is the exact gluing criterion for
the *distinguished local representative* `T_i(y) = A i y (𝟙_𝒮)`, and nothing more.

**What Task 36 adds** (`RequestProject/Spine/Task36/TimeOrientation.lean`):

* `Task36.TimeOrientationReduction B` — the structural notion: a field of future cones in
  chart coordinates, preserved by the genuine tangent transitions on overlaps;
* `Task36.solder_timeOrientationReduction` / `Task36.nonempty_timeOrientationReduction_of_solder`
  — **regular solder → coherent smooth future-cone reduction on `TM`**, unconditionally;
* `Task36.loop_timeOrientationReduction_isGlued` — positive control on the one-loop model
  (nontrivial global topology): the reduction exists *and* its distinguished representative
  glues.

**Global smooth timelike representative.**  Audited and not derivable here: it needs a smooth
section of a field of open convex cones over a paracompact smooth manifold (partition of
unity).  The pinned Mathlib has the partition-of-unity machinery for functions into a vector
space, but the project's `TM` is presented at the `VectorBundleCore` level, with no smooth
section API and no smooth-bundle structure on it (see §1), so the standard argument cannot be
assembled.

**Classification.**

```text
time-orientation reduction            : DERIVED
global smooth timelike representative : ADDITIONAL THEOREM / INFRASTRUCTURE BLOCKER
```

Failure of `A_i(sOne)` to glue is **not** failure of time orientability, and no statement in
the tree says otherwise.  The clarification notice is in `Spine/Solder/OrientationTime.lean`.

---

## §4 — Gauge action packaging

Completed, in `RequestProject/Spine/Task36/GaugeGroup.lean`, without touching Task-35
statements:

| §4 item | status |
| --- | --- |
| identity | `Task36.gaugeOne` |
| composition | `Task36.gaugeMul` |
| inverse | `Task36.gaugeInv` (smoothness of the inverse field **derived**: `Task36.contDiffOn_gauge_symm`) |
| group laws | `Group (SpinNative.RegularTangentGauge B)` instance |
| `act_one` | `Task36.act_one` |
| `act_mul` | `Task36.act_mul` |
| preservation of regular solder data | the `MulAction` instance itself |
| strongest standard torsor notion | `Group` + `MulAction` + `MulAction.IsPretransitive` + freeness, bundled in `Task36.regular_solder_is_gauge_torsor` |

The pinned Mathlib has **no multiplicative torsor class** (`AddTorsor` is additive), so the
wording used everywhere remains "**free and transitive regular gauge action**".

---

## §5 — Primitive-input / target-leakage audit

See `TASK36_PROVENANCE.md` §5 for the full dependency certificate (what is primitive, where
the fourth real direction enters, where `BaseGluingData`, `M = Space B`, `TM`, the solder and
the global orientation/Spin conditions first appear).  Mechanically enforced by
`Spine/Audit/Firewall.lean`, `Spine/Audit/ArchitectureDAG.lean` and
`Spine/Task36/Firewall.lean`.

---

## §6 — Trivial positive control

`Task36.oneChart_positive_control` proves, at the exact project-native level: smooth gluing;
`IsManifold`; pointwise trivial Spin lift; existence of a regular solder; orientation
compatibility **as a consequence** of the solder; existence of a time-orientation reduction
whose distinguished representative glues; and that every kernel 1-cocycle on this cover is
pointwise trivial, i.e. no artificial family of global sign choices is generated by the local
model.

**Not claimed:** uniqueness of the Spin structure.  No classification theorem relating
contractibility to uniqueness is proved in this project, so none is invoked.

---

## §7 — One-loop gluing control

`Task36.loopGluing = Task36.loopGluingOf Unit LoopTwist.id'` is a genuine four-dimensional
model: two slabs of the local model `ℝ ⊕ ℝ³` glued along two disjoint overlap components, one
of which is the wrap-around, producing one noncontractible loop.  It is a smooth gluing and
its emergent base is a `C^∞` four-manifold.

* `Task36.nonempty_solder_loopGluing` — the model has a regular solder;
* `Task36.one_loop_has_kernel_sign_freedom` — two native Spin data over the **same** projected
  Lorentz transition system, both regularly soldered, that are **not** gauge equivalent, the
  difference being the kernel sign `negOneSpin` around the loop.

Deliberately **not** claimed: that the two lifts are physically distinct.  The statement is
about inequivalence at exactly the gauge-equivalence relation the project implements
(`SpinNative.GaugeEquiv`).

---

## §8 — `N`-torus / `H¹`-like multiplicity control

`Task36.fixed_cover_spin_choice_family` — for `κ` independent loops the sign choices
`κ → Bool` inject into gauge classes of native Spin data over one and the same projected
Lorentz transition system, each of them regularly soldered.
`Task36.two_loop_spin_choice_family` instantiates `N = 2` with `2² = 4` classes.

**Explicit caveat, as §8 requires:**

```text
THIS IS THE PROJECT'S FIXED-COVER H¹-LIKE CONTROL,
NOT YET A THEOREM IDENTIFYING IT WITH GLOBAL H¹(T^N; ℤ₂).
```

The base is a disjoint family of `κ` loop models, not a literal `T^N`; the project has no
smooth-quotient construction of `T^N` and no comparison theorem between its fixed-cover Čech
classes and singular `H¹`.  The test's purpose — detecting accidental canonization — is met:
the bottom-up construction does **not** erase the other classes.

---

## §9 — Orientation-reversing / Möbius-type negative control

`Task36.moebiusGluing = Task36.loopGluingOf Unit LoopTwist.flip` uses an explicit linear
wrap-around twist with `LinearMap.det = -1` (`Task36.det_flipEquiv`).

`Task36.orientation_reversing_gluing_no_solder :
IsEmpty (SmoothTangentSolderData moebiusGluing S)` for **every** native Spin datum `S`.

**The gate.**  The proof uses only the determinant law of the solder
(`Task36.Solder.solderDet_law`, itself a consequence of `projectedLorentzTransition_det = 1`)
together with constancy of the sign of a nowhere-zero continuous function on a connected chart
domain.  No lift family, no triple overlap and no kernel cocycle occurs.  This obstruction is
**not** described as `w₂` anywhere.

---

## §10 — Independent Spin-lifting / triple-overlap negative control

In the single comparison module `RequestProject/Spine/Task36/SpinObstruction.lean`:

* `Task36.smooth_solder_implies_spin_obstruction_trivial` — regular solder → the tangent
  Lorentz transition cocycle read in the solder frames **is** the projected native Spin
  cocycle → it carries the native Spin lift → its project-native Čech obstruction class is
  trivial, for **every** family of local lifts;
* `Task36.spin_obstruction_nonzero_implies_no_native_lift` — the strong contrapositive;
* `Task36.spin_obstruction_nonzero_implies_no_solder` — the requested corollary.

**Naming discipline.**  The class used is the project-native
`CechSpinLift.SpinLiftFamily.obstruction` in `CechSpinLift.ObstructionClass`.  The project
contains **no** formal identification of that class with `w₂(TM)` and none is asserted.  The
missing comparison theorem is named in §11.

---

## §11 — Classical reconvergence

`Task36.classical_reconvergence` :

```text
SmoothTangentSolderData B S
    →  orientation obstruction = 0   (determinant 1-cocycle is a continuous
                                      nowhere-vanishing coboundary)
    ∧  Spin lifting obstruction = 0  (project-native Čech class = trivialClass)
```

with the two independent contrapositives
`Task36.orientation_obstruction_nonzero_implies_no_solder` and
`Task36.spin_obstruction_nonzero_implies_no_solder`.

Neither `w₁ = 0` nor `w₂ = 0` is assumed anywhere; both conclusions are consequences of the
regular solder.

**Why the statement is not written with `w₁`/`w₂`.**  Audit of the pin:

| required object | present in Mathlib `v4.28.0`? |
| --- | --- |
| Stiefel–Whitney classes, `w₁`, `w₂` | **no** |
| mod-2 cohomology of a smooth manifold with the comparison to Čech classes of a good cover | not in the form needed |

The project *does* have its own Čech/`ℤ₂` machinery (`Spine.Cech.**`, `Spine.Cohomology.**`,
`Spine.GoodCover.**`), but the theorem identifying its obstruction class with `w₂(TM)` of the
tangent bundle of `Space B` is **not** formalized.  Writing `w₂(TM) = 0` would therefore be an
analogy, and it is not written.

```text
MISSING COMPARISON THEOREM:
    project-native obstruction class of the tangent Lorentz transition system
        =  w₂(TM)   in  H²(Space B; ℤ/2)
    and the analogous degree-1 statement for the determinant cocycle and w₁(TM).
```

This is the exact reason Task 36 lands at **PASS-B** rather than PASS-A (see §25 below).

---

## §12 — `S⁴` separation test

**Audited first, as required, and not assumed.**  The standard statement is: `S⁴` is a smooth
closed simply-connected 4-manifold, hence orientable and Spin, and it admits Riemannian
metrics; it admits **no** Lorentz metric because `χ(S⁴) = 2 ≠ 0` and a Lorentz metric on a
closed manifold forces a nowhere-zero line field, hence `χ = 0`.

Audit of the pin:

| required object | present? |
| --- | --- |
| Euler characteristic of a smooth manifold | **no** |
| Poincaré–Hopf / nowhere-zero vector field criterion | **no** |
| Lorentzian metrics on a manifold | **no** |
| Spin structures on a smooth manifold | **no** (project-native notion only) |
| Stiefel–Whitney classes | **no** |

§12 explicitly forbids reimplementing that topology library here, so:

```text
concrete S⁴ instantiation : BLOCKED BY INFRASTRUCTURE — NOT a theorem-level pass
```

**Strongest conditional theorem proved instead**
(`RequestProject/Spine/Task36/SpinNotLorentz.lean`):

* `Task36.spin_does_not_imply_lorentz_conditional` — over any base gluing whose tangent
  determinant cocycle admits no continuous nowhere-vanishing trivialization, native Spin
  transition data exist while no native Spin datum admits a regular solder;
* `Task36.spin_does_not_imply_lorentz_moebius` — a concrete witness: a smooth emergent
  four-manifold that carries native Spin transition data and **no** regular solder.

**Honest caveat.**  In the concrete witness the failure is at the **orientation** gate, not at
the Euler-characteristic gate.  It establishes "native Spin transition data ⇏ regular Lorentz
solder", which is the structural lesson of §12, but it is **not** the `S⁴` theorem and is not
reported as one.

---

## §13 — `E8`-type gate-separation audit

**Audit target, not a premise.**  The object usually meant is Freedman's closed simply
connected topological 4-manifold with intersection form `E8`.  The relevant standard facts
are: it is a topological manifold; its intersection form is even and unimodular, which is the
sense in which it is "Spin" in the topological category; by Rokhlin's theorem it admits no
smooth structure; by Casson's work it is not triangulable.

Establishing that the five claims *non-smooth*, *non-triangulable*, *Spin*, *no Spin
connection*, *no Dirac operator* hold simultaneously for one and the same object under one
and the same set of definitions requires Freedman's classification, Rokhlin's theorem and a
topological-category notion of Spin structure.  None of these, and no part of the required
4-manifold topology, exists in the pinned Mathlib or in this project.

```text
E8-type case : EXTERNAL ROBUSTNESS CASE — NOT FORMALIZED
```

No unrelated smooth manifold is substituted.  The structural lesson that is *kept* — Spin or
topological lift data alone must not imply smooth geometry, a connection or a Dirac operator —
is enforced in this project by the curvature claim firewall of §15 and by the fact that
nothing in the tree derives a connection or a Dirac operator from any lift datum.

---

## §14 — Spin-foam gate separation

"Spin foams carry spin" is **not** "a manifold has a Spin structure on `TM`".  The distinction
is made at the level of types and theorems in
`RequestProject/Spine/Task36/SpinFoamControl.lean`:

* `Task36.SpinFoamLabels V` — a minimal spin-labelled combinatorial complex: vertices, a
  symmetric adjacency relation, and a `SpinGroup`-valued label on each ordered pair.  No
  topology, no cover, no local model, no continuity requirement, no cocycle law;
* `Task36.spinFoamLabels_unconstrained` — the labels satisfy no constraint whatsoever, so they
  cannot encode a gluing condition, in contrast with `CechSpinLift.VisibleCocycle`, which is
  defined over an actual cover and is required to be continuous and to satisfy the
  triple-overlap cocycle law;
* `Task36.spin_foam_labels_do_not_determine_solder` — for **every** spin foam there are, quite
  independently of its labels, both a smooth emergent four-manifold with a regular solder and
  a smooth emergent four-manifold with none.

**Not claimed:** that no object called a spin foam can ever underlie or encode a manifold.
The theorem is exactly the §14 robustness target and no more.

---

## §15 — Flat topology control / claim firewall

At this stage the project has **no connection and no curvature structure**, so no zero-curvature
theorem is added and none is faked.

**Mechanical claim firewall** (`Spine/Task36/Firewall.lean`, check 4): the audit scans every
declaration of `RequestProject.Spine.**` — 6119 declarations at the final build — and fails to
compile if any of them is named with `curvature`, `Curvature`, `Riemann`, `holonomy`,
`Holonomy`, `connection` or `Connection`.  None is.  Consequently no theorem in the tree can
infer curvature from `BaseGluingData`, from nontrivial fundamental loops, from Spin kernel
signs or from regular soldering.

The nontrivial-gluing example with flat *local* Lorentz geometry does exist
(`Task36.loopGluing`: locally the transitions are translations and the identity on tangents,
`Task36.tangentTransitionMap_loop_id`, with a regular solder), but the word "flat" is used
only in the sense "the tangent transitions are the identity", never as a curvature statement.

```text
curvature statement : NOT YET DEFINED — deferred to the later connection stage
```

---

## §16 — Globally-hyperbolic / product positive control

The recollection to be verified was: physically usual orientable 3-manifold Cauchy surfaces
are parallelizable hence Spin, so products `ℝ × Σ` supply a broad positive class.

The mathematical statement "every closed orientable 3-manifold is parallelizable"
(Stiefel) is standard and correct.  But the pin has none of the machinery required to state,
let alone use, it: no parallelizability predicate for manifolds, no Stiefel–Whitney classes,
no product formula for characteristic classes, no Lorentzian metrics, no global hyperbolicity,
no Cauchy surfaces.  The project itself has no construction of a smooth manifold from an
abstract 3-manifold, only its own `BaseGluingData` route.

```text
ℝ × Σ positive class : EXTERNAL ROBUSTNESS CASE — NOT FORMALIZED
                       (blocked: parallelizability of oriented 3-manifolds, product
                        behaviour of the obstruction classes, Lorentzian metrics,
                        global hyperbolicity — none available)
```

Two things are explicitly **not** inferred anywhere in the tree: global hyperbolicity from a
product topology, and a Lorentz metric from Spin.

The positive controls that *are* proved take the place of this test in the matrix: the
one-chart control (§6) and the one-loop control (§7).

---

## §17 — Non-canonicity / choice-freedom audit

Every declaration added since the native-Spin selection and solder stages whose name or
docstring uses *canonical*, *unique*, *distinguished* or *natural*, classified:

| declaration / wording | classification |
| --- | --- |
| `SpinNative.Canonical.**`, `Comparison.CanonicalSpinSeed.**` — the canonical native representative of a gauge class | **CANONICAL ONLY AFTER EXTRA DATA / FIXED-COVER CHOICE**: canonical *inside* one selected construction on one fixed cover, not a statement about the manifold |
| `SpinNative.SmoothTangentSolderData` — the solder field `A` | **GAUGE-DEPENDENT**: `SpinNative.SmoothTangentSolderData.not_unique`, and the free transitive action of §4; no solder is canonical |
| the "distinguished" time field `T_i(y) = A i y (𝟙_𝒮)` | **GAUGE-DEPENDENT / FIXED-COVER CHOICE**: it depends on the solder, and its gluing is a property of *that* representative (§3) |
| `Task36.TimeOrientationReduction` produced by a solder | **CANONICAL ONLY AFTER EXTRA DATA**: determined by the solder, which is itself gauge-dependent; but *existence* is theorem-level (`nonempty_timeOrientationReduction_of_solder`) |
| `Task36.twistedSpin σ` | **NOT CANONICAL** by design: the whole point of §§7–8 |
| `EmergentBase.LocalModel` as "the canonical local model" | **THEOREM-LEVEL CANONICAL** relative to the primitive core: it is literally the primitive carrier, no choice is made |
| `Task36.RegularBundleCertificate` | **CANONICAL ONLY AFTER EXTRA DATA**: determined by the solder it is built from |

**Regression test, as §17 requires.**  The canonical-representative results and the
multiplicity results coexist in one build: `Task36.fixed_cover_spin_choice_family` and
`Task36.one_loop_has_kernel_sign_freedom` are theorems in the same environment as the
canonical-seed machinery.  A canonical representative *inside one construction* therefore
demonstrably does not erase the inequivalent global classes when the base topology permits
them.  No FAIL-CANONICITY condition is triggered.

---

## §18 — Pair-overlap / triple-overlap wording audit and dependency diagram

The external heuristic "pairwise ↔ orientation/`w₁`, triple ↔ Spin/`w₂`" is **not** copied into
any theorem name.  The actual Čech degrees implemented are:

```text
    tangent transition functions  B.tangentTransitionMap i j          (pairwise, degree 1 data)
              │
              │  det  (Task36.Solder.solderDet, solderDet_law)
              ▼
    determinant 1-cocycle on double overlaps
              │
              │  Task36.smooth_solder_implies_orientation_compatible
              ▼
    orientation reduction: the 1-cocycle is a continuous nowhere-vanishing coboundary
              │
              │  [ MISSING COMPARISON THEOREM ]
              ▼
    w₁(TM) = 0                                                        (NOT FORMALIZED)


    chosen local Spin lifts   CechSpinLift.SpinLiftFamily             (pairwise lifts)
              │
              │  defect on triple overlaps
              ▼
    kernel 2-cocycle          (degree 2 data)
              │
              ▼
    obstruction class         CechSpinLift.SpinLiftFamily.obstruction
              │
              │  Task36.smooth_solder_implies_spin_obstruction_trivial
              ▼
    obstruction = trivialClass
              │
              │  [ MISSING COMPARISON THEOREM ]
              ▼
    w₂(TM) = 0                                                        (NOT FORMALIZED)
```

Indexing check: the orientation statement is a statement about pairs `(i, j)` and a 0-cochain
`a : ι → LocalModel → ℝ`; the lifting obstruction is a statement about triples `(i, j, k)` and
a 1-cochain of local lifts.  The degrees are those of the implementation; no re-indexing
occurs anywhere in Task 36.

---

## §21 — Import firewall

`RequestProject/Spine/Task36/Firewall.lean` fails to compile unless all of the following hold
(output of the final green build quoted):

1. **Task 36 is a leaf** — "199 non-Task-36 Spine modules checked, 0 of them reach
   `RequestProject.Spine.Task36`".  The frozen bottom-up construction is therefore completely
   independent of the adversarial battery.
2. **Bottom-up adversarial modules avoid the top-down branch** — "11 bottom-up adversarial
   modules reach none of the 6 top-down obstruction prefixes"
   (`Spine.E2.Cech.Obstruction`, `Spine.Geometry`, `Spine.Cech`, `Spine.Cohomology`,
   `Spine.GoodCover`, `Spine.Comparison`).
3. **The comparison module is genuinely a comparison** — `Task36.SpinObstruction` reaches both
   `Spine.Solder.RegularSolder` and `Spine.E2.Cech.Obstruction` (positive control; without it
   check 2 would be vacuous).
4. **Curvature claim firewall** (§15).
5. **Zero legacy / zero external** for all 13 Task-36 modules.

The forbidden shape `bottom-up production module → Task36 → top-down w₁/w₂ branch` is
excluded by checks 1 and 2 together.

---

## §25 — Stop condition reached

**PASS-B — PROJECT-NATIVE RECONVERGENCE.**

* The regular bottom-up solder is proved to imply the classical orientation compatibility and
  the triviality of the Spin-lifting obstruction (`Task36.classical_reconvergence`).
* The orientation-reversing control is rejected at the **orientation** gate
  (`Task36.orientation_reversing_gluing_no_solder`) and a nontrivial lifting obstruction is
  rejected at the **triple-overlap** gate
  (`Task36.spin_obstruction_nonzero_implies_no_solder`) — independently, by different
  mechanisms.
* Nontrivial Spin-choice freedom survives where expected
  (`Task36.one_loop_has_kernel_sign_freedom`, `Task36.fixed_cover_spin_choice_family`), so
  there is no FAIL-CANONICITY.
* The three Task-35 overstatements of §§1–3 are repaired, and the §4 gauge packaging is
  complete.
* The final identification of the project-native classes with standard `w₁`/`w₂`, and the
  concrete exotic examples `S⁴` (§12), `E8` (§13) and `ℝ × Σ` (§16), are blocked by
  pinned-Mathlib infrastructure; every blocker is named exactly above.

No FAIL-STRUCTURAL condition arose: no certified adversarial target admits
`SmoothTangentSolderData` where it should not.  **STOP-EXOTIC** applies to §§13 and 16 (and to
the concrete instantiation of §12), which are recorded as external robustness cases without
substituting easier objects.

### Answer to the final scientific question

After the bottom-up route `ℝ³ → intrinsic Clifford/Spin/Lorentz core → base gluing → smooth M
→ regular solder → TM`, the classical global restrictions and choice freedoms **do** reappear
at the correct gates, and they were not inserted into the primitive local input:

* an orientation-type obstruction re-emerges at the level of *pairwise* tangent transitions,
  and it alone kills the orientation-reversing gluing;
* a Spin-lifting-type obstruction re-emerges at the level of *triple* overlaps, independently,
  and a nontrivial one alone kills the solder;
* `H¹`-type `ℤ/2` freedom re-emerges wherever the base gluing has a noncontractible loop, and
  the bottom-up construction does not canonize it away.

What is **not** claimed is that these project-native classes have been identified with
`w₁(TM)` and `w₂(TM)`; that comparison theorem is the principal outstanding item.

---

## CORRECTION NOTICE (Task 37 §6) — loop-model terminology

Nothing above is deleted.  Where this document (and the Task-36 module docstrings) described
the emergent base of `Task36.loopGluingOf κ LoopTwist.id'` as "a model of `S¹ × ℝ³`" with "one
noncontractible loop", the exact proved content is weaker and is now stated in those terms
everywhere:

* **periodic fixed-cover loop model** — two slabs of the local model glued along a
  **two-component periodic overlap**, one component of which is the wrap-around;
* **project-native loop-sign control** and **fixed-cover `ℤ₂` lift freedom** for the residual
  `±1` freedom of §§7–8.

The project proves **neither** `Space B ≅ S¹ × ℝ³` **nor** `π₁(Space B) ≠ 0`, and no proof uses
either statement; establishing them would require fundamental-group and product-space
infrastructure that has not been built.  Task 37 is a freeze refactor and deliberately did not
expand topology.
