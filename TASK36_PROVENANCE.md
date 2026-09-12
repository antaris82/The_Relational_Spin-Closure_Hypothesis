# TASK 36 — Provenance

Adversarial global-topology battery and Task-35 closure repairs.

Date: 2026-09-12.  Toolchain and dependencies unchanged: Lean `4.28.0`, single dependency
`mathlib` at tag `v4.28.0` (commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`, Apache 2.0).
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json` are byte-identical to their
Task-35 state.  No external Lean project was imported, read or depended on.

---

## 0. Frozen Task-35 baseline

* Frozen commit: `a3e3e7a` ("Initial commit"), the green Task-35 state as received.
* Baseline build at that commit: `lake build RequestProject` — **green, 8327 jobs**, with
  `SPINE ARCHITECTURE AUDIT: all checks passed`.
* `#print axioms` on the Task-35 principal endpoints at that commit: every one reports
  `[propext, Classical.choice, Quot.sound]`.
* **No Task-35 theorem statement was modified by Task 36.**  The only edits to pre-existing
  Lean files are appended *docstring* correction/clarification notices (§§1–4 below); the
  original wording is preserved verbatim above each notice.
* The adversarial branch depends on the frozen bottom-up branch and never the reverse; this is
  enforced mechanically (§21).

## Final Task-36 state

* `lake build RequestProject` — **green, 8341 jobs**, architecture audit passed, zero errors.
* `#print axioms` is run on every Task-36 endpoint inside the sources: **53 audits**, all
  reporting `[propext, Classical.choice, Quot.sound]`.
* `rg` over `RequestProject/Spine/Task36/`: no `sorry`, no `admit`, no `axiom`, no
  `native_decide`, no `unsafe`, no `partial`, no `implemented_by`, no `Matrix.inv`, and no
  `simp`, `simpa` or `Classical` anywhere.

---

## Modules added by Task 36

All new modules live in `RequestProject/Spine/Task36/`.

| Module | Section | Content |
| --- | --- | --- |
| `LoopModel.lean` | §§7, 9 | the four-dimensional periodic/Möbius base-gluing models `loopGluingOf κ t`, `loopGluing`, `moebiusGluing`; smoothness and `IsManifold`; the tangent-transition computations and the shared test points |
| `OrientationGate.lean` | §§9, 11, 20 | the determinant field of a regular solder and the **orientation gate** `smooth_solder_implies_orientation_compatible`, with its contrapositive |
| `OrientationReversing.lean` | §9, 20 | `orientation_reversing_gluing_no_solder` |
| `LoopSolder.lean` | §7 | the regular solder of the one-loop model |
| `LoopSpinFreedom.lean` | §§7, 8, 20 | the kernel sign cocycles, the twisted Spin seeds, `one_loop_has_kernel_sign_freedom`, `fixed_cover_spin_choice_family`, `two_loop_spin_choice_family` |
| `TimeOrientation.lean` | §3 | `TimeOrientationReduction` and `solder_timeOrientationReduction` |
| `TrivialControl.lean` | §6 | the one-chart positive control |
| `SpinObstruction.lean` | §§10, 11, 20 | the **comparison** module: the Spin-lifting gate, both contrapositives, `classical_reconvergence` |
| `SmoothBundlePackaging.lean` | §1 | `RegularBundleCertificate` and `nonempty_regularBundleCertificate_iff` |
| `GaugeGroup.lean` | §4 | the `Group`/`MulAction` packaging of `RegularTangentGauge`, free and transitive |
| `SpinNotLorentz.lean` | §12 | the project-native Spin/Lorentz separation (conditional and concrete) |
| `SpinFoamControl.lean` | §14 | the spin-labelled combinatorial control object and the gate separation |
| `Certificate.lean` | §20 | the bundled `adversarial_global_topology_certificate` |
| `Firewall.lean` | §§15, 21 | the mechanical import firewall and the curvature claim firewall |

## Pre-existing Lean files edited (docstrings only)

| File | Section | Edit |
| --- | --- | --- |
| `Spine/Solder/BundleEquivalence.lean` | §1 | appended `CORRECTION NOTICE (Task 36 §1)`: smooth total-space packaging is blocked by infrastructure, **not** by the continuity of the native Spin cocycle |
| `Spine/Solder/OrientationTime.lean` | §3 | appended `CLARIFICATION NOTICE (Task 36 §3)`: `timeField_glue_iff` is the gluing criterion of the distinguished representative, not an obstruction to time orientability |
| `Spine/Solder/RegularGauge.lean` | §4 | appended `UPDATE NOTICE (Task 36 §4)`: the gauge action is now packaged as `Group` + `MulAction` + pretransitivity + freeness |

No statement, hypothesis or proof in any pre-existing file was changed.

---

## §5 — Primitive-input and target-leakage dependency certificate

This is the anti-target-leakage audit required by §5.  It records **mathematical dependency
provenance only**; no claim of historical discovery order is made or formalized.

### What is primitive

| Object | Module | Import closure |
| --- | --- | --- |
| `SpinCore.LorentzCarrier := ℝ × (Fin 3 → ℝ)` | `Spine/E1/Carrier.lean` | `Mathlib` **only** |

The root module imports `Mathlib` and nothing else.  It defines the Euclidean inner product
`sip` on the `ℝ³` factor, the Jordan product, the unit, the intrinsic trace `strS`, the
quadratic form `NS`, its polarization `BS`, the cone `ConeS` and the real coordinate
equivalence `spinToVec`.

### Where the extra real direction enters

The primitive Euclidean root is the rank-three spin factor `ℝ³` with its Euclidean inner
product.  The **fourth real direction is the Jordan-algebra scalar direction of the spin
factor itself**: the carrier is the Jordan algebra `ℝ ⊕ ℝ³` generated by the `ℝ³` root, and
the `ℝ` summand is its unit line, not an additional input.  The Lorentz signature is not
posited either: it is the intrinsic quadratic form `NS` of that Jordan algebra.

So the split is

```text
    primitive Euclidean root                :  ℝ³ with sip
    Jordan algebra generated by it          :  ℝ ⊕ ℝ³            (the unit line is the ℝ)
    intrinsic quadratic form on it          :  NS                (Lorentz signature, derived)
    local four-dimensional model            :  EmergentBase.LocalModel := SpinCore.LorentzCarrier
```

### The dependency chain, module by module

| Question of §5 | Answer | Module |
| --- | --- | --- |
| What is primitive? | `SpinCore.LorentzCarrier` and its Jordan/Clifford structure | `Spine/E1/Carrier.lean` (imports `Mathlib` only) |
| What is explicitly constructed from it? | the Clifford algebra, the intrinsic `SpinGroup ≤ Cl3ˣ`, the Lorentz action `spinLor`, the proper group `GLor`, the covering `spinCover` and its kernel | `Spine/E1/**` |
| Where is the four-dimensional local model first named? | `EmergentBase.LocalModel` — an *abbreviation* of the primitive carrier; still no manifold, chart, atlas, base point or cover in its closure | `Spine/Emergent/LocalModel.lean` |
| Where are `BaseGluingData` introduced? | `EmergentBase.BaseGluingData` — the first place where *several* copies of the local model and identification maps exist | `Spine/Emergent/BaseGluing.lean` |
| Where does `M = Space B` first exist? | `EmergentBase.Space B := Quotient B.setoid`; smoothness of the atlas and `IsManifold` come one module later | `Spine/Emergent/Reconstruction.lean`, `Spine/Emergent/SmoothStructure.lean` |
| Where does `TM` first enter? | `tangentBundleCore localModelI (Space B)` and its coordinate changes `tangentTransitionMap` | `Spine/Emergent/TangentTransition.lean` |
| Where does the solder first couple the internal bundle to `TM`? | `SpinNative.TangentSolderData` (weak, Task 34) and `SpinNative.SmoothTangentSolderData` (regular, Task 35) | `Spine/Solder/Solder.lean`, `Spine/Solder/RegularSolder.lean` |
| Where do global orientation / Spin conditions first become *meaningful*? | only once transitions over a cover exist: the orientation statement first has content in `Task36.OrientationGate`, the lifting obstruction first has content in `Task36.SpinObstruction` | `Spine/Task36/**` |

### No leakage at the root

At the `ℝ³` root there is **no** global four-manifold, **no** Lorentz metric on a manifold,
**no** tangent bundle, **no** `Spin(TM)`, **no** orientation and **no** characteristic class:
the import closure of `Spine/E1/Carrier.lean` is `Mathlib` alone, and the closure of
`Spine/Emergent/LocalModel.lean` consists of `Mathlib` and `Spine.E1` modules only.  The
mechanical statement of this is the pre-existing architecture audit
(`Spine/Audit/Firewall.lean`, `Spine/Audit/ArchitectureDAG.lean`), extended by
`Spine/Task36/Firewall.lean` for the Task-36 boundary.

Conversely, the orientation and Spin-lifting conditions of §§9–11 are *conclusions* of
Task 36, never hypotheses: no module of the bottom-up chain mentions them, which is exactly
what the leaf audit of `Spine/Task36/Firewall.lean` check 1 certifies.
