# TASK 37 — provenance

Task 37 had two purposes only: **(A)** freeze Task 36 by a small, low-risk refactor, and
**(B)** prepare a deformation-ready shared-transport interface for the next task.  The
deformation experiment itself was **not** performed.

---

## Part 0 — the frozen state

* Frozen source state: git commit `a0d0aa3` ("Initial commit" of this working copy), i.e. the
  repository exactly as Task 36 left it.
* Baseline build before any edit: `lake build RequestProject` — **green, 8341 jobs**, every
  architecture audit passing.
* Baseline axiom audit: the build log contains 1 248 `#print axioms` lines, 53 of them from
  the Task-36 tree; **every** Task-36 endpoint reports exactly
  `[propext, Classical.choice, Quot.sound]`.
* No theorem statement and no hypothesis of Task 36 was weakened, strengthened or deleted in
  Task 37.  The only Task-36 *statement-level* change is the replacement of one auxiliary
  library-gap lemma by a `LocalModel`-specific version (§4 below), which is the instance that
  was actually used.

---

## Part I — the freeze refactor

### 1. Import-DAG parallelisation (§2)

Before (serial chain, depth 9 to the firewall):

```text
LoopModel → OrientationGate → LoopSolder → TimeOrientation → TrivialControl
          → SpinObstruction → Certificate → Firewall
                        ↘ OrientationReversing → SpinNotLorentz → SpinFoamControl
                        ↘ SmoothBundlePackaging → GaugeGroup
```

After (parallel, depth 5 to the firewall):

```text
Solder.RegularSolder ─→ OrientationGate ─┬─→ OrientationReversing → SpinNotLorentz → SpinFoamControl
                                         ├─→ TrivialControl ──────────────────────────↗
                                         └─→ SpinObstruction (comparison join)
Solder.RegularExamples → LoopModel ─→ LoopSolder ─┬→ LoopSpinFreedom
                                                  └→ LoopTimeOrientation
Solder.OrientationTime → TimeOrientation ─────────↗
Solder.BundleEquivalence → SmoothBundlePackaging
Solder.RegularGauge     → GaugeGroup
Certificate aggregates; Firewall audits.
```

Concretely:

| module | old imports | new imports | reason |
|---|---|---|---|
| `OrientationGate` | `Task36.LoopModel` | `Solder.RegularSolder` | its theorems are general; it never used the loop model |
| `LoopSolder` | `Task36.OrientationGate` | `Task36.LoopModel` | it needs the loop model and the general solder layer, not the orientation gate |
| `OrientationReversing` | `Task36.OrientationGate` | `Task36.LoopModel`, `Task36.OrientationGate` | it genuinely needs both (Möbius model + determinant gate) |
| `TimeOrientation` | `Task36.LoopSolder`, `Solder.OrientationTime` | `Solder.OrientationTime` | the general layer must not depend on a loop model (see §3) |
| `LoopTimeOrientation` (new) | — | `Task36.LoopSolder`, `Task36.TimeOrientation` | the loop-specific control |
| `TrivialControl` | `Task36.TimeOrientation`, `SpinNative.KernelTwist` | + `Task36.OrientationGate`, `Solder.RegularExamples` | explicit, no longer inherited through a chain |
| `SmoothBundlePackaging` | `Task36.OrientationGate`, `Solder.BundleEquivalence` | `Solder.BundleEquivalence` | the orientation gate was unused |
| `GaugeGroup` | `Task36.SmoothBundlePackaging`, `Solder.RegularGauge` | `Solder.RegularGauge` | the packaging module was unused |
| `SpinObstruction` | `Task36.TrivialControl`, `Comparison.SpinNativeVsSO` | `Task36.OrientationGate`, `Comparison.SpinNativeVsSO` | it never used the one-chart control |
| `Certificate` | 5 imports | + `Task36.TrivialControl` | it aggregates; the one-chart control is no longer inherited |
| `Firewall` | 8 imports | + `Task36.LoopTimeOrientation` | audit coverage of the new module |

No umbrella module was created; production modules do not import `Certificate`.

### 2. Loop time-orientation split (§3)

`Task36.loop_timeOrientationReduction_isGlued` moved **verbatim** (statement and proof
unchanged) from `Task36/TimeOrientation.lean` to the new
`Task36/LoopTimeOrientation.lean`.  The general layer —
`TimeOrientationReduction`, `solder_timeOrientationReduction`,
`nonempty_timeOrientationReduction_of_solder` — is now loop-free.

### 3. Removal of the unnecessary `Classical` use (§4)

`Task36.continuous_det_of_continuous` (arbitrary finite-dimensional `E`, basis obtained from
`Module.Free.exists_basis`, hence `classical`) was replaced by

```text
    Task36.continuous_det_localModel
```

which uses the project's own explicit coordinate equivalence
`EmergentBase.localModelEquivFin4 : LocalModel ≃ₗ[ℝ] (Fin 4 → ℝ)` through
`Module.Basis.ofEquivFun`.  No `classical`, no `Fintype` transport, three lines shorter.  The
only consumer (`continuousOn_solderDet`) instantiated the general lemma at `E = LocalModel`,
so no mathematical content was lost.

### 4. The second `Classical` use (§5) — retained, documented

`Task36.signFun` still uses `open Classical in`; so does the new
`Task37.Deformation.loopTransportFun`.  Both are piecewise-constant functions defined by a
case split on membership in the *open, undecidable* wrap component.  Replacing this would
require a decidable characterisation of the wrap set in the quotient base — a new auxiliary
library that would obscure the control.  Both occurrences are itemised in
`TASK37_CODE_HYGIENE.md`, and the Task-36 hygiene table is corrected there.

### 5. Loop-model wording (§6)

Docstrings in `LoopModel.lean`, `LoopSolder.lean` and `LoopSpinFreedom.lean` that said
"the emergent base is (a model of) `S¹ × ℝ³`" or "a genuine noncontractible loop" were
corrected to the exact proved terminology: **periodic fixed-cover loop model**,
**two-component periodic overlap model**, **project-native loop-sign control**,
**fixed-cover `ℤ₂` lift freedom**.  No theorem statement was touched; nothing was deleted,
the corrections are inserted next to the historical wording.

### 6. Revalidation (§7)

All principal Task-36 endpoints survive the refactor and rebuild unchanged:
`classical_reconvergence`, `orientation_reversing_gluing_no_solder`,
`orientation_obstruction_nonzero_implies_no_solder`,
`spin_obstruction_nonzero_implies_no_solder`, `one_loop_has_kernel_sign_freedom`,
`fixed_cover_spin_choice_family`, `two_loop_spin_choice_family`,
`regular_solder_is_gauge_torsor`, `oneChart_positive_control`,
`loop_timeOrientationReduction_isGlued` (relocated),
`adversarial_global_topology_certificate`.  All report
`[propext, Classical.choice, Quot.sound]`.

---

## Part II — the deformation preparation

Four new modules plus one audit module under `RequestProject/Spine/Deformation/`:

| module | content |
|---|---|
| `SharedTransport.lean` | the one shared native Spin-side transport state `transportState : ℝ → SpinGroup`, its group laws, the derived `projectedTransportState`, visibility for `λ ≠ 0`, and the two-field family interface |
| `LoopSharedTransport.lean` | the `λ`-deformed native Spin transition datum `loopSharedSpin` on the frozen periodic fixed-cover loop model, with the Čech cocycle law proved, exact regression at `λ = 0`, and visibility of the deformation on the wrap component |
| `NeutralRegression.lean` | the undeformed reference family, the fixed-base smoke-test family, and the availability of the Task-36 reconvergence theorem at `λ = 0` |
| `ClosureAdmissibility.lean` | `RegularClosureSolution` / `RegularClosureAdmissible`, CONTROL A vs MAIN TEST B, the anti-vacuity controls, and the regime vocabulary |
| `Firewall.lean` | the leaf, legacy/external, shared-origin (field-list), target-leakage-token and sensitivity audits |

The scientific content, the exact audit table and the stop-condition discussion are in
`TASK37_DEFORMATION_INTERFACE.md`; the next experiment is stated in
`TASK38_SHARED_TRANSPORT_SMOKETEST_HANDOFF.md`.

---

## Final validation

* `lake build RequestProject` — green; the Spine architecture audit, the Task-36 firewall and
  the new Task-37 deformation firewall all print their pass lines.
* No `sorry`, `admit`, new `axiom`, `native_decide`, `unsafe`, `partial`, `implemented_by` or
  `Matrix.inv` in any new or edited module.
* Every new endpoint reports `[propext, Classical.choice, Quot.sound]`.
