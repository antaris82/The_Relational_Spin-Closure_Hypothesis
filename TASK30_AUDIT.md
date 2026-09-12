# Task 30 — Audit

**Outcome A.**  The Spin-native branch exists (minimally extracted from an object the project
already had), it is independent of the standard `SO`-lift branch, its projection produces
standard `SO`-transition data, and the **existing** standard obstruction of those projected
data is theorem-level trivial.  The standard branch is unchanged.

---

## 1. What was added

Three production modules and one audit check.

```
RequestProject/Spine/SpinNative/TransitionData.lean     (Branch B, level 1)
RequestProject/Spine/SpinNative/Projection.lean         (Branch B, level 2)
RequestProject/Spine/Comparison/SpinNativeVsSO.lean     (comparison layer, leaf)
RequestProject/Spine/Audit/ArchitectureDAG.lean         (check 7: the branch firewall)
```

Principal declarations:

| declaration | kind | content |
|---|---|---|
| `SpinNative.NativeSpinTransitionData` | `abbrev` | Spin-valued gluing data on a cover = the existing `CechSpinLift.VisibleCocycle` at the internal group |
| `SpinNative.native_transition_laws` | theorem | identity, inverse (derived) and cocycle laws |
| `SpinNative.project` | def | `g_ij := ρ ∘ g̃_ij`, again an exact cocycle |
| `SpinNative.proj_ker_mul` | theorem | `ρ(z·u) = ρ(u)` for `z ∈ ker ρ` |
| `SpinNative.project_eq_of_ker_factor` | theorem | kernel-valued factors are invisible after projection |
| `SpinNative.nativeLiftFamily` | def | Spin-native data are a family of local lifts of their own projection |
| `SpinNative.nativeLiftFamily_defect_eq_one` | theorem | the standard defect of that family is `1` |
| `SpinNative.nativeLiftFamily_isCoherent` | theorem | coherence in the sense of the standard branch |
| `SpinNative.projected_obstruction_trivial` | theorem | `[c] = trivialClass` for the tautological family |
| **`SpinNative.projected_obstruction_trivial_of_lifts`** | theorem | **`[c] = trivialClass` for every lift family — the principal Task-30 target** |
| `SpinNative.native_projection_square` | theorem | the packaged square (5 conjuncts) |
| `SpinCore.spin_projected_obstruction_trivial` | theorem | the same for the intrinsic Spin/Lorentz cover |
| `LorentzFrames.SpinFrameStructure.toNative` | def | forgetting the `projects` field |
| `LorentzFrames.project_toNative_eq_transition` | theorem | the projection is the frame transition, on the overlaps |
| **`LorentzFrames.project_twist`** | theorem | **`project(ε·S) = project(S)` on the overlaps** |
| `LorentzFrames.native_spin_structure_projection` | theorem | packaged Lorentz-frame endpoint |

The obstruction used is the frozen `CechSpinLift.SpinLiftFamily.obstruction` of
`RequestProject/Spine/E2/Cech/Obstruction.lean`; its definition, and the definitions of the
defect, the coboundary calculus and the `Cohomologous` quotient, were not modified.

## 2. What was **not** done

* No Nerve Theorem work.
* No identification of the obstruction with `w₂(TM)`.
* No Stage 1.4, no dynamics, curvature, torsion or RSCH closure.
* No H¹-classification, no torsor classification of Spin structures, no new (co)homology, no
  new manifold or principal-bundle theory.
* No claim that `w₂ = 0` for physical manifolds, and no claim that `w₂` is "caused by"
  information loss.
* No claim that a Spin structure reconstructed by the standard branch from `[c] = 1` recovers
  the Spin-native datum: the standard branch gives existence, not provenance.

## 3. Provenance findings

Summarised here; derived in full, with source locations, in `TASK30_PROVENANCE.md`.

1. The earliest genuinely Spin-valued primitive is `SpinCore.SpinGroup`
   (`E1/SpinGroup.lean:41`) with `SpinCore.spinCover` (`E1/SpinCover.lean:42`) — a *local
   fibre* object, prior to all `SO` transition data.
2. Before Task 30 the project contained no Spin-valued *gluing* object stated without prior
   `SO`-data: `SpinLiftFamily`, `SpinFrameStructure` and
   `CompatibleContinuousInternalTransitions` all take the `SO` datum as a parameter or
   constrain their Spin maps by a projection field.
3. The generic cocycle structure `CechSpinLift.VisibleCocycle`, however, is group-agnostic;
   the `SO`-first reading is carried by its *name* alone.  Instantiating it at the internal
   group gives the Spin-native gluing datum with no change of definition.  The `SO`-first
   architecture at that point is therefore **historical packaging, not mathematical
   necessity** — the answer to Q6.
4. The exact architectural edge is the parameter `(T : VisibleCocycle G 𝓤)` of
   `CechSpinLift.SpinLiftFamily` (`E2/Cech/LocalLifts.lean`).
5. Lost under projection: the kernel-sign/choice information (proved).  Retained: existence
   information (proved).  Global H¹-type freedom: **not** classified, not claimed.

## 4. Build and axioms

* Cold build: `rm -rf .lake/build && lake build RequestProject` →
  **`Build completed successfully (8292 jobs)`**, 0 errors.
* Both compiled audits report all checks passed (see `TASK30_CODE_HYGIENE.md` §3).
* `#print axioms` is run in `Comparison/SpinNativeVsSO.lean` on all thirteen new endpoints
  (and on the projection and the comparison arrow).  Every one reports exactly

  ```
  [propext, Classical.choice, Quot.sound]
  ```

  No `sorryAx`, no project-local axiom.
* Axiom table of the whole build: `scripts/task30_axioms_post.txt`, 1037 declarations,
  against the Task-29 baseline of 1024.  The difference is **exactly** the thirteen new
  declarations; no previously audited declaration changed profile, and the three pre-existing
  lighter profiles (`[Quot.sound, propext]` ×2, `[propext]` ×1) are unchanged.
* Metrics: `scripts/task30_metrics_post.txt`.  Maximum import depth unchanged at 67.

## 5. Stop condition

The diagram of §15 of the task is valid in the project:

```
   coherent Spin-native data   ──────────►   coherent Spin lift family (proved)
             │ ρ                                        │
             ▼                                          ▼
   SO-transition data          ──────────►   standard obstruction [c] = 0 (proved)
```

with the independent control branch `SO → local Spin lift → [c]` fully intact.  Outcome A is
reached, so Task 30 stops here; the next standard Stage-1.3 edge remains the genuine Nerve
Theorem, which was deliberately not begun.
