# TASK 34 — code hygiene report

## Module and line counts

| | after Task 33 | after Task 34 | delta |
|---|---|---|---|
| `RequestProject/Spine` modules | 285 | 291 | +6 |
| `RequestProject/Spine` lines | 56 145 | 57 601 | +1 456 |
| files edited (pre-existing) | — | 2 | one audit module, one documentation-only edit |

New modules:

| module | lines | role |
|---|---|---|
| `Spine/Emergent/TangentTransition.lean` | 224 | the genuine tangent transitions of the Task-33 emergent manifold: `D(φ_ij)`, its invertibility, and the identification with Mathlib's `tangentBundleCore` coordinate change for the actual atlas; the explicit anti-shortcut record |
| `Spine/Solder/InternalLorentz.lean` | 200 | the internal Lorentz transition of an emergent Spin seed and all its inherited invariance/Čech/regularity laws |
| `Spine/Solder/Independence.lean` | 189 | the smooth rescaling two-chart base gluing and the main non-derivability theorem |
| `Spine/Solder/Solder.lean` | 385 | `TangentSolderData`, the tangent Lorentz metric and its well-definedness, non-vacuity, and the exact residual gauge freedom |
| `Spine/Solder/LorentzBundle.lean` | 160 | the associated internal Lorentz `VectorBundleCore` and the fibrewise intertwining |
| `Spine/Comparison/SolderTangentGate.lean` | 239 | the only join with the top-down branch: derived tangent frame data, the comparison square, the native Spin lift |

Edited pre-existing files:

| file | change |
|---|---|
| `Spine/Audit/ArchitectureDAG.lean` | firewall: check 9 extended by `Emergent.TangentTransition`; new check 10 for the four `Spine.Solder` modules and the comparison join; one exemption list widened, with the reason in the source |
| `Spine/Emergent/Symmetric.lean` | documentation only: item 6 of `symmetric_emergent_manifold` no longer says "canonically homeomorphic"; it says what is proved (existence, via an arbitrary index) and points at the Task-33 canonical/diffeomorphic statements |

No module exceeds 385 lines; no file needed splitting.

## Style and forbidden constructs

* `rg -n 'sorry|admit|native_decide|unsafe|implemented_by|^axiom |partial def'` over the six
  new modules returns **nothing**.
* **`partial`, precisely.**  The repository does contain `partial def` declarations — they
  are in the audit infrastructure (`Spine/Audit/Firewall.lean`, the import-closure walker),
  where a partial fixpoint over the module graph is the natural implementation and where no
  mathematical statement depends on them.  The correct statement is therefore: **no new
  Task-34 production module introduces `partial`**, and no Task-34 theorem depends on a
  `partial` definition.  The blanket phrase "no `partial` exists" would be false for the
  repository as a whole and is not used.
* No `set_option linter… false`, no `nolint`.  Every linter warning raised during development
  (unused `simp` arguments, dead `norm_num`, unused binder) was fixed at the source; see
  `TASK34_FAILBUILDS.md` F5 and F10.
* No new `axiom`.  `#print axioms` runs inside every new module on every principal endpoint
  and reports exactly `[propext, Classical.choice, Quot.sound]`.
* Two `set_option … maxHeartbeats` lines follow the pre-existing convention of the
  Spin-native and comparison layers; no other options are set.

## Naming

New names are prefixed by their subject (`tangentTransition…`, `projectedLorentzTransition…`,
`TangentSolderData…`, `internalLorentzBundleCore`) and live in the existing namespaces
`EmergentBase` and `SpinNative`.  One namespace clash was found and resolved by
qualification rather than renaming: both `SpinCore` and `LorentzFrames` export a
`carrierBasis`, and the comparison module is the first to open both.

## Deliberate structural choices

* `TangentSolderData` has exactly one data field and one law.  Regularity of the frame
  *comparisons* is derived, not assumed; regularity of the frames themselves is deliberately
  not required, and the consequences of that choice are recorded in `TASK34_AUDIT.md` §4.
* The bottom-up branch does not import `Spine.Geometry.CausalAlgebra` either, although that
  module is pure carrier algebra: the small facts needed there (`BS` bilinearity,
  nondegeneracy) are proved locally from `SpinCore.BS_eq`, keeping the firewall check simple
  and prefix-based.

---

# TASK-35 CORRECTION NOTICE (2026-09-12)

During the Task-35 hygiene pass, four `simp`/`simpa` calls introduced by Task 34 in production
modules (`Spine/Solder/Solder.lean` ×2, `Spine/Solder/Independence.lean` ×2) were replaced by
explicit structural proofs.  The remaining Task-34 occurrences are itemised, with the reason
each was kept, in `TASK35_CODE_HYGIENE.md` §4.  No statement was changed.
