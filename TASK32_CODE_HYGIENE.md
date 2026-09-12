# TASK 32 — code hygiene report

> ### Task-33/34 correction notice (added by Task 34; the Task-32 text below is preserved verbatim)
>
> This document is **historical provenance** for Task 32.  Four of its statements have since
> been corrected or superseded; the original wording is left untouched, and each correction
> is also annotated inline where it occurs.
>
> 1. **"minimal" / "the minimal missing primitive".**  What is proved about
>    `EmergentBase.BaseGluingData` is: *an explicit sufficient base-gluing primitive;
>    cross-piece incidence / identification information is irreducibly additional;
>    field-by-field or universal minimality of `BaseGluingData` is not proved.*
>    (Task 33; `Emergent/LocalPieceData.lean`.)
> 2. **"unique up to canonical homeomorphism" (symmetric sector).**  Task 32 proved the
>    *existence* of a homeomorphism.  Task 33 constructed a distinguished intrinsic-coordinate
>    comparison with identity / inverse / composition coherence and upgraded it to a canonical
>    diffeomorphism (`Emergent/SymmetricCanonical.lean`, `Emergent/SymmetricSmooth.lean`).
> 3. **The smooth gate.**  Task 32 did not close the smooth-manifold gate.  Task 33 proved
>    `SmoothGluing → IsManifold` for the actual reconstructed atlas
>    (`BaseGluingData.isManifold_of_smoothGluing`).
> 4. **"requires solder form" (row 22 / §5).**  Still correct as a statement about Task 32,
>    and now *resolved* by Task 34: the required datum is `SpinNative.TangentSolderData`, the
>    coupling is proved **not** derivable from the Task-32/33 data
>    (`SpinNative.tangent_spin_base_data_do_not_force_transition_identification`), and with the
>    solder datum the tangent Lorentz frame cocycle equals the projected native Lorentz
>    cocycle (`TangentSolderData.projected_eq_tangentFrameTransition`).  See
>    `TASK34_PROVENANCE.md`.
>
> Every `Ȟ¹` statement in this document is a **fixed-cover Čech `Ȟ¹`** statement about the
> **specific symmetric full-overlap emergent cover**.  It is not `H¹(M;ℤ₂) = 0`, and it is not
> a theorem for arbitrary emergent bases.


## Module and line counts

| | before Task 32 | after Task 32 | delta |
|---|---|---|---|
| `RequestProject/Spine` modules | 272 | 281 | +9 |
| `RequestProject/Spine` lines | 53 941 | 55 227 | +1 286 |
| files edited (pre-existing) | — | 1 (`Spine/Audit/ArchitectureDAG.lean`) | +~70 lines |

New modules (lines):

| module | lines | role |
|---|---|---|
| `Spine/Emergent/LocalModel.lean` | 79 | base-free 4-dimensional Clifford/Lorentz local model |
| `Spine/Emergent/BaseGluing.lean` | 181 | the minimal base-gluing primitive and its equivalence relation |

> **Task-33/34 correction.**  Read "the minimal base-gluing primitive" in the table above as
> *an explicit sufficient base-gluing primitive*: cross-piece incidence / identification
> information is irreducibly additional, but field-by-field or universal minimality of
> `BaseGluingData` is not proved.  The module is 193 lines after the Task-33 documentation
> repair.
>
> **Task-34 hygiene note on `partial`.**  Statements of the form "no `partial`" in the
> task-level hygiene reports are about *new production modules*.  The repository does contain
> historical `partial def` declarations in the audit infrastructure
> (`Spine/Audit/Firewall.lean`, the import-closure walker); no mathematical statement depends
> on them.  The precise current claim is: **no new Task-34 production module introduces
> `partial`.**
| `Spine/Emergent/Reconstruction.lean` | 251 | quotient, open quotient map, charts, Hausdorff, second countability, charted space |
| `Spine/Emergent/Symmetric.lean` | 174 | the symmetric ("null") sector and its canonical quotient |
| `Spine/Emergent/NonDerivability.lean` | 149 | the disjoint sector and the non-derivability theorem |
| `Spine/Emergent/SmoothGate.lean` | 92 | change-of-chart law and the exact remaining smoothness condition |
| `Spine/Emergent/CoverAdapter.lean` | 88 | **adapter**: emergent base → existing Čech-cover interface |
| `Spine/Cech/FullNerve.lean` | 76 | `Ȟ¹(U;ℤ₂) = 0` on a full-nerve cover (generic Čech addition) |
| `Spine/Comparison/EmergentSpinGate.lean` | 196 | comparison join: Spin seed over an emergent base, `Ȟ¹` gate closed |

No module exceeds 300 lines; no file was split, none needed splitting.

## New internal dependency edges

```
E1.SpinCover  ──▶ Emergent.LocalModel ──▶ Emergent.BaseGluing ──▶ Emergent.Reconstruction
                                                                     │
                                                                     ▼
                                                             Emergent.Symmetric
                                                              │        │      │
                        ┌─────────────────────────────────────┘        │      └────────────┐
                        ▼                                              ▼                   ▼
              Emergent.CoverAdapter ◀── E2.Cech.Cover        Emergent.NonDerivability  Emergent.SmoothGate
                        │                                              │
                        └──────────────┬───────────────────────────────┘
                                       ▼
Cech.Cohomology ─▶ Cech.FullNerve ─▶ Comparison.EmergentSpinGate ◀── Comparison.CanonicalSpinSeed
```

Nine new edges in total (one per new module, plus the two extra imports of the comparison
join and the adapter).  `Spine/Audit/ArchitectureDAG.lean` gains two imports, which is
audit-only and outside the production DAG.

## Maximum import depth

The deepest new production chain is

`E1.Carrier → … → E1.SpinCover → Emergent.LocalModel → Emergent.BaseGluing →
Emergent.Reconstruction → Emergent.Symmetric → Emergent.CoverAdapter →
Comparison.EmergentSpinGate`

Measured maximum project-internal import depth (longest chain of `RequestProject` modules):

| module | depth | project modules in closure |
|---|---|---|
| `Cech.FullNerve` | 3 | 3 |
| `Emergent.Symmetric` | 15 | 22 |
| `Emergent.NonDerivability`, `Emergent.SmoothGate` | 16 | 23 |
| `Emergent.CoverAdapter` | 22 | 47 |
| `Comparison.EmergentSpinGate` | 32 | 84 |

For comparison, the pre-existing Task-31 endpoint `Comparison.CanonicalSpinSeed` has depth 31
and closure 76, so the comparison join adds one level and eight modules to the deepest
pre-existing chain.

## Closure size of the principal endpoints

| endpoint | project modules in its import closure |
|---|---|
| `EmergentBase.symmetric_emergent_manifold` (`Emergent/Symmetric.lean`) | 22 (19 of them in `Spine/E1`, 3 emergence modules) |
| `EmergentBase.base_not_determined_by_local_pieces` (`Emergent/NonDerivability.lean`) | 23 |
| `SpinNative.emergent_seed_certificate` (`Comparison/EmergentSpinGate.lean`) | 84 (the Spin-native, Čech and obstruction stack it compares against) |

The base-free half of the layer therefore has a genuinely small closure: it does not drag in
any Čech, obstruction, Nerve or frame-geometry module.

## Refactors performed

None was required.  Nothing was renamed, moved or rewritten:

* the existing cover interface `CechSpinLift.CechCover` is *reused* through the adapter
  rather than duplicated;
* the existing Čech `ℤ₂` complex is *reused*; the only addition is the missing
  full-nerve vanishing lemma, placed in the existing `Spine/Cech` area;
* the Task-30/31 statements (`CanonicalSpinSeed`, kernel twist, gauge equivalence, rigidity
  gate) are used unchanged, and no file of those layers was edited;
* no duplicate wrapper was introduced merely to rename an existing object — `LocalModel` is
  an `abbrev` for the existing `SpinCore.LorentzCarrier`, and `NativeSpinTransitionData` is
  still the pre-existing cocycle structure.

## Branch-firewall checks (mechanical, in `Spine/Audit/ArchitectureDAG.lean`, §9)

Negative controls (must not reach):

* each of `Emergent.LocalModel`, `Emergent.BaseGluing`, `Emergent.Reconstruction`,
  `Emergent.Symmetric`, `Emergent.NonDerivability`, `Emergent.SmoothGate` must reach **no**
  module of `Spine.E2`, `Spine.Cech`, `Spine.Geometry`, `Spine.Nerve`, `Spine.GoodCover`,
  `Spine.Cohomology`, `Spine.AlgebraicTopology`, `Spine.SpinNative`, `Spine.Comparison`,
  `Spine.Controls`;
* `Emergent.CoverAdapter` must reach no obstruction module (`E2.Cech.Defect`,
  `E2.Cech.Coboundary`, `E2.Cech.LocalLifts`, `E2.Cech.Obstruction`, `E2.Cech.SpinInstance`,
  `E2.Cech.Core`), no frame geometry, no Nerve/GoodCover/Čech module, no Spin-native module
  and no comparison module;
* the pre-existing check "the comparison layer is a leaf" now also covers
  `Comparison.EmergentSpinGate`: no production module imports it.

Positive controls (must reach — so no check can pass vacuously):

* `BaseGluing → LocalModel`, `Reconstruction → BaseGluing`, `Symmetric → Reconstruction`,
  `NonDerivability → Symmetric`, `SmoothGate → Symmetric`;
* `LocalModel → E1.SpinCover` (the layer really rests on the Clifford/Spin core);
* `CoverAdapter → E2.Cech.Cover` and `CoverAdapter → Emergent.Symmetric`;
* `Comparison.EmergentSpinGate → {Emergent.CoverAdapter, Emergent.NonDerivability,
  Cech.FullNerve, SpinNative.Rigidity, Comparison.KernelTwistCohomology}`.

All checks pass; the audit prints
`Task-32 manifold-emergence firewall audited: 6 base-free modules + 1 adapter + 1 comparison
join; illegal edges: 0` and `SPINE ARCHITECTURE AUDIT: all checks passed`.

## Library growth policy

No general differential-topology library was started.  The only generic additions are the
base-gluing primitive with its reconstruction (which is the subject of the task) and one
Čech lemma.  No connection, transport, holonomy, curvature, metric or dynamics appears in
any new module or in any new import closure.
