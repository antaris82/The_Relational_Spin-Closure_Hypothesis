# TASK 38 — code hygiene

Scope: the five new modules of the Task-38 fixed-base smoke test, all inside the existing
`RequestProject/Spine/Deformation/` leaf branch.

```text
ProjectedParaAction.lean        closed form of the projected shared transport state
FixedBaseSmokeTest.lean         admissibility locus, explicit compensating regular solder
CocycleGaugeOrbit.lean          full-group cocycle gauge equivalence, the explicit gauge
TangentMetricComparison.lean    comparison of the induced tangent Lorentz metrics
SmokeTestCertificate.lean       interface certificate, first-order control, final certificate
```

## Prohibited constructs — none present

| construct | occurrences in the new modules |
| --- | --- |
| `sorry` | 0 |
| `admit` | 0 |
| new `axiom` | 0 |
| `native_decide` | 0 |
| `unsafe` | 0 |
| `partial` | 0 |
| `implemented_by` | 0 |
| `Matrix.inv` | 0 |

Verified by `rg` over the five files and by the `#print axioms` block at the end of each
module: every endpoint reports `[propext, Classical.choice, Quot.sound]`.

## Discouraged tactics

| tactic | occurrences | note |
| --- | --- | --- |
| `simp` / `simpa` | 0 | one `simp only` was introduced while developing `continuous_transportElem` and was removed before completion, in favour of an explicit `funext` rewrite |
| `decide` | 7 | only on closed statements about `Fin 3` / `Bool` indices (e.g. `(1 : Fin 3) ≠ 0`, the case split of a `Fin 3` index, `Bool` inequalities) |
| `omega` | 0 | |
| `linarith` | 18 | numeric slab bounds of the frozen periodic model, the same style as the frozen Task-36 modules |
| `norm_num` | 2 | nonemptiness of the two slabs of a loop |

## Localized `Classical` use — one inherited instance, documented

`Task37.Deformation.loopAngle` (in `FixedBaseSmokeTest.lean`) opens `Classical` for a case split
on membership in the open wrap-around component, which is not a decidable predicate.  This is
**the same, and only the same** localized exception that the frozen `Task36.signFun` and
`Task37.Deformation.loopTransportFun` already carry: `loopAngle` is deliberately written with
the identical `if … then … else` shape so that
`loopTransportFun_eq_transportState` can be proved by a single `split`.  The case split never
enters a mathematical hypothesis: the value is `l`, `-l` or `0`.  No other `Classical` use was
added.

## Style

* Every new declaration carries a docstring tagged `NEWLY DEFINED (Task 38)` or
  `DERIVED (Task 38)`, matching the existing convention of the branch.
* No `exact?`, `apply?`, `aesop` or leftover no-op tactic remains.
* No declaration name contains a banned token; the mechanical token audit of
  `Spine/Deformation/Firewall.lean` scans all 225 declarations of the branch and passes.
* Every `set_option` in the new modules matches the ones already used by the branch
  (`synthInstance.maxHeartbeats 400000`, `maxHeartbeats 1000000`); no linter is disabled
  anywhere.
* No frozen module was edited.  The only edit outside the new files is the extension of the
  audited-module list of the branch firewall, recorded in `TASK38_FAILBUILDS.md`.
