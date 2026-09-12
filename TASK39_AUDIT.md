# TASK 39 — audit of the documentation against the current source

Part X of the Task-39 specification: every principal documentation claim was checked against
the **current** Lean source, not against earlier task summaries.  Classification vocabulary:

```text
MATCHES SOURCE | WORDING TOO STRONG | WORDING TOO WEAK | STALE | DUPLICATED | MISSING | HISTORICAL ONLY
```

Baseline recorded before any edit (Part I §1):

| item | value |
| --- | --- |
| Lean | `leanprover/lean4:v4.28.0` |
| Lake | `5.0.0-src+7e01a1b` |
| Mathlib | pinned `v4.28.0` (`lake-manifest.json`) |
| full build command | `lake build RequestProject` |
| pre-Task-39 build | **green, 8352 jobs**, run before any modification |
| post-Task-39 build | **green, 8356 jobs** (four new modules, 794 lines: `Deformation/SmoothProjectedGauge.lean` 144, `Deformation/SolderTransport.lean` 265, `Closure/IntermediateMilestone.lean` 271, `Closure/AxiomAudit.lean` 114) — *corrected by Task 40: this line previously said "three new modules", which miscounted the audit module; the counts above are computed from the current tree (`wc -l`), see `TASK40_RELEASE_HARDENING_AUDIT.md` ISSUE-40-06* |
| Task-36/37/38 source tree | unmodified by Task 39, except for the audit-only firewall extension recorded in §5 below |
| Task-38 outcome | **C — universally admissible and gauge absorbable on the tested control** |

---

## 1. Known historical risk areas (Part X §34)

| # | risk area | verdict | evidence in the current source |
| --- | --- | --- | --- |
| 1 | "regular solder is a gate, not universally available" | **MATCHES SOURCE** | `Task36.orientation_reversing_gluing_no_solder` proves non-existence for the Möbius model; `Task37.Deformation.not_forall_regularClosureAdmissible` proves there is no universal existence theorem. All solder-dependent statements in the new certificate are implications with hypothesis `Nonempty (SmoothTangentSolderData B S)`. |
| 2 | "smooth Lorentz bundle equivalence does not require falsely postulating smooth Spin transitions" | **MATCHES SOURCE** | `SpinNative.smooth_solder_iff_regular_bundle_equivalence` states continuity of the total-space maps and `ContDiffOn ℝ ⊤` of the *local representatives* only. The module docstring says explicitly why a smooth bundle equivalence is not available. The fact sheet and README repeat the exact regularity. **TASK-41 CORRECTION (post-Task-40 review, ISSUE-41-01):** the original Task-39 wording of this cell attributed the missing strong packaging to "a merely continuous Spin cocycle". That is the obsolete Task-35 explanation, superseded by the correction notice in `Spine/Solder/BundleEquivalence.lean` and by `Spine/Task36/SmoothBundlePackaging.lean`: a regular smooth solder already gives smooth local/projected Lorentz transition representatives, and the residual blocker is an infrastructure / packaging limitation. The historical verdict of this row is otherwise unchanged. |
| 3 | "Spin smoothness remains an infrastructure/theorem-level issue" | **MATCHES SOURCE**, and now sharper | There is no `LieGroup`/`ContMDiff` structure on `SpinCore.SpinGroup` anywhere. Task 39 §4 added `contDiffOn_loopProjectedGauge`, which is about the **projected** gauge only; its docstring states in full that the Spin-side gauge stays continuous. Recorded as [CLAIM-B001] and `OP-001`. |
| 4 | "distinguished time-field gluing is not identical to general time-orientability" | **MATCHES SOURCE** | `Task36.TimeOrientationReduction` is a chartwise future-cone structure; no theorem relates it to a standard Lorentzian time orientation. Recorded as [CLAIM-B006] and `OP-010`. |
| 5 | "fixed-cover `H¹`-like freedom is not automatically `H¹(M; ℤ₂)`" | **MATCHES SOURCE** | `Task36.two_loop_spin_choice_family` is a `Fintype.card (Fin 2 → Bool) = 4` statement on a fixed cover; no refinement limit is taken anywhere. Recorded as [CLAIM-B005]. |
| 6 | "project-native Spin obstruction is not automatically `w₂`" | **MATCHES SOURCE** | `Task36/SpinObstruction.lean` says so in its docstring; `Spine/Core.lean` and `Comparison/SpinNativeVsSO.lean` repeat it; no Stiefel–Whitney class exists in the repository. Recorded as [CLAIM-B002] and `OP-006`. |
| 7 | "periodic fixed-cover model is not automatically `S¹ × ℝ³`" | **MATCHES SOURCE** | `Task36/LoopModel.lean` contains the Task-37 wording correction verbatim and states that neither the homeomorphism nor any `π₁` statement is proved or used. Recorded as [CLAIM-B004] and `OP-009`. |
| 8 | "Task-38 gauge result is scoped to the tested family/control" | **MATCHES SOURCE**; wording corrected by Task 39 | The theorems quantify over `l₁ l₂ : ℝ` for `loopSharedSpin` over `loopGluingOf κ LoopTwist.id'`. Every Task-39 document states the scope explicitly, and `PAPER_I_DO_NOT_CLAIM.md` §6 forbids the universal phrasing. |
| 9 | "Task-38 metric equality has exactly the scope the source proves" | **WORDING TOO WEAK before Task 39; now MATCHES SOURCE** | Task 38 proved equality for the explicit witnesses `loopParaSolder` only. Task 39 §5 added `loopSolderEquiv` and `tangentMetric_loopSolderTransport`, so the certified statement is now a bijection of the whole regular solution space with the metric preserved — still on the frozen control. Both the narrow and the strengthened statement are recorded ([CLAIM-S008], [CLAIM-S010]). |
| 10 | "connection/holonomy/curvature are still absent" | **MATCHES SOURCE** | A repository-wide search finds no definition of a connection, a transport form, a holonomy, a field strength or a Riemann tensor; the deformation-branch firewall additionally rejects such tokens in declaration names. Recorded as [CLAIM-B003]. |

## 2. Claim-by-claim audit result

All 64 registered claims were checked against the source.  Summary:

| verdict | count | notes |
| --- | --- | --- |
| MATCHES SOURCE | 62 | recorded with their supporting theorem IDs in `docs/machine/CLAIM_REGISTRY.jsonl` |
| WORDING TOO WEAK (repaired by proving more) | 1 | the Task-38 metric comparison, see risk area 9 — now [CLAIM-S010] |
| WORDING TOO STRONG (repaired by scoping) | 1 | the informal phrase "transition-cocycle deformations are pure gauge" that appeared in earlier handoff prose is replaced everywhere by the scoped [CLAIM-S011] wording; the forbidden phrasing is listed in `PAPER_I_DO_NOT_CLAIM.md` §6 |
| STALE / DUPLICATED / MISSING | 0 | — |
| HISTORICAL ONLY | the per-task `TASK*_AUDIT.md`, `TASK*_FAILBUILDS.md`, `TASK*_PROVENANCE.md` files | retained unchanged; they are the authoritative record of their own task |

No theorem statement was changed in order to make documentation easier, and no documentation
claim was retained that the source does not support.

## 3. What Task 39 added to the mathematics

Two strengthenings, both small, both using only already available explicit formulas:

* `RequestProject/Spine/Deformation/SmoothProjectedGauge.lean` (§4) — the projected Lorentz
  gauge of the smoke test, written in chart coordinates, is proved equal to the native
  projection of the Task-38 Spin gauge and `C^∞` on every chart domain.
* `RequestProject/Spine/Deformation/SolderTransport.lean` (§5) — transport of an **arbitrary**
  regular solder solution along that gauge; the regular solution spaces at two parameter values
  are in explicit bijection and the induced tangent Lorentz metric is preserved.

Both are inside the existing deformation leaf branch, use no new assumption, and introduce no
new physical target.  The §5 result is exactly the upgrade the specification allowed: it did
not require new infrastructure, so the weaker wording was not used.

## 4. The closure certificate

`RequestProject/Spine/Closure/IntermediateMilestone.lean` aggregates only already certified
results.  Blocked or merely documented claims are **not** conjuncts.  Every solder-dependent
conjunct is an implication with hypothesis "a regular solder exists".

`RequestProject/Spine/Closure/AxiomAudit.lean` runs `#print axioms` on all 62 registry
endpoints; see `TASK39_AXIOM_AUDIT.md`.

## 5. Audit-only change to an existing module

`RequestProject/Spine/Deformation/Firewall.lean` was extended (audit code only, no mathematics):

* the two new deformation modules were added to the audited module list, and the sensitivity
  threshold was raised from 9 to 11 modules;
* the closure branch `RequestProject.Spine.Closure` was made exempt from the
  deformation-leaf check — it aggregates certified endpoints and therefore must import them;
* a **new check 7** requires the closure branch to be a leaf in turn: no production or frozen
  module may reach it, so nothing can reach the deformation branch through the closure branch.

Both checks pass: `deformation leaf audit: 209 non-deformation Spine modules checked, 0 of them
reach RequestProject.Spine.Deformation`; `closure leaf audit: 220 non-closure Spine modules
checked, 0 of them reach RequestProject.Spine.Closure`.

## 6. Final verification state

| check | result |
| --- | --- |
| `lake build RequestProject` | **PASS**, 8356 jobs |
| `RequestProject.Spine.Audit.Firewall` | PASS (`SPINE FIREWALL AUDIT: all checks passed`) |
| `RequestProject.Spine.Audit.ArchitectureDAG` | PASS (`SPINE ARCHITECTURE AUDIT: all checks passed`) |
| `RequestProject.Spine.Task36.Firewall` | PASS |
| `RequestProject.Spine.Deformation.Firewall` | PASS, including the new closure-leaf check |
| `RequestProject.Spine.Closure.AxiomAudit` | PASS, 62 endpoints, all `[propext, Classical.choice, Quot.sound]` |
| `python3 audit/verify_documentation_snapshot.py` | PASS |

**TASK 39 — INTERMEDIATE PROJECT CLOSURE: PASS / FROZEN.**
