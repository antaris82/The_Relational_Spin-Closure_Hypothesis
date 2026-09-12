# TASK 41 — release snapshot repair: audit

**Scope.** Task 40 is a completed historical task.  A post-Task-40 review found **four**
narrowly scoped defects in the release snapshot / documentation infrastructure.  Task 41
repairs exactly those four and regenerates the frozen snapshot.  No mathematics was added,
removed or altered: **no Lean source file under `RequestProject/` was modified** (verified by
`git status` / `git diff --stat` over that tree), no theorem statement, no hypothesis and no
construction of Tasks 36–40 was touched, and no new research branch was opened.

Task-40 history is preserved as written.  Task 41 records the true chronology: Task 40
completed; a post-release review then found four snapshot defects; Task 41 repaired them.

---

## 1. Frozen baseline (recorded before any edit)

| item | value |
| --- | --- |
| repository commit at start | `d162016` (`git log --oneline`, single-commit history) |
| Lean | `leanprover/lean4:v4.28.0` (`lean-toolchain`) |
| Lake | `Lake version 5.0.0-src+7e01a1b (Lean version 4.28.0)` |
| Mathlib | `v4.28.0` (`lake-manifest.json`) |
| build command | `lake build RequestProject` |
| pre-Task-41 build | **green**, 8356 jobs |
| pre-Task-41 validator | `python3 audit/verify_documentation_snapshot.py` → `DOCUMENTATION SNAPSHOT: all checks passed` |
| pre-Task-41 registry counts | claims 67, theorems 67 (definition 2, theorem 65), objects 46, modules 58, controls 11, open problems 12, failbuilds 174, provenance events 17, claim IDs cited in prose 67 |
| pre-Task-41 manifest state | canonical documents 8, sentinel-checked documents 7, **hashed files 379, hash mismatches 0** |
| Task-40 release label | `TASK 40 — INTERMEDIATE RELEASE HARDENING: PASS / FROZEN` |

The mathematical production source was confirmed unchanged before Task 41 (the whole tree is at
the recorded commit; the Task-40 audit is its own record).  Task 41 preserves the existing
`lake build RequestProject` result and every principal theorem endpoint.

---

## ISSUE-41-01 — smooth-bundle causal explanation

**Original defect.** Parts of the release documentation had reintroduced the older,
already-corrected Task-35 claim that *strong smooth Lorentz bundle equivalence is blocked
because the native Spin cocycle is only continuous*.

**Mathematical source used** (read, not remembered):

* `RequestProject/Spine/Solder/BundleEquivalence.lean` — the Task-35 paragraph is preserved for
  provenance and is immediately followed by the **CORRECTION NOTICE (Task 36 §1)**: the Task-35
  wording "conflates two different things", since Task 35 itself proves
  `SpinNative.SmoothTangentSolderData.contDiffOn_solderLorentzRep`, and "what actually blocks
  the packaging is **infrastructure, not mathematics**", with the classification
  `smooth total-space packaging: BLOCKED BY INFRASTRUCTURE`;
* `RequestProject/Spine/Task36/SmoothBundlePackaging.lean` — the same correction, plus
  `Task36.internal_coordChange_eq_solderRep`,
  `Task36.internal_bundle_coordChange_smooth_in_charts`, the certificate
  `Task36.RegularBundleCertificate` and `Task36.nonempty_regularBundleCertificate_iff`, and the
  exact missing infrastructure (no vector-bundle morphism/equivalence type in the pinned
  Mathlib; `VectorBundleCore.IsContMDiff` is stated over the base manifold while the solder
  supplies `ContDiffOn` in chart coordinates).

**Final distinction now carried by the release.**

* CERTIFIED — a regular smooth solder gives smooth local/projected Lorentz transition
  representatives and the corresponding smooth Lorentz-side data required by the project-native
  regular-solder construction.
* NOT THE BLOCKER — smoothness of the native Spin cocycle is *not* required merely to obtain
  smooth projected Lorentz bundle data.
* CURRENT STRONG-PACKAGING BOUNDARY — the stronger total-space smooth vector-bundle-equivalence
  package is an **infrastructure / packaging limitation**.
* OVERCLAIM GUARD — smooth projected Lorentz data is **not** a fully packaged smooth intrinsic
  Spin Lie-group bundle theory; neither is evidence for the other.

**Affected files and exact repair.**

| file | repair |
| --- | --- |
| `docs/mathematics/GLOBAL_MATHEMATICS.md` (Stage 7) | the "Exact regularity" bullet rewritten: certified smooth projected Lorentz data, infrastructure/packaging boundary, explicit overclaim guard |
| `docs/paper/PAPER_I_FACT_SHEET.md` §4 | the [CLAIM-G008] caveat rewritten in the same terms, naming `contDiffOn_solderLorentzRep` and `internal_bundle_coordChange_smooth_in_charts` |
| `docs/paper/PAPER_I_DO_NOT_CLAIM.md` | entry 12 rewritten; new entry 12b forbids the obsolete causal sentence explicitly |
| `docs/machine/CLAIM_REGISTRY.jsonl` (CLAIM-G008) | `forbidden_stronger_reading` rewritten: infrastructure/packaging limitation, the obsolete causal explanation explicitly forbidden, and the projected-Lorentz / Spin-Lie-group distinction stated; `scope` updated |
| `docs/machine/THEOREM_REGISTRY.jsonl` (THM-G008) | `overclaim_guard` rewritten in `audit/build_theorem_registry.py` and regenerated |
| `INTERMEDIATE_MILESTONE_README.md` §7 | the bundle-equivalence bullet carries the corrected boundary |
| `PROJECT_INTERMEDIATE_HANDOFF.md` ("strongest regular-solder theorem") | same correction |
| `TASK39_AUDIT.md` row 2 | historical verdict kept; an explicit **TASK-41 CORRECTION** note replaces the obsolete causal clause (history not rewritten) |
| `README.md` §Task 35 | the causal clause replaced by the Task-36 correction, with a pointer to the source module |
| `audit/verify_documentation_snapshot.py` | five new overclaim sentinels reject the wording in any canonical document |

Theorem statements changed? **NO** — assumptions changed? **NO** — production architecture
changed? **NO** — release schema changed? **NO** (documentation and sentinels only).
Final validation: documentation validator **PASS**.

---

## ISSUE-41-02 — `supporting_theorem_ids` semantics

**Original defect.** `CLAIM-S010` listed definition IDs inside `supporting_theorem_ids`.
Audited against source (`RequestProject/Spine/Deformation/SolderTransport.lean`) and registry:

| id | Lean name | kind in source | role |
| --- | --- | --- | --- |
| THM-S017 | `Task37.Deformation.loopSolderTransport` | `def` | construction |
| THM-S018 | `Task37.Deformation.loopSolderEquiv` | `def` | construction |
| THM-S019 | `Task37.Deformation.tangentMetric_loopSolderTransport` | `theorem` | support |
| THM-S020 | `Task37.Deformation.loopSolderSolutionSpace_correspondence` | `theorem` | support |
| THM-S021 | `Task37.Deformation.loopSolderTransport_involutive` | `theorem` | support (was registered but not listed by the claim) |

**Exact repair.**  `CLAIM-S010.supporting_theorem_ids = ["THM-S019", "THM-S020", "THM-S021"]`;
the two definitions are referenced by the new optional field
`supporting_construction_ids = ["THM-S017", "THM-S018"]`.  The claim's `scope` says so in
words.  `THEOREM_REGISTRY` was **not** renamed and no other claim was migrated.

**Validator rule added** (applies to *all* claims): every ID in `supporting_theorem_ids` must
resolve to a registered declaration whose `declaration_kind` is `theorem` or `lemma`; every ID
in `supporting_construction_ids` must resolve to a registered declaration that is *not* of such
a kind.  Confirmed to fire on the pre-repair registry (`TASK41_FAILBUILDS.md` F3).
`docs/machine/PROJECT_INDEX.tsv` and `docs/machine/VERIFICATION_DAG.json` were regenerated; the
definitions remain visible in the verification DAG under the new edge kind `uses_construction`.
`docs/paper/PAPER_I_FACT_SHEET.md` §7 lists the theorem support and names the constructions
separately.

Theorem statements changed? **NO** — assumptions changed? **NO** — production architecture
changed? **NO** — release schema changed? **YES** (one new *optional*, backwards-safe claim
field, documented in `docs/machine/REGISTRY_SCHEMA.md`).
Final validation: documentation validator **PASS**.

---

## ISSUE-41-03 — `statement_text` extraction

**Original defect.** `THM-G004`
(`EmergentBase.BaseGluingData.tangentTransition_eq_derivative_baseTransition`) was registered
with a truncated statement ending at `haveI : IsManifold localModelI 1 (Space B)`: the
extractor treated the `:=` of a term-level binder *inside the result type* as the end of the
signature, so the registered statement contained no conclusion at all.

**Mathematical source used.** `RequestProject/Spine/Emergent/TangentTransition.lean:153–163`
(read directly): the result type opens with
`haveI : IsManifold localModelI 1 (Space B) := (isManifold_of_smoothGluing h).of_le …` and ends
with `… = B.tangentTransitionMap i j y`.

**Exact repair.** `audit/lean_statement.py` now counts depth-zero term-level binders
(`have`, `haveI`, `let`, `letI`, `suffices`) and skips exactly one depth-zero `:=` per binder
before accepting one as the body delimiter; `--` line comments are ignored, and a trailing
` by` terminates only when no binder is pending.  This is structural scanning only: **no Lean
parser, no new dependency, no semantic reading of proof bodies.**

**Mandatory regression case.** `audit/test_statement_extraction.py` checks that the extracted
statement of `tangentTransition_eq_derivative_baseTransition` contains
`= B.tangentTransitionMap i j y`, the `tangentBundleCore … .coordChange` term and the internal
`haveI … :=`, and that it does not stop at the `haveI` header.  The old extractor produced
exactly that truncated output, so the test fails on it (evidence in `TASK41_FAILBUILDS.md` F1).
The test also exercises four synthetic fixtures (`haveI :=`, `let :=`, a plain statement and a
bracketed `let` inside a lambda) and re-extracts **every** registered declaration.

**Regeneration.** All 67 `statement_text` entries were regenerated with
`python3 audit/build_theorem_registry.py`; THM-G004 was not patched by hand, and it is the only
entry whose text changed (verified by a field-by-field diff against the pre-Task-41 file).

**Conservative sanity checks** (`lean_statement.statement_problems`, enforced by the validator
and by the regression test): nonempty statement; the statement opens with the declaration
keyword and the declared name; every extracted line occurs in the declared source file; a
theorem statement extends beyond its header; the known regression declaration contains its
terminal conclusion.  Each entry carries an explicit `statement_extraction_status` ∈
`{OK, UNRELIABLE}`, so an unreliable extraction is *marked*, never replaced by an invented
statement.  Current state: **67 OK, 0 UNRELIABLE**.

Theorem statements changed? **NO** (the Lean source is untouched; only the copied text in the
registry is now complete) — assumptions changed? **NO** — production architecture changed?
**NO** — release schema changed? **YES** (the new `statement_extraction_status` field).
Final validation: extraction regression **PASS**, documentation validator **PASS**.

---

## ISSUE-41-04 — selected `cle 0` control direction

**Original defect.** The Task-37/38 native one-parameter family was presented as an ordinary
canonical derived local structure, although it is not asserted to be the unique, canonical or
exhaustive deformation direction.

**Mathematical source used.** `RequestProject/Spine/Deformation/SharedTransport.lean`:
`transportElem l = algebraMap ℝ Cl3 (cosh (l/2)) + sinh (l/2) • cle 0`,
`transportState l = mkSpin (isSpinElem_transportElem l)`, with the module docstring stating that
the family is built "from the explicit paravector generator `SpinCore.cle 0`".  The family is
therefore built from the intrinsic Spin/Clifford core — that is certified — but through one
**selected** spatial generator.

**Required wording, now carried by the release.**

> The Task-37/38 deformation is a deliberately selected one-parameter subgroup generated by the
> chosen Clifford direction `cle 0`.  It is a control slice through the intrinsic Spin
> structure, not a theorem that this direction is canonical, exhaustive, or the full
> deformation space.

**Affected files and exact repair.**

| file | repair |
| --- | --- |
| `docs/machine/OBJECT_REGISTRY.jsonl` (OBJ-031, OBJ-032, OBJ-033) | new fields `selection_status: SELECTED_CONTROL`, `exhaustive: false`, `selection_note` naming `cle 0`; interpretation/notes updated |
| `docs/machine/CLAIM_REGISTRY.jsonl` (CLAIM-L010) | new fields `canonical_status: SELECTED_CONTROL`, `exhaustive: false`; `detailed_claim` names `cle 0`; `scope` and `forbidden_stronger_reading` state the control status and forbid the canonical / unique / exhaustive readings |
| `docs/machine/PROJECT_STATE.json` | the family moved from `derived_local_structures` to `control_specific_data`, labelled `DERIVED_CONTROL_CONSTRUCTION`; `smoketest_result.deformation_direction` records the selected direction and `exhaustive = false` |
| `docs/mathematics/LOCAL_MATHEMATICS.md` §8 | retitled and opened with the classification paragraph; the summary-table row records `SELECTED_CONTROL`, not exhaustive |
| `docs/paper/PAPER_I_FACT_SHEET.md` §7 | a "Selected control direction" paragraph above the table |
| `docs/paper/PAPER_I_DO_NOT_CLAIM.md` | new entries 19b and 19c forbid the four readings below |
| `INTERMEDIATE_MILESTONE_README.md` §8, `PROJECT_INTERMEDIATE_HANDOFF.md` ("What does Task 38 not establish?") | the selected-direction statement added |
| `audit/verify_documentation_snapshot.py` | new rules: the three objects must carry `selection_status`/`exhaustive`/`selection_note`; CLAIM-L010 must carry `canonical_status: SELECTED_CONTROL` and `exhaustive: false` and name `cle 0`; `transportState` must appear under `control_specific_data` and not under `derived_local_structures`; four new sentinels |

**Explicitly forbidden readings** (guards in `PAPER_I_DO_NOT_CLAIM.md`, in
`CLAIM-L010.forbidden_stronger_reading` and in the validator sentinels): `transportState` is the
unique native Spin deformation; `cle 0` is canonically selected by the primitive Euclidean
input; the Task-38 result classifies the full Spin deformation space; the Task-38 pure-gauge
result applies to every possible native Spin deformation.  **No second deformation direction
was added.**

Theorem statements changed? **NO** — assumptions changed? **NO** — production architecture
changed? **NO** — release schema changed? **YES** (optional classification fields only, kept
inside the existing enums; no enum value was renamed).
Final validation: documentation validator **PASS**.

---

## 2. Regenerated release artifacts

| artifact | how |
| --- | --- |
| `docs/machine/THEOREM_REGISTRY.jsonl` | `python3 audit/build_theorem_registry.py` (all statements re-extracted) |
| `docs/machine/FAILBUILD_LEDGER.jsonl` | `python3 audit/build_failbuild_ledger.py` (Task-41 ledger indexed; historical entries untouched) |
| `docs/machine/MATHEMATICAL_DAG.json`, `PROVENANCE_DAG.json`, `VERIFICATION_DAG.json` and the three `.dot` files | `python3 audit/build_dags.py` |
| `docs/machine/PROJECT_INDEX.tsv`, `SOURCE_MANIFEST.json`, `RELEASE_MANIFEST.json` | `python3 audit/build_manifests.py` |
| `docs/machine/PROJECT_STATE.json`, `CLAIM_REGISTRY.jsonl`, `OBJECT_REGISTRY.jsonl`, `REGISTRY_SCHEMA.md` | hand-maintained files, edited exactly as recorded above |
| `docs/machine/PROVENANCE_LEDGER.jsonl` | one appended event `PRV-018` (T41), recording that Task 40 completed and that a post-release review found the four defects repaired here; earlier events untouched |
| `docs/machine/AXIOM_AUDIT.json` | regenerated from the build log by `python3 audit/build_axiom_audit.py`; byte-identical to the Task-40 file (67 endpoints, `result: PASS`) |

No historical data was regenerated destructively: the Task-40 audit, failbuild ledger and
provenance records are unchanged, and the release manifest keeps the Task-40 label under
`previous_milestone_name`.

## 3. Validation results

| check | command | result |
| --- | --- | --- |
| documentation validator | `python3 audit/verify_documentation_snapshot.py` | **PASS** — see §4 |
| statement-extraction regression | `python3 audit/test_statement_extraction.py` | **PASS** — see §4 |
| manifest verification | inside the validator (check 12) | hashed files **381**, hash mismatches **0** |
| full Lean build | `lake build RequestProject` | **PASS**, 8356 jobs (unchanged) |
| axiom audit | `lake build RequestProject.Spine.Closure.AxiomAudit` (inside the full build) | 67 endpoints, all `[propext, Classical.choice, Quot.sound]` — unchanged; no endpoint added or removed |
| firewalls | `lake build RequestProject.Spine.Audit.Firewall`, `… Spine.Audit.ArchitectureDAG`, `… Spine.Task36.Firewall`, `… Spine.Deformation.Firewall` | **PASS**; no source-DAG change, no reverse dependency, deformation/closure leaf properties unchanged |

## 4. Exact final outputs

```text
$ python3 audit/verify_documentation_snapshot.py
claims 67, theorems 67 (definition: 2, theorem: 65), objects 46, modules 58, controls 11,
open problems 12, failbuilds 180, provenance events 18, claim IDs cited in prose 67
canonical documents 8, sentinel-checked documents 7, hashed files 381, hash mismatches 0
DOCUMENTATION SNAPSHOT: all checks passed

$ python3 audit/test_statement_extraction.py
regression case tangentTransition_eq_derivative_baseTransition: extracted 11 lines,
terminal conclusion present
synthetic fixtures: 4 checked
registered declarations: 67 checked, 0 with extraction problems
STATEMENT EXTRACTION: all checks passed

$ lake build RequestProject
... Build completed successfully (8356 jobs).

$ python3 audit/build_axiom_audit.py /tmp/build.log     # regenerated from that build log
wrote 67 endpoints, result PASS
# byte-identical to the pre-Task-41 docs/machine/AXIOM_AUDIT.json (diff: no output)
```

Firewall lines printed by the same build (unchanged):

```text
Spine external-project imports: 0 (prefixes checked: 7); Spine modules audited: 176
SPINE ARCHITECTURE AUDIT: all checks passed
Task-36 leaf audit: 199 non-Task-36 Spine modules checked, 0 of them reach …Task36
curvature claim firewall: 6119 Spine declarations scanned, none names curvature, holonomy,
  a connection or a Riemann tensor
deformation leaf audit: 209 non-deformation Spine modules checked, 0 of them reach …Deformation
deformation target-leakage audit: 248 declarations scanned, none names a curvature sign,
  a target geometry, a field equation, a transport form or a loop-transport object
closure leaf audit: 220 non-closure Spine modules checked, 0 of them reach …Closure
```

## 5. Scope firewall

Nothing beyond the four repairs was edited: no theorem was added, no statement or hypothesis
altered, no definition introduced, no module refactored, no import changed, no connection,
`Lie(SpinGroup)`, `dρ_e`, parallel-transport, holonomy, curvature or topology infrastructure
created, and no second deformation direction added.  Incidental observations are recorded, one
sentence each, at the end of `TASK41_FAILBUILDS.md` as `OBS-41-001`, `OBS-41-002` and
`OBS-41-003` (`status: OUT_OF_SCOPE`, `blocks_task41: false`).  None of them blocked a required
repair, so none was investigated further.

## 6. Final scientific boundary (unchanged, now stated correctly)

```text
primitive local Euclidean R³ datum
        → derived Lorentz / Clifford / Spin core
             ├─► certified Lorentz-skew Lie-algebra branch
             ↓
        global gluing + smooth 4-manifold
        → regular solder gate
        → smooth tangent Lorentz geometry
        → project-native global reconvergence

and separately (CONTROL RESULT, not a classification):

selected cle-0 one-parameter Spin control
        → specific Task-37/38 fixed-base smoke test
        → one full-Spin Čech gauge orbit
        → Task-39 solution-space correspondence with tangent metric preservation
```

The next research boundary is exactly where Task 40 left it: the intrinsic Spin infinitesimal
bridge (OPEN), `dρ_e` (OPEN), and only then a shared connection layer, parallel transport,
holonomy and curvature (FUTURE).  Task 41 crossed none of these edges.

**TASK 41 — RELEASE SNAPSHOT REPAIR: PASS / FINAL FROZEN**
