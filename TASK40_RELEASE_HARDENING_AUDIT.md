# TASK 40 — intermediate release hardening: audit

**Scope.** Task 40 is a documentation, registry, validator and manifest task.  The frozen
mathematics of Tasks 36–39 is unchanged: no theorem statement, no hypothesis and no
mathematical construction was touched.  The single Lean edit is audit-only and is recorded in
`TASK40_FAILBUILDS.md` (five `#print axioms` lines appended to
`RequestProject/Spine/Closure/AxiomAudit.lean`).

---

## 1. Frozen baseline (Part I)

| item | value |
| --- | --- |
| mathematical baseline | TASK 39 — INTERMEDIATE PROJECT CLOSURE (frozen) |
| pre-Task-40 build | `lake build RequestProject` → **green, 8356 jobs** |
| post-Task-40 build | `lake build RequestProject` → **green, 8356 jobs** |
| principal certificate | `Closure.intermediate_milestone_certificate`, unchanged |
| Task-36/37/38/39 theorem statements | unchanged (verified by `git diff` over `RequestProject/`: the only modified file is `Closure/AxiomAudit.lean`, which contains no declaration) |
| axiom audit | 67 endpoints, all `[propext, Classical.choice, Quot.sound]`, `result: PASS` |
| firewalls | Spine legacy/layering, architecture DAG, Task-36 battery, deformation/closure branch — all print their pass lines inside the full build |
| documentation validator | `python3 audit/verify_documentation_snapshot.py` → all checks passed |

Proof policy unchanged and re-checked: no `sorry`, no `admit`, no new `axiom`, no
`native_decide`, no `unsafe`, no `partial` (outside the two pre-existing meta-level audit
helpers), no `implemented_by`, no `Matrix.inv`.

## 2. The six review defects and their repairs

| id | defect | status | evidence |
| --- | --- | --- | --- |
| **ISSUE-40-01** | the Task-38 result was overgeneralized ("a transition-cocycle deformation is a change of trivialisation, not a change of geometry"; "transition-cocycle deformations are pure gauge") | **FIXED** | the offending draft, `TASK39_CONNECTION_TRANSPORT_GATE_HANDOFF.md`, is reduced to a withdrawal stub quoting the sentence as invalid; its replacement `NEXT_PHASE_TRANSPORT_GATE.md` §1 states the scoped result plus the Task-39 strengthening and carries the explicit guard `GENERAL ČECH-DEFORMATION CLASSIFICATION: NOT PROVED`; `PROJECT_INTERMEDIATE_HANDOFF.md` ("Why is the present phase being closed here?"), `ARCHITECTURE.md` §Task-38 and `INTERMEDIATE_MILESTONE_README.md` §9 were rescoped; `CLAIM-S011.forbidden_stronger_reading` was extended; `PAPER_I_DO_NOT_CLAIM.md` §6 lists both phrasings; the validator now refuses either phrasing in a canonical document |
| **ISSUE-40-02** | false "no Lie algebra" statements | **FIXED** | the repository does contain `SpinCore.gB`, `SpinCore.gBLie`, `SpinCore.bivectorEquivSkew` (source read, not summarized): registered as OBJ-043 … OBJ-046 and THM-L012 … THM-L015, claimed as [CLAIM-L011]; `docs/mathematics/LOCAL_MATHEMATICS.md` has a new §6 and a corrected §7 boundary; the statement was removed from the handoff, added to `PAPER_I_FACT_SHEET.md` §2, `PAPER_I_DO_NOT_CLAIM.md` §16–§17, `INTERMEDIATE_MILESTONE_README.md` §3/§9, `PROJECT_INTERMEDIATE_HANDOFF.md`; `OP-001` was reworded and `OP-012` added; the validator forbids the phrase |
| **ISSUE-40-03** | the incorrect future-connection relation `spinCover ∘ ω` | **FIXED** | `NEXT_PHASE_TRANSPORT_GATE.md` §3 and §7 state that `spinCover` is group-level, that the composite is a type error, and that the Lorentz-side connection must be induced through `dρ_e` or a proved equivalent infinitesimal representation (a future architectural requirement, not a theorem); recorded as [CLAIM-B011] and `OP-012`; `PAPER_I_DO_NOT_CLAIM.md` §18; `OP-002.forbidden_shortcut` updated; the validator forbids the expression |
| **ISSUE-40-04** | `PROJECT_STATE.json` conflated primitive input with global and gate data | **FIXED** | the strict taxonomy `primitive_local_input` / `derived_local_structures` / `additional_global_data` / `global_regularization_or_gate_data` / `derived_global_structures` / `control_specific_data`; `primitive_local_input` now contains ℝ³ with `sip` only; `q3` moved to derived; `BaseGluingData`, `SmoothGluing` and the native Spin transition datum moved to additional global data; the two solder types moved to gate data; conditional outputs are marked `[CONDITIONAL …]`; object registry gained `definition_status`, `existence_status`, `existence_note` and the statuses `ADDITIONAL_GLOBAL_DATUM`, `GATE_DATA`, `CONTROL_MODEL`; enums documented in `docs/machine/REGISTRY_SCHEMA.md`; validator checks 10 enforce all of it |
| **ISSUE-40-05** | definitions were registered as theorems (`THM-S017`, `THM-S018`) | **FIXED** | every registry entry now carries `declaration_kind`, read from the source text; the two definitions are labelled `definition` with `proof_status: CONSTRUCTED`; the theorem `loopSolderTransport_involutive` was registered as `THM-S021`; `CLAIM-S010` is supported by the theorems `THM-S019`, `THM-S020`, `THM-S021`; the validator rejects a kind that disagrees with the source and rejects a PROVED-like claim whose only support is a definition |
| **ISSUE-40-06** | the Task-39 module count was wrong | **FIXED** | Task 39 introduced **four** modules, not three: `Deformation/SmoothProjectedGauge.lean` (144 lines), `Deformation/SolderTransport.lean` (265), `Closure/IntermediateMilestone.lean` (271), `Closure/AxiomAudit.lean` (114) — 794 lines, counted with `wc -l` on the current tree and cross-checked against `MODULE_REGISTRY.jsonl` (`task_origin: T39` gives exactly MOD-051, MOD-052, MOD-054, MOD-055; MOD-053 is the pre-existing firewall, extended not created); `TASK39_AUDIT.md` line 19 corrected with an explicit correction note |

## 3. Additional defects found during Task 40 (not hidden)

| id | defect | status | evidence |
| --- | --- | --- | --- |
| **ISSUE-40-07** | `docs/machine/FAILBUILD_LEDGER.jsonl` did not contain Task 39's own five failbuild records: the ledger had been generated before `TASK39_FAILBUILDS.md` was written | **FIXED** | regenerating with `audit/build_failbuild_ledger.py` adds `FB-T39-F1 … FB-T39-Summary` and the seven `FB-T40-*` records; 162 → 174 entries; no record was removed or rewritten |
| **ISSUE-40-08** | the scientifically significant handoff document sat outside the validated document set | **FIXED** | `NEXT_PHASE_TRANSPORT_GATE.md` is a canonical document: it is in `CANONICAL_MARKDOWN` of the validator (every Claim ID, Open-Problem ID and Object ID in it is resolved) and in `CANONICAL_DOCS` of the manifest generator (size and SHA-256 recorded) |
| **ISSUE-40-09** | `docs/machine/AXIOM_AUDIT.json` was a hand-maintained file described as a build artefact | **FIXED** | new generator `audit/build_axiom_audit.py` parses the `#print axioms` lines of a real build log (handling Lean's line wrapping) and writes the file; it now records 67 endpoints with `result: PASS` |
| **ISSUE-40-10** | the manifests recorded hashes that nothing ever re-checked | **FIXED** | validator check 12 recomputes every SHA-256 in `SOURCE_MANIFEST.json` and in the documentation snapshot of `RELEASE_MANIFEST.json` and reports the number of hashed files and mismatches |
| **ISSUE-40-11** | `OBJ-014` (native Spin transition datum) and `OBJ-017` (base gluing) were classified `DERIVED` / `PRIMITIVE (global)` | **FIXED** | both are now `ADDITIONAL_GLOBAL_DATUM` with `existence_status: SUPPLIED_DATUM`; `OBJ-019` (`SmoothGluing`) likewise, with the counterexample recorded in its note |

## 4. The corrected Lie-algebra inventory

CERTIFIED — read from `RequestProject/Spine/E1/Bivector.lean` and
`RequestProject/Spine/E1/LieAlgebra.lean`:

```text
SpinCore.gB                : Submodule ℝ (Module.End ℝ LorentzCarrier)
                             A ∈ gB ↔ ∀ x y, BS (A x) y + BS x (A y) = 0
SpinCore.gBLie             : LieSubalgebra ℝ (Module.End ℝ LorentzCarrier)
SpinCore.bivectorEquivSkew : (⋀[ℝ]^2 LorentzCarrier) ≃ₗ[ℝ] gB
SpinCore.gB_bracket_mem    : A ∈ gB → B ∈ gB → A * B - B * A ∈ gB          (THM-L015)
SpinCore.gBLie_bracket     : ⁅A, B⁆ = A * B - B * A                        (THM-L013)
SpinCore.bivectorEquivSkew_wedge : bivectorEquivSkew (wedge u v) = Kend u v (THM-L014)
SpinCore.finrank_gB        : Module.finrank ℝ gB = 6                       (THM-L012)
```

NOT YET CERTIFIED anywhere in the repository — verified by searching the whole tree, not by
recalling a summary:

* a smooth Lie-group structure on `SpinCore.SpinGroup` [CLAIM-B001], `OP-001`;
* an object `Lie(SpinGroup)` or any equivalence `Lie(SpinGroup) ≃ gB` [CLAIM-B010], `OP-012`;
* a differential `dρ_e : Lie(SpinGroup) → gB` or a proved equivalent infinitesimal
  representation [CLAIM-B011], `OP-012`;
* a native Spin connection, parallel transport, holonomy or curvature [CLAIM-B003],
  `OP-002` … `OP-005`.

`OP-012` replaces the old "construct a Lie algebra" framing: the next problem is to *relate* the
existing intrinsic Lorentz-skew Lie algebra to the infinitesimal structure of the intrinsic
`SpinGroup` and to construct/prove the corresponding differential representation.

## 5. The next open edge, as the release states it

```text
   existing intrinsic Lorentz-skew Lie algebra gB / gBLie     [CERTIFIED, CLAIM-L011]
                 |  OPEN: identify the intrinsic Spin infinitesimal structure
                 v                                            [CLAIM-B010, OP-012]
        Lie(SpinGroup) ?≃ gB                                   [DOES NOT EXIST]
                 |  OPEN: dρ_e / equivalent infinitesimal map  [CLAIM-B011, OP-012]
                 v
      infinitesimal Spin → Lorentz map                         [DOES NOT EXIST]
                 |
                 v  future shared connection  [OP-002] → parallel transport / holonomy
                    [OP-003, OP-004] → curvature [OP-005]
```

`docs/machine/MATHEMATICAL_DAG.json` shows the certified branch
`LorentzCarrier → Λ² LorentzCarrier → gB / gBLie` and `LorentzCarrier → Cl3 → SpinGroup →
spinCover` as ordinary edges, marks every node `status: CERTIFIED`, and keeps the three missing
bridges in a separate `open_edges` field with `status: OPEN` and their claim/problem IDs.  There
is **no** proved edge `Lie(SpinGroup) → gB`.

## 6. Machine-readable snapshot after the repair

| file | content |
| --- | --- |
| `PROJECT_STATE.json` | six-key taxonomy, principal results (incl. CLAIM-L011), open blockers `OP-001 … OP-012`, `next_phase_open_edges` |
| `THEOREM_REGISTRY.jsonl` | 67 entries — 65 `theorem`, 2 `definition`; statements copied from source; all `axiom_audit_status: PASS` |
| `CLAIM_REGISTRY.jsonl` | 67 claims (CLAIM-L011, CLAIM-B010, CLAIM-B011 added) |
| `OBJECT_REGISTRY.jsonl` | 46 objects (OBJ-043 … OBJ-046 added), all with definition/existence status |
| `OPEN_PROBLEMS.jsonl` | 12 problems (OP-012 added; OP-001 and OP-002 reworded) |
| `MODULE_REGISTRY.jsonl` | 58 modules |
| `NEGATIVE_CONTROLS.jsonl` | 11 controls |
| `FAILBUILD_LEDGER.jsonl` | 174 mirrored records |
| `PROVENANCE_LEDGER.jsonl` | 17 events (PRV-017 records this task) |
| `AXIOM_AUDIT.json` | 67 endpoints, PASS |
| three DAGs + `docs/graphs/*.dot` | regenerated |
| `SOURCE_MANIFEST.json`, `RELEASE_MANIFEST.json`, `PROJECT_INDEX.tsv` | regenerated; every hash re-verified |
| `REGISTRY_SCHEMA.md` | new: documents every enumeration and the sentinel list |

## 7. Final validation

```text
lake build RequestProject                                  green, 8356 jobs
  (the Spine architecture audit, the legacy/layering firewall, the Task-36 firewall and the
   deformation/closure firewall all print their pass lines inside this build)
lake build RequestProject.Spine.Closure.AxiomAudit         67 endpoints, all
                                                           [propext, Classical.choice, Quot.sound]
python3 audit/verify_documentation_snapshot.py             all checks passed
```

Validator counts recorded at the final run:

```text
claims 67, theorems 67 (definition: 2, theorem: 65), objects 46, modules 58,
controls 11, open problems 12, failbuilds 174, provenance events 17,
claim IDs cited in prose 67
canonical documents 8, sentinel-checked documents 7,
hashed files 379, hash mismatches 0
```

## 8. Final release conclusion

### CERTIFIED

* the intrinsic Euclidean ℝ³ starting datum;
* the derived Lorentz / Clifford / Spin core, including the intrinsic double cover;
* the existing six-dimensional intrinsic Lorentz-skew Lie-algebra layer `gB` / `gBLie`,
  linearly equivalent to the bivector space of the intrinsic carrier;
* the emergent smooth four-manifold construction from a smooth base gluing;
* the regular solder / tangent Lorentz geometry sector, conditionally on the solder gate;
* project-native global reconvergence (orientation compatibility, Spin-obstruction triviality,
  future-cone reduction), conditionally on the same gate;
* the adversarial topology controls;
* the Task-37/38 specific native transition deformation smoke test, on the frozen periodic
  fixed-cover control base;
* the Task-39 full regular-solder solution-space transport for that control, with the induced
  tangent Lorentz metric preserved.

### OPEN

* a smooth Lie-group structure on the intrinsic `SpinGroup` (`OP-001`);
* identification of the infinitesimal Spin structure with `gB` / `gBLie` (`OP-012`);
* the differential `dρ_e` (`OP-012`);
* a native connection (`OP-002`);
* parallel transport (`OP-003`);
* holonomy (`OP-004`);
* curvature (`OP-005`);
* any resulting dynamical or geometric closure (`OP-008`, [CLAIM-B008]).

The next research phase begins specifically at the missing infinitesimal bridge, **not** at
"construct some Lie algebra".  Task 40 does not cross that edge.

---

## TASK 40 — INTERMEDIATE RELEASE HARDENING: PASS / FROZEN
