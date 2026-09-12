# TASK 42 — Warning-Zero Release Cleanup

Mechanical release cleanup only: every Lean compiler/linter warning emitted by the full
project build is repaired **at source**.  No mathematics, no new theorem, no new definition,
no new abstraction, no renaming, no re-architecture.

    pre-cleanup warning count:   76
    post-cleanup warning count:   0

---

## 1. Baseline (recorded from the actual build, not from the task prompt)

    lake build RequestProject 2>&1 | tee task42_before.log
    Build completed successfully (8356 jobs).   EXIT=0
    grep -c '^warning:' task42_before.log  →  76

Baseline distribution by module and warning category:

| module | unusedSimpArgs | unnecessarySeqFocus | deprecated | unusedSectionVars | baseline total | final |
|---|---|---|---|---|---|---|
| `RequestProject/Spine/E1/Clifford.lean` | 41 | 0 | 0 | 0 | 41 | 0 |
| `RequestProject/Spine/E1/PauliRepresentation.lean` | 13 | 0 | 0 | 0 | 13 | 0 |
| `RequestProject/Spine/Foundation/MinkowskiMatrix.lean` | 8 | 0 | 2 | 0 | 10 | 0 |
| `RequestProject/Spine/Cohomology/AlexanderWhitney.lean` | 7 | 0 | 0 | 0 | 7 | 0 |
| `RequestProject/Spine/E1/Shell.lean` | 0 | 2 | 0 | 0 | 2 | 0 |
| `RequestProject/Spine/E1/MatrixModel.lean` | 0 | 1 | 0 | 0 | 1 | 0 |
| `RequestProject/Spine/Comparison/EmergentSpinGate.lean` | 0 | 0 | 0 | 1 | 1 | 0 |
| `RequestProject/Spine/Deformation/CocycleGaugeOrbit.lean` | 0 | 0 | 0 | 1 | 1 | 0 |
| **total** | **69** | **3** | **2** | **2** | **76** | **0** |

The observed distribution agrees exactly with the expected baseline of the task statement.

## 2. Final verification

    lake build RequestProject 2>&1 | tee task42_after.log
    Build completed successfully (8356 jobs).   EXIT=0
    grep -c '^warning:' task42_after.log  →  0
    grep -ci 'warning'  task42_after.log  →  0      (no warning marker anywhere in the log)
    python3 audit/check_zero_warnings.py task42_after.log
        LEAN WARNING AUDIT: PASS
        warnings=0

Clean rebuild (project build artefacts deleted, `rm -rf .lake/build`, dependency versions
untouched):

    lake build RequestProject 2>&1 | tee task42_clean.log
    Build completed successfully (8356 jobs).   EXIT=0
    grep -c '^warning:' task42_clean.log  →  0

No linter was disabled anywhere: the repository contains no
`set_option linter.unusedSimpArgs`, `linter.unnecessarySeqFocus`, `linter.unusedSectionVars`
or `warningAsError` setting, no build command was wrapped, and no log was filtered.

## 3. Source changes, file by file

Eight Lean files were modified; 41 insertions / 40 deletions in total.  For every file:
theorem statements, assumptions, conclusions and proof architecture are unchanged, with the
single, explicitly permitted exception of the two `omit` repairs of §3.7–3.8.

### 3.1 `RequestProject/Spine/E1/Clifford.lean`

* Warnings addressed: 41 × `unusedSimpArgs` at 117:63, 118:4, 182:39/44/49/54, 183:4/22,
  188:44/49/54/64/81, 189:24/33/42, 191:44/49/54/59/81, 192:15/24/33/42,
  194:39/54/59/64/69, 195:24/42, 227:13/24/34/44/54/66, 228:4/13/22.
* Class of edit: deletion of the flagged entries from the existing `simp only [...]` lists
  (`spinToCl_symmetrized`, `omega_sq`, `omega_comm_cle`, `reverse_omega`).  No list was
  broadened to `simp`, no tactic replaced.
* statement changed? NO — assumptions changed? NO — conclusion changed? NO — proof strategy
  changed? NO.

### 3.2 `RequestProject/Spine/E1/PauliRepresentation.lean`

* Warnings addressed: 13 × `unusedSimpArgs` at 53:48/66, 82:53/71, 100:16/34/53, 159:57,
  160:44, 174:40/58, 205:46, 206:10.
* Class of edit: deletion of the flagged entries.  At line 174 *both* arguments of
  `simp [Matrix.one_apply, Complex.ext_iff]` were flagged, so the now-empty argument list was
  removed and the tactic is the plain `simp` it already was (no `simp only` was broadened, no
  new automation introduced).
* statement changed? NO — assumptions changed? NO — conclusion changed? NO — proof strategy
  changed? NO.

### 3.3 `RequestProject/Spine/Foundation/MinkowskiMatrix.lean`

* Warnings addressed: 8 × `unusedSimpArgs` at 40:53, 45:32/74, 175:4, 182:4, 227:30, 284:79,
  293:79; 2 × `deprecated` at 130:8 and 134:2.
* Class of edit: (a) deletion of the flagged simp entries; where a deleted entry was the sole
  content of a continuation line, the residue was folded back onto the preceding line and two
  over-long lines were re-wrapped (whitespace only).  (b) The two uses of the deprecated
  `Matrix.mul_eq_one_comm` were replaced by the current `mul_eq_one_comm` (root namespace,
  `Mathlib/Algebra/Group/Defs.lean`), applied identically as `mul_eq_one_comm.2 …`.  No
  compatibility alias was introduced; the deprecated name no longer occurs in the sources.
* statement changed? NO — assumptions changed? NO — conclusion changed? NO — proof strategy
  changed? NO.

### 3.4 `RequestProject/Spine/Cohomology/AlexanderWhitney.lean`

* Warnings addressed: 7 × `unusedSimpArgs` at 69:36, 70:36, 80:36, 80:48, 104:36, 105:36,
  107:15.
* Class of edit: deletion of the flagged entries.  At line 107 the flagged `Fin.val_mk` was
  the only entry of `simp only [Fin.val_mk]`; the residual definitional normalisation that the
  step performed is retained as `dsimp only` (the following `omega` needs it: deleting the
  step outright made `omega` fail, recorded as F1 in `TASK42_FAILBUILDS.md`).  This introduces
  no new automation — `dsimp only` with no lemmas performs definitional simplification only.
* statement changed? NO — assumptions changed? NO — conclusion changed? NO — proof strategy
  changed? NO.

### 3.5 `RequestProject/Spine/E1/MatrixModel.lean`

* Warning addressed: 1 × `unnecessarySeqFocus` at 64:71.
* Class of edit: the warned `<;>` before `ring` replaced by the sequencing `;` the compiler
  suggests: `… simp [hMat, Complex.ext_iff, Matrix.smul_apply, Complex.real_smul]; ring`.
* statement changed? NO — assumptions changed? NO — conclusion changed? NO — proof strategy
  changed? NO (identical tactic behaviour; only the combinator that the linter proved
  superfluous is gone).

### 3.6 `RequestProject/Spine/E1/Shell.lean`

* Warnings addressed: 2 × `unnecessarySeqFocus` at 329:31 and 329:46.
* Class of edit: `fin_cases i <;> simp [sip] <;> field_simp <;> linear_combination …` becomes
  `fin_cases i <;> simp [sip]` followed by `field_simp` and `linear_combination …` as
  successive tactic steps — the plain sequencing the linter reports as sufficient.
* statement changed? NO — assumptions changed? NO — conclusion changed? NO — proof strategy
  changed? NO.

### 3.7 `RequestProject/Spine/Comparison/EmergentSpinGate.lean`

* Warning addressed: 1 × `unusedSectionVars` at 174:0, theorem
  `SpinNative.spin_data_do_not_determine_base`, automatically included `[IsTopologicalGroup L]`.
* Class of edit: one added line, `omit [IsTopologicalGroup L] in`, placed before the
  declaration's doc comment (Lean rejects it between the doc comment and the `theorem`
  keyword — recorded as F2 in `TASK42_FAILBUILDS.md`).  The linter is **not** disabled.
* **Elaborated signature: the unused instance parameter `[IsTopologicalGroup L]` is removed.**
  theorem proposition weakened? NO — theorem requires fewer assumptions? YES — mathematical
  conclusion changed? NO — proof architecture changed? NO.  This is a conservative
  generalisation of the theorem interface.

### 3.8 `RequestProject/Spine/Deformation/CocycleGaugeOrbit.lean`

* Warning addressed: 1 × `unusedSectionVars` at 82:0, theorem
  `Task37.Deformation.CocycleGaugeEquiv.refl`, automatically included `[IsTopologicalGroup L]`.
* Class of edit: one added line, `omit [IsTopologicalGroup L] in`, before the theorem.
* **Elaborated signature: the unused instance parameter `[IsTopologicalGroup L]` is removed.**
  theorem proposition weakened? NO — theorem requires fewer assumptions? YES — mathematical
  conclusion changed? NO — proof architecture changed? NO.

No other declaration's signature changed: the remaining six files are edited inside tactic
blocks only.

## 4. Regression checks

| check | command | result |
|---|---|---|
| full mathematical build | `lake build RequestProject` | PASS, 8356 jobs, 0 errors |
| clean rebuild | `rm -rf .lake/build && lake build RequestProject` | PASS, 8356 jobs, 0 warnings |
| warning-zero audit | `python3 audit/check_zero_warnings.py task42_after.log` | PASS, warnings=0 |
| Spine import firewall (compile time) | emitted by `RequestProject/Spine/Audit/Firewall.lean` | `SPINE FIREWALL AUDIT: all checks passed` |
| architecture / layering / Task-36 / deformation / closure firewalls (compile time) | emitted by `RequestProject/Spine/Audit/ArchitectureDAG.lean` | `SPINE ARCHITECTURE AUDIT: all checks passed` (all per-task firewall lines report `illegal edges: 0`) |
| principal axiom audit | `python3 audit/build_axiom_audit.py task42_after.log` | `wrote 67 endpoints, result PASS`; regenerated `docs/machine/AXIOM_AUDIT.json` is **byte-identical** to the pre-cleanup file — every endpoint still reports exactly `propext, Classical.choice, Quot.sound` |
| documentation snapshot | `python3 audit/verify_documentation_snapshot.py` | `DOCUMENTATION SNAPSHOT: all checks passed`, hash mismatches 0 |
| statement extraction regression (Task 41) | `python3 audit/test_statement_extraction.py` | `STATEMENT EXTRACTION: all checks passed`, 67 declarations, 0 extraction problems |
| manifest verification | `python3 audit/build_theorem_registry.py`, `build_module_registry.py`, `build_manifests.py` then the validator | regenerated; hash mismatches = 0 |

Registry regeneration effect: `THEOREM_REGISTRY.jsonl` and `MODULE_REGISTRY.jsonl` are
byte-unchanged — the two `omit` lines precede the declaration headers, so no registered
`statement_text` changed and no claim mapping needed updating.  Only the recorded file hashes
in `docs/machine/SOURCE_MANIFEST.json` (8 Lean files) and the derived
`docs/machine/RELEASE_MANIFEST.json` moved.

Proof policy: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `partial`,
`implemented_by` or `Matrix.inv` was introduced; the cleanup deletes tokens, and the only
tokens added are two `omit … in` lines, one `dsimp only`, and the replacement of three `<;>`
by ordinary sequencing.

## 5. Warning baseline, recorded historically

The Task-41 release was **not** warning free.  For the record:

    Task-41 local verification:   build PASS,  8356 jobs,  76 Lean warnings
    Task-42 final verification:   build PASS,  8356 jobs,   0 Lean warnings

Both logs are kept in the repository: `task42_before.log` (76 warnings),
`task42_after.log` and `task42_clean.log` (0 warnings).

## 6. Warning regression guard

`audit/check_zero_warnings.py` accepts a captured full build log and exits nonzero if any line
begins with `warning:`.  It prints `LEAN WARNING AUDIT: PASS` / `warnings=0` on success and
lists the offending lines on failure.  It reads a log file only; it does not wrap, filter or
modify `lake build`.  Verified in both directions: PASS on `task42_after.log`, FAIL with
`warnings=76` on `task42_before.log`.

## 7. Incidental observations (out of scope, not modified)

* **OBS-42-001 — OUT OF SCOPE — NOT MODIFIED.** `scripts/legacy_audit.py` reports
  `RESULT: FAIL` (direction violation: `RequestProject.Spine.Task36.Firewall` imports the
  control modules it is designed to audit).  This is a pre-existing condition of the frozen
  release: running the identical script on the pre-cleanup tree gives the identical `FAIL`.
  It emits no Lean build warning and is superseded by the compile-time firewalls, both of
  which pass.  Not investigated further.

## 8. Stop condition

    full Lean build PASS                                   ✔
    warnings = 0                                           ✔
    no warning linter disabled                             ✔
    all 76 baseline warnings genuinely repaired at source  ✔
    firewalls PASS                                         ✔
    principal axiom audit PASS, axiom boundary unchanged   ✔
    documentation validator PASS                           ✔
    statement extraction regression PASS                   ✔
    manifest hashes PASS (mismatches = 0)                  ✔
    no new theorem or mathematical definition              ✔
    no theorem conclusion changed                          ✔
    only the two compiler-identified unused section
      assumptions disappeared                              ✔

**TASK 42 — WARNING-ZERO RELEASE CLEANUP: PASS / FINAL FROZEN**
