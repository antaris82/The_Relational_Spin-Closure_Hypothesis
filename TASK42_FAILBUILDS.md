# TASK 42 — fail / change ledger (append-only)

Every build failure, validator failure and manifest mismatch encountered while producing the
warning-zero cleanup, recorded at the moment it happened.  Nothing is erased after the final
PASS.  Historical ledgers `TASK10…TASK41_FAILBUILDS.md` are untouched.

For each entry: exact command, exact file, exact error, diagnosis, repair, and the four impact
questions (statement / assumptions / conclusion / proof strategy).

---

## F1

* **Command** `lake build RequestProject`
* **Location** `RequestProject/Spine/Cohomology/AlexanderWhitney.lean:107`, theorem
  `backIncl_comp_delta_of_gt`
* **Error**
  `error: RequestProject/Spine/Cohomology/AlexanderWhitney.lean:107:4: omega could not prove the goal: a possible counterexample may satisfy the constraints m ≥ 0, l ≥ 0 …`
* **Diagnosis** the warned step was `simp only [Fin.val_mk]`, whose *only* argument the linter
  proved unused.  Deleting the whole tactic removed not just the unused rewrite but also the
  definitional normalisation that `simp only` performs on the goal produced by the preceding
  `show`, which `omega` relies on.
* **Repair** keep the definitional step without the unused lemma: `dsimp only`.  No lemma
  list, no new automation, no broadening to `simp`.
* statement changed? NO — assumptions changed? NO — conclusion changed? NO — proof strategy
  changed? NO.

## F2

* **Command** `lake build RequestProject`
* **Location** `RequestProject/Spine/Comparison/EmergentSpinGate.lean:173`
* **Error** `error: RequestProject/Spine/Comparison/EmergentSpinGate.lean:173:61: unexpected token 'omit'; expected 'lemma'`
* **Diagnosis** the `omit [IsTopologicalGroup L] in` line repairing the `unusedSectionVars`
  warning for `spin_data_do_not_determine_base` had been inserted *between* the declaration's
  doc comment and the `theorem` keyword, which Lean does not accept.
* **Repair** move the `omit … in` line to immediately *before* the doc comment.
* statement changed? NO — assumptions changed? YES, and only in the sanctioned sense: the
  unused instance parameter `[IsTopologicalGroup L]` is removed from the elaborated signature
  — conclusion changed? NO — proof strategy changed? NO.

## F3

* **Command** `python3 audit/verify_documentation_snapshot.py`
* **Location** `docs/machine/SOURCE_MANIFEST.json`
* **Error** `FAILED: 8 problem(s)` — `hash mismatch` for each of the eight Lean files edited
  by the cleanup (`AlexanderWhitney.lean`, `EmergentSpinGate.lean`, `CocycleGaugeOrbit.lean`,
  `Clifford.lean`, `MatrixModel.lean`, `PauliRepresentation.lean`, `Shell.lean`,
  `MinkowskiMatrix.lean`).
* **Diagnosis** expected consequence of editing frozen sources: the recorded manifest hashes
  still described the pre-cleanup bytes.
* **Repair** regenerate the machine snapshot in the documented order:
  `python3 audit/build_theorem_registry.py`, `python3 audit/build_module_registry.py`,
  `python3 audit/build_manifests.py`.  The theorem and module registries came out
  byte-identical (no `statement_text` and no claim mapping changed); only the file hashes in
  `SOURCE_MANIFEST.json` and `RELEASE_MANIFEST.json` moved.  Re-run of the validator:
  `DOCUMENTATION SNAPSHOT: all checks passed`, hash mismatches 0.
* statement changed? NO — assumptions changed? NO — conclusion changed? NO — proof strategy
  changed? NO.

---

No other build failure occurred.  The final full build and the final clean rebuild both report
`Build completed successfully (8356 jobs).` with `grep -c '^warning:' → 0`.
