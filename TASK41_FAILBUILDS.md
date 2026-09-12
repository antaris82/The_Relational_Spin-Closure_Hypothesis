# TASK 41 — fail / change ledger (append-only)

Every validator failure, extraction-regression failure, manifest mismatch and build failure
encountered while producing the Task-41 release-snapshot repair, recorded at the moment it
happened.  Nothing is erased after the final PASS.  Historical ledgers
`TASK10…TASK40_FAILBUILDS.md` are untouched; they remain the authoritative record of their own
tasks and are mirrored (never rewritten) into `docs/machine/FAILBUILD_LEDGER.jsonl`.

Task 41 is a documentation / registry / validator task: **no Lean source file was modified and
no Lean build ever failed.**  For each entry: exact command, exact file, exact error,
diagnosis, repair, and the four impact questions.

---

## F1

* **Command** `git show HEAD:audit/lean_statement.py > /tmp/oldext/lean_statement.py` followed
  by `python3 -c "import sys; sys.path.insert(0,'/tmp/oldext'); from pathlib import Path; from
  lean_statement import extract_statement;
  print(extract_statement(Path('RequestProject/Spine/Emergent/TangentTransition.lean'),
  'tangentTransition_eq_derivative_baseTransition'))"`
* **Location** `docs/machine/THEOREM_REGISTRY.jsonl` (THM-G004), produced by
  `audit/lean_statement.py` from `RequestProject/Spine/Emergent/TangentTransition.lean:153`
* **Error** the extracted statement ends at
  `    haveI : IsManifold localModelI 1 (Space B)`; the test
  `'= B.tangentTransitionMap i j y' in s` returns `False`.  The registered statement was
  therefore truncated: it contained no conclusion at all.
* **Diagnosis** the extractor stopped at the first `:=` at bracket depth zero.  In this
  declaration the *result type* itself opens with a term-level binder
  `haveI : IsManifold localModelI 1 (Space B) := (isManifold_of_smoothGluing h).of_le …`, whose
  `:=` is not the body delimiter.
* **Repair** `audit/lean_statement.py` now counts depth-zero term-level binders
  (`have`, `haveI`, `let`, `letI`, `suffices`) and skips exactly one depth-zero `:=` per binder
  before accepting one as the body delimiter; it also ignores `--` line comments and requires
  the pending-binder count to be zero before accepting a trailing ` by`.  No Lean parser and no
  new dependency was introduced.  Every registered `statement_text` was regenerated with
  `python3 audit/build_theorem_registry.py`; THM-G004 was **not** patched by hand, and it is the
  only entry whose text changed.
* Theorem statement changed? **NO** — assumptions changed? **NO** — production architecture
  changed? **NO** — release schema changed? **YES** (each registry entry gained
  `statement_extraction_status`).

## F2

* **Command** `python3 audit/verify_documentation_snapshot.py`
* **Location** `docs/machine/SOURCE_MANIFEST.json` (11 entries) and
  `docs/machine/RELEASE_MANIFEST.json` (4 entries)
* **Error** `hash mismatch for INTERMEDIATE_MILESTONE_README.md`,
  `… PROJECT_INTERMEDIATE_HANDOFF.md`, `… TASK39_AUDIT.md`,
  `… docs/mathematics/LOCAL_MATHEMATICS.md`, `… docs/mathematics/GLOBAL_MATHEMATICS.md`,
  `… docs/paper/PAPER_I_FACT_SHEET.md`, `… docs/paper/PAPER_I_DO_NOT_CLAIM.md`,
  `… docs/machine/PROJECT_STATE.json`, `… docs/machine/THEOREM_REGISTRY.jsonl`,
  `… docs/machine/CLAIM_REGISTRY.jsonl`, `… docs/machine/OBJECT_REGISTRY.jsonl`
  (15 mismatches in total, all other checks passing)
* **Diagnosis** expected and required: the Task-40 hashes are stale as soon as a document or a
  registry is edited.  Reusing them would have frozen a snapshot that no longer describes the
  files.
* **Repair** regenerate the affected artifacts and recompute every hash:
  `python3 audit/build_theorem_registry.py`, `python3 audit/build_failbuild_ledger.py`,
  `python3 audit/build_dags.py`, `python3 audit/build_manifests.py`, then re-run the validator.
  Final state: hash mismatches **0**.
* Theorem statement changed? **NO** — assumptions changed? **NO** — production architecture
  changed? **NO** — release schema changed? **NO**.

## F3

* **Command** `git checkout docs/machine/CLAIM_REGISTRY.jsonl && python3
  audit/verify_documentation_snapshot.py` — the new Task-41 rule run against the *restored
  pre-repair* registry, to confirm that it fires (the repaired file was put back immediately
  afterwards)
* **Location** `docs/machine/CLAIM_REGISTRY.jsonl` (CLAIM-S010)
* **Error** `CLAIM-S010: supporting_theorem_ids contains THM-S017, whose declaration_kind is
  'definition'; only ['lemma', 'theorem'] are allowed (use supporting_construction_ids for
  definitions)` (and the same for THM-S018)
* **Diagnosis** the two entries are `def loopSolderTransport` and `def loopSolderEquiv`; Task 40
  had labelled them correctly as definitions but left their IDs inside the claim's
  theorem-support list, and the theorem `loopSolderTransport_involutive` (THM-S021) was missing
  from it.
* **Repair** `CLAIM-S010.supporting_theorem_ids = [THM-S019, THM-S020, THM-S021]`; the two
  definitions moved to the new, optional, backwards-safe field `supporting_construction_ids`.
  The rule is applied to **all** claims, not only this one.
* Theorem statement changed? **NO** — assumptions changed? **NO** — production architecture
  changed? **NO** — release schema changed? **YES** (one new optional claim field).

## F4

* **Command** `git checkout docs/mathematics/GLOBAL_MATHEMATICS.md
  docs/paper/PAPER_I_FACT_SHEET.md && python3 audit/verify_documentation_snapshot.py` — the new
  Task-41 sentinels run against the *restored pre-repair* documents, to confirm that they fire
  (the repaired files were put back immediately afterwards)
* **Location** `docs/mathematics/GLOBAL_MATHEMATICS.md:136`,
  `docs/paper/PAPER_I_FACT_SHEET.md:51`
* **Error** `forbidden statement 'Spin cocycle is only continuous' — obsolete blocker wording:
  the strong smooth packaging is blocked by infrastructure, and a regular smooth solder already
  gives smooth projected Lorentz representatives (Task 36)`
* **Diagnosis** the release documentation had reintroduced the Task-35 causal explanation that
  Task 36 corrected in source (`Spine/Solder/BundleEquivalence.lean` correction notice,
  `Spine/Task36/SmoothBundlePackaging.lean`).
* **Repair** the affected sentences were rewritten to the source-supported distinction
  (certified smooth projected Lorentz data; infrastructure/packaging limitation for the strong
  total-space package), and five sentinels were added to the validator so the wording cannot
  return.
* Theorem statement changed? **NO** — assumptions changed? **NO** — production architecture
  changed? **NO** — release schema changed? **NO**.

## F5

* **Command** as F3/F4 (the same run against the restored pre-repair registries)
* **Location** `docs/machine/CLAIM_REGISTRY.jsonl` (CLAIM-L010)
* **Error** `CLAIM-L010: must carry canonical_status SELECTED_CONTROL, not None`;
  `CLAIM-L010: must carry exhaustive false`;
  `CLAIM-L010: the detailed_claim must name the selected Clifford direction cle 0`
* **Diagnosis** the Task-37/38 one-parameter family was recorded as an ordinary canonical
  derived local structure, although its construction uses the specifically selected Clifford
  direction `cle 0` (`RequestProject/Spine/Deformation/SharedTransport.lean`,
  `transportElem l = cosh(l/2) + sinh(l/2) · cle 0`).
* **Repair** CLAIM-L010 gained `canonical_status: SELECTED_CONTROL` and `exhaustive: false`,
  its text names `cle 0` and forbids the canonical/unique/exhaustive readings; OBJ-031, OBJ-032
  and OBJ-033 gained `selection_status`, `exhaustive` and `selection_note`; the family moved
  from `derived_local_structures` to `control_specific_data` in `PROJECT_STATE.json`.
* Theorem statement changed? **NO** — assumptions changed? **NO** — production architecture
  changed? **NO** — release schema changed? **YES** (optional classification fields only).

---

## Observations outside Task-41 scope

* **OBS-41-001** — status: `OUT_OF_SCOPE`, `blocks_task41: false`.  `TASK35_PROVENANCE.md:138`
  and `README.md` §Task 35 keep Task-35-era phrasing around the Spin cocycle; the factual
  sentence in the provenance file ("the native Spin datum itself is only continuous") is true
  and was left untouched, while the one *causal* sentence in `README.md` was repaired as part of
  ISSUE-41-01.  No further historical rewriting was performed.
* **OBS-41-002** — status: `OUT_OF_SCOPE`, `blocks_task41: false`.
  `SpinNative.SmoothTangentSolderData.contDiffOn_solderLorentzRep` and
  `Task36.internal_bundle_coordChange_smooth_in_charts` are cited in prose but are not
  registered declarations; registering them would add principal endpoints, which Task 41 must
  not do.
* **OBS-41-003** — status: `OUT_OF_SCOPE`, `blocks_task41: false`.  The theorem docstring at
  `RequestProject/Spine/Solder/BundleEquivalence.lean:561` still points to the Task-35 reason
  ("a merely continuous Spin cocycle"); the module docstring it refers to already carries the
  superseding Task-36 correction notice, and Task 41 must not modify production Lean modules,
  so the line was **not modified**.
