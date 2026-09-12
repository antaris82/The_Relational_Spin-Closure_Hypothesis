# TASK 39 — failed-build ledger (append-only)

Every failed build encountered while producing the Task-39 closure work, recorded at the moment
it happened.  Nothing is erased after success.  Historical ledgers `TASK10…TASK38_FAILBUILDS.md`
are untouched; they remain the authoritative record of their own tasks, and are additionally
mirrored (never rewritten) into `docs/machine/FAILBUILD_LEDGER.jsonl`.

For each entry: exact command, exact source location, the Lean error (abbreviated to its
essential line), diagnosis, repair, and the three impact questions.

---

## F1

* **Command** `lake build RequestProject.Spine.Deformation.SolderTransport`
* **Location** `RequestProject/Spine/Deformation/SolderTransport.lean:129`
  (`loopSolderTransport`, field `intertwine`)
* **Error** `Type mismatch: the term after show is not definitionally equal to the goal`
  — the `show` pattern written for the transported intertwining equation did not match the
  goal produced by the structure field, because the goal still contained the unreduced
  `tangentTransitionMap` application rather than the identity map.
* **Diagnosis** on the frozen periodic control every tangent transition is the identity, but
  this holds only after `tangentTransitionMap_loop_id` has been rewritten *and* the resulting
  `ContinuousLinearMap.id` has been applied via `ContinuousLinearMap.id_apply`.  The first
  attempt rewrote only the former.
* **Repair** rewrite `tangentTransitionMap_loop_id p q hy` together with
  `ContinuousLinearMap.id_apply` (and `projectedLoop_apply`) in the hypothesis `hE` before
  stating the `show`.
* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

## F2

* **Command** as F1
* **Location** `SolderTransport.lean:149` (`loopSolderTransport`, second `show` of the same
  field)
* **Error** `Type mismatch: the term after show is not definitionally equal to the goal`
* **Diagnosis** the second `show` was written with the projected Lorentz transition in its
  unexpanded form `projectedLorentzTransition (loopSharedSpin l₂) p q _ v`, while the goal at
  that point already carried the closed form supplied by `projectedLoop_apply`.
* **Repair** state the `show` in the unexpanded form and then rewrite forwards with
  `projectedLoop_apply`, `← paraMap_add` twice and `gaugeAngle_step`, rather than trying to
  match the already-rewritten shape.
* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

## F3

* **Command** as F1
* **Location** `SolderTransport.lean` (`loopSolderTransport_involutive`)
* **Error** `unsolved goals ⊢ (A p y) (id v) = (A p y) v`
* **Diagnosis** after `paraMap_zero` the composite gauge angle collapses to the identity, but
  Lean leaves the residual `id v` unreduced inside the solder application, so `congr 1` on the
  `SmoothTangentSolderData.mk` constructor closes every field except this one.
* **Repair** close the remaining goal with a trailing `rfl`.
* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

## F4–F7

* **Command** `lake build RequestProject.Spine.Closure.AxiomAudit`
* **Location** `RequestProject/Spine/Closure/AxiomAudit.lean` (four separate
  `#print axioms` lines)
* **Error** `unknown constant` (four occurrences), among them
  `Task36.regular_gauge_action_free_transitive` and
  `EmergentBase.base_gluing_is_additional_datum`.
* **Diagnosis** two of the four names were guessed from documentation rather than read from
  source and do not exist under that spelling; the other two existed but their defining module
  was not in the import list of the audit module, so the constant was not in scope.
* **Repair** the audit module now imports the full closure of principal endpoint modules, and
  every audited name was re-read from its source file before being listed.  The final module
  prints axioms for 62 endpoints, all reporting `[propext, Classical.choice, Quot.sound]`.
* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

---

## Summary

Seven failed builds, all local elaboration/scoping problems in the two new Task-39 proof
modules and in the audit module.  **No Task-39 failure was repaired by weakening a theorem
statement, by adding a hypothesis, or by changing the architecture.**  No frozen Task-36/37/38
endpoint was touched at any point; the final full build

```text
lake build RequestProject   →   Build completed successfully (8356 jobs)
```

reproduces the pre-Task-39 baseline (8352 jobs) plus exactly the new modules.
