# TASK 34 — repository-wide terminology audit and documentation repair

This document discharges Task 34 §2 and §21.  Historical provenance is **preserved**: no
Task-32 or Task-33 statement was deleted or rewritten in place.  Where a statement is
obsolete, the original text is kept and a visible correction notice was added — at the head of
the document and, where the statement occurs, inline.

`ARISTOTLE_SUMMARY.md` is the append-only record of previous runs and is deliberately left
byte-for-byte unchanged; its Task-32 paragraphs are historical, and their corrections are the
ones listed below.

---

## 1. Files carrying a Task-34 correction notice

| file | notice added | inline annotations |
|---|---|---|
| `TASK32_PROVENANCE.md` | head of file | §0 outcome paragraph; row 22 of the §3 table; §5 (solder) |
| `TASK32_AUDIT.md` | head of file | the "Not claimed" list (smooth gate, solder form) |
| `TASK32_CODE_HYGIENE.md` | head of file | the module table ("minimal base-gluing primitive"); the `partial` wording |
| `TASK33_PROVENANCE.md` | head of file | — (Task-33 statements stand; only the forward-looking "no tangent/solder content" remark is dated) |
| `TASK33_AUDIT.md` | head of file | — (same) |
| `RequestProject/Spine/Emergent/Symmetric.lean` | — | docstring of `symmetric_emergent_manifold`, item 6: "canonically homeomorphic" → what is actually proved, with pointers |
| `README.md`, `PROVENANCE_LEDGER.md`, `COMBINED_PROJECT_PROVENANCE.md`, `ARCHITECTURE.md`, `DEPENDENCY_DAG.md` | Task-34 sections appended/updated | — |

## 2. The four required corrections, in their final form

**(a) "the minimal missing primitive"** must be read as

> an explicit sufficient base-gluing primitive; cross-piece incidence / identification
> information is irreducibly additional; field-by-field or universal minimality of
> `BaseGluingData` is not proved.

Already repaired in the Lean sources by Task 33 (`Emergent/BaseGluing.lean`,
`Emergent/LocalPieceData.lean`); now also annotated in the Task-32 documents.

**(b) "unique up to canonical homeomorphism"** must distinguish the stages:

> *Task 32:* existence of a homeomorphism was proved.
> *Task 33:* a distinguished intrinsic-coordinate comparison was constructed, with identity /
> inverse / composition coherence, and upgraded to a canonical diffeomorphism.

Annotated in `TASK32_PROVENANCE.md` and repaired in the docstring of
`EmergentBase.symmetric_emergent_manifold`.

**(c) "literally the same Spin transition datum"** must be read as

> the same pointwise trivial group-valued transition law on two distinct typed covers.

Already repaired in `Comparison/EmergentSpinGate.lean` (Task 33); no surviving occurrence
asserts the old reading.

**(d) "Smoothness is not claimed"** must be read as

> Task 32 did not close the smooth-manifold gate.  Task 33 proved `SmoothGluing → IsManifold`
> for the actual reconstructed atlas.

Annotated in `TASK32_PROVENANCE.md` and `TASK32_AUDIT.md`.

**(e) Every `H¹` statement** of the emergence layer retains the scope

> fixed-cover Čech `Ȟ¹`, specific symmetric full-overlap emergent cover,

and is nowhere described as `H¹(M;ℤ₂) = 0` or as a theorem for arbitrary emergent bases.  The
scope paragraph is in `Comparison/EmergentSpinGate.lean` (Task 33) and is repeated in the
correction notices of the Task-32/33 documents.

**(f) Hygiene wording about `partial`.**  The repository contains historical `partial def`
declarations in the audit infrastructure (`Spine/Audit/Firewall.lean`: the import-closure
walker).  The globally correct statement is

> No new Task-34 production module introduces `partial`,

and no Task-34 theorem depends on a `partial` definition.  See `TASK34_CODE_HYGIENE.md`.

---

## 3. Repository-wide terminology audit

Searched across the whole repository (excluding `.lake`).  Classification:
**CURRENT** = accurate as written; **HISTORICAL + CORRECTED** = preserved historical text now
carrying a visible correction; **INVALID / REPAIR REQUIRED** = none remain.

| term | occurrences | classification |
|---|---|---|
| `minimal missing primitive` | 5 | HISTORICAL + CORRECTED (2 in Lean docstrings that *quote the phrase in order to repair it*; 2 in Task-33 reports describing the repair; 1 in `TASK33_AUDIT.md`'s repair table).  No occurrence asserts it. |
| `minimal base-gluing primitive` | 2 | HISTORICAL + CORRECTED (`TASK32_CODE_HYGIENE.md` module table, now annotated; `TASK33_AUDIT.md` repair table). |
| `canonical homeomorphism` | 3 | HISTORICAL + CORRECTED (all in `TASK32_PROVENANCE.md`, now annotated at the head and inline).  The Lean sources use the precise Task-33 wording. |
| `literally the same` | 7 | CURRENT.  Two occurrences are in `Comparison/EmergentSpinGate.lean`, where the phrase appears only to *deny* it; the remaining five are unrelated, correct, definitional statements in the Nerve/E2 layers ("the carriers are literally the same types"). |
| `Smoothness is not claimed` | 0 | no occurrence remains outside the append-only run summary. |
| `H¹(M` | 6 | CURRENT.  Every occurrence is a statement that the passage to `H¹(M;ℤ₂)` is *not* taken (`TASK04_AUDIT.md`, `TASK31_PROVENANCE.md`, `Comparison/LorentzSpinUniqueness.lean`, `Comparison/EmergentSpinGate.lean`). |
| `Ȟ¹` | 40 | CURRENT, all fixed-cover statements; the emergence-layer ones additionally carry the explicit symmetric-full-overlap scope paragraph. |
| `partial` | audit infrastructure only | HISTORICAL + CORRECTED: `Spine/Audit/Firewall.lean` has `partial def closureAux`; the hygiene wording is now scoped per task (§2(f)). |
| `solder` | Task-32/33 reports (as "missing"), Task-34 sources and reports | HISTORICAL + CORRECTED for Tasks 32/33 (annotated: the datum is now isolated); CURRENT for Task 34.  Nowhere is a type-level identification called a solder form. |
| `tangent` | Task-4 top-down branch, Task-34 bottom-up branch | CURRENT.  The two are kept apart by firewall checks 9 and 10; the only module that sees both is `Comparison/SolderTangentGate.lean`. |
| `w₂` | Tasks 4, 5, 29–33 reports | CURRENT.  Every occurrence states that the identification with `w₂(TM)` is *not* made.  Task 34 adds no `w₂` claim. |

## 4. What a reader should take from the repaired documents

1. `BaseGluingData` is a **sufficient** base-gluing primitive with an irreducibly additional
   incidence layer; it is not proved minimal.
2. The symmetric sector has an **existence** statement (Task 32) and, separately, a
   **distinguished coherent** comparison upgraded to a **diffeomorphism** (Task 33).
3. The **smooth gate is closed** (Task 33) for the actual reconstructed atlas.
4. The `Ȟ¹` vanishing is a **fixed-cover** statement about one specific symmetric cover.
5. The **solder coupling is an additional datum**, proved not derivable (Task 34); with it the
   internal Lorentz structure is coupled fibrewise to the genuine tangent geometry, with the
   frame cocycle equal to the projected native Lorentz cocycle.
6. Nothing anywhere in the project claims `w₁(TM)`, `w₂(TM)`, a connection, curvature or
   dynamics.

---

# TASK-35 CORRECTION NOTICE (2026-09-12)

Item 5 of §4 above ("the **solder coupling is an additional datum**, proved not derivable
(Task 34)") is to be read as: *direct/raw transition identification is not forced* — a
non-derivability statement about the raw identification of the two transition systems, not
about every possible construction of a coupling.  The coupling remains an **ADDITIONAL DATUM**,
and Task 35 identifies that datum exactly: it is a regular (bundle-level) equivalence
`InternalLorentzBundle(S) ≃ TM`.  Task 35 additionally proves that the Task-34 fibrewise object
does not suffice (`SpinNative.weak_solder_not_regular`).
