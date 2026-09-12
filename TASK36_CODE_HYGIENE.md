# TASK 36 — Code hygiene

Scope: the 14 modules of `RequestProject/Spine/Task36/` plus the three docstring-only edits
to pre-existing files listed in `TASK36_PROVENANCE.md`.

## Forbidden constructs (§22)

Scanned with `rg` over `RequestProject/Spine/Task36/` at the final green build:

| construct | occurrences |
| --- | --- |
| `sorry` | 0 |
| `admit` | 0 |
| `axiom` | 0 |
| `native_decide` | 0 |
| `unsafe` | 0 |
| `partial` | 0 |
| `implemented_by` | 0 |
| `Matrix.inv` | 0 |

(The word "admits" occurs in prose; the scan for the tactic/keyword `admit` is word-bounded.)

## Discouraged tactics (§22)

| tactic | occurrences in Task 36 |
| --- | --- |
| `simp` (as a tactic) | 0 |
| `simpa` | 0 |
| `Classical.` | 0 |

No exception was needed, so no library-boundary exception is recorded.

`@[simp]` *attributes* are used on six pure projection lemmas
(`Task36.gauge_one_a`, `gauge_mul_a`, `gauge_inv_a`, `smul_A`, and the two `LoopModel`
projections); tagging a lemma is not invoking the `simp` tactic.

`decide` is used twice, both times on closed decidable goals with no free variables:
`Fintype.card (Fin 2 → Bool) = 4` and a `Bool` disequality
(`RequestProject/Spine/Task36/LoopSpinFreedom.lean:444`, `:469`).  `decide` is kernel-checked
and is not on the forbidden list; `native_decide` is not used.

## Axiom audit (§22)

`#print axioms` is invoked in the sources on every Task-36 endpoint: **53 audits**, each
reporting exactly

```text
[propext, Classical.choice, Quot.sound]
```

`Classical.choice` here is the ambient Mathlib axiom reported for essentially every Mathlib
development; it is not a use of the `Classical` namespace in the proofs (see the table above).

## Statement integrity

* No theorem statement was weakened to make a counterexample compile.  Every fail-build in
  `TASK36_FAILBUILDS.md` records `statement changed: no` and `assumptions changed: no`.
* No Task-35 statement, hypothesis or proof was modified; the only edits to pre-existing files
  are appended docstring notices that preserve the original wording verbatim.

## Naming

* Every Task-36 declaration lives in the `Task36` namespace (or, for the audit module, in
  `Task36Audit`), so no collision with Mathlib or with the frozen branches is possible.
* Principal endpoints use the exact names requested in §20:
  `smooth_solder_implies_orientation_compatible`,
  `smooth_solder_implies_spin_obstruction_trivial`,
  `orientation_obstruction_nonzero_implies_no_solder`,
  `spin_obstruction_nonzero_implies_no_solder`,
  `one_loop_has_kernel_sign_freedom`,
  `orientation_reversing_gluing_no_solder`,
  `adversarial_global_topology_certificate`.
  Two requested names were deliberately altered, with the reason stated in the docstring:
  `fixed_cover_spin_choice_family` (rather than `torus_fixed_cover_spin_choice_family`,
  because the base is a disjoint family of loop models, not a literal torus) and
  `spin_does_not_imply_lorentz_conditional` / `spin_does_not_imply_lorentz_moebius` (rather
  than an unqualified `spin_does_not_imply_lorentz`, because the concrete `S⁴` case is
  blocked — see `TASK36_AUDIT.md` §12).

## File sizes

All Task-36 modules are well under 600 lines; the largest is
`RequestProject/Spine/Task36/LoopSpinFreedom.lean`.  No module needed splitting.

## Build

`lake build RequestProject` — green, 8341 jobs, zero errors, zero warnings originating in
Task-36 files, with `SPINE ARCHITECTURE AUDIT: all checks passed` and the five Task-36
firewall checks passing.

---

## CORRECTION NOTICE (Task 37 §5) — the `Classical` row of the table above

Nothing above is deleted; the following correction applies to the row `| Classical. | 0 |`.

Read literally as a count of the string `Classical.` in Task-36 sources, the entry is correct.
Read as the claim "Task 36 uses no `Classical`", it is **wrong**:
`RequestProject/Spine/Task36/LoopSpinFreedom.lean` line 189 contains

```text
    open Classical in
    def signFun …
```

The corrected statement is:

> Task 36 contains exactly one localized `Classical` exception, `Task36.signFun`.  It is
> needed because the definition case-splits on membership in the open wrap component of the
> quotient emergent base, which is not a decidable predicate.  It is computational /
> presentation infrastructure for a piecewise-constant `±1`-valued function on two disjoint
> open sets, it is immediately replaced by the three lemmas `signFun_of_eq`,
> `signFun_of_notMem`, `signFun_of_mem_wrap`, and it enters no mathematical hypothesis of any
> principal statement.

Task 37 audited whether a constructive replacement is available and concluded that it would
require a decidability library for the wrap component in the quotient, obscuring the
adversarial control; the exception is therefore retained deliberately.  See
`TASK37_CODE_HYGIENE.md` §3.

A second occurrence of the same pattern, `Task37.Deformation.loopTransportFun`, exists in the
Task-37 deformation branch and is documented in the same place.

## CORRECTION NOTICE (Task 37 §4) — the removed `Classical` use

`Task36.continuous_det_of_continuous` used the `classical` tactic to select a basis of an
arbitrary finite-dimensional space.  Task 37 replaced it by `Task36.continuous_det_localModel`,
which uses the project's explicit equivalence `EmergentBase.localModelEquivFin4`; the
mathematical content used downstream (the case `E = LocalModel`) is unchanged, and that
`classical` no longer exists.

## CORRECTION NOTICE (Task 37 §§2, 3) — the frozen DAG and the module count

Task 37 parallelised the Task-36 import DAG and added
`RequestProject/Spine/Task36/LoopTimeOrientation.lean` (the loop-specific time-orientation
control, moved verbatim out of `TimeOrientation.lean`).  The layer now has 15 modules, the
firewall audits 14 of them as bottom-up plus the declared comparison module, and the build
figures quoted above ("8341 jobs", "13 Task-36 modules") are the pre-refactor ones; the
Task-37 green build reports 8 347 jobs and 14 audited Task-36 modules.  No theorem statement
and no hypothesis changed.
