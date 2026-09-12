# Task 27 — code-hygiene audit

## A. New modules

| module | why this layer |
|---|---|
| `RequestProject/Spine/AlgebraicTopology/DirectSumHomology.lean` | Pure homological algebra over `ℤ₂`: the homology of an arbitrary-index direct sum of chain complexes. It sits directly above the definition module `AlgebraicTopology/DirectSumComplex.lean` (which supplies `finsuppCx`, `finsuppCxι`, `finsuppCxπ`, `sumHomologyMap`) and below every Nerve-specific module. It has *no* geometric, simplicial or Nerve input; its whole project-local import closure is 4 modules (`RelativeChains` and its two predecessors, plus `DirectSumComplex`). |

One module was **renamed**, not added:

| before | after | why |
|---|---|---|
| `RequestProject/Spine/Nerve/Comparison/FiniteRelJ.lean` | `RequestProject/Spine/Nerve/Comparison/RelJ.lean` | The module now proves blocker B3 for an arbitrary cell family; the finite forms remain in it as wrappers. Keeping the name `FiniteRelJ` would describe the contents incorrectly. It is still the same leaf join of the same three branches, so the architecture check that constrains it was retargeted, not weakened. |

No `Task27.lean` module was created; nothing in the production tree carries a task number.

## B. New project-local import edges

| edge | mathematical dependency |
|---|---|
| `AlgebraicTopology.DirectSumHomology` → `AlgebraicTopology.DirectSumComplex` | the theorem is *about* `finsuppCx`, `finsuppCxι`, `finsuppCxπ` and `sumHomologyMap`, all defined there. |
| `Nerve.CellFamily.RelativeChainDecomposition` → `AlgebraicTopology.DirectSumHomology` | `isIso_sumCellHomology` is the transported form `isIso_sumHomologyMap_of_iso` applied to the chain-level isomorphism `Θ_rel`. |

That is the whole delta: **+2 internal import edges** (143 → 145), and no other module's import list changed except for the rename (`Nerve.Audit.Stage13Axioms` now imports `Nerve.Comparison.RelJ`).

## C. Removed imports

None. No import became redundant: the generic theorem was added below the existing stack rather than replacing a branch of it.

## D. Duplication check

No finite/arbitrary duplication remains in the direct-sum layer.

* The finite splitting criterion `SpineTask23.isIso_sumHomologyMap` was **moved** out of
  `DirectSumComplex` into `DirectSumHomology` and **re-proved as a three-line corollary** of
  `isIso_sumHomologyMap_of_splitting`: over a finite index type the local-finiteness hypothesis
  is exactly the completeness identity `∑ s, P s ≫ Ι s = 𝟙 K`. Its old element-chasing proof is
  gone.
* `SpineTask23.isIso_sumHomologyMap_of_iso` keeps its name and statement but lost its
  `[Fintype α] [DecidableEq α]` hypotheses; there is only one proof of it.
* Downstream, `isIso_sumCellHomology` lost its `Fintype` hypothesis (single proof);
  `isIso_tgtDecomp_finite` and `relJIsIso_finite` are one-line wrappers around the arbitrary
  theorems, not parallel proofs.

## E. Genericity check

`AlgebraicTopology.DirectSumHomology` imports exactly one project module,
`AlgebraicTopology.DirectSumComplex`; its transitive project-local closure is
`{DirectSumComplex, RelativeChains, SimplicialChains, Normalization}` — no `Nerve`, `Geometry`,
`StandardCell`, `Cech`, `GoodCover`, `Cohomology`, `E1`, `E2` or `Controls` module. This is
enforced mechanically by check 2 of `Spine/Audit/ArchitectureDAG.lean` (every
`AlgebraicTopology` module is tested) and, additionally, by a new explicit `auditNoReach` for
`DirectSumHomology` in check 5.

## F. Principal public declarations introduced or changed

Introduced (`SpineTask23`, in `AlgebraicTopology/DirectSumHomology.lean`):

* `sumHomologyMap_apply`, `homologyMap_retraction_sumHomologyMap`, `hom_finset_sum_f_apply`,
  `homologyMap_finset_idem` — the steps of the argument;
* `isIso_sumHomologyMap_of_splitting` — the general splitting criterion;
* `finsuppCx_sum_support_single` — the finite-support input;
* `isIso_sumHomologyMap_finsuppCxι` — **the arbitrary-index direct-sum homology theorem**;
* `sumHomologyMap_comp_right`.

Changed:

* `SpineTask23.isIso_sumHomologyMap` — moved module, same statement, now a corollary.
* `SpineTask23.isIso_sumHomologyMap_of_iso` — moved module, `[Fintype α] [DecidableEq α]`
  dropped (a strictly weaker hypothesis list, so all call sites are unaffected).
* `SpineTask24.isIso_sumCellHomology` — `[Fintype ↑(X.nonDegenerate r)]` dropped.
* `SpineTask24.isIso_tgtDecomp` — new name for the arbitrary-family statement;
  `isIso_tgtDecomp_finite` retained with its old statement as a wrapper.
* `SpineTask24.relJIsIso`, `SpineTask24.singularCellFamilyAdditivity` — new, arbitrary family;
  `relJIsIso_finite`, `singularCellFamilyAdditivity_finite`,
  `finiteSingularCellFamilyAdditivity_finite` retained as wrappers.

## G. Dead-code check

Two finite-only helpers in `DirectSumComplex` became unreachable once the general theorem
existed and were removed:

* `SpineTask23.finsupp_sum_single` (`∑ s : α, single s (x s) = x` for a `Fintype`);
* `SpineTask23.finsuppCx_sum_π_ι` (`∑ s : α, π s ≫ ι s = 𝟙` for a `Fintype`).

Both were used only by the old finite proof of `isIso_sumHomologyMap_of_iso`, and their content
is subsumed by `finsuppCx_sum_support_single`, which holds for an arbitrary index type. No
other declaration referenced them (checked by search over the whole project, including the
axiom-audit module).

Nothing else became unused: the finite wrappers listed in F are deliberately kept, per the
compatibility requirement.

## H. Namespace check

No task-number namespace was introduced. New generic declarations join the existing
`SpineTask23` namespace, which is where the direct-sum API (`finsuppCx`, `sumHomologyMap`, …)
already lives; splitting the API across two namespaces would have been worse for discovery than
the (historical, project-wide) namespace name. The Nerve-side additions stay in `SpineTask24`
next to the declarations they generalize. Renaming these two namespaces project-wide is a
mechanical change orthogonal to Task 27 and was not attempted here.

## I. Comment/docstring check

No production docstring mentions a task number or a work package. In the touched modules the
remaining `Task NN` / `WPk` references were rewritten in mathematical terms:

* `AlgebraicTopology/DirectSumComplex.lean` — module docstring rewritten (was “Task 23, WP6
  (algebraic half) — finite direct sums …”).
* `Nerve/CellFamily/RelativeChainDecomposition.lean` — section heading and the docstring of
  `isIso_sumCellHomology`.
* `Nerve/CellFamily/TargetDecomposition.lean` — module docstring and all five `WP` section
  headings and theorem docstrings.
* `Nerve/CellFamily/TargetMap.lean`, `Nerve/Comparison/FiniteCriterion.lean` — the cross
  references to the (formerly finite, formerly open) target decomposition.
* `Nerve/Comparison/RelJ.lean` — rewritten module docstring.

Task chronology is recorded here and in `TASK27_AUDIT.md`, not in the sources.
