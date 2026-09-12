# Task 29 — code hygiene

Task 29 is a completion task, so consolidation was preferred to new modules; a new module was
created only where the material is generic and could not live in an existing file without
violating the layering.

## 1. Modules touched

| module | status | why |
|---|---|---|
| `Nerve/Geometry/SkeletalFactorization.lean` | edited (inherited) | compile repair; universe generalization of the compact domain |
| `Nerve/Skeleton/SkeletalSupport.lean` | edited (inherited) | `skeletalSupport` proved here, next to the proposition it discharges; docstring corrected |
| `Nerve/Comparison/GlobalHomology.lean` | edited (inherited) | unconditional `globalHomologyIso` and the subsumption remark appended next to the conditional theorem |
| `Nerve/Cochain/Dualization.lean` | edited (inherited) | generic part moved down and re-exported |
| `AlgebraicTopology/NaiveHomology.lean` | **new** | generic categorical/elementary homology dictionary; may not live under `Nerve` |
| `AlgebraicTopology/DualCohomology.lean` | **new** | generic `ℤ₂` duality theorem; may not live under `Nerve` |
| `Nerve/Comparison/GlobalCohomology.lean` | **new** | the Nerve-specific assembly; may not live in `Cochain/`, which is below the comparison layer |
| `Nerve/Audit/Stage13Axioms.lean` | edited | `#print axioms` for the fourteen new/renewed endpoints |
| `Spine/Audit/ArchitectureDAG.lean` | edited | the layering rule replaces the "RelJ is a leaf" rule |

No `Task29*.lean` module exists; no module in the production DAG carries a chronological name
(mechanically checked: "chronological TaskNN modules: 0").  Chronological names appear only in
this and the other audit/provenance documents.

## 2. No duplicated mathematics

* The generic dualisation (`freeDualEquiv`, `dualOf`, `dualOf_apply`,
  `linearCombination_dualOf`, `dualOf_id`, `dualOf_comp`, `dualOf_add`, `dualOf_sum`,
  `dualOf_lmapDomain`) existed in `Nerve/Cochain/Dualization.lean`, a Nerve module, although it
  mentions nothing about nerves.  It now lives once, in
  `AlgebraicTopology/DualCohomology.lean` (namespace `SpineDualCohomology`), and
  `Dualization.lean` re-exports it, so `NerveGeom.dualOf` and all its lemmas keep their names
  and their single proof.  The Nerve-specific identifications (`dualOf_simpBoundary`,
  `dualOf_singBoundary`, `dualOf_chainMap`) stayed where they were.
* The exhaustive-homology assembly (`SpineExhaustion.isIso_homologyMap_of_exhaustive`) was
  reused, not re-derived; it remains free of any Nerve dependency.
* There is exactly one global comparison route.  The finite-dimensional theorem
  `SpineTask16.finiteDimensional_homologyIso` is retained unchanged for regression, and
  `NerveComparison.homologyIso_of_hasDimensionLT` records, in the layer above it, that its
  dimension bound and its relative hypothesis are no longer needed — the two hypotheses are
  kept there only to exhibit the subsumed statement and are marked unused (`_hrel`).
  It could not be re-proved *inside* `Comparison/SkeletalInduction.lean` as a corollary without
  inverting the import order (that module is below `GlobalHomology`).
* No second comparison map, no replacement equivalence and no `sorry`-ed helper survives.

## 3. Obsolete documentation removed

* `Nerve/Skeleton/SkeletalSupport.lean` no longer says that "every singular simplex of `|K|`
  already lives in some `|Sk K r|` … is the remaining input, recorded as the proposition
  `SkeletalSupport K`".  It now states that both halves are theorems and points at
  `skeletalSupport`.  The proposition itself is kept, because the assembly is phrased in terms
  of it; the docstring says so explicitly.
* `Nerve/Comparison/GlobalHomology.lean` no longer presents
  `globalHomologyIso_of_skeletalSupport` as the main theorem; the unconditional
  `globalHomologyIso` is, and the conditional form is described as the intermediate step.

## 4. Style

* No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `partial`, `@[implemented_by]`
  anywhere in the project.
* One `set_option maxHeartbeats 1000000 in` was needed, on
  `SpineDualCohomology.bijective_Hmap`; the reason (higher-order unification against families of
  free modules) is documented in `TASK29_FAILBUILDS.md` §F2.
* No `exact?`/`apply?` leftovers, no `skip`, no `nolint`, no linter suppression.
* All new declarations carry doc comments; the two new generic modules carry module docstrings
  stating explicitly that they are independent of simplicial sets, nerves, covers and geometry.
