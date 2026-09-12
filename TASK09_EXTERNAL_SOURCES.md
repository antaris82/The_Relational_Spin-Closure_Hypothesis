# TASK 09 — external source ledger

## Policy

No external repository may become a dependency of `Spine/**`. The mechanical check is in
`RequestProject/Spine/Audit/Firewall.lean` (`auditNoExternal`, run over every Spine module);
it reports `external-project imports = 0`.

## Sources consulted during Task 9

| owner / author | repository | file | commit | licence | accessed | construction / theorem consulted | influence |
| --- | --- | --- | --- | --- | --- | --- | --- |
| leanprover-community | `mathlib4` (the pinned dependency of this project) | `Mathlib/AlgebraicTopology/SingularSet.lean` | `v4.28.0` as pinned in `lake-manifest.json` | Apache-2.0 | 2026-09-08 | `TopCat.toSSet`, `SSet.toTop`, `sSetTopAdj`, `SSet.toTopSimplex`, `TopCat.toSSetObjEquiv` | `MATHLIB_API_REFERENCE` (and a genuine dependency: Mathlib is the project's declared dependency) |
| leanprover-community | `mathlib4` | `Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean` | `v4.28.0` | Apache-2.0 | 2026-09-08 | `SimplicialObject.δ`, `σ`, `δ_comp_δ`, `σ_comp_σ`, `δ_comp_σ_self`, `δ_comp_σ_succ`, `δ_comp_σ_of_le`, `δ_comp_σ_of_gt` | `MATHLIB_API_REFERENCE` |
| leanprover-community | `mathlib4` | `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` | `v4.28.0` | Apache-2.0 | 2026-09-08 | `SSet.singularChainComplexFunctor`, `singularHomologyFunctor` — inspected to establish that the pinned library contains definitions only, and no comparison theorem | `NEGATIVE_CONTROL` |
| leanprover-community | `mathlib4` | `Mathlib/AlgebraicTopology/SimplicialSet/**` (`Degenerate.lean`, `NonDegenerateSimplices.lean`, `Skeleton.lean`) | `v4.28.0` | Apache-2.0 | 2026-09-08 | inspected for an existing CW/skeletal comparison; none found | `NEGATIVE_CONTROL` |

No non-Mathlib Lean formalisation was inspected during Task 9. The Task-5 and Task-8 ledgers
(`TASK05_EXTERNAL_SOURCES.md`, `TASK08_EXTERNAL_SOURCES.md`) are preserved unchanged and remain
the record for the earlier tasks.

## Categories used

`BACKGROUND_ONLY`, `DESIGN_REFERENCE`, `THEOREM_DECOMPOSITION_REFERENCE`,
`MATHLIB_API_REFERENCE`, `NEGATIVE_CONTROL`, `NOT_USED`.
