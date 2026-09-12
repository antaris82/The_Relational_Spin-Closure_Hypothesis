# Task 13 — external source ledger

Every source consulted for `TASK13_NORMALIZED_SKELETAL_COMPARISON.md` and for the four new
Lean modules. **Nothing was imported**: `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json` are unchanged, no external project or formalisation was added as a
dependency, and the mechanical firewall still reports `external-project imports = 0`,
`Experiment1 direct/transitive = 0`, `Experiment2 direct/transitive = 0`.

Influence classes used: `PINNED_LIBRARY_SOURCE`, `THEOREM_STATEMENT_REFERENCE`,
`PROOF_ROUTE_REFERENCE`, `BACKGROUND_ONLY`, `NOT_USED`.

Access date for all items: **2026-09-09**.

---

## 1. Pinned Mathlib source files (read directly from `.lake/packages/mathlib`)

The pin is `v4.28.0`, manifest rev `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.  These files
were read as *source*, and the declarations they contain are used in the proofs; they are part
of the build, not an external import.

| file | declarations used | influence |
| --- | --- | --- |
| `Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean` | `alternatingFaceMapComplex`, `AlternatingFaceMapComplex.objD`, `alternatingFaceMapComplex_obj_d` | `PINNED_LIBRARY_SOURCE` |
| `Mathlib/AlgebraicTopology/DoldKan/PInfty.lean` | `PInfty`, `PInfty_f_0`, `PInfty_f_idem`, `PInfty_f_naturality`, `QInfty`, `QInfty_f`, `PInfty_add_QInfty` | `PINNED_LIBRARY_SOURCE` |
| `Mathlib/AlgebraicTopology/DoldKan/Degeneracies.lean` | `σ_comp_PInfty` | `PINNED_LIBRARY_SOURCE` |
| `Mathlib/AlgebraicTopology/DoldKan/Decomposition.lean` | `decomposition_Q` | `PINNED_LIBRARY_SOURCE` |
| `Mathlib/AlgebraicTopology/DoldKan/Homotopies.lean` | `hσ`, `hσ'`, `hσ'_naturality`, `Hσ`, `natTransHσ` (naturality audit, §5.3 of the audit) | `PROOF_ROUTE_REFERENCE` |
| `Mathlib/AlgebraicTopology/DoldKan/HomotopyEquivalence.lean` | `homotopyPToId`, `homotopyPInftyToId`, `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex` | `PINNED_LIBRARY_SOURCE` |
| `Mathlib/AlgebraicTopology/DoldKan/Normalized.lean` | `N₁_iso_normalizedMooreComplex_comp_toKaroubi` | `PINNED_LIBRARY_SOURCE` (probe only) |
| `Mathlib/AlgebraicTopology/MooreComplex.lean` | `normalizedMooreComplex`, `inclusionOfMooreComplexMap` | `PINNED_LIBRARY_SOURCE` (probe only) |
| `Mathlib/AlgebraicTopology/SimplicialSet/Degenerate.lean` | `SSet.degenerate`, `SSet.nonDegenerate`, `mem_degenerate_iff`, `degenerate_eq_iUnion_range_σ`, `exists_nonDegenerate`, `Subcomplex.mem_degenerate_iff`, `Subcomplex.mem_nonDegenerate_iff` | `PINNED_LIBRARY_SOURCE` |
| `Mathlib/AlgebraicTopology/SimplicialSet/Skeleton.lean` | `SSet.skeleton`, `mem_skeleton`, `skeleton_obj_eq_top`, `mem_skeleton_obj_iff_of_nonDegenerate`, `skeleton_succ`; also the file's own `TODO` list, cited in the audit as evidence that the cell-attachment presentation of the skeleton is absent | `PINNED_LIBRARY_SOURCE` + `THEOREM_STATEMENT_REFERENCE` |
| `Mathlib/AlgebraicTopology/SimplicialSet/Subcomplex.lean` | `Subcomplex`, `toSSet`, `homOfLE` | `PINNED_LIBRARY_SOURCE` |
| `Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean` | `CochainComplex.IsKProjective`, `isKProjective_of_projective`, `IsKProjective.Qh_map_bijective` | `PROOF_ROUTE_REFERENCE` (Bridge A audit, probes only) |
| `Mathlib/Algebra/Homology/HomologySequence.lean` (`HomologicalComplex.HomologySequence.*`) | `snakeInput`, `composableArrows₃_exact`, `composableArrows₅_exact`, `δ_naturality` | `THEOREM_STATEMENT_REFERENCE` (WP7/WP10 audit) |
| `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` | `singularChainComplexFunctor`, `singularHomologyFunctor` | `THEOREM_STATEMENT_REFERENCE` (WP10 audit) |

## 2. Mechanical enumeration of the pinned environment

The negative findings of the audit (no excision, no relative singular homology, no cellular
homology, no CW structure on realizations, no `quasi-iso ⇒ homotopy equivalence`, no five
lemma) were obtained by enumerating `Lean.Environment.constants` in a scratch file importing
all of `Mathlib` and filtering by substring.  This is not an external source; it is recorded
here because it is the evidence for every `MISSING` classification.  Method and counts:
`TASK13_NORMALIZED_SKELETAL_COMPARISON.md`, §2.5.

* Influence: `PINNED_LIBRARY_SOURCE`.

## 3. Project-internal documents

* `TASK09_AUDIT.md`, `TASK10_AUDIT.md`, `TASK11_UPSTREAM_DELTA_AUDIT.md`,
  `TASK12_ACYCLIC_MODELS_APPLICABILITY.md` — the frozen canonical data, the Task-10 dualisation
  theorem, the upstream delta, and the Acyclic-Models verdict that selected the skeletal route.
* Influence: `PROOF_ROUTE_REFERENCE`.

## 4. Classical mathematical background (not consulted as text in this run)

The statements formalised here are classical and were reconstructed directly, not transcribed:

* the normalization theorem (the degenerate subcomplex is acyclic; `C ≃ C/D`) — Eilenberg–Mac
  Lane / Dold–Kan; in this run it is *derived from the pinned Dold–Kan projector* rather than
  reproved, so no textbook statement was needed;
* the cellular chain complex of a CW/simplicial pair — standard; used only to state the WP6
  target, which was then proved directly from the pinned skeleton API;
* excision, the long exact sequence of a pair, and `H_*(D^r, S^{r-1})` — standard; used only to
  *name* the missing theorems.
* Influence: `BACKGROUND_ONLY`.

No online source was retrieved for this task.
