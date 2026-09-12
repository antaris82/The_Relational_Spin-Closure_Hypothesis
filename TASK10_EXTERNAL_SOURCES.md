# TASK 10 — external formalization source ledger

Scope of the permitted search: existing Lean formalizations of simplicial versus singular
homology, homology of a geometric realization, the unit `K → Sing|K|`, acyclic carriers,
simplicial approximation, subdivision, and normalized versus unnormalized chains.

**No external project was imported.**  The project's `lakefile.toml` declares exactly one
dependency, `mathlib` at tag `v4.28.0`, and the mechanical firewall
(`RequestProject/Spine/Audit/Firewall.lean`) reports `Spine external-project imports: 0` on the
full build.  No proof block from any source below was copied.

Access date for every entry: **2026-09-08**.

---

## 1. Pinned dependency, inspected as source

| field | value |
| --- | --- |
| author/owner | The mathlib community |
| repository | `leanprover-community/mathlib4` |
| exact files | `Mathlib/AlgebraicTopology/SingularSet.lean`; `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`; `Mathlib/AlgebraicTopology/TopologicalSimplex.lean`; `Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean`; `Mathlib/AlgebraicTopology/MooreComplex.lean`; `Mathlib/AlgebraicTopology/DoldKan/**`; `Mathlib/AlgebraicTopology/ExtraDegeneracy.lean`; `Mathlib/AlgebraicTopology/SimplicialSet/**`; `Mathlib/AlgebraicTopology/ModelCategory/**`; `Mathlib/AlgebraicTopology/RelativeCellComplex/**`; `Mathlib/Geometry/Manifold/ChartedSpace.lean`; `Mathlib/Geometry/Manifold/IsManifold/Basic.lean`; `Mathlib/LinearAlgebra/Finsupp/**` (`Finsupp.llift`) |
| exact commit | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`), as pinned in `lake-manifest.json` |
| license | Apache 2.0 |
| access date | 2026-09-08 |
| constructions inspected | `sSetTopAdj`, `SSet.toTop`, `TopCat.toSSet`, `SSet.toTopSimplex`, `AlgebraicTopology.SSet.singularChainComplexFunctor`, `singularChainComplexFunctor`, `singularHomologyFunctor`, `alternatingFaceMapComplex`, `normalizedMooreComplex`, `PInftyToNormalizedMooreComplex`, `Abelian.DoldKan.equivalence`, `SimplicialObject.Augmented.ExtraDegeneracy`, `ExtraDegeneracy.homotopyEquiv`, `SSet.Skeleton`, `SSet.Subcomplex`, `RelativeCellComplex`, `HomotopicalAlgebra.ModelCategory`, `ChartedSpace.sum`, `IsManifold.disjointUnion`, `OpenPartialHomeomorph.lift_openEmbedding`, `Finsupp.llift`, `Finsupp.linearCombination`, `LinearMap.dualMap` |
| applies to Lean 4 / Mathlib v4.28.0 | yes — this *is* the pinned version |
| influence category | `MATHLIB_API_REFERENCE` for everything actually used (`Finsupp.llift`, `sSetTopAdj`, `OpenPartialHomeomorph.lift_openEmbedding`, `Topology.IsOpenEmbedding.sigmaMk`, `SecondCountableTopology.to_separableSpace`); `NEGATIVE_CONTROL` for the components confirmed **absent** (no `SSet.homology`, no excision, no Mayer–Vietoris for singular homology, no subdivision, no Eilenberg–Steenrod, no model structure on `SSet`/`TopCat`); `DESIGN_REFERENCE` for `IsManifold.disjointUnion`, whose proof pattern (same chart ⟹ compatible, different charts ⟹ empty source) was re-derived for the `Σ`-indexed case |

Notes.

* `Mathlib/AlgebraicTopology/SingularSet.lean` line 37 records, in the pinned tree itself, the
  open TODO "Show the adjunction `sSetTopAdj` is a Quillen equivalence".  This is the single
  most important negative datum of Task 10 and it is a *primary* source, not documentation.
* The `IsManifold.disjointUnion` proof was read to learn the idiom
  `ContDiffGroupoid.mem_of_source_eq_empty` and `lift_openEmbedding_trans`.  The Task-10
  instance `SpineTask10.isManifoldSigma` is written independently for `Σ _ : ι, H`; no proof
  block was copied.

---

## 2. Sources considered and not used

| source | why inspected | outcome |
| --- | --- | --- |
| Current upstream `mathlib4` `master` documentation and file tree, for `AlgebraicTopology.SimplicialSet.Homology`, `Subdivision`, `EilenbergSteenrod`, excision | to check whether the missing components exist *later* than the pin | `NOT_USED`. The task forbids inferring pinned availability from current upstream documentation, and forbids using declarations that are unavailable in v4.28.0. No claim is made in this project about the state of upstream beyond the pinned tree, and no upstream-only name is referenced in any Lean file. |
| `leanprover-community/mathlib4` issue/PR history on singular homology and the Quillen equivalence | to look for an in-flight formalization of the comparison | `NOT_USED`. Nothing from it is relied upon; the pinned tree's own TODO comment is the recorded evidence instead. |
| Other Lean 4 algebraic-topology repositories (searched for: acyclic models, simplicial approximation, barycentric subdivision, `Sing|K|` comparison) | to see whether an importable or adaptable development exists | `NOT_USED`. Importing external projects is forbidden by the task, and no such development was relied upon. |
| Standard textbook treatments of the simplicial-to-singular comparison (acyclic models; cellular/skeletal induction) | to fix the shape of the missing theorem `T` and of the route matrix | `BACKGROUND_ONLY` / `THEOREM_DECOMPOSITION_REFERENCE`. Used only to decide *what* to state as the blocker (`ChainHomotopyEquivData`) and how to decompose the recommended successor route (compact supports → acyclicity of models → acyclic models → assembly). No text, statement or proof was copied. |

---

## 3. Influence-category summary

```
MATHLIB_API_REFERENCE            : pinned mathlib v4.28.0 (declarations actually used)
NEGATIVE_CONTROL                 : pinned mathlib v4.28.0 (declarations confirmed absent)
DESIGN_REFERENCE                 : IsManifold.disjointUnion proof idiom
THEOREM_DECOMPOSITION_REFERENCE  : textbook shape of the acyclic-models route
BACKGROUND_ONLY                  : textbook simplicial-vs-singular comparison
NOT_USED                         : current upstream mathlib beyond the pin; external Lean repos
```
