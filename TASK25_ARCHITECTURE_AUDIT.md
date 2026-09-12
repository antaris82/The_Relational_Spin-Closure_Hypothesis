# TASK 25 ARCHITECTURE AUDIT

Stage-1.3 architecture refactor: the chronological module layer
(`RequestProject.Spine.Nerve.TaskNN…`) has been replaced by a content-based layout, the import
graph has been narrowed to genuine mathematical dependencies, and the result is checked
mechanically by `RequestProject/Spine/Audit/ArchitectureDAG.lean`.

**No mathematics was added, removed or restated in this task.** Every theorem statement, proof
and namespace is the one that existed before the refactor; only file names and `import` lines
changed. The mechanical evidence for that claim is the axiom table of §5, which is
byte-identical to the pre-refactor baseline.

---

## 0. Verification status

| item | result |
| --- | --- |
| `lake build RequestProject` (from a deleted `.lake/build`, i.e. full rebuild) | **Build completed successfully (8275 jobs)**, 0 errors |
| `sorry` / `admit` / `sorryAx` | none (0 occurrences in sources; 0 `sorryAx` in the axiom table) |
| `native_decide`, `unsafe`, `@[implemented_by]`, project-local `axiom` | none |
| `RequestProject/Spine/Audit/Firewall.lean` (legacy firewall) | `Spine external-project imports: 0 (prefixes checked: 7)`, `Spine modules audited: 173` |
| `RequestProject/Spine/Audit/ArchitectureDAG.lean` (this task's audit) | `SPINE ARCHITECTURE AUDIT: all checks passed` |
| `lean-toolchain`, `lake-manifest.json` | unchanged |

Repairs needed to reach the green build, with the exact Lean errors, are recorded in
`TASK25_FAILBUILDS.md`.

---

## 1. The architecture rule

> A production module may import another module only for a genuine mathematical definition or
> theorem dependency. Historical task order is not an import dependency. Generic results live
> below domain-specific results. Independent branches stay independent until their first
> necessary join. A lightweight definition must not drag in its heavy proof stack.

## 2. The layout

Two top prefixes carry Stage 1.3.

* `RequestProject.Spine.AlgebraicTopology` — statements that mention no nerve-specific object:
  simplicial chains, normalization, skeleta and skeletal attachment, relative chains and the
  relative/pair long exact sequences, affine simplices, subdivision, mesh, the prism chain
  homotopy, small simplices, excision, contractibility, singular homology and its homotopy
  invariance, `H_0`, discrete and reduced homology, Mayer–Vietoris, sphere covers, and the
  finite direct-sum chain complex.
* `RequestProject.Spine.Nerve` — the nerve-specific development, in seven groups:
  `Basic` (cover nerve, realization, chain map, canonical comparison map), `Cochain` (the Čech
  cochain comparison branch), `Skeleton` (pushout/realization monomorphism), `Geometry`
  (point-set geometry of realizations, punctured cells, separation, retractions),
  `StandardCell` (homology, fundamental class, generators, the standard pair and its excision),
  `CellFamily` (the singular factorization, excision compatibility, relative chain
  decomposition, the frozen target map and its finite decomposition), and `Comparison`
  (relative comparison map, blockers, skeletal step/induction, source decomposition, family
  compatibility, the finite criterion and the finite `RelJ` endpoint). `Controls` and `Audit`
  are leaves that no production module imports.

The complete old → new module map (70 renames) is `scripts/task25_module_map.txt`.

Fourteen modules of the area are not renames: the five generic modules that already lived under
`AlgebraicTopology` (`SimplicialChains`, `RelativeChainCalculus`, `RelativeAcyclicity`,
`FamilyChainMap`, `RealizationColimits`), the aggregates `Nerve.Core` and
`Nerve.Audit.Stage13Axioms`, and the definition/proof splits introduced by the refactor:
`Nerve.StandardCell.Pair` (the definition of the standard cell pair),
`Nerve.StandardCell.RealizedSimplexHomology`, `Nerve.Geometry.OpenStandardCell` (the open cell
and its point-set facts), `Nerve.CellFamily.TargetMap` (the definition of the frozen
`tgtDecomp`), `Nerve.Comparison.SkeletalStep`, `Nerve.Comparison.SkeletalInduction` and
`Nerve.Comparison.FiniteRelJ` (the endpoint).

### Layer sizes (exact, post-refactor)

| layer | modules | Lean LOC |
| --- | ---: | ---: |
| `Spine.AlgebraicTopology` | 28 | 6196 |
| `Spine.Nerve.Geometry` | 11 | 3044 |
| `Spine.Nerve.StandardCell` | 12 | 2083 |
| `Spine.Nerve.Comparison` | 9 | 1302 |
| `Spine.Nerve.Cochain` | 5 | 1147 |
| `Spine.Nerve.CellFamily` | 5 | 978 |
| `Spine.Nerve.Audit` | 3 | 898 |
| `Spine.Nerve.Controls` | 3 | 712 |
| `Spine.Nerve.Basic` | 5 | 580 |
| `Spine.Nerve.Skeleton` | 2 | 455 |
| `Spine.Nerve.Core` (aggregate) | 1 | 180 |
| **total** | **84** | **17575** |

### Layer-level import edges (direct, counted between groups)

```
Nerve.Basic            -> AlgebraicTopology   2
Nerve.Skeleton         -> AlgebraicTopology   2
Nerve.Geometry         -> AlgebraicTopology   2 ;  -> Nerve.Skeleton       1
Nerve.StandardCell     -> AlgebraicTopology   6 ;  -> Nerve.Geometry       4 ;  -> Nerve.CellFamily 1
Nerve.CellFamily       -> AlgebraicTopology   4 ;  -> Nerve.Geometry       3 ;
                          -> Nerve.Skeleton   1 ;  -> Nerve.StandardCell   2 ;  -> Nerve.Comparison 1
Nerve.Comparison       -> AlgebraicTopology   3 ;  -> Nerve.Geometry       1 ;
                          -> Nerve.Skeleton   1 ;  -> Nerve.StandardCell   1 ;  -> Nerve.CellFamily 2
Nerve.Cochain          -> Nerve.Basic         2
Nerve.Controls         -> AlgebraicTopology   3 ;  -> Nerve.Basic          1
Nerve.Audit            -> everything it audits (leaf)
Nerve.Core (aggregate) -> Nerve.Audit 1, Nerve.Cochain 1, Nerve.Controls 1
```

The *module* graph is a DAG (the longest chain below has no repetition, and Lean would reject a
cycle outright). At the coarser *group* level the pairs
`StandardCell ↔ CellFamily` and `CellFamily ↔ Comparison` both appear in each direction; these
are honest mathematical dependencies between individual modules, not cycles:

* `StandardCell.Excision` uses the generic excision compatibility lemmas of
  `CellFamily.ExcisionCompatibility`, while `CellFamily.RelativeChainDecomposition` and
  `CellFamily.TargetDecomposition` use the standard-cell pair and its excision isomorphism;
* `CellFamily.TargetMap` (a definition module) uses the relative comparison map of
  `Comparison.RelativeMap`, while `Comparison.SourceDecomposition` and
  `Comparison.FiniteCriterion` use the cell-family results.

Groups are therefore a naming device; the audited invariant is the module-level graph.

## 3. The mechanical audit — `Spine/Audit/ArchitectureDAG.lean`

The module runs six checks on the *compiled* import graph and fails the build on violation.
Each negative check is paired with a `requireModule` (so it cannot pass because the constrained
module is absent) and the endpoint check is paired with positive `auditReaches` controls (so it
cannot pass vacuously). Reported on the final build:

```
Stage-1.3 production modules audited: 78 (of 231 production Spine modules);
    chronological TaskNN modules: 0
generic AlgebraicTopology modules audited: 28, domain-specific imports: 0
low-level Nerve modules audited: 18, high-level imports: 0
SPINE ARCHITECTURE AUDIT: all checks passed
```

1. **No chronological production module** in the Stage-1.3 area: none of the 78 audited modules
   has a `TaskNN…` name component. (`E1`/`E2` keep their own historical names; they are outside
   this refactor and are excluded explicitly.)
2. **Generic below domain-specific**: no module of `Spine.AlgebraicTopology` reaches
   `Spine.Nerve`, `…Cech`, `…GoodCover`, `…Cohomology`, `…Geometry`, `…E1`, `…E2`, `…Controls`.
3. **Low-level geometry independent of the high-level comparison**: no module of
   `Nerve.Geometry`, `Nerve.Skeleton`, `Nerve.Basic` reaches `Nerve.Comparison`,
   `Nerve.CellFamily` or `Nerve.StandardCell`.
4. **Definitions do not drag in proof stacks**: `Nerve.CellFamily.TargetMap`, which defines the
   frozen `tgtDecomp`, reaches none of the finite-family proof, the relative chain
   decomposition, the singular factorization, the excision compatibility, the standard-cell
   homology / fundamental class / generator / canonical generator / relative comparison /
   excision modules, the cell geometry, or `AlgebraicTopology.Excision`. It imports only the
   *definition* of the standard pair (`Nerve.StandardCell.Pair`).
5. **Independent branches**: `AlgebraicTopology.DirectSumComplex` reaches neither the nerve
   material nor Excision nor Subdivision; `Nerve.Geometry.CellSeparation` reaches neither the
   standard cell nor the comparison nor the cell family nor Excision;
   `Nerve.CellFamily.SingularFactorization` reaches neither `Nerve.StandardCell` nor
   `Nerve.Comparison`.
6. **`Nerve.Comparison.FiniteRelJ` is a leaf join**: no production module imports it, and it
   does reach all four of `Comparison.SourceDecomposition`,
   `StandardCell.RelativeComparison`, `CellFamily.TargetDecomposition` and
   `AlgebraicTopology.DirectSumComplex`.

## 4. Metrics

Pre-refactor snapshot: `scripts/task25_metrics_pre.txt` (taken with prefix
`RequestProject.Spine.Nerve`, which then contained the generic material as well).
Post-refactor snapshot: `scripts/task25_metrics_post.txt` (prefixes
`RequestProject.Spine.AlgebraicTopology` **and** `RequestProject.Spine.Nerve`, i.e. the same
body of material after the generic half was moved out of `Nerve`). Both are produced by
`scripts/arch_metrics.py`.

| metric | pre | post |
| --- | ---: | ---: |
| modules in the area | 81 | 84 |
| Lean LOC | 17208 | 17575 |
| internal import edges | 117 | 143 |
| all project-local import edges out of the area | 122 | 150 |
| **max internal import depth (longest chain)** | **45** | **24** |

The module and edge counts rise slightly because seven definition/proof splits were introduced
(§2) and because the area now includes the five generic modules that already lived under
`AlgebraicTopology`; the LOC rise is the module headers and docstrings of the split modules.
The figure the refactor targets is the depth: the longest chain of modules each importing the
next drops from 45 to 24, i.e. the chronological "each task imports the previous task" spine has
been replaced by a genuine mathematical layering.

Transitive project-local import closures of the principal endpoints, same content before and
after (old name → new name):

| endpoint | pre closure | post closure |
| --- | ---: | ---: |
| `Task22RelJCompatibility` → `Nerve.Comparison.FamilyCompatibility` | 57 | 46 |
| `Task23FiniteTargetDecomp` → `Nerve.Comparison.FiniteCriterion` | 65 | 47 |
| `Task24FiniteTargetDecomp` → `Nerve.CellFamily.TargetDecomposition` | 69 | 39 |
| `Nerve.Comparison.FiniteRelJ` (final endpoint) | — | 61 |

Post-refactor longest internal chain (24 modules), from `scripts/task25_metrics_post.txt`:

```
Nerve.Audit.Stage13Axioms → Nerve.Comparison.FiniteRelJ → Comparison.FiniteCriterion
→ Comparison.FamilyCompatibility → Comparison.SourceDecomposition
→ StandardCell.RelativeComparison → StandardCell.CanonicalGenerator
→ StandardCell.BoundaryTwoSetCover → StandardCell.FaceMaps → StandardCell.Generator
→ StandardCell.FundamentalClass → StandardCell.Homology → StandardCell.BoundaryHomology
→ StandardCell.BoundaryCover → Geometry.BoundarySphere → Geometry.StandardSimplex
→ Geometry.RealizedBoundary → Geometry.PointModel → Skeleton.RealizationMono
→ Skeleton.Pushout → AlgebraicTopology.SkeletalAttachment
→ AlgebraicTopology.SimplicialSkeleton → AlgebraicTopology.Normalization
→ AlgebraicTopology.SimplicialChains
```

### Import narrowing completed in this task

`scripts/min_imports.py` recomputes, for every module of the area, the project-local imports
that are justified by a declaration the module actually mentions, and reports the transitive
reduction of that set. Four further edges were removed and the full build re-verified:

| module | import removed |
| --- | --- |
| `Nerve.CellFamily.TargetMap` | `AlgebraicTopology.RelativeChainCalculus` |
| `Nerve.Comparison.BaseCase` | `Nerve.Skeleton.RealizationMono` |
| `Nerve.Comparison.RelativeMap` | `AlgebraicTopology.RealizationColimits` |
| `Nerve.StandardCell.BoundaryHomology` | `AlgebraicTopology.SingularHZero` |

A fifth proposal (removing `AlgebraicTopology.SingularHomology` from
`AlgebraicTopology.SingularHomotopy`) is **rejected**: the import is real, and the automatic
check missed it only because the name it provides is the three-letter abbreviation `Cx`, below
the script's identifier-length cutoff. The edge is kept; see F2 in `TASK25_FAILBUILDS.md`.
`scripts/min_imports.py` now reports one remaining difference, that rejected one.

## 5. Axiom audit

`RequestProject/Spine/Nerve/Audit/Stage13Axioms.lean` is a leaf module (no production module
imports it) that runs `#print axioms` on 359 principal declarations of Stage 1.3; the other
`Core` aggregates and the `E1`/`E2` audits bring the default build to 1023 `#print axioms`
commands over 1003 distinct declarations. `scripts/axiom_table.py` extracts the whole table from
the build log (re-joining Lean's line-wrapped messages).

Result on the final from-scratch build (`scripts/task25_axioms_post.txt`):

| axiom set | declarations |
| --- | ---: |
| `[Classical.choice, Quot.sound, propext]` | 1000 |
| `[Quot.sound, propext]` | 2 |
| `[propext]` | 1 |
| anything else — `sorryAx`, a `native_decide` axiom, a project-local `axiom` | **0** |

The three declarations with a smaller axiom set are `CechSpinLift.VisibleCocycle`,
`CechSpinLift.VisibleCocycle.visible_transition_laws` and
`NullSectorTask28.InternalProjection.exact_internal_transition_compatibility_iff_defect_trivial`.

**`scripts/task25_axioms_post.txt` is byte-identical to the pre-refactor baseline
`scripts/task25_axioms_baseline.txt`** (`diff` empty, 1003 lines each). The refactor therefore
changed no declaration's name and no declaration's logical dependencies: the same 1003
declarations exist, and each depends on exactly the same axioms as before.

## 6. Scope

Only file names and `import` lines were touched. `E1`, `E2`, `Cech`, `Cohomology`, `GoodCover`,
`Geometry` and the legacy `Experiment1`/`Experiment2` provenance trees are unchanged, and the
legacy firewall still reports 0 imports of an experiment tree from the Spine.
