# Task 29 — completion and certification of the Task-28 global comparison

**Outcome A.**  All three targets are theorem-level complete and sorry-free:

| statement | Lean name |
|---|---|
| `∀ K, SkeletalSupport K` | `NerveSkeleton.skeletalSupport` |
| `∀ K q, H_q(J_K)` is an isomorphism | `NerveComparison.globalHomologyIso` |
| `∀ 𝓤 n, geometricHmap 𝓤 n` is bijective | `NerveGeom.geometricHmap_bijective` |
| `GeometricComparison 𝓤` unconditionally | `NerveGeom.geometricComparison` |

The frozen canonical map is untouched: `J_K = C_*(η_K)` is
`SpineTask14.sSetChainComplexFunctor.map (sSetTopAdj.unit.app K)` throughout, and the
cohomological endpoint is the already existing `NerveGeom.geometricHmap`, not a replacement.

Environment: Lean 4.28.0, Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json` are unchanged.  No `sorry`, no
`admit`, no new `axiom`, no `native_decide`, no `unsafe`, no `partial`, no `@[implemented_by]`.

---

## 1. Provenance: what is inherited, what is repaired, what is new

### 1.1 Task-28 inherited source (used as delivered, not rebuilt)

| module | inherited content |
|---|---|
| `AlgebraicTopology/ExhaustiveHomology.lean` | `SpineExhaustion.isIso_homologyMap_of_exhaustive` and its three chases (`exists_stage_cycle`, `exists_stage_homology_class`, `exists_later_stage_zero`) |
| `Nerve/Geometry/RealizationTopology.lean` | weak topology of `|K|`, `carrierDim`, `exists_carrierDim_bound`, `mem_range_skeleton_iff` |
| `Nerve/Geometry/SkeletalFactorization.lean` | `isClosedMap_realization_subcomplex`, `exists_skeletal_factorization` |
| `Nerve/Skeleton/SkeletalSupport.lean` | `realization_transition_injective`, `realization_skIncl_injective`, the proposition `SkeletalSupport`, `singSkIncl_injective` |
| `Nerve/Comparison/GlobalHomology.lean` | the families `simpFamily`/`singFamily`, the cocones, `famJ`, `globalJ`, the exhaustion lemmas, `globalHomologyIso_of_skeletalSupport` |

None of these constructions was replaced.  Everything Task 29 adds sits **on top** of them.

### 1.2 Task-29 repairs to inherited source

* `Nerve/Geometry/SkeletalFactorization.lean` did **not** compile in the pinned environment
  (two errors inside `isClosedMap_realization_subcomplex`; see `TASK29_FAILBUILDS.md` §F1).
  The repair is proof-only: one `show` and two explicit arguments.  No statement changed.
* The same file's `exists_skeletal_factorization` was **generalized** from a compact domain in
  `Type u` to a compact domain in any universe `Type v`; this is what lets it be applied to the
  domain `stdSimplex ℝ (Fin (q+1))` of a singular simplex.  Strictly weaker hypothesis, same
  conclusion.
* `Nerve/Skeleton/SkeletalSupport.lean`: the module docstring no longer claims that skeletal
  support is an external input (it is now proved in the same file).
* `Nerve/Comparison/GlobalHomology.lean`: docstring updated; two theorems appended (below).
* `Nerve/Cochain/Dualization.lean`: the *generic* dualisation content was moved down to
  `AlgebraicTopology/DualCohomology.lean` and re-exported, so there is exactly one copy
  (see §5).

### 1.3 Task-29 genuinely new mathematics

1. **`NerveSkeleton.skeletalSupport`** — for every simplicial set `K`, every singular simplex
   of `|K|` comes from a finite skeleton.  Proof: a singular `q`-simplex is (via
   `TopCat.toSSetObjEquiv`) a continuous map from the compact space `stdSimplex ℝ (Fin (q+1))`
   into `|K|`; `NerveTopology.exists_skeletal_factorization` factors it continuously through
   some `|Sk K r|`, and the factorization *is* the required singular simplex of `|Sk K r|`,
   because the equivalence is natural in the space (that naturality is `rfl`).
   No `Fintype`, `Finite`, `HasDimensionLT`, finite cover or finite nerve occurs.

2. **`NerveComparison.globalHomologyIso`** — the unconditional global comparison, obtained by
   feeding (1) into the inherited `globalHomologyIso_of_skeletalSupport`.
   `NerveComparison.homologyIso_of_hasDimensionLT` records that the finite-dimensional theorem
   `SpineTask16.finiteDimensional_homologyIso` is subsumed.

3. **`SpineNaiveHomology`** (`AlgebraicTopology/NaiveHomology.lean`, new) — the dictionary
   between Mathlib's categorical homology of `ChainComplex (ModuleCat R) ℕ` and the elementary
   submodule/quotient homology the cochain layer of the Spine is written in:
   `cycles`, `boundaries`, `Homology`, `cls`, `homologyMap`, the comparison map `zeta` with
   `zeta_surjective`, `zeta_eq_zero_iff`, `zeta_naturality`, and the transfer theorem
   `bijective_homologyMap_of_isIso`.  Generic: no simplicial set, no nerve, no geometry.

4. **`SpineDualCohomology`** (`AlgebraicTopology/DualCohomology.lean`, new) — the duality
   theorem over `ℤ₂`:

   > if a chain map of free `ℤ₂`-complexes is an isomorphism on homology in every degree, then
   > its transpose is an isomorphism on the cohomology of the dual (function-type) complexes in
   > every degree — `SpineDualCohomology.bijective_Hmap`.

   The two ingredients are `mem_coboundaries_iff` (a cocycle is a coboundary exactly when it
   annihilates the cycles; the non-trivial direction factors a functional through the image of
   the differential and extends it by `LinearMap.exists_extend`) and
   `exists_cocycle_of_functional` (a functional annihilating the boundaries is realised by a
   cocycle).  Only two properties of `ℤ₂` are used, both consequences of its being a field.
   No universal-coefficient theorem is invoked, no finite dimensionality, no chain homotopy.

5. **`NerveGeom.bijective_naive_homologyMap`, `geometricHmap_bijective`, `geometricComparison`**
   (`Nerve/Comparison/GlobalCohomology.lean`, new) — the assembly.

---

## 2. The assembly, step by step

1. `SpineTask14.sSetChainComplexFunctor.obj (coverNerveSSet 𝓤)` has, degreewise, exactly the
   Task-9 chain modules, and its differential and functorial action are exactly
   `NerveGeom.simpBoundary` and `NerveGeom.chainMap`
   (`sSetChainComplexFunctor_X/_d/_map_f`, `simpBoundary_eq`, `singBoundary_eq`,
   `chainMap_eq_unitChainMap` — the last is `rfl`).
2. `NerveComparison.globalHomologyIso (coverNerveSSet 𝓤) n` gives the categorical statement.
3. `SpineNaiveHomology.bijective_homologyMap_of_isIso` turns it into bijectivity of the
   elementary homology map of `(simpBoundary 𝓤, singBoundary |N(𝓤)|, chainMap 𝓤)` — this is
   `NerveGeom.bijective_naive_homologyMap`.
4. `NerveGeom.dualOf_simpBoundary`, `dualOf_singBoundary`, `dualOf_chainMap` say that the
   Spine's cochain data are the transposes of that chain data.
5. `SpineDualCohomology.bijective_Hmap` then gives bijectivity of
   `(NerveGeom.geometricCochainMap 𝓤).Hmap n`; the generic `Hmap` is *definitionally* the
   existing one, because the cocycles are `ker δ` on both sides and the coboundaries enter the
   generic theory as a parameter satisfying `Bd 0 = ⊥`, `Bd (n+1) = range (δ n)` (both `rfl`
   here).
6. `NerveGeom.geometricHmap 𝓤 n = cechCohomologyEquivSSet 𝓤 n ∘ (geometricCochainMap 𝓤).Hmap n`
   with a linear *equivalence* on the left, so bijectivity transfers:
   `NerveGeom.geometricHmap_bijective`, hence `NerveGeom.geometricComparison`.

Nothing in this chain assumes `ChainHomotopyEquivData`, a good cover, a Nerve Theorem, finite
dimensionality, finiteness of the nerve, or any unproved comparison hypothesis.

---

## 3. Regression checks

All of the following still exist with unchanged statements and are part of the green build:

`SpineTask24.relJIsIso`, `SpineTask16.skeletalInduction`,
`SpineTask16.finiteDimensional_homologyIso`, `NerveGeom.geometricHmap`,
`NerveGeom.dualOf_chainMap`, `NerveGeom.GeometricComparison`, together with all Task-28
factorization and topology results (`isClosedMap_realization_subcomplex`,
`exists_skeletal_factorization` — the latter with a strictly weaker universe hypothesis —
`realization_skIncl_injective`, `globalHomologyIso_of_skeletalSupport`,
`isIso_homologyMap_of_exhaustive`).  No theorem statement was weakened anywhere.

`NerveGeom.dualOf` and its algebraic lemmas keep their names (they are re-exported from the
generic layer), so `Nerve/Cochain/ChainHomotopyComparison.lean` and the Task-10 audit in
`Nerve/Core.lean` are unaffected.

---

## 4. Build and axiom audit

* Cold build: `rm -rf .lake/build && lake build RequestProject` → success, 0 errors.
* `Spine/Audit/Firewall.lean`: 176 Spine modules audited, 0 legacy (`Experiment1`/`Experiment2`)
  imports, direct or transitive.
* `Spine/Audit/ArchitectureDAG.lean`: all checks passed — 92 Stage-1.3 production modules
  audited (of 245 production Spine modules), 0 chronological `TaskNN` modules, 34 generic
  `AlgebraicTopology` modules with 0 domain-specific imports, 24 low-level Nerve modules with 0
  high-level imports, and the new comparison-layering rule
  `RelJ → GlobalHomology → GlobalCohomology` (see §6).
* `#print axioms` (in `Nerve/Audit/Stage13Axioms.lean`) on every principal declaration of this
  task:

  | declaration | axioms |
  |---|---|
  | `NerveTopology.isClosedMap_realization_subcomplex` | `[propext, Classical.choice, Quot.sound]` |
  | `NerveTopology.exists_skeletal_factorization` | `[propext, Classical.choice, Quot.sound]` |
  | `NerveSkeleton.skeletalSupport` | `[propext, Classical.choice, Quot.sound]` |
  | `SpineExhaustion.isIso_homologyMap_of_exhaustive` | `[propext, Classical.choice, Quot.sound]` |
  | `NerveComparison.globalHomologyIso_of_skeletalSupport` | `[propext, Classical.choice, Quot.sound]` |
  | `NerveComparison.globalHomologyIso` | `[propext, Classical.choice, Quot.sound]` |
  | `NerveComparison.homologyIso_of_hasDimensionLT` | `[propext, Classical.choice, Quot.sound]` |
  | `SpineNaiveHomology.bijective_homologyMap_of_isIso` | `[propext, Classical.choice, Quot.sound]` |
  | `SpineDualCohomology.mem_coboundaries_iff` | `[propext, Classical.choice, Quot.sound]` |
  | `SpineDualCohomology.exists_cocycle_of_functional` | `[propext, Classical.choice, Quot.sound]` |
  | `SpineDualCohomology.bijective_Hmap` | `[propext, Classical.choice, Quot.sound]` |
  | `NerveGeom.bijective_naive_homologyMap` | `[propext, Classical.choice, Quot.sound]` |
  | `NerveGeom.geometricHmap_bijective` | `[propext, Classical.choice, Quot.sound]` |
  | `NerveGeom.geometricComparison` | `[propext, Classical.choice, Quot.sound]` |

  No `sorryAx`, no `native_decide` axiom, no project-local axiom.  This is exactly the
  Task-27/Task-28 baseline `[propext, Classical.choice, Quot.sound]`, extended by the fourteen
  declarations above (the new audited declarations of this task).

  The full table extracted from the cold-build log is `scripts/task29_axioms_post.txt`: 1024
  audited declarations (1021 with `[propext, Classical.choice, Quot.sound]`, 2 with
  `[Quot.sound, propext]`, 1 with `[propext]`, 0 with anything else), against 1010 in the
  Task-27 baseline `scripts/task27_axioms_post.txt`.  The difference is exactly: the fourteen
  new declarations above, plus the three names `NerveGeom.dualOf`,
  `NerveGeom.dualOf_comp`, `NerveGeom.linearCombination_dualOf` now being audited under their
  generic names `SpineDualCohomology.*` (the consolidation of §5 — same constants, moved one
  layer down), plus `SpineDualCohomology.dualOf`, `dualOf_comp`, `linearCombination_dualOf`.

---

## 5. Code hygiene at a glance

See `TASK29_CODE_HYGIENE.md`.  In summary: three new modules, all mathematically named, none
chronological; the generic dualisation moved down one layer and re-exported so that no
declaration is duplicated; obsolete "remaining input" documentation removed.

---

## 6. Architecture

The Task-27 rule "`RelJ` is an absolute leaf" is mathematically obsolete once the global
comparison consumes it.  It was **replaced** (not deleted, not weakened) by the layering rule

```
lower AlgebraicTopology
        ↓
lower Nerve geometry / cell machinery
        ↓
Nerve.Comparison.RelJ
        ↓
Nerve.Comparison.GlobalHomology
        ↓
Nerve.Comparison.GlobalCohomology
```

mechanically checked as: (a) only the three modules of the global comparison layer may reach
`RelJ`; (b) nothing may reach the endpoint `GlobalCohomology`; (c) no generic, geometry,
skeleton, basic, cell-family or standard-cell module may reach `GlobalHomology` or
`GlobalCohomology`; (d) positive controls that `RelJ` reaches its five branches, that
`GlobalHomology` reaches `RelJ`, `SkeletalInduction`, `SkeletalSupport`, `SkeletalFactorization`
and `ExhaustiveHomology`, and that `GlobalCohomology` reaches `GlobalHomology`, `Dualization`,
`DualCohomology` and `NaiveHomology`.  Invariants (a)–(d) are strictly stronger than "the
project builds": the checks fail on any upward or downward violation, and no check can pass
vacuously.  `AlgebraicTopology` still imports no Nerve module (check 2, 34 modules), the
low-level Nerve layer still imports no comparison module (check 3, 24 modules), there is no
import cycle (the build is a DAG by construction) and no umbrella import was used.

---

## 7. Metrics

Measured with `scripts/arch_metrics.py` (Stage-1.3 = `Spine.AlgebraicTopology` + `Spine.Nerve`);
snapshots in `scripts/task29_metrics_pre.txt` and `scripts/task29_metrics_post.txt`.

| metric | pre-Task-29 (= Task-28 OOB tree) | post-Task-29 |
|---|---|---|
| active `RequestProject/Spine` Lean modules | 258 | 261 |
| active `RequestProject/Spine` Lean LOC | 51052 | 51919 |
| Stage-1.3 relevant modules | 95 | 98 |
| Stage-1.3 relevant LOC | 19401 | 20222 |
| internal import edges (Stage-1.3) | 158 | 165 |
| maximum internal import depth | 24 | 26 |
| transitive closure of `GlobalHomology` | 71 | 75 |
| transitive closure of the final endpoint | — (`GlobalCohomology` did not exist) | 182 project-local, 85 within Stage-1.3 |

The Task-28 OOB figures quoted in the task statement (≈258 modules / ≈51052 LOC) were verified
against the actual starting tree and are exact.

**Justification of the depth increase (24 → 26).**  The longest internal chain now runs
`… → RelJ → GlobalHomology → GlobalCohomology → (audit)`.  The two extra levels are exactly the
two new mathematical layers: the global homology comparison consumes `RelJ` (blocker B3), and
the cohomological comparison consumes the global homology comparison.  Neither edge can be
removed without deleting the corresponding theorem; the increase is therefore forced by the
mathematics, not by packaging.

---

## 8. Frontier

```
B1: CLOSED
B2: CLOSED
B3 finite: CLOSED
B3 arbitrary: CLOSED
global canonical simplicial–singular homology comparison: CLOSED
canonical cohomology comparison: CLOSED
NEXT: genuine Nerve Theorem for the actual good cover  (NOT started here)
```

Neither the Nerve Theorem nor the identification with `w₂(TM)` was begun.
