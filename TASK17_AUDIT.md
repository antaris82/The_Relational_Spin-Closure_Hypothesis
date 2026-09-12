# Task 17 — Standard Cell Pair and the B1 → B3 Bridge

**Outcome: D — boundary topology closed, homology calculation remains.**

The Task-16 *set-theoretic* identification of the realized boundary has been upgraded to a
topological one (outcome E), and beyond it: the realized boundary is now formally identified,
by an explicit homeomorphism, with the standard sphere `S^{r-1}`, and the realized standard
simplex with the geometric standard simplex (contractible, compact, Hausdorff).  **B1 (the
relative homology of the standard cell pair) is *not* proved**, and neither is its generator,
the single-cell relative comparison, the attached-cell excision/additivity theorem, or B3.
The first missing theorem is isolated in §7 below.

Nothing was assumed: every topological hypothesis used (compactness, Hausdorffness,
continuity, injectivity) is proved inside the project in the pinned environment.

---

## 1. Exact new modules

| module | content |
|---|---|
| `RequestProject/Spine/Nerve/Task17StandardCellTopology.lean` | WP2, WP3, WP5, WP6(low dimensions) |
| `RequestProject/Spine/Nerve/Task17BoundarySphere.lean` | WP6 (the sphere) |
| `RequestProject/Spine/Nerve/Task17AxiomAudit.lean` | `#print axioms` for every principal Task-17 declaration |

No existing module was modified.  `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`
are untouched.  No `axiom`, no `sorry`, no `admit`, no `native_decide` was introduced.

## 2. Exact reused Task-14/15/16 modules (frozen, never redefined)

* `Nerve/Task13CanonicalMap.lean`, `Nerve/Task13Skeletal.lean` — the canonical `J = C_*(η_K)`
  and the skeleta; untouched and not re-derived.
* `Nerve/Task14RelativeChains.lean`, `Nerve/Task14RelativeLES.lean`,
  `Nerve/Task14Comparison.lean` (`relJ`), `Nerve/Task14Blocker.lean` (`RelJIsIso`),
  `Nerve/Task14SkeletalAttachment.lean` — the relative chain complexes, the LES, the canonical
  relative comparison `J_r^rel` and the attachment machinery.  Task 17 does **not** touch,
  restate or replace any of them.
* `Nerve/Task15Pushout.lean`, `Nerve/Task15RealizationMono.lean` (`Real`, `StandardCellMono`,
  the reduction), `Nerve/Task15BaseCase.lean` — the skeletal induction infrastructure.
* `Nerve/Task16PointModel.lean` — `Rz`, `coord`, `coord_naturality`, `faceSimplex`,
  `subFaceMap`, `subFaceMap_comp_ι`, `subCoord`, `subNormalForm`, `subcomplexMono`,
  `faceMap`, `bdCoord`, `normalForm`, `standardCellMono`.
* `Nerve/Task16Consequences.lean` — `range_bdCoord`, `compl_range_bdCoord`,
  `range_realization_boundary`, `boundaryZero_realization_isEmpty`,
  `realization_skInc_injective`, `skeletalInduction`, `finiteDimensional_homologyIso`.

## 3. WP1 — audit of the inherited Task-16 standard-simplex topology

Exact statements available *before* Task 17 (all in universe-polymorphic form; `Rz = SSet.toTop ⋙ forget TopCat`):

| # | requested item | exact theorem | what it is |
|---|---|---|---|
| 1 | barycentric realization of `|Δ[r]|` | `SpineTask16.coord (n) : Rz.obj (stdSimplex.obj n) ≃ stdSimplex ℝ (Fin (n.len+1))` | **bijection of sets only** (an `Equiv`), built from `SSet.toTopSimplex` |
| 2 | nonnegativity | `stdSimplex.zero_le` (Mathlib) | property of the target model |
| 3 | sum to one | `stdSimplex.sum_eq_one` (Mathlib) | property of the target model |
| 4 | vertex coordinates | *(not available in Task 16)* — supplied in Task 17 as `SpineTask17.simplexHomeo_vertex` | equality of points |
| 5 | face-coordinate behaviour | `SpineTask16.coord_naturality`, `subCoord_subFaceMap`, `bdCoord_faceMap` | equalities of points |
| 6 | `im |∂Δ[r]| = {x : ∃ i, λᵢ x = 0}` | `SpineTask16.range_bdCoord`, `range_realization_boundary` | **equality of sets/images**, no topology |
| 7 | complement = interior | `SpineTask16.compl_range_bdCoord` | equality of sets |
| 8 | injectivity of `|∂Δ[r]| → |Δ[r]|` | `SpineTask16.standardCellMono` | **injection only** |
| 9 | subcomplex generalisation | `SpineTask16.subcomplexMono` | injection only |
| 10 | normal form | `SpineTask16.subNormalForm`, `normalForm` | existence + (implicitly) uniqueness used inside `subcomplexMono` |

Explicitly: before Task 17 the project had **bijections and set equalities only** — no
continuous bijection statement, no embedding, no homeomorphism, no statement about subspace
topologies, and no compactness or Hausdorffness anywhere in the realization layer.

## 4. WP2/WP3/WP5/WP6 — what is now theorem-level

All in `SpineTask17`.

**WP3 (realized simplex = geometric simplex).**
* `simplexHomeo (n) : ↥(SSet.toTop.obj (stdSimplex.obj n)) ≃ₜ stdSimplex ℝ (Fin (n.len+1))` —
  a **homeomorphism**, obtained from the pinned identification `SSet.toTopSimplex` read in
  `TopCat` plus `Homeomorph.ulift`.  No second coordinate model is introduced:
* `coe_simplexHomeo : ⇑(simplexHomeo n) = SpineTask16.coord n` — holds **by `rfl`**;
* `simplexHomeo_naturality` — the simplicial operators act by `stdSimplex.map`;
* `simplexHomeo_vertex : simplexHomeo ⦋n⦌ (realizedVertex i) = stdSimplex.vertex i`;
* `compactSpace_realized_simplex`, `t2Space_realized_simplex` — **proved**, not assumed;
* the realized boundary maps onto `{λ : ∃ i, λᵢ = 0}` (item 4 of WP3) is `boundaryHomeo`.

**WP5 (contractibility).** `contractibleSpace_realized_simplex (n) :
ContractibleSpace ↥(SSet.toTop.obj Δ[n])`, by transporting `Convex.contractibleSpace` for the
convex set `stdSimplex ℝ (Fin (n+1))` along `simplexHomeo`.  No new homotopy was written by
hand: the convex contraction of the pinned library is used through the *exact* realization
model, as WP5 permits.

**WP2 (from image to subspace).**
* `subCover_surjective (A)` — for every subcomplex `A ≤ Δ[r]`, the finite family of realized
  `r`-simplices of `A` covers `|A|` (proved from the Task-16 normal form, the bound `k ≤ r`
  for a strictly monotone `⦋k⦌ ⟶ ⦋r⦌`, and the splitting of the collapse epimorphism);
* `compactSpace_realized_subcomplex (A) : CompactSpace ↥(SSet.toTop.obj A)` — **compactness of
  the realization of every subcomplex of a standard simplex, proved**;
* `isClosedEmbedding_subCoord (A)` / `isClosedEmbedding_realization_subcomplex (A)` — the
  realized inclusion is a **closed topological embedding** (compact source, Hausdorff target,
  continuous injection: `Continuous.isClosedEmbedding`);
* `isClosedEmbedding_bdCoord`, `isClosedEmbedding_realization_boundary`,
  `isOpen_compl_realized_boundary` — the boundary instances;
* **the boxed WP2 target**: `boundaryHomeo (r) : ↥(SSet.toTop.obj ∂Δ[r]) ≃ₜ bdLocus r` where
  `bdLocus r = {x : stdSimplex ℝ (Fin (r+1)) | ∃ i, x i = 0}`, with
  `coe_boundaryHomeo` recording that its underlying map is the Task-16 `bdCoord`.

**WP6 (boundary topology).**
* `boundaryZero_isEmpty` — `|∂Δ[0]|` is empty;
* `boundaryOneHomeo : ↥(SSet.toTop.obj ∂Δ[1]) ≃ₜ Fin 2` — `|∂Δ[1]|` is a discrete two-point
  space, i.e. `S⁰`; the two points are proved to be the two barycentric vertices
  (`twoPointEquiv`);
* `bdLocusSphereHomeo (r) : bdLocus r ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin r)) 1` and
  hence
  `boundaryRealizationSphereHomeo (r) : ↥(SSet.toTop.obj ∂Δ[r]) ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin r)) 1`
  — **`|∂Δ[r]| ≅ S^{r-1}`, by an explicit radial projection from the barycentre**, uniformly in
  `r` (for `r = 0` both sides are empty; for `r = 1` both sides have two points, consistently
  with `boundaryOneHomeo`).
  Ingredients: the gauge `simplexGauge r y = (r+1)·maxᵢ(-yᵢ)` with
  `mem_stdSimplex_bary_add`, `exists_zero_coord`, `simplexGauge_sub_bary`,
  `simplexGauge_smul`, `simplexGauge_pos`, `continuous_simplexGauge`; the hyperplane
  `hyper r = ker (∑ᵢ)` with `finrank_hyper : finrank ℝ (hyper r) = r` and the linear
  homeomorphism `hyperEquiv r : hyper r ≃L[ℝ] EuclideanSpace ℝ (Fin r)`.

The distinctions demanded by WP1 are respected throughout: `boundaryHomeo` and
`bdLocusSphereHomeo` are `Homeomorph`s, `isClosedEmbedding_*` are `IsClosedEmbedding`s, and
`SpineTask16.range_bdCoord` remains an equality of sets; none of these is silently promoted.

## 5. Complete theorem dependency DAG (new declarations)

```
SSet.toTopSimplex (Mathlib)                SpineTask16.coord
        │                                        │  (definitionally the same map)
        └──► simplexHomeo ◄──────────────────────┘
               ├──► coe_simplexHomeo, simplexHomeo_naturality, simplexHomeo_vertex
               ├──► compactSpace_realized_simplex   ─┐
               ├──► t2Space_realized_simplex        ─┤
               └──► contractibleSpace_realized_simplex
                     (convex_stdSimplex, Convex.contractibleSpace)

SpineTask16.subNormalForm ─┐
collapse, collapse_surjective, le_of_strictMono ─┤
SimplexCategory.isSplitEpi_of_epi ─┤
SpineTask16.subFaceMap_comp_ι ─────┴──► subCover_surjective ─┐
continuous_sigma, (SSet.toTop.map f).hom.continuous ─► continuous_subCover ─┤
compactSpace_realized_simplex, Finite (topIdx A) ───────────────────────────┴──►
        compactSpace_realized_subcomplex
                 │
                 ├─ + t2Space_realized_simplex + SpineTask16.subcomplexMono
                 │        (Continuous.isClosedEmbedding)
                 ├──► isClosedEmbedding_subCoord ──► isClosedEmbedding_bdCoord
                 └──► isClosedEmbedding_realization_subcomplex
                            └──► isClosedEmbedding_realization_boundary
                                        └──► isOpen_compl_realized_boundary

isClosedEmbedding_bdCoord + SpineTask16.range_bdCoord ──► boundaryHomeo ──► coe_boundaryHomeo
        ├──► (twoPointEquiv, bdLocusOneHomeo) ──► boundaryOneHomeo
        └──► boundaryRealizationSphereHomeo
                     ▲
simplexGauge_{smul,pos,sub_bary}, mem_stdSimplex_bary_add, exists_zero_coord,
continuous_simplexGauge, finrank_hyper ──► hyperEquiv ──► sphereMap / simplexPoint
     ──► simplexPoint_sphereMap, sphereMap_simplexPoint, continuous_sphereMap,
         continuous_simplexPoint ──► bdLocusSphereHomeo ────────────────────┘
```

## 6. WP4 — audit of the shortest standard-cell homology route

Inventory of the pinned environment (Lean 4.28.0, Mathlib `8f9d9cf`):

* `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` is the **only** singular-homology
  file.  It contains `SSet.singularChainComplexFunctor`, `singularChainComplexFunctor`,
  `singularHomologyFunctor`, and one computation (totally disconnected spaces).  There is
  **no** homotopy invariance, **no** long exact sequence of a pair, **no** relative singular
  homology, **no** homology of spheres, **no** degree theory.
* The string `excision` does not occur anywhere in Mathlib.
* `MayerVietoris` occurs only for sheaves / sheaf cohomology
  (`Mathlib/Topology/Sheaves/MayerVietoris.lean`,
  `Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean`); there is no
  Mayer–Vietoris sequence for singular homology.
* There is no barycentric subdivision and no small-simplices ("`Sing^U`") theorem.
* `Mathlib/AlgebraicTopology/RelativeCellComplex/` provides abstract cell attachment
  (transfinite composition of pushouts) but no homology of a cell attachment.
* Spheres exist only as metric objects (`Metric.sphere`,
  `Mathlib/Analysis/InnerProductSpace/…`, `OnePoint/Sphere.lean`); their homology is absent.
* Project-side, over `ℤ₂`: Task 14 supplies relative chain complexes and the LES; Task 8
  supplies a **cochain**-level prism operator and cohomological homotopy invariance
  (`Mod2Cohomology.prismK_identity`, `Hmap_eq_of_homotopy`,
  `cohomology_succ_eq_zero_of_contractible`); Task 10 supplies dualization.  There is **no**
  chain-level prism and hence no homology-level homotopy invariance in the project.

Route-by-route verdict:

| route | status in the pin | verdict |
|---|---|---|
| A `(Σ_r, ∂Σ_r) ≅ (D^r, S^{r-1})` | the pair identification is now available on the boundary side (`bdLocusSphereHomeo`); `Σ_r ≅ D^r` is not formalized, and no relative homology of `(D^r,S^{r-1})` exists in the pin | blocked at homology, not at topology |
| B quotient `Σ_r/∂Σ_r ≅ S^r` + relative-to-reduced | needs a good-pair theorem (excision) — absent | blocked |
| C contractibility + LES | contractibility **is** proved (`contractibleSpace_realized_simplex`), the project LES **is** available, but the LES step needs homology-level homotopy invariance (absent) and then `H̃_*(S^{r-1})` (absent) | blocked at two named theorems |
| D boundary ≅ `S^{r-1}` directly | **completed** in Task 17 (`bdLocusSphereHomeo`) | done, but only topology |
| E direct relative-chain argument | no acyclic-models/Eilenberg–Zilber input for the pair in the pin; the direct computation of `H_*(C_*(Σ_r), C_*(∂Σ_r))` still needs subdivision to see that small simplices suffice | blocked |

Coefficient compatibility: the project's chain complexes are `ℤ₂ = ZMod 2` throughout
(`SpineTask14.sSetChainComplexFunctor`), so any imported homology statement would have to be
instantiated at `ModuleCat (ZMod 2)`; Mathlib's `singularHomologyFunctor` is stated for a
general coefficient category and would be compatible, but it carries none of the theorems
needed.  None of the routes, as available, identifies the canonical top generator.

## 7. WP7–WP12 — status and the exact first missing theorem

* **WP7 (B1)** — *not proved*, in no degree and for no `r ≥ 1`.  Not weakened into a
  structure, not assumed, not stated as a hypothesis-carrying definition anywhere.
* **WP8 (canonical generator)** — *not attempted*; it presupposes WP7.
* **WP9 (single-cell relative `J`)** — *not proved*.
* **WP10/WP11 (attached-cell excision/additivity)** — *not proved*; per the WP10 instruction,
  no attempt was made to infer the direct-sum decomposition from the realized pushout square
  alone (which Task 15 does provide), because that inference is invalid without an
  excision/additivity theorem.
* **WP12 (B3)** — *not closed*.  `SpineTask14.RelJIsIso` remains exactly the hypothesis it was
  after Task 16.
* **WP13** — not consumed: the finite-dimensional comparison
  `SpineTask16.finiteDimensional_homologyIso` still carries `∀ r, RelJIsIso K r`.
* **WP14** — `NerveGeom.geometricHmap` remains open, and the Task-10 distinction
  (homology quasi-isomorphism ⇏ bijectivity of the existing cohomology comparison) is
  untouched.

**Exact first missing theorem.**  On the shortest route now open (route C/D: contractibility,
already proved, plus the LES, already available, plus `|∂Δ[r]| ≅ S^{r-1}`, now proved), the
first missing statement is

> **(M1) Homotopy invariance of the project's `ℤ₂` singular *chain* homology**: for homotopic
> `f, g : X → Y` the chain maps `C_*(Sing f), C_*(Sing g) : C_*^{sing}(X;ℤ₂) → C_*^{sing}(Y;ℤ₂)`
> are chain homotopic — i.e. the chain-level analogue of the existing cochain-level
> `Mod2Cohomology.prismK_identity`.

and, immediately after it, the genuine obstruction

> **(M2) Excision / Mayer–Vietoris for singular homology over `ℤ₂`**, in the weakest form
> sufficient to compute `H̃_*(S^{r-1};ℤ₂)` by induction (equivalently, the small-simplices
> theorem obtained from iterated barycentric subdivision).

(M1) is a bounded construction: the prism pieces already exist in
`RequestProject/Spine/Cohomology/PrismMaps.lean` and `Prism.lean` and would have to be
re-assembled on chains instead of cochains.  (M2) is not present in any form in the pinned
environment and is the real blocker; it is also exactly the theorem that WP11 would need in
its specialized attached-cell form, so B1 and B3 are blocked by the *same* missing input,
which is a further reason not to identify them.

## 8. WP15 — geometry audit (documentation only)

Theorem-level after Task 17 (no physical interpretation is attached to any of these):

| item | status | witness |
|---|---|---|
| barycentric coordinates | theorem-level, now as a **homeomorphism** | `simplexHomeo`, `coe_simplexHomeo` |
| `r+1` vertices | theorem-level | `realizedVertex`, `simplexHomeo_vertex` |
| `r+1` codimension-one faces | theorem-level (as the covering family and as the boundary decomposition) | `SpineTask16.realized_boundary_eq_iUnion_faces`, `subCover_surjective` |
| face loci `λᵢ = 0` | theorem-level | `SpineTask16.range_bdCoord`, `bdLocus` |
| interior locus `λᵢ > 0` | theorem-level, and now **open** | `SpineTask16.compl_range_bdCoord`, `isOpen_compl_realized_boundary` |
| unique nondegenerate-face provenance | theorem-level (Task 16) | `SpineTask16.subNormalForm` + the uniqueness argument inside `subcomplexMono` |
| boundary embedding | **new**, theorem-level | `isClosedEmbedding_realization_boundary` |
| topological simplex/boundary identification | **new**, theorem-level | `simplexHomeo`, `boundaryHomeo`, `boundaryRealizationSphereHomeo` |
| characteristic-cell generator | **not** theorem-level | — |

## 9. Required final audit (the 18 questions)

1. **New modules** — `Nerve/Task17StandardCellTopology.lean`, `Nerve/Task17BoundarySphere.lean`,
   `Nerve/Task17AxiomAudit.lean`.
2. **Reused Task-14/15/16 modules** — listed in §2; all frozen, none modified.
3. **Dependency DAG** — §5.
4. **Build status** — `lake build RequestProject` completes successfully (8222 jobs), including
   the pre-existing `Spine/Audit/Firewall.lean` proof-closure audit ("all checks passed").
5. **Axiom/sorry audit** — `Nerve/Task17AxiomAudit.lean` prints, for all 22 principal Task-17
   declarations, exactly `[propext, Classical.choice, Quot.sound]`.  No `sorry`, no `admit`,
   no `axiom`, no `native_decide` in the Task-17 layer.
6. **Failbuilds and repairs** — `TASK17_FAILBUILDS.md`.
7. **Is the Task-16 boundary bijection now a homeomorphism onto the barycentric boundary?** —
   **Yes**: `boundaryHomeo`, with `coe_boundaryHomeo` proving it is the Task-16 map, and
   `isClosedEmbedding_realization_boundary` giving the closed-embedding form.
8. **Is `|Δ[r]|` formally identified with the geometric standard simplex?** — **Yes**:
   `simplexHomeo`, a homeomorphism, definitionally equal to the Task-16 coordinate bijection.
9. **Is `|∂Δ[r]|` formally identified with the appropriate sphere/boundary model?** — **Yes**:
   `boundaryHomeo` (boundary locus) and `boundaryRealizationSphereHomeo` (standard sphere
   `S^{r-1}`), with the low-dimensional cases `r = 0` (empty) and `r = 1` (`S⁰`) explicit.
10. **Is B1 proved in every degree and every `r`?** — **No.**  It is not proved in any degree
    for any `r ≥ 1`; `r = 0` was not separately computed either.
11. **Is the characteristic top simplex proved nonzero?** — **No.**
12. **Is it proved to generate the top relative homology?** — **No.**
13. **Is the single-cell relative `J` an isomorphism?** — **Not proved.**
14. **Is the attached-cell excision/additivity theorem proved?** — **No.**
15. **Is B3 closed?** — **No**; `SpineTask14.RelJIsIso` is still an open hypothesis.
16. **Is finite-dimensional `J` now a quasi-isomorphism?** — **No**; it remains conditional on
    `∀ r, RelJIsIso K r` (`SpineTask16.finiteDimensional_homologyIso`).
17. **Does `geometricHmap` remain open?** — **Yes**, and the Task-10 distinction is preserved.
18. **Exact first remaining blocker** — (M1) chain-level homotopy invariance of the project's
    `ℤ₂` singular chain complex, and behind it the true obstruction (M2) excision /
    Mayer–Vietoris / small simplices for singular homology, absent from the pinned Mathlib in
    every form (§6, §7).
