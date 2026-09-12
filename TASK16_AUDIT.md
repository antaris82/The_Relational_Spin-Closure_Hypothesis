# Task 16 — Point model for geometric realization and the standard-cell monomorphism

**Environment (frozen, unchanged):** Lean `v4.28.0`, Mathlib pinned at
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.  `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json` are byte-identical to their Task-15 state.

**Outcome classification: `B` — full point normal form + standard-cell theorem**, strengthened
on one axis: the normal form and the injectivity theorem are proved not only for `∂Δ[r]` but
for *every subcomplex of a standard simplex*.  The fully general
"realization of any simplicial monomorphism is injective" (outcome `A`) was **not** proved; see
§9.

Boxed target of the task:

> `|∂Δ[r]| ⟶ |Δ[r]|` is injective for every `r` — **PROVED** (`SpineTask16.standardCellMono`).

Consequently:

> `|K^{(r)}| ↪ |K^{(r+1)}|` for every simplicial set `K` and every `r` — **PROVED**
> (`SpineTask16.realization_skInc_injective`), by theorem-level reuse of the Task-15 reduction.

No `sorry`, no `admit`, no project-local `axiom`, no `native_decide`.  Every principal Task-16
declaration reports exactly `[propext, Classical.choice, Quot.sound]`
(`RequestProject/Spine/Nerve/Task16AxiomAudit.lean`).  Full `lake build` green (8220 jobs), and
the Spine firewall audit still reports `all checks passed`.

---

## 1. Modules inspected (WP1 — source-level audit of the realization implementation)

Pinned Mathlib sources read in full:

| module | what was extracted |
|---|---|
| `Mathlib/AlgebraicTopology/SingularSet.lean` | `SSet.toTop := stdSimplex.leftKanExtension SimplexCategory.toTop`; `sSetTopAdj`; `SSet.toTopSimplex : stdSimplex ⋙ toTop ≅ SimplexCategory.toTop`; `SSet.toTop.IsLeftKanExtension`. The Kan extension is **never evaluated** in the pin. |
| `Mathlib/AlgebraicTopology/TopologicalSimplex.lean` | `SimplexCategory.toTop₀.obj n = TopCat.of (stdSimplex ℝ (Fin (n.len+1)))`, `toTop = toTop₀ ⋙ TopCat.uliftFunctor`, `toTop.map f = stdSimplex.map f.toOrderHom` (up to `ULift`). |
| `Mathlib/Analysis/Convex/StdSimplex.lean` | `stdSimplex ℝ X = {f // (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}`; `stdSimplex.map`, `map_comp_apply`, `vertex`, `map_vertex`, `sum_eq_one`, `zero_le`. |
| `Mathlib/LinearAlgebra/Finsupp/Pi.lean` | `FunOnFinite.linearMap_apply_apply` : the coordinate formula `(map g u) y = ∑_{x : g x = y} u x`. |
| `Mathlib/CategoryTheory/Limits/Presheaf.lean` | `Presheaf.tautologicalCocone'` / `isColimitTautologicalCocone'` — every presheaf is the colimit of representables over `CostructuredArrow uliftYoneda P`. |
| `Mathlib/CategoryTheory/Limits/Types/Colimits.lean` | `Types.jointly_surjective_of_isColimit`. |
| `Mathlib/AlgebraicTopology/SimplicialSet/StdSimplex.lean` | `stdSimplex = uliftYoneda`; `objEquiv`, `yonedaEquiv`, `yonedaEquiv_map`, `yonedaEquiv_comp`, `Subcomplex.yonedaEquiv_coe`, `stdSimplex.map_apply`. |
| `Mathlib/AlgebraicTopology/SimplicialSet/Boundary.lean` | `∂Δ[n].obj m = {s | ¬ Surjective (asOrderHom s)}`; `boundary_eq_iSup`. |
| `Mathlib/CategoryTheory/Subfunctor/Basic.lean` | `Subfunctor.obj` / `Subfunctor.map` (closure of a subcomplex under simplicial operators). |
| `Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean` | `epi_iff_surjective`; `SplitEpiCategory SimplexCategory` (every epi of `SimplexCategory` splits). |
| `Mathlib/Data/Finset/Sort.lean` | `orderIsoOfFin`, `orderEmbOfFin`, `orderEmbOfFin_mem`, `image_orderEmbOfFin_univ`, `orderEmbOfFin_unique`. |

**Exact dependency map of the realization used.**

```
SSet.toTop  =  stdSimplex.leftKanExtension SimplexCategory.toTop      (a left adjoint)
   │
   ├── evaluated on representables by  SSet.toTopSimplex               (an iso in TopCat)
   │        |Δ[n]|  ≅  ULift (stdSimplex ℝ (Fin (n.len+1)))
   │
   └── evaluated on a general presheaf: NOT by the pin.  Instead, in this task:
           A  ≅  colim_{CostructuredArrow uliftYoneda A} Δ[n]          (Presheaf, pin)
           |A| ≅  colim_{same}  |Δ[n]|                                  (left adjoint)
           colimits of types are jointly surjective                     (Types, pin)
```

There is **no** quotient/coend presentation of `|A|` in the pin, and none was added: the point
model is obtained from the *colimit* presentation, whose surjectivity half is all that the
argument needs (see §3).

## 2. Newly introduced modules

| module | contents |
|---|---|
| `RequestProject/Spine/Nerve/Task16PointModel.lean` (390 lines) | barycentric support calculus; Level A; `coord`; the normal form; `subcomplexMono`; `standardCellMono` |
| `RequestProject/Spine/Nerve/Task16Consequences.lean` | the realized-boundary characterization; WP8; the two Task-15 instantiations; the `r = 0, 1` smoke tests |
| `RequestProject/Spine/Nerve/Task16AxiomAudit.lean` | `#print axioms` for every principal declaration |

No existing module was modified.  `SSet.toTop`, `∂Δ[r]`, the boundary inclusion,
`SpineTask15.StandardCellMono`, `SpineTask15.realization_skInc_injective` and the realized
skeletal pushout are all reused verbatim; the canonical comparison `J = C_*(η_K)` is untouched.

## 3. Exact theorem names

**Coordinate calculus** (about `stdSimplex ℝ X`, no simplicial input)

* `SpineTask16.supp`, `mem_supp`, `eq_zero_of_notMem_supp`, `supp_nonempty`
* `SpineTask16.map_apply` — `(stdSimplex.map g u) y = ∑_{x : g x = y} u x`
* `SpineTask16.supp_map` — `supp (map g u) = (supp u).image g`
* `SpineTask16.restrict`, `restrict_apply`, `map_restrict` — restriction along an injective
  reindexing whose image contains the support is a section of `stdSimplex.map`

**Level A**

* `SpineTask16.exists_representative` : `∀ A (x : |A|), ∃ n (f : Δ[n] ⟶ A) t, |f| t = x`.

**WP4, barycentric coordinates on `|Δ[n]|`**

* `SpineTask16.coord (n) : |Δ[n]| ≃ stdSimplex ℝ (Fin (n.len+1))` — *defined from
  `SSet.toTopSimplex`*, i.e. from the pin's own identification, not a new model
* `SpineTask16.coord_naturality` : `coord m (|Δ(a)| t) = stdSimplex.map a.toOrderHom (coord n t)`

**Faces and subcomplexes**

* `SpineTask16.faceSimplex`, `subFaceMap`, `subFaceMap_comp_ι`, `subCoord`,
  `subCoord_subFaceMap`
* boundary specialisations: `faceMap`, `faceMap_comp_ι`, `bdCoord`, `bdCoord_faceMap`

**WP2/WP3, the normal form**

* `SpineTask16.subNormalForm (A : (Δ[r]).Subcomplex) (x : |A|)` :
  `∃ k (e : ⦋k⦌ ⟶ ⦋r⦌) (hmem : faceSimplex e ∈ A) v, StrictMono e ∧ (∀ j, 0 < v j) ∧
  |subFaceMap A e hmem| (coord⁻¹ v) = x`
* `SpineTask16.normalForm` — the case `A = ∂Δ[r]`, with `hmem` read as non-surjectivity

**WP6/WP7**

* `SpineTask16.subcomplexMono (A : (Δ[r]).Subcomplex) : Function.Injective |A.ι|`
* **`SpineTask16.standardCellMono (r) : SpineTask15.StandardCellMono r`**

**WP5/WP10**

* `SpineTask16.range_bdCoord` : `range (bdCoord r) = {u | ∃ i, u i = 0}`
* `SpineTask16.realized_boundary_eq_iUnion_faces` : `= ⋃ i, {u | u i = 0}`
* `SpineTask16.compl_range_bdCoord` : the complement is `{u | ∀ i, 0 < u i}`
* `SpineTask16.range_realization_boundary` — the same as a statement about
  `range |∂Δ[r].ι| ⊆ |Δ[r]|`

**WP8**

* `SpineTask16.realization_skInc_injective`, `realizationInjective`, `oneSkeletonStep`,
  `skeletalInduction`, `finiteDimensional_homologyIso`

**WP11**

* `SpineTask16.boundaryZero_realization_isEmpty`, `SpineTask16.boundaryOne_eq_vertex`

## 4. The proof, in one page

Write `Rz = SSet.toTop ⋙ forget TopCat` (the Task-15 functor `Real`).

1. **Level A.**  `A` is the colimit of representables over `CostructuredArrow uliftYoneda A`
   (`Presheaf.isColimitTautologicalCocone'`); `Rz` is a composite of two left adjoints, hence
   preserves this colimit; colimit cocones of types are jointly surjective.  So every
   `x : Rz.obj A` is `Rz.map f t` for some `f : Δ[n] ⟶ A`, `t : Rz.obj Δ[n]`.
2. **Coordinates.**  `coord n` transports `Rz.obj Δ[n]` to `stdSimplex ℝ (Fin (n.len+1))` using
   `SSet.toTopSimplex`; naturality is the naturality of `toTopSimplex`.
3. **Normal form** (for `A ≤ Δ[r]`).  Given `x = Rz.map f t`, let `α : n ⟶ ⦋r⦌` be the simplex
   of `Δ[r]` underlying `f` (`f ≫ A.ι = stdSimplex.map α`, `α`'s simplex lies in `A`), and
   `w = coord n t`.
   * *Kill the zero coordinates.*  Let `j : ⦋m⦌ ⟶ n` be the increasing enumeration of
     `supp w`; then `stdSimplex.map j (w|supp) = w`, hence `x = Rz.map (Δ(j) ≫ f) (coord⁻¹ w')`
     with `w'` interior.
   * *Kill the degeneracies.*  Let `γ = j ≫ α`, `S = im γ`, `e : ⦋k⦌ ⟶ ⦋r⦌` the increasing
     enumeration of `S`, and `p : ⦋m⦌ ⟶ ⦋k⦌` the induced surjection, so `γ = p ≫ e`.
     `e`'s simplex lies in `A` because `p` is an epimorphism of `SimplexCategory`, every such
     epimorphism splits (`SplitEpiCategory`), and a subcomplex is closed under the simplicial
     operators: `e = section_ p ≫ γ`.
   * Since `A.ι` is a monomorphism, `Δ(j) ≫ f = Δ(p) ≫ subFaceMap A e`, so
     `x = Rz.map (subFaceMap A e) (coord⁻¹ (stdSimplex.map p w'))`, and
     `stdSimplex.map p w'` is interior because `p` is surjective.
4. **Injectivity.**  If two normal forms `(k,e,v)`, `(k',e',v')` have the same image in
   `|Δ[r]|` then `stdSimplex.map e v = stdSimplex.map e' v'`.  Taking supports and using
   interiority, `im e = im e'`; comparing cardinalities gives `k = k'`, and
   `Finset.orderEmbOfFin_unique` gives `e = e'`; evaluating at `e j` gives `v = v'`.  Hence the
   two points of `|A|` are equal.

Note the asymmetry that made this work with the pin's API: only the **surjectivity** half of
the colimit presentation is used (Level A).  The relations of the colimit are never needed,
because every identification used in step 3 is an instance of *functoriality* of `Rz`, and the
uniqueness in step 4 is proved *downstream*, in `|Δ[r]|`, where coordinates are available.

## 5–10. Answers to the required report items

5. **Does every realization point have a representative?**  Yes — `exists_representative`, for
   every simplicial set (Level A, unrestricted).
6. **Nondegenerate representative?**  Yes for subcomplexes of a standard simplex
   (`subNormalForm`): the representing simplex is a strictly monotone `e : ⦋k⦌ ⟶ ⦋r⦌`, i.e. a
   nondegenerate simplex of `Δ[r]` lying in `A`.  For a *general* simplicial set, Level B is
   **not** proved (it would need the Eilenberg–Zilber lemma; see §9).
7. **Uniqueness / interior normal form?**  Proved in the following exact sense: for
   `A ≤ Δ[r]`, the pair `(e, v)` with `e` strictly monotone and `v` interior is *uniquely
   determined by the image point in `|Δ[r]|`* — this is precisely the content of the proof of
   `subcomplexMono` (steps 4 above).  It is not packaged as a separate `∃!` statement; the
   uniqueness is consumed directly by the injectivity theorem.
8. **Barycentric coordinates available?**  Yes: `coord`, `coord_naturality`, and the whole
   `supp`/`restrict`/`map_apply` calculus.  Vertices are `stdSimplex.vertex`, faces are the
   images of `subFaceMap`, the support of a point is `supp`, and the relative interior is
   `{u | ∀ i, 0 < u i}` (`compl_range_bdCoord`).
9. **Is the realized boundary characterized?**  Yes — `range_bdCoord` /
   `range_realization_boundary` / `realized_boundary_eq_iUnion_faces`: the image is exactly the
   union of the `r+1` coordinate faces, i.e. `{x | ∃ i, λ_i(x) = 0}`.  This is derived from the
   actual simplicial definition of `∂Δ[r]` (non-surjectivity) and the actual realization, not
   assumed from the geometry.
10. **Is `StandardCellMono r` proved for all `r`?**  Yes, `SpineTask16.standardCellMono`.
11. **Is skeletal realization injectivity closed?**  Yes, unconditionally, by *reuse* of the
    Task-15 reduction: `SpineTask16.realization_skInc_injective`,
    `SpineTask16.realizationInjective`.  In addition `SpineTask16.oneSkeletonStep`,
    `skeletalInduction` and `finiteDimensional_homologyIso` now carry only the relative
    comparison hypothesis `SpineTask14.RelJIsIso`.
12. **Stronger embedding theorems?**  Injectivity is proved for the inclusion of *any*
    subcomplex of a standard simplex (`subcomplexMono`), which is strictly stronger than the
    required boundary case.  **Topological embedding / closed embedding were not proved**: they
    require the topology of `|A|`, i.e. the colimit topology, which the point model does not by
    itself supply.  Nothing here claims them.

## 9. WP7 — why the fully general monomorphism theorem was not proved

The normal-form argument used two facts special to a subcomplex `A ≤ Δ[r]`:

* every map `Δ[n] ⟶ Δ[r]` is `stdSimplex.map α` for a unique `α` (Yoneda), so a representative
  is described by a *morphism of `SimplexCategory`*, and its epi–mono factorization is the
  ordinary image factorization of a monotone map;
* the target `|Δ[r]|` has coordinates, which is what makes the *uniqueness* step (step 4)
  possible.

For a general monomorphism `f : K ⟶ L` neither is available.  Level B for a general `K` needs
the Eilenberg–Zilber lemma (unique factorization of a simplex as a degeneracy of a
nondegenerate simplex), and the uniqueness step needs a normal-form theorem *for `|L|`*, i.e.
an actual quotient presentation of the realization with a decidable equality criterion.  That
is substantial extra machinery, and per the task's scope rule it was not attempted.  The task's
required target (the standard cell) is proved, and the intermediate generalization to
subcomplexes of `Δ[r]` came for free from the same proof.

## 10. WP10 — the boundary as a union of faces

* *Simplicial level*: `SSet.boundary_eq_iSup : ∂Δ[n] = ⨆ i, stdSimplex.face {i}ᶜ` is already in
  the pin; nothing new is needed, and it is used only as an inventory item.
* *Realization level*: proved in coordinates, `realized_boundary_eq_iUnion_faces`.  Note that
  what is proved is the statement about **images**: the image of `|∂Δ[r]|` is the union of the
  images of the `r+1` faces.  Realization does not a priori commute with intersections, and no
  such claim is made.

## 11. WP11 — dimension-sensitive base cases

* `r = 0` : `boundaryZero_realization_isEmpty` — `|∂Δ[0]| = ∅` (reusing
  `SpineTask15.boundaryZero_isInitial`).
* `r = 1` : `boundaryOne_eq_vertex` — every point of `|∂Δ[1]|` is one of the two vertices
  `stdSimplex.vertex i` of `|Δ[1]|`; combined with `standardCellMono 1` and `range_bdCoord`
  this pins `|∂Δ[1]|` down to the two endpoints.
* `r = 2` : not formalized separately; it is the instance `r = 2` of
  `realized_boundary_eq_iUnion_faces` (the union of the three realized edges).  A separate
  formalization would have exposed no new API.

## 12. WP12 — compatibility with characteristic simplices

No alternative realization model was introduced.  `coord` is *defined* as the underlying
bijection of `SSet.toTopSimplex.app n`, the pin's own comparison, and `coord_naturality` is its
naturality square.  Consequently, for any simplicial set `K` and any `σ : Δ[r] ⟶ K`, the
characteristic map `|σ| : |Δ[r]| → |K|` is literally `Rz.map σ` precomposed with `coord⁻¹`; no
translation layer stands between the point model and the frozen `J = C_*(η_K)`.  In particular
`subFaceMap_comp_ι` and `faceMap_comp_ι` state exactly the compatibility of the faces of the
point model with the characteristic maps of `Δ[r]`.

## 13. Failed proof routes (provenance, diagnosis, repair)

Recorded in full in `TASK16_FAILBUILDS.md`.

## 14. Final build status

`lake build` : **green**, 8220 jobs, no warnings other than the `#print axioms` info lines and
the Spine firewall audit (`all checks passed`).  `rg 'sorry|admit'` over the Task-16 modules:
no hits outside documentation prose.

## 15. Axiom audit

`RequestProject/Spine/Nerve/Task16AxiomAudit.lean` prints, for each of the 26 principal
declarations, exactly `[propext, Classical.choice, Quot.sound]`.

## 16. Required theorem dependency DAG, and the exact next blocker

```
realization implementation (SSet.toTop = Lan, toTopSimplex)     PROVED (pin, audited)
        ↓
point representative theorem (exists_representative, coord)     PROVED
        ↓
normal form (subNormalForm / normalForm)                        PROVED
        ↓
boundary characterization (range_bdCoord, …_iUnion_faces)       PROVED
        ↓
|∂Δ[r]| ↪ |Δ[r]|            (standardCellMono)                  PROVED
        ↓
|K^{(r)}| ↪ |K^{(r+1)}|     (realization_skInc_injective)       PROVED
```

Every arrow of the required DAG is proved; there is no unproved arrow left in it.

**Next blocker (outside Task 16's scope, unchanged in nature but now isolated):**

```
H_q^{sing}(|Δ[r]|, |∂Δ[r]|; ℤ₂)  =  0 for q ≠ r,  ≅ ℤ₂ for q = r,
    together with the identification of the canonical top generator
    represented by the identity characteristic simplex.
```

In project terms this is `SpineTask14.RelJIsIso`, the only hypothesis still carried by
`SpineTask16.finiteDimensional_homologyIso`.  What Task 16 changes for it: the pair
`(|Δ[r]|, |∂Δ[r]|)` is no longer opaque.  Its points are now described in barycentric
coordinates, `|Δ[r]|` is the topological simplex, and the subspace `|∂Δ[r]|` maps bijectively
onto `{λ | ∃ i, λ_i = 0}`.  The precise first missing Lean-level statements for Task 17 are:

1. `SpineTask16.range_realization_boundary` upgraded from a bijection onto its image to a
   *homeomorphism* onto `{λ | ∃ i, λ_i = 0}` (i.e. the colimit topology on `|∂Δ[r]|` agrees
   with the subspace topology) — the pin has no theorem about the topology of a realization;
2. `H_*(D^r, S^{r-1})` (equivalently the reduced homology of spheres) — absent from the pin;
3. singular excision / the small-simplices theorem — absent from the pin.
