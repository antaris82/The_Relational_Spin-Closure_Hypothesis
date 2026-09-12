# TASK18 FAILBUILDS

Every failed elaboration / proof attempt encountered while building the Task-18 layer, with
provenance, diagnosis, repair, and whether the repair changed the mathematical statement.

Legend for the last column: **no** = the statement finally proved is the statement originally
attempted (only the proof script changed); **yes** = the statement itself was altered.

---

## A. Foundations (`Task18Affine.lean`)

| # | module | failing statement / error | diagnosis | repair | statement changed? |
|---|---|---|---|---|---|
| A1 | `Task18Affine` | `combo_stdC` attempted by direct coordinate computation; goal left an unmanageable double sum over `Finset.filter` | `stdSimplex.map` expands to a filtered sum, which does not match the `combo` normal form | derived `combo_stdC` from `combo_comp` + `combo_vertex` instead | no |
| A2 | `Task18Affine` | `rw [sSetBoundary_single]` — unknown identifier | the lemma lives in the `SpineTask13`/`NerveGeom` namespace, not the local one | qualified as `SpineTask13.`/`NerveGeom.` | no |
| A3 | `Task18Affine` | `simp`/`rfl` failures on `(codisc V).obj n` not reducing to `Fin (k+1) → V` | `codisc` is a structure instance; `obj` did not unfold under `simp` in universe-polymorphic positions | defined `LChain V k` directly as the `Finsupp` and proved `lbd_eq_sSetBoundary` by `rfl`, keeping `codisc` only as the source of `∂∘∂=0` | no |

## B. Linear subdivision (`Task18LinearSubdivision.lean`)

| # | module | failing statement / error | diagnosis | repair | statement changed? |
|---|---|---|---|---|---|
| B1 | `Task18LinearSubdivision` | `refine lchain_induction c ?_ ?_ ?_` — "failed to elaborate eliminator, motive is not type correct" | higher-order unification cannot guess the motive from a bare `refine` | added `@[elab_as_elim]` and used `induction c using lchain_induction with \| h0 \| hadd \| hsingle` | no |
| B2 | `Task18LinearSubdivision` | `Subsingleton (Fin (0+1))` instance not found in `lbd_lcone_zero` | no such instance is registered for the literal `Fin (0+1)` | replaced by an explicit `Fin.ext (by omega)` argument | no |
| B3 | `Task18LinearSubdivision` | `rw [← h]` in the `sdT` homotopy: "motive is not type correct" | rewriting backwards under a dependent boundary index | proved the rearranged equation forward as an auxiliary `h2` and closed with `rwa` | no |

## C. Mesh estimate (`Task18Mesh.lean`)

| # | module | failing statement / error | diagnosis | repair | statement changed? |
|---|---|---|---|---|---|
| C1 | `Task18Mesh` | `rw [div_le_div_iff]` — unknown constant | the name does not exist in the pinned Mathlib revision | replaced by `sub_nonneg` + `field_simp` + `positivity` | no |
| C2 | `Task18Mesh` | `Unique`/`Inhabited (Δs 0)` instance failures | `stdSimplex ℝ (Fin 1)` carries no such instance in the pin | proved an explicit `hsub : ∀ x y : Δs 0, x = y` via `Fin.sum_univ_one` | no |
| C3 | `Task18Mesh` | coercion mismatches between `Subtype.val` and the metric-space coercion on `stdSimplex` (`Metric.dist_le_diam_of_mem` did not apply) | two different coercions print identically | inserted explicit `show (x : Fin (n+1) → ℝ) …` normalisations | no |

## D. Small simplices (`Task18SmallSimplices.lean`)

| # | module | failing statement / error | diagnosis | repair | statement changed? |
|---|---|---|---|---|---|
| D1 | `Task18SmallSimplices` | `rw [Finsupp.support_mapDomain]` — unknown constant | the pinned name is `Finsupp.mapDomain_support` | renamed | no |
| D2 | `Task18SmallSimplices` | `HomologicalComplex.exactAt` — unknown constant | the pin spells it `ExactAt` | renamed | no |

## E. Excision, WP8 (`Task18Excision.lean`)

| # | module | failing statement / error | diagnosis | repair | statement changed? |
|---|---|---|---|---|---|
| E1 | `Task18Excision` | `isZero_relSmall_zero`: `failed to synthesize Subsingleton ↑((relChainCx (smallInc U V)).X 0)` | the `Subsingleton` instance was stated for `RelChainMod …`, which is only *definitionally* `(relChainCx …).X 0` | inserted `rw [show (relChainCx …).X 0 = ModuleCat.of (ZMod 2) (RelChainMod …) from rfl]` before applying `ModuleCat.isZero_of_subsingleton` | no |
| E2 | `Task18Excision` | `relSmall_exactAt`, range ⊆ ker branch: `simpa using this` reduced the hypothesis to `True` | `simp` normalised the hypothesis but not the goal | replaced by the explicit term `congrFun (congrArg DFunLike.coe (congrArg ModuleCat.Hom.hom hdd)) y` | no |
| E3 | `Task18Excision` | `relSmall_exactAt`, ker ⊆ range branch: `rw [← hc]` rewrote every occurrence of `c`, including the one inside `homN X (m+1) N c`, leaving an unprovable goal | unrestricted rewriting of a variable that also occurs on the right | `symm` + `conv_lhs => rw [← hc]` to target only the intended occurrence | no |
| E4 | `Task18Excision` | `rw [HomologicalComplex.quasiIsoAt_iff_isIso_homologyMap]` — unknown constant | the lemma is in the root namespace: `quasiIsoAt_iff_isIso_homologyMap` | renamed | no |

## F. Excision, WP9 (`Task18Excision.lean`)

| # | module | failing statement / error | diagnosis | repair | statement changed? |
|---|---|---|---|---|---|
| F1 | `Task18Excision` | `carrierAt_toSSet_map := Set.range_comp _ _` — type mismatch | `carrierAt` is a `Set.range` of a `ContinuousMap` coercion; the composite had to be exhibited | prefixed by `show Set.range (⇑(ConcreteCategory.hom g) ∘ ⇑(TopCat.toSSetObjEquiv X n σ)) = _` | no |
| F2 | `Task18Excision` | `range_toSSet_subInc`: `congrArg sOf …` produced `sOf ?a = sOf ?b` but the goal's right-hand side was `σ` | `σ` is not syntactically of the form `sOf _` | `Eq.trans (congrArg sOf …) (sOf_sMap σ)` | no |
| F3 | `Task18Excision` | `incInterU_injective := fun _ _ h => Subtype.ext (congrArg Subtype.val h)` — application type mismatch | `Subtype.val` was elaborated at the wrong subtype | `congrArg (fun z : U => (z : X)) h` | no |
| F4 | `Task18Excision` | `excisionMap_factor` closed by `rfl` — not definitionally equal | `mapDomain` of a composite is *not* definitionally the composite of `mapDomain`s | inserted `show … ` and `rw [← Finsupp.mapDomain_comp]` | no |
| F5 | `Task18Excision` | `excPsi_injective`: `carrier ((toSmallU U V).app _ σ : … )` — type mismatch `smallSSet U V _⦋q⦌` vs `Sing X q` | the small simplex is a subtype, the underlying simplex is its `.1` | used `((toSmallU U V).app _ σ).1` | no |
| F6 | `Task18Excision` | `excPsi_surjective`: `rw [excPsi_f_mk]` — pattern not found, although the goal printed identically | the goal used `Submodule.mkQ` while the lemma is phrased with `Submodule.Quotient.mk` | replaced the `rw` by an explicit `show` of the quotient equation | no |
| F7 | `Task18Excision` | `excAlpha_injective`: `have hx' : Submodule.Quotient.mk … = 0 := hx` — "typeclass instance problem is stuck: `Module ?m …`" | the submodule `p` of the quotient could not be inferred from the statement | supplied `(p := LinearMap.range (sSetChainMap … ))` explicitly | no |
| F8 | `Task18Excision` | `excSC_zero` / `excSC_shortExact`: `show Submodule.Quotient.mk (sSetChainMap (smallInc U V) q c) = 0` — not definitionally equal to the target | `excBeta` is `relChainCxMap … (𝟙 _)`, so the composite carries an extra `mapDomain id`, which is not definitionally the identity | added the lemma `sSetChainMap_id` and wrote the `show` with the explicit `sSetChainMap (𝟙 _) q` factor, then `rw [sSetChainMap_id]` | no |
| F9 | `Task18Excision` | `excSC_shortExact`, ker branch: `have hx' … := hx` — type mismatch (membership in `ker` vs the equation) | `LinearMap.mem_ker` was not unfolded, and the `g` map again contained `mapDomain id` | introduced `hbeta` computing `g (mk c)` and used `rw [LinearMap.mem_ker, hbeta] at hx` | no |

## G. Chain prism, WP2 (`Task18ChainPrism.lean`)

| # | module | failing statement / error | diagnosis | repair | statement changed? |
|---|---|---|---|---|---|
| G1 | `Task18ChainPrism` | `stdC_comp`: unsolved goal `stdSimplex.vertex (g (f i)) = stdSimplex.vertex ((g ∘ f) i)` | `rw` closed the main rewrite but left a `rfl`-goal | appended `rfl` | no |
| G2 | `Task18ChainPrism` | `combo_const`: `rw [x.2.2]` — pattern `∑ x_1, ↑x x_1` not found | the sum in the goal and the sum in `x.2.2` use different printings of the same coercion | used `rw [show ∑ i, (x : Fin (m+1) → ℝ) i = 1 from x.2.2]` | no |
| G3 | `Task18ChainPrism` | `pcombo_prismPtMap`: "no goals to be solved" after `rw [← combo_vertex f, combo_comp]` | the rewrite already closed the goal by `rfl` | deleted the trailing tactic block | no |
| G4 | `Task18ChainPrism` | `realizeP_botP` / `realizeP_topP`: `congrArg (fun s => Finsupp.single s 1) (ContinuousMap.ext …)` — application type mismatch | the goal is an equation of `sOf`s, so an intermediate `congrArg sOf` is needed | `congrArg (fun s => Finsupp.single s 1) (congrArg sOf (ContinuousMap.ext …))` | no |
| G5 | `Task18ChainPrism` | `prismHom`: `eqToHom (by rw [h])` left the goal `ModuleCat.of … = (singCx Y).X (i+1)` | the `ofHom` was elaborated at `ModuleCat.of …`, not at `(singCx Y).X (i+1)` | ascribed the type of the `ofHom` and used `eqToHom (congrArg (singCx Y).X h.symm)` | no |
| G6 | `Task18ChainPrism` | `prismHomotopy.comm`: `show … = ((singCx Y).d 1 0).hom (prismOp H 0 c) + sSetChainMap … c` — "failed to synthesize `HAdd ↑((singCx Y).X 0) (SSetChain …)`" | mixing the `ModuleCat` carrier type and the `Finsupp` type in one expression | rewrote the differentials first (`simp only [SpineTask14.sSetChainComplexFunctor_d, …]`), then a `show` with all summands in the `SSetChain` form | no |
| G7 | `Task18ChainPrism` | `prismHomotopy.comm`: `rw [hid]` — pattern not found although `hid` printed exactly like the subterm | the additive structure in the goal came from the `ModuleCat` instance, the one in `hid` from the `Finsupp` instance | inserted a `show` converting the whole goal to the `Finsupp` form before rewriting | no |

## H. Contractibility, WP3 (`Task18Contractible.lean`)

| # | module | failing statement / error | diagnosis | repair | statement changed? |
|---|---|---|---|---|---|
| H1 | `Task18Contractible` | `toI_mem`: `linarith failed` with `hsum : ↑s 0 + ↑s 1 = 1` and goal `1 < s 1 → False` | the two coercions of `s` were not syntactically identified | restated the hypotheses with explicit `(s : Fin 2 → ℝ)` ascriptions and used `Set.mem_Icc.2` | no |
| H2 | `Task18Contractible` | `singMap_id_apply`: `rw [TopCat.toSSet.map_id X]` — pattern not found | `singMap` is an `abbrev`, so the functor application is hidden | prefixed with `show sSetChainMap (TopCat.toSSet.map (𝟙 X)) q c = c` | no |
| H3 | `Task18Contractible` | `singBd_constSimp`: `rw [show (2 : ZMod 2) = 0 …]` after `push_cast` — pattern `2` not found (goal `↑q + 1 + 1 = ↑q`) | `push_cast` had already split `2` into `1 + 1` | `rw [add_assoc, show (1 + 1 : ZMod 2) = 0 from by decide, add_zero]` | no |
| H4 | `Task18Contractible` | parity computation `↑k + ↑k + 1 = 1` (even case) and `2 * ↑k + 1 = 1` (odd case) failed with the same `rw` | `push_cast` produces different shapes for `Even`/`Odd` witnesses | even case: `mod2_add_self`; odd case: `show (2 : ZMod 2) = 0`, `zero_mul`, `zero_add` | no |
| H5 | `Task18Contractible` | `rw [hz] at this` in the odd case — pattern `(singBd X m) z` not found | the `map_add` normalisation had to precede the rewrite | reordered the rewrite chain (`sSetBoundary_comp_sSetBoundary`, `map_add`, `hz`, `zero_add`) | no |
| H6 | `Task18Contractible` | `exactAt_singCx_of_contractible`: `rw [SpineTask14.sSetChainComplexFunctor_d]` — pattern not found | the goal is phrased with `HomologicalComplex.sc'` fields, not with `d` | inserted `rw [show (HomologicalComplex.sc' …).g = (singCx X).d (m+1) m from rfl, …]` (and likewise for `.f`) | no |

---

## Design attempts abandoned before implementation

These are recorded for completeness; they never reached a failing elaboration, but they are
routes that were considered and rejected on cost grounds.

1. **Hatcher's minimal-`m(σ)` construction** for the Small-Simplices theorem (choosing, for
   each simplex, the least subdivision depth making it small, and controlling
   `m(∂ⱼσ) ≤ m(σ)`).  Rejected in favour of proving acyclicity of `C_*(X)/C_*^{small}`
   directly from `homN_homotopy` plus eventual smallness, which reuses the project's existing
   relative short exact sequence and the pinned long exact sequence and avoids the five lemma.
2. **An explicit triangulation of the prism** `Δⁿ × I` into `n+1` simplices, with the classical
   index bookkeeping.  Rejected in favour of the acyclic-models cone recursion in the model
   `PrismPt n = Δs n × Δs 1`; the only combinatorial input then needed is `∂∘∂ = 0` for the
   *coface* direction, which the pinned `AlternatingCofaceMapComplex.d_squared` supplies once
   the model is packaged as a cosimplicial `ℤ₂`-module.
3. **A general convex-subset affine framework** (affine combinations in an arbitrary convex
   subset of a normed space) as the prism model.  Rejected because `Δs n × Δs 1` lets both
   coordinates reuse the existing `combo` API verbatim.
