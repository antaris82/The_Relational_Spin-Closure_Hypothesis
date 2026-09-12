# TASK 18 AUDIT — native singular small-simplices and excision engine

**Principal outcome: Outcome A — Excision closed.**

The chain prism, chain homotopy invariance, the contractibility smoke test, the native
barycentric subdivision of singular chains, `sd ~ id` with locality, eventual smallness, the
Small-Simplices quasi-isomorphism and the relative singular Excision theorem over `ZMod 2`
are all proved, with no `sorry`, no new `axiom`, no `native_decide`.

---

## 1. Exact new modules

All new modules are under `RequestProject/Spine/Nerve/` and are picked up by the existing
`RequestProject.Spine.+` glob of `lakefile.toml` (the lakefile was **not** modified).

| module | content |
|---|---|
| `Task18Affine.lean` | affine simplices `combo`, singular simplices in the project's model (`Sing`, `sMap`, `sOf`, `pre`), the codiscrete simplicial set `codisc`, linear chains `LChain`, `lbd`, `lmap`, realization `realizeChain` |
| `Task18LinearSubdivision.lean` | cone operator `lcone`, augmentation `laug`, barycentric subdivision `sd` and homotopy `sdT` on linear chains, naturality |
| `Task18Subdivision.lean` | WP4: singular subdivision `sdS`, homotopy `sdTS`, chain-map property, locality (`carrier`, `carriedIn`), naturality |
| `Task18Mesh.lean` | WP7 geometry: mesh bound `sd_support_mesh`, iterated mesh, `exists_pow_mesh_lt` |
| `Task18SmallSimplices.lean` | WP6: `smallSSet`, `smallInc`, `smallChains`; WP7: `exists_iterate_small`, `exists_iterate_small_chain` |
| `Task18Excision.lean` | WP8: iterated homotopy `homN`, acyclicity of `C_*(X)/C^{small}`, `isIso_homologyMap_smallInc`, `quasiIso_smallInc`; WP9: excision square, `excisionMap`, `excSC_shortExact`, `isIso_homologyMap_excisionMap`, `excisionIso` |
| `Task18ChainPrism.lean` | WP2: prism model `PrismPt`, cosimplicial coface operator `cobd` with `cobd_cobd`, universal prism chain, `prismOp`, `prismHomotopy`, `homologyMap_eq_of_prism` |
| `Task18Contractible.lean` | WP3: `exactAt_singCx_of_contractible`, `isZero_homology_of_contractible`, `isZero_homology_realized_simplex` |
| `Task18AxiomAudit.lean` | `#print axioms` for all principal Task-18 declarations |

## 2. Exact old modules reused

* `RequestProject/Spine/Nerve/UnitChainMap.lean` — `NerveGeom.SSetChain`, `sSetBoundary`,
  `sSetChainMap` (**the** chain model; no replacement model was introduced).
* `RequestProject/Spine/Nerve/Task13Normalization.lean` —
  `SpineTask13.sSetBoundary_comp_sSetBoundary`, `SpineTask13.modCat_hom_zsmul_neg_one_pow`,
  `SpineTask13.afmc_d_hom`.
* `RequestProject/Spine/Nerve/Task14RelativeChains.lean` — `sSetChainComplexFunctor` (+ the
  three identification lemmas `_X`, `_d`, `_map_f`), `RelChainMod`, `relChainCx`,
  `relChainCx_d`, `relChainCxMap`, `relProj`, `relSC`, `relSC_shortExact`, `relSingChainCx`,
  `toSSet_map_injective`.
* `RequestProject/Spine/Nerve/Task14RelativeLES.lean` — `pair_exact₁`, `pair_exact₂`.
* `RequestProject/Spine/Nerve/Task17StandardCellTopology.lean` —
  `SpineTask17.contractibleSpace_realized_simplex` (WP3 instantiation only).
* Pinned Mathlib: `AlgebraicTopology.AlternatingFaceMapComplex` (including its **dual**
  `AlternatingCofaceMapComplex.d_squared`), `TopCat.toSSet` / `TopCat.toSSetObjEquiv`,
  `stdSimplex` (`map`, `vertex`, `barycenter`, `diam_stdSimplex_le`, `isCompact_stdSimplex`),
  `lebesgue_number_lemma_of_metric`, `Homotopy` / `Homotopy.homologyMap_eq`,
  `ShortComplex` exactness API, `HomologicalComplex.shortExact_of_degreewise_shortExact`,
  `id_nullhomotopic`.

The Task-13–17 *cohomological* prism machinery (`Spine/Cohomology/…`) was **not** used:
Task 18 is a direct chain-level construction, and no chain/cochain duality was assumed.

## 3. Was any existing source modified?

**No.** No file predating Task 18 was edited (verified by `git status` / `git diff` against the
Task-17 tree). `lean-toolchain`, `lake-manifest.json` and `lakefile.toml` are untouched.

## 4. Production revision

* Lean `v4.28.0`
* Mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365`

(unchanged from Task 17; see `lean-toolchain`, `lake-manifest.json`.)

## 5. New theorem dependency DAG

```
Task18Affine
  combo, combo_comp, combo_stdC, combo_vertex, combo_apply_vertex
  Sing/sMap/sOf/pre, sing_delta
  codisc, LChain, lbd, lbd_lbd, lmap, lmap_lbd
  realizeChain, realizeChain_lbd, realizeChain_lmap, taut
        │
        ├────────────────────────────────────────────┐
        ▼                                            ▼
Task18LinearSubdivision                        Task18ChainPrism  (WP2)
  lcone, laug, lbd_lcone, lbd_lcone_zero         PrismPt, pcombo, prismPtMap
  sd (lbd_sd), sdT (sdT_homotopy)                prismCosimp ─► cobd, cobd_cobd
  lmap_sd, lmap_sdT                              botP/topP, lbd_botP/lbd_topP
        │                                        prismChain, prismCyc
        ▼                                              │  lbd_prismChain
Task18Subdivision  (WP4, WP5 locality)                 ▼
  sdS, sdTS                                      realizeP, realizeP_lbd,
  sdS_chain_map      (∂ ∘ sd = sd ∘ ∂)            realizeP_prismPtMap
  sdTS_homotopy      (∂T + T∂ = id + sd)          prismSimp, prismOp
  carrier/carriedIn, carrier_sdS, carrier_sdTS    singBd_prismSimp_zero/_succ
  sdS_natural                                     prism_identity_zero/_succ
        │                                         prismHom, prismHomotopy
        ▼                                         homologyMap_eq_of_prism
Task18Mesh  (WP7 geometry)                             │
  sd_support_mesh, chainMesh_sd, sdIter                ▼
  chainMesh_sdIter, exists_pow_mesh_lt           Task18Contractible  (WP3)
        │                                          exists_boundary_of_cycle
        ▼                                          exactAt_singCx_of_contractible
Task18SmallSimplices  (WP6, WP7)                   isZero_homology_of_contractible
  IsSmallAt, smallSSet, smallInc, smallChains      isZero_homology_realized_simplex
  range_smallInc_chainMap                             ▲
  sdS_smallChains, sdTS_smallChains                   │ (Task17 contractibility)
  sdSIter, exists_iterate_small
  exists_iterate_small_chain
        │
        ▼
Task18Excision  (WP8, WP9)
  homN, homN_homotopy, homN_smallChains
  smallChains_zero_eq_top ─► isZero_relSmall_zero
  relSmall_exactAt ─► isZero_relSmall_homology
  (+ Task14 relSC_shortExact, pair_exact₁/₂)
        ├─► mono/epi_homologyMap_smallInc ─► isIso_homologyMap_smallInc ─► quasiIso_smallInc
        └─► WP9:
              mem_range_sSetChainMap, subInc, range_toSSet_subInc,
              toSmallU/toSmallV, range_toSmallU/V, incInterU/V
              excPsi (degreewise iso: excPsi_injective/​surjective ─► excPsi_isIso)
              excAlpha, excBeta, excSC, excSC_shortExact
              excisionMap, excisionMap_factor
              isIso_homologyMap_excAlpha
              ─► isIso_homologyMap_excisionMap ─► excisionIso
```

## 6. Exact chain-prism theorem

Chain level, on singles (`SpineTask18.singBd_prismSimp_succ`, `Task18ChainPrism.lean`), for
`H : C(↥X × Δs 1, ↥Y)` and `σ : Sing X (n+1)`:

```lean
singBd Y (n + 1) (prismSimp H σ)
  = singMap (endMap H e0) (n + 1) (Finsupp.single σ 1)
    + singMap (endMap H e1) (n + 1) (Finsupp.single σ 1)
    + prismOp H n (singBd X n (Finsupp.single σ 1))
```

and in degree zero (`singBd_prismSimp_zero`)

```lean
singBd Y 0 (prismSimp H σ)
  = singMap (endMap H e0) 0 (Finsupp.single σ 1) + singMap (endMap H e1) 0 (Finsupp.single σ 1)
```

For arbitrary chains (`prism_identity_succ`, `prism_identity_zero`):

```lean
singBd Y (n + 1) (prismOp H (n + 1) c) + prismOp H n (singBd X n c)
  = singMap (endMap H e0) (n + 1) c + singMap (endMap H e1) (n + 1) c
```

i.e. the sign-free mod-2 form `∂P + P∂ = C_*(f) + C_*(g)`.  Here
`prismOp H n : SSetChain (TopCat.toSSet.obj X) n →ₗ[ZMod 2] SSetChain (TopCat.toSSet.obj Y) (n+1)`
is a genuine `ZMod 2`-linear map on the **exact chain modules used by `SpineTask14`**
(`NerveGeom.SSetChain (TopCat.toSSet.obj ·)`).

The construction is acyclic-models in the explicit model `PrismPt n = Δs n × Δs 1`: the
universal prism chain `prismChain n : LChain (PrismPt n) (n+1)` is defined by a cone recursion
and its boundary is computed by `lbd_prismChain`:

```lean
lbd (PrismPt n) n (prismChain n) = prismCyc n
prismCyc 0       = botP 0 + topP 0
prismCyc (n + 1) = botP (n+1) + topP (n+1) + cobd n (n+1) (prismChain n)
```

The only nontrivial combinatorial input is `cobd_cobd`, `∂∘∂ = 0` for the model **coface**
operator, obtained from the pinned `AlternatingCofaceMapComplex.d_squared` applied to the
honest cosimplicial `ℤ₂`-module `prismCosimp k` (signs removed by
`SpineTask13.modCat_hom_zsmul_neg_one_pow`).

## 7. Exact chain-homotopy packaging

`SpineTask18.prismHomotopy H :`
`Homotopy (singCxMap (endMap H e0)) (singCxMap (endMap H e1))`

— a genuine `Homotopy` of morphisms of `ChainComplex (ModuleCat (ZMod 2)) ℕ`, with components
`prismHom H i j = ofHom (prismOp H i)` when `j = i+1` and `0` otherwise; the `comm` field is
exactly the mod-2 prism identity.

The homological consequence, obtained from the pinned API and **not** by a hand computation on
cycles:

`SpineTask18.homologyMap_eq_of_prism (q : ℕ) :`
`HomologicalComplex.homologyMap (singCxMap (endMap H e0)) q`
`= HomologicalComplex.homologyMap (singCxMap (endMap H e1)) q`.

`singCx X = SpineTask14.sSetChainComplexFunctor.obj (TopCat.toSSet.obj X)`,
`singCxMap g = SpineTask14.sSetChainComplexFunctor.map (TopCat.toSSet.map g)`; the passage
between `d` and `sSetBoundary` uses only `SpineTask14.sSetChainComplexFunctor_d`.

## 8. Exact contractibility consequence

`SpineTask18.exactAt_singCx_of_contractible [ContractibleSpace ↥X] (m : ℕ) :`
`(singCx X).ExactAt (m + 1)`

`SpineTask18.isZero_homology_of_contractible [ContractibleSpace ↥X] (m : ℕ) :`
`IsZero ((singCx X).homology (m + 1))`

instantiated at Task 17's realized simplex:

`SpineTask18.isZero_homology_realized_simplex (r m : ℕ) :`
`IsZero ((singCx (SSet.toTop.obj Δ[r])).homology (m + 1))`.

**Nothing is claimed in degree 0 and nothing is claimed about reduced homology.**  The proof
uses the WP2 prism applied to a null-homotopy of the identity, plus the boundary of constant
simplices; the parity split is genuine (in even positive degree the augmentation of a cycle is
shown to vanish, in odd degree the constant chain is exhibited as a boundary).

## 9. Exact subdivision chain map

`SpineTask18.sdS (X) (k) : SSetChain (TopCat.toSSet.obj X) k →ₗ[ZMod 2] SSetChain (TopCat.toSSet.obj X) k`
(linear by construction: it is a `Finsupp.linearCombination`), defined *tautologically* by
`sd(σ) = σ_# (sd ιₙ)` through `realizeChain`, i.e. attached to the actual geometric standard
simplex `Δs n = stdSimplex ℝ (Fin (n+1))` which is the domain of singular simplices in the
pinned model.  Finiteness in each degree is automatic (`Finsupp`).

`SpineTask18.sdS_chain_map (X) (k) : (singBd X k).comp (sdS X (k+1)) = (sdS X k).comp (singBd X k)`
— i.e. `∂ ∘ sd = sd ∘ ∂`; this is a **chain map**, not merely a degreewise map.

Naturality: `SpineTask18.sdS_natural (g : X ⟶ Y) (k) : (singMap g k).comp (sdS X k) = (sdS Y k).comp (singMap g k)`.

This operator is *not* a simplicial-set subdivision functor; it is defined on singular chains.

## 10. Exact `sd ~ id` theorem

`SpineTask18.sdTS_homotopy (X) (k) (c) :`
`singBd X (k+1) (sdTS X (k+1) c) + sdTS X k (singBd X k c) = c + sdS X (k+1) c`

(the mod-2 form of `∂D + D∂ = id + sd`), together with the degenerate cases
`sdS_zero_deg`, `sdTS_zero_deg`.

Iterated form (`Task18Excision.lean`): `homN X k N = ∑_{i<N} sdTS ∘ sd^i` and

`SpineTask18.homN_homotopy (k) (N) (c) :`
`singBd X (k+1) (homN X (k+1) N c) + homN X k N (singBd X k c) = c + sdSIter X (k+1) N c`.

This is a **chain homotopy identity**; it is used below to prove exactness, and (through the
long exact sequence) an isomorphism on homology.  It is *not* itself packaged as a
`Homotopy` object.

## 11. Exact subdivision locality theorem

Carrier of a singular simplex: `carrier σ = Set.range (sMap σ)`;
`carriedIn W k` = chains supported on simplices with carrier `⊆ W`.

* `SpineTask18.realizeChain_carried : carrier σ ⊆ W → realizeChain σ k c ∈ carriedIn W k`
* `SpineTask18.carrier_sdS : carrier σ ⊆ W → sdS X k (single σ 1) ∈ carriedIn W k`
* `SpineTask18.carrier_sdTS : carrier σ ⊆ W → sdTS X k (single σ 1) ∈ carriedIn W (k+1)`

(every simplex occurring in `sd σ`, and in the homotopy term `D σ`, factors as
`pre (combo p) σ`, hence is carried by the image of `σ`).  The consequences used for
Small-Simplices:

* `SpineTask18.sdS_smallChains`, `sdTS_smallChains`, `sdSIter_smallChains`,
  `SpineTask18.homN_smallChains` — smallness is preserved by `sd`, by the subdivision
  homotopy, by all iterates, and by `homN`.

## 12. Exact eventual-smallness theorem for one simplex

`SpineTask18.exists_iterate_small (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)`
`(hUV : U ∪ V = Set.univ) {n} (σ : Sing X n) :`
`∃ N : ℕ, sdSIter X n N (Finsupp.single σ 1) ∈ smallChains U V n`

The proof is genuinely geometric: `lebesgue_number_lemma_of_metric` on the compact metric
space `Δs n = stdSimplex ℝ (Fin (n+1))` for the two-element open cover
`{σ⁻¹U, σ⁻¹V}`, combined with the mesh estimate

`SpineTask18.sd_support_mesh : MeshLE p r → ∀ q ∈ (sd n k (single p 1)).support,`
`(each vertex of q lies in the convex hull of p) ∧ MeshLE q ((k/(k+1)) * r)`

and `chainMesh_sdIter` / `exists_pow_mesh_lt` (`(n/(n+1))^N → 0`).

## 13. Exact eventual-smallness theorem for a finite chain

`SpineTask18.exists_iterate_small_chain (U V) (hU) (hV) (hUV) {k}`
`(c : SSetChain (TopCat.toSSet.obj X) k) : ∃ N : ℕ, sdSIter X k N c ∈ smallChains U V k`

with `N := c.support.sup g`, `g σ` the depth supplied by `exists_iterate_small` for the single
simplex `σ`: only the **finite support of the individual chain** is used, never a globally
uniform depth.

## 14. Exact definition of the small-chain complex

Smallness at every simplicial degree: `IsSmallAt U V σ ↔ carrierAt σ ⊆ U ∨ carrierAt σ ⊆ V`;
it is stable under all simplicial operators (`IsSmallAt.map`), so

`SpineTask18.smallSSet U V : SSet` with `(smallSSet U V).obj n = {σ // IsSmallAt U V σ}`

is an honest **simplicial subset** of `TopCat.toSSet.obj X`, with degreewise injective
inclusion `SpineTask18.smallInc U V`.  Its chain complex is the project's own
`SpineTask14.sSetChainComplexFunctor.obj (smallSSet U V)`; degreewise its image inside
`C_*(X)` is the submodule `smallChains U V k` (`range_smallInc_chainMap`).  Faces of a small
simplex are small by construction, so no separate subcomplex condition is needed.

## 15. Is the small-chain inclusion proved a quasi-isomorphism?

**Yes.**

* `SpineTask18.relSmall_exactAt (hU hV hUV) (q) : (relChainCx (smallInc U V)).ExactAt q` —
  the quotient complex `C_*(X)/C_*^{small}` is exact in every degree (this is where
  `homN_homotopy`, `homN_smallChains` and eventual smallness are used);
* `SpineTask18.isZero_relSmall_homology` — hence its homology vanishes;
* with `SpineTask14.relSC_shortExact` and the pinned long exact sequence
  (`pair_exact₁`, `pair_exact₂`, `ShortComplex.exact_iff_mono/epi`) this gives
  `mono_homologyMap_smallInc` and `epi_homologyMap_smallInc`, hence
* `SpineTask18.isIso_homologyMap_smallInc (q) :`
  `IsIso (HomologicalComplex.homologyMap (sSetChainComplexFunctor.map (smallInc U V)) q)`
  — **both** injectivity and surjectivity on homology, in every degree;
* packaged as `SpineTask18.quasiIso_smallInc : QuasiIso (sSetChainComplexFunctor.map (smallInc U V))`.

## 16. Exact Excision theorem

With `subTop W = TopCat.of ↥W`, `subInc W : subTop W ⟶ X` the subspace inclusion, and
`incInterU U V : subTop (U ∩ V) ⟶ subTop U`, the inclusion of pairs `(U, U∩V) → (X, V)` is

```lean
def excisionMap : relSingChainCx (incInterU U V) ⟶ relSingChainCx (subInc V) :=
  relChainCxMap (TopCat.toSSet.map (incInterU U V)) (TopCat.toSSet.map (subInc V))
    (TopCat.toSSet.map (incInterV U V)) (TopCat.toSSet.map (subInc U)) …
```

stated for the project's exact relative singular complex `SpineTask14.relSingChainCx`.

**`SpineTask18.isIso_homologyMap_excisionMap`**

```lean
theorem isIso_homologyMap_excisionMap (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (excisionMap U V) q)
```

and the packaged isomorphism

```lean
noncomputable def excisionIso (q : ℕ) :
    (relSingChainCx (incInterU U V)).homology q ≅ (relSingChainCx (subInc V)).homology q
```

i.e. `H_q(U, U∩V; ℤ₂) ≅ H_q(X, V; ℤ₂)` for every `q`.

The classical algebraic mechanism is exposed exactly as required:

* `excisionMap = excPsi ≫ excAlpha` (`excisionMap_factor`);
* `excPsi : C_*(U)/C_*(U∩V) ⟶ C^{small}_*/C_*(V)` is a **degreewise isomorphism**
  (`excPsi_injective`, `excPsi_surjective`, `excPsi_isIso`) — this is the statement
  `C^{small}_* = C_*(U) + C_*(V)` at the relevant level;
* `0 → C^{small}_*/C_*(V) → C_*(X)/C_*(V) → C_*(X)/C^{small}_* → 0` is short exact
  (`excSC_shortExact`), and its third term is acyclic by WP8, so `excAlpha` is a
  homology isomorphism (`isIso_homologyMap_excAlpha`).

A closed-subset excision corollary was **not** derived (it was optional).

## 17. Does B1 remain open?

**Yes.**  `H_q^sing(|Δ[r]|, |∂Δ[r]|; ℤ₂)` is *not* computed.  Task 18 deliberately stops at
general Excision; the only statement about `|Δ[r]|` proved here is the WP3 smoke test
`isZero_homology_realized_simplex` (absolute homology, positive degrees only).

## 18. Does the canonical top generator remain open?

**Yes.**  No generator of the standard-cell relative homology is constructed.

## 19. Does B3 remain open?

**Yes.**  Nothing about `relJ` inducing a homology isomorphism was attempted; `relJ`,
`J = C_*(η_K)` and all Task-13–17 interfaces are untouched.

## 20. Does `geometricHmap` remain open?

**Yes.**  Not attempted (nor the nerve theorem, nor `w₂(TM)`).

## 21. First exact missing theorem if full Excision was not reached

Not applicable: full open-cover Excision was reached (Outcome A).

Cellwise excision/additivity for the skeletal attachment is **not** identified with WP9 and
remains a further, separate theorem.

---

## Terminology discipline

Throughout this audit:

* **chain map** — `sdS_chain_map`, `realizeP_lbd`, `sdS_natural`;
* **chain homotopy identity** (unpackaged) — `sdTS_homotopy`, `homN_homotopy`,
  `prism_identity_succ`/`_zero`;
* **chain homotopy** (packaged `Homotopy` object) — `prismHomotopy`;
* **equality on homology** — `homologyMap_eq_of_prism`;
* **quasi-isomorphism** — `quasiIso_smallInc` (and the degreewise `isIso_homologyMap_smallInc`);
* **short exact sequence** — `relSC_shortExact` (reused), `excSC_shortExact` (new);
* **relative homology isomorphism** — `isIso_homologyMap_excisionMap`, `excisionIso`.

None of these is promoted to another in the statements above.

## Verification

`lake build RequestProject` — **Build completed successfully (8232 jobs)**, no errors, no
warnings other than the `#print axioms` info lines of the audit modules.

`#print axioms` for every principal Task-18 declaration (see
`RequestProject/Spine/Nerve/Task18AxiomAudit.lean`) reports exactly

`[propext, Classical.choice, Quot.sound]`.

`rg -n "sorry|admit|axiom|native_decide" RequestProject/Spine/Nerve/Task18*.lean` returns only
the prose occurrence inside the audit module's doc-comment.
