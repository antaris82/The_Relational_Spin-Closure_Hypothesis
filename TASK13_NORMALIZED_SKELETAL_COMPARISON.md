# Task 13 — Normalized skeletal comparison and cohomology bridge

**Environment.** Lean `v4.28.0`; Mathlib pinned at `lake-manifest.json` rev
`8f9d9cff6bd728b17a24e163c9402775d9e6a365` (`lakefile.toml` requires `v4.28.0`). Neither the
toolchain nor the manifest was touched by this task. All statements below marked `PROVED`
are `sorry`-free and compile in this pin; all statements marked `MISSING` were established by
exhaustive name searches over the pinned environment (method recorded in §2.5).

**Headline (WP18 decision, stated once and unambiguously).**

> **Bridge A is selected**: `J` quasi-iso ⇒ `J` chain-homotopy equivalence ⇒ `geometricHmap`
> bijective. Its *algebraic* half is `PINNED_ADAPTABLE` (K-projective machinery, §11) and its
> *second* half is already `DERIVED` in the project (Task 10,
> `NerveGeom.geometricHmap_bijective_of_chainHomotopyEquiv`).
> **But the bridge is not reached**: its input — `J` is a quasi-isomorphism — is
> `BLOCKED` at the first missing theorem, which is *topological*, not algebraic:
>
> **`EXCISION` / relative singular homology of a pair is entirely absent from the pin**
> (§9, §10), and with it the standard cell pair `H_*(|Δ^r|, |∂Δ^r|;ℤ₂)` and the
> cell-attachment decomposition of `|K^{(r)}|` over `|K^{(r-1)}|`.
>
> Consequently `NerveGeom.geometricHmap` is **not** unconditionally bijective, the conditional
> `GeometricComparison` assumption stays in place (WP20 blocked), and the scope actually
> reached on the simplicial side is recorded honestly in §13.

What Task 13 *did* settle, unconditionally and in Lean, is the whole **degeneracy-control
layer** that the previous tasks lacked: the project's unnormalized complex is chain-homotopy
equivalent to its normalized quotient, that comparison is natural, and the normalized relative
skeletal complex is computed exactly.

---

## 0. Deliverable index

| # | deliverable | where |
| --- | --- | --- |
| 1 | pinned normalization-infrastructure audit | §2 |
| 2 | project-native degeneracy-subcomplex status | §3 |
| 3 | normalization theorem | §4 |
| 4 | skeletal compatibility theorem | §5 |
| 5 | relative normalization theorem | §5.3 |
| 6 | normalized relative skeletal computation | §6 |
| 7 | relative simplicial homology audit | §7 |
| 8 | realized skeletal pair construction | §8 |
| 9 | standard simplex/boundary relative homology audit | §9 |
| 10 | relative singular homology / LES audit | §10 |
| 11 | excision / cell-attachment audit | §10.3 |
| 12 | canonical relative comparison map | §5.3, §12 |
| 13 | strongest proved one-skeleton-step comparison | §12 |
| 14 | strongest proved finite-skeletal comparison | §13 |
| 15 | quasi-iso ⇒ chain-homotopy-equivalence audit | §11 |
| 16 | direct-cohomology alternative audit | §11.3 |
| 17 | hard Bridge A/B/C decision | §11.4 |
| 18 | exact remaining blocker | §14 |
| 19 | updated certification DAG | §15 |
| 20 | source ledger | `TASK13_EXTERNAL_SOURCES.md` |
| 21 | this document | — |
| 22 | complete failbuild ledger | `TASK13_FAILBUILDS.md` |
| 23 | full build evidence | §16 |
| 24 | axiom audit | §16.2 |

New Lean modules (all `sorry`-free, no `axiom`, no `native_decide`, no `partial`, no
`implemented_by`):

* `RequestProject/Spine/Nerve/Task13Normalization.lean` — Objective A;
* `RequestProject/Spine/Nerve/Task13Skeletal.lean` — Objective B, simplicial side;
* `RequestProject/Spine/Nerve/Task13CanonicalMap.lean` — WP1 freeze + WP12 descent of `J`;
* `RequestProject/Spine/Nerve/Task13PinAudit.lean` — compile probes + axiom audit.

None of them is imported by the production Spine (`RequestProject.Spine.Core`); they are built
by the library glob, exactly as the Task-12 probe layer was.

---

## 1. WP1 — the frozen canonical data

Unchanged, and not replaced anywhere in Task 13:

| object | declaration |
| --- | --- |
| `K = N(𝓤)` | `NerveGeom.coverNerveSSet` |
| `\|K\|` | `NerveGeom.coverNerveRealization = SSet.toTop.obj K` |
| `η_K` | `sSetTopAdj.unit.app K` |
| `J = C_*(η_K)` | `NerveGeom.chainMap`, identified with the unit linearisation by `NerveGeom.chainMap_eq_unitChainMap` (Task 10) |
| `geometricHmap` | `NerveGeom.geometricHmap` (Task 9) |

Task 13 re-verifies the freeze at theorem level in `Task13CanonicalMap.lean`:
`nerveChain_eq`, `nerveBoundary_eq`, `singChain_eq` are all `rfl`, so every Objective-A
statement about `SSetChain`/`sSetBoundary` *is* a statement about the Task-9 objects, and
`normJ` is obtained by applying the natural construction `normMap` to `η_K` itself
(`normJ_normProj`), not by choosing a new map.

---

## 2. WP2 — audit of the pinned normalization infrastructure

### 2.1 Present and used

| item | pinned declaration | class |
| --- | --- | --- |
| alternating face map complex | `AlgebraicTopology.alternatingFaceMapComplex`, `AlternatingFaceMapComplex.objD`, `alternatingFaceMapComplex_obj_d` | `PINNED_DIRECT` |
| normalized Moore complex | `AlgebraicTopology.normalizedMooreComplex` | `PINNED_DIRECT` (not used: subcomplex form, see §3) |
| inclusion of the Moore complex | `AlgebraicTopology.inclusionOfMooreComplexMap` | `PINNED_DIRECT` (not used) |
| Moore ≃ alternating face map complex | `AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex` | `PINNED_DIRECT` (not used: wrong side of the normalization, §3) |
| Dold–Kan projector | `AlgebraicTopology.DoldKan.PInfty`, `PInfty_f_idem`, `PInfty_f_0` | `PINNED_DIRECT`, used |
| complementary projector | `AlgebraicTopology.DoldKan.QInfty`, `QInfty_f`, `PInfty_add_QInfty`, `Q_f_0_eq` | `PINNED_DIRECT`, used |
| `P∞` kills degeneracies | `AlgebraicTopology.DoldKan.σ_comp_PInfty` | `PINNED_DIRECT`, used |
| decomposition of `Q` into terms ending in a degeneracy | `AlgebraicTopology.DoldKan.decomposition_Q` | `PINNED_DIRECT`, used |
| homotopy `P∞ ≃ id` | `AlgebraicTopology.DoldKan.homotopyPInftyToId` | `PINNED_DIRECT`, used |
| naturality of `P∞` | `AlgebraicTopology.DoldKan.PInfty_f_naturality` | `PINNED_DIRECT`, used |
| Dold–Kan equivalence (abelian case) | `CategoryTheory.Abelian.DoldKan.equivalence`, `DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi` | `PINNED_DIRECT` (not needed) |
| degenerate/nondegenerate simplices | `SSet.degenerate`, `SSet.nonDegenerate`, `SSet.degenerate_eq_iUnion_range_σ`, `SSet.mem_degenerate_iff`, `SSet.exists_nonDegenerate` | `PINNED_DIRECT`, used |
| skeleta of a simplicial set | `SSet.skeleton`, `SSet.mem_skeleton`, `SSet.skeleton_obj_eq_top`, `SSet.mem_skeleton_obj_iff_of_nonDegenerate`, `SSet.skeleton_succ` | `PINNED_DIRECT`, used |
| subcomplex API | `SSet.Subcomplex`, `Subcomplex.toSSet`, `Subcomplex.homOfLE`, `Subcomplex.mem_degenerate_iff`, `Subcomplex.mem_nonDegenerate_iff` | `PINNED_DIRECT`, used |
| homotopy of a `Homotopy` in a chain complex | `Homotopy.dNext_zero_chainComplex`, `Homotopy.dNext_succ_chainComplex`, `Homotopy.prevD_chainComplex` | `PINNED_DIRECT`, used |

Every one of these is exercised by the build: the used ones inside the proofs, the unused ones
as compile probes in `Task13PinAudit.lean`.

### 2.2 Present but not adequate

| item | why not adequate |
| --- | --- |
| normalized **Moore** complex (`normalizedMooreComplex`) | it is the *subcomplex* `⋂_{i>0} ker dᵢ`, not the *quotient* `C/D` demanded by WP3/WP4. The pin contains **no** definition of the degenerate subcomplex `D` and no comparison `C/D ≃ Moore`. |
| `hσ'_naturality` (`DoldKan.Homotopies`) | naturality of the *pieces* of the contracting homotopy. The pin has **no** naturality lemma for the assembled `homotopyPInftyToId`; this is exactly what blocks the second half of the relative statement (§5.3). |
| `ModuleCat.free` | universe-monomorphic (`Type u ⥤ ModuleCat.{u} R` with `R : Type u`), so it cannot produce `ℤ₂`-modules in the project's universe `u`. Task 13 therefore builds the free simplicial `ℤ₂`-module by hand (`SpineTask13.freeSSetModule`, 6 lines). |

### 2.3 Missing

| item | class |
| --- | --- |
| degeneracy subcomplex `D_*(X)` of the (un)normalized chain complex | `MISSING` — supplied here |
| quotient normalization `C_* ↠ C_*/D_*` and its chain-homotopy equivalence | `MISSING` — supplied here |
| `N_q ≅` free module on nondegenerate `q`-simplices | `MISSING` — supplied here |
| naturality of `homotopyPInftyToId` | `MISSING` — not supplied (see §5.3, §14.2) |

### 2.4 Not relevant

`AlgebraicTopology.DoldKan.Compatibility.*`, `Idempotents.DoldKan.*`,
`Preadditive.DoldKan.*` (Karoubi bookkeeping for the equivalence), `SSet.sk`/`SSet.skAdj`
(truncation adjunction; the subcomplex skeleton is the one that matches the classical filtration
argument): `NOT_RELEVANT`.

### 2.5 Method for the negative findings

For each keyword the whole pinned environment was enumerated (`Lean.Environment.constants`)
and filtered by substring, in a scratch file importing all of `Mathlib`. Counts obtained:

| keyword | number of declarations |
| --- | --- |
| `excision` / `Excision` | **0** |
| `singularHomology` | 3 (`AlgebraicTopology.singularHomologyFunctor`, plus two totally-disconnected corollaries) |
| `singularChain` | 4 (`AlgebraicTopology.singularChainComplexFunctor` and variants) |
| `Relative`+`Homolog` / `relative`+`homolog` | **0** |
| `CWComplex`+`omolog` | **0** |
| `cellular` / `Cellular` | **0** |
| `CWComplex` ∧ (`SSet` or `toTop`) | **0** |
| `MayerVietoris` | 85, all in `CategoryTheory.GrothendieckTopology` (sheaf cohomology), none topological |
| `homotopyEquivOfQuasiIso` | **0** |

Absence cannot be witnessed by a Lean declaration; this enumeration is the evidence offered.

---

## 3. WP3 — the degeneracy subcomplex (project-native status)

**Status before Task 13:** the project's simplicial chain complex is the *unnormalized* one
(`NerveGeom.SSetChain`, `NerveGeom.sSetBoundary`; for the nerve, `NerveGeom.simpBoundary`), and
the project exposed **no** degeneracy subcomplex. (`NerveGeom.isDegenerate_iff_exists_degen`
existed at the level of *simplices*, not chains.)

**Supplied by Task 13** (`Task13Normalization.lean`, `Task13Skeletal.lean`):

```lean
def degenSubmodule (S : SSet.{u}) : (q : ℕ) → Submodule (ZMod 2) (SSetChain S q)
  | 0       => ⊥
  | (n + 1) => ⨆ i : Fin (n + 1),
      LinearMap.range (Finsupp.lmapDomain (ZMod 2) (ZMod 2) (S.σ i))
```

| theorem | statement | status |
| --- | --- | --- |
| `single_degen_mem` | every degenerate simplex spans a chain in `D` | `PROVED` |
| `degenSubmodule_eq_supported` | `D_q(S) = Finsupp.supported ℤ₂ ℤ₂ (S.degenerate q)` — `D` is *exactly* the chains supported on degenerate simplices | `PROVED` |
| `proj_degen_zero` | `P∞ D_q = 0` | `PROVED` (from `σ_comp_PInfty`) |
| `sub_proj_mem_degen` | `x - P∞ x ∈ D_q` | `PROVED` (from `PInfty_add_QInfty` + `decomposition_Q`) |
| `boundary_degen_mem` | **`∂ D_{q+1} ⊆ D_q`** | `PROVED` |

The proof of `∂D ⊆ D` deliberately avoids a hand computation with the simplicial identities:
for `x ∈ D`, `P∞(∂x) = ∂(P∞ x) = 0`, hence `∂x = ∂x − P∞(∂x) ∈ D`.

Endpoint: **`DEGENERACY_CONTROL` — achieved.**

---

## 4. WP4 — the normalization theorem

Definitions (`Task13Normalization.lean`): `NormChain S q = SSetChain S q ⧸ degenSubmodule S q`,
`normBoundary` (induced by `boundary_degen_mem`), `normProj = mkQ`,
`normInc = liftQ P∞`, `normHtpy = (homotopyPInftyToId _).hom q (q+1)`.

| theorem | statement | status |
| --- | --- | --- |
| `afmc_d_hom` | the project's `sSetBoundary` **is** Mathlib's alternating face map differential on `ℤ₂[S]` (signs vanish in characteristic 2) | `PROVED` |
| `sSetBoundary_comp_sSetBoundary` | `∂∘∂ = 0` for the project's complex | `PROVED` |
| `normBoundary_comp_normBoundary` | `∂̄∘∂̄ = 0` | `PROVED` |
| `normProj_comm`, `normInc_comm` | `p` and `i` are chain maps | `PROVED` |
| `normProj_comp_normInc` | **`p ∘ i = id`** (on the nose) | `PROVED` |
| `normInc_comp_normProj` | `i ∘ p = P∞` | `PROVED` |
| `normHtpy_zero`, `normHtpy_succ` | **`∂h + h∂ = id + i∘p`** in every degree (over `ℤ₂`, `−` is `+`) | `PROVED` |

Together: `C_*^{simp,unn}(S;ℤ₂) ≃_ch N_*(S;ℤ₂)`, with explicit `p`, `i`, `h`.

**Classification: `NORMALIZATION_CHAIN_EQUIV`.** (Not merely a quasi-isomorphism.)

Naturality (`normMap`, `normProj_natural`, `normInc_natural`, `normMap_comm`,
`sSetChainMap_degen_mem`): the construction is natural in `S` for `p`, `i`, `∂̄` and the induced
maps, hence compatible with simplicial maps, with subcomplex/skeletal inclusions, and with the
canonical `J`. The homotopy `h` is *not* proved natural (§5.3).

Answer to Final Question 1: **the project-native unnormalized simplicial chain complex is
theorem-level chain-homotopy equivalent (not merely quasi-isomorphic) to the normalized
quotient complex, with `p i = id` and `i p ≃ id`.**

---

## 5. WP5 — skeletal compatibility

### 5.1 The skeletal pair in the pin

`SSet.skeleton n` is the subcomplex generated by simplices of dimension `< n`, so
`K^{(r)} = Sk X (r+1)` and the pair `K^{(r-1)} ⊆ K^{(r)}` is
`skInc X r : Sk X r ⟶ Sk X (r+1)` (`SSet.Subcomplex.homOfLE` of `X.skeleton.monotone`).
The indexing shift is stated in the module and used consistently.

### 5.2 The absolute square

`normProj_natural (skInc X r) q` and `normInc_natural (skInc X r) q` give exactly the
commuting square demanded by WP5,

```
C_*(K^{(r-1)}) ──→ C_*(K^{(r)})
      │ p                │ p
      ▼                  ▼
N_*(K^{(r-1)}) ──→ N_*(K^{(r)})
```

together with the reverse square for `i`. `PROVED`.

### 5.3 The relative comparison

`RelChain X r q` (relative unnormalized) and `RelNormChain X r q` (relative normalized) are the
quotients by the images of the skeletal inclusion, and

* `relNormProj : RelChain → RelNormChain` — `PROVED` (descent of `p`);
* `relNormInc : RelNormChain → RelChain` — `PROVED` (descent of `i`, using naturality of `P∞`);
* `relNormProj_comp_relNormInc : pʳᵉˡ ∘ iʳᵉˡ = id` — `PROVED`;
* `iʳᵉˡ ∘ pʳᵉˡ ≃ id` — **NOT PROVED**.

The missing ingredient is precisely: *naturality of the contracting homotopy*, i.e. for every
simplicial map `f : X ⟶ Y`,

```
C_*(f) ∘ (homotopyPInftyToId X).hom q (q+1) = (homotopyPInftyToId Y).hom q (q+1) ∘ C_*(f).
```

The pin provides `DoldKan.hσ'_naturality` (naturality of the building blocks) and
`natTransHσ`, `natTransP`, `natTransPInfty` (naturality of `Hσ`, `P q`, `P∞`), but
`homotopyPInftyToId` is assembled by recursion (`homotopyPToId`, `Homotopy.add`,
`Homotopy.compLeft`) and no naturality lemma for the assembled homotopy exists. Deriving it is
routine but was not done here.

**Classification: `RELATIVE_NORMALIZATION` = split surjection `PROVED`; full relative
chain-homotopy equivalence `DEFERRED` (small, purely simplicial gap; not the route blocker).**

Answer to Final Question 2: **yes for the absolute squares and for the induced relative maps;
the relative statement is currently a split surjection, not yet a proved relative
chain-homotopy equivalence.**

---

## 6. WP6 — the normalized relative skeletal complex

| statement | Lean | status |
| --- | --- | --- |
| in dimension `≥ n`, every simplex of the `n`-skeleton is degenerate | `degenerate_of_mem_skeleton` | `PROVED` |
| `N_q(K^{(r)}) = 0` for `q > r` | `normChain_skeleton_subsingleton` | `PROVED` |
| **`N_q(K^{(r)},K^{(r-1)}) = 0` for `q < r`** | `relNormChain_subsingleton_of_lt` | `PROVED` |
| **`N_q(K^{(r)},K^{(r-1)}) = 0` for `q > r`** | `relNormChain_subsingleton_of_gt` | `PROVED` |
| **`N_r(K^{(r)},K^{(r-1)}) ≅ ℤ₂⟨NDeg_r⟩`** | `relNormChainEquiv` | `PROVED` |
| the generating set is the *nondegenerate* `r`-simplices of `X` | `nonDegenerateSkeletonEquiv`, `normChainEquiv`, `degenSubmodule_eq_supported` | `PROVED` |

Precision about the generators, as demanded: the identification is
`N_q(S) ≅ (↥(S.nonDegenerate q) →₀ ℤ₂)` where `SSet.nonDegenerate` is the pinned notion
(complement of `SSet.degenerate`), **not** the set of all `q`-simplices; and in the relative
degree-`r` case the subcomplex contributes nothing because its own normalized chains already
vanish in degree `r` (`normChain_skeleton_subsingleton` with `n = q = r`).

Endpoint: **`RELATIVE_SIMPLICIAL` (normalized, skeletal) — achieved.**

Answer to Final Question 3: **yes — `N_q(K^{(r)},K^{(r-1)}) = 0` for every `q ≠ r`, and degree
`r` is free over `ℤ₂` on the nondegenerate `r`-simplices.**

---

## 7. WP7 — relative simplicial homology infrastructure in the pin

| capability | pin | class |
| --- | --- | --- |
| chain complex of a simplicial pair | absent as such; a quotient of the free chain modules is a two-line construction (done here: `RelChain`, `RelNormChain`) | `MISSING`/`NATIVE_CHEAP` |
| homology of a relative complex | `HomologicalComplex.homology` applies once the relative complex is packaged as a `HomologicalComplex` | `PINNED_ADAPTABLE` |
| long exact sequence of a pair | `HomologicalComplex.HomologySequence.snakeInput`, `composableArrows₃_exact`, `composableArrows₅_exact`, `δ_naturality` — the LES of a **short exact sequence of complexes**, with naturality | `PINNED_ADAPTABLE` |
| maps induced by inclusions, naturality | `HomologicalComplex.homologyMap`, `HomologySequence.δ_naturality` | `PINNED_DIRECT` |
| five lemma | no named five/four lemma in the pin; `CategoryTheory.ComposableArrows` exactness API would support an explicit chase | `MISSING` |

Task 13 implemented only the small native wrapper it needed (`RelChain`, `RelNormChain` as
`Submodule` quotients) rather than importing a parallel theory; it did **not** package the
project's complexes as `HomologicalComplex`, since that is only worth doing once the
topological side is unblocked.

Current upstream Mathlib: not consulted for this task beyond the pin (Task 11 already audited
the upstream delta and found nothing closing the gap). Nothing was imported from upstream.

---

## 8. WP8 — the realized skeletal pair

What is actually formalized:

* `SSet.toTop : SSet ⥤ TopCat` (pinned) — so `|K^{(r)}| := SSet.toTop.obj (Sk K (r+1))` and
  `|K^{(r-1)}| := SSet.toTop.obj (Sk K r)` are defined objects of `TopCat`, and
  `SSet.toTop.map (skInc K r) : |K^{(r-1)}| ⟶ |K^{(r)}|` is a continuous map — this much is
  `PINNED_DIRECT`.
* Whether that map is a **subspace inclusion** (a homeomorphism onto its image, or even
  injective) is **not** available in the pin: there is no theorem that `SSet.toTop` preserves
  monomorphisms, no theorem that it preserves the colimit presentation by skeleta as a
  CW-filtration, and no theorem identifying `|X.skeleton n|` with a subspace of `|X|`.
* Realization does commute with skeleta only in the weak categorical sense that
  `SSet.toTop` is a left adjoint (`sSetTopAdj`) and hence preserves colimits; but the pinned
  library contains no statement that `X.skeleton (n+1)` is the pushout of
  `∂Δ[n] ⟶ Δ[n]` cells along `X.skeleton n` (this is an explicit `TODO` in
  `Mathlib/AlgebraicTopology/SimplicialSet/Skeleton.lean`, attributed to the file's author).

Therefore: **the topological pair `(|K^{(r)}|, |K^{(r-1)}|)` exists as a pair of spaces with a
map, and nothing more is theorem-level available.** No CW structure on `|K|` is assumed
anywhere in this project, and none is available: the pin's CW-complex theory
(`Topology.CWComplex`, `Topology.RelCWComplex`, ~247 declarations) is never connected to
`SSet.toTop`, and carries **no homology theory at all** (§2.5).

Classification: `SKELETAL_PAIR` = `PARTIAL` (spaces and map: yes; subspace pair / CW pair:
`MISSING`).

---

## 9. WP9 — the standard cell pair

Target: `H_q^{sing}(|Δ[r]|, |∂Δ[r]|; ℤ₂) = ℤ₂` for `q = r`, `0` otherwise.

Route audit in the pin:

| route | first missing ingredient |
| --- | --- |
| relative homology of the disk/sphere pair | there is **no relative singular homology** in the pin at all (§10) |
| excision | **no excision** (0 declarations) |
| long exact sequence of the pair + contractibility of `\|Δ[r]\|` + `H_*(\|∂Δ[r]\|)` | the algebraic LES is available (§7), contractibility of `\|Δ[n]\|` is already proved in this project (`SpineTask12.realization_stdSimplex_contractible`), but `H_*(\|∂Δ[r]\|;ℤ₂) ≅ H_*(S^{r-1})` is **not** available: the pin has no computation of the singular homology of spheres, and no identification of `\|∂Δ[r]\|` with a sphere |
| quotient theorem `\|Δ[r]\|/\|∂Δ[r]\| ≃ S^r` | quotient exists topologically, but the relative-homology comparison theorem for good pairs is absent |
| cellular homology | absent (`cellular` : 0 declarations) |

**Shortest pinned route: none. `CELL_PAIR` = `BLOCKED`.**

The cheapest *native* route would be: define relative singular chains as a quotient (cheap);
obtain the LES from `HomologySequence.snakeInput` (cheap); then one still needs
`H_*(S^{r-1};ℤ₂)`, i.e. essentially a full development of excision or of a Mayer–Vietoris
argument for the singular theory. That is the real cost, and it is large.

Answer to Final Question 4: **the exact singular relative theorem corresponding to one attached
`r`-simplex is `H_q(|Δ[r]|, |∂Δ[r]|;ℤ₂) ≅ ℤ₂` for `q = r` and `0` otherwise (together with the
excision statement that lets these summands be assembled). Neither half exists in the pin.**

---

## 10. WP10 — relative singular homology and LES audit

### 10.1 What the pin has

* `AlgebraicTopology.singularChainComplexFunctor`, `AlgebraicTopology.singularHomologyFunctor`
  — absolute singular homology of a space, defined through `TopCat.toSSet` and the free
  simplicial abelian group. Two corollaries only (totally disconnected spaces).
* `HomologicalComplex.HomologySequence.*` — the LES of a short exact sequence of complexes,
  with connecting morphism and naturality (`PINNED_ADAPTABLE` for pairs, once relative chains
  are constructed by hand).
* `CategoryTheory.ShortComplex.SnakeInput` — the snake lemma machinery underneath.

### 10.2 What the pin does **not** have

* relative singular chain complexes / relative singular homology of a pair: **absent**;
* excision: **absent** (0 declarations matching `excision`);
* homotopy invariance of `singularHomologyFunctor`: **absent** (the project has its own
  cochain-level homotopy invariance, `Mod2Cohomology`, which is what Task 12 used);
* good-pair / cofibration infrastructure for singular homology: **absent**;
* Mayer–Vietoris for singular homology: **absent** (all 85 `MayerVietoris` declarations are
  sheaf-theoretic).

### 10.3 Cell attachment (WP11)

There is **no** Lean-level representation in the pin of "`|K^{(r)}|` is obtained from
`|K^{(r-1)}|` by attaching one `r`-cell per nondegenerate `r`-simplex":

* the simplicial statement (`X.skeleton (n+1)` is a pushout of `∂Δ[n] ⟶ Δ[n]` cells) is an
  explicit `TODO` in the pinned `Skeleton.lean`;
* even given it, transporting it through `SSet.toTop` and converting the pushout into a
  direct-sum decomposition of relative homology needs excision, which is absent.

No direct-sum decomposition is asserted anywhere in this project.

**Classification: `RELATIVE_SINGULAR_PARTIAL` (chains constructible, LES adaptable) +
`EXCISION_MISSING` (hard blocker). `LES_MISSING` is *not* the right label — the algebraic LES
is available.**

Answer to Final Question 5: **no. The pin has enough homological algebra for the LES of a pair,
but no excision and no relative singular homology, so the one-step skeletal comparison cannot
be proved.**

---

## 11. WP16/WP17/WP18 — the algebraic bridge and the decision

### 11.1 The exact algebraic theorem needed

> For chain complexes of `ℤ₂`-vector spaces, a quasi-isomorphism is a chain-homotopy
> equivalence.

### 11.2 Pin status

* Statement itself: **absent** (`homotopyEquivOfQuasiIso` : 0 declarations).
* Derivable from pinned machinery: `CochainComplex.isKProjective_of_projective` (a complex of
  projectives, strictly bounded above, is K-projective), `HomotopyEquiv.isKProjective`,
  `CochainComplex.IsKProjective.Qh_map_bijective` (for K-projective `K`, the functor from the
  homotopy category to the derived category is **bijective** on morphisms out of `K`), plus
  `HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso`. Free `ℤ₂`-modules — which is
  what every chain module in this project is — are projective (probe
  `SpineTask13.probeFreeProjective`). Both `probeIsKProjective` and `probeQhBijective` compile
  in `Task13PinAudit.lean`.
* Cost of the adaptation: reindex the project's `ℕ`-graded `Finsupp` complexes as
  `CochainComplex (ModuleCat ℤ₂) ℤ` objects that are `IsStrictlyLE 0`, supply
  `HasDerivedCategory`, run the two bijectivity statements, and read the homotopy inverse back
  off as explicit linear maps to populate `NerveGeom.ChainHomotopyEquivData`. Estimated: one
  module, no new mathematics.

**Classification: `PINNED_ADAPTABLE` (equivalently `SMALL_ALGEBRAIC_PROOF` in the task's
scheme — it is not `PINNED_DIRECT`, and it is not `MAJOR_HOMOLOGICAL_ALGEBRA`).**

### 11.3 WP17 — the direct-cohomology alternative

Running the skeletal comparison on cochains instead would need: relative singular **cohomology**
of the pairs `(|K^{(r)}|,|K^{(r-1)}|)`, its long exact sequence, and the cellular cochain
computation. The pin has none of the topological ingredients (§9, §10) — they are the *same*
missing ingredients as on the chain side, plus a dualisation step. The project already owns the
dualisation step in the *other* direction (Task 10: `NerveGeom.dualOf`,
`geometricHmap_bijective_of_chainHomotopyEquiv`), so Bridge B duplicates work without removing
any blocker.

**Bridge B is strictly more expensive. Not implemented.**

### 11.4 WP18 — decision

> **Selected: Bridge A.**
> `J` quasi-iso ⇒ (K-projective route, `PINNED_ADAPTABLE`) `J` chain-homotopy equivalence ⇒
> (Task 10, already `DERIVED`) `geometricHmap` bijective.

This is the route decision. It is **not** a claim that the bridge has been traversed: its
premise (`J` quasi-iso) is `BLOCKED` upstream at excision (§9, §10), and Task 13 does not
implement the K-projective adaptation, because there is nothing yet to feed it.

Answers to Final Questions 9 and 10: **pinned Mathlib does not prove "quasi-isomorphism over
`ℤ₂` ⇒ chain-homotopy equivalence"; it does contain the K-projective machinery from which it
follows, and that adaptation is smaller than a direct cohomological skeletal comparison
(which needs the same missing topology plus a dualisation).**

---

## 12. WP12/WP13 — the canonical relative comparison map, and the one-step theorem

**WP12, proved.** `J` respects the whole degeneracy layer and descends:

| theorem | statement |
| --- | --- |
| `chainMap_degen_mem` | `J(D_q(K)) ⊆ D_q(Sing\|K\|)` |
| `normJ` | the normalized comparison, defined as `normMap η_K` — the *same* canonical map |
| `normJ_normProj` | `p ∘ J = normJ ∘ p` |
| `normJ_comm` | `normJ` is a chain map for `∂̄` |

`J` also respects skeleta: for any subcomplex inclusion `A ⟶ X` the square of §5.2 commutes,
and `η` is natural, so `J` restricted to `K^{(r)}` is `C_*(η_{K^{(r)}})`. No abstract relative
isomorphism is substituted anywhere.

**WP13, blocked.** The one-skeleton-step comparison
`H_q(J_r^{rel}) : H_q(N_*(K^{(r)},K^{(r-1)})) → H_q^{sing}(|K^{(r)}|,|K^{(r-1)}|)` cannot be
proved: the left-hand side is now computed (§6), the right-hand side does not exist in the pin
(§10), and the comparison would need the cell-attachment decomposition (§10.3) and excision
(§9). **Stop here, per WP21.** The exact first missing theorem is stated in §14.

Answer to Final Question 6: **yes — the relative comparison is induced by the actual canonical
`J = C_*(η_K)`, through `normJ = normMap η_K` and `normJ_normProj`; nothing was substituted.**

Answer to Final Question 7: **no. A five-lemma propagation cannot even be started: one of the
two long exact sequences (the singular one) does not exist in the pin, and the pin has no
five-lemma theorem either.**

---

## 13. WP14/WP15/WP19 — scope actually reached

| claim | scope | status |
| --- | --- | --- |
| `C_*^{simp,unn}(S) ≃_ch N_*(S)`, naturally in `S` | **arbitrary simplicial set** | `PROVED` |
| `N_q(S) ≅ ℤ₂⟨NDeg_q(S)⟩` | arbitrary `S` | `PROVED` |
| `N_q(K^{(r)},K^{(r-1)}) = 0` for `q ≠ r`, free on `NDeg_r` for `q = r` | arbitrary `S`, every `r` | `PROVED` |
| `H_q(J_r^{rel})` iso (one skeleton step) | — | `BLOCKED` |
| `H_q(J|_{K^{(r)}})` iso (finite skeletal) | — | `BLOCKED` |
| `H_q(J)` iso for `dim K ≤ r` (finite-dimensional) | — | `BLOCKED` |
| `H_q(J)` iso for arbitrary `K` | — | `BLOCKED` |

**Scope classification: `FINITE_SKELETON_ONLY` is *not* reached either.** The strongest scope
reached is: **the simplicial (algebraic) side of one skeleton step, for arbitrary `K`** —
i.e. normalization and the relative normalized computation, with no comparison to singular
homology at any scope. Per WP19 nothing is claimed about `H_*^{simp}(K) ≅ H_*^{sing}(|K|)`, at
any scope, and the infinite-dimensional passage was not attempted.

**WP20: blocked.** The conditional `GeometricComparison` assumption is *not* removed; the
Spin-lift class on `|N(𝓤)|` remains conditional exactly as Task 10 left it. The nerve theorem
was not invoked; `w₂` was not invoked; `GeometricComparison` was not consumed.

Answer to Final Question 8: **the strongest scope reached is the simplicial side of one
skeleton step (for arbitrary `K`), not the comparison at one skeleton step, not
finite-dimensional `K`, and not arbitrary `K`.**

---

## 14. The exact remaining blocker, with its dependency cone

### 14.1 First missing theorem (hard blocker)

> **Excision for singular homology.** For a space `X`, subsets `Z ⊆ A ⊆ X` with
> `closure Z ⊆ interior A`, the inclusion `(X∖Z, A∖Z) ↪ (X,A)` induces an isomorphism on
> relative singular homology.

Nothing of this exists in the pin (0 declarations matching `excision`). Its dependency cone as
it would have to be built:

```
relative singular chain complex of a pair                (native, cheap)
   └── LES of a pair            ← HomologicalComplex.HomologySequence.*   (PINNED_ADAPTABLE)
   └── barycentric subdivision operator on singular chains (MISSING, large)
        └── small-simplices theorem  (MISSING, large)
             └── EXCISION            (MISSING)
                  └── H_*(|Δ[r]|,|∂Δ[r]|;ℤ₂)        (MISSING)  ← WP9
                  └── cell-attachment decomposition (MISSING)  ← WP11
                       ├── needs: X.skeleton (n+1) is a pushout of ∂Δ[n] ⟶ Δ[n]
                       │          (explicit TODO in pinned SSet/Skeleton.lean)
                       └── needs: SSet.toTop preserves that pushout as a *topological* pair
                                  (MISSING: no CW structure on |X| in the pin)
                            └── H_q(J_r^{rel}) iso                    ← WP13
                                 └── skeletal induction (also needs a five lemma: MISSING)
                                      └── J quasi-iso
                                           └── Bridge A (PINNED_ADAPTABLE)
                                                └── geometricHmap bijective
```

### 14.2 Second, much smaller, missing item (simplicial side)

> **Naturality of `AlgebraicTopology.DoldKan.homotopyPInftyToId`.** For `f : X ⟶ Y`,
> `K[f] ∘ (homotopyPInftyToId X).hom q (q+1) = (homotopyPInftyToId Y).hom q (q+1) ∘ K[f]`.

This is the only gap on the simplicial side (§5.3). It is not on the critical path of the
blocker above.

No blocker is hidden behind a new `Spec`, a structure field, an assumed equivalence or an
abstract comparison isomorphism: Task 13 introduced **no** new `Prop`-valued assumption, **no**
new structure with a comparison field, and consumed none of the existing ones.

---

## 15. WP22 — the certification DAG, with realized status

```
J = C_*(η_K)                                                  PINNED_MATHLIB + DERIVED
  │      (NerveGeom.chainMap = sSetChainMap η_K, Task 10)
  ▼
C_*^{unn}(K) ≃_ch N_*(K)                                      DERIVED   (Task 13, §4)
  │      p i = id, i p ≃ id, natural in K
  ▼
N_*(K^{(r)}, K^{(r-1)})                                       DERIVED   (Task 13, §6)
  │      = 0 for q ≠ r; free on NDeg_r(K) for q = r
  ║
  ║  ‖  C_*^{sing}(|K^{(r)}|, |K^{(r-1)}|)                    BLOCKED   (§10: no relative
  ║  ‖                                                                  singular homology,
  ║  ‖                                                                  no excision)
  ▼
H_*(J_r^{rel}) iso                                            BLOCKED   (§12, WP13)
  ▼
H_*(J|_{K^{(r)}}) iso                                         BLOCKED   (§13; also needs a
  ▼                                                                     five lemma: MISSING)
J quasi-iso                                                   BLOCKED
  ▼
J chain-homotopy equivalence                                  CONDITIONAL / PINNED_ADAPTABLE
  │      (Bridge A, K-projective route, §11)                  — adaptation not implemented
  ▼
geometricHmap bijective                                       CONDITIONAL
         (Task 10: geometricHmap_bijective_of_chainHomotopyEquiv — DERIVED, given the datum)
```

Side edges proved by Task 13:

```
J(D_q(K)) ⊆ D_q(Sing|K|)          DERIVED   (chainMap_degen_mem)
p ∘ J = normJ ∘ p                 DERIVED   (normJ_normProj)
C_*(K^{(r-1)}) → C_*(K^{(r)}) compatible with p, i   DERIVED (normProj_natural, normInc_natural)
pʳᵉˡ ∘ iʳᵉˡ = id                  DERIVED   (relNormProj_comp_relNormInc)
iʳᵉˡ ∘ pʳᵉˡ ≃ id                  DEFERRED  (§5.3, §14.2)
|K^{(r-1)}| → |K^{(r)}| as a pair of spaces   PINNED_MATHLIB (map only; subspace/CW: BLOCKED)
```

---

## 16. Verification evidence

### 16.1 Builds (all green, in this order)

```
lake build RequestProject.Spine.Nerve.Core          → Build completed successfully (8134 jobs)
lake build RequestProject.Spine.Cohomology.Core     → Build completed successfully (8065 jobs)
lake build RequestProject.Spine.Cech.Core           → Build completed successfully (8111 jobs)
lake build RequestProject.Spine.GoodCover.Core      → Build completed successfully (8124 jobs)
lake build RequestProject.Spine.Geometry.Core       → Build completed successfully (8088 jobs)
lake build RequestProject.Spine.Core                → Build completed successfully (8189 jobs)
lake build RequestProject.Spine.Audit.Firewall      → SPINE FIREWALL AUDIT: all checks passed
lake build                                          → Build completed successfully (8207 jobs)

lake build RequestProject.Spine.Nerve.Task13Normalization   → success
lake build RequestProject.Spine.Nerve.Task13Skeletal        → success
lake build RequestProject.Spine.Nerve.Task13CanonicalMap    → success
lake build RequestProject.Spine.Nerve.Task13PinAudit        → success
```

Firewall output, unchanged from before Task 13:

```
Spine external-project imports: 0 (prefixes checked: 7)
endpoint RequestProject.Spine.Core: direct legacy imports E1 = 0, E2 = 0,
                                    transitive legacy imports E1 = 0, E2 = 0
```

i.e. Experiment1 direct = 0, Experiment1 transitive = 0, Experiment2 direct = 0,
Experiment2 transitive = 0, external-project imports = 0.

A `rg` search for `sorry`, `admit`, `axiom`, `unsafe`, `partial`, `implemented_by` over the four
new modules returns nothing.

### 16.2 Axiom audit

`#print axioms` is run inside `Task13PinAudit.lean` for every principal Task-13 declaration:
`afmc_d_hom`, `degenSubmodule`, `boundary_degen_mem`, `degenSubmodule_eq_supported`,
`normBoundary`, `normBoundary_comp_normBoundary`, `normProj_comm`, `normInc_comm`,
`normProj_comp_normInc`, `normInc_comp_normProj`, `normHtpy_zero`, `normHtpy_succ`,
`normProj_natural`, `normInc_natural`, `normMap_comm`, `normChainEquiv`,
`degenerate_of_mem_skeleton`, `normChain_skeleton_subsingleton`,
`relNormChain_subsingleton_of_lt`, `relNormChain_subsingleton_of_gt`, `relNormProj`,
`relNormInc`, `relNormProj_comp_relNormInc`, `relNormChainEquiv`, `nonDegenerateSkeletonEquiv`,
`normJ`, `normJ_normProj`, `normJ_comm`, `chainMap_degen_mem`.

Every one reports exactly

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

— the three standard Lean axioms, and nothing else.

---

## 17. Endpoint classification

| endpoint | verdict |
| --- | --- |
| `NORMALIZATION` | **`NORMALIZATION_CHAIN_EQUIV`** — proved, natural, for arbitrary simplicial sets |
| `DEGENERACY_CONTROL` | **achieved** — `D` defined, `∂D ⊆ D`, `D` = chains supported on degenerate simplices |
| `RELATIVE_NORMALIZATION` | **partial** — relative maps and `pʳᵉˡ iʳᵉˡ = id` proved; `iʳᵉˡ pʳᵉˡ ≃ id` `DEFERRED` |
| `SKELETAL_PAIR` | **partial** — simplicial pair fully available; realized pair only as a map of spaces |
| `RELATIVE_SIMPLICIAL` | **achieved** — `N_q(K^{(r)},K^{(r-1)})` computed in every degree |
| `RELATIVE_SINGULAR` | `RELATIVE_SINGULAR_PARTIAL` — chains constructible, LES adaptable, theory absent |
| `CELL_PAIR` | `BLOCKED` |
| `EXCISION` | `EXCISION_MISSING` — **the first missing theorem** |
| `RELATIVE_COMPARISON` | `BLOCKED` (map exists and is canonical; isomorphism unprovable in the pin) |
| `SKELETAL_INDUCTION` | `BLOCKED` (also `five lemma MISSING`) |
| `QUASI_ISOMORPHISM` | `BLOCKED` |
| `CHAIN_HOMOTOPY_EQUIVALENCE` | `CONDITIONAL` — Bridge A, `PINNED_ADAPTABLE` |
| `COHOMOLOGY_BRIDGE` | `CONDITIONAL` — Task 10's `geometricHmap_bijective_of_chainHomotopyEquiv` is already proved |
| `FINITE_ONLY` | not reached |
| `BLOCKED` | see §14 |
| `DEFERRED` | naturality of `homotopyPInftyToId`; infinite-dimensional passage |
| `NEGATIVE_RESULT` | none — nothing was refuted in Task 13 |

**Final answer to the last Final Question.** `NerveGeom.geometricHmap_{K,n}` has **not** become
unconditionally bijective. The exact theorem that still prevents it, in the order it is needed:
**excision for singular homology** (and, immediately downstream of it,
`H_q(|Δ[r]|,|∂Δ[r]|;ℤ₂)` and the cell-attachment decomposition of `|K^{(r)}|` over
`|K^{(r-1)}|`). Everything between that theorem and the conclusion is now either proved here
(normalization, degeneracy control, the relative normalized skeletal computation, the descent
of the canonical `J`), pinned-adaptable (Bridge A), or already derived in the project
(Task 10's dualisation theorem).
