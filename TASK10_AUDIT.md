# TASK 10 — Canonical Geometric Comparison and Unit Homology Equivalence

Source hypothesis paper: **Relational Spin-Closure Hypothesis — Nakahara-revised, 8 September 2026**
(`Relational_Spin_Closure_Hypothesis_2026-09-08.pdf`).

Pinned environment: `leanprover/lean4:v4.28.0`, `mathlib` at tag `v4.28.0`
(`lake-manifest.json`; commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).

**Overall classification of Task 10: `NEGATIVE_RESULT` for the unconditional comparison
theorem, with a genuine `CHAIN_IDENTIFICATION` + `COHOMOLOGY_ISOMORPHISM`-reduction obtained
along the way, and a `DERIVED_NATIVE` correction of the Task-4/Task-9 assumption status.**

Task 10 does **not** prove that `NerveGeom.geometricHmap 𝓤 n` is bijective.  It does prove
that the only thing still missing is one chain-level statement, and it removes every
cohomological, dualisation and coefficient-theoretic step from the gap.

---

## 0. Summary table of endpoints

| item | classification |
| --- | --- |
| WP0 correction of the Task-4/Task-9 global-assumption status | `DERIVED_NATIVE` |
| WP1 pinned-Mathlib v4.28.0 capability audit | see §2 |
| WP2 `chainMap` = `C_*(η_K)` | `CHAIN_IDENTIFICATION` |
| WP3 bridge to Mathlib's `SSet.singularChainComplexFunctor` | `DEFERRED` (see §4) |
| WP4 Dold–Kan contribution | `NO_NET_SHORTENING` |
| WP5 exact remaining theorem | `NerveGeom.ChainComparisonStatement` |
| WP6 route matrix | see §6 — all routes rejected |
| WP7 preferred construction | chain-homotopy equivalence; datum *specified*, not built |
| WP9 degree-two scope test | `NO_MEANINGFUL_REDUCTION` |
| WP10 chains ⟹ existing cohomology map | `COHOMOLOGY_ISOMORPHISM` (conditional, proved) |
| WP11 elimination of `GeometricComparison` | `SUPERSEDED` as an *input*, not eliminated |
| unconditional realised Spin-lift class | `BLOCKED` |
| WP12 nerve theorem | `DEFERRED` (untouched, as mandated) |

---

## 1. WP0 — corrected Task-4 global-assumption status

### 1.1 What Task 4 actually assumes

```
[TopologicalSpace M] [ChartedSpace LorentzCarrier M]   (+ [IsManifold carrierModel ⊤ M])
```

with `SpinCore.LorentzCarrier = ℝ × (Fin 3 → ℝ)`.  Nothing else.

### 1.2 The incorrect Task-9 statement

`RequestProject/Spine/Nerve/ComparisonSpec.lean`, docstring of `NerveTheoremStatement`, said:

> Derivability in the Task-4 manifold model: `hopen`, `hcover` and `hparacompact` are available
> (a manifold charted on a finite-dimensional normed space is locally compact, second countable
> in the Task-4 model, hence paracompact) …
>
> Hausdorffness is **not** needed for the statement, but is available in the Task-4 model.

Both claims are false.  They have been **withdrawn** and replaced in that docstring, and this
audit records the correction.

### 1.3 Corrected status

| property | assumed by Task 4 | derived in the project | comment |
| --- | --- | --- | --- |
| Hausdorffness (`T2Space`) | no | **no** | classical counterexample: line with two origins (not formalised here) |
| second countability | no | **no**, and *refuted* | see §1.4 |
| paracompactness | no | **no** | classical counterexample: Prüfer surface (not formalised here) |
| metrisability | no | **no** | follows from the above |
| numerability of an arbitrary open cover | no | **no** | needs paracompactness |
| existence of a good cover | no | **no** | Task 7: needs the Riemannian convexity input, absent |

For the future nerve theorem the two lists are now kept apart explicitly, in the corrected
docstring of `NerveGeom.NerveTheoremStatement`:

* *hypotheses required by the theorem*: open cover, covering, paracompactness (numerability),
  good cover;
* *hypotheses currently derived in the project*: **none of those**, beyond what is supplied by
  hypothesis in the statement itself.

Nothing has been added to Task 4.

### 1.4 The correction is machine-checked

`RequestProject/Spine/Nerve/ManifoldAssumptionAudit.lean`:

* `SpineTask10.chartedSigma` — the disjoint union of `ι` copies of a model space `H` is
  charted on `H`;
* `SpineTask10.isManifoldSigma` — and is a `C^n` manifold for any model with corners on `H`
  (chart transitions are the identity, or have empty source);
* `SpineTask10.not_secondCountable_sigma` — with `ι` uncountable it is not second countable
  (a countable dense set would have to meet uncountably many disjoint open pieces);
* `SpineTask10.BigChartedSpace := Σ _ : ℝ, LorentzCarrier`, with instances
  `ChartedSpace LorentzCarrier` and `IsManifold carrierModel ⊤`;
* `SpineTask10.chartedNotSecondCountable` — it is not second countable;
* `SpineTask10.not_secondCountable_of_charted` — hence "charted on the Task-4 carrier ⟹ second
  countable" is false.

Since second countability is exactly the step by which the Task-9 docstring reached
paracompactness, that inference is destroyed at the root.

The corresponding statement of the Task-9 audit is corrected in `TASK09_AUDIT.md`
(appended correction section) and in `DEPENDENCY_DAG.md`.

---

## 2. WP1 — capability audit of pinned Mathlib v4.28.0

Audited by reading `.lake/packages/mathlib/Mathlib/**` directly.  No online documentation was
used to decide availability.

### 2.1 Modules explicitly requested

| module | status | notes |
| --- | --- | --- |
| `Mathlib.AlgebraicTopology.SingularSet` | `PINNED_AVAILABLE` | `TopCat.toSSet`, `SSet.toTop`, `sSetTopAdj`, `SSet.toTopSimplex`, `SSet.toTop.IsLeftKanExtension` |
| `Mathlib.AlgebraicTopology.TopologicalSimplex` | `PINNED_AVAILABLE` | `SimplexCategory.toTop`, `SimplexCategory.toTopObj` |
| `Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic` | `NOT_AVAILABLE` | no such file; there is **no** `SSet.homology` in v4.28.0 |
| `Mathlib.AlgebraicTopology.SingularHomology.Basic` | `PINNED_PARTIAL` | see §2.2 |
| `Mathlib.AlgebraicTopology.AlternatingFaceMapComplex` | `PINNED_AVAILABLE` | `AlgebraicTopology.alternatingFaceMapComplex` |
| `Mathlib.AlgebraicTopology.MooreComplex` | `PINNED_AVAILABLE` | `AlgebraicTopology.normalizedMooreComplex`, `inclusionOfMooreComplexMap` |
| `Mathlib.AlgebraicTopology.DoldKan.Normalized` | `PINNED_AVAILABLE` | `PInftyToNormalizedMooreComplex`, `N₁_iso_normalizedMooreComplex_comp_toKaroubi` |
| `Mathlib.AlgebraicTopology.DoldKan.Equivalence` | `PINNED_AVAILABLE` | `CategoryTheory.Abelian.DoldKan.equivalence : SimplicialObject A ≌ ChainComplex A ℕ` (abelian `A`) |
| `Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy` | `NOT_AVAILABLE` | no such file (`SimplicialObject/` contains `Basic`, `Coskeletal`, `II`, `Op`, `Split`) |
| `Mathlib.AlgebraicTopology.ExtraDegeneracy` | `PINNED_AVAILABLE` | `SimplicialObject.Augmented.ExtraDegeneracy`, `ExtraDegeneracy.homotopyEquiv`, `SimplexCategory.extraDegeneracy` (for the augmented standard simplex) |
| `Mathlib.AlgebraicTopology.SimplicialSet.Subdivision` | `NOT_AVAILABLE` | no subdivision, no `Sd`, no simplicial-approximation API anywhere in v4.28.0 |
| `Mathlib.AlgebraicTopology.EilenbergSteenrod` | `NOT_AVAILABLE` | no such file; no axioms, and no uniqueness theorem |

### 2.2 `SingularHomology/Basic.lean` in detail

95 lines, author Andrew Yang, 2025.  Exactly the following declarations exist:

```
AlgebraicTopology.SSet.singularChainComplexFunctor        : C ⥤ SSet ⥤ ChainComplex C ℕ
AlgebraicTopology.singularChainComplexFunctor             : C ⥤ TopCat ⥤ ChainComplex C ℕ
AlgebraicTopology.singularHomologyFunctor                 : C ⥤ TopCat ⥤ C
AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
AlgebraicTopology.singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace
AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace
```

So: definitions plus **one** computation, for totally disconnected spaces.  There is
**no** homotopy invariance, **no** excision, **no** Mayer–Vietoris, **no** long exact sequence
of a pair, **no** dimension axiom beyond the totally disconnected case, and **no** comparison
with simplicial homology.

### 2.3 Other relevant components

| component | status | notes |
| --- | --- | --- |
| singular excision | `NOT_AVAILABLE` | the string `excision` does not occur anywhere in `Mathlib/` |
| Mayer–Vietoris for singular homology | `NOT_AVAILABLE` | the three `MayerVietoris` files are about sheaves/sites, `IRRELEVANT_TO_COMPARISON` |
| relative singular homology / homology of a pair | `NOT_AVAILABLE` | |
| acyclic models | `NOT_AVAILABLE` | |
| CW complexes / cellular chain complex | `NOT_AVAILABLE` | `AlgebraicTopology/RelativeCellComplex/` provides `RelativeCellComplex`, `AttachCells` — a *transfinite-composition* bookkeeping structure with **no** homology attached; `IRRELEVANT_TO_COMPARISON` in its present form |
| model-category API | `PINNED_PARTIAL` | `AlgebraicTopology/ModelCategory/**` defines `ModelCategory`, weak equivalences, cylinders, Brown's lemma, homotopy relations |
| `ModelCategory SSet` (Kan–Quillen) | `NOT_AVAILABLE` | no instance; the only `ModelCategory` instances in v4.28.0 are `Cᵒᵖ` and `Over S` |
| `ModelCategory TopCat` (Serre/Quillen) | `NOT_AVAILABLE` | no instance |
| `sSetTopAdj` a Quillen equivalence | `NOT_AVAILABLE` | `Mathlib/AlgebraicTopology/SingularSet.lean:37` lists it as an explicit **TODO** |
| `SSet.Skeleton`, `SSet.Degenerate`, `SSet.NonDegenerateSimplices` | `PINNED_AVAILABLE` | combinatorial only; no statement relating skeleta to `SSet.toTop` |
| `SSet.toTop` preserves colimits / cell structure of `|S|` | `NOT_AVAILABLE` | only the left-Kan-extension characterisation |
| project-native singular homotopy invariance | `DERIVED_NATIVE` (Task 8) | `Mod2Cohomology.Hmap_eq_of_homotopy`, `homotopyEquivCohomology`, `cohomology_succ_eq_zero_of_contractible` — cochain level, with an explicit prism operator |

The last line matters: the *cochain-level* homotopy invariance that a comparison proof needs
does exist, but **only in the project**, and only in the form "homotopic maps induce equal maps
on cohomology", not as a natural chain homotopy usable as an acyclic-carrier input.

---

## 3. WP2 — the Task-9 chain map is the linearised adjunction unit

`RequestProject/Spine/Nerve/UnitChainMap.lean`.

One construction, the free `ℤ₂`-linearisation of a simplicial set:

```
SSetChain    S n = Sₙ →₀ ℤ₂
sSetBoundary S n = ∑ᵢ (dᵢ)_*
sSetChainMap φ n = (φₙ)_*
```

Theorems:

| statement | Lean name | proof |
| --- | --- | --- |
| linearisation is a chain-complex functor | `sSetBoundary_naturality` | naturality of `φ` |
| `∂^simp` of Task 9 is the linearised boundary of `N(𝓤)` | `simpBoundary_eq` | `rfl` |
| `∂^sing` of Task 9 is the linearised boundary of `Sing|N(𝓤)|` | `singBoundary_eq` | `rfl` |
| **`J = C_*(η_K)`** | `chainMap_eq_unitChainMap` | `rfl` |
| Task-9 `chainMap_comm` is naturality of `η` | `chainMap_comm_of_unit` | `sSetBoundary_naturality` |

The identification is **definitional**: the carriers are literally the same types
(`SimpChain U n = Nerve U n →₀ ℤ₂ = (coverNerveSSet U).obj [n]ᵒᵖ →₀ ℤ₂`, and
`SingChain (|N(𝓤)|) n = Mod2Cohomology.Simplex _ n →₀ ℤ₂ = (TopCat.toSSet.obj |N(𝓤)|).obj [n]ᵒᵖ →₀ ℤ₂`),
so no commuting square with chosen equivalences is needed.  Classification:
**`CHAIN_IDENTIFICATION`.**

---

## 4. WP3 — bridge to Mathlib's chain complexes

`SSet.singularChainComplexFunctor` and `singularChainComplexFunctor` exist (§2.2);
`SSet.homology` and `AlgebraicTopology.singularHomologyFunctor`'s simplicial counterpart do not.

The Mathlib complexes are built from `sigmaConst` (categorical coproducts in `C`) composed with
`alternatingFaceMapComplex`, i.e. with the **signed** differential `∑ (-1)ⁱ dᵢ`.  With
`C = ModuleCat (ZMod 2)` and coefficient object `ZMod 2` they are degreewise isomorphic to the
project's `Finsupp` chain modules, and the signs collapse because `-1 = 1` in `ZMod 2`
(the project already records that collapse as a theorem in
`RequestProject/Spine/Cohomology/CharTwo.lean`).

Status: **`DEFERRED`.**  The bridge is constructible but was *not* built, for a reason that is
recorded rather than hidden: it buys nothing for Task 10.  The missing theorem (§5) is not
available on the Mathlib side either — `SSet.singularChainComplexFunctor` carries no comparison
theorem at all — so a bridge would only add a second presentation of the same complexes,
against the WP3 instruction not to introduce a parallel theory.  The one thing a bridge could
have supplied, Dold–Kan normalisation, is shown in §5 not to shorten the proof.

What *was* built instead is the honest minimum: the project's own chain complexes are shown
(§3) to be the free linearisation of the two relevant simplicial sets, which is exactly the
input any Mathlib bridge would have to reproduce.

---

## 5. WP4 — Dold–Kan contribution

Pinned Mathlib contains the full Dold–Kan package for a **preadditive/idempotent-complete**,
resp. **abelian**, target category: `CategoryTheory.Abelian.DoldKan.equivalence`,
`PInftyToNormalizedMooreComplex`, `N₁_iso_normalizedMooreComplex_comp_toKaroubi`, and the
`DoldKan.Decomposition` / `Degeneracies` splitting of the degenerate part.

Exact usable consequence for this project: with `A = ModuleCat (ZMod 2)`, the natural map
from the unnormalized alternating-face complex of a simplicial `ℤ₂`-module to its normalized
Moore complex is a quasi-isomorphism (indeed a chain-homotopy equivalence, via `PInfty`), so
homology may be computed with either.

Why this does not help here:

1. **The project does not need it.**  Task 9 WP3 already established that the Čech complex of
   the Spine is the *unnormalized* one on the nose
   (`NerveGeom.underlyingPresimplicial_coverNerveSSet`, `cochain_eq`, `d_eq`, `cocycles_eq`,
   `coboundaries_eq`, `cechCohomologyEquivSSet`).  Both sides of the comparison —
   simplicial and singular — are unnormalized, so no normalisation step occurs anywhere in the
   statement `geometricHmap` is about.
2. **The missing theorem is topological, not algebraic.**  Dold–Kan is an equivalence between
   simplicial objects and chain complexes in a *fixed* abelian category.  It says nothing about
   the functor `S ↦ Sing|S|`, which is where the entire content of the comparison lives.
   Normalising both sides replaces one unknown quasi-isomorphism question by an isomorphic
   unknown quasi-isomorphism question.
3. **The degenerate-splitting route (Route C below) stalls at the same place.**  Knowing that
   `C_*^simp(K)` splits as normalized ⊕ degenerate does not identify the singular chains of
   `|K|`; one still needs the cell structure of `|K|`, which pinned Mathlib does not expose.

Classification: **`NO_NET_SHORTENING`** (it would be `USEFUL_NORMALIZATION_ONLY` if the Spine
had used the normalized convention; it does not).

Explicitly, and as mandated: *Dold–Kan alone does not prove that `K → Sing|K|` is a homology
equivalence*, and Task 10 is not marked solved on the strength of any normalisation result.

---

## 6. WP6 — route matrix

Common notation: `K = N(𝓤) = NerveGeom.coverNerveSSet 𝓤`, `|K| = SSet.toTop.obj K`,
`η_K : K ⟶ TopCat.toSSet.obj |K|`, `J = C_*(η_K) = NerveGeom.chainMap 𝓤`.

### Route A — an existing pinned theorem about `K → Sing|K|`

* available prerequisites: `sSetTopAdj`, the unit, `SSet.toTop.IsLeftKanExtension`.
* missing prerequisites: any statement that `η_K` is a weak equivalence, a homology
  equivalence, or induces an isomorphism on any homology theory.  `SSet.homology` does not
  exist; `singularHomologyFunctor` has no comparison theorem; there is no `ModelCategory SSet`
  instance and Mathlib's own file lists the Quillen equivalence as unfinished.
* estimated proof DAG: n/a.
* reaches `geometricHmap`: would, if it existed.
* parallel theory: no.
* **rejected — the theorem is not in v4.28.0.**

### Route B — simplicial homology functor + singular homology functor

* available: `AlgebraicTopology.SSet.singularChainComplexFunctor`,
  `AlgebraicTopology.singularHomologyFunctor`, `alternatingFaceMapComplex`.
* missing: a simplicial-homology functor on `SSet` (`SSet.homology` absent), and any theorem
  identifying the map induced by `η_K`.  The functors are definitions only; the sole computation
  in the file is for totally disconnected spaces, which `|K|` is not.
* estimated DAG: identical to Route A after the bridge.
* reaches `geometricHmap`: only via the bridge of §4, and then it still needs Route A's
  missing theorem.
* parallel theory: yes, if the bridge is built without a use for it.
* **rejected.**

### Route C — Dold–Kan / degenerate splitting

* available: full Dold–Kan for abelian targets, `DoldKan.Decomposition`, `Degeneracies`,
  `PInfty`.
* missing: everything topological (see §5).
* estimated DAG: normalisation is ~1 module; the actual comparison is unchanged.
* reaches `geometricHmap`: no.
* parallel theory: it would add a normalized complex the Spine does not use.
* **rejected — `NO_NET_SHORTENING`.**

### Route D — extra degeneracy / acyclic carriers

* available: `SimplicialObject.Augmented.ExtraDegeneracy`, `ExtraDegeneracy.homotopyEquiv`
  (an augmented simplicial object with an extra degeneracy has a chain complex homotopy
  equivalent to the augmentation), and `SimplexCategory.extraDegeneracy` for the augmented
  standard simplex.  On the singular side the project has an explicit prism operator
  (`RequestProject/Spine/Cohomology/Prism.lean`) and cochain-level homotopy invariance.
* missing: (i) the acyclic-model / acyclic-carrier theorem itself; (ii) *freeness on models* for
  the singular functor applied to `|K|`, which requires knowing that a singular simplex of `|K|`
  factors through a finite subcomplex — that is a genuine theorem about the colimit topology of
  `SSet.toTop`, not exposed in v4.28.0; (iii) chain-level (not just cohomology-level) homotopy
  invariance of the singular functor, i.e. a natural chain homotopy, which the project's prism
  layer supplies only in the dualised, cohomology-class form.
* estimated DAG: acyclic-models theorem (≈ 1 large module) + finite-subcomplex/compactness
  theorem for `|S|` (≈ 2–3 modules, new theory about the colimit topology) + naturality
  bookkeeping.  This is a substantial independent algebraic-topology project.
* reaches `geometricHmap`: yes, in principle, and in the strong chain-homotopy-equivalence form.
* parallel theory: no.
* **rejected for Task 10 — WP8 applies: it is a major independent project.**  It is, however,
  the *recommended* route for a successor task.

### Route E — skeletal induction

* available: `SSet.Skeleton`, `SSet.NonDegenerateSimplices`, `SSet.Subcomplex`,
  `SubcomplexColimits`, `RelativeCellComplex`/`AttachCells`.
* missing: the statement that `SSet.toTop` sends the skeletal filtration to a cell attachment
  (nothing in v4.28.0 connects `SSet.Skeleton` to `SSet.toTop`), *and* the entire relative
  singular homology apparatus: long exact sequence of a pair, excision, homology of a wedge of
  spheres.  None exists.
* estimated DAG: relative homology + LES + excision + cellular chain identification ≈ a
  multi-month formalisation.
* reaches `geometricHmap`: yes.
* parallel theory: yes — it would create a second homology theory unless carefully fused with
  the Task-5 native complex.
* **rejected.**

### Route F — subdivision / simplicial approximation

* available: nothing.  `Subdivision` is absent; no `Sd`, no `Ex`, no simplicial approximation.
* missing: the whole theory.
* **rejected.**

### Route G — Eilenberg–Steenrod uniqueness

* available: nothing.  `Mathlib.AlgebraicTopology.EilenbergSteenrod` does not exist in v4.28.0;
  neither the axioms nor a uniqueness theorem is present.  (Per the task instruction: even had
  the axioms been present, that would not have implied a uniqueness theorem.)
* **rejected.**

### Route summary

Every route either does not exist in the pinned environment or requires a major independent
body of algebraic topology.  Per WP8 the implementation was stopped at the first genuine
missing theorem and the reduction of §7 was produced instead.

---

## 7. WP5/WP7/WP10 — what Task 10 *did* prove

### 7.1 Exact dualisation, with no coefficient theorem

`RequestProject/Spine/Nerve/Dualization.lean`.

Over `ℤ₂` the Spine's cochain modules are literally the duals of its chain modules:
`Hom_{ℤ₂}(A →₀ ℤ₂, ℤ₂) ≅ (A → ℤ₂)` (`NerveGeom.freeDualEquiv`, i.e. `Finsupp.llift`).
`NerveGeom.dualOf` is the induced transpose, defined by the explicit formula
`(dualOf f g) a = ⟨f (single a 1), g⟩`, with

* `linearCombination_dualOf` — the defining adjunction `⟨f x, g⟩ = ⟨x, dualOf f g⟩`;
* `dualOf_id`, `dualOf_comp` (strict contravariance), `dualOf_add`, `dualOf_sum`,
  `dualOf_lmapDomain`;
* `dualOf_simpBoundary : dualOf ∂^simp = δ_simp`;
* `dualOf_singBoundary : dualOf ∂^sing = δ_sing`;
* `dualOf_chainMap    : dualOf J = J*`, the Task-9 `geometricCochainMap`.

**No universal coefficient theorem is used and no exactness of dualisation is assumed**; every
step is a proved identity about an explicitly defined operation.

### 7.2 The chain-level datum and the reduction

`RequestProject/Spine/Nerve/ChainHomotopyComparison.lean`.

`NerveGeom.ChainHomotopyEquivData 𝓤` is exactly

```
J : C_*^simp(N(𝓤);ℤ₂) ⇄ C_*^sing(|N(𝓤)|;ℤ₂) : R ,
∂h + h∂ = id + R J    (simplicial side, with h₋₁ = 0)
∂g + g∂ = id + J R    (singular side, with g₋₁ = 0)
```

with `J` **fixed** to `NerveGeom.chainMap` — it is not a field of the structure, so the
canonical map cannot be silently replaced (anti-shortcut 4).  There is no field asserting
bijectivity, quasi-isomorphy, or anything about cohomology (anti-shortcuts 1–3).

Proved from it:

| statement | Lean name |
| --- | --- |
| `R*` is a cochain map | `ChainHomotopyEquivData.cochainInv_comm` |
| dualised homotopies, degrees `0` and `n+1`, both sides | `cochainHtpySimp_zero/_succ`, `cochainHtpySing_zero/_succ` |
| `(geometricCochainMap 𝓤).Hmap n` surjective | `Hmap_surjective` |
| `(geometricCochainMap 𝓤).Hmap n` injective | `Hmap_injective` |
| **`geometricHmap 𝓤 n` bijective, all `n`** | `geometricHmap_bijective_of_chainHomotopyEquiv` |
| construction of the Task-9 `GeometricComparison` | `ChainHomotopyEquivData.toGeometricComparison` |
| Spin-lift class statements from the chain datum only | `spinLiftRealizedClassOfChain_eq_zero_iff_cech`, `spinLiftRealizedClassOfChain_eq_zero_iff` |

The degree-`0` case is handled separately throughout, because the Spine uses `B⁰ = 0`; nothing
is assumed about finiteness of any chain group (anti-shortcut 9).

Classification: **`CHAIN_HOMOTOPY_EQUIVALENCE ⟹ COHOMOLOGY_ISOMORPHISM`, proved.**

### 7.3 WP11 status

`NerveGeom.GeometricComparison` is marked
`SUPERSEDED_BY_TASK10_CHAIN_COMPARISON` **as an input**: it is now *derivable* from the chain
datum and should no longer be assumed directly.  It is retained for provenance and because the
Task-9 Spin-transport declarations are phrased in terms of it.  It is **not** eliminated,
because the chain datum is not constructed.  Therefore

```
[z]_{|N|} ∈ H²_sing(|N(𝓤)|;ℤ₂)   is still CONDITIONAL.
```

---

## 8. WP9 — degree-two scope test

Classification: **`NO_MEANINGFUL_REDUCTION`.**

Justification.

1. `H²` of a cochain complex depends on `C¹`, `C²`, `C³`; dually the degree-two comparison
   depends on the chain groups `C₁, C₂, C₃` and on the homotopies in those degrees.  A
   degree-two-only chain datum would still need `R₁, R₂, R₃`, `h₁, h₂, h₃`, `g₁, g₂, g₃` and
   their identities — i.e. essentially the same objects.
2. Every candidate construction of `R` and the homotopies (Routes D, E, F) is defined by
   induction on the degree, or by an acyclic-carrier argument that is uniform in the degree.
   Truncating at 3 does not remove any step; it only removes the (trivial) bookkeeping of the
   induction.
3. In the reduction actually proved (§7.2), all degrees cost the same: `Hmap_surjective` and
   `Hmap_injective` are single proofs with a `zero`/`succ` split, and the degree-2 instance is
   literally the `succ` branch with `m = 1`.  Extracting only degree 2 would *lengthen* the
   development, since the degree-`0` case would still be needed for nothing.
4. The Task-9 `GeometricComparison₂` fragment is retained only to record the engineering scope
   honestly; `GeometricComparison.toDegreeTwo` shows the full datum implies it, and no
   converse is claimed.

The physical obstruction class living in degree two is therefore **not** a reason to restrict:
`ALL_DEGREES_PREFERRED`.

---

## 9. Negative-result statement — the exact remaining theorem `T`

> **All project-native work reduces the problem to theorem `T`.**

**`T` (mathematical statement).**  For the simplicial set `K = N(𝓤)` (Task 9,
`NerveGeom.coverNerveSSet`), the map of `ℤ₂`-chain complexes obtained by free linearisation of
the adjunction unit

```
J = C_*(η_K) : C_*^simp(K;ℤ₂) ⟶ C_*^sing(|K|;ℤ₂)
```

is a **chain-homotopy equivalence**: there are `R_n`, `h_n`, `g_n` as in
`NerveGeom.ChainHomotopyEquivData`.

**Lean carrier types.**

```
C_n^simp = NerveGeom.SimpChain 𝓤 n = CechZ2.Nerve 𝓤 n →₀ ZMod 2
C_n^sing = NerveGeom.SingChain (NerveGeom.coverNerveRealization 𝓤) n
         = Mod2Cohomology.Simplex (SSet.toTop.obj (NerveGeom.coverNerveSSet 𝓤)) n →₀ ZMod 2
∂^simp   = NerveGeom.simpBoundary 𝓤 n
∂^sing   = NerveGeom.singBoundary (NerveGeom.coverNerveRealization 𝓤) n
```

**Canonical map involved.**  `NerveGeom.chainMap 𝓤 n`, proved equal to
`NerveGeom.sSetChainMap (sSetTopAdj.unit.app (NerveGeom.coverNerveSSet 𝓤)) n`
(`NerveGeom.chainMap_eq_unitChainMap`).  Formal `Prop`:
`NerveGeom.ChainComparisonStatement 𝓤`.

**Why Dold–Kan does not prove it.**  §5: Dold–Kan is internal to a fixed abelian category and
says nothing about `S ↦ Sing|S|`; the Spine already uses unnormalized chains, so the only
consequence Dold–Kan offers is not even needed.

**Closest pinned Mathlib theorem.**  There is none about `η_K`.  The closest *relevant*
declarations are `sSetTopAdj` (the adjunction — explicitly not the comparison),
`AlgebraicTopology.SSet.singularChainComplexFunctor` (a definition), and
`SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv` (the correct *shape* of conclusion,
but for an augmented simplicial object with an extra degeneracy, not for `η_K`).

**Smallest additional theorem family required.**  In increasing order of what a successor task
would have to build (Route D):

1. *Compact supports in a realisation*: every singular simplex `Δⁿ_top → |S|` factors through
   the realisation of a finite subcomplex of `S`.  (New theory about the colimit topology of
   `SSet.toTop`; nothing in v4.28.0.)
2. *Acyclicity of the models*: `C_*^sing(|Δ[n]|;ℤ₂)` is chain-homotopy equivalent to `ℤ₂`
   concentrated in degree `0`, naturally in `[n]`.  The project's prism operator
   (`RequestProject/Spine/Cohomology/Prism.lean`) is the right tool but currently produces a
   *cochain-class-level* statement; a natural chain contraction is needed.
3. *Acyclic models / acyclic carriers* for the pair of functors
   `S ↦ C_*^simp(S)` and `S ↦ C_*^sing(|S|)` on `SSet`, both free on the models `Δ[n]`.
4. Assembly: an inverse `R` and the two homotopies, i.e. `T`.

Steps 1–3 are each a self-contained module-sized theorem; together they are a genuine
independent algebraic-topology project, which is why WP8 stops here.

**Has upstream Mathlib progressed beyond v4.28.0?**  Not verified.  No claim is made in either
direction; the audit above is strictly about the pinned tree, as instructed.  What *is* recorded
from the pinned tree itself is that `Mathlib/AlgebraicTopology/SingularSet.lean` lists the
Quillen equivalence for `sSetTopAdj` as an open TODO.

**Does degree two reduce the burden?**  No — §8.

**Recommended next task.**  Route D, in the order 1 → 2 → 3 → 4 above, keeping the Task-5
native singular complex as the *only* singular theory so that no parallel theory appears.  The
nerve theorem (`|N(𝓤)| ≃ M`) remains a separate, independent problem and must not be merged
into it.

---

## 10. Anti-shortcut compliance

| constraint | compliance |
| --- | --- |
| 1. no `GeometricComparison` assumed as an input | new results assume `ChainHomotopyEquivData` only, and it is never assumed in an unconditional statement |
| 2. no field "`geometricHmap` is bijective" consumed as a result | `ChainHomotopyEquivData` has no such field; the bijectivity is a *theorem* |
| 3. no arbitrary cohomology equivalence | none introduced |
| 4. Task-9 `chainMap` not replaced | it is *fixed* in the structure, and identified with `C_*(η_K)` |
| 5. no claim that Dold–Kan proves `K ≃ Sing|K|` | §5 states the opposite explicitly |
| 6. no claim that an adjunction is an equivalence | §2.3, §6 Route A |
| 7. no Quillen equivalence assumed | recorded as absent |
| 8. no newer Mathlib declarations | every name used is checked in the pinned tree |
| 9. no finite-dimensionality of chain groups | the proofs are `Finsupp`-generic |
| 10. no universal coefficient argument | §7.1 |
| 11. no unproved exactness of dualisation | §7.1: `dualOf` is explicit and its properties are proved |
| 12. nerve theorem not invoked | untouched |
| 13. nothing added to Task 4 | §1; only a counterexample is added |
| 14. `w₂` not defined from the desired class | untouched |
| 15. no `sorry`/`admit`/project `axiom`/`unsafe`/`partial`/`implemented_by` | verified, §11 |

---

## 11. Verification evidence

Commands run in `/`(project root)`:

```
lake build RequestProject.Spine.Cohomology.Core     ✔
lake build RequestProject.Spine.Cech.Core           ✔
lake build RequestProject.Spine.GoodCover.Core      ✔
lake build RequestProject.Spine.Nerve.Core          ✔
lake build RequestProject.Spine.Geometry.Core       ✔
lake build RequestProject.Spine.Core                ✔
lake build RequestProject.Spine.Audit.Firewall      ✔
lake build                                          ✔  (8201 jobs)
lake build RequestProject.Spine.Nerve.UnitChainMap             ✔
lake build RequestProject.Spine.Nerve.Dualization               ✔
lake build RequestProject.Spine.Nerve.ChainHomotopyComparison   ✔
lake build RequestProject.Spine.Nerve.ManifoldAssumptionAudit   ✔
```

Firewall output on the full build:

```
Spine external-project imports: 0 (prefixes checked: 7)
Spine modules audited: 171
endpoint RequestProject.Spine.Core: direct legacy imports E1 = 0, E2 = 0,
                                    transitive legacy imports E1 = 0, E2 = 0
SPINE FIREWALL AUDIT: all checks passed
```

so

```
Experiment1 direct imports     = 0
Experiment1 transitive imports = 0
Experiment2 direct imports     = 0
Experiment2 transitive imports = 0
external-project imports       = 0
```

Axiom audit: `RequestProject/Spine/Nerve/Core.lean` runs `#print axioms` on all Task-9 and all
Task-10 principal declarations (68 in total).  Every one reports exactly

```
[propext, Classical.choice, Quot.sound]
```

Source scan of the new layer: no `sorry`, `admit`, project-local `axiom`, `unsafe`, `partial`
or `implemented_by`.

Failbuild ledger: `TASK10_FAILBUILDS.md` (append-only).

---

## 12. Final questions, answered

**Is the existing Task-9 `chainMap` exactly the chain map induced by the adjunction unit
`K → Sing|K|`?**
Yes, on the nose.  `NerveGeom.chainMap_eq_unitChainMap` proves
`chainMap 𝓤 n = sSetChainMap (sSetTopAdj.unit.app (coverNerveSSet 𝓤)) n` by `rfl`; the two
boundaries are likewise the linearised simplicial boundaries (`simpBoundary_eq`,
`singBoundary_eq`), and Task 9's `chainMap_comm` is the naturality of the unit
(`chainMap_comm_of_unit`).

**Does pinned Mathlib v4.28.0 already contain a theorem implying that this map is a homology
equivalence?**
No.  There is no `SSet.homology`, no comparison attached to
`AlgebraicTopology.SSet.singularChainComplexFunctor`, no model structure on `SSet` or `TopCat`,
no excision, no Mayer–Vietoris, no acyclic models, no subdivision, no Eilenberg–Steenrod file;
and Mathlib's own `SingularSet.lean` lists the Quillen equivalence for `sSetTopAdj` as a TODO.

**What does Dold–Kan actually remove from the proof burden, and what does it leave untouched?**
It removes only the normalized-vs-unnormalized bookkeeping: with an abelian target one may
compute with the normalized Moore complex instead of the alternating-face complex.  The Spine
uses unnormalized chains on both sides already, so even that is not needed.  Dold–Kan leaves
the entire topological content — anything about `S ↦ Sing|S|` — untouched.
Classification `NO_NET_SHORTENING`.

**Is there a materially shorter route through normalization, extra degeneracies, subdivision,
skeletal induction, Eilenberg–Steenrod infrastructure, or another existing theorem?**
No.  §6: normalisation (C) buys nothing; subdivision (F) and Eilenberg–Steenrod (G) do not
exist in the pinned tree; skeletal induction (E) needs relative homology and excision, both
absent; extra degeneracies (D) give the right *shape* of theorem but require a compact-supports
theorem for `|S|`, a natural chain contraction of the models, and the acyclic-models theorem —
a major independent project.  Route D is nevertheless the recommended successor route.

**Has the canonical map `geometricHmap_{K,n}` been proved bijective without supplying comparison
data?**
No.  It is proved bijective in every degree *given* `NerveGeom.ChainHomotopyEquivData`, which is
chain-level data about the canonical map itself — not a cohomological assumption, and not an
assumption that anything is bijective.  Unconditionally, it remains open.

**If not, what is the first exact theorem still missing?**
`NerveGeom.ChainComparisonStatement 𝓤`, i.e. theorem `T` of §9: the canonical chain map
`J = C_*(η_K)` is a chain-homotopy equivalence.  Its first genuinely missing prerequisite is
the compact-supports theorem for realisations (every singular simplex of `|S|` factors through
the realisation of a finite subcomplex).

**Is proving only degree 2 materially easier?**
No: `NO_MEANINGFUL_REDUCTION` (§8).  `H²` already involves `C¹, C², C³`, and the reduction
proved here is uniform in the degree.

**After Task 10, can the genuine fixed-cover Spin-lift obstruction be represented
unconditionally as `[z]_{|N|} ∈ H²_sing(|N(𝓤)|;ℤ₂)`?**
No.  It remains conditional, but the condition has been strictly weakened: it is no longer a
cohomology-level bijectivity assumption but the single chain-level statement
`ChainComparisonStatement`, from which
`spinLiftRealizedClassOfChain_eq_zero_iff_cech` and `spinLiftRealizedClassOfChain_eq_zero_iff`
follow.  The nerve theorem `|N(𝓤)| ≃ M` was not touched and remains a separate later problem,
independent of the comparison theorem.

---

# TASK 11 CORRECTION SECTION — appended by Task 11 (2026-09-09)

Append-only.  Nothing above this line has been deleted or rewritten; the corrections below
supersede the indicated passages.

## C1. "the only thing still missing is one chain-level statement" (§0, line 14)

**Superseded wording.**  The introduction said that Task 10 "does prove that the only thing
still missing is one chain-level statement".

**Corrected wording.**  Task 10 proved

```
ChainComparisonStatement 𝓤  ⟹  GeometricComparison 𝓤  ⟹  ∀ n, Bijective (geometricHmap 𝓤 n)
```

i.e. that `ChainComparisonStatement 𝓤` is *a* sufficient condition, and the one Task 10
recommends.  It is **not** proved to be necessary, and no converse implication exists in the
project.  The route-independent target remains

```
∀ n, Function.Bijective (NerveGeom.geometricHmap 𝓤 n),
```

and a weaker sufficient route (for example a bare quasi-isomorphism statement plus a
coefficient argument) is not excluded.

## C2. `ChainHomotopyEquivData` is a *stronger*, not weaker, condition

**Superseded wording.**  The docstring of `NerveGeom.GeometricComparison` in
`RequestProject/Spine/Nerve/ComparisonSpec.lean` described the chain-level datum as "strictly
weaker to assume" than `GeometricComparison`, and the closing section of this audit described
the Spin-lift condition as "strictly weakened".

**Corrected wording.**  `ChainHomotopyEquivData 𝓤 ⟹ GeometricComparison 𝓤`, with no proved
converse.  It is therefore a **stronger**, more structured **sufficient** condition:

> Task 10 replaced an abstract cohomological comparison assumption by a stronger but
> structurally deeper sufficient condition tied to the canonical chain map `J = C_*(η_K)`.

Applied in the sources: `RequestProject/Spine/Nerve/ComparisonSpec.lean` (docstring of
`GeometricComparison`, marked `TASK 11 CORRECTION (WP3)`) and
`RequestProject/Spine/Nerve/ChainHomotopyComparison.lean` (module docstring, section *Task 11
status corrections*).

## C3. The compact-support theorem is route-specific

**Superseded wording.**  This audit called the compact-supports theorem "the first genuinely
missing prerequisite", in a context that could be read as "the unique logical blocker".

**Corrected wording.**  "Every singular simplex of `|S|` factors through the realisation of a
finite subcomplex" is the first identified missing prerequisite **on the proposed
Acyclic-Models route** (Route D).  It is route-specific.  It is not the unique logical blocker,
and other routes have different first prerequisites (for example the model-category route needs
the Kan–Quillen model structure, which upstream Mathlib itself has not finished).

## C4. "Has upstream Mathlib progressed beyond v4.28.0?  Not verified." (§ WP8 answers)

**Now verified, by Task 11.**  Upstream Mathlib at commit
`076c9da2981330e0d1ba84a10afa6544faafa612` (2026-09-09, Lean `v4.34.0-rc2`, 6002 commits after
the pin) has gained substantial algebraic-topology infrastructure — `SSet.homology`, homotopy
invariance of simplicial and singular homology, `H₀` computations, the normalized chain
complex, relative simplicial homology with its long exact sequence (`SSetPair`), the category
`TopPair`, `TopPair.HomologyPretheory` with the homotopy axiom, and the subdivision adjunction
`sd ⊣ ex` — but it contains **no** theorem about `η_K : K → Sing|K|` beyond naturality, **no**
excision, **no** acyclic models, **no** homology of contractible spaces or of `Δ[n]`, and the
Quillen-equivalence statement is still an explicit TODO in `SingularSet.lean`.

Task-11 verdict: **Outcome C, `NO_MATERIAL_SHORTENING`**.  Full evidence, provenance, decision
matrix and the proposed Task-12 DAG are in `TASK11_UPSTREAM_DELTA_AUDIT.md`; the external
source ledger is `TASK11_EXTERNAL_SOURCES.md`.

## C5. Route matrix entry "Route G — Eilenberg–Steenrod uniqueness"

**Unchanged in substance, refined.**  At the pin, `Mathlib.AlgebraicTopology.EilenbergSteenrod`
does not exist.  At `076c9da` it exists, but contains only the *data* of a homology pretheory
plus the homotopy-invariance class; there is still **no uniqueness theorem**, so the route stays
`REJECT`.
