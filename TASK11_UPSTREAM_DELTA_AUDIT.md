# TASK 11 — Upstream Delta Audit for the Geometric Comparison Blocker

Source hypothesis paper: **Relational Spin-Closure Hypothesis — Nakahara-revised, 8 September 2026**
(`Relational_Spin_Closure_Hypothesis_2026-09-08.pdf`).

Task 11 is an **audit and route-selection task**.  No new algebraic topology was developed; the
only new Lean is the compile-probe module `RequestProject/Spine/Nerve/Task11Probe.lean`
(WP14/WP17) and two documentation corrections.

**Overall classification of Task 11:**

> **Outcome C — `NO_MATERIAL_SHORTENING`.**
> Current upstream Mathlib does **not** remove the Task-10 blocker.

Execution/access date: **2026-09-09**.

---

## 0. Summary table

| WP | question | classification |
| --- | --- | --- |
| WP1 | production environment frozen | unchanged: `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` untouched |
| WP2 | exact version provenance | §1 |
| WP3 | exact Task-10 blocker restated | §2 |
| WP4 | post-pin algebraic-topology module delta | `UPSTREAM_NEW` / `PARTIAL_INFRASTRUCTURE` (§3) |
| WP5 | direct comparison theorem for `η_K` | `NEGATIVE_RESULT` — none exists (§4) |
| WP6 | Quillen-equivalence status | still an explicit upstream `TODO` (§5) |
| WP7 | relative simplicial homology delta | `PARTIAL_INFRASTRUCTURE`, does **not** shorten the actual map (§6) |
| WP8 | Eilenberg–Steenrod delta | definitions + one axiom only; **no uniqueness theorem** (§7) |
| WP9 | Dold–Kan / normalization delta | `NORMALIZATION_ONLY` = `UNCHANGED_NORMALIZATION_ONLY` (§8) |
| WP10 | PR / issue / history audit | §9 |
| WP11 | external Lean formalizations | `TASK11_EXTERNAL_SOURCES.md`, summary in §10 |
| WP12 | backport feasibility | `MEDIUM_INFRASTRUCTURE_DELTA` … `MAJOR_MATHLIB_UPGRADE_REQUIRED` (§11) |
| WP13 | upgrade feasibility | `HIGH_RISK` (§12) |
| WP14 | compile probes | pin probes green, upstream probes run (§13) |
| WP15 | decision matrix | §14 |
| WP16 | hard decision gate | **Outcome C** (§15) |
| WP17 | no proof expansion | respected — see §13 |
| WP18 | physical boundary preserved | respected — nothing physical was touched |

---

## 1. WP2 — exact version provenance

### 1.1 Production environment (unchanged by Task 11)

| field | value |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.28.0` (`lean-toolchain`) |
| Mathlib requirement | `git = https://github.com/leanprover-community/mathlib4.git`, `rev = v4.28.0` (`lakefile.toml`) |
| Mathlib resolved commit | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (`lake-manifest.json`) |
| that commit's date / subject | 2026-02-16T15:28:25Z — *chore: bump toolchain to v4.28.0 (#35406)* |
| other dependencies | `plausible 55c8532e…`, `LeanSearchClient c5d5b8fe…`, `importGraph 85b59af4…`, `proofwidgets v0.0.87 (be3b2e63…)`, `aesop f642a64c…`, `Qq b8f98e90…`, `batteries 495c008c…`, `Cli v4.28.0 (4f10f476…)` |
| project state | Task-10 tree plus the Task-11 probe module; `lake build` green (§13.3) |

### 1.2 Current upstream environment (external research source only)

| field | value |
| --- | --- |
| repository | `https://github.com/leanprover-community/mathlib4` |
| branch | `master` |
| **exact upstream commit audited** | **`076c9da2981330e0d1ba84a10afa6544faafa612`** |
| commit date | 2026-09-09T03:44:13Z (subject: *feat(Counterexamples): the space ω₁ (#41962)*) |
| access date | 2026-09-09 |
| Lean toolchain required by that commit | `leanprover/lean4:v4.34.0-rc2` |
| relation to the pin | the pin is an ancestor; `git rev-list --count 8f9d9cf..076c9da` = **6002** commits |
| where it lives | scratch checkout outside the Lake project; **not** linked into the production build |

No vague label such as "latest Mathlib" is used anywhere below: every claim is
`8f9d9cff6bd728b17a24e163c9402775d9e6a365` **vs.** `076c9da2981330e0d1ba84a10afa6544faafa612`.

---

## 2. WP3 — the exact Task-10 blocker, restated, with the Task-10 status corrections

### 2.1 The objects, exactly as they exist in the project

* `K = N(𝓤) = NerveGeom.coverNerveSSet 𝓤 : SSet`.
* `|K| = NerveGeom.coverNerveRealization 𝓤 = SSet.toTop.obj (coverNerveSSet 𝓤) : TopCat`
  (`NerveGeom.coverNerveRealization_def`).
* `η_K = sSetTopAdj.unit.app (coverNerveSSet 𝓤) : K ⟶ TopCat.toSSet.obj (SSet.toTop.obj K)`.
* `J = NerveGeom.chainMap 𝓤 : C_*^simp(K;ℤ₂) → C_*^sing(|K|;ℤ₂)`, and Task 10 proved
  `NerveGeom.chainMap_eq_unitChainMap : chainMap 𝓤 n = sSetChainMap (sSetTopAdj.unit.app K) n`
  by `rfl`, i.e. **`J = C_*(η_K)`**.
* `NerveGeom.geometricHmap 𝓤 n : Hⁿ_sing(|N(𝓤)|;ℤ₂) → Ȟⁿ(𝓤;ℤ₂)` is the Task-9 cohomology map.
* `NerveGeom.ChainHomotopyEquivData 𝓤` is chain-homotopy-inverse data **for that fixed `J`**;
  `NerveGeom.ChainComparisonStatement 𝓤 = Nonempty (ChainHomotopyEquivData 𝓤)`.
* Task 10 proved `NerveGeom.geometricHmap_bijective_of_chainHomotopyEquiv` and
  `NerveGeom.ChainHomotopyEquivData.toGeometricComparison`.

### 2.2 The two endpoints, kept separate

**Required endpoint (route-independent target).**

```
∀ n, Function.Bijective (NerveGeom.geometricHmap 𝓤 n)
```

**Preferred stronger sufficient endpoint.**

```
C_*(η_K) is a chain-homotopy equivalence     (= NerveGeom.ChainComparisonStatement 𝓤)
```

These are **not** conflated.  The proved implication is one-directional:

```
ChainComparisonStatement 𝓤  ⟹  GeometricComparison 𝓤  ⟹  ∀ n, Bijective (geometricHmap 𝓤 n)
```

and no converse is proved anywhere in the project.  A **weaker** sufficient route (for
instance a bare quasi-isomorphism statement for `C_*(η_K)` over `ℤ₂` together with a
coefficient argument, or a cohomology-level argument that never builds explicit homotopies) is
not excluded and is not ruled out by Task 10 or Task 11.

### 2.3 Status corrections carried forward from Task 10 (applied)

1. **`ChainHomotopyEquivData` is a stronger, not weaker, condition.**  The Task-10 docstring in
   `RequestProject/Spine/Nerve/ComparisonSpec.lean` said the chain-level datum is "strictly
   weaker to assume" than `GeometricComparison`.  That is **withdrawn**.  Correct wording, now
   in the source and repeated here: *Task 10 replaced an abstract cohomological comparison
   assumption by a stronger but structurally deeper sufficient condition tied to the canonical
   chain map.*  Corrections applied in
   `RequestProject/Spine/Nerve/ComparisonSpec.lean` (docstring of `GeometricComparison`,
   marked `TASK 11 CORRECTION (WP3)`) and
   `RequestProject/Spine/Nerve/ChainHomotopyComparison.lean` (module docstring, section
   *Task 11 status corrections*).  `TASK10_AUDIT.md` is corrected append-only in its
   `TASK 11 CORRECTION SECTION`.
2. **The compact-support theorem is route-specific.**  "Every singular simplex of `|S|`
   factors through the realisation of a finite subcomplex" is the first identified missing
   prerequisite **of the proposed Acyclic-Models route**, not the unique logical blocker.  Any
   statement to the contrary in Task-10 material is withdrawn; the route-independent target
   remains §2.2.

---

## 3. WP4 — post-v4.28.0 algebraic-topology module delta

`git diff --stat 8f9d9cf..076c9da -- Mathlib/AlgebraicTopology` reports **160 files changed,
12 214 insertions, 1 176 deletions**.  Only the items that could plausibly touch the blocker
are listed.  `AVAILABLE IN PIN?` was checked by file existence in
`.lake/packages/mathlib/…` and by the elaboration probes of §13.1.

| DECLARATION | FILE | UPSTREAM COMMIT INTRODUCED | IN PIN? | MATHEMATICAL ROLE | DIRECTLY RELEVANT? |
| --- | --- | --- | --- | --- | --- |
| `SSet.chainComplexFunctor`, `SSet.chainComplex`, `SSet.chainComplexMap`, `SSet.homology`, `SSet.homologyMap`, `SSet.homologyFunctor` | `AlgebraicTopology/SimplicialSet/Homology/Basic.lean` | `a21ec0212b`, 2026-04-13, PR #37656 | **partly** — the pin has the *chain complex* under the old name `AlgebraicTopology.SSet.singularChainComplexFunctor`; it has **no** `SSet.homology`/`homologyMap` | simplicial chains and homology of a simplicial set with coefficients in `R : C` | yes — this is the *source* side of our comparison, and `SSet.homologyMap (sSetTopAdj.unit.app K) R n` is exactly the upstream name of our map |
| `AlgebraicTopology.singularChainComplexFunctor`, `singularHomologyFunctor` | `AlgebraicTopology/SingularHomology/Basic.lean` | pre-pin, extended `a21ec0212b` | **yes** (both) | singular chains/homology of `X` defined as the simplicial chains of `Sing X` | yes — the *target* side |
| `SSet.homology₀Iso`, `SSet.homology₀ε` | `…/SimplicialSet/Homology/HomologyZero.lean` | `57d3e16137`, 2026-04-17, PR #38134 | no | `H₀(X;R) ≅ ∐_{π₀X} R` | partially (degree 0 only) |
| `TopCat.singularHomology₀Iso`, `TopCat.singularHomology₀ε` | `…/SingularHomology/HomologyZero.lean` | `29373c83a7`, 2026-04-28, PR #37630 | no | `H₀^sing(X;R) ≅ ∐_{π₀X} R` | partially (degree 0 only) |
| `SSet.Homotopy.congr_homologyMap`, `SSet.Homotopy.chainComplexMap` | `…/SimplicialSet/Homology/HomotopyInvariance.lean` | `a21ec0212b`, PR #37656 | no | homotopy invariance of simplicial homology | yes as an *ingredient*; it says nothing about `η_K` |
| `TopCat.Homotopy.singularChainComplexFunctorObjMap`, `TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor` | `…/SingularHomology/HomotopyInvariance.lean` | `f71a4059a8` (2026-03-30, PR #37091) / renamed `ff517753c5` (PR #37658) | no | homotopy invariance of singular homology | yes as an *ingredient* |
| `SSet.normalizedChainComplex`, `SSet.homotopyEquivNormalizedChainComplex`, `QuasiIso (X.toNormalizedChainComplex R)`, `SSet.isZero_homology_of_hasDimensionLT` | `…/SimplicialSet/Homology/Nondegenerate.lean` | `6a9afea8b4`, 2026-05-12, PR #38552 | no | normalized ↔ unnormalized simplicial chains; vanishing above the dimension | normalization layer only (§8) |
| `SSetPair`, `SSet.Subcomplex.pair`, `SSet.toPairFunctor` | `…/SimplicialSet/SSetPair.lean` | `dbd0e3c605`, 2026-08-31, PR #41285 | no | pairs of simplicial sets | yes as an *ingredient* (§6) |
| `SSetPair.chainComplex`, `SSetPair.homology`, `SSetPair.homologyπ`, `SSetPair.homologyδ`, `SSetPair.shortExact_chainComplexShortComplex`, `SSetPair.homology_exact₁/₂/₃` | `…/SimplicialSet/Homology/Relative.lean` | `dbd0e3c605`, PR #41285 | no | relative simplicial homology and its long exact sequence | yes as an *ingredient* (§6) |
| `TopPair`, `TopPair.incl`, `TopPair.proj₁/₂` | `Mathlib/Topology/Category/TopPair.lean` | `e6a5fb085e`, 2026-05-01, PR #36621 | no | the category of topological pairs | supporting |
| `TopPair.HomologyPretheory`, `HomologyPretheory.IsHomotopyInvariant` | `AlgebraicTopology/EilenbergSteenrod.lean` | `09f78106cb`, 2026-06-04, PR #39236 | no | *data* of an ES homology theory + the homotopy axiom | no (§7) |
| `SimplexCategory.sd`, `SSet.sd`, `SSet.ex`, `SSet.sdExAdjunction`, `SSet.stdSimplex.sdIso` | `…/SimplicialSet/Subdivision.lean` | `2cade716a1`, 2026-04-19, PR #38067 | no | the subdivision/`Ex` adjunction — **definitions only** | no: no simplicial-approximation or `sd`-homology theorem |
| `SimplicialObject.Homotopy`, `SimplicialObject.Homotopy.toChainHomotopy` | `…/SimplicialObject/ChainHomotopy.lean`, `…/SimplicialObject/Homotopy.lean` | `cb339e879a`, 2026-03-19, PR #32881 | no | combinatorial simplicial homotopies ⟹ chain homotopies | ingredient for homotopy invariance |
| `SSet.Homotopy`, `TopCat.Homotopy.toSSet` | `…/SimplicialSet/Homotopy.lean`, `Mathlib/Topology/Homotopy/TopCat/ToSSet.lean` | `8f4ffc6cdc` (PR #33683), `f71a4059a8` (PR #37091) | no | topological homotopies induce simplicial homotopies of singular sets | ingredient |
| `SSet.π₀`, `SSet.IsConnected`, `TopCat.zerothHomotopyEquiv` | `…/SimplicialSet/PiZero.lean`, `Mathlib/Topology/Homotopy/TopCat/ZerothHomotopy.lean` | `5f98bd4a02`, 2026-04-11, PR #37607 | no | `π₀` of a simplicial set, `π₀(Sing X) ≅ π₀(X)` | degree-0 comparison only |
| `SimplexCategory.toTopHomeo`, `TopCat.toSSetObj₀Equiv`, `SSet.stdSimplex.toTopObjIsoI` | `…/SimplicialSet/TopAdj.lean` | `4b77bd7bd6`, 2026-03-26, PR #37099 | no | API for `|Δ[n]|` and for `Sing X` in degree 0 | supporting only |
| anodyne extensions: `SSet.anodyneExtensions`, pushout-product, `RelativeCellComplex`, `UnionProd`, Moss pairings | `…/SimplicialSet/AnodyneExtensions/**` | many, 2026-03 … 2026-08 | partly (a smaller `AnodyneExtensions` dir exists at the pin) | machinery towards the Kan–Quillen model structure | no theorem about `η_K` |
| `Mathlib/AlgebraicTopology/SimplicialComplex/Basic.lean`, `Reedy/Basic.lean`, `SimplexCategory/SemiSimplexCategory.lean`, `Quasicategory/**`, `ModelCategory/**` | various | 2026-03 … 2026-08 | no / partly | general infrastructure | no |

**Absent from the audited upstream commit as well (checked by exhaustive `rg` over the whole
tree at `076c9da`):**

* no occurrence of `excision` anywhere in `Mathlib/`;
* no occurrence of `acyclic model` / `AcyclicModel` / `acyclic carrier`;
* no occurrence of `nerve theorem`;
* no Mayer–Vietoris for singular homology;
* no homology of `Δ[n]`, no homology of a contractible space, no homology of spheres;
* no `ContractibleSpace` result in `Mathlib/AlgebraicTopology`;
* no simplicial-approximation theorem, no `sd`-to-homology comparison;
* no Kan–Quillen model structure (the cofibration/fibration classes in
  `SimplicialSet/CategoryWithFibrations.lean` are still documented as "(TODO)");
* only **three** files in the entire tree mention `SSet.toTop`/`sSetTopAdj`
  (`SingularSet.lean`, `SimplicialSet/TopAdj.lean`, `SingularHomology/Basic.lean`), and none
  of them states a homological property of the unit or the counit.

---

## 4. WP5 — search for a direct comparison theorem: `NEGATIVE_RESULT`

Searched at `076c9da` by name and by semantics for any theorem giving one of

* `IsIso (SSet.homologyMap (sSetTopAdj.unit.app K) R n)`,
* `Hₙ(K;R) ≅ Hₙ^sing(|K|;R)`,
* `QuasiIso (SSet.chainComplexMap (sSetTopAdj.unit.app K) R)`,
* a chain-homotopy equivalence `C_*(K;R) ≃ C_*^sing(|K|;R)`,
* `η_K` (or the counit `|Sing X| → X`) being a weak equivalence.

**Result: no such theorem exists at `076c9da`.**  Evidence:

1. Name/semantic grep: the three files that mention the adjunction contain no such statement
   (§3).  There is no `SSet.homologyMap`-valued `IsIso` lemma anywhere.
2. Upstream compile probe B3 (§13.2): `QuasiIso (SSet.chainComplexMap (sSetTopAdj.unit.app K) R)`
   has **no instance** — `failed to synthesize instance`.
3. Upstream compile probe B4 (§13.2), run against **all of `import Mathlib`** at `076c9da`:
   ```
   example … : IsIso (SSet.homologyMap (sSetTopAdj.unit.app K) R n) := by exact?
   ⇒ error: `exact?` could not close the goal.
   ```

None of the forbidden inferences was used: the existence of `sSetTopAdj`, of `SSet.toTop`, of
`TopCat.toSSet`, of Dold–Kan, of relative simplicial homology, or of the Eilenberg–Steenrod
*axioms* was **not** taken as evidence of a comparison theorem.

Classification: `NEGATIVE_RESULT` / `NO_MATERIAL_SHORTENING` on the direct route.

---

## 5. WP6 — Quillen-equivalence status at `076c9da`

`Mathlib/AlgebraicTopology/SingularSet.lean`, lines 32–35, at commit `076c9da`:

```
## TODO (@joelriou)

- Show that the singular simplicial set is a Kan complex.
- Show the adjunction `sSetTopAdj` is a Quillen equivalence.
```

This is **verbatim identical** to the pin (`.lake/packages/mathlib/Mathlib/AlgebraicTopology/
SingularSet.lean`, lines 34–37).  Consequently:

| statement | status at `076c9da` |
| --- | --- |
| 1. `TopCat.toSSet X` is a Kan complex | **not proved** (explicit TODO) |
| 2. the unit `K → Sing\|K\|` is a weak equivalence | **not proved**, not even stated |
| 3. the counit `\|Sing X\| → X` is a weak equivalence | **not proved**, not even stated |
| 4. `sSetTopAdj` is a Quillen adjunction | **not proved** (no model structure on `SSet` yet) |
| 5. `sSetTopAdj` is a Quillen equivalence | **not proved** (explicit TODO) |

As required, the TODO was not treated as sufficient evidence: the independent WP5 search
(§4), including the library-wide `exact?` probe, was carried out separately and also came back
empty.

---

## 6. WP7 — relative simplicial homology delta

New since the pin (PR #41285, merge commit `dbd0e3c605`, 2026-08-31):

| ingredient | present at `076c9da`? | comment |
| --- | --- | --- |
| chain complexes for simplicial pairs | **yes** — `SSetPair.chainComplex R` as the cokernel of `C_*(A) ↣ C_*(X)` | for `SSetPair`, i.e. a monomorphism of simplicial sets |
| short exact sequence of complexes | **yes** — `SSetPair.shortExact_chainComplexShortComplex` | |
| long exact homology sequence | **yes** — `homology_exact₁`, `homology_exact₂`, `homology_exact₃` | |
| connecting morphisms | **yes** — `SSetPair.homologyδ` | |
| naturality | **yes** — `SSetPair.homologyFunctor`, `homologyMap_comp` | |
| excision-like statements | **no** | no excision anywhere in Mathlib at `076c9da` |
| homology of simplices `Δ[n]` | **no** | still PR #37480, open |
| homology of horns | **no** | |
| homology of boundaries `∂Δ[n]` | **no** | |
| skeletal-induction ingredients | **partial** — `SSet.Skeleton`, `SSet.Subcomplex`, `HasDimensionLT`, `isZero_homology_of_hasDimensionLT`, non-degenerate-simplices colimits exist; the homology of the skeletal filtration quotients does **not** | |
| relative **singular** homology (pairs of spaces) | **no** | `TopPair` exists, but `TopPair ⥤ SSetPair` and its homology are only in open PR #37659 and in the out-of-tree `joelriou/excision` repository |

> **Does this materially shorten a proof that `C_*(η_K)` is a quasi-isomorphism?**
> **No.**  There is no dependency chain from `SSetPair.homology_exact₁/₂/₃` to any statement
> about `η_K`.  The classical skeletal-induction proof needs, in addition: (a) the homology of
> `|Δ[n]|`, i.e. of a contractible space (absent); (b) excision or a good-pair computation of
> `H_*(|K^{(n)}|, |K^{(n-1)}|)` (absent); (c) compatibility of singular homology with the
> filtered colimit of skeleta, which is the compact-support theorem (absent).  Relative
> simplicial homology supplies only the bookkeeping of step (0).

Classification: `PARTIAL_INFRASTRUCTURE`, **not** counted as a solution — per the WP7 rule,
no concrete dependency chain to the Task-10 map exists.

---

## 7. WP8 — Eilenberg–Steenrod delta

`Mathlib/AlgebraicTopology/EilenbergSteenrod.lean` (new since the pin; PR #39236, first
appearance `09f78106cb`, 2026-06-04) contains, in full:

* `TopPair.HomologyPretheory C c` — a **structure** bundling relative functors `Hₚ i : TopPair ⥤ C`,
  absolute functors `H i : TopCat ⥤ C`, the comparison isomorphism `iso i : H i ≅ incl ⋙ Hₚ i`,
  and boundary transformations `δ i j` with `shape_δ`;
* the category structure on `HomologyPretheory` (`Hom`, `hₚFunctor`, `hFunctor`, `IsIso`
  transport lemmas);
* the class `HomologyPretheory.IsHomotopyInvariant` — **one** axiom (homotopy invariance),
  and `IsClosedUnderIsomorphisms (isHomotopyInvariant C c)`.

It contains **no** exactness axiom, **no** excision axiom, **no** dimension axiom, **no**
additivity axiom, and in particular:

* **no uniqueness theorem**;
* no comparison theorem;
* no natural-isomorphism theorem;
* no extension theorem;
* no cellular comparison;
* no relative-theory comparison.

Therefore the question "can one now show cheaply that simplicial homology of `K` and singular
homology of `|K|` agree because both satisfy the axioms?" has the answer **no**: there is no
uniqueness theorem to apply, and no hypothesis DAG to reconstruct.  (A fuller axioms PR,
#38369 by `quantumsnow`, is **open**, and even it does not contain a uniqueness theorem.)

Classification: `PARTIAL_INFRASTRUCTURE` / `NO_MATERIAL_SHORTENING`.

---

## 8. WP9 — Dold–Kan / normalization delta

Upstream changes to `AlgebraicTopology/DoldKan/**` since the pin are refactors, `module`-system
migration and small API additions (`Compatibility`, `Degeneracies`, `SplitSimplicialObject`
+115 lines, etc.).  The one genuinely new normalization result relevant here is
`SimplicialSet/Homology/Nondegenerate.lean` (PR #38552): `X.normalizedChainComplex R`, the
split-mono/split-epi comparison with `X.chainComplex R`, `QuasiIso` instances in both
directions, `homotopyEquivNormalizedChainComplex`, and vanishing above the dimension.

That is exactly the layer

```
normalized simplicial chains  ↔  unnormalized simplicial chains
```

on **one** simplicial set.  It says nothing about

```
K  ⟶  Sing |K| .
```

No new upstream theorem connects the two layers.

Classification: **`UNCHANGED_NORMALIZATION_ONLY`** (equivalently `NORMALIZATION_ONLY`).
Not `NEW_USEFUL_BRIDGE`, not `NOW_SOLVES_COMPARISON`.

(For the project specifically, this layer is also not needed: Task 9/10 proved that the Čech
cochain complex of the cover is the **unnormalized** one on the nose, so no normalization
bridge is on the critical path.)

---

## 9. WP10 — upstream Git history, PRs and issues

Merged and available **only after the pin** (`MERGED_AFTER_PIN` for all of them; none is in
`v4.28.0`):

| PR | title | author | merge commit | date | files | contribution |
| --- | --- | --- | --- | --- | --- | --- |
| #32881 | feat(AlgebraicTopology/SimplicialObject): define simplicial homotopy | — | `cb339e879a` | 2026-03-19 | `SimplicialObject/ChainHomotopy.lean`, `…/Homotopy.lean` | combinatorial homotopies ⟹ chain homotopies |
| #37099 | feat(AlgebraicTopology): API for the geometric realization of simplicial sets | — | `4b77bd7bd6` | 2026-03-26 | `SimplicialSet/TopAdj.lean` | `\|Δ[n]\| ≃ₜ Δⁿ_top`, `Sing X` in degree 0, `\|Δ[1]\| ≅ I` |
| #33683 | feat(AlgebraicTopology/SimplicialSet): the simplicial homotopy induced by a homotopy | — | `8f4ffc6cdc` | 2026-03-27 | `SimplicialSet/Homotopy.lean` | `SSet.Homotopy` |
| #37091 | feat(AlgebraicTopology): homotopy invariance of singular homology | — | `f71a4059a8` | 2026-03-30 | `Topology/Homotopy/TopCat/ToSSet.lean`, `SingularHomology/HomotopyInvariance*` | homotopy invariance |
| #37607 | feat(AlgebraicTopology/SimplicialSet): connected components | — | `5f98bd4a02` | 2026-04-11 | `SimplicialSet/PiZero.lean` | `π₀` |
| #37656 | feat(AlgebraicTopology): simplicial homology | Joël Riou, Andrew Yang | `a21ec0212b` | 2026-04-13 | `SimplicialSet/Homology/Basic.lean`, `…/HomotopyInvariance.lean` | `SSet.chainComplex`, `SSet.homology`, homotopy invariance |
| #38134 | feat(AlgebraicTopology/SimplicialSet): homology in degree 0 | Joël Riou | `57d3e16137` | 2026-04-17 | `Homology/HomologyZero.lean` | `H₀ ≅ ∐_{π₀} R` |
| #37658 | chore: rename `SingularHomology.HomotopyInvarianceTopCat` | — | `ff517753c5` | 2026-04-17 | `SingularHomology/**` | rename |
| #38067 | feat(AlgebraicTopology/SimplicialSet): the subdivision functor | Joël Riou | `2cade716a1` | 2026-04-19 | `SimplicialSet/Subdivision.lean` | `sd ⊣ ex` (definitions only) |
| #37630 | feat(AlgebraicTopology/SingularHomology): homology in degree 0 | — | `29373c83a7` | 2026-04-28 | `SingularHomology/HomologyZero.lean` | `H₀^sing ≅ ∐_{π₀} R` |
| #36621 | feat: add the category of topological pairs | — | `e6a5fb085e` | 2026-05-01 | `Topology/Category/TopPair.lean` | `TopPair` |
| #38552 | feat(…/Homology): computing homology using nondegenerate simplices | Joël Riou | `6a9afea8b4` | 2026-05-12 | `Homology/Nondegenerate.lean` | normalized complex, `QuasiIso` |
| #39236 | feat(AlgebraicTopology): `HomologyPretheory` for Eilenberg-Steenrod homology | Jakob Scharmberg | (in tree by `09f78106cb`) | 2026-06-04 | `EilenbergSteenrod.lean` | ES *data* + homotopy axiom |
| #41285 | feat(AlgebraicTopology/SimplicialSet): relative homology | Joël Riou, Andrew Yang | `dbd0e3c605` | 2026-08-31 | `SSetPair.lean`, `Homology/Relative.lean` | relative simplicial homology + LES |

Open work (`OPEN_WORK`) at access date 2026-09-09:

| PR | title | author | state | created / updated | relevance |
| --- | --- | --- | --- | --- | --- |
| #37480 | feat(AlgebraicTopology): homology of contractible spaces | `erdOne` | open, 2 files, +62/−4 | 2026-04-01 / 2026-04-17 | **high** — would supply "acyclicity of the models", ingredient 2 of the Acyclic-Models route |
| #37659 | feat(AlgebraicTopology): relative singular homology | `erdOne` | open, 5 files, +205/−2 | 2026-04-05 / 2026-07-02 | high — relative singular homology of `TopPair` |
| #38369 | feat(AlgebraicTopology): Eilenberg Steenrod axioms | `quantumsnow` | open, 2 files, +282/−7 | 2026-04-22 / 2026-09-04 | medium — more axioms, still **no uniqueness theorem** |
| #41318 | feat(…/SimplicialSet/Homology): long exact sequence of a triple | `joelriou` | open, 18 files, +954/−39 | 2026-07-03 / 2026-08-31 | medium; PR text: *"I will put this PR on pause until I upstream the excision theorem for topological spaces"* |
| #43524 | feat(Geometry/Convex): the cone of an affine map from the standard simplex | `joelriou` | open | 2026-09-07 | ingredient of the excision development |
| #43528 | feat(Geometry/Convex): the simplicial set of affine simplices of a convex space | `joelriou` | open | 2026-09-07 | ingredient of the excision development; PR text: *"From https://github.com/joelriou/excision"* |
| #42435, #42488 | homotopy groups / fundamental groupoid of Kan complexes | `joelriou` | open | 2026-08 | homotopical, not homological; does not mention `η_K` |

`ABANDONED`: none identified.  `MERGED_AND_AVAILABLE` (i.e. already in the pin): the
adjunction `sSetTopAdj`, `AlgebraicTopology.SSet.singularChainComplexFunctor`,
`singularChainComplexFunctor`, `singularHomologyFunctor`, Dold–Kan, `ExtraDegeneracy`.

**Nothing merged or open contains a nearly complete simplicial-to-singular comparison
theorem.**  The most advanced relevant work — the excision line (#41318, #43524, #43528, and
`joelriou/excision`) — is aimed at excision for **singular** homology of topological pairs; it
does not mention geometric realization at all.

---

## 10. WP11 — external Lean formalizations (summary)

Full ledger: `TASK11_EXTERNAL_SOURCES.md`.  Nothing was imported; the firewall still reports
`external-project imports = 0`.

* `joelriou/excision` @ `7d6441e263568075b0228ca503b6976b4269906f` (2026-09-06, Apache-2.0
  headers, Lean `v4.34.0-rc2`, Mathlib fork `810b3888…`): a sorry-free out-of-tree development
  of **excision for singular homology** (`SmallSimplices`, barycentric subdivision, Lebesgue
  number, dévissage for `SSetPair`).  It contains **no** occurrence of `SSet.toTop`, hence no
  simplicial-to-singular comparison.  Influence: `THEOREM_DECOMPOSITION_REFERENCE`.
* `Shamrock-Frost/BrouwerFixedPoint` @ `2883ceb0f5d461155fa1689266a7af40ff8ae671` (Lean 3.51.1,
  mathlib3 `13361559…`, **no licence file**): contains a complete Lean-3 **acyclic models**
  development (`src/acyclic_models_theorem.lean`, ~505 lines: `functor_basis`, `lift_nat_trans`,
  `lift_nat_trans_unique`, `lifts_of_nat_trans_H0_give_same_map_in_homology`), barycentric
  subdivision, homotopy invariance, homology of spheres.  It does **not** formalize
  `H_*^simp(K) ≅ H_*^sing(|K|)`.  Influence: `DESIGN_REFERENCE` /
  `THEOREM_DECOMPOSITION_REFERENCE` only; no code may be copied (no licence).
* No repository was found formalizing `H_*^simp(K) ≅ H_*^sing(|K|)`, simplicial approximation,
  compact support in realizations, or finite-subcomplex containment.

---

## 11. WP12 — backport feasibility

For each upstream item that could ever matter, `Deps(T)` was traced down to declarations
present in `v4.28.0`.

| upstream item `T` | dependency cone beyond the pin | classification |
| --- | --- | --- |
| `SSet.homology` / `SSet.homologyMap` (PR #37656) | `SSet.chainComplexFunctor` (**already in the pin** as `AlgebraicTopology.SSet.singularChainComplexFunctor`) + `HomologicalComplex.homology` (in the pin) + `SSet.Nonempty`, `HasDimensionLT` (in the pin) | `SMALL_BACKPORT` — but useless on its own, since it is a definition, not a theorem |
| `SSet.Homotopy.congr_homologyMap`, `TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor` | `SimplicialObject.Homotopy` + `Homotopy.toChainHomotopy` + `SSet.Homotopy` + `TopCat.Homotopy.toSSet` + monoidal `SSet` API changes | `MEDIUM_INFRASTRUCTURE_DELTA` (≈ 4 new modules, ≈ 600 lines, plus `SimplicialSet/Monoidal` deltas) |
| `SSetPair.homology` + LES (PR #41285) | `MorphismProperty.Arrow`, `HomologicalComplexAbelian`, `HomologicalComplexKernels`, `HomologySequence`, `Limits.Preserves.SigmaConst`, `SSet.Subcomplex` deltas | `MEDIUM_INFRASTRUCTURE_DELTA` |
| `SSet.normalizedChainComplex` (PR #38552) | `SSet.Splitting`, `DoldKan/SplitSimplicialObject` deltas, `SigmaConst` | `MEDIUM_INFRASTRUCTURE_DELTA` |
| `TopPair.HomologyPretheory` (PR #39236) | `TopPair` (PR #36621) + `Category*`/`cat_disch` elaboration features of Lean ≥ 4.30 | `MEDIUM_INFRASTRUCTURE_DELTA`, and it proves nothing we need |
| `SSet.sd`, `SSet.ex` (PR #38067) | `Order.NonemptyFiniteChains`, `PartOrd.nerveFunctor`, `Limits.Presheaf` deltas | `SMALL_BACKPORT`, and it proves nothing we need |
| any theorem implying our target | — | **does not exist**, so nothing to backport |

Cross-cutting obstacle: every upstream file listed above is written in the **new Lean module
system** (`module`, `public import`, `@[expose] public section`, `Category*`, `cat_disch`,
`lia`, `dsimp%`, `set_option backward.defeqAttrib.useBackward`), which does not exist in Lean
`v4.28.0`.  A backport is therefore never a copy; it is a rewrite.

**Bottom line for WP12.**  Since no upstream theorem closes the gap, backporting buys *no*
mathematical progress: it would only re-import definitions the project already has in its own
`ℤ₂`-`Finsupp` form.  Recommended classification for a backport of the *useful delta*:
`MEDIUM_INFRASTRUCTURE_DELTA` and **not recommended** at this time.

---

## 12. WP13 — upgrade feasibility (assessment only; no upgrade performed)

| dimension | delta |
| --- | --- |
| Lean version | `v4.28.0` → `v4.34.0-rc2` (six minor releases; new module system, `Category*`, `cat_disch`, `lia`, changed `simp`/defeq backward options) |
| Mathlib commits | 6002 between `8f9d9cf` and `076c9da` |
| project modules potentially affected | 174 Spine modules / ≈ 33 600 lines (plus 221 legacy `Experiment1`/`Experiment2` modules, which are not default targets but are kept building) |
| known breaking imports | the Spine uses only `import Mathlib` (plus, from Task 11, `Mathlib.AlgebraicTopology.SingularHomology.Basic` and `Mathlib.Algebra.Homology.QuasiIso`); all three still exist at `076c9da`, so *import* breakage is low |
| known renames on our critical path | `AlgebraicTopology.SSet.singularChainComplexFunctor` → `SSet.chainComplexFunctor` (deprecated alias present at `076c9da`); `SingularHomology.HomotopyInvarianceTopCat` → `…HomotopyInvariance` |
| proof/tactic API drift | unquantified but large: 6002 commits touching `simp` sets, `Finsupp`, `LinearMap`, `ZMod`, manifolds, category theory; the Spine's 33 600 lines are tactic-heavy |
| firewall implications | none structurally: the firewall is a project-internal import audit and does not depend on Mathlib version |
| reproducibility impact | high — the whole Task-1…Task-10 audit trail is stated against the pin; an upgrade invalidates every "not available in the pinned library" statement in `TASK05…TASK10` and would require re-running all of them |

Classification: **`HIGH_RISK`**.  As required, this does **not** influence the mathematical
conclusion of §15: even a zero-risk upgrade would not supply the missing theorem.

---

## 13. WP14 — compile probes

### 13.1 Production-pin probes (class A)

Run inside the pinned environment.  **Negative controls** (verbatim elaboration errors):

```
#check @SSet.homology                                       -- Unknown constant `SSet.homology`
#check @SSetPair                                            -- Unknown identifier `SSetPair`
#check @TopPair.HomologyPretheory                           -- Unknown identifier `TopPair.HomologyPretheory`
#check @SSet.sd                                             -- Unknown constant `SSet.sd`
#check @SSet.normalizedChainComplex                         -- Unknown constant `SSet.normalizedChainComplex`
#check @TopCat.Homotopy.singularChainComplexFunctorObjMap   -- Unknown constant `…`
#check @TopPair                                             -- Unknown identifier `TopPair`
#check @SSet.Homotopy                                       -- Unknown constant `SSet.Homotopy`
#check @SimplicialObject.Homotopy                           -- Unknown constant `CategoryTheory.SimplicialObject.Homotopy`
```

**Positive controls** at the pin:

```
AlgebraicTopology.SSet.singularChainComplexFunctor : (C : Type _) → … → C ⥤ SSet ⥤ ChainComplex C ℕ
AlgebraicTopology.singularChainComplexFunctor      : (C : Type _) → … → C ⥤ TopCat ⥤ ChainComplex C ℕ
AlgebraicTopology.singularHomologyFunctor          : (C : Type _) → … → ℕ → C ⥤ TopCat ⥤ C
sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet ;  SSet.toTop ;  TopCat.toSSet
SSet.Subcomplex ;  SSet.HasDimensionLT ;  QuasiIso
```

Committed probe module `RequestProject/Spine/Nerve/Task11Probe.lean` (namespace `SpineTask11`):

* `unitChainComplexMap R K = ((SSet.singularChainComplexFunctor C).obj R).map (sSetTopAdj.unit.app K)`
  — the canonical comparison morphism, constructible **already at the pin**;
* `unitChainComplexMap_target` — its target is, by `rfl`,
  `((SSet.singularChainComplexFunctor C).obj R).obj (TopCat.toSSet.obj (SSet.toTop.obj K))`;
* `unitChainComplexMap_naturality` — naturality in `K` (proved; it is the naturality of the
  unit, and it is all the pin gives);
* `UnitQuasiIsoStatement` — the `Prop` "`unitChainComplexMap` is a quasi-isomorphism",
  deliberately **unproved** and consumed by nothing;
* `taskNine_and_mathlib_share_the_unit` — the Task-9 chain map and the generic Mathlib
  morphism are two linearisations of the *same* morphism `η_K` of simplicial sets.
  This is bookkeeping, **not** the deferred bridge between the two chain complexes.

### 13.2 Upstream research probes (class B)

A separate scratch checkout of `076c9da` (Lean `v4.34.0-rc2`, `lake exe cache get`) was made
**outside** the Lake project; it is not a dependency and is not in any import closure.

* **B1** — the new API elaborates with the expected types:
  `SSet.homology`, `SSet.homologyMap`, `SSetPair.homology`, `SSetPair.homologyδ`,
  `SSetPair.homology_exact₁/₂/₃`, `SSet.normalizedChainComplex`, `SSet.homology₀Iso`,
  `TopCat.singularHomology₀Iso`, `SSet.isZero_homology_of_hasDimensionLT`,
  `SSet.Homotopy.congr_homologyMap`,
  `TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor`,
  `TopPair.HomologyPretheory`, `SSet.sd` — **all present**.
* **B2** — the canonical comparison exists upstream in exactly our shape and compiles:
  ```lean
  noncomputable def unitChainMapUp (R : C) (K : SSet) :
      K.chainComplex R ⟶ (TopCat.toSSet.obj (SSet.toTop.obj K)).chainComplex R :=
    SSet.chainComplexMap (sSetTopAdj.unit.app K) R
  example (R : C) (K : SSet) :
      (TopCat.toSSet.obj (SSet.toTop.obj K)).chainComplex R
        = ((singularChainComplexFunctor C).obj R).obj (SSet.toTop.obj K) := rfl   -- ✓
  ```
  So upstream's own name for `J = C_*(η_K)` is `SSet.chainComplexMap (sSetTopAdj.unit.app K) R`,
  and its homology-level name is `SSet.homologyMap (sSetTopAdj.unit.app K) R n`.
* **B3** (negative) — `QuasiIso (unitChainMapUp R K)` : `failed to synthesize instance`.
* **B4** (negative, library-wide) — with `import Mathlib` at `076c9da`:
  `IsIso (SSet.homologyMap (sSetTopAdj.unit.app K) R n) := by exact?` ⇒
  `` `exact?` could not close the goal. ``

### 13.3 Production build evidence

```
$ lake build RequestProject.Spine.Nerve.Core
… ✔ Built RequestProject.Spine.Nerve.Task11Probe
Build completed successfully (8134 jobs).
```

Full evidence, including the firewall counts, the axiom audit and the other required targets,
is in §16.

---

## 14. WP15 — decision matrix

| Route | Pin | Current upstream `076c9da` | Closes the actual Task-10 map? | New infrastructure that is genuinely new | recommendation |
| --- | --- | --- | --- | --- | --- |
| direct theorem for `η_K` | absent | **absent** (WP5, probes B3/B4) | no | none | `BLOCKED` |
| Quillen / weak-equivalence route | absent; TODO in `SingularSet.lean` | **absent**; same TODO verbatim; no model structure on `SSet` | no | anodyne extensions, `RelativeCellComplex`, Moss pairings (all still short of the model structure) | `BLOCKED` |
| relative homology + skeletal induction | absent | `SSetPair` + LES present; homology of `Δ[n]`, of `∂Δ[n]`, of horns absent; excision absent; compact support absent | no | `SSetPair.homology`, `homologyδ`, `homology_exact₁/₂/₃`, `Skeleton`/`Subcomplex` colimits | `UPGRADE_CANDIDATE` (only if the missing three ingredients are also built) |
| Eilenberg–Steenrod uniqueness | absent | data + homotopy axiom only; **no uniqueness theorem** | no | `TopPair`, `HomologyPretheory` | `REJECT` |
| Dold–Kan / normalization | present (unnormalized ↔ normalized) | plus `SSet.normalizedChainComplex`, `QuasiIso` | no | normalization layer only | `REJECT` |
| subdivision | absent | `sd ⊣ ex` **definitions only**; no simplicial approximation, no `sd`-homology theorem | no | `SSet.sd`, `SSet.ex`, `sdExAdjunction` | `REJECT` (for this task) |
| Acyclic Models | absent | **absent** (no occurrence anywhere in Mathlib) | no | none upstream; a Lean-3 reference implementation exists externally | `NATIVE_NEXT_TASK` |

---

## 15. WP16 — hard decision gate

> ### Outcome C — upstream does not materially shorten the blocker
>
> **Current upstream Mathlib (commit `076c9da2981330e0d1ba84a10afa6544faafa612`) does not
> remove the Task-10 blocker.**

The canonical comparison `C_*(K;ℤ₂) → C_*^sing(|K|;ℤ₂)` remains genuinely unformalized at the
needed level: upstream can now *name* the map (`SSet.chainComplexMap (sSetTopAdj.unit.app K) R`)
and *name* both homologies, but proves nothing about the map beyond naturality.

### 15.1 Selected native route for Task 12

**Acyclic Models remains the preferred native route**, for three reasons: (i) it is the only
route whose every ingredient is a self-contained theorem rather than a large theory (unlike the
model-category route, which requires the Kan–Quillen model structure that upstream itself has
not finished); (ii) its output is exactly the *preferred stronger* endpoint, an explicit
chain-homotopy equivalence, which Task 10 already converted into bijectivity of the existing
`geometricHmap`; (iii) a complete Lean-3 reference decomposition exists
(`Shamrock-Frost/BrouwerFixedPoint`, `DESIGN_REFERENCE` only).

**First route-specific missing theorem** (route-specific, *not* the unique logical blocker):

> **Compact supports in a realisation.**  For every simplicial set `S` and every singular
> simplex `σ : Δⁿ_top → |S|` there is a finite subcomplex `L ≤ S` with `σ` factoring through
> `|L| → |S|`.

### 15.2 Proposed Task-12 dependency DAG

```
T12.1  colimit description of |S| over its finite subcomplexes
         (|·| is a left adjoint, hence preserves the colimit; the topological content is that
          the canonical continuous bijection colim |L| → |S| is a homeomorphism)
   │
   ├── T12.2  compact supports:  every compact subset of |S| meets only finitely many
   │            nondegenerate simplices; hence every σ : Δⁿ_top → |S| factors through some |L|
   │            with L a finite subcomplex                       ← FIRST ROUTE-SPECIFIC THEOREM
   │
T12.3  acyclicity of the models: a natural ℤ₂-chain contraction of C_*^sing(|Δ[n]|)
         onto ℤ₂ in degree 0   (the project's prism operator, Spine/Cohomology/Prism.lean,
         upgraded from a cochain-class statement to a natural chain contraction)
   │
T12.4  freeness of both functors on the models Δ[n]
         (a) C_*^simp(-) is free with basis the simplices              — immediate
         (b) C_*^sing(|-|) is free on the *finite-subcomplex* models   — needs T12.2
   │
T12.5  acyclic-models comparison theorem (native, ℤ₂, over the category SSet):
         two functors free on models and acyclic on models, agreeing in H₀,
         admit natural transformations in both directions, unique up to natural chain homotopy
   │
T12.6  assembly:  Nonempty (NerveGeom.ChainHomotopyEquivData 𝓤)
         = NerveGeom.ChainComparisonStatement 𝓤
   │
T12.7  NerveGeom.geometricHmap_bijective_of_chainHomotopyEquiv   ← ALREADY PROVED (Task 10)
   │
   ▼
∀ n, Function.Bijective (NerveGeom.geometricHmap 𝓤 n)
```

Scope warning carried forward: T12.5 alone is a module-sized development, and T12.1–T12.4 are
each self-contained theorems.  Task 12 should therefore take **T12.1 + T12.2 only**, and
classify T12.3–T12.6 as later tasks.

### 15.3 What was explicitly *not* concluded

* Not concluded that upstream "solves it" (Outcome A) — no theorem exists (§4).
* Not concluded that upstream "materially shortens it" (Outcome B) — the new upstream
  infrastructure duplicates layers the project already owns natively (its own `ℤ₂` chain and
  cochain complexes, its own dualisation, its own cohomology comparison) and supplies **none**
  of the four ingredients that are actually missing (compact support, acyclicity of the models,
  acyclic models, or excision).
* Not concluded that Eilenberg–Steenrod, Dold–Kan, relative homology or the adjunction imply
  the comparison.

---

## 16. Verification evidence

All commands run in the production tree at the pinned toolchain.

```
$ lake build RequestProject.Spine.Nerve.Core          ⇒ Build completed successfully (8134 jobs)
$ lake build RequestProject.Spine.Cohomology.Core     ⇒ Build completed successfully (8065 jobs)
$ lake build RequestProject.Spine.Cech.Core           ⇒ Build completed successfully (8111 jobs)
$ lake build RequestProject.Spine.Geometry.Core       ⇒ Build completed successfully (8088 jobs)
$ lake build RequestProject.Spine.Core                ⇒ Build completed successfully (8189 jobs)
$ lake build RequestProject.Spine.Audit.Firewall      ⇒ Build completed successfully (8198 jobs),
                                                        SPINE FIREWALL AUDIT: all checks passed
$ lake build                                          ⇒ Build completed successfully (8202 jobs)
                                                        (Task 10 reported 8201; +1 is the new probe module)
```

Firewall status (unchanged from Task 10):

```
Spine external-project imports: 0 (prefixes checked: 7)
Spine direct legacy imports:      Experiment1 = 0   Experiment2 = 0
Spine transitive legacy imports:  Experiment1 = 0   Experiment2 = 0
SPINE FIREWALL AUDIT: all checks passed
```

Axiom audit of the five new Task-11 declarations (`#print axioms`, in
`RequestProject/Spine/Nerve/Core.lean`):

```
SpineTask11.unitChainComplexMap                 : [propext, Classical.choice, Quot.sound]
SpineTask11.unitChainComplexMap_target          : [propext, Classical.choice, Quot.sound]
SpineTask11.unitChainComplexMap_naturality      : [propext, Classical.choice, Quot.sound]
SpineTask11.UnitQuasiIsoStatement               : [propext, Classical.choice, Quot.sound]
SpineTask11.taskNine_and_mathlib_share_the_unit : [propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, project-local `axiom`, `unsafe`, `partial` or `implemented_by` was added.
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json` are byte-identical to their Task-10
state.  The upstream checkout at `076c9da` lives outside the project and is documented here and
in `TASK11_EXTERNAL_SOURCES.md` only.

Failbuild ledger: no build failure occurred during Task 11 (`TASK10_FAILBUILDS.md` is preserved
unchanged and append-only).

---

## 17. Final questions, answered exactly

**What exact upstream Mathlib commit was audited against the production v4.28.0 pin?**
`076c9da2981330e0d1ba84a10afa6544faafa612` (branch `master`, committed 2026-09-09T03:44:13Z,
toolchain `leanprover/lean4:v4.34.0-rc2`), audited against
`8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`, 2026-02-16), 6002 commits apart.

**Does current upstream contain a theorem proving that `η_K : K → Sing|K|` induces an
isomorphism on homology or cohomology?**
**No.**  It contains the map (`SSet.chainComplexMap (sSetTopAdj.unit.app K) R`,
`SSet.homologyMap (sSetTopAdj.unit.app K) R n`) and nothing about it except naturality.  A
library-wide `exact?` on `IsIso (SSet.homologyMap (sSetTopAdj.unit.app K) R n)` fails.

**Is the realization–singular adjunction currently known in Mathlib to be a Quillen
equivalence?**
**No.**  `Mathlib/AlgebraicTopology/SingularSet.lean` at `076c9da` still lists both "the
singular simplicial set is a Kan complex" and "`sSetTopAdj` is a Quillen equivalence" as
TODOs, verbatim as in the pin; and there is still no Kan–Quillen model structure on `SSet`.

**What new relative-homology and Eilenberg–Steenrod infrastructure exists upstream that was
absent from the pin?**
Relative: `SSetPair`, `SSetPair.chainComplex/homology/homologyπ/homologyδ`,
`shortExact_chainComplexShortComplex`, `homology_exact₁/₂/₃`, `SSet.Subcomplex.pair`
(PR #41285).  Eilenberg–Steenrod: `TopPair` (PR #36621) and `TopPair.HomologyPretheory` with
its category structure and the single class `IsHomotopyInvariant` (PR #39236).  Also, though
not asked: `SSet.homology`, homotopy invariance on both sides, `H₀` computations,
`normalizedChainComplex`, and the `sd ⊣ ex` subdivision adjunction.

**Does any of it materially shorten the proof for the actual existing Task-10 map
`geometricHmap_{K,n}`?**
**No.**  There is no dependency chain from any of it to a statement about `C_*(η_K)`.  What it
would shorten are layers the project already owns natively.  Classification:
`NO_MATERIAL_SHORTENING`.

**Is Dold–Kan still normalization-only for this problem?**
**Yes** — `UNCHANGED_NORMALIZATION_ONLY`.  The new `SSet.normalizedChainComplex` work is a
statement about one simplicial set, not about `K → Sing|K|`.

**If upstream does not solve the problem, what is the shortest currently credible native
route?**
Acyclic Models over `SSet` with models `Δ[n]`, in `ℤ₂`, producing the explicit
chain-homotopy-equivalence datum `NerveGeom.ChainHomotopyEquivData 𝓤` that Task 10 already
converts into bijectivity of `geometricHmap`.  DAG in §15.2.

**On that selected route, what is the first route-specific missing theorem?**
The compact-support / finite-subcomplex theorem: every singular simplex `Δⁿ_top → |S|` factors
through `|L|` for some finite subcomplex `L ≤ S` (T12.2, resting on the colimit description
T12.1).  It is route-specific, **not** the unique logical blocker.

**Would backporting the useful upstream delta be smaller than upgrading the entire project?**
Yes, strictly smaller (`MEDIUM_INFRASTRUCTURE_DELTA` versus `HIGH_RISK` for the full upgrade),
but both are **not recommended**, because neither yields the missing theorem.

> ### Final classification
>
> **C: NO MATERIAL SHORTENING**

**Exact Task-12 recommendation.**  Keep the pin.  Do not backport, do not upgrade.  Task 12 =
`T12.1` (the colimit description of `|S|` over its finite subcomplexes) **plus** `T12.2` (the
compact-support theorem), stated natively over `ℤ₂` for the existing
`NerveGeom.coverNerveSSet`/`coverNerveRealization`, with `T12.3`–`T12.6` deferred and named as
later tasks.  Nothing downstream of `NerveGeom.ChainComparisonStatement` needs to change: the
Task-10 conversion `geometricHmap_bijective_of_chainHomotopyEquiv` is already proved.
