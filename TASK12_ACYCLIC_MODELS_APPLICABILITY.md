# Task 12 — Acyclic-Models Applicability Audit and Proof-Route Gate

**Decision: `B — FORWARD ONLY; REVERSE ROUTE REQUIRED`.**
**Verdict on the central question (WP9): `ONLY_FORWARD_MAP_F_TO_G`.**

The audit is complete, the applicability question is settled, and it is settled *negatively for
the direction we need*. Standard Acyclic Models applies to the pair of functors fixed by Tasks
9–11 in the direction `F → G` only. That direction produces (and characterises up to natural
chain homotopy) exactly the map the project already owns,

```
J = C_*(η_K) : C_*^simp(K;ℤ₂) ⟶ C_*^sing(|K|;ℤ₂),          K = N(𝓤),
```

and it cannot construct the missing reverse map `R : G → F`. No repair by a larger model class
is available: the obstruction is a cardinality obstruction that rejects **every countable class
of models with finitely many vertices** at once, and the two candidate classes named in the task
(`{Δ[n]}`, finite simplicial sets) are additionally rejected — the second one twice over, since
finite simplicial sets are not even acyclic.

Everything asserted here as *proved* is proved in
`RequestProject/Spine/Nerve/Task12Probe.lean`, `sorry`-free, with axioms
`[propext, Classical.choice, Quot.sound]` only. Statements that are classical but **not**
formalised in this task are labelled `THEOREM_LEVEL (not formalised)`; nothing in the production
Spine consumes them.

Production was not touched: `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` are
unchanged, no external project is imported, and the new module is a leaf that nothing depends
on.

---

## WP1 — The exact Acyclic-Models theorem needed

We use the classical Eilenberg–MacLane theorem in the form standard in textbooks (Rotman,
*An Introduction to Algebraic Topology*, ch. 9, Thm. 9.12; Barr, *Acyclic Models*, CRM
Monograph 17). Every hypothesis is instantiated below; the phrase "Acyclic Models applies" is
never used without that instantiation.

### Data

| item | content |
| --- | --- |
| source category | an arbitrary category `𝒞` (here: `SSet`, see WP2) |
| target category | non-negatively graded chain complexes of `R`-modules, `Ch_{≥0}(R\text{-Mod})`, `R = ℤ₂` |
| models | a *set* `𝓜 ⊆ Ob 𝒞` (variant: an indexed family, models may repeat) |
| functors | `A, B : 𝒞 ⟶ Ch_{≥0}(R\text{-Mod})`, often augmented over a common functor `ε : (−) ⟶ R` |

### Free on models

`A` is **free on `𝓜` in degree `q`** if there is an index set `J_q`, models `M_j ∈ 𝓜` and
elements `m_j ∈ A_q(M_j)` (`j ∈ J_q`) such that for **every** object `K` of `𝒞` the family

```
{ A(f)(m_j)  |  j ∈ J_q,  f ∈ Hom_𝒞(M_j, K) }
```

is an `R`-**basis** of `A_q(K)`. Two weaker variants occur in the literature: *generated* on
models (the family spans) and *presentable/projective* on models. All three require, in
particular, that the indexing map

```
⨆_{j ∈ J_q} Hom_𝒞(M_j, K)  ⟶  (basis / generating set of) A_q(K)
```

be **surjective onto the basis of the free module** `A_q(K)` whenever `A_q(K)` is itself free on
a natural set of generators. That necessary condition is the one refuted in WP3 and WP5; it is
recorded formally as `SpineTask12.surjective_of_span_singles` (if the singletons indexed by a
family span the free module on a set `S`, the family is surjective onto `S`), so the
counterexamples below defeat even the weakest, "generated on models" variant.

### Acyclic on models

`B` is **acyclic on `𝓜`** if `H_q(B(M)) = 0` for all `q > 0` and all `M ∈ 𝓜`. In the
*augmented* variant one asks that the augmented complex `⋯ → B_0(M) →^ε R → 0` be acyclic,
i.e. additionally `H_0(B(M)) ≅ R` via the augmentation.

### Conclusions

* **(Extension.)** If `A` is free on `𝓜` in every degree `q > 0` and `B` is acyclic on `𝓜`,
  then every natural transformation `A_0 → B_0` commuting with the augmentations (equivalently:
  every natural chain map defined in degrees `< n`) extends to a natural chain map `A → B`.
* **(Uniqueness.)** Under the same hypotheses any two natural chain maps `A → B` that agree in
  degree `−1`/`0` (on augmentations) are naturally chain homotopic.
* **(Equivalence — the *corollary*, not the theorem.)** If `A` and `B` are **both** free on `𝓜`
  and **both** acyclic on `𝓜`, and both are augmented over the same functor with the
  augmentation-degree comparison an isomorphism, then a natural transformation `A → B`
  extending the identity is a natural chain **homotopy equivalence**: one applies the extension
  theorem twice (once in each direction) and the uniqueness theorem twice.

### The asymmetry, stated explicitly

For a natural transformation `A → B`:

| role | required hypothesis |
| --- | --- |
| **domain** functor `A` | *free on the models* |
| **codomain** functor `B` | *acyclic on the models* |

Hence:

* to build `F → G` one needs `F` free and `G` acyclic;
* to build `G → F` one needs **`G` free** and `F` acyclic;
* to get a chain homotopy equivalence one needs **all four** conditions.

These are not symmetric and must not be assumed to be.

---

## WP2 — The two functors, fixed exactly

The category of inputs is the project's actual simplicial-set category, Mathlib's
`SSet = Δᵒᵖ ⥤ Type u`, in which `NerveGeom.coverNerveSSet 𝓤` lives (Task 9, WP2).

| functor | definition in the project | file |
| --- | --- | --- |
| `F(K) = C_*^simp(K;ℤ₂)` | `NerveGeom.SSetChain K n = K_n →₀ ℤ₂`, boundary `NerveGeom.sSetBoundary K n = ∑ᵢ (dᵢ)_*` | `Nerve/UnitChainMap.lean` |
| `G(K) = C_*^sing(\|K\|;ℤ₂)` | `NerveGeom.SSetChain (TopCat.toSSet.obj (SSet.toTop.obj K))`, same construction applied to `Sing\|K\|` | `Nerve/UnitChainMap.lean` (`singBoundary_eq`) |
| `J` | `NerveGeom.chainMap 𝓤 n = NerveGeom.sSetChainMap (sSetTopAdj.unit.app K) n`, i.e. `C_*(η_K)` (Task 10, `chainMap_eq_unitChainMap`, by `rfl`) | `Nerve/ChainMap.lean`, `Nerve/UnitChainMap.lean` |

`G` is **not** replaced by singular chains on an arbitrary topological space, `K` is **not**
replaced by `Sing|K|`, and `J` is left exactly as Task 10 fixed it. Both `F` and `G` are
functors `SSet ⟶ Ch_{≥0}(ℤ₂\text{-Mod})` (functoriality of `F` and of `G` is
`sSetBoundary_naturality`, Task 10), and both are augmented over `ℤ₂` by the sum-of-coefficients
map in degree `0`.

---

## WP3 — Model class A: the standard simplices `𝓜_Δ = {Δ[n] | n ≥ 0}`

### `F` is free on `𝓜_Δ` — `FREE_ON_MODELS` (proved)

By Yoneda, `Hom_{SSet}(Δ[q], K) ≃ K_q` naturally in `K`
(`SpineTask12.freeOnStdSimplex_bijective`, from `SSet.yonedaEquiv`), and `F_q(K)` is by
definition the free `ℤ₂`-module on `K_q`. Taking `J_q = {*}`, `M_* = Δ[q]`, `m_* = ι_q` the
fundamental `q`-simplex, the model images are exactly the basis:

* `SpineTask12.simpChain_model_generator` — `F(f)(single ι_q 1) = single (f(ι_q)) 1`, so the
  generators really are of the required form `A(f)(m_j)`;
* `SpineTask12.simpChain_model_span` — those generators span `F_q(K)`;
* `SpineTask12.simpChainModelBasis` — the resulting linear isomorphism
  `(Hom(Δ[q],K) →₀ ℤ₂) ≃ₗ F_q(K)`.

### `F` is acyclic on `𝓜_Δ` — `ACYCLIC_ON_MODELS` (proved)

`SpineTask12.stdSimplex_chain_acyclic`: `H_{>0}(F(Δ[n])) = 0`. The proof is the classical cone
contraction, formalised: `coneHom` prepends the vertex `0` to a simplex of `Δ[n]`,
`cone_face_zero` and `cone_face_succ` are the two face identities `d₀h = id`,
`d_{i+1}h = h d_i`, and `cone_chain_homotopy` is the resulting identity `∂h + h∂ = id`
(signs invisible over `ℤ₂`). In degree `0` the same identity gives the augmented statement,
so `F` is acyclic on `𝓜_Δ` in the augmented sense as well.

### `G` is **not** free on `𝓜_Δ` — `MODEL_CLASS_REJECTED`, `COUNTEREXAMPLE` (proved)

A degree-`q` generator produced by the models is
`SpineTask12.singularGenerator K q f = η_K(f(ι_q)) ∈ Sing_q|K|`; freeness (or even generation)
requires this map to be surjective onto the singular `q`-simplices. It is not, already for
`K = Δ[1]`:

* `Hom_{SSet}(Δ[q], Δ[1]) ≃ Δ[1]_q = Hom_Δ([q],[1])` is **finite**;
* `Sing_q|Δ[1]| ≃ C(|Δ^q|, |Δ[1]|)` is **uncountable** — `|Δ[1]|` is homeomorphic to the
  geometric `1`-simplex (`SSet.toTopSimplex`), into which the interval `[0,1]` injects
  (`SpineTask12.segPoint`), and constant maps then give uncountably many singular simplices
  (`SpineTask12.not_countable_simplex`).

Hence `SpineTask12.singularGenerator_not_surjective` and, in the module-theoretic form the
hypothesis actually uses, `SpineTask12.singularGenerator_not_spanning`.

### `G` is acyclic on `𝓜_Δ` — `ACYCLIC_ON_MODELS`

`|Δ[n]|` is contractible: `SpineTask12.realization_stdSimplex_contractible` (it is homeomorphic
to the nonempty convex set `stdSimplex ℝ (Fin (n+1))`). In the project's own singular mod-2
theory this yields vanishing directly, by the Task-8 homotopy invariance:
`SpineTask12.singularCohomology_stdSimplex_vanishing` — `H^{>0}_sing(|Δ[n]|;ℤ₂) = 0` (proved).
The *chain*-level statement `H_{>0}(C_*^sing(|Δ[n]|;ℤ₂)) = 0` is the classical dual and is
`THEOREM_LEVEL (not formalised)` here: the pinned library has no singular-homology
homotopy-invariance theorem (Task 11, WP5), and formalising the singular cone operator on a
convex set was out of scope for a route gate (WP12). This does not affect the verdict, since
the verdict turns on freeness, not on this entry.

### The WP3 matrix

|  | free on `𝓜_Δ` | acyclic on `𝓜_Δ` |
| --- | --- | --- |
| `F = C_*^simp` | **YES** (proved, `freeOnStdSimplex_bijective`) | **YES** (proved, `stdSimplex_chain_acyclic`) |
| `G = C_*^sing ∘ \|−\|` | **NO** (proved, `singularGenerator_not_surjective`) | **YES** (cohomological form proved; chain form classical) |

---

## WP4 — What standard-simplex models actually give

With `F` free and `G` acyclic on `𝓜_Δ`, the theorem of WP1 gives exactly:

1. **existence** of a natural chain map `F → G` extending the degree-`0` comparison, and
2. **uniqueness up to natural chain homotopy** of any such map.

Both concern the direction `F → G`. The project already *has* such a map, namely
`J = C_*(η_K)`; the only new information is the (useful, but not decisive) fact that `J` is the
essentially unique natural augmentation-preserving comparison, so no competing comparison map
can exist up to natural chain homotopy. It is therefore *the* map any future route must
reproduce (WP14).

It gives **nothing** in the direction `G → F`. Constructing `R : G → F` by the same theorem
would require `G` to be free on the same models — refuted in WP3 — and `F` to be acyclic on them
— true, but useless on its own. **This is the central Task-12 endpoint: `FORWARD_ONLY`.**

---

## WP5 — Model class B: finite simplicial sets `𝓜_fin`

1. **Do singular simplices factoring through finite subcomplexes give freeness for `G`?** No.
   Factorisation is a *generation-by-subobjects* statement, not a *basis indexed by
   `Hom(M, K)`* statement (see WP6). Formally, freeness would still require the generating map
   `⨆_{L ∈ 𝓜_fin} Hom_{SSet}(L, K) → Sing_q|K|` to be surjective, and it is not: every finite
   simplicial set has finitely many vertices, a simplicial map into `Δ[m]` is determined by its
   vertex values (`SpineTask12.hom_stdSimplex_ext`), hence `Hom(L, Δ[1])` is finite
   (`SpineTask12.finite_hom_to_stdSimplex`); a countable class of such models gives a countable
   generating family, and no countable family generates `Sing_q|Δ[1]|`
   (`SpineTask12.no_countable_family_generates`, `SpineTask12.countableFiniteModels_not_generating`).
   `MODEL_CLASS_REJECTED`.
2. **Is the factorisation statement strong enough for the exact theorem of WP1?** No — see (1)
   and WP6.
3. **Are all models in `𝓜_fin` acyclic for `F`?** **No.** `COUNTEREXAMPLE`, proved:
   `SpineTask12.boundary2_homology_one_ne_zero`. The model is `∂Δ[2]`, finite in the pinned
   library's own sense (`SpineTask12.circleModel_isFinite`, i.e. `SSet.Finite`), with
   `|∂Δ[2]| ≅ S¹`. The fundamental cycle `z = e₀ + e₁ + e₂` (the three nondegenerate edges,
   i.e. the three faces of the missing `2`-simplex) satisfies `∂z = 0`
   (`boundary_fundamentalCycle`) and is not a boundary: the linear functional
   `edgeFunctional`, "number of nondegenerate edges mod 2", vanishes on `∂C_2`
   (`edgeFunctional_boundary`; the case analysis is exactly the observation that the only
   monotone `[2] → [2]` with three distinct vertices, `(0,1,2)`, is the simplex *removed* from
   `Δ[2]`) while `edgeFunctional z = 1`. So `H₁(F(∂Δ[2]);ℤ₂) ≠ 0`.
4. **Are all models in `𝓜_fin` acyclic for `G`?** No; the same object is the counterexample,
   `H₁^{sing}(|∂Δ[2]|;ℤ₂) = H₁(S¹;ℤ₂) = ℤ₂ ≠ 0`. `THEOREM_LEVEL (not formalised)` — the
   chain-level statement was not formalised because the `F`-side counterexample already rejects
   the class, and rejecting a class needs only one failure.

**Conclusion: finite simplicial sets are not an acyclic model class**, and they do not repair
freeness either. `MODEL_CLASS_REJECTED`.

---

## WP6 — Compact-support claim audit

**Statement.** Every singular simplex `σ : |Δ^n| → |K|` factors through `|L|` for some finite
simplicial subset `L ⊆ K`.

* **True in the generality needed?** Yes, classically. `|Δ^n|` is compact, `|K|` carries the
  colimit topology of its skeletal/cell filtration, and a compact subset of a CW complex meets
  only finitely many open cells; the finitely many cells met are contained in a finite
  subcomplex. Hatcher gives a direct proof of the "compact set meets finitely many open
  simplices" step for Δ-complexes (*Algebraic Topology*, §2.1, inside the proof of Thm. 2.27,
  p. 130); the CW statement for `|K|` is Milnor's theorem that the realisation of a
  semi-simplicial complex is a CW complex with cells the nondegenerate simplices.
* **Hypotheses.** Compactness of `|Δ^n|`; the CW/colimit description of `|K|` (with the
  compactly generated convention for products; not needed for this statement); no Hausdorff or
  finiteness assumption on `K`.
* **In pinned Mathlib?** **No.** The pin has `SSet.toTop`, `TopCat.toSSet`, `sSetTopAdj`
  (`AlgebraicTopology/SingularSet.lean`), CW complexes (`Topology/CWComplex/Classical`),
  `SSet.Finite`, `SSet.skeleton`, `SSet.N` — but **no theorem connecting `SSet.toTop` to
  `CWComplex`**: `SSet.toTop`/`sSetTopAdj` occur in exactly one Mathlib file
  (`AlgebraicTopology/SingularSet.lean`), and it contains no compactness or cell-structure
  result. A native proof would need the CW/colimit structure of `|K|` first, and would use
  compactness of `|Δ^n|`; interiors/stars of simplices would have to be constructed, since the
  pin has none of that for realisations.
* **What it buys.** `G(K) = colim_{L ⊆ K finite} G(L)` (a filtered colimit statement) and, dually,
  a way to reduce a comparison theorem from arbitrary `K` to finite `L`. That is
  **finite-subcomplex factorisation**, and it is *not* **freeness on an acyclic model class**:
  the factorisation is neither unique nor natural in a way that indexes a basis, the
  factorisations of one `σ` form a filtered system rather than a single generator, and the
  singular simplices of `|L|` are themselves not indexed by `Hom_{SSet}(M, L)`. WP5(1) shows the
  gap is not a technicality: it fails by an uncountability argument.
* **Classification: `ROUTE_SPECIFIC_BLOCKER`** — useful for Route K (and as the last step of
  Route C for infinite-dimensional `K`), useless for Acyclic Models.

---

## WP7 — Other candidate model classes

For each class, "free" and "acyclic" are asked of both functors, and the last column says which
direction the class could support.

| model class `𝓜` | `F` free | `F` acyclic | `G` free | `G` acyclic | supports `F→G` | supports `G→F` |
| --- | --- | --- | --- | --- | --- | --- |
| standard simplices `Δ[n]` | **yes** (proved) | **yes** (proved) | **no** (proved) | yes | **yes** | **no** |
| representable simplicial sets | identical to the row above (`Δ[n]` *are* the representables in `SSet`) | | | | yes | no |
| finite simplicial sets | yes (contains the `Δ[n]`) | **no** (proved: `∂Δ[2]`) | **no** (proved) | **no** (`S¹`) | no | no |
| contractible finite simplicial sets | yes | yes (classically; contractible finite complexes) | **no** (proved: countable class, finitely many vertices) | yes | yes | **no** |
| simplicial cones `C(L)` on finite `L` | yes | yes (cone contraction) | **no** (same argument) | yes | yes | **no** |
| subdivisions `Sd^k Δ[n]` | yes | yes | **no** (same argument: finite, countably many) | yes | yes | **no** |
| pairs simplex/boundary `(Δ[n], ∂Δ[n])` | yes (relative freeness) | `∂Δ[n]` **not** acyclic for `n = 2` (proved) | no | no for `∂Δ[n]` | only relatively | no |
| singular complexes `Sing |Δ^n|` | yes | yes (classically) | **no**, see below | yes | yes | **no** |

The last row is the only candidate not covered by the countability theorem (`Sing|Δ^n|` has
uncountably many vertices), and it deserves the explicit argument:

* Freeness of `G` on any class forces, by evaluating at the terminal object `K = Δ[0]`, that the
  index set `J_q` be in bijection with `Sing_q|Δ[0]| = Sing_q(pt)`, a one-element set. So there
  is exactly one model `M_q` and one generator per degree, and freeness says precisely that the
  functor `K ↦ Sing_q|K|` is **representable** by `M_q`.
* `K ↦ Sing_q|K|` is not representable, because a representable functor preserves all limits
  while realisation does not preserve infinite products: a point of `|X|` lies in the interior
  of a unique nondegenerate simplex, of some finite dimension `n`, so its coordinates in
  `∏_{i∈ℕ}|Δ[1]|` take at most `n+2` distinct values, whereas a sequence of points with
  infinitely many distinct parameters in `(0,1)` is an element of `∏_{i∈ℕ} Sing_0|Δ[1]|` not in
  the image of `Sing_0|∏_{i∈ℕ} Δ[1]|`. `THEOREM_LEVEL (not formalised)`.
* Moreover `Hom_{SSet}(Sing|Δ^n|, Δ[1])` has exactly two elements (a simplicial map to the nerve
  of a linear order is determined by its vertex map, and any two points of `Δ^n` are joined by
  paths in both directions, forcing that map to be constant), so this class fails the surjectivity
  test at `K = Δ[1]` as badly as the others.

No model class in the list supports `G → F`. We did **not** admit an artificial model class whose
assumptions restate the desired theorem (e.g. "the class of all `K` for which `J` is an
equivalence").

---

## WP8 — Adjunction does not repair freeness; the circularity

A singular simplex `|Δ^n| → |K|` corresponds under `SSet.toTop ⊣ TopCat.toSSet` to a simplicial
map `Δ[n] → Sing|K|`, and by Yoneda those are exactly the elements of `Sing_n|K|`. The generators
the models can supply are the simplicial maps `Δ[n] → K` — and their images are precisely the
maps `Δ[n] → Sing|K|` that **factor through `η_K`**:

```
SpineTask12.generator_eq_unit_comp :  singularGenerator K q f = yonedaEquiv (f ≫ η_K).
```

So the discrepancy between "what the models generate" and "all singular simplices" **is** the
discrepancy between `K` and `Sing|K|` — i.e. exactly the unresolved unit `η_K`. Using the
adjunction to justify freeness of `G` would therefore assume what is to be proved.
**`CIRCULARITY RECORDED`** (proved, and it is a `rfl`-level identity).

---

## WP9 — Can standard Acyclic Models produce `R : G → F`?

```
ONLY_FORWARD_MAP_F_TO_G
```

Justification, strictly from the matrix: the theorem requires the **domain** functor of the
desired transformation to be free on the models. For `R : G → F` the domain is `G`, and `G` is
not free on `𝓜_Δ` (proved), not free on `𝓜_fin` or on any countable class of models with
finitely many vertices (proved), and not free on `{Sing|Δ^n|}` (WP7). The acyclicity of `F` on
the models, which is the other half of the hypothesis and is proved, is not sufficient by
itself. In the direction actually available, `F → G`, the theorem constructs and characterises
`J = C_*(η_K)`, which the project already has.

We do **not** answer YES on the grounds that "acyclic models is used in proofs of
simplicial–singular comparison": see WP10, where the actual dependency structure of those proofs
turns out to be something else.

---

## WP10 — Audit of classical proofs of `H_*^simp(K) ≅ H_*^sing(|K|)`

Reconstructed dependency structures (not textbook slogans):

* **Hatcher, *Algebraic Topology* (2002), §2.1, Theorem 2.27** (verified from the author's
  official PDF, see the source ledger). Statement: `H_n^Δ(X,A) → H_n(X,A)` is an isomorphism for
  all Δ-complex pairs. Actual ingredients, in order of use:
  1. the long exact sequences of the pairs `(X^k, X^{k-1})` in both theories;
  2. computation of `H_n^Δ(X^k, X^{k-1})` (free on the `k`-simplices) and of
     `H_n(X^k, X^{k-1})` via the characteristic maps `⨆(Δ^k_α, ∂Δ^k_α) → (X^k, X^{k-1})`, which
     induce a homeomorphism of quotients — i.e. **good pairs / quotient (excision-type)
     input**, plus `H_k(Δ^k, ∂Δ^k) ≅ ℤ` generated by the identity map (Hatcher Example 2.23);
  3. **induction on skeleta** and the **five lemma**;
  4. for infinite-dimensional `X`: **compact support** ("a compact set meets only finitely many
     open simplices"), used for surjectivity and injectivity separately;
  5. for `A ≠ ∅`: the five lemma again on the two long exact sequences.
  **No acyclic models anywhere** — the string "acyclic models" does not occur in the book's
  proof of this theorem. `PROOF_ROUTE_REFERENCE`.
* **Milnor (1957), *The geometric realization of a semi-simplicial complex*.** `|K|` is a CW
  complex whose cells are the nondegenerate simplices; this is what makes the skeletal induction
  and the compact-support step available for realisations of simplicial sets (as opposed to
  Δ-complexes). `PROOF_ROUTE_REFERENCE`.
* **May, *Simplicial Objects in Algebraic Topology* (1967).** Same architecture: `|K|` is a CW
  complex and the (normalised) simplicial chain complex is its cellular chain complex; the
  comparison is then cellular-vs-singular homology.
* **Eilenberg–MacLane (1953), *Acyclic Models*.** The theorem itself. Its classical *applications*
  are Eilenberg–Zilber (`C_*(X × Y) ≃ C_*(X) ⊗ C_*(Y)`) and comparisons of theories **defined on
  the same category with the same models**, e.g. ordered vs oriented simplicial chains, or
  cubical vs simplicial singular chains. In every such application both functors are free on the
  models — which is exactly the condition that fails here.
* **Barr, *Acyclic Models* (CRM Monograph 17, 2002; and Canad. J. Math. 48 (1996) 258–273).** The
  modern general form (acyclic classes, presentable functors). Notably, Barr's treatment of the
  singular/simplicial comparison still routes through **simplicial subdivision** — confirming
  that the naive symmetric argument is not available even in the general framework.

**Extra ingredient used by the classical proofs, in one line:** a *geometric* input — either
the CW/skeletal structure of `|K|` with relative homology and excision (Hatcher/May/Milnor), or
subdivision/simplicial approximation (Barr, and the classical simplicial-complex proofs) — never
a second application of naive acyclic models.

---

## WP11 — Comparison of the three post-audit routes

### Route S — subdivision / simplicial approximation

Target: a natural map `C_*^sing(|K|) → C_*^simp(K)` after enough subdivision.

Needed: barycentric subdivision `Sd` of simplicial sets and the natural map `|Sd K| ≅ |K|`; the
last-vertex map `Sd K → K`; a Lebesgue-number/small-simplices argument for singular simplices of
`|K|`; a simplicial approximation theorem for maps `|Δ^q| → |K|`; naturality of all of it in `K`;
and chain homotopies comparing subdivision with the identity. Pinned support: **none** (no `SSet.sd`
at the pin — recorded as a negative control in Task 11; no simplicial approximation; no Lebesgue
number for realisations). Structural size: largest of the three; it needs both a new subdivision
theory and a new approximation theorem, and the approximation step is not natural on the nose
(only up to homotopy), which multiplies the bookkeeping.

### Route K — compact support + finite case + filtered colimit

Target: `K = colim_{L ⊆ K finite} L`, `G(K) = colim_L G(L)`, then the comparison for finite `L`.

Needed: the compact-support theorem of WP6 (itself resting on the CW structure of `|K|`);
commutation of homology with filtered colimits; and **the finite case**, which is *not* free —
for finite `L` one still needs a genuine comparison theorem, i.e. Route C on a finite complex.
So Route K is a *reduction step*, not a route: it removes the infinite-dimensionality, nothing
else. Pinned support: `SSet.Finite`, `SSet.skeleton`, `SSet.N` exist; the CW structure of `|K|`
and homology-commutes-with-filtered-colimits do not.

### Route C — skeletal / cellular comparison  ⟵ **recommended**

Target: compare `H_n(K^{(r)}, K^{(r-1)})` with `H_n(|K^{(r)}|, |K^{(r-1)}|)` and induct.

Needed: relative simplicial (co)homology; relative singular (co)homology; the long exact
sequences of a pair on both sides; the computation of the relative groups of
`(Δ^r, ∂Δ^r)`; an excision/good-pair input identifying `H_*(|K^{(r)}|,|K^{(r-1)}|)` with a
wedge of `(Δ^r, ∂Δ^r)`'s; the five lemma; and, for infinite-dimensional `K`, the compact-support
step of Route K. Pinned support: `SSet.skeleton` (skeletal filtration by subcomplexes) and
`SSet.Subcomplex` exist and are usable *today*; the project already owns singular mod-2
cohomology with homotopy invariance and vanishing on contractible spaces (Task 8), the
`(Δ^r, ∂Δ^r)` models (this task: contractibility of `|Δ[n]|`, acyclicity of `C_*^simp(Δ[n])`,
the `∂Δ[2]` computation), and the dualisation machinery (Task 10). Missing: relative theory,
long exact sequences, excision, five lemma.

Route C is recommended because it is the architecture of the standard published proof (WP10),
because its first two layers (relative groups and the long exact sequence of a pair for the
project's own mod-2 theories) are self-contained homological algebra with no new topology, and
because its geometric input is concentrated in exactly two theorems (the `(Δ^r,∂Δ^r)`
computation and the quotient/excision identification), rather than spread over a subdivision
theory.

---

## WP12 — Scope compliance

Implemented (permitted): explicit freeness statements; exact representability/Yoneda lemmas; a
small formal counterexample; contractibility and acyclicity checks; compile probes
(`SSet.skeleton`, `SSet.Finite`); a tiny categorical adapter (`singularGenerator`).

Not implemented (correctly deferred): acyclic-models infrastructure, barycentric subdivision,
simplicial approximation, singular excision, cellular homology, general filtered-colimit
homology, the comparison theorem itself.

---

## WP13 — Formal counterexample: why `Hom_{Top}(|Δ^n|, |K|)` is much larger

`Hom_{SSet}(Δ[n], K) ≃ K_n` classifies *simplicial* `n`-simplices — a combinatorial set,
finite whenever `K` has finitely many `n`-simplices. `Hom_{Top}(|Δ^n|, |K|)` contains **all**
continuous maps. Concretely, for `K = Δ[1]` and `n = 0`:

* the simplicial side has exactly two elements (the two vertices of `Δ[1]`);
* the topological side is the point set of `|Δ[1]| ≅ [0,1]`, which is uncountable
  (`SpineTask12.not_countable_realization_one`, via the explicit injection
  `t ↦ (t, 1-t)` of `[0,1]` into the geometric `1`-simplex).

Explicit singular simplex not of the form `|f|` for a simplicial `f`: the constant map
`|Δ^0| → |Δ[1]|` at the barycentre `(1/2, 1/2)` — the realisations of the two simplicial
vertices are the two endpoints, so this constant map is not one of them. In higher degrees the
same holds for every point of the open interval, and for `n ≥ 1` also for every non-affine path.
This is a construction, not a cardinality heuristic; the cardinality statement is then used only
to get the *uniform* result "no countable family suffices".

---

## WP14 — Protection of the Task-10 result

Nothing in this task replaces, weakens or competes with `J = C_*(η_K)`. On the contrary, WP4
strengthens its status: on the standard-simplex models the Acyclic-Models uniqueness clause says
that any natural augmentation-preserving chain map `F → G` is naturally chain homotopic to `J`,
so **no alternative comparison map can be introduced**. Any future route must end at bijectivity
of the existing `NerveGeom.geometricHmap 𝓤 n`, and must prove that its comparison is `J` or is
theorem-level chain homotopic to it. The Task-9/10 declarations were not edited.

---

## WP15 — Decision gate

```
┌──────────────────────────────────────────────┐
│  B :  FORWARD ONLY — REVERSE ROUTE REQUIRED  │
└──────────────────────────────────────────────┘
```

Outcome A (validated) is refuted: no common model class satisfies the four conditions. Outcome C
(another class repairs the reverse direction) is refuted for every class audited, by a single
uniform obstruction plus the `Sing|Δ^n|` argument. Outcome D is not needed: the route selection
*is* decided, in favour of **Route C (skeletal/cellular)**, with Route K's compact-support
theorem as its final step for infinite-dimensional `K`.

Naive symmetric Acyclic Models is therefore **`ROUTE_REJECTED`**; Route C is
**`ROUTE_VALIDATED` (as the recommendation for Task 13, not as a proved theorem)**.

---

## WP16 — Required decision matrices

### Model classes

| Model class | `F` free | `F` acyclic | `G` free | `G` acyclic | Builds `J`? | Builds `R`? |
| --- | --- | --- | --- | --- | --- | --- |
| `Δ[n]` | yes (proved) | yes (proved) | **no** (proved) | yes (cohomological form proved) | yes (already have it) | **no** |
| finite `SSet` | yes | **no** (proved, `∂Δ[2]`) | **no** (proved) | **no** (`S¹`) | no | **no** |
| contractible finite `SSet` | yes | yes | **no** (proved) | yes | yes | **no** |
| `Sing|Δ^n|` (other candidate) | yes | yes | **no** (non-representability) | yes | yes | **no** |

### Proof routes

| Proof route | Main missing theorem | Current Mathlib/project support | Estimated infrastructure (structural) | Recommendation |
| --- | --- | --- | --- | --- |
| naive Acyclic Models | freeness of `G` on models — **false** | — | — | **rejected** (`ROUTE_REJECTED`) |
| subdivision / simplicial approximation | simplicial approximation for `|Δ^q| → |K|`, natural up to homotopy | none at the pin (`SSet.sd` absent) | new subdivision theory + approximation theorem + comparison homotopies (≥ 3 independent layers, each large) | not recommended |
| compact support + finite case | compact subsets of `|K|` meet finitely many cells; homology commutes with filtered colimits | `SSet.Finite`, `SSet.skeleton`; no CW structure on `|K|` | 2 layers, but leaves the finite case = Route C | adopt as the **final step** of Route C, not as a route |
| **skeletal / cellular comparison** | relative theories + LES of a pair + `(Δ^r,∂Δ^r)` + excision/good pairs + five lemma | `SSet.skeleton`, `SSet.Subcomplex`, project's mod-2 cohomology with homotopy invariance (Task 8), `Δ[n]`-acyclicity and `|Δ[n]|`-contractibility (this task), dualisation (Task 10) | 4 layers, two of them pure homological algebra | **recommended for Task 13** |
| other (upstream import) | a quasi-isomorphism theorem for `η_K` | absent upstream (Task 11) | — | rejected (Task 11) |

Sizes are structural dependency counts, not wall-clock estimates.

---

## WP17 — Source ledger

See `TASK12_EXTERNAL_SOURCES.md` for the full ledger with authors, titles, editions, exact
sections, identifiers, access dates and influence classification. Summary: Hatcher §2.1
Thm. 2.27 (`PROOF_ROUTE_REFERENCE`, verified verbatim), Eilenberg–MacLane 1953
(`THEOREM_STATEMENT_REFERENCE`), Rotman ch. 9 Thm. 9.12 (`THEOREM_STATEMENT_REFERENCE`),
Barr 1996/2002 (`THEOREM_STATEMENT_REFERENCE`), Milnor 1957 (`PROOF_ROUTE_REFERENCE`),
May 1967 (`BACKGROUND_ONLY`), pinned Mathlib modules (`MATHLIB_API_REFERENCE` and
`NEGATIVE_CONTROL`). No external formalisation was imported; the firewall is unchanged.

---

## WP18 — Verification

Commands run at the end of the task, all green:

```
lake build RequestProject.Spine.Nerve.Core          → Build completed successfully (8134 jobs)
lake build RequestProject.Spine.Cohomology.Core     → Build completed successfully (8065 jobs)
lake build RequestProject.Spine.Cech.Core           → Build completed successfully (8111 jobs)
lake build RequestProject.Spine.Core                → Build completed successfully (8189 jobs)
lake build RequestProject.Spine.Audit.Firewall      → SPINE FIREWALL AUDIT: all checks passed
lake build                                          → Build completed successfully (8203 jobs)
```

Import discipline (`python3 scripts/legacy_audit.py`, `RESULT: PASS`):

```
Experiment1 direct imports     = 0
Experiment1 transitive imports = 0
Experiment2 direct imports     = 0
Experiment2 transitive imports = 0
external-project imports       = 0
```

`RequestProject/Spine/Nerve/Task12Probe.lean` has exactly two imports, both project-internal
(`Nerve.UnitChainMap`, `Cohomology.HomotopyInvariance`), and contains no `sorry`, `admit`,
project-local `axiom`, `unsafe`, `partial` or `implemented_by` (mechanical scan: no matches).

**Axiom audit.** `#print axioms` was run on every new declaration —
`span_singles_top`, `surjective_of_span_singles`, `freeOnStdSimplex_bijective`,
`simpChainModelBasis`, `simpChain_model_generator`, `simpChain_model_span`, `singularGenerator`,
`generator_eq_unit_comp`, `segPoint`, `segPoint_injective`, `not_countable_Icc`,
`realizationOneHomeo`, `not_countable_realization_one`, `not_countable_simplex`,
`no_countable_family_generates`, `hom_stdSimplex_ext`, `finite_hom_to_stdSimplex`,
`singularGenerator_not_surjective`, `singularGenerator_not_spanning`,
`countableFiniteModels_not_generating`, `coneHom`, `coneHom_apply_zero`, `coneHom_apply_succ`,
`cone_face_zero`, `cone_face_succ`, `coneSimplex`, `coneChain`, `coneChain_single`,
`cone_chain_homotopy`, `stdSimplex_chain_acyclic`, `realizationHomeo`,
`realization_stdSimplex_contractible`, `singularCohomology_stdSimplex_vanishing`, `circleModel`,
`circleModel_finite`, `circleModel_isFinite`, `edge`, `edgeWeight`, `edgeFunctional`,
`edgeFunctional_boundary_single`, `edgeFunctional_boundary`, `fundamentalCycle`,
`edgeFunctional_fundamentalCycle`, `boundary_fundamentalCycle`,
`boundary2_homology_one_ne_zero`, `skeletalFiltration`, `acyclicModels_forward_only` —
and **every one** reports `[propext, Classical.choice, Quot.sound]`.

The failbuild ledger is `TASK12_FAILBUILDS.md` (append-only).

---

## Task-13 recommendation and dependency DAG

**Task 13 = Route C, layer by layer.** Nothing below assumes a new comparison map: the target is
still bijectivity of `NerveGeom.geometricHmap 𝓤 n` for `J = C_*(η_K)`.

```
                       ┌─────────────────────────────────────────────┐
                       │ L0  (already owned)                          │
                       │  • J = C_*(η_K)                    [Task 10] │
                       │  • dualisation, geometricHmap      [Task 10] │
                       │  • mod-2 singular cohomology,                │
                       │    homotopy invariance, contractible ⇒ 0     │
                       │                                     [Task 8] │
                       │  • F free & acyclic on Δ[n],                 │
                       │    |Δ[n]| contractible             [Task 12] │
                       │  • SSet.skeleton / Subcomplex / Finite  [pin]│
                       └───────────────┬─────────────────────────────┘
                                       │
        ┌──────────────────────────────┴──────────────────────────────┐
        │                                                             │
┌───────▼─────────────────────────┐                    ┌──────────────▼──────────────────┐
│ L1a  relative simplicial mod-2  │                    │ L1b  relative singular mod-2    │
│   chains/cochains of a pair     │                    │   chains/cochains of a pair     │
│   (K, K') for K' ⊆ K a          │                    │   (X, A), A ⊆ X                 │
│   subcomplex; short exact       │                    │   short exact sequence of       │
│   sequence of complexes         │                    │   complexes                     │
└───────┬─────────────────────────┘                    └──────────────┬──────────────────┘
        │                                                             │
        └──────────────────────────────┬──────────────────────────────┘
                                       │
                        ┌──────────────▼───────────────────┐
                        │ L2  long exact sequence of a      │
                        │  pair, both theories (pure        │
                        │  homological algebra: snake/      │
                        │  connecting map)                  │
                        └──────────────┬───────────────────┘
                                       │
        ┌──────────────────────────────┴──────────────────────────────┐
        │                                                             │
┌───────▼────────────────────────────┐          ┌─────────────────────▼─────────────────┐
│ L3a  the model computation          │          │ L3b  excision / good-pair step:       │
│  H_*(Δ[r], ∂Δ[r]) and               │          │  ⨆_α (|Δ^r_α|,|∂Δ^r_α|) → (|K^{(r)}|, │
│  H_*(|Δ^r|,|∂Δ^r|), free on the     │          │  |K^{(r-1)}|) induces an isomorphism  │
│  r-simplices; generated by the      │          │  (via the homeomorphism of quotients) │
│  characteristic maps                │          │                                       │
└───────┬────────────────────────────┘          └─────────────────────┬─────────────────┘
        │                                                             │
        └──────────────────────────────┬──────────────────────────────┘
                                       │
                        ┌──────────────▼───────────────────┐
                        │ L4  five lemma + induction on r:  │
                        │  J is an isomorphism on           │
                        │  H_*(K^{(r)}) for all r           │
                        └──────────────┬───────────────────┘
                                       │
                        ┌──────────────▼───────────────────┐
                        │ L5  compact support (WP6):        │
                        │  every singular simplex of |K|    │
                        │  lands in some |K^{(r)}|;         │
                        │  pass to the colimit              │
                        └──────────────┬───────────────────┘
                                       │
                        ┌──────────────▼───────────────────┐
                        │ L6  assembly: ChainComparison-    │
                        │  Statement 𝓤  ⇒  geometricHmap    │
                        │  𝓤 n bijective   [Task 10 owns    │
                        │  this implication already]        │
                        └──────────────────────────────────┘
```

L1a, L1b and L2 are independent of any new topology and can be done first; L3b is the single
hardest geometric input and should be scoped before L3a/L4 are attempted; L5 may be postponed by
restricting attention first to finite-dimensional nerves.

---

## Endpoint classification

| endpoint | classification |
| --- | --- |
| `F` free on `Δ[n]` | `FREE_ON_MODELS` (proved) |
| `F` acyclic on `Δ[n]` | `ACYCLIC_ON_MODELS` (proved) |
| `G` acyclic on `Δ[n]` | `ACYCLIC_ON_MODELS` (cohomological form proved; chain form theorem-level) |
| `G` free on `Δ[n]` | `COUNTEREXAMPLE`, `MODEL_CLASS_REJECTED` (proved) |
| `𝓜_fin` acyclic | `COUNTEREXAMPLE`, `MODEL_CLASS_REJECTED` (proved) |
| every countable class with finitely many vertices | `MODEL_CLASS_REJECTED` (proved) |
| `{Sing|Δ^n|}` | `MODEL_CLASS_REJECTED` (theorem-level) |
| acyclic-models direction available | `FORWARD_ONLY`, `NEGATIVE_RESULT` |
| reverse map `R` by acyclic models | `NO_FOR_THE_REQUIRED_REVERSE_MAP` |
| compact-support theorem | `ROUTE_SPECIFIC_BLOCKER`, `DEFERRED` |
| naive acyclic models route | `ROUTE_REJECTED` |
| subdivision route | `ROUTE_SPECIFIC_BLOCKER` |
| skeletal/cellular route | `ROUTE_VALIDATED` (recommended; not yet proved) |
| chain-level comparison for `J` | still `BLOCKED` (unchanged from Task 10) |

---

## Final questions, answered exactly

1. **Is `F(K) = C_*^simp(K;ℤ₂)` free on the standard simplex models `Δ[n]`?**
   **Yes** — proved (`freeOnStdSimplex_bijective`, `simpChain_model_span`).
2. **Is `G(K) = C_*^sing(|K|;ℤ₂)` free on the same models?**
   **No** — proved, with an explicit counterexample at `K = Δ[1]` in every degree
   (`singularGenerator_not_surjective`).
3. **Are both functors acyclic on those models in positive degrees?**
   **Yes.** `F`: proved by the cone contraction. `G`: `|Δ[n]|` is contractible (proved) and the
   positive-degree singular mod-2 cohomology vanishes (proved); the chain-level dual is
   classical.
4. **Which direction of Acyclic Models is available?**
   **`F → G` only.**
5. **Does that direction give anything beyond `J = C_*(η_K)`?**
   Only the uniqueness clause: any natural augmentation-preserving chain map `F → G` is naturally
   chain homotopic to `J`. No new map, and in particular no reverse map.
6. **Does finite-subcomplex factorisation repair the missing freeness?**
   **No.** It is a filtered-colimit/generation statement, not a basis indexed by
   `Hom_{SSet}(M, K)`; the freeness failure is by uncountability and survives it.
7. **Are finite simplicial sets an acyclic model class? If not, the counterexample.**
   **No.** `∂Δ[2]` — a finite simplicial set with `|∂Δ[2]| ≅ S¹` — has
   `H₁(C_*^simp(∂Δ[2];ℤ₂)) ≠ 0`, proved formally by exhibiting the cycle `e₀ + e₁ + e₂` and the
   linear functional "nondegenerate-edge count mod 2" that kills all boundaries but not the
   cycle.
8. **Is there another explicit model class making the reverse construction valid?**
   **No** — every audited class fails, and a uniform argument (evaluation at the terminal object
   forces representability of `K ↦ Sing_q|K|`, which fails) shows the failure is structural.
9. **Which route is now the shortest justified one?**
   **Skeletal/cellular comparison (Route C)**, with the compact-support step of Route K as its
   final layer. Subdivision/simplicial approximation is strictly larger; compact support alone is
   only a reduction.
10. **Final choice.**

```
┌──────────────────────────────────────────────┐
│  B :  FORWARD ONLY — REVERSE ROUTE REQUIRED  │
└──────────────────────────────────────────────┘
```
