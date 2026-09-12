# TASK 08 — Native homotopy invariance of singular mod-2 cohomology, and comparison-interface hardening

**Status summary.**  The primary objective closes.  Homotopic maps induce the *same* pullback
on the Task-5 singular mod-2 cohomology, in **every degree**, and the proof is a genuine
prism/chain-homotopy construction carried out inside the Task-5 model.  The two remaining
Task-7 comparison interfaces are not proved (that was an explicit non-goal) but they are now
*hardened*: neither can any longer be satisfied by an arbitrary space or an arbitrary linear
isomorphism.

| Work package | Result | Classification |
| --- | --- | --- |
| WP1 audit of Task-5 `Hmap` functoriality | done, §1; `Hmap_id`, `Hmap_comp` confirmed theorem-level with contravariant order | — |
| WP2 Mathlib homotopy/prism audit | done, §2 | — |
| WP3 singular prism operator | `Mod2Cohomology.prismPiece`, `prism`, `prismK` — the standard prism, built natively | `CHAIN_HOMOTOPY`, `DERIVED_NATIVE` |
| WP4 characteristic-two sign audit | `Mod2Cohomology.CharTwo.*`, `alternating_coboundary_eq_coboundary`, visible in the dependency graph | `DERIVED_NATIVE` |
| WP5 cochain homotopy | `Mod2Cohomology.cochainHomotopy`, `cochainHomotopy_zero` | `CHAIN_HOMOTOPY` |
| WP6 equality on cocycles mod coboundaries | `Mod2Cohomology.pullback_add_pullback_mem_coboundaries` — consumes `δα = 0` | `DERIVED_NATIVE` |
| WP7 main theorem | `Mod2Cohomology.Hmap_eq_of_homotopy` / `Hmap_eq_of_homotopic`, **all degrees** | `HOMOTOPY_INVARIANT` |
| WP8 homotopy-equivalence isomorphism | `Mod2Cohomology.homotopyEquivCohomology`, built from `Hmap` in both directions | `COHOMOLOGY_ISOMORPHISM` |
| WP9 contractible-space corollary | `Mod2Cohomology.cohomology_succ_eq_zero_of_contractible` (all `n > 0`), plus degrees 1 and 2 | `DERIVED_NATIVE` |
| WP10 good cover ⇒ acyclic | `GoodCoverZ2.isAcyclicCover_of_isGoodCover`, now **unconditional** | `GOOD_COVER_ACYCLIC` |
| WP11 provisional homotopy-invariance interface | `GoodCoverSpec.nativeHomotopyInvariance` inhabits it from the theorem; the structure is retained and relabelled | `SUPERSEDED` |
| WP12 nerve-realization interface | `GoodCoverSpec.NervePresentation`, `NerveRealizationSpec` | `SPECIFICATION_HARDENED`, `BLOCKED_PENDING_GEOMETRIC_REALIZATION` |
| WP13 simplicial-to-singular interface | `GoodCoverSpec.SimplicialSingularCochainMap`, `SimplicialSingularComparisonSpec` | `SPECIFICATION_HARDENED`, `BLOCKED` |
| WP14 Čech→singular DAG | §9; exactly one blocked edge removed | — |

New Lean modules (6):

```
RequestProject/Spine/Cohomology/CharTwo.lean            (WP4)
RequestProject/Spine/Cohomology/PrismMaps.lean          (WP3, combinatorial input)
RequestProject/Spine/Cohomology/Prism.lean              (WP3, WP4)
RequestProject/Spine/Cohomology/HomotopyInvariance.lean (WP5–WP9)
RequestProject/Spine/GoodCover/GoodCoverAcyclic.lean    (WP10)
RequestProject/Spine/GoodCover/HardenedSpec.lean        (WP11–WP13)
```

No `sorry`, no `admit`, no project-local `axiom`, no `unsafe`, no `partial`, no
`implemented_by`.  All principal declarations report only
`[propext, Classical.choice, Quot.sound]` (§11).  Full `lake build` is green (8190 jobs) and the
mechanical firewall passes.

---

## 1. WP1 — audit of the Task-5 singular functoriality

The Task-5 dependency DAG, as it actually exists in
`RequestProject/Spine/Cohomology/{Cochain,Coboundary,Cohomology,Functorial}.lean`:

```
  Simplex X n  :=  (TopCat.toSSet.obj X).obj (op [n])          -- Cochain.lean
        │                                                        (definitionally
        │                                                         ULift (|Δⁿ| ⟶ X))
        ├── reindex a σ  := (toSSet.obj X).map a.op σ
        │        └── face i σ := reindex (SimplexCategory.δ i) σ
        │
  Cochain X n  :=  Simplex X n → ZMod 2                        -- a genuine Pi type
        │
  coboundary n c σ = ∑_{i : Fin (n+2)} c (face i σ)            -- Coboundary.lean
  d X n : Cⁿ →ₗ[ZMod 2] Cⁿ⁺¹ ,   d ∘ d = 0
        │
  cocycles = ker d ,  coboundaries = im d (⊥ in degree 0)      -- Cohomology.lean
  Cohomology X n = cocycles ⧸ coboundariesIn                   -- a real quotient module

  f : X ⟶ Y
        │
        ├── simplexMap f n : Simplex X n → Simplex Y n         -- Functorial.lean
        │        (naturality: simplexMap f ∘ reindex = reindex ∘ simplexMap f,
        │         hence simplexMap f ∘ face = face ∘ simplexMap f)
        ├── pullback f n : Cⁿ(Y) →ₗ Cⁿ(X)
        │        pullback_d : f*(δc) = δ(f*c)
        ├── cocyclesMap f n : Zⁿ(Y) →ₗ Zⁿ(X)
        └── Hmap f n : Hⁿ(Y;ℤ₂) →ₗ Hⁿ(X;ℤ₂)
```

Confirmed at theorem level, unchanged by Task 8:

* `Mod2Cohomology.Hmap_id (n) : Hmap (𝟙 X) n = LinearMap.id`;
* `Mod2Cohomology.Hmap_comp (f) (g) (n) : Hmap (f ≫ g) n = (Hmap f n).comp (Hmap g n)` —
  contravariant, with the correct order: `f : X ⟶ Y`, `g : Y ⟶ Z`, so
  `(f ≫ g)* = f* ∘ g*` as maps `Hⁿ(Z) → Hⁿ(X)`.

Nothing of Task 5 was rebuilt.  Task 8 adds two *facts about the model* that Task 5 did not
need and that the prism does:

* `Mod2Cohomology.toMap` / `ofMap` — a singular simplex is (definitionally, by `ULift.down`) a
  morphism `|Δⁿ| ⟶ X` of `TopCat`;
* `reindex a s` is precomposition with `SimplexCategory.toTop.map a`, and `simplexMap f n s` is
  postcomposition with `f` (both `rfl`).

These are the hooks by which a *topological* construction can enter the Task-5 cochain theory
at all.

---

## 2. WP2 — Mathlib homotopy / prism infrastructure audit

| Ingredient | Status | Where / comment |
| --- | --- | --- |
| continuous maps, `TopCat`, `ConcreteCategory` | `MATHLIB_NATIVE` | used unchanged |
| homotopy of continuous maps `ContinuousMap.Homotopy f g` | `MATHLIB_NATIVE` | `Mathlib.Topology.Homotopy.Basic`; a bundled `C(I × X, Y)` |
| endpoint evaluation `H.apply_zero`, `H.apply_one` | `MATHLIB_NATIVE` | consumed directly by `prismPiece_betaN_top` / `_zero` |
| homotopy relation `ContinuousMap.Homotopic` | `MATHLIB_NATIVE` | `Nonempty (Homotopy f g)` |
| homotopy equivalence `ContinuousMap.HomotopyEquiv` | `MATHLIB_NATIVE` | fields `toFun`, `invFun`, `left_inv`, `right_inv` |
| the unit interval `unitInterval` | `MATHLIB_NATIVE` | — |
| products with the unit interval | `MATHLIB_NATIVE` | ordinary product topology; no extra API needed |
| singular simplices `TopCat.toSSet` | `MATHLIB_NATIVE` | restricted ULift-Yoneda along `SimplexCategory.toTop` |
| topological standard simplex `SimplexCategory.toTop` | `MATHLIB_NATIVE` | `toTop₀ ⋙ TopCat.uliftFunctor`, carrier `stdSimplex ℝ (Fin (n+1))` |
| affine maps between standard simplices | `MATHLIB_NATIVE` | `SimplexCategory.toTop.map`, coordinates by `stdSimplex.map` (fibrewise sums) |
| cosimplicial identities `δ_comp_δ`, `δ_comp_σ_*` | `MATHLIB_PARTIAL` | present, but stated in `Fin`-indexed form with `castSucc`/`succ` casts that obstruct the prism double sum; see §3 |
| **prism decomposition of `Δⁿ × I`** | **MISSING** | a search of the pinned tree for `prism` returns nothing |
| **chain homotopies for the singular complex** | **MISSING** | `Mathlib.AlgebraicTopology.SingularHomology` contains `Basic.lean` only |
| **homotopy invariance of singular (co)homology** | **MISSING** | not present in any form |
| chain homotopies in the abstract (`HomotopicalAlgebra`, `HomologicalComplex.Homotopy`) | `MATHLIB_NATIVE` | *not used*: the Task-5 theory is an explicit cochain theory, not a `HomologicalComplex`, so wiring it into the categorical machinery would have been a larger and less faithful detour than the direct argument |
| Task-5 singular `ℤ₂` cochain theory, `Hmap` | `SPINE_NATIVE` | reused unchanged |
| `ℕ`-indexed cofaces/codegeneracies/cut maps | `SPINE_NATIVE` (new) | `Mod2Cohomology.deltaN`, `sigmaN`, `betaN` |
| the prism operator itself | `SPINE_NATIVE` (new) | `Mod2Cohomology.prismPiece`, `prism`, `prismK` |

**No second notion of homotopy was introduced.**  The construction consumes Mathlib's
`ContinuousMap.Homotopy` and `ContinuousMap.HomotopyEquiv` directly.

---

## 3. WP3 — the prism operator, as constructed

A singular simplex of `X` in the Task-5 model *is* a map `|Δᵏ| ⟶ X`.  Consequently the classical
affine prism map `p_i : Δⁿ⁺¹ → Δⁿ × I` can be described by a **pair of morphisms of the simplex
category**, and the whole face calculus becomes simplicial algebra:

```
  prismPiece H a b s  :  |Δᵏ| → Y ,     t ↦ H ( β(b)(t) , s(a(t)) )
        a : [k] ⟶ [m]     the Δᵐ-direction
        b : [k] ⟶ [1]     the interval direction, read off by `unitCoord : |Δ¹| → I`

  prism H i s := prismPiece H (sigmaN m i) (betaN (m+1) (i+1)) s      i : Fin (m+1)
```

`sigmaN m i` is the `i`-th codegeneracy and `betaN (m+1) r` is the "cut at `r`" map sending the
vertices `0,…,r-1` to `0 ∈ [1]` and `r,…` to `1`.  Vertexwise this is exactly the classical
`[v₀ … v_i w_i … w_n]`.

Everything else follows from two functorialities (`reindex_prismPiece`,
`prismPiece_reindex`, both proved by pointwise extensionality plus `Functor.map_comp`) and two
endpoint identifications:

```
  prismPiece H a (betaN k 0) s = simplexMap g k (reindex a s)     -- unitCoord = 1, H.apply_one
  prismPiece H a (betaN k r) s = simplexMap f k (reindex a s)     -- r > k: unitCoord = 0, H.apply_zero
```

The two `unitCoord` computations are the only genuinely *geometric* steps, and they are done
from the barycentric-coordinate formula for `SimplexCategory.toTop.map`
(`Mod2Cohomology.coord_toTop_map`: the `k`-th coordinate of the image is the sum over the fibre).

### Why the families are indexed by `ℕ` and not by `Fin`

The three simplicial identities the prism needs,

```
  δ_b ≫ σ_a = σ_{a-1} ≫ δ_b     (b < a)
  δ_b ≫ σ_a = σ_a ≫ δ_{b-1}     (b > a+1)
  δ_b ≫ σ_a = 𝟙                 (b = a, b = a+1)
```

change the *dimension* of the intermediate object between the two sides.  In Mathlib's
`Fin`-indexed form (`SimplexCategory.δ_comp_σ_of_le`, `_of_gt`, `_self`, `_succ`) the indices
carry `Fin.castSucc`/`Fin.succ` coercions whose bookkeeping swamps the double-sum argument.
`PrismMaps.lean` therefore introduces `deltaN`, `sigmaN`, `betaN` with `ℕ` parameters and fixed
source/target, proves `SimplexCategory.δ j = deltaN m ↑j` and `SimplexCategory.σ i = sigmaN m ↑i`
(`delta_eq`, `sigma_eq`) so nothing is a *new* notion, and re-proves the three identities in
`ℕ`-parameter form by value-level extensionality plus `omega`.  The fourth identity,

```
  δ_s ≫ β_r = β_{r-1}  if s < r ,   = β_r  otherwise         (deltaN_comp_betaN)
```

is the interval-direction analogue and has no Mathlib counterpart.

### The identity, and how it is proved

```
    δ ∘ K  +  K ∘ δ  =  g*  +  f*                (Mod2Cohomology.prismK_identity)
              K ∘ δ  =  g*  +  f*   in degree 0  (Mod2Cohomology.prismK_identity_zero)
```

Evaluated on a singular `(n+1)`-simplex `s`, the left-hand side is the sum of two double sums:
`S a b` (the `a`-th prism simplex of the `b`-th face of `s`) and `T a b` (the `b`-th face of the
`a`-th prism simplex of `s`).  Both are of the form `c (prismPiece H _ _ s)` with the two
structure morphisms determined by `a` and `b`, so the four simplicial identities give

```
  T a b = S (a-1) b        (b < a)
  T a b = S a (b-1)        (b > a+1)
  T a a = A a ,  T a (a+1) = A (a+1)      A r := c (prismPiece H 𝟙 (betaN (n+1) r) s)
```

The off-diagonal terms exhaust `S` exactly once each, so they cancel in characteristic two; the
diagonal terms telescope to `A 0 + A (n+2)`, which are `c(g_# s)` and `c(f_# s)`.  This purely
algebraic step is isolated as `Mod2Cohomology.prism_double_sum`, a statement about three
arbitrary families `S`, `T`, `A : ℕ → … → ZMod 2` satisfying the four relations; the telescoping
is `Mod2Cohomology.telescope_charTwo`.

**The prism identity is proved, not postulated.**

---

## 4. WP4 — the characteristic-two sign audit

`RequestProject/Spine/Cohomology/CharTwo.lean` exists solely to make the sign collapse a
*visible node of the dependency graph* rather than a silent convention.

| Statement | Content |
| --- | --- |
| `Mod2Cohomology.CharTwo.neg_one` | `(-1 : ZMod 2) = 1` — the whole content of the collapse |
| `Mod2Cohomology.CharTwo.neg_self`, `add_self` | `-x = x`, `x + x = 0` |
| `Mod2Cohomology.CharTwo.neg_cochain`, `sub_cochain` | `-c = c`, `c - c' = c + c'` for cochains |
| `Mod2Cohomology.CharTwo.signed_vs_unsigned` | `u - v = w ↔ u + v = w`: **the exact translation** between the signed prism identity `∂P + P∂ = g_# - f_#` and the mod-2 identity `∂P + P∂ = g_# + f_#` |
| `Mod2Cohomology.alternating_coboundary_eq_coboundary` | `∑ᵢ (-1)ⁱ f(∂ᵢσ) = coboundary n f σ`: the Task-5 unsigned coboundary **is** the reduction of the classical alternating one, so the two theories are not merely analogous |

The distinction asked for in the task is therefore recorded as a proved biconditional, not as a
remark: over signed chains the statement is `g_# - f_#`, over `ℤ/2` it is `g_# + f_#`, and
`signed_vs_unsigned` is the bridge.  `CharTwo.sub_cochain` is *used* in the proof of
`Hmap_eq_of_homotopy`, so the collapse is a real edge of the proof DAG and not decoration.

---

## 5. WP5–WP6 — the cochain homotopy and its use on cocycles

`Mod2Cohomology.prismK H n : Cⁿ⁺¹(Y;ℤ₂) →ₗ Cⁿ(X;ℤ₂)` is the cochain-level operator, `ZMod 2`-linear
by construction, and

```
  cochainHomotopy      : g* c + f* c = δ (K c) + K (δ c)     (deg n+1)
  cochainHomotopy_zero : g* c + f* c = K (δ c)               (deg 0)
```

use the **Task-5 coboundary** `Mod2Cohomology.d` on both sides; no alternative convention is
introduced.

The descent to cohomology is *not* assumed.  `pullback_add_pullback_mem_coboundaries` proves,
for a cochain `α` with `δα = 0`,

```
  g*α + f*α  =  δ (K α)  ∈  Bⁿ(X;ℤ₂)                (degree n = m+1)
  g*α + f*α  =  K 0  =  0                            (degree 0)
```

and the hypothesis `δα = 0` is consumed explicitly in both branches (it is what kills `K(δα)`).
In degree `0` the conclusion is stronger than needed — the two pullbacks agree as cochains —
which is the correct statement there, since `B⁰ = 0` in the Task-5 theory.

---

## 6. WP7 — the main theorem

```lean
theorem Mod2Cohomology.Hmap_eq_of_homotopy
    (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) : Hmap f n = Hmap g n

theorem Mod2Cohomology.Hmap_eq_of_homotopic
    (h : (f.hom).Homotopic (g.hom)) (n : ℕ) : Hmap f n = Hmap g n
```

The result lives in the genuine Task-5 quotient: the proof takes an arbitrary class, writes it
as `mk z` with `z : cocycles Y n` (`mk_surjective`), and closes the goal through
`mk_eq_mk_iff`, i.e. by exhibiting the difference of the two representatives as an element of
`coboundaries X n`.  It is *not* a statement about representatives.

**Generality.**  The theorem is proved for all `n : ℕ`; the degree-`2` endpoint the task allows
as a fallback was not needed.  The reason generality was cheap here is that the prism operator
is itself degree-generic and the whole face calculus is uniform in `n`: the only degree-specific
work is the degenerate degree-`0` case, handled once in `prismK_identity_zero`.

---

## 7. WP8 — homotopy equivalences

```lean
def Mod2Cohomology.homotopyEquivCohomology
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) : Cohomology Y n ≃ₗ[ZMod 2] Cohomology X n
```

with

```lean
homotopyEquivCohomology e n q       = Hmap (hequivFwd e) n q     -- rfl
(homotopyEquivCohomology e n).symm q = Hmap (hequivInv e) n q    -- rfl
```

so both directions are `Hmap` of the equivalence's own continuous maps, and neither is chosen.
The two inverse laws are `Hmap_hequivInv_comp` and `Hmap_hequivFwd_comp`, each obtained from

* `Hmap_comp` (Task-5 functoriality, contravariant), and
* `Hmap_eq_of_homotopic` applied to `e.right_inv` / `e.left_inv`, and
* `Hmap_id`,

which is exactly the derivation the task prescribes.  No fresh linear equivalence is
introduced anywhere.

---

## 8. WP9–WP10 — contractibility and good covers

```lean
theorem Mod2Cohomology.cohomology_succ_eq_zero_of_contractible
    (Z : TopCat) [ContractibleSpace Z] (n : ℕ) (q : Cohomology Z (n+1)) : q = 0
```

proved by transporting `q` to a one-point space along `homotopyEquivCohomology` and applying the
Task-7 point computation `Mod2Cohomology.cohomology_succ_eq_zero_of_subsingleton`.  Both the
transport and the point computation are theorems of this project; the degrees `1` and `2` are
recorded separately (`cohomology_one_eq_zero_of_contractible`,
`cohomology_two_eq_zero_of_contractible`).  The point computation was **not** re-derived: the
Task-7 module is imported unchanged, so this corollary added no new point-cohomology project.

```lean
theorem GoodCoverZ2.isAcyclicCover_of_isGoodCover (h : IsGoodCover U) : IsAcyclicCover U
```

is now unconditional.  Its degreewise form
`GoodCoverZ2.cohomology_inter_succ_eq_zero` gives, for every nonempty finite overlap
`U i₀ ∩ ⋯ ∩ U i_k` of a good cover and every `k`,
`H^{k+1}_sing(overlap; ℤ₂) = 0`; degrees 1 and 2 are recorded separately.

```
    good cover  ⟹  acyclic cover in every positive degree
```

Task 7 stated this implication only under the hypothesis `GoodCoverSpec.HomotopyInvariance`;
that hypothesis is gone.

---

## 9. WP11–WP14 — the hardened comparison layer, and the DAG

### WP11 — supersession

`GoodCoverSpec.HomotopyInvariance` is **retained** (provenance, backward compatibility) and
relabelled in its own docstring as `SUPERSEDED_BY_NATIVE_THEOREM`.  It is now *inhabited*:

```lean
def GoodCoverSpec.nativeHomotopyInvariance (n : ℕ) : HomotopyInvariance n :=
  ⟨fun e => (Mod2Cohomology.homotopyEquivCohomology e n).symm⟩
```

and `nativeHomotopyInvariance_transport_symm` records that its transport is `Hmap` of the
forward map.  The hardened comparison below has **no homotopy-invariance field**.

### WP12 — the nerve-realization specification

The old `NerveRealization` had a bare `realization : TopCat` and an equivalence with `X`; any
space homotopy equivalent to `X` inhabited it.  The hardened form separates the four layers:

```lean
structure NervePresentation (U : ι → Set X) where
  sset         : SSet                                        -- 2. a simplicial set …
  simplexEquiv : ∀ n, sset.obj (op [n]) ≃ (coverNerve U).obj n --    … presenting …
  face_compat  : …                                            --    … the nerve, faces included

structure NerveRealizationSpec (U : ι → Set X) where
  presentation    : NervePresentation U                       -- 1. the Task-7 nerve, fixed
  realization     : TopCat                                    -- 3. the underlying space …
  realization_eq  : realization = SSet.toTop.obj presentation.sset   --   … which *is* |N(𝓤)|
  equiv           : HomotopyEquiv realization X               -- 4. the comparison with X
```

`NerveRealizationSpec.toNerveRealization` exhibits the hardened datum as strictly stronger than
the old one.  Nothing is constructed: no realization is produced, and the nerve theorem is not
proved.  Classification `BLOCKED_PENDING_GEOMETRIC_REALIZATION`.  (Pinned Mathlib *does* supply
`SSet.toTop`, so no fake realization type was needed; what is missing is the nerve theorem
itself, i.e. the equivalence, together with a simplicial set presenting a presimplicial nerve.)

### WP13 — the simplicial-to-singular specification

The old `SimplicialSingularComparison` was a bare `compare : H²_simp ≃ₗ H²_sing`.  The hardened
form demands the comparison at **cochain level** and proves the descent here:

```lean
structure SimplicialSingularCochainMap (S : Presimplicial) (R : TopCat) where
  map  : ∀ n, S.Cochain n →ₗ[ZMod 2] Mod2Cohomology.Cochain R n
  comm : ∀ n c, map (n+1) (S.d n c) = Mod2Cohomology.d R n (map n c)
```

with `map_mem_cocycles`, `map_mem_coboundaries` and hence `SimplicialSingularCochainMap.Hmap`
proved in this project — compatibility with coboundaries is therefore established *before*
descending.  A comparison is then

```lean
structure SimplicialSingularComparisonSpec (S) (R) where
  cochain   : SimplicialSingularCochainMap S R
  bijective : ∀ n, Function.Bijective (cochain.Hmap n)
```

and its `equiv` is `LinearEquiv.ofBijective` of the **induced** map.  An arbitrary linear
isomorphism no longer satisfies the specification.  Classification `SPECIFICATION_HARDENED`,
still `BLOCKED`.

### WP14 — the Čech→singular DAG at the end of Task 8

```
  Ȟ²(𝓤;ℤ₂)  =  H²_simp(N(𝓤);ℤ₂)            NerveZ2.cechCohomologyEquiv      [PROVED, identity]
        │
        │  BLOCKED — simplicial→singular comparison
        │  now specified honestly: GoodCoverSpec.SimplicialSingularComparisonSpec
        ▼
  H²_sing(|N(𝓤)|;ℤ₂)
        │
        │  ***UNBLOCKED IN TASK 8***  Mod2Cohomology.homotopyEquivCohomology
        │  (given a nerve equivalence; no free-standing HomotopyInvariance assumption)
        ▼
  H²_sing(M;ℤ₂)
```

and the nerve equivalence itself:

```
  BLOCKED — nerve theorem
  now specified honestly: GoodCoverSpec.NerveRealizationSpec
  (BLOCKED_PENDING_GEOMETRIC_REALIZATION)
```

The assembled hardened comparison `GoodCoverSpec.HardenedComparison` has exactly two fields —
the two remaining blocked edges — and produces `HardenedComparison.equiv n` in **every** degree
(Task 7's assembled comparison existed in degree two only).  The Spin endpoints are transported
along it: `spinLiftSingularClassHardened`, its lift-independence, its vanishing criterion, and
`frameSingularClassHardened_eq_zero_iff_spinStructure`.

**Exactly one major blocked edge was removed**, as the task predicted.

---

## 10. Failbuild ledger

Every failed build during Task 8, with the exact diagnostic, cause, repair and
statement-change classification.  No statement was weakened by any repair.

| # | command | diagnostic | cause | repair | statement change |
| --- | --- | --- | --- | --- | --- |
| 1 | `lake build` | `RequestProject/Spine/Cohomology/CharTwo.lean:51:45: Expected type must not contain free variables` (and `:54:48`) | `decide` invoked on `-x = x` with `x : ZMod 2` a *free* variable; `Decidable` instances need a closed proposition | `revert x; decide` in `CharTwo.neg_self` and `CharTwo.add_self` | none (tactic only) |
| 2 | `lake build` | `RequestProject/Spine/Cohomology/Prism.lean:372:76: unsolved goals` | in `prismK_identity`, after `rw [deltaN_comp_betaN, if_pos …]` the residual goal `betaN (n+1) (a+1-1) = betaN (n+1) a` was left open | added `congr 1` | none (tactic only) |
| 3 | `lake build` | `RequestProject/Spine/Cohomology/Prism.lean:430:8: Unknown constant 'Finset.sum_singleton_eq_sum_of_unique'` | guessed a non-existent Mathlib lemma name for the one-element sum | replaced by `Fin.sum_univ_one` | none (tactic only) |
| 4 | `lake build` | `RequestProject/Spine/Cohomology/HomotopyInvariance.lean:119:2` and `:130:2: Type mismatch: After simplification, term … = q` | `simpa … using this.symm`: the derived equation already had the required orientation, so `.symm` reversed it wrongly | dropped `.symm` | none (tactic only) |
| 5 | `lake build` | `RequestProject/Spine/Audit/Firewall.lean:568:2: maximum recursion depth has been reached` | after adding eight Task-8 targets to the firewall's proof-closure audit, the single `run_cmd` exceeded the default `maxRecDepth` while walking the (larger) dependency closures | `set_option maxRecDepth 100000 in` on the audit command; no audit was weakened or removed | none (audit is strictly larger: 8 new targets) |

Elaboration hazards met during development that did **not** reach a full build but are recorded
because they were statement-level, not tactic-level:

* in a goal of the shape `((… : Fin (m+1)) : ℕ) = if p then k else k+1`, Lean elaborated the
  `else` branch as `((k+1 : Fin (m+1)) : ℕ)` — i.e. with *wrap-around* `Fin` arithmetic — rather
  than as `(k : ℕ) + 1`.  The two statements differ at `k = m`.  All value-level lemmas in
  `PrismMaps.lean` therefore write `(k : ℕ)` explicitly on both sides;
* `simp`/`rw` with `classical` in scope produced `Finset.filter` terms carrying
  `Classical.propDecidable` instead of the `Fin` decidability instance, so a `rw` of a filter
  identity failed to match; the `classical` was removed from those proofs.

---

## 11. Build evidence and axiom audit

```
lake build RequestProject.Spine.Cohomology.Core            OK
lake build RequestProject.Spine.Cech.Core                  OK
lake build RequestProject.Spine.Geometry.Core              OK
lake build RequestProject.Spine.Core                       OK
lake build RequestProject.Spine.Audit.Firewall             OK   (SPINE FIREWALL AUDIT: all checks passed;
                                                                 8 Task-8 proof-closure targets added)
lake build                                                 OK   (8190 jobs)

lake build RequestProject.Spine.Cohomology.CharTwo             OK
lake build RequestProject.Spine.Cohomology.PrismMaps           OK
lake build RequestProject.Spine.Cohomology.Prism               OK
lake build RequestProject.Spine.Cohomology.HomotopyInvariance  OK
lake build RequestProject.Spine.GoodCover.GoodCoverAcyclic     OK
lake build RequestProject.Spine.GoodCover.HardenedSpec         OK
lake build RequestProject.Spine.GoodCover.Core                 OK
```

Import isolation (`scripts/dep_stats.py`), for each new module and for the endpoint
`RequestProject.Spine.Core`:

```
  Experiment1 direct imports      = 0
  Experiment1 transitive imports  = 0
  Experiment2 direct imports      = 0
  Experiment2 transitive imports  = 0
  external-project imports        = 0        (mechanically re-checked by Spine.Audit.Firewall)
```

Grep over the six new modules for `sorry`, `admit`, `axiom `, `unsafe `, `partial `,
`implemented_by`: **no matches**.

`#print axioms` on every principal new declaration —
`CharTwo.neg_one`, `CharTwo.sub_cochain`, `CharTwo.signed_vs_unsigned`,
`alternating_coboundary_eq_coboundary`, `delta_eq`, `sigma_eq`, `deltaN_comp_sigmaN_lt`,
`deltaN_comp_sigmaN_gt`, `deltaN_comp_sigmaN_eq`, `deltaN_comp_betaN`, `prismPiece`, `prism`,
`prismK`, `prism_double_sum`, `prismK_identity`, `prismK_identity_zero`, `cochainHomotopy`,
`pullback_add_pullback_mem_coboundaries`, `Hmap_eq_of_homotopy`, `Hmap_eq_of_homotopic`,
`homotopyEquivCohomology`, `cohomology_succ_eq_zero_of_contractible`,
`cohomology_one_eq_zero_of_contractible`, `cohomology_two_eq_zero_of_contractible`,
`GoodCoverZ2.cohomology_inter_succ_eq_zero`, `GoodCoverZ2.isAcyclicCover_of_isGoodCover`,
`GoodCoverSpec.nativeHomotopyInvariance`, `GoodCoverSpec.SimplicialSingularCochainMap.Hmap`,
`GoodCoverSpec.HardenedComparison.equiv`,
`GoodCoverSpec.spinLiftSingularClassHardened_eq_zero_iff`,
`GoodCoverSpec.frameSingularClassHardened_eq_zero_iff_spinStructure` —
reports in every case exactly

```
  [propext, Classical.choice, Quot.sound]
```

---

## 12. External sources

No external Lean formalization of singular homotopy invariance, of prism operators or of chain
homotopies was inspected during Task 8.  The construction was derived from the standard
textbook prism argument and from the pinned Mathlib API only.  The Task-5 ledger
`TASK05_EXTERNAL_SOURCES.md` is preserved verbatim; the Task-8 entry is
`TASK08_EXTERNAL_SOURCES.md`.

---

## 13. Answers to the final scientific questions

**Does the singular mod-2 cohomology constructed natively in Task 5 now satisfy theorem-level
homotopy invariance?**
Yes.  `Mod2Cohomology.Hmap_eq_of_homotopic : f.hom.Homotopic g.hom → Hmap f n = Hmap g n`, for
every `n : ℕ`, proved from a genuine prism/chain-homotopy construction inside the Task-5
cochain theory.  Nothing about it is postulated.

**For a genuine homotopy equivalence `X ≃ₕ Y`, is the resulting cohomology isomorphism
constructed from the actual induced maps `Hmap`, rather than supplied as arbitrary comparison
data?**
Yes.  `Mod2Cohomology.homotopyEquivCohomology e n` has `toFun = Hmap (hequivFwd e) n` and
`invFun = Hmap (hequivInv e) n`, both by `rfl`; the two inverse laws are derived from
`Hmap_comp`, `Hmap_id` and the new homotopy invariance applied to `e.left_inv` and
`e.right_inv`.

**Does contractibility now imply vanishing positive-degree singular mod-2 cohomology in the
degrees required by the good-cover programme?**
Yes, and in all positive degrees, not only the required ones:
`Mod2Cohomology.cohomology_succ_eq_zero_of_contractible`, with `H¹ = 0` and `H² = 0` recorded
separately, and the cover-level corollary
`GoodCoverZ2.isAcyclicCover_of_isGoodCover` (good ⇒ acyclic, unconditionally).

**Which exact blocked edges remain before the Task-6 Spin-lift class can be transported
canonically from `Ȟ²(𝓤;ℤ₂)` into `H²_sing(M;ℤ₂)`?**
Two, plus one that concerns canonicity rather than existence.

1. **The nerve theorem.**  Missing: a simplicial set presenting `N(𝓤)` together with a homotopy
   equivalence `|N(𝓤)| ≃ M` for a good cover `𝓤`.  Mathlib supplies `SSet.toTop` but no nerve
   theorem and no partition-of-unity construction of the comparison maps.  Now specified by
   `GoodCoverSpec.NerveRealizationSpec` (`BLOCKED_PENDING_GEOMETRIC_REALIZATION`).
2. **Simplicial-to-singular comparison.**  Missing: an explicit cochain map
   `C*_simp(N(𝓤);ℤ₂) → C*_sing(|N(𝓤)|;ℤ₂)` inducing an isomorphism.  Now specified by
   `GoodCoverSpec.SimplicialSingularComparisonSpec` (`BLOCKED`).
3. **Canonicity in the cover** (carried over from Task 7, unchanged by Task 8): existence of
   good covers on the Task-4 manifold class, and of a *common good refinement* of two good
   covers, are both still missing (`GoodCoverSpec.CommonGoodRefinement`), so cover-independence
   of the transported class remains conditional.

   The homotopy-invariance edge, which was blocked at the end of Task 7, is **no longer**
   in this list.

**Has the Task-7 conditional comparison layer been hardened so that future arbitrary linear
isomorphisms can no longer masquerade as the nerve theorem or the simplicial-to-singular
comparison theorem?**
Yes.  A nerve realization must now exhibit its space as `SSet.toTop.obj` of a simplicial set
whose simplices and faces are those of `NerveZ2.coverNerve U`; a simplicial-to-singular
comparison must now supply a degreewise cochain map commuting with both coboundaries, and may
only assert bijectivity of the map that *this* data induces on cohomology.  The two old
structures are retained for provenance and are relabelled in their own docstrings as
provisional conditional interfaces that must never be documented as proved comparison theorems.
