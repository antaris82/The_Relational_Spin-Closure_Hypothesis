# TASK 09 AUDIT — Canonical cover nerve as a full simplicial set, and the geometric simplicial-to-singular comparison

Scope: classical mathematical certification only. No quantum mechanics, no physical
interpretation, no Stiefel–Whitney classes, no nerve theorem, no Čech-to-singular comparison on
the manifold.

Status of the build at the time of writing: `lake build` green (8197 jobs), mechanical firewall
green, no `sorry`, no `admit`, no project-local `axiom`, no `unsafe`, no `partial`, no
`implemented_by` in the new layer. Every principal new declaration reports
`[propext, Classical.choice, Quot.sound]`.

---

## 0. New Lean layer

```
RequestProject/Spine/Nerve/CoverNerveSSet.lean     (WP2)
RequestProject/Spine/Nerve/CochainComparison.lean  (WP3)
RequestProject/Spine/Nerve/Realization.lean        (WP4, WP5)
RequestProject/Spine/Nerve/ChainMap.lean           (WP6)
RequestProject/Spine/Nerve/CochainMap.lean         (WP7)
RequestProject/Spine/Nerve/ComparisonSpec.lean     (WP8–WP14)
RequestProject/Spine/Nerve/Core.lean               (endpoint + axiom audit)
```

`RequestProject/Spine/Core.lean` now imports `RequestProject.Spine.Nerve.Core`, and
`RequestProject/Spine/Audit/Firewall.lean` audits the seven new modules (import isolation,
layer order) and sixteen new proof closures.

---

## 1. WP1 — audit of the existing Task-6/7/8 nerve representation

### 1.1 What exists, where

| component | declaration | module | classification (before Task 9) |
| --- | --- | --- | --- |
| finite overlap of a tuple | `CechZ2.inter` | `Spine/Cech/Cochain.lean` | `FULL_SIMPLICIAL` (reused unchanged) |
| monotonicity of overlaps under reindexing | `CechZ2.inter_subset_comp` | `Spine/Cech/Cochain.lean` | `FULL_SIMPLICIAL` (this is the key lemma that makes degeneracies exist) |
| nerve simplices | `CechZ2.Nerve U n = {σ : Fin (n+1) → ι // (inter U σ).Nonempty}` | `Spine/Cech/Cochain.lean` | `PRESIMPLICIAL_ONLY` |
| face operator | `CechZ2.face t σ = σ.idx ∘ t.succAbove` | `Spine/Cech/Cochain.lean` | `PRESIMPLICIAL_ONLY` |
| presimplicial identity | `CechZ2.succAbove_comm` | `Spine/Cech/Coboundary.lean` | `PRESIMPLICIAL_ONLY` |
| abstract presimplicial sets and their `ℤ₂` cochain complex | `NerveZ2.Presimplicial` | `Spine/GoodCover/Presimplicial.lean` | `PRESIMPLICIAL_ONLY` |
| the cover nerve as a presimplicial set | `NerveZ2.coverNerve` | `Spine/GoodCover/NerveIdentification.lean` | `PRESIMPLICIAL_ONLY` |
| Čech complex = simplicial complex of the nerve | `NerveZ2.cechCohomologyEquiv` (the identity) | `Spine/GoodCover/NerveIdentification.lean` | `FULL_SIMPLICIAL` (reused; still the identity) |
| Task-3 ↔ nerve overlap dictionary in low degrees | `CechSpinZ2.inter_pair/inter_triple/inter_quad`, `nerve₁/₂/₃`, `face₂_*`, `face_nerve₂_*` | `Spine/Cech/CoverNerve.lean` | `FULL_SIMPLICIAL` (unchanged, still valid) |
| **degeneracy maps** | — | — | **`MISSING`** |
| **simplicial identities other than `dᵢdⱼ`** | — | — | **`MISSING`** |
| `SSet` wrapper | `GoodCoverSpec.NervePresentation` | `Spine/GoodCover/HardenedSpec.lean` | `SPECIFICATION_ONLY` |
| geometric-realization specification | `GoodCoverSpec.NerveRealizationSpec` | `Spine/GoodCover/HardenedSpec.lean` | `SPECIFICATION_ONLY` |
| older realization interface (free `realization : TopCat`) | `GoodCoverSpec.NerveRealization` | `Spine/GoodCover/SingularComparisonSpec.lean` | `SUPERSEDED` |
| simplicial-to-singular comparison, arbitrary linear equivalence | `GoodCoverSpec.SimplicialSingularComparison` | `Spine/GoodCover/SingularComparisonSpec.lean` | `SUPERSEDED` |
| simplicial-to-singular cochain map (abstract, simp → sing) | `GoodCoverSpec.SimplicialSingularCochainMap` | `Spine/GoodCover/HardenedSpec.lean` | `SPECIFICATION_ONLY` |
| simplicial-to-singular comparison specification | `GoodCoverSpec.SimplicialSingularComparisonSpec` | `Spine/GoodCover/HardenedSpec.lean` | `SPECIFICATION_ONLY` |
| homotopy invariance interface | `GoodCoverSpec.HomotopyInvariance` | `Spine/GoodCover/SingularComparisonSpec.lean` | `SUPERSEDED` (Task 8 theorem) |

### 1.2 Explicit answers to the WP1 checklist

* **Ordered vertices** — YES. A simplex is a *function* `Fin (n+1) → ι`; the vertices are
  ordered by their `Fin` position. No order relation on `ι` is used or required.
* **Simplex dimension** — YES, the degree `n` is explicit in the type `Nerve U n`.
* **Face maps** — YES (`CechZ2.face`, deletion of a position via `Fin.succAbove`).
* **Degeneracy maps** — NO. Nothing in Task 6/7/8 constructed one, and nothing inferred one
  from naming. (Verified by reading `Spine/Cech/**` and `Spine/GoodCover/**` in full.)
* **Simplicial identities** — only the presimplicial one `dᵢ ∘ d_{j+1} = dⱼ ∘ d_i`
  (`NerveZ2.Presimplicial.face_comm`). The mixed and degeneracy identities did not exist.
* **`NervePresentation`** — exists as a specification only; nothing inhabited it.
* **`SSet` wrappers** — none; `GoodCoverSpec.NervePresentation.sset` was a *field*, i.e. a
  hypothesis.
* **Geometric-realization specification** — `NerveRealizationSpec.realization_eq` demanded
  `realization = SSet.toTop.obj presentation.sset`, but no inhabitant existed.
* **Simplicial-to-singular comparison specification** — `SimplicialSingularComparisonSpec`,
  uninhabited.

### 1.3 Dependency DAG at the start of Task 9

```
CechZ2.inter ──► CechZ2.Nerve ──► CechZ2.face ──► CechZ2.coboundary ──► CechZ2.d ──► δ²=0
                     │                                                        │
                     │                                                        ▼
                     │                                    CechZ2.cocycles / coboundaries
                     │                                                        │
                     ▼                                                        ▼
        NerveZ2.coverNerve (presimplicial) ══ identity ══════════► CechZ2.Cohomology = Ȟⁿ(𝓤;ℤ₂)
                     │
                     ▼
        GoodCoverSpec.NervePresentation (spec, uninhabited)
                     │
                     ▼
        GoodCoverSpec.NerveRealizationSpec (spec, uninhabited) ──► GoodCoverSpec.HardenedComparison
                     ▲                                                        ▲
                     │                                                        │
        GoodCoverSpec.SimplicialSingularComparisonSpec (spec, uninhabited) ────┘
```

---

## 2. WP2 — the canonical cover nerve as a full simplicial set — `FULL_SIMPLICIAL_NERVE`

`NerveGeom.coverNerveSSet U : SSet.{u}` is a genuine functor `Δᵒᵖ ⥤ Set`:

* objects: `[n] ↦ CechZ2.Nerve U n`, the ordered `(n+1)`-tuples of cover indices whose total
  intersection is nonempty, **repetitions allowed**;
* morphisms: `f : [m] ⟶ [n]` acts by `σ ↦ σ.idx ∘ f.toOrderHom`.

The construction works for **every** morphism of the simplex category — not just the cofaces —
because `CechZ2.inter_subset_comp` says that reindexing a tuple along *any* map can only
enlarge its intersection. Functoriality is strict (composition of functions):
`map_id` and `map_comp` are `Nerve.ext` + `rfl`.

Consequences, all proved:

| statement | declaration |
| --- | --- |
| `n`-simplices are the Task-6 ones | `coverNerveSSet_obj` (`rfl`) |
| face maps are the Task-6 `CechZ2.face` | `coverNerveSSet_delta` (`rfl`) |
| face maps are the Task-7 presimplicial faces | `coverNerveSSet_presimplicial` (`rfl`) |
| degeneracy maps are vertex repetition | `coverNerveSSet_sigma` (`rfl`), `degen_idx_castSucc`, `degen_idx_succ`, `degen_repeats_vertex` |
| `dᵢd_{j+1} = dⱼdᵢ` (`i ≤ j`) | `face_face_comm` |
| `sᵢsⱼ` identity | `degen_degen_comm` |
| `d_{i.castSucc} sᵢ = id` | `face_castSucc_degen` |
| `d_{i.succ} sᵢ = id` | `face_succ_degen` |
| `dᵢsⱼ`, low range | `face_degen_of_le` |
| `dᵢsⱼ`, high range | `face_degen_of_gt` |

As WP2 instructs, the identities are **not** restated by hand: each is
`CategoryTheory.SimplicialObject.<identity> (coverNerveSSet U)` applied pointwise, i.e. it is
the functorial structure that carries them. `degen i σ` is `reindex (Fin.predAbove i) σ`, and
`Fin.predAbove i` is exactly the underlying map of `SimplexCategory.σ i`.

**Repeated vertices are handled explicitly**: a simplex is an arbitrary function
`Fin (n+1) → ι`, so `(i, i, j)` is a legitimate `2`-simplex whenever `U i ∩ U j ≠ ∅`, and it is
`s₀` of the `1`-simplex `(i, j)`.

---

## 3. WP3 — relation to the existing Task-6 cochain complex — `DERIVED_NATIVE`

**Which convention did Task 6 use?** All ordered tuples with nonempty intersection, i.e. the
**unnormalized** simplicial cochain complex. Specifically:

* *not* strictly increasing tuples (there is no order on `ι`);
* *not* injective tuples;
* *not* nondegenerate simplices only;
* degenerate simplices are genuine elements of `CechZ2.Nerve U n`.

Consequently **no normalization bridge is required**, and none is invented. The precise
statement replacing it is

```
NerveGeom.underlyingPresimplicial (NerveGeom.coverNerveSSet U) = NerveZ2.coverNerve U   -- rfl
```

(`underlyingPresimplicial_coverNerveSSet`): forgetting the degeneracies of the new full
simplicial set returns the *existing* Task-7 presimplicial set, not an isomorphic copy. Hence

| object | agreement |
| --- | --- |
| cochain modules | `cochain_eq` (`rfl`) |
| coboundary (linear map) | `d_eq` (`rfl`) |
| cocycles | `cocycles_eq` (`rfl`) |
| coboundaries | `coboundaries_eq` |
| cohomology, as a linear equivalence | `cechCohomologyEquivSSet` — *is* the pre-existing `NerveZ2.cechCohomologyEquiv`, the identity |

so the WP3 endpoint

```
Ȟⁿ(𝓤;ℤ₂) ≅ Hⁿ_simp(N(𝓤);ℤ₂)
```

holds for the **full** simplicial nerve, is the identity, and is the already-existing Task-6/7
theorem — no parallel theory was created and nothing was silently replaced.

For completeness the notion of degeneracy is characterised combinatorially:
`NerveGeom.IsDegenerate σ` ("two adjacent vertices coincide") is equivalent to "σ lies in the
image of a degeneracy operator" (`isDegenerate_iff_exists_degen`, whose non-trivial direction is
`degen_face_of_repeat`). `normalizedCochains` records the normalized subcomplex carrier, and
`one_not_mem_normalizedCochains` records that the Task-6 complex is *not* it.

---

## 4. WP4 — audit of the geometric-realization infrastructure

| item | pinned Mathlib | classification |
| --- | --- | --- |
| `SSet.toTop : SSet ⥤ TopCat` (left Kan extension of `SimplexCategory.toTop` along the Yoneda embedding) | `Mathlib/AlgebraicTopology/SingularSet.lean` | `MATHLIB_NATIVE` |
| `TopCat.toSSet : TopCat ⥤ SSet` (singular simplicial set) | same file | `MATHLIB_NATIVE` |
| `sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet` | same file | `MATHLIB_NATIVE` |
| `SSet.toTopSimplex : stdSimplex ⋙ toTop ≅ SimplexCategory.toTop` (realization of standard simplices) | same file | `MATHLIB_NATIVE` |
| `TopCat.toSSetObjEquiv` (`n`-simplices ≃ `C(Δⁿ_top, X)`) | same file | `MATHLIB_NATIVE` |
| topology on the realization | inherited from the Kan extension / colimit | `MATHLIB_NATIVE` |
| canonical map `Δⁿ_top → |S|` attached to `σ ∈ Sₙ` | not packaged; it is the unit of `sSetTopAdj` | `MATHLIB_PARTIAL` → supplied here (`NerveGeom.charSimplex`, `NerveGeom.charMap`) |
| face compatibility of those maps | it is naturality of the unit | `MATHLIB_PARTIAL` → `NerveGeom.charSimplex_face` |
| degeneracy compatibility | idem | `MATHLIB_PARTIAL` → `NerveGeom.charSimplex_degen` |
| singular chain complex of a simplicial set / space | `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` — definitions only; the sole computation is for totally disconnected spaces | `MATHLIB_PARTIAL` |
| CW / cellular structure on `SSet.toTop.obj S`, skeletal filtration | — | `MISSING` |
| excision, Mayer–Vietoris, acyclic models for singular homology | — | `MISSING` |
| simplicial-to-singular comparison theorem | — | `MISSING` |
| quotient realization as an alternative | not usable without a comparison theorem | `MISSING` |
| homotopy invariance of the native mod-2 singular cohomology | Task-8 theorem of this project | `SPINE_NATIVE` |

Because Mathlib supplies the correct realization, it is **reused**:

```
NerveGeom.coverNerveRealization U := SSet.toTop.obj (NerveGeom.coverNerveSSet U)
```

No arbitrary topological space is introduced, and nothing is *declared* to be a realization.

---

## 5. WP5 — the canonical singular simplex of each simplicial simplex — `GEOMETRIC_REALIZATION`

`NerveGeom.charSimplex U n σ := (sSetTopAdj.unit.app (coverNerveSSet U)).app [n]ᵒᵖ σ`.

* It lands in `Mod2Cohomology.Simplex (coverNerveRealization U) n`, the Task-5 type of singular
  `n`-simplices, definitionally.
* `NerveGeom.charMap` presents it as an honest continuous map
  `C(Δⁿ_top, |N(𝓤)|)` via `TopCat.toSSetObjEquiv`.
* **Face compatibility** — `charSimplex_face : |∂ᵢσ| = ∂ᵢ|σ|`, i.e.
  `charSimplex U n (CechZ2.face i σ) = Mod2Cohomology.face i (charSimplex U (n+1) σ)`.
* **Degeneracy compatibility** — `charSimplex_degen : |sᵢσ| = |σ| ∘ σᵢ`, i.e.
  `charSimplex U (n+1) (degen i σ) = Mod2Cohomology.reindex (SimplexCategory.σ i) (charSimplex U n σ)`.
  So a degenerate simplicial simplex maps to the corresponding **degenerate singular simplex**;
  it is not mapped to something unrelated and it is not discarded.
* Both are instances of the single naturality statement `charSimplex_reindex`, which says
  `σ ↦ |σ|` is a morphism of simplicial sets.
* **No arbitrary choice** — `charSimplex_universal` proves the universal property: for every
  space `Y` and every simplicial map `φ : N(𝓤) ⟶ Sing(Y)` there is a *unique* continuous
  `g : |N(𝓤)| → Y` with `η ≫ Sing(g) = φ`. The family `η` is therefore determined, not
  selected.

---

## 6. WP6 — the simplicial-to-singular chain map — `CHAIN_MAP`

With `ℤ₂` coefficients the free module on a set of simplices is `Finsupp`:

* `NerveGeom.SimpChain U n := Nerve U n →₀ ZMod 2`, `NerveGeom.SingChain R n := Simplex R n →₀ ZMod 2`;
* `NerveGeom.simpBoundary U n := ∑ₜ Finsupp.lmapDomain _ _ (CechZ2.face t)`;
* `NerveGeom.singBoundary R n := ∑ᵢ Finsupp.lmapDomain _ _ (Mod2Cohomology.face i)`;
  (unsigned, because `-1 = 1` in `ℤ₂`; the same convention as the whole Spine, audited in Task 8
  by `Mod2Cohomology.CharTwo.signed_vs_unsigned`);
* `NerveGeom.chainMap U n := Finsupp.lmapDomain _ _ (charSimplex U n)`.

**Theorem `NerveGeom.chainMap_comm`:**

```
∂_sing ∘ J = J ∘ ∂_simp
```

Its proof consumes exactly `charSimplex_face` (WP5) and the behaviour of `mapDomain` on
`Finsupp.single`. Nothing is postulated.

Normalization: not used. Because the Task-6 complex is unnormalized (WP3), `J` is defined on
all of `C_*^simp` and no descent through a normalized quotient is claimed. The degenerate case is
nevertheless *audited*: `charSimplex_degen` shows `J` sends a degenerate simplicial simplex to
the corresponding degenerate singular simplex.

---

## 7. WP7 — the dual cochain map — `COCHAIN_MAP`

The Spine's cohomology is cochain-level, so the comparison used downstream is the transpose:

```
J* : Cⁿ_sing(|N(𝓤)|;ℤ₂) → Cⁿ_simp(N(𝓤);ℤ₂),   (J*f)(σ) = f(|σ|)
```

* `NerveGeom.SingularToSimplicialCochainMap R S` is the general interface: a degreewise linear
  map together with **the commutation with the two coboundaries**.
* `NerveGeom.geometricCochainMap U` is the canonical instance; its `comm` field is the theorem
  `J*δ_sing = δ_simp J*`.
* `NerveGeom.geometricCochainMap_dual_chainMap` proves `J*` is literally the transpose of the
  WP6 chain map `J` against the `Finsupp` pairing, so WP6 and WP7 are one construction.
* Descent: `map_mem_cocycles`, `map_mem_coboundaries`, and
  `SingularToSimplicialCochainMap.Hmap`, the induced map on cohomology.
* `NerveGeom.geometricHmap U n : Hⁿ_sing(|N(𝓤)|;ℤ₂) →ₗ Ȟⁿ(𝓤;ℤ₂)` is that descent composed with
  the *identity* identification of WP3. **No cohomology-level map is introduced standalone.**

Direction: WP7 explicitly permits the opposite direction when it is more convenient for the
formalization. It is: the geometric construction is covariant on chains, hence contravariant on
cochains, and the Spine has no chain-level cohomology theory to dualise against.

---

## 8. WP8 — which standard comparison theorem is required — `BLOCKED`

The remaining statement is exactly:

> `NerveGeom.geometricHmap U n` is bijective for all `n`
> (equivalently: `J : C_*^simp(S) → C_*^sing(|S|)` is a quasi-isomorphism for every simplicial
> set `S`, applied to `S = coverNerveSSet U`).

Audited routes:

1. **Skeletal/cellular induction.** `|S|` is a CW complex whose `n`-skeleton is obtained from the
   `(n-1)`-skeleton by attaching one `n`-cell per nondegenerate `n`-simplex; the cellular chain
   complex of that structure is the normalized chain complex of `S`. Requires: the CW structure
   on `SSet.toTop.obj S` (`MISSING`), the long exact sequence of a pair and excision
   (`MISSING`), and the identification of cellular with singular homology (`MISSING`).
2. **Acyclic models.** Requires the acyclic-model theorem (`MISSING`), contractibility of
   `|Δ[n]|` together with the computation of its singular homology (`MISSING` — the pinned
   library computes singular homology only for totally disconnected spaces), and freeness of
   both functors on models.
3. **Dold–Kan + normalization.** Mathlib *does* have Dold–Kan and the normalized/unnormalized
   comparison for simplicial objects in an abelian category, so the normalization half is
   available; but it only reduces route 1 or 2 to the normalized complex and does not touch the
   topological content.
4. **A known chain-homotopy equivalence.** None is in the pinned library.

**Is a degree-2-only route materially smaller?** No. All three standard proofs are global in the
degree: computing `H²` still requires the `2`- and `3`-skeleta, the attaching maps, and excision
(or the acyclic-model machinery in degrees `0..3`). The saving would be bookkeeping, not
infrastructure. This is recorded as an honest negative answer, not as an engineering scope
choice.

**Conclusion.** The comparison theorem is standard mathematics but is **not** derivable in the
pinned library without building singular-homology infrastructure (excision / CW theory) that is
entirely absent and is far outside the certification goal. Classification: `BLOCKED`.

---

## 9. WP9 — status of the comparison isomorphism — `BLOCKED`

Not proved. It is recorded as

```lean
structure NerveGeom.GeometricComparison (U : ι → Set X) where
  bijective : ∀ n : ℕ, Function.Bijective (geometricHmap U n)
```

with a degree-two fragment `GeometricComparison₂`. This is an **explicitly conditional
specification**, and it is deliberately *not* of the forbidden shape:

* it is not an arbitrary linear equivalence — it asserts bijectivity of the single canonical map
  built in WP5–WP7;
* it does not bypass the chain/cochain map — `geometricHmap` *is* the descent of `J*`;
* it is not an `isIso` field hiding a gap: the map is fully constructed, and the only thing
  asserted is the truth of a statement about it;
* it is consumed only by declarations that say so in their docstrings, and by nothing in the
  unconditional part of the Spine.

---

## 10. WP10 — transport of the Spin-lift class to the realized nerve — `SPIN_CLASS_TRANSPORT` (conditional)

Given `C : GeometricComparison 𝓤.U`, a good cover `h`, and Task-3 local Spin lifts `D`:

```lean
NerveGeom.spinLiftRealizedClass C h D : Mod2Cohomology.Cohomology (coverNerveRealization 𝓤.U) 2
  := C.equivSymm 2 (GoodCoverZ2.spinLiftCechClassGood h D)
```

* `spinLiftRealizedClass_lift_independent` — independent of the chosen local Spin lifts;
* `spinLiftRealizedClass_eq_zero_iff_cech` — **`[z]_{|N|} = 0 ⟺ [z]_{Ȟ²} = 0`**;
* `spinLiftRealizedClass_eq_zero_iff` — **`[z]_{|N|} = 0 ⟺ coherent Spin transition data exist
  on the fixed cover`** (composing with the Task-6 lifting theorem);
* `frameRealizedClass_eq_zero_iff_spinStructure` — for Task-4 Lorentz frame data,
  **`[z]_{|N|} = 0 ⟺ a Spin structure exists`**.

The class used is the genuine Task-6 class (`GoodCoverZ2.spinLiftCechClassGood`,
`GoodCoverZ2.frameCechClassGood`), reached through the Task-6-to-simplicial identification of
WP3, which is the identity. The class is **not** transported to the manifold `M`.

**Unconditional?** No. Because WP9 is blocked, `[z]_{|N|}` exists only relative to a
`GeometricComparison`. This is stated plainly and is not hidden.

---

## 11. WP11 — supersession of the provisional comparison interface — `SUPERSEDED`

Nothing was deleted. The following declarations now carry the explicit marker
`SUPERSEDED_BY_GEOMETRIC_COMPARISON` in their docstrings or in an in-structure comment:

| declaration | module | marker |
| --- | --- | --- |
| `GoodCoverSpec.SimplicialSingularComparison` | `Spine/GoodCover/SingularComparisonSpec.lean` | `SUPERSEDED_BY_GEOMETRIC_COMPARISON` |
| `GoodCoverSpec.NerveRealization` | `Spine/GoodCover/SingularComparisonSpec.lean` | `SUPERSEDED_BY_GEOMETRIC_COMPARISON` |
| `GoodCoverSpec.SimplicialSingularComparisonSpec` | `Spine/GoodCover/HardenedSpec.lean` | `SUPERSEDED_BY_GEOMETRIC_COMPARISON` |
| `GoodCoverSpec.NerveRealizationSpec` | `Spine/GoodCover/HardenedSpec.lean` | `SUPERSEDED_BY_GEOMETRIC_COMPARISON` (realization half now constructed) |
| `GoodCoverSpec.HardenedComparison` | `Spine/GoodCover/HardenedSpec.lean` | `SUPERSEDED_BY_GEOMETRIC_COMPARISON` |

Downstream certification must use `NerveGeom.GeometricComparison` and
`NerveGeom.NerveTheoremData`, whose only degrees of freedom are the *truth values* of two named
statements about canonical objects. In particular a future theorem can no longer satisfy the
comparison requirement by supplying an arbitrary chain/cochain equivalence unrelated to the
canonical realization map: the specification names `geometricHmap` explicitly.

---

## 12. WP12 — hardened nerve-realization semantics — `SPECIFICATION_HARDENED`

* `NerveGeom.canonicalNervePresentation U : GoodCoverSpec.NervePresentation U` — **constructed**
  (`sset := coverNerveSSet U`, `simplexEquiv := Equiv.refl`, `face_compat := rfl`). The
  simplicial-set half of the Task-8 hardened interface is no longer a hypothesis.
* `NerveGeom.coverNerveRealization U` is *the* meaning of `|N(𝓤)|` from now on. It is a
  definition, not a field: no interface can substitute another space.
* `NerveGeom.NerveTheoremData U` has a **single** field, the homotopy equivalence
  `|N(𝓤)| ≃ X`. The forbidden shape

  ```lean
  realization : TopCat
  equiv : realization ≃ₕ X
  ```

  no longer occurs in the Task-9 layer, and
  `NerveGeom.NerveTheoremData.toNerveRealizationSpec` shows the new datum inhabits the Task-8
  hardened interface with `realization_eq := rfl`.

The three layers stay distinct: `coverNerveSSet 𝓤` (combinatorial) ≠ `coverNerveRealization 𝓤`
(topological) ≠ the base space. No two are identified by definition anywhere.

---

## 13. WP13 — the certification DAG after Task 9

```
                        Task-4 Lorentz frame data
                                   │
                                   ▼
                      Task-3 triple-overlap Spin defect
                                   │
                                   ▼
                 [z] ∈ Ȟ²(𝓤;ℤ₂)          (Task 6, unconditional on a good cover)
                                   │
                    identity  ══════════════  (WP3, `cechCohomologyEquivSSet`, `rfl`)
                                   │
                     H²_simp(N(𝓤);ℤ₂)
                                   ▲
                                   │  geometricHmap 2   (WP5–WP7: canonical, constructed)
                                   │
                    H²_sing(|N(𝓤)|;ℤ₂)
                                   │
                                   │  ◄── BLOCKED: `geometricHmap` bijective (WP8/WP9)
                                   ▼
                      H²_sing(M;ℤ₂)
                                   ▲
                                   │  ◄── BLOCKED: nerve theorem `|N(𝓤)| ≃ M` (WP14)
                                   │        followed automatically by the Task-8
                                   │        homotopy-invariance theorem
```

`NerveGeom.fullComparison` assembles the whole bridge `Ȟⁿ(𝓤;ℤ₂) ≅ Hⁿ_sing(X;ℤ₂)` from exactly
the two blocked edges; the third arrow (homotopy invariance) is the Task-8 **theorem**
`Mod2Cohomology.homotopyEquivCohomology`, not a datum.

**What Task 9 changed in the DAG.** The arrow `H²_simp(N(𝓤)) — H²_sing(|N(𝓤)|)` was previously
*absent*: there was no map at all, only a hypothesised isomorphism. It is now a constructed,
canonical, geometric map; what remains blocked is only its bijectivity.

---

## 14. WP14 — the next missing theorem, exactly

The blocker for `H²_sing(|N(𝓤)|;ℤ₂) ≅ H²_sing(M;ℤ₂)` is the **nerve theorem for a good cover**,
recorded formally as `NerveGeom.NerveTheoremStatement` (a `Prop`, consumed by nothing):

```lean
∀ (U : ι → Set X), (∀ i, IsOpen (U i)) → (⋃ i, U i) = Set.univ →
  ParacompactSpace X → GoodCoverZ2.IsGoodCover U →
    Nonempty (NerveGeom.NerveTheoremData U)
```

Exact hypotheses, itemised (not "good cover"):

| hypothesis | needed? | why | available in the Task-4 model? |
| --- | --- | --- | --- |
| open cover | YES | the partition of unity is subordinate to it; the canonical map `X → |N(𝓤)|` is built from it | YES |
| covering (`⋃ i, U i = univ`) | YES | otherwise the canonical map is not everywhere defined | YES |
| **contractible nonempty finite intersections** | YES | this is the actual homotopical input; it is `GoodCoverZ2.IsGoodCover`, stated on exactly the nerve tuples the Čech complex uses. Empty intersections are excluded and carry no condition | **NO** — good-cover existence needs the Riemannian convexity input recorded as absent since Task 7 |
| numerable cover / partition of unity | YES | the classical proofs (Weil, Segal, Borsuk, tom Dieck) build the comparison map from a partition of unity subordinate to the cover | ~~derivable from paracompactness + open cover~~ **NO** — paracompactness is not derived; **CORRECTED BY TASK 10 WP0** |
| paracompactness of the base | YES (or numerability assumed directly) | it is what produces the subordinate partition of unity | ~~YES — the Task-4 manifold is charted on a finite-dimensional normed space; such a locally compact, second-countable space is paracompact~~ **NO** — **CORRECTED BY TASK 10 WP0**, see the correction section at the end of this file |
| local finiteness of the cover | NO, not separately | implied after refinement by paracompactness; the proof uses local finiteness of the *supports* of the partition of unity | — |
| Hausdorffness | NO for the statement | not used by the classical argument | ~~available anyway~~ **NO** — not assumed and not derived; **CORRECTED BY TASK 10 WP0** |
| weak homotopy equivalence vs homotopy equivalence | the classical theorem gives a *weak* homotopy equivalence in general; it is a genuine homotopy equivalence when both sides have the homotopy type of a CW complex — true for `|N(𝓤)|` always and for a manifold | needs CW theory, `MISSING` in the pinned library |

~~Derivability summary for the Task-4 manifold model: `hopen`, `hcover`, `hparacompact` — YES;
`hcontr` — NO (unchanged from Task 7, where `SpineTop.exists_contractible_refinement` gives
contractible *members* but not contractible finite *intersections*).~~

**CORRECTED BY TASK 10 WP0.**  Correct summary: `hopen` and `hcover` hold only for a cover that
is *given* as open and covering; `hparacompact` — **NO**; `hcontr` — **NO**.  See the correction
section at the end of this file.

Additional infrastructure the nerve theorem itself would need and which is `MISSING` in pinned
Mathlib: partitions of unity subordinate to an arbitrary open cover of a paracompact space in the
form required, the canonical map `X → |N(𝓤)|`, nerve-theorem homotopy inverse construction, and
(for upgrading weak to genuine homotopy equivalence) Whitehead's theorem.

The theorem does **not** emerge for free from present infrastructure, so per instruction it was
not attempted in Task 9.

---

## 15. Results classification table

| result | classification |
| --- | --- |
| `NerveGeom.coverNerveSSet` and its face/degeneracy/identity lemmas | `FULL_SIMPLICIAL_NERVE`, `DERIVED_NATIVE` |
| `underlyingPresimplicial_coverNerveSSet`, `cochain_eq`, `d_eq`, `cocycles_eq`, `coboundaries_eq`, `cechCohomologyEquivSSet` | `DERIVED_NATIVE` |
| `IsDegenerate`, `isDegenerate_iff_exists_degen`, `normalizedCochains` | `DERIVED_NATIVE` |
| `coverNerveRealization`, `charSimplex`, `charMap`, `charSimplex_reindex/face/degen/universal` | `GEOMETRIC_REALIZATION` |
| `chainMap`, `chainMap_comm` | `CHAIN_MAP` |
| `SingularToSimplicialCochainMap`, `geometricCochainMap`, `geometricCochainMap_dual_chainMap`, `Hmap`, `geometricHmap` | `COCHAIN_MAP` |
| `H²_simp(N(𝓤)) ≅ H²_sing(|N(𝓤)|)` | `COHOMOLOGY_ISOMORPHISM` — **`BLOCKED`** |
| `GeometricComparison`, `GeometricComparison₂`, `GeometricComparisonStatement` | `SPECIFICATION_HARDENED`, `BLOCKED` |
| `spinLiftRealizedClass` and its vanishing theorems | `SPIN_CLASS_TRANSPORT` (conditional on `GeometricComparison`) |
| `canonicalNervePresentation` | `SPECIFICATION_HARDENED` (constructed) |
| `NerveTheoremData`, `NerveTheoremData.toNerveRealizationSpec`, `NerveTheoremStatement` | `SPECIFICATION_HARDENED`, `BLOCKED` |
| `fullComparison` | `DEFERRED` (assembled from the two blocked edges) |
| Task-7/8 comparison interfaces | `SUPERSEDED` |
| full nerve theorem, Čech-to-singular on `M`, cover independence, `w₂` | `NOT_REQUIRED` in Task 9 / `DEFERRED` |

---

## 16. Failbuild ledger

Every failed build during Task 9, preserved.

### F1

* **Command** `lake build RequestProject.Spine.Nerve.CoverNerveSSet`
* **Diagnostic** `Invalid field notation: Function 'SimplicialObject.δ_comp_δ' does not have a
  usable parameter of type 'SimplicialObject ...' for which to substitute 'coverNerveSSet U'`
  (and the same for `σ_comp_σ`, `δ_comp_σ_self`, `δ_comp_σ_succ`, `δ_comp_σ_of_le`,
  `δ_comp_σ_of_gt`) — six errors.
* **Cause** In pinned Mathlib the simplicial object is an **explicit** argument of these
  lemmas, so the dot-notation form `(coverNerveSSet U).δ_comp_δ (X := coverNerveSSet U) h` is
  rejected.
* **Repair** Use the plain application `SimplicialObject.δ_comp_δ (coverNerveSSet U) h`, etc.
* **Statement-change classification** NONE — proof-term change only; all six statements are
  byte-identical before and after.

### F2

* **Command** `lake build RequestProject.Spine.Nerve.CochainComparison`
* **Diagnostic** `Type mismatch: Eq.symm heq has type i.castSucc = x but is expected to have
  type x = i.castSucc`; then `Unknown identifier 'x'` and an `unsolved goals` cascade in
  `degen_face_of_repeat`. Plus three deprecation warnings (`Fin.coe_castSucc` →
  `Fin.val_castSucc`) and one unused-`simp`-argument warning.
* **Cause** The orientation of the equation produced by `eq_or_lt_of_le` was mis-read, so the
  intended `subst` never happened and the rest of the branch referred to an eliminated variable.
* **Repair** `subst heq` directly, and restate the two `Fin` identities of that branch
  (`i.predAbove i.castSucc = i`, `i.castSucc.succAbove i = i.succ`) explicitly. Deprecations
  applied; unused `simp` argument removed.
* **Statement-change classification** NONE — proof-term change only.

### F3

* **Command** `lake build RequestProject.Spine.Nerve.Realization`
* **Diagnostic** `Tactic 'rewrite' failed: Did not find an occurrence of the pattern
  (Adjunction.unit ?adj).app ?X ≫ Functor.map ?m ?f` in `charSimplex_universal`, twice.
* **Cause** The goal of the first `ExistsUnique` component is a beta-redex
  `(fun g => …) ((homEquiv …).symm φ)`, so `rw` could not see the pattern; and the functor
  metavariable in `Adjunction.homEquiv_unit` was not determined by the goal.
* **Repair** Introduce the specialised equation `key : ∀ g, unit ≫ toSSet.map g = homEquiv g`
  from `Adjunction.homEquiv_unit`, and `show` the beta-reduced goal before rewriting.
* **Statement-change classification** NONE — proof-term change only.

No other build failed. In particular `RequestProject.Spine.Nerve.ChainMap`,
`RequestProject.Spine.Nerve.CochainMap`, `RequestProject.Spine.Nerve.ComparisonSpec`,
`RequestProject.Spine.Nerve.Core` and the full `lake build` all succeeded on the first attempt
after the three repairs above.

---

## 17. Build evidence

```
$ lake build RequestProject.Spine.Cohomology.Core     ✔  (up to date, part of the full build)
$ lake build RequestProject.Spine.Cech.Core           ✔
$ lake build RequestProject.Spine.Geometry.Core       ✔
$ lake build RequestProject.Spine.Core                ✔
$ lake build RequestProject.Spine.Audit.Firewall      ✔  "SPINE FIREWALL AUDIT: all checks passed"
$ lake build RequestProject.Spine.Nerve.CoverNerveSSet     ✔
$ lake build RequestProject.Spine.Nerve.CochainComparison  ✔
$ lake build RequestProject.Spine.Nerve.Realization        ✔
$ lake build RequestProject.Spine.Nerve.ChainMap           ✔
$ lake build RequestProject.Spine.Nerve.CochainMap         ✔
$ lake build RequestProject.Spine.Nerve.ComparisonSpec     ✔
$ lake build RequestProject.Spine.Nerve.Core               ✔
$ lake build                                          ✔  Build completed successfully (8197 jobs).
```

Import isolation, from the firewall report:

```
Experiment1 direct imports     = 0
Experiment1 transitive imports = 0
Experiment2 direct imports     = 0
Experiment2 transitive imports = 0
external-project imports       = 0
```

Layer order: `Spine.Nerve.CoverNerveSSet` and `Spine.Nerve.CochainComparison` reach neither
`Spine.E1`, `Spine.E2`, `Spine.Geometry`, `Spine.Cohomology` nor any control — the simplicial
nerve is Spin-independent and singular-cohomology-independent. `Spine.Nerve.Realization`,
`.ChainMap`, `.CochainMap`, `.ComparisonSpec`, `.Core` reach no historical experiment module and
no control.

Prohibited constructs: `rg -n "sorry|admit|^axiom |unsafe |partial |implemented_by"` over
`RequestProject/Spine/Nerve/` returns no code hit (the single textual match is the word
"admits" inside a docstring).

---

## 18. Axiom audit

`RequestProject/Spine/Nerve/Core.lean` runs `#print axioms` on 38 principal declarations. Every
one reports

```
[propext, Classical.choice, Quot.sound]
```

The list: `coverNerveSSet`, `coverNerveSSet_delta`, `coverNerveSSet_sigma`,
`degen_repeats_vertex`, `face_face_comm`, `degen_degen_comm`, `face_castSucc_degen`,
`face_succ_degen`, `face_degen_of_le`, `face_degen_of_gt`,
`underlyingPresimplicial_coverNerveSSet`, `d_eq`, `cechCohomologyEquivSSet`,
`isDegenerate_iff_exists_degen`, `normalizedCochains`, `coverNerveRealization`, `charSimplex`,
`charMap`, `charSimplex_reindex`, `charSimplex_face`, `charSimplex_degen`,
`charSimplex_universal`, `chainMap`, `chainMap_comm`, `geometricCochainMap`,
`geometricCochainMap_dual_chainMap`, `SingularToSimplicialCochainMap.Hmap`, `geometricHmap`,
`canonicalNervePresentation`, `NerveTheoremData.toNerveRealizationSpec`,
`GeometricComparison.equiv`, `spinLiftRealizedClass`, `spinLiftRealizedClass_lift_independent`,
`spinLiftRealizedClass_eq_zero_iff_cech`, `spinLiftRealizedClass_eq_zero_iff`,
`frameRealizedClass_eq_zero_iff_spinStructure`, `fullComparison`, `NerveTheoremStatement`.

The firewall additionally audits sixteen Task-9 proof closures against the removed/control-only
constant list.

---

## 19. Negative-result report (as required)

* **What has been constructed.** The full simplicial cover nerve with degeneracies and all
  simplicial identities; its identification with the existing Task-6 cochain complex; the
  canonical geometric realization; the canonical characteristic singular simplex of every
  simplicial simplex with face *and* degeneracy compatibility and its universal property; the
  chain map with `∂J = J∂`; the cochain map with `J*δ = δJ*`; and the induced map on cohomology.
* **What exact theorem remains missing.** That `NerveGeom.geometricHmap U n` is bijective — the
  standard theorem `H*_simp(K;A) ≅ H*_sing(|K|;A)`.
* **Is it standard mathematics?** Yes; it is classical and textbook.
* **What Mathlib currently provides.** See the WP4 table: realization, singular simplicial set,
  the adjunction, realization of standard simplices, and the *definitions* of singular chain
  complexes. No excision, no CW/cellular theory for `SSet.toTop`, no acyclic models, no
  comparison theorem.
* **What native infrastructure would be required.** Either (a) the CW/skeletal filtration of
  `SSet.toTop.obj S` plus the long exact sequence of a pair and excision for the native mod-2
  singular theory, or (b) the acyclic-model theorem plus the computation of the singular
  homology of `|Δ[n]|`. Both are large, and both are unrelated to the Spin-certification goal.
* **Is a degree-2-only route materially smaller?** No — see WP8.
* **Is the gap hidden behind a structure field?** No. It is `NerveGeom.GeometricComparison`,
  documented as a conditional specification, asserting bijectivity of the *constructed* map, and
  consumed only by declarations whose docstrings say they are conditional.

---

## 20. Final scientific questions

> **Is the Task-6 cover nerve now represented by a genuine full simplicial set whose degeneracy
> structure is fixed canonically by the cover data?**

**Yes.** `NerveGeom.coverNerveSSet 𝓤` is an actual functor `Δᵒᵖ ⥤ Set`. Its degeneracies are not
added by hand: they are the action of the codegeneracies of the simplex category under the one
rule "reindex the index tuple", which is available for *every* simplex-category morphism because
enlarging a tuple's index set can only enlarge its intersection. Concretely `sᵢ` repeats the
`i`-th cover index, and the whole structure is determined by the cover data `U : ι → Set X`
alone. Its simplices and faces are *definitionally* the Task-6 ones.

> **Is the space denoted `|N(𝓤)|` now the actual geometric realization of that exact simplicial
> nerve rather than an arbitrary homotopy-equivalent auxiliary space?**

**Yes.** `NerveGeom.coverNerveRealization 𝓤 := SSet.toTop.obj (coverNerveSSet 𝓤)` is a
definition, using the pinned library's geometric-realization functor on the exact simplicial set
above. There is no `realization : TopCat` field anywhere in the Task-9 layer, so no auxiliary
space can occupy that position; the Task-8 interface that permitted one is marked
`SUPERSEDED_BY_GEOMETRIC_COMPARISON`.

> **Has a concrete geometric simplicial-to-singular chain/cochain comparison been constructed
> from the canonical realization simplices?**

**Yes.** `NerveGeom.charSimplex` is the characteristic singular simplex of each nerve simplex,
taken from the unit of the adjunction `SSet.toTop ⊣ TopCat.toSSet` (so it is universal, not
chosen); `charSimplex_face` and `charSimplex_degen` are theorems, not postulates;
`NerveGeom.chainMap` with `chainMap_comm : ∂_sing J = J ∂_simp` is the chain map;
`NerveGeom.geometricCochainMap` with `J*δ_sing = δ_simp J*` is the dual cochain map, proved to be
the transpose of the chain map; and `NerveGeom.geometricHmap` is its descent to cohomology.

> **Is the induced map `H²_simp(N(𝓤);ℤ₂) → H²_sing(|N(𝓤)|;ℤ₂)` proved to be an isomorphism rather
> than supplied as comparison data?**

**No.** This is the one target of Task 9 that was not reached. It is *not* supplied as arbitrary
comparison data either: what is recorded is `NerveGeom.GeometricComparison`, whose only field
asserts bijectivity of the constructed canonical map `geometricHmap`. Proving it requires
singular-homology infrastructure (CW/skeletal filtration of the realization plus excision, or
the acyclic-model theorem) that pinned Mathlib does not have and that would be a large
development unrelated to the certification goal. A degree-2-only route is not materially
smaller. This is the negative result of Task 9 and is reported in full in section 19.

> **Can the genuine Task-6 Spin-lift obstruction now be represented unconditionally as
> `[z]_{|N|} ∈ H²_sing(|N(𝓤)|;ℤ₂)` with the same vanishing criterion?**

**No — conditionally only.** `NerveGeom.spinLiftRealizedClass` and the vanishing theorems
`spinLiftRealizedClass_eq_zero_iff_cech`, `spinLiftRealizedClass_eq_zero_iff` and
`frameRealizedClass_eq_zero_iff_spinStructure` are proved, but they take a
`GeometricComparison` as an argument. Unconditional transport waits on the comparison
isomorphism above. The class transported is the genuine Task-6 class, reached through the
identity identification of WP3, not a new parallel class.

> **After Task 9, is the only major missing fixed-good-cover bridge to `H²_sing(M;ℤ₂)` the
> genuine nerve theorem `|N(𝓤)| ≃ M`, and if not, what exact theorem is still missing?**

**No — there are exactly two, and they are both named.**

1. the **simplicial-to-singular comparison theorem**: `NerveGeom.geometricHmap 𝓤 n` is bijective
   (`NerveGeom.GeometricComparison`, `NerveGeom.GeometricComparisonStatement`);
2. the **nerve theorem** in the genuine shape `|N(𝓤)| ≃ M`
   (`NerveGeom.NerveTheoremData`, `NerveGeom.NerveTheoremStatement`), with hypotheses itemised
   in section 14.

Given both, `NerveGeom.fullComparison` produces `Ȟⁿ(𝓤;ℤ₂) ≅ Hⁿ_sing(M;ℤ₂)` in every degree, the
final arrow being the Task-8 homotopy-invariance **theorem**. Carried over from Task 7 and
unchanged: existence of good covers on the Task-4 manifold model, and existence of common good
refinements, remain open, so cover independence stays conditional.

---

# CORRECTION SECTION — appended by Task 10, WP0 (2026-09-08)

This section is appended, not substituted: the original Task-9 text above is retained for
provenance and the affected passages are struck through in place.

## What was wrong

Task 9 asserted, in this file and in the docstring of `NerveGeom.NerveTheoremStatement`
(`RequestProject/Spine/Nerve/ComparisonSpec.lean`), that

> the Task-4 manifold is charted on a finite-dimensional normed space; such a locally compact,
> second-countable space is paracompact

and that Hausdorffness is "available anyway".  Both are false as statements about the Task-4
layer.  Task 4 assumes exactly `[TopologicalSpace M]`, `[ChartedSpace LorentzCarrier M]` and,
where used, `[IsManifold carrierModel ⊤ M]`.  A charted space need not be second countable, and
being charted on a finite-dimensional normed space does not make it locally compact *as a
global property in the sense required*, nor Hausdorff, nor paracompact.

## Corrected status of the Task-4 layer

| property | assumed by Task 4 | derived in the project |
| --- | --- | --- |
| Hausdorffness (`T2Space`) | no | **no** |
| second countability | no | **no**, and refuted |
| paracompactness | no | **no** |
| metrisability | no | **no** |
| numerability of an arbitrary open cover | no | **no** |
| existence of a good cover | no | **no** (Task 7, unchanged) |

Task 7 (`RequestProject/Spine/GoodCover/ManifoldCovers.lean`) had already stated this correctly;
the error was confined to Task 9.

## The correction is machine-checked

`RequestProject/Spine/Nerve/ManifoldAssumptionAudit.lean` proves

* `SpineTask10.chartedNotSecondCountable` — the disjoint union of continuum-many copies of the
  Task-4 carrier `ℝ × (Fin 3 → ℝ)` is charted on that carrier, is a `C^∞` manifold for
  `carrierModel`, and is **not** second countable;
* `SpineTask10.not_secondCountable_of_charted` — hence "charted on the Task-4 carrier ⟹ second
  countable" is false.

Since second countability was the step by which the Task-9 text reached paracompactness, that
inference is destroyed at the root.  No counterexample is formalised for Hausdorffness or
paracompactness themselves; the claim made about them is only the (true) one that the project
neither assumes nor derives them.

**Nothing has been added to Task 4.**

## Required-vs-derived split for the future nerve theorem

* *Required by the theorem*: open cover, covering, paracompactness (equivalently, numerability
  of the cover), contractible nonempty finite intersections.
* *Currently derived in the project*: none of these, beyond what a statement supplies as a
  hypothesis.

Full details: `TASK10_AUDIT.md`, §1.
