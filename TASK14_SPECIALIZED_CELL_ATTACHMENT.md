# TASK14_SPECIALIZED_CELL_ATTACHMENT.md

**Task 14 — specialized cell attachment and the relative singular bridge.**
Environment: Lean **v4.28.0**, Mathlib at the pinned revision (`lakefile.toml`, `rev = "v4.28.0"`).
Every Lean statement referenced below is machine-checked in the pinned environment; the Task-14
modules contain no `sorry`, no `axiom`, no `unsafe`, no `partial`, no `implemented_by`, no
`native_decide`.

**Hard outcome (WP10): `B — FULL EXCISION IS GENUINELY REQUIRED`** (in the precise form given in
§9: the *small-simplices / barycentric-subdivision* theorem, of which excision, Mayer–Vietoris
and the good-pair quotient theorem are equivalent-strength consequences), **together with a
second, logically independent blocker: injectivity of geometric realization on monomorphisms.**

The simplicial and algebraic halves of the task, by contrast, are **complete**: the skeletal
cell-attachment theorem, the realized pushout, the relative singular chain complex, the pair long
exact sequence, the canonical relative comparison induced by `J = C_*(η_K)`, and the
one-skeleton-step five-lemma are all proved.

---

## 1. WP1 — the frozen data (unchanged)

Nothing from Tasks 9–13 was replaced. The canonical comparison is still

```
J = C_*(η_K),    η_K : K ⟶ Sing |K|   the unit of  SSet.toTop ⊣ TopCat.toSSet
```

and the Task-13 results `C_*^{simp,unn}(K) ≃_ch N_*(K)`, `N_q(K^{(r)},K^{(r-1)}) = 0` for
`q ≠ r`, `N_r(K^{(r)},K^{(r-1)}) ≅ ℤ₂⟨NDeg_r K⟩` stand untouched. The Task-14 relative
comparison `SpineTask14.relJ` is *constructed from* `η` by functoriality
(`SpineTask14.relJ_tau₂ : (relJSC X r).τ₂ = C_*(η)`, proved by `rfl`), never chosen.

---

## 2. WP2 — audit of the pinned topological infrastructure

Read from the pinned **source** tree (`.lake/packages/mathlib/Mathlib/…`), not from generated
documentation.

| item | pinned declaration / file | classification |
| --- | --- | --- |
| geometric realization `SSet.toTop` | `AlgebraicTopology/SingularSet.lean` | `PINNED_DIRECT` |
| singular simplicial set `TopCat.toSSet` | idem | `PINNED_DIRECT` |
| adjunction `sSetTopAdj` | idem | `PINNED_DIRECT` |
| `SSet.toTopSimplex : stdSimplex ⋙ toTop ≅ SimplexCategory.toTop` | idem | `PINNED_DIRECT` |
| left adjoints preserve colimits | `CategoryTheory/Adjunction/Limits.lean` | `PINNED_DIRECT` |
| realization preserves **pushouts** as an instance for the shape needed | — | `PINNED_PARTIAL` (derived here: `SpineTask14.realizationPreservesColimits`, `toTop_isPushout`) |
| realization of a **mono** is injective | — | `MISSING` (**blocker B2**) |
| skeleton `SSet.skeleton` | `SimplicialSet/Skeleton.lean` | `PINNED_DIRECT` |
| **skeletal cell-attachment pushout** | `SimplicialSet/Skeleton.lean`, module `TODO` | `MISSING` upstream (**supplied here**, WP3) |
| boundary `∂Δ[n]` and its inclusion | `SimplicialSet/Boundary.lean` | `PINNED_DIRECT` |
| `Δ[n]`, Yoneda, subcomplexes | `SimplicialSet/StdSimplex.lean`, `Subcomplex.lean` | `PINNED_DIRECT` |
| Eilenberg–Zilber unique decomposition | `SimplicialSet/Degenerate.lean` | `PINNED_DIRECT` |
| pushouts / colimits in `SSet`, in `TopCat` | `CategoryTheory/Limits/*` | `PINNED_DIRECT` |
| singular chain complex functor | `AlgebraicTopology/SingularHomology/Basic.lean` | `PINNED_DIRECT` (but see below) |
| singular homology functor | idem | `PINNED_DIRECT` |
| **relative singular chains** `C_*(X,A)` | — | `MISSING` (**supplied here**, WP7) |
| **relative singular homology** | — | `MISSING` (**supplied here**, WP7/WP8) |
| quotient chain complex / cokernel of complexes | `Algebra/Homology/HomologicalComplexAbelian.lean` | `ALGEBRA_ONLY` (used) |
| short exact sequence of complexes ⇒ LES | `Algebra/Homology/HomologySequence.lean` | `ALGEBRA_ONLY` (used) |
| naturality of the connecting map | `Algebra/Homology/HomologySequenceLemmas.lean` | `ALGEBRA_ONLY` (used) |
| `τ₃` five-lemma for a map of short exact sequences | idem | `ALGEBRA_ONLY` (used) |
| **`τ₂` five-lemma** | idem, explicit `TODO` | `MISSING` upstream (**supplied here**, WP13) |
| four/five lemma in an abelian category | `CategoryTheory/Abelian/DiagramLemmas/Four.lean` | `ALGEBRA_ONLY` (used) |
| **excision** | — | `MISSING` (full-text search for `excision` in the pinned `Mathlib/`: **0 hits**) |
| **barycentric subdivision of singular chains** | — | `MISSING` |
| **small-simplices theorem / Lebesgue-number chain argument** | — | `MISSING` |
| good pair, cofibration, NDR pair | — | `MISSING` |
| cell attachment: `RelativeCellComplex`, `AttachCells` | `AlgebraicTopology/RelativeCellComplex/*` | `TOPOLOGY_ONLY` — a *definition* of cell complexes for the small-object argument; there is **no** theorem giving `\|K\|` such a structure, and no cellular-homology theorem. `NOT_USEFUL` for Task 14. |
| CW complex `CWComplex X` | `Topology/CWComplex/Abstract/Basic.lean` | `TOPOLOGY_ONLY`; same remark. `NOT_USEFUL` here. |
| disk `𝔻 n`, sphere `𝕊 n`, `diskBoundaryInclusion` | `Topology/Category/TopCat/Sphere.lean` | `TOPOLOGY_ONLY` — exist, but nothing relates them to `\|Δ[r]\|`, `\|∂Δ[r]\|`. |
| `H_*(S^n)` | — | `MISSING` |
| reduced homology, homology of a quotient, wedge formula | — | `MISSING` |

### What exactly the pinned skeletal `TODO` leaves unproved

`Mathlib/AlgebraicTopology/SimplicialSet/Skeleton.lean` defines `X.skeleton : ℕ →o X.Subcomplex`
and proves membership criteria (`mem_skeleton`, `skeleton_obj_eq_top`,
`mem_skeleton_obj_iff_of_nonDegenerate`). Its `TODO` block leaves unproved exactly:

1. that `X.skeleton (n+1)` is obtained from `X.skeleton n` by attaching `∂Δ[n] ⟶ Δ[n]` cells
   (and the same for `skeletonOfMono`);
2. that `(SSet.sk n).obj X ≅ X.skeleton (n+1)`.

Item 1 is WP3 and is supplied here. Item 2 is not needed.

---

## 3. WP3 — the simplicial skeletal attachment (`SKELETAL_ATTACHMENT`, **proved**)

Module `RequestProject/Spine/Nerve/Task14SkeletalAttachment.lean`.

**Is the square a pushout in the pinned Mathlib? No** — it is the upstream `TODO`. The smallest
native theorem expressing the required universal property was therefore constructed.

*Degreewise decomposition.* `SpineTask14.skelPiece_bijective` : for every `n` the map

```
(K^{(r-1)})_n  ⊕  Σ_{σ ∈ NDeg_r X} { f : ⦋n⦌ ⟶ ⦋r⦌ // Epi f }  →  (K^{(r)})_n
inl x ↦ x ,  inr (σ,f) ↦ σ·f
```

is a **bijection**. Under Yoneda, `Δ[r]_n = (⦋n⦌ ⟶ ⦋r⦌)` and `∂Δ[r]_n` is the set of
*non-surjective* such maps, so the second summand is `∐_σ (Δ[r]_n ∖ ∂Δ[r]_n)`; a square of sets
whose left edge is a mono is a pushout exactly when the right edge is the disjoint union with
the complement. So this **is** the degreewise pushout statement, and colimits of simplicial sets
are computed degreewise.

*Universal property.* `SpineTask14.AttachData X r Y` packages `φ : K^{(r-1)} ⟶ Y`, cells
`y_σ ∈ Y_r`, and the boundary agreement `Y(h)(y_σ) = φ(σ·h)` for every **non-surjective**
`h : ⦋n⦌ ⟶ ⦋r⦌`. Then

* `attachExtend` — the extension `K^{(r)} ⟶ Y` exists;
* `attachExtend_comp_skInc` — it restricts to `φ`;
* `attachExtend_cell` — it takes the prescribed value on each nondegenerate `r`-simplex;
* `attachExtend_unique` — it is the unique such map.

That is exactly `K^{(r)} ≅ K^{(r-1)} ∪_{∐ ∂Δ[r]} ∐ Δ[r]`, in universal-property form.

*Canonicity of the attaching maps.* The cell of `σ` is `σ·(−)`, i.e. the Yoneda transpose of `σ`
itself (`SpineTask14.cellSimplex`). No attaching map is chosen.
`SpineTask14.mem_skeleton_of_not_epi` proves that this attaching map does land in `K^{(r-1)}`.

*Provenance.* Statement and proof architecture: Goerss–Jardine, *Simplicial Homotopy Theory*,
Ch. I §2 (skeleta and the Eilenberg–Zilber lemma). The Eilenberg–Zilber input is **not**
reproved: it is the pinned `SSet.exists_nonDegenerate`, `SSet.unique_nonDegenerate_simplex`,
`SSet.unique_nonDegenerate_map`. Nakahara contains no simplicial sets and hence nothing here;
its §3.2.1–3.2.2 was used only as a geometric guide. Deviation forced by the pinned API: the
result is packaged as a degreewise bijection plus an explicit universal property rather than as
a `CategoryTheory.IsPushout` on coproducts of `Δ[r]`/`∂Δ[r]`, because the pin has no ready
description of `(∐_I Δ[r])_n` and the universal property is the form actually consumed
downstream. Negative control: nothing stronger is claimed — in particular **no** CW structure on
`|K|` is asserted anywhere.

---

## 4. WP4 — realization of the attachment (`REALIZATION_PUSHOUT`, **proved**)

Module `Task14Comparison.lean`.

* `SpineTask14.realizationPreservesColimits` — the instance `PreservesColimitsOfSize SSet.toTop`,
  obtained from `sSetTopAdj.leftAdjoint_preservesColimits`. This is the actual instance the
  pinned API needs; the slogan "left adjoints preserve colimits" is *not* left as a slogan.
* `SpineTask14.toTop_isPushout` — a pushout square of simplicial sets is carried to a pushout
  square of spaces.

Consequently `|K^{(r)}|` **is** the topological pushout obtained by attaching the realized
`r`-simplices along their realized boundaries. This is stated as "pushout by standard
simplices"; it is **not** called a CW structure, because no CW structure is formally available
(WP20 items 1 and 3).

---

## 5. WP5 — the standard simplex pair in the pin (`STANDARD_CELL_PAIR`, audit)

| description | status in the pin |
| --- | --- |
| `\|Δ[r]\| ≅ Δ^r_top` (the convex topological simplex) | **available**: `SSet.toTopSimplex` |
| `Δ^r_top` is a compact convex set with nonempty interior in a hyperplane of `ℝ^{r+1}` | available in the analysis library, but no simplex↔disk homeomorphism is stated |
| `\|Δ[r]\| ≅ 𝔻 r` | **missing** |
| `\|∂Δ[r]\| ≅ 𝕊 (r-1)` | **missing** |
| `\|∂Δ[r]\| → \|Δ[r]\|` is injective / an embedding onto the geometric boundary | **missing** (special case of blocker B2) |
| `𝔻 n`, `𝕊 n`, `diskBoundaryInclusion` as objects | available, unusable without the two comparisons above |

**Shortest route in this environment.** Since the disk/sphere identifications are missing *and*
`H_*(S^n)` is missing, introducing them would create two new obligations instead of one
(WP5 explicitly warns against this). The shortest formulation is therefore the **direct
relative-chain formulation** of the pair `(|Δ[r]|, |∂Δ[r]|)` used in `Task14Blocker.lean`:
`SpineTask14.stdCellPair r` together with `SpineTask14.relChainCx`. It requires no disk/sphere
equivalence to *state*, and it is the object that the rest of the argument actually consumes.

---

## 6. WP6 — the standard cell pair homology: route audit

Target `H_q^{sing}(|Δ[r]|,|∂Δ[r]|;ℤ₂) = ℤ₂` for `q = r`, `0` otherwise
(`SpineTask14.StandardCellPairAcyclic`, `SpineTask14.StandardCellPairTop`).

| route | what it needs beyond what now exists | verdict |
| --- | --- | --- |
| **P** — pair LES + `\|Δ[r]\|` contractible + `H_*(\|∂Δ[r]\|) = H_*(S^{r-1})` | pair LES: **now available** (WP8). Contractibility of `\|Δ[r]\|`: **available** (Task 12, `realization_stdSimplex_contractible`). `H_*(S^{r-1})`: **missing entirely**, and its standard proof is by induction using Mayer–Vietoris or excision. | needs excision-strength input |
| **Q** — quotient: `\|Δ[r]\|/\|∂Δ[r]\| ≅ S^r` + relative = reduced homology of the quotient | both ingredients missing; the second (`good pair` theorem) is a *consequence of excision*. Also needs blocker B2 to even form the quotient pair. | strictly larger |
| **D** — direct specialized chain proof for this pair | a singular `q`-chain of `\|Δ[r]\|` is an arbitrary continuous family; there is no finite generation and no simplicial approximation available, so a direct computation of `C_*(\|Δ[r]\|)/C_*(\|∂Δ[r]\|)` is not available without subdivision. | not smaller |
| **C** — Mayer–Vietoris / induction on the boundary decomposition | Mayer–Vietoris for singular homology is itself proved from the small-simplices theorem; it is *not* in the pin. | equivalent to excision |

**Conclusion (WP6).** Every audited route passes through the same technical core: the
**small-simplices theorem** (barycentric subdivision of singular chains + a Lebesgue-number
argument + a chain homotopy between subdivision and the identity). No route computes the
standard cell pair without it.

---

## 7. WP7 — the minimal relative singular chain complex (`RELATIVE_SINGULAR`, **proved**)

Module `Task14RelativeChains.lean`. For any morphism of simplicial sets `f : S ⟶ T`:

| required property | Lean |
| --- | --- |
| the chain functor is the project's own complex | `sSetChainComplexFunctor_X`, `sSetChainComplexFunctor_d` (`= NerveGeom.sSetBoundary`), `sSetChainComplexFunctor_map_f` — all `rfl`/Task-13 `afmc_d_hom` |
| 1. inclusion gives a subcomplex | `relSC_shortExact.mono_f` (degreewise `Finsupp.mapDomain_injective`) |
| 2. the quotient differential is well defined | `relBoundary` (via `Submodule.mapQ` and `sSetBoundary_naturality`), `relBoundary_comp` |
| 3. the quotient maps form a chain map | `relProj` |
| 4. functoriality for maps of pairs | `relChainCxMap`, `relChainCxMap_relProj` |
| 5. short exact sequence | `relSC_shortExact` |
| specialisation to a topological pair | `relSingChainCx`, `toSSet_map_injective`, `relSingSC_shortExact` |
| specialisation to a simplicial subcomplex pair | `relSimpChainCx`, `relSimpSC_shortExact` |

Definition used: `C_*^{sing}(X,A) = C_*^{sing}(X)/C_*^{sing}(A)`, exactly as in Hatcher §2.1.
No general relative-homology category was built.

---

## 8. WP8 — the pair long exact sequence (**proved**)

Module `Task14RelativeLES.lean`: `pairDelta`, `pair_exact₁`, `pair_exact₂`, `pair_exact₃`,
and naturality `pairDelta_naturality` (via the pinned `δ_naturality` applied to `relSCMap`).
No generality beyond what WP12/WP13 consume was added.

---

## 9. WP9/WP10 — specialized versus full excision: the decision

### The dependency DAG (topological side)

```
                    (proved, Task 14)                          (missing)
  Eilenberg–Zilber ──▶ WP3 skeletal attachment ──▶ WP4 realized pushout
        (pin)               (Task 14)                  (Task 14)
                                                            │
                                                            ▼
   WP7 relative chains ──▶ WP8 pair LES ──▶ WP12 relJ ──▶  B3  RelJIsIso
        (Task 14)            (Task 14)       (Task 14)      ▲    ▲
                                                            │    │
                                        B1 StandardCellPair─┘    │
                                                 ▲               │
                                                 │               │
                                    ┌────────────┴───────────────┴─────────────┐
                                    │   SMALL-SIMPLICES THEOREM (subdivision)  │
                                    │   ⇒ excision ⇒ Mayer–Vietoris,           │
                                    │     good-pair quotient theorem, H_*(Sⁿ)  │
                                    └──────────────────────────────────────────┘

  B2  RealizationInjective  (independent of everything above)
        │
        ▼
  WP13 one-skeleton step  ◀── WP13 τ₂ five lemma (proved, Task 14)
```

### Route-by-route

* **E1 — full singular excision.** Requires barycentric subdivision of singular chains, the
  small-chain theorem, a Lebesgue-number/cover argument, and a chain homotopy between
  subdivision and the identity. None of the four exists in the pin.
* **E2 — specialized cell-attachment excision.** The desired
  `H_q(|K^{(r)}|,|K^{(r-1)}|) ≅ ⊕_{NDeg_r} H_q(|Δ[r]|,|∂Δ[r]|)` is *not* obtainable from the
  realized pushout alone. The realized square is a pushout of spaces, but singular chains do
  **not** turn pushouts of spaces into pushouts of complexes: a singular simplex of `|K^{(r)}|`
  need not lie in `|K^{(r-1)}|` nor in a single closed cell. Making it lie in one of the two is
  precisely the small-simplices theorem. So E2 does **not** bypass the core; it only bypasses
  the *statement* of excision, not its proof.
* **E3 — quotient/wedge.** Needs (i) `|K^{(r)}|/|K^{(r-1)}| ≅ ⋁ S^r`, (ii) relative homology =
  reduced homology of the quotient for a good pair, (iii) a wedge formula, (iv) `H_*(S^r)`.
  All four are missing, and (ii) is a corollary of excision. Strictly larger than E1.
* **E4 — direct relative chain decomposition.** Fails for the reason given under E2; the
  characteristic simplices generate the relative complex only *after* subdivision.

### Decision (WP10)

```
B — FULL EXCISION IS GENUINELY REQUIRED
```

read precisely as: **the small-simplices/barycentric-subdivision theorem is unavoidable on every
audited route**; excision, Mayer–Vietoris, the good-pair quotient theorem and `H_*(S^n)` are all
downstream of it, and no specialized cell-attachment statement short-circuits it. The decision
is forced by the DAG above, not by counting theorems.

A **second, independent** blocker was found, which is *not* about excision and would remain even
if excision were granted:

```
B2 — geometric realization of a monomorphism of simplicial sets is injective
```

Without B2 the singular chains of `|K^{(r-1)}|` need not inject into those of `|K^{(r)}|`, so the
realized skeletal pair has no relative *pair* sequence at all. The previous audit's warning not
to collapse the two missing components into "excision is missing" is therefore vindicated: the
two components are (i) the cell-attachment/pushout presentation — **now proved** — and (ii) the
relative machinery, which splits further into the *available* algebra (WP7/WP8, proved) and the
*missing* geometry (B1 via subdivision, and B2).

---

## 10. WP11 — the specialized theorem: **not implemented** (`BLOCKED`)

Outcome B was established, so the preferred WP11 target
`H_q^{sing}(|K^{(r)}|,|K^{(r-1)}|;ℤ₂) ≅ ℤ₂⟨NDeg_r K⟩ / 0` is **not** proved. It is stated in Lean
as `SpineTask14.RelJIsIso` (blocker B3) and used only as an explicit hypothesis. No abstract
rank statement was proved in its place, and no unrelated isomorphism was introduced.

---

## 11. WP12 — the canonical relative comparison (`RELATIVE_COMPARISON`, **proved**)

Module `Task14Comparison.lean`.

* `unit_skeletal_square` — the naturality square of the frozen unit `η` for the skeletal pair.
* `relJ X r : C_*(K^{(r)},K^{(r-1)}) ⟶ C_*^{sing}(|K^{(r)}|,|K^{(r-1)}|)` — obtained from that
  square by the WP7 functoriality.
* `relJ_tau₂ : (relJSC X r).τ₂ = C_*(η)` — `rfl`; the comparison really is induced by
  `J = C_*(η_K)` and by nothing else.
* `relJ_generator` — **the generator identification**: on the relative class of a simplex `σ`,
  `J^rel` is the relative class of the *characteristic singular simplex* `η(σ)` of `σ`.

Note that `relJ` exists **unconditionally**; only the *homology* statement about it (B3) is
blocked.

---

## 12. WP13 — the one-skeleton step (`ONE_SKELETON_STEP`, **proved, conditionally on B2 and B3**)

Module `Task14RelativeLES.lean` and `Task14Comparison.lean`.

* `isIso_homologyMap_τ₂` / `quasiIso_τ₂` — the **missing `τ₂` five-lemma** for `ℕ`-indexed chain
  complexes: for a morphism of short exact sequences of complexes, if `τ₁` and `τ₃` are homology
  isomorphisms in every degree, so is `τ₂`. The pin proves only the `τ₃` version and lists the
  `τ₁`/`τ₂` versions as a `TODO`. The proof follows the pinned `τ₃` architecture exactly (four
  lemmas applied to `composableArrows₅`), with the bottom degree `i = 0` — where a chain complex
  over `ℕ` has no further differential — handled by the pinned short-complex four lemma.
* `oneSkeletonStep` (and its repackaging `oneSkeletonStep_of_blockers`):

  ```
  B2 (realization injective)  ∧  H(J|_{K^{(r-1)}}) iso  ∧  B3 (H(J^rel) iso)
      ⟹  H(J|_{K^{(r)}}) iso
  ```

  This is a genuine Lean theorem and an explicit diagram chase, not a slogan. It is the whole of
  Task 14's success condition modulo the two named topological blockers.

No iteration to infinite `K` was attempted (WP14 respected), and the algebraic bridge
(quasi-iso ⇒ chain-homotopy equivalence ⇒ `geometricHmap` bijective) was **not** built (WP15).

---

## 13. WP17 — consistency controls

See `RequestProject/Spine/Nerve/Task14Controls.lean` and `TASK14_TOPOLOGY_SOURCES.md` §5.
Filled triangle and boundary-of-triangle agree with Nakahara Examples 3.9 and 3.8. The
boundary-of-tetrahedron control (Exercise 3.3) was **not performed**; this is recorded, not
hidden. Nothing in the implementation disagrees with Nakahara.

---

## 14. WP19 — the exact remaining theorems

### Blocker B2 — realization of a monomorphism is injective

1. **Statement.** If `i : A ⟶ X` is a monomorphism of simplicial sets, then `|i| : |A| → |X|`
   is injective (equivalently, `Sing|A| → Sing|X|` is degreewise injective).
2. **Lean type.** `SpineTask14.RealizationInjective (X : SSet.{u}) (r : ℕ) : Prop`, i.e.
   `∀ n, Function.Injective ((SpineTask14.singSkInc X r).app n)` — the special case needed.
3. **Hypotheses.** None beyond `Mono i` (equivalently degreewise injectivity of `i`).
4. **Why it cannot be bypassed.** Without it, `C_*^{sing}(|K^{(r-1)}|) → C_*^{sing}(|K^{(r)}|)`
   need not be a monomorphism, so there is no short exact sequence and hence no pair LES on the
   topological side; the five-lemma step has no second row.
5. **Smallest known proof architecture.** The explicit description of `|X|` as
   `(∐_n Δ^n_top × X_n)/∼` together with the statement that every point of `|X|` has a unique
   representative `(t, x)` with `t` interior and `x` nondegenerate (Milnor's theorem; the
   "canonical form" of a point of a realization). None of this is in the pin: the pin defines
   `SSet.toTop` as a left Kan extension and proves nothing about its points.
6. **From Nakahara?** No. Nakahara has no simplicial sets and no geometric realization in this
   sense; his `|K|` (§3.2.2, PDF p. 118) is the polyhedron of a *finite geometric* simplicial
   complex, where injectivity of a subcomplex inclusion is a triviality about subsets of `ℝ^m`
   and gives no information about `SSet.toTop`.
7. **Other source.** Goerss–Jardine, *Simplicial Homotopy Theory*, Ch. I §2 and Ch. III;
   Milnor, *The geometric realization of a semi-simplicial complex*, Ann. of Math. 65 (1957).

### Blocker B1 — homology of the standard cell pair

1. **Statement.** `H_q^{sing}(|Δ[r]|,|∂Δ[r]|;ℤ₂) = 0` for `q ≠ r` and `≅ ℤ₂` for `q = r`,
   generated by the class of the identity singular `r`-simplex.
2. **Lean types.** `SpineTask14.StandardCellPairAcyclic (r : ℕ) : Prop` and
   `SpineTask14.StandardCellPairTop (r : ℕ) : Prop`, both phrased with the Task-14 relative
   complex `relChainCx (stdCellPair r)`.
3. **Hypotheses.** None.
4. **Why it cannot be bypassed.** It is the coefficient of the cellular chain complex: the
   generator identification demanded by WP11/WP12 is exactly the statement that the class of the
   characteristic simplex generates this group.
5. **Smallest known proof architecture.** Small-simplices theorem ⇒ excision ⇒ either
   (a) pair LES with `H_*(S^{r-1})` proved by induction, or (b) the good-pair quotient theorem
   with `|Δ[r]|/|∂Δ[r]| ≅ S^r`.
6. **From Nakahara?** Only as motivation: Example 3.8 (`S¹`, PDF p. 127) and Exercise 3.3
   (`S²`, PDF p. 129) are *instances*; the book has no `H_*(S^n)` and no relative homology, so
   nothing here may be attributed to it.
7. **Other source.** Hatcher, *Algebraic Topology*, §2.1 (Proposition 2.21 and the surrounding
   subdivision argument).

### Blocker B3 — the specialized cell-attachment isomorphism

1. **Statement.** `H_q(J^rel_r)` is an isomorphism for every `q`; equivalently
   `H_q^{sing}(|K^{(r)}|,|K^{(r-1)}|;ℤ₂) ≅ ⊕_{NDeg_r K} H_q^{sing}(|Δ[r]|,|∂Δ[r]|;ℤ₂)` compatibly
   with the characteristic simplices.
2. **Lean type.** `SpineTask14.RelJIsIso (X : SSet.{u}) (r : ℕ) : Prop`.
3. **Hypotheses.** B1, B2, plus additivity over the cells.
4. **Why it cannot be bypassed.** It is the second row of the one-skeleton-step five lemma.
5. **Smallest known proof architecture.** Excision applied to the realized pushout of WP4.
6. **From Nakahara?** No — the book has no cell attachment theory.
7. **Other source.** Hatcher, §2.2 (cellular homology) and the Appendix on cell complexes.

### Recommended Task 15

**Build the small-simplices theorem for singular chains over `ℤ₂`, and B2, in that order.**
Concretely, the minimal Task-15 theorem family is:

1. `sd : C_*^{sing}(X) ⟶ C_*^{sing}(X)`, barycentric subdivision of singular chains, and a chain
   homotopy `T` with `∂T + T∂ = 1 − sd`;
2. for an open cover `𝓤` of `X`, the subcomplex `C_*^{𝓤}(X)` of `𝓤`-small chains, and the
   theorem that its inclusion is a chain-homotopy equivalence (small-simplices theorem);
3. excision `H_*(X∖Z, A∖Z) ≅ H_*(X,A)` under `cl Z ⊆ int A`, as a corollary;
4. `|i|` injective for `i` a monomorphism of simplicial sets (blocker B2), via the canonical form
   of a point of a realization;
5. then B1 and B3, and finally `oneSkeletonStep` becomes unconditional.

Items 1–3 are the single largest missing block and are entirely independent of the Spine; item 4
is independent of items 1–3 and can be done in parallel.

---

## 15. Endpoint classification

| endpoint | classification |
| --- | --- |
| pinned topological-infrastructure audit (§2) | `MATHLIB_NATIVE` (audit) |
| Nakahara Chapter-3 source audit | `NAKAHARA_SOURCED` |
| skeletal simplicial attachment theorem (WP3) | `PROJECT_NATIVE`, `SKELETAL_ATTACHMENT` — **proved** |
| realized pushout (WP4) | `MATHLIB_NATIVE` + `PROJECT_NATIVE`, `REALIZATION_PUSHOUT` — **proved** |
| standard simplex pair audit (WP5) | `BLOCKED` |
| standard cell-pair relative homology (WP6) | `BLOCKED` (blocker B1) |
| minimal relative singular chains (WP7) | `PROJECT_NATIVE`, `RELATIVE_SINGULAR` — **proved** |
| relative LES (WP8) | `MATHLIB_NATIVE` + `PROJECT_NATIVE` — **proved** |
| specialized-vs-full excision decision (WP9/WP10) | `FULL_EXCISION_REQUIRED`, `NEGATIVE_RESULT` |
| strongest specialized cell-attachment theorem (WP11) | `BLOCKED` (blocker B3) |
| canonical relative comparison induced by `J` (WP12) | `PROJECT_NATIVE`, `RELATIVE_COMPARISON` — **proved** |
| one-skeleton-step comparison (WP13) | `PROJECT_NATIVE`, `ONE_SKELETON_STEP` — **proved conditionally on B2, B3** |
| `τ₂` five lemma | `PROJECT_NATIVE` — **proved** (upstream `TODO`) |
| infinite passage (WP14), algebraic bridge (WP15) | `DEFERRED` |
| boundary-of-tetrahedron control (WP17) | `NOT_USED` / not performed |

---

## 16. Final questions, answered

**Does the pinned Mathlib already prove `K^{(r)} = K^{(r-1)} ∪_{∐∂Δ[r]} ∐Δ[r]` as the required
simplicial pushout?**
No. It is an explicit open `TODO` in `Mathlib/AlgebraicTopology/SimplicialSet/Skeleton.lean`.
Task 14 supplies it natively: `SpineTask14.skelPiece_bijective` (degreewise pushout) together
with `attachExtend`, `attachExtend_comp_skInc`, `attachExtend_cell`, `attachExtend_unique`
(universal property).

**Does geometric realization theorem-level carry this to the corresponding topological pushout?**
Yes. `SpineTask14.realizationPreservesColimits` (the actual pinned instance) and
`SpineTask14.toTop_isPushout`. `|K^{(r)}|` is the pushout obtained by attaching the realized
standard simplices along their realized boundaries. It is **not** claimed to be a CW complex.

**What exact description of `(|Δ[r]|, |∂Δ[r]|)` is available in the pin?**
Only `|Δ[r]| ≅ Δ^r_top` (`SSet.toTopSimplex`). There is **no** `|Δ[r]| ≅ 𝔻 r`, **no**
`|∂Δ[r]| ≅ 𝕊 (r-1)`, and not even injectivity of `|∂Δ[r]| → |Δ[r]|`. The shortest usable
formulation in this pin is the direct relative-chain one (`SpineTask14.stdCellPair`).

**Can `H_q^{sing}(|Δ[r]|,|∂Δ[r]|;ℤ₂)` be computed without developing full singular excision?**
No. All four audited routes (P, Q, D, C) reduce to the small-simplices/barycentric-subdivision
theorem, which is absent from the pin.

**Which parts are directly supported by Nakahara, and which require another source?**
Nakahara supports: simplexes and their faces, the polyhedron `|K|` and triangulation (§3.2,
PDF pp. 117–119), chain/cycle/boundary groups and `H_r(K;ℤ₂)` (§3.3.2–3.3.3, pp. 121–126), and
the two consistency examples `S¹` (Ex. 3.8, p. 127) and the filled triangle (Ex. 3.9, p. 128).
Nakahara supports **none** of: relative homology, the pair LES, excision, subdivision, CW/cell
attachment, `H_*(S^n)` for general `n`, simplicial sets or geometric realization. Those required
Hatcher (relative chains, LES, excision, cellular homology) and Goerss–Jardine/Milnor (skeletal
attachment, realization of monos).

**Is a minimal project-native relative singular chain complex and pair LES sufficient for the
standard cell pair?**
No. They are necessary and are now built (`Task14RelativeChains.lean`, `Task14RelativeLES.lean`),
but they are purely formal: they transport information, they do not create it. Computing the
standard cell pair additionally needs B1, i.e. subdivision.

**Can one prove the specialized theorem
`H_q^{sing}(|K^{(r)}|,|K^{(r-1)}|) ≅ ⊕_{NDeg_r} H_q^{sing}(|Δ[r]|,|∂Δ[r]|)` without full
excision?**
No. The realized square is a pushout of spaces, but singular chains do not send pushouts of
spaces to pushouts of complexes; making a singular simplex small enough to lie in one piece is
exactly the missing theorem.

**Decision.**

```
B: FULL EXCISION IS REQUIRED
```

(in the precise sense of §9: the small-simplices/subdivision theorem, of which excision is the
standard packaging), **plus** the independent blocker B2.

**Is the relative comparison induced by the actual canonical map `J = C_*(η_K)`?**
Yes — `SpineTask14.relJ_tau₂` proves it by `rfl`, and `SpineTask14.relJ_generator` proves that
`J^rel[σ]` is the characteristic singular simplex of `σ`.

**Has the one-skeleton-step theorem been proved?**
Yes, in the strongest form the pin allows: `SpineTask14.oneSkeletonStep` proves
`H(J|_{K^{(r-1)}})` iso `∧` `H(J^rel)` iso `∧` B2 `⟹` `H(J|_{K^{(r)}})` iso, using the pair LES,
naturality and the newly proved `τ₂` five lemma. It is unconditional *as an implication*; its
hypotheses B2 and B3 are the blockers.

**What is the exact smallest Task-15 theorem family required?**
Items 1–4 of §14 ("Recommended Task 15"): barycentric subdivision of singular chains with its
chain homotopy; the small-simplices theorem for an open cover; excision as its corollary; and,
independently, injectivity of the realization of a monomorphism of simplicial sets.

---

## TASK 15 CORRECTION SECTION (append-only; nothing above is deleted)

Task 15 revisited the two conclusions recorded above and corrects them as follows.  See
`TASK15_AUDIT.md` for the evidence.

1. **The endpoint label `B — FULL EXCISION IS GENUINELY REQUIRED` is withdrawn.**  No
   impossibility theorem was ever proved, in Task 14 or in Task 15.  The justified formulation
   is:

   > No audited specialized route bypasses excision-strength small-simplices infrastructure in
   > the pinned environment.

   Task 15 additionally sharpens the diagnosis: on every audited route the *first* obstruction is
   not excision but the absence of any evaluation of the left Kan extension defining
   `SSet.toTop` outside the representables — i.e. the absence of a pointwise model for the
   points of `|X|`.  Excision is the *second* obstruction.

2. **Task-14 status, recorded accurately.**
   * WP3, concrete simplicial attachment: **proved** (Task 14).
   * Generic realization of categorical pushouts: **proved** (Task 14).
   * Their concrete theorem-level composition: **proved in Task 15**, as
     `SpineTask15.skeletalIsPushout`, `skeletalIsPushout_toTop` and
     `skeletalIsPushout_toTop_coprod`.

3. **Blocker `B2` is no longer an open statement about arbitrary simplicial sets.**  Task 15
   proves `SpineTask15.realization_skInc_injective`: injectivity of `|K^{(r-1)}| → |K^{(r)}|`
   for every `K` follows from injectivity of `|∂Δ[r]| → |Δ[r]|` alone
   (`SpineTask15.StandardCellMono r`), which is proved outright for `r = 0`.

4. **Blockers `B1` and `B3` are unchanged and still open.**
