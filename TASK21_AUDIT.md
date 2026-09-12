# TASK 21 AUDIT — single standard-cell relative `J` isomorphism

**Outcome: A — the single-cell comparison is closed.**
For every `r` and every `q`, the homology map induced by the *existing, frozen* `cellRelJ r`
is an isomorphism, and the result is additionally packaged as a quasi-isomorphism.

---

## 1. Exact production pin

* Lean `v4.28.0` (`lean-toolchain`, unchanged).
* Mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
  (`lake-manifest.json`, unchanged; `lakefile.toml` unchanged).
* No newer upstream result was imported; the only new Mathlib imports are
  `Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence`, already transitively present through
  Task 13.

## 2. Exact existing `cellRelJ` used

`SpineTask20.cellRelJ` from `RequestProject/Spine/Nerve/Task20CanonicalGenerator.lean`:

```lean
def cellRelJ (r : ℕ) :
    relChainCx ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι) ⟶ relChainCx (stdCellPair.{u} r) :=
  relChainCxMap _ _ (sSetTopAdj.unit.app _) (sSetTopAdj.unit.app _)
    (sSetTopAdj.unit.naturality (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι)
```

i.e. `J = C_*(η)` for the adjunction unit, applied to the pair `(Δ[r], ∂Δ[r])`.  It was **not**
redefined, replaced, or wrapped in a new quasi-isomorphic model.  Every Task-21 theorem is
stated for this morphism, accessed through the project-native
`HomologicalComplex.homologyMap (cellRelJ r) q`.

## 3. Exact simplicial source homology results reused

Audit result: **the simplicial relative homology of `(Δ[r], ∂Δ[r])` did not exist in the
project in any degree.**  Searching the whole tree, the only source-side statements available
were:

* `SpineTask14.relChainCx`, `relBoundary`, `relProj`, `relSC_shortExact`,
  `relSimpSC_shortExact` — the relative complex itself and its short exact sequence;
* `SpineTask20.simplicialTop_mem_Zc` — the identity `r`-simplex is a relative cycle;
* `SpineTask13` normalization data for the *absolute* unnormalized complex:
  `proj` ( = `P∞`), `proj_degen_zero`, `sub_proj_mem_degen`, `degenSubmodule`,
  `single_degen_mem`, `normInc_natural` (naturality of `P∞`), `normHtpy`, `normHtpy_zero`,
  `normHtpy_succ`;
* `SpineTask19.hcls`, `hcls_surjective`, `hcls_eq_zero_iff`, `hcls_smul`, `homologyMap_hcls`,
  `Zc`, `mem_Zc_succ` — the element-level homology dictionary.

Nothing of the source-side *calculation* pre-existed, so it is proved here — directly at chain
level, with no new general homology machinery.

## 4. Source-side lemmas newly required

In `RequestProject/Spine/Nerve/Task21Normalization.lean`:

| declaration | statement |
| --- | --- |
| `SpineTask21.homotopyPToId_hom_naturality` | the Dold–Kan homotopies `P q ≃ id` are natural in the simplicial object (induction on `q`, using the pinned `P_f_naturality` and `hσ'_naturality`) |
| `SpineTask21.homotopyPInftyToId_hom_naturality` | the same for `P∞` |
| `SpineTask21.normHtpy_natural` | `C(φ) ∘ h_S = h_T ∘ C(φ)` for the Task-13 normalization homotopy |

In `RequestProject/Spine/Nerve/Task21SingleCellRelJ.lean`:

| declaration | statement |
| --- | --- |
| `single_mem_range_of_not_surjective` | a non-surjective simplex of `Δ[r]` spans a chain carried by `∂Δ[r]` |
| `single_mem_degen_of_surjective` | a **surjective** simplex of `Δ[r]` in a degree `q ≠ r` is degenerate (`SimplexCategory.eq_σ_comp_of_not_injective` plus the cardinality comparison) |
| `proj_natural` | naturality of `P∞` in element form (from `normInc_natural`) |
| `proj_mem_range` | for `q ≠ r`, `P∞` maps `C_q(Δ[r])` into the image of `C_q(∂Δ[r])` |
| `isZero_simpRel_homology` | **`H_q^{simp}(Δ[r],∂Δ[r];ℤ₂) = 0` for `q ≠ r`** |
| `exists_smul_relTop` | in degree `r` the relative chain module is spanned by the class of the identity `r`-simplex |
| `exists_smul_simpTopClass` | hence every class in `H_r^{simp}` is a multiple of `e_r` |

Consequently the required source-side statement

`H_q^{simp}(Δ[r],∂Δ[r];ℤ₂) ≅ ℤ₂` for `q = r`, `= 0` otherwise

holds: the vanishing is `isZero_simpRel_homology`, and one-dimensionality in degree `r` is
recorded as `isLine_simpRel_homology_top` (with `simpTopClass_ne_zero`), obtained after the
comparison theorem by transporting Task 19's `isLine_relHomology_top` through it.

## 5. Non-top-degree proof route

Exactly the preferred route.

1. Source is zero: `isZero_simpRel_homology r q hqr`.
   Chain-level argument: every simplex of `Δ[r]` in degree `q ≠ r` is either non-surjective
   (hence a simplex of `∂Δ[r]`) or surjective and therefore degenerate; `P∞` kills degenerate
   chains and is natural, so `P∞` lands in the boundary chains (`proj_mem_range`).  The Task-13
   identity `∂h + h∂ = id + P∞`, whose homotopy is natural by
   `Task21Normalization.normHtpy_natural`, then descends to the quotient complex and exhibits
   every relative cycle as a relative boundary.
2. Target is zero: `SpineTask19.standardCellPairAcyclic r q hqr` (Task 19 / blocker B1).
3. Both homology modules are subsingletons, so the unique morphism between them is bijective,
   hence an isomorphism (`ConcreteCategory.isIso_iff_bijective`).  No explicit inverse was
   constructed.

## 6. Top-degree generator used

`SpineTask21.simpTopClass r = hcls (Submodule.Quotient.mk (Finsupp.single (topSimp r) 1))
(SpineTask20.simplicialTop_mem_Zc r)` — the class of the *canonical* simplicial relative cycle,
the identity `r`-simplex `topSimp r = ULift.up (𝟙 ⦋r⦌)`.  No arbitrary basis vector is chosen.

## 7. Exact theorem showing its image under `cellRelJ`

`SpineTask21.homologyMap_cellRelJ_simpTopClass r`, which is literally Task 20's
`SpineTask20.homologyMap_cellRelJ_top r`:

```
(HomologicalComplex.homologyMap (cellRelJ r) r).hom (simpTopClass r) = stdCellGenerator r
```

together with `SpineTask20.stdCellGenerator_eq_stdCellTopClass` and
`SpineTask20.stdCellGenerator_ne_zero`.

## 8. Top-degree injectivity

`SpineTask21.bijective_homologyMap_cellRelJ_top`, first component.
Every class of the source is `c • e_r` with `c : ZMod 2` (`exists_smul_simpTopClass`, from the
chain-level spanning statement `exists_smul_relTop`).  Its image is `c • γ_r`.  For `c = 1` this
is `γ_r ≠ 0` (`stdCellGenerator_ne_zero`), so a class in the kernel has `c = 0` and is zero.

## 9. Top-degree surjectivity

`SpineTask21.bijective_homologyMap_cellRelJ_top`, second component.
The target is one-dimensional over `ZMod 2` (Task 19), so each element is `0` or
`stdCellTopClass r` (`eq_zero_or_eq_stdCellTopClass`); `0` is the image of `0`, and
`stdCellTopClass r = γ_r` is the image of `e_r`.

No determinants, dimensions or bases were used; the argument is the minimal one for
one-dimensional `ZMod 2`-modules.

## 10. Final all-degree `IsIso` theorem

```lean
theorem SpineTask21.isIso_homologyMap_cellRelJ (r q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cellRelJ.{u} r) q)
```

with the packaged form

```lean
def SpineTask21.homologyIso_cellRelJ (r q : ℕ) :
    (simpRel.{u} r).homology q ≅ relHomology (stdCellPair.{u} r) q
```

realising, for the existing canonical `J`,
`H_q^{simp}(Δ[r],∂Δ[r];ℤ₂) ≅ H_q^{sing}(|Δ[r]|,|∂Δ[r]|;ℤ₂)` for all `r, q`.

## 11. Quasi-isomorphism packaging

Obtained, and immediate: `instance SpineTask21.quasiIso_cellRelJ (r : ℕ) : QuasiIso (cellRelJ r)`
via the pinned `quasiIsoAt_iff_isIso_homologyMap`.  No new abstract infrastructure was built.

## 12. Attached-cell additivity

**Still open.**  Nothing about a family of cells, about coproducts of standard cell pairs, or
about the relative skeletal quotient being a sum of standard-cell pairs, was proved or used.
That statement is only mentioned here as the next intended step (Task 22).

## 13. B3

**Still open.**  `SpineTask14.RelJIsIso` is untouched and remains a hypothesis;
`SpineTask15.finiteDimensional_homologyIso` remains conditional on it.  No global
simplicial–singular comparison theorem was used or proved, and `geometricHmap`, the nerve
theorem and `w₂(TM)` were not touched.

## 14. First exact missing theorem

Not applicable: full success (Outcome A) for the stated scope.  The first theorem *outside*
this scope, needed by Task 22, is the additivity statement: for a family `σ ∈ NDeg_r(K)`, the
relative comparison of the skeletal pair `(K^{(r)}, K^{(r-1)})` decomposes as the coproduct of
the standard-cell comparisons proved here, i.e. that
`relChainCx (skInc K r)` and `relChainCx (singSkInc K r)` split as `⊕_σ` of the standard-cell
relative complexes compatibly with `J` (in the project's names, the missing input to
`SpineTask14.RelJIsIso`).

---

## Verification

* `lake build RequestProject` → **Build completed successfully (8254 jobs)**, including the
  pre-existing spine firewall audit (`SPINE FIREWALL AUDIT: all checks passed`).
* `RequestProject/Spine/Nerve/Task21AxiomAudit.lean` runs `#print axioms` on every principal
  Task-21 declaration; each reports exactly `[propext, Classical.choice, Quot.sound]`.
  In particular `isZero_simpRel_homology`, `bijective_homologyMap_cellRelJ_top`,
  `isIso_homologyMap_cellRelJ`, `homologyIso_cellRelJ` and `quasiIso_cellRelJ` are free of
  `sorryAx`.
* No `sorry`, `admit`, new `axiom` or `native_decide` occurs in the new modules.
* No existing module, the toolchain, the lakefile or the manifest was modified.
