# TASK 22 AUDIT — finite cell-family relative decomposition and `J` compatibility

**Principal outcome: C — the source finite-family decomposition is closed, the singular
finite-family decomposition is blocked.**

Beyond Outcome C, the *componentwise compatibility of the frozen `relJ`* (WP4, the principal
compatibility theorem) **is also closed**, unconditionally, together with the §7 geometric
separation statement.  What is missing, and only what is missing, is the singular cell-family
decomposition itself (WP3).  The exact first missing theorem is stated in §14 below.

---

## 0. Production pin

* Lean `v4.28.0` (`lean-toolchain`, unchanged).
* Mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (`lake-manifest.json`, unchanged;
  `lakefile.toml` unchanged).
* No newer upstream theorem is imported; no existing module was modified.
* The comparison `J = C_*(η)` is untouched: `SpineTask14.relJ` and `SpineTask20.cellRelJ` are
  used exactly as they stand and are never replaced.

New modules (all in namespace `SpineTask22`):

| module | content |
| --- | --- |
| `RequestProject/Spine/Nerve/Task22FiniteCellAdditivity.lean` | WP1 finite direct sum; the general relative-chain lemmas; WP2 source decomposition |
| `RequestProject/Spine/Nerve/Task22RelJCompatibility.lean` | the realized cell family; WP4 comparison square; generator statements; the open WP3 proposition |
| `RequestProject/Spine/Nerve/Task22CellSeparation.lean` | §7 geometric separation of the realized cell family |
| `RequestProject/Spine/Nerve/Task22AxiomAudit.lean` | `#print axioms` for every principal declaration |

---

## 1. The finiteness assumption used

**None was needed.**

The source decomposition, the comparison square and the generator statements are proved for an
*arbitrary* family `X.nonDegenerate r`, with no `Finite` or `Fintype` instance anywhere.  The
reason is that the direct sum used is the `Finsupp` direct sum

`⊕_{σ ∈ X.nonDegenerate r} M  :=  (↑(X.nonDegenerate r) →₀ M)`,

which is the *coproduct* of the family in `Module (ZMod 2)` for any index type, and the
source-side calculation (Task 13) is already a statement about a free module on
`X.nonDegenerate r`.  No arbitrary-coproduct *preservation* theorem is used anywhere: the
decomposition map is built by hand as `Finsupp.lsum` of the canonical cell components, and the
proof of bijectivity is elementary.

For a finite family the same object is the finite biproduct; this is recorded explicitly as

```lean
def SpineTask22.finiteBiproduct_of_fintype (α : Type u) [Finite α] (M : Type u) [AddCommGroup M]
    [Module (ZMod 2) M] : (α →₀ M) ≃ₗ[ZMod 2] (α → M)
```

so that the finite-family framing requested by Task 22 is available, but it is not needed by
any theorem below.  **This is a strengthening of the statements requested, not a weakening**;
nothing was assumed to make a build pass.

## 2. Is the whole simplicial set required finite?

No.  Neither `X` nor `X.nonDegenerate r` is required finite anywhere in Task 22.

## 3. The exact Task-13 source decomposition reused

Reused verbatim, not rebuilt:

* `SpineTask13.RelNormChain`, `SpineTask13.RelChain`;
* `SpineTask13.relNormChain_subsingleton_of_lt` and
  `SpineTask13.relNormChain_subsingleton_of_gt` — the vanishing of the relative *normalized*
  chains of the skeletal pair in every degree `q ≠ r`;
* `SpineTask13.normChainEquiv` and `SpineTask13.normChainEquiv_apply` — the normalized chains
  are free on the nondegenerate simplices;
* `SpineTask13.normChain_skeleton_subsingleton` — normalized chains of `Sk X n` vanish in
  degrees `≥ n` (used in degree `r` for `Sk X r` and in degree `r+1` for `Sk X (r+1)`);
* `SpineTask13.nonDegenerateSkeletonEquiv` — `(Sk X (r+1)).nonDegenerate r ≃ X.nonDegenerate r`;
* the Task-13 normalization data `proj` (`P∞`), `normProj`, `normMap`, `normHtpy`,
  `proj_degen_zero`, `normProj_natural`, `normProj_comm`, `normHtpy_zero`, `normHtpy_succ`;
* Task 21's `SpineTask21.normHtpy_natural` (naturality of the homotopy) and
  `SpineTask21.proj_natural`.

`SpineTask13.relNormChainEquiv`, `relNormProj`, `relNormInc` are *not* used directly: the
argument needs only the two subsingleton statements plus `normChainEquiv`, which avoids having
to build the relative normalized complex as a chain complex.  Nothing of the Task-13
calculation is re-proved.

## 4. The exact Task-15 realized pushout reused

`SpineTask15.skeletalIsPushout X r`, transported to `Type` by the colimit-preserving functor
`SpineTask15.Real = SSet.toTop ⋙ forget TopCat`:

```lean
theorem SpineTask22.realIsPushout :
    IsPushout (Real.map (attachMap X r)) (Real.map (bdryMap X r))
      (Real.map (skInc X r)) (Real.map (cellMap X r))
```

together with `SpineTask15.attachSrc`, `attachTgt`, `bdryMap`, `attachMap`, `cellMap`,
`cellChar`, `cellAttach`, `cellAttach_comm`, `Real_sigmaMap_injective`, and the unconditional
`SpineTask16.standardCellMono`.

`SpineTask15.skeletalIsPushout_toTop_coprod` is the frozen *topological* form of the same
square; it is the input that the missing WP3 argument would consume (see §14).  It is not used
in any proved Task-22 theorem, because Task 22 stops before the excision step.

## 5. The exact Task-18 excision theorem reused

**None.**  `SpineTask18.isIso_homologyMap_excisionMap` / `SpineTask18.excisionIso` were audited
as the intended engine for WP3, but they could not be applied: they require two *open* subsets
`U, V` of `|Sk X (r+1)|` with `U ∪ V = univ`, and the excisive family is exactly what is still
missing (see §8 and §14).  No Task-18 result appears in the proof of any Task-22 theorem.

## 6. The source finite-family homology decomposition

Endpoint:

```lean
theorem SpineTask22.isIso_srcDecomp (X : SSet.{u}) (r q : ℕ) : IsIso (srcDecomp X r q)
def       SpineTask22.srcDecompIso  (X : SSet.{u}) (r q : ℕ) :
    srcSumMod X r q ≅ (relChainCx (skInc X r)).homology q
```

i.e.

`⊕_{σ ∈ X.nonDegenerate r} H_q^{simp}(Δ[r], ∂Δ[r]; ℤ₂)  ≅  H_q^{simp}(Sk X (r+1), Sk X r; ℤ₂)`,

where the `σ`-component of the map is the **canonical** one:
`SpineTask22.cellPairMap X r σ`, induced by the Task-15 characteristic map
`SpineTask15.cellChar X r σ` and attaching map `SpineTask15.cellAttach X r σ`.  No noncanonical
isomorphism is chosen anywhere.

Route (all new, but built only from the Task-13/Task-21 inputs of §3):

1. `hcls_rel_eq_zero_of_proj_mem_range` — the general form of Task 21's vanishing argument: if
   `P∞ x` is carried by the subobject then the relative class of the cycle `x` is zero.
2. `proj_mem_range_of_normMap_surj` — if every normalized chain of the total object comes from
   the subobject, then so does `P∞` of every chain.
3. `normChain_mem_range_of_ne` (Task 13) ⟹ `proj_skel_mem_range` ⟹
   **`isZero_skelRel_homology`: `H_q^{simp}(Sk X (r+1), Sk X r; ℤ₂) = 0` for `q ≠ r`.**
4. `subsingleton_relChain_of_lt` — the relative *unnormalized* chains vanish in degrees `< r`,
   so in degree `r` every relative chain is a cycle (`mem_Zc_top`) and `topCls` is a linear map.
5. `topCls_eq_of_normProj_eq` — in degree `r` the relative class only depends on the
   normalization.
6. `phi` : `(X.nonDegenerate r →₀ ℤ₂) → H_r^{simp}(Sk X (r+1), Sk X r; ℤ₂)`, `σ ↦ [σ]`, is
   **bijective** (`bijective_phi`); injectivity uses `normProj_comm` plus
   `normChain_skeleton_subsingleton` in degrees `r` and `r+1`, surjectivity uses `normChainEquiv`
   and `nonDegenerateSkeletonEquiv`.
7. `lineEquiv r : ℤ₂ ≃ₗ H_r^{simp}(Δ[r], ∂Δ[r]; ℤ₂)` from Task 21
   (`exists_smul_simpTopClass`, `simpTopClass_ne_zero`), and
   `srcDecomp_lineSumEquiv` identifies `srcDecomp` in degree `r` with `phi`.
8. In degrees `q ≠ r` both sides are zero (`isZero_simpRel_homology` from Task 21 and
   `isZero_skelRel_homology`), so the canonical map is an isomorphism there too.

## 7. The singular finite-family homology decomposition

**Not obtained.**  The map is constructed,

```lean
def SpineTask22.tgtDecomp (X : SSet.{u}) (r q : ℕ) :
    tgtSumMod X r q ⟶ (relChainCx (singSkInc X r)).homology q
```

with `σ`-component `SpineTask22.topCellPairMap X r σ`, the map of relative singular complexes
induced by the realized characteristic map `|cellChar X r σ|`; but the statement that it is an
isomorphism is only *stated*, as

```lean
def SpineTask22.SingularCellFamilyAdditivity (X : SSet.{u}) (r : ℕ) : Prop :=
  ∀ q, IsIso (tgtDecomp X r q)
```

and is **never assumed** anywhere in the project (it occurs only as an explicit hypothesis of
the single conditional corollary of §11).

## 8. The exact excisive-family / separation theorem used

The §7 separation statement **is proved**, in
`RequestProject/Spine/Nerve/Task22CellSeparation.lean`, at the level of underlying sets:

* `range_skInc_union_range_cellMap` — `|Sk X r|` and `∐_σ |Δ[r]|` jointly cover `|Sk X (r+1)|`;
* `real_cellMap_eq_skInc_iff` — a cell point and a skeleton point are identified **iff** they
  come from `∐_σ |∂Δ[r]|`;
* `real_cellMap_eq_cellMap_iff` — two cell points are identified **iff** they are equal, or
  both lie on the boundary with the same attaching image;
* `real_cellMap_injOn_compl_bdry` — the total characteristic map is injective off the boundary;
* `real_cellMap_notMem_range_skInc` — open cell points miss the old skeleton;
* **`compl_range_skInc`** —
  `(range |skInc|)ᶜ = |cellMap| '' (range |bdryMap|)ᶜ`, i.e. *the complement of the old skeleton
  in `|Sk X (r+1)|` is the disjoint union of the open cells indexed by `X.nonDegenerate r`.*

Inputs: only `SpineTask15.skeletalIsPushout` (transported by the colimit-preserving `Real`),
`SpineTask15.Real_sigmaMap_injective`, the unconditional `SpineTask16.standardCellMono`, and the
pinned `CategoryTheory.Limits.Types.Pushout` API (`quot_mk_eq_iff`, `inl_rel'_inl_iff`,
`inl_eq_inr_iff`).  No local finiteness, no closure-finiteness, no CW theory.

What is **not** available is the *excisive family itself*: an open `V ⊆ |Sk X (r+1)|` containing
`|Sk X r|` and an open `U` covering the open cells with `U ∪ V = univ` and with `V` deformation
retracting onto `|Sk X r|`.  That is a statement about the *topology*, not the underlying set,
of the realized pushout; see §14.

## 9. The component generator theorem

Three statements, all derived from the frozen `SpineTask14.relJ_generator` and never reproved
geometrically:

```lean
theorem SpineTask22.relJ_f_cellSimplex (σ : X.nonDegenerate r) :
    ((relJ X r).f r).hom (Submodule.Quotient.mk (Finsupp.single (cellSimplex σ) 1))
      = Submodule.Quotient.mk (Finsupp.single (charSimplexSk X r (cellSimplex σ)) 1)

theorem SpineTask22.relJ_topCls (σ : X.nonDegenerate r) :        -- e_σ ↦ γ_σ

theorem SpineTask22.relJ_generator_component (σ : X.nonDegenerate r) :
    (HomologicalComplex.homologyMap (relJ X r) r).hom
        ((srcDecomp X r r).hom (Finsupp.single σ (simpTopClass r)))
      = (tgtDecomp X r r).hom (Finsupp.single σ (stdCellGenerator r))
```

The last one is exactly the required form "under the finite-family decompositions,
`e_σ ↦ the σ-summand of stdCellGenerator r`"; its proof is the comparison square of §10
evaluated on `Finsupp.single σ (simpTopClass r)`, plus Task 20/21's
`homologyMap_cellRelJ_simpTopClass`.

Also recorded on the source side:
`SpineTask22.homologyMap_cellPairMap_simpTopClass` — the `σ`-component carries `e_r` to the
relative class of `σ`.

## 10. The full commutative decomposition square for `relJ`

```lean
theorem SpineTask22.relJ_decomposition_square (X : SSet.{u}) (r q : ℕ) :
    srcDecomp X r q ≫ HomologicalComplex.homologyMap (relJ X r) q
      = sumCellRelJ X r q ≫ tgtDecomp X r q
```

with

* `sumCellRelJ X r q = ⊕_σ HomologicalComplex.homologyMap (SpineTask20.cellRelJ r) q` —
  the bottom morphism is the **existing Task-21 `cellRelJ r` on every component**, and nothing
  else;
* the left vertical is the isomorphism of §6;
* the right vertical is the (not yet invertible) `tgtDecomp`.

The chain-level heart is

```lean
theorem SpineTask22.cellPairMap_relJ (σ : X.nonDegenerate r) :
    cellPairMap X r σ ≫ relJ X r = cellRelJ r ≫ topCellPairMap X r σ
```

both sides being the relative comparison attached to the *unit naturality square* of the
characteristic map `SpineTask15.cellChar X r σ` (`relChainCxMap_comp` plus
`relChainCxMap_eq_of_v` plus `sSetTopAdj.unit.naturality`).

A rearranged form is recorded as

```lean
theorem SpineTask22.homologyMap_relJ_eq :
    HomologicalComplex.homologyMap (relJ X r) q
      = (srcDecompIso X r q).inv ≫ sumCellRelJ X r q ≫ tgtDecomp X r q
```

so the frozen comparison is *determined* by the Task-21 single-cell comparison together with
`tgtDecomp`.  Also, `SpineTask22.isIso_sumCellRelJ`: `sumCellRelJ` is an isomorphism, directly
from Task 21's `isIso_homologyMap_cellRelJ`.

## 11. Was a finite-family `RelJIsIso` corollary obtained?

Only a **conditional** one, and it is marked as such:

```lean
/-- finite-cell-family only, and conditional on the still open singular decomposition -/
theorem SpineTask22.relJIsIso_of_singularCellFamilyAdditivity (X : SSet.{u}) (r : ℕ)
    (h : SingularCellFamilyAdditivity X r) : SpineTask14.RelJIsIso X r
```

Its hypothesis is not proved anywhere, so no unconditional `RelJIsIso` was produced, for any
`X`, finite or not.  It is included only to make visible that the *sole* remaining input to
blocker B3 for one skeletal step is the singular cell-family decomposition.

## 12. Arbitrary-family B3

**Still open.**  `SpineTask14.RelJIsIso` is untouched and is still an unproved
`Prop`-valued definition; `SpineTask16.skeletalInduction` and
`SpineTask16.finiteDimensional_homologyIso` remain conditional on it exactly as before.
Nothing in Task 22 assumes `RelJIsIso`, cellular homology, relative homology of a cell family,
additivity of singular homology over arbitrary coproducts, a wedge axiom, or local finiteness
of realizations.

## 13. Skeletal induction

**Untouched.**  No induction over `r` occurs anywhere in Task 22; every theorem is stated for a
fixed `r`.  `geometricHmap`, `finiteDimensional_homologyIso` and the nerve theorem were not
touched.

## 14. The first exact missing theorem

Full finite-family additivity was **not** reached.  The first missing statement, in the exact
shape the Task-18 excision engine would consume, is:

> **Missing (excisive neighbourhood of the old skeleton).**  For a simplicial set `X` and
> `r : ℕ` there exist open subsets `U V ⊆ |Sk X (r+1)|` with
>
> * `U ∪ V = Set.univ`,
> * `|Sk X r| ⊆ V`, and the inclusion `|Sk X r| ↪ V` a deformation retract,
> * `U` the image of the open cells together with a homeomorphism
>   `U ≅ ∐_{σ ∈ X.nonDegenerate r} (|Δ[r]| \ |∂Δ[r]|)`, and
>   `U ∩ V` corresponding to `∐_σ (|Δ[r]| \ (|∂Δ[r]| ∪ {barycenter}))`.

Everything *set-theoretic* in this statement is now available (§8, `compl_range_skInc`,
`real_cellMap_injOn_compl_bdry`).  What is missing is purely topological, and splits into three
independent sub-inputs, none of which exists in the pin or in the project:

1. **Openness in the realized pushout.**  A characterisation of the open subsets of
   `|Sk X (r+1)|` as those whose preimages in `|Sk X r|` and in `∐_σ |Δ[r]|` are open, i.e. that
   `SSet.toTop` applied to the Task-15 square gives the *quotient* topology.  (The square is a
   pushout in `TopCat`, `SpineTask15.skeletalIsPushout_toTop_coprod`; the missing step is the
   concrete point-set consequence.)
2. **The radial deformation retraction.**  A homotopy on `∐_σ (|Δ[r]| \ {b_σ})` onto
   `∐_σ |∂Δ[r]|` compatible with the attaching maps, hence descending through the pushout to a
   deformation retraction of `V` onto `|Sk X r|`.  The barycentric coordinates needed for this
   are available (`SpineTask16` `coord`, `SpineTask20Coords`), the descent is available from the
   pushout universal property, but the homotopy itself is not built.
3. **Homotopy invariance of *relative* singular homology**, to convert the deformation
   retraction of (2) into `H_q(|Sk X (r+1)|, V) ≅ H_q(|Sk X (r+1)|, |Sk X r|)`, together with
   **finite additivity of relative singular homology over a topological coproduct** to identify
   `H_q(U, U ∩ V)` with `⊕_σ H_q^{sing}(|Δ[r]|, |∂Δ[r]|)`.  The project has the chain prism
   `SpineTask18ChainPrism`, but no packaged relative homotopy-invariance theorem, and no finite
   coproduct additivity for singular chains.

Only after (1)–(3) does `SpineTask18.isIso_homologyMap_excisionMap` apply and give
`SingularCellFamilyAdditivity`, and then — by the *already proved*
`relJIsIso_of_singularCellFamilyAdditivity` — the finite-cell-family form of B3.

---

## Verification

* `lake build RequestProject` → **Build completed successfully (8258 jobs)**, including the
  pre-existing spine firewall audit (`SPINE FIREWALL AUDIT: all checks passed`).
* `RequestProject/Spine/Nerve/Task22AxiomAudit.lean` runs `#print axioms` on every principal
  Task-22 declaration (WP1 direct sum, the general relative-chain lemmas, the whole source
  decomposition, the realized cell family, the comparison square, the generator statements, the
  §7 separation theorems, and the conditional corollary).  Each reports exactly
  `[propext, Classical.choice, Quot.sound]`; in particular **no `sorryAx`**.
* No `sorry`, `admit`, new `axiom`, `@[implemented_by]` or `native_decide` occurs in the new
  modules.
* No existing module, the toolchain, `lakefile.toml` or `lake-manifest.json` was modified.
