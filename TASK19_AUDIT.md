# TASK19_AUDIT.md — Sphere homology, blocker B1, and the canonical relative generator

## 1. Exact production pin

Unchanged, and verified against the files in the repository:

* Lean toolchain: `leanprover/lean4:v4.28.0` (`lean-toolchain`, untouched).
* Mathlib revision: `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (`lake-manifest.json`, untouched).
* `lakefile.toml` untouched.  Default target `RequestProject`, glob `RequestProject.Spine.+`, so
  every new module below is part of the default build.

No result of current upstream Mathlib is imported; no `axiom`, `sorry`, `admit` or
`native_decide` occurs anywhere in Task-19 code.

## 2. New modules

All under `RequestProject/Spine/Nerve/`, all in namespace `SpineTask19`.

| Module | Content |
|--------|---------|
| `Task19Homology.lean` | Element-level dictionary for `ChainComplex (ModuleCat (ZMod 2)) ℕ`: cycles `Zc`, the `Z/B` model `hIso`, the class map `hcls` with surjectivity, vanishing criterion and naturality (`homologyMap_hcls`). |
| `Task19HZero.lean` | Degree-zero singular homology: the point class `ptCls`, the augmentation `augH`, path-invariance of `ptCls`, `h0Equiv`, `ptCls_ne_zero`. |
| `Task19Transport.lean` | Homotopy invariance packaged for transport: `homologyMap_eq_of_homotopic`, `singHomologyIsoOfHomotopyEquiv`, `singHomologyIsoOfHomeo`. |
| `Task19Discrete.lean` | Totally disconnected spaces: `isZero_homology_td`, and for a two-point space `h0_two_spanning`, `h0_two_indep`, `h0TwoEquiv`. |
| `Task19Reduced.lean` | The augmentation kernel `Hred0`, its naturality, homotopy invariance (`hred0Equiv`) and the two-point computation `hred0TwoEquiv`. |
| `Task19PairLES.lean` | Usable consequences of the Task-14 pair sequence: `isIso_pProj`, `isIso_pProj_one`, `isIso_pairDelta`, `mono_pairDelta`, `range_pairDelta`. |
| `Task19MayerVietoris.lean` | Binary Mayer–Vietoris for a cover by two contractible open sets: `mvIsoSucc`, `mvIsoOne`, `mv_mono_delta_one`, `mv_range_delta_one`. |
| `Task19SphereGeometry.lean` | The explicit two-set cover of a sphere and the equatorial deformation retraction. |
| `Task19BoundaryCover.lean` | Transport of that cover to `Bd r = |∂Δ[r]|` along Task 17's homeomorphism; `bdInterHomotopyEquiv`. |
| `Task19BoundaryHomology.lean` | `IsLine`; `H_*(∅)=0`; `mvOneEquiv`; the sphere induction `sphere_homology`; the `|∂Δ[r]|` statements `bd_isZero`, `bd_isLine_top`, `bd_isLine_zero`. |
| `Task19StandardCellHomology.lean` | The pair `(|Δ[r]|,|∂Δ[r]|)`: `relIsoBd`, `relEquivOneBd`, `isZero_rel_zero`, and **B1** (`standardCellPairAcyclic`, `standardCellPairTop`). |
| `Task19FundamentalClass.lean` | `lineGen` and uniqueness of the nonzero element of a line; `bdFundClass` (`β_r`); `stdCellTopClass`, `stdCellTopEquiv`; the connecting relations. |
| `Task19StandardCellGenerator.lean` | The characteristic simplex `charSimp`, `charChain_boundary`, `relCharChain_mem_Zc`, `stdCellGenerator` (`γ_r`), and the `r = 0` identification. |
| `Task19AxiomAudit.lean` | `#print axioms` on every principal Task-19 declaration. |

## 3. Modified old modules

**None.**  No Task-14 … Task-18 source file was edited.

## 4. Exact reused Task-14 … Task-18 declarations

Task 14: `sSetChainComplexFunctor` (+ `_X`, `_d`, `_map_f`), `RelChainMod`, `relBoundary`,
`relBoundary_mk`, `relChainCx`, `relChainCx_X`, `relChainCx_d`, `relProj`, `relProj_f_apply`,
`relSC`, `relSC_shortExact`, `relSingChainCx`, `toSSet_map_injective`, `sSetHomology`,
`relHomology`, `pairDelta`, `pair_exact₁`, `pair_exact₂`, `pair_exact₃`, `stdCellPair`,
`StandardCellPairAcyclic`, `StandardCellPairTop`.

Task 16: `Rz`, `coord` (through Task 17), `boundaryZero_realization_isEmpty` (through Task 17).

Task 17: `simplexHomeo`, `contractibleSpace_realized_simplex`,
`isClosedEmbedding_realization_boundary`, `boundaryRealizationSphereHomeo`, `boundaryOneHomeo`,
`boundaryZero_isEmpty`.

Task 18: `Δs`, `Sing`, `sMap`, `sOf`, `pre`, `stdC`, `singBd`, `singBd_single`,
`singBd_constSimp`, `singMap`, `singMap_single`, `singCx`, `singCxMap`, `constSimp`, `augS`,
`augS_single`, `lchain_induction`, `mod2_add_self`, `ofHomotopy`, `homologyMap_eq_of_prism`,
`isZero_homology_of_contractible`, `subTop`, `subInc`, `subInc_injective`, `incInterU`,
`incInterU_injective`, `excisionIso`.

Mathlib (pinned): `sSetTopAdj`, `SSet.boundary`, `stdSimplex.asOrderHom`,
`ShortComplex.moduleCatHomologyIso`, `HomologicalComplex.homologyIsoSc'`,
`isPathConnected_sphere`, `stereographic` (via Task-19 sphere geometry),
`OrthonormalBasis.fromOrthogonalSpanSingleton`.

## 5. Chosen sphere-homology proof route (WP1)

Two deliberate simplifications, both documented before implementation:

1. **No new Mayer–Vietoris short exact sequence.**  Building
   `0 → C_*(U∩V) → C_*(U) ⊕ C_*(V) → C^{small}_*(X) → 0` would require biproducts of chain
   complexes in `ChainComplex (ModuleCat (ZMod 2)) ℕ` and a second snake lemma.  Instead the
   *conclusion* of Mayer–Vietoris is obtained, for the covers actually used (both pieces
   contractible), from the **already proved** Task-14 pair sequences of `(X,V)` and `(U,U∩V)`
   glued by the **already proved** Task-18 `excisionIso`.  This is the classical proof of
   Mayer–Vietoris and uses exactly the chain-level Task-18 material, as required.
2. **No reduced chain complex.**  Instead an augmentation `augH : H₀(X) → ℤ₂` is defined at
   the level of `H₀` and `Hred0 X := ker (augH X)`.  All low-degree statements
   (`H₀(pt)`, `H₀(Fin 2)`, the collapse kernel, the `S⁰ ⇝ S¹` transition) are then ordinary
   homology statements, and degree `0` and degree `1` are handled explicitly and separately.

Universes: the sphere geometry lives in `Type 0`, the realized boundary `Bd r` in `TopCat.{u}`;
homology transport is only ever applied between two `TopCat.{u}` objects, so the whole
development remains universe-polymorphic.

## 6. H₀ theorem for a point / for a nonempty contractible space

`SpineTask19.h0Equiv [PathConnectedSpace ↥X] (x₀ : X) : (singCx X).homology 0 ≃ₗ[ZMod 2] ZMod 2`
(`Task19HZero.lean`), together with `SpineTask19.ptCls_ne_zero`.  A point and any nonempty
contractible space are path connected, so both cases are instances of this theorem.

## 7. H₀ theorem for `Fin 2`

`SpineTask19.h0TwoEquiv (hne : p₀ ≠ p₁) (hall : ∀ x, x = p₀ ∨ x = p₁) :
(ZMod 2 × ZMod 2) ≃ₗ[ZMod 2] (singCx X).homology 0` (`Task19Discrete.lean`), with the two
point classes as a basis: `h0_two_spanning` and `h0_two_indep`.  Nothing is assumed: for a
totally disconnected space every singular simplex is constant (`sing_eq_constSimp`), which is
what makes the chain complex computable (`chain_zero_eq_two`, `isZero_homology_td`).

## 8. Explicit collapse-map / kernel theorem

* `SpineTask19.augH_natural (g : X ⟶ Y) (t) : augH Y (H₀(g) t) = augH X t` — the collapse map
  to a point is the augmentation.
* `SpineTask19.ker_homologyMap_zero_eq_Hred0 (g : X ⟶ Y) [PathConnectedSpace ↥Y] (y₀) :
  ker (H₀(g)) = Hred0 X` — the kernel of the collapse map is exactly the augmentation kernel.
* `SpineTask19.hred0TwoEquiv : Hred0 X ≃ₗ[ZMod 2] ZMod 2` for a two-point space, with generator
  `ptCls p₀ + ptCls p₁` (`twoRedMap`, `twoRedMap_bijective`).  Over `ZMod 2` this is exactly
  `ker((a,b) ↦ a + b) = ⟨(1,1)⟩`.

## 9. Mayer–Vietoris theorem

* `SpineTask19.mvIsoSucc (m) : H_{m+2}(X) ≅ H_{m+1}(U ∩ V)`;
* `SpineTask19.mvIsoOne (hm : Mono (H₀(V) → H₀(X))) : H₁(X) ≅ H₁(U, U∩V)`;
* `SpineTask19.mv_mono_delta_one`, `SpineTask19.mv_range_delta_one` — the connecting map
  `H₁(U,U∩V) → H₀(U∩V)` is injective with image `ker (H₀(U∩V) → H₀(U))`;
* `SpineTask19.mvOneEquiv : H₁(X) ≃ₗ[ZMod 2] Hred0 (U ∩ V)` — the degree-one conclusion in
  final form.

All for a binary **open** cover `U ∪ V = X` with `U`, `V` contractible.  No Čech machinery.

## 10. Sphere-cover geometry (WP4)

In `Task19SphereGeometry.lean`, for a unit vector `v` of a real inner-product space:

* `Uset hv = {x ∈ sphere 0 1 | x ≠ v}`, `Vset hv = {x ∈ sphere 0 1 | x ≠ -v}`;
* `isOpen_Uset`, `isOpen_Vset`, `Uset_union_Vset : Uset ∪ Vset = univ`;
* `contractibleSpace_Uset`, `contractibleSpace_Vset` — via the stereographic charts
  (`UsetHomeo`, `VsetHomeo`) onto the tangent hyperplane, which is contractible;
* `interSphereHomotopyEquiv` — an explicit **homotopy equivalence**
  `Uset ∩ Vset ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin n)) 1`, built from the explicit
  deformation `interHomotopy` normalising the orthogonal component
  `ocomp v x = x - ⟪v,x⟫ • v`, followed by the orthonormal-basis identification of `(ℝ ∙ v)ᗮ`
  with `EuclideanSpace ℝ (Fin n)`.  Nothing is read off a picture.

Transported to the realized boundary in `Task19BoundaryCover.lean`: `bdU`, `bdV`,
`isOpen_bdU`, `isOpen_bdV`, `bdU_union_bdV`, the contractibility instances, and
`bdInterHomotopyEquiv : ↥(bdU n ∩ bdV n) ≃ₕ ↥(Bd (n+1))`.

`S⁰` is handled separately (`Bd 1` is a two-point space); the general construction is only ever
applied to `Bd (n+2)`.

## 11. Sphere-homology theorem in every degree (WP5)

`SpineTask19.sphere_homology (n : ℕ)` in `Task19BoundaryHomology.lean`:

```
(∀ q, q ≠ 0 → q ≠ n → IsZero ((singCx (Bd (n+1))).homology q)) ∧
  (n ≠ 0 → IsLine ((singCx (Bd (n+1))).homology n))
```

with `Bd (n+1) ≅ Sⁿ` (Task 17), plus

* degree `0` for `n ≥ 1`: `bd_isLine_zero` (`Bd (n+2)` is path connected);
* `S⁰ = Bd 1`: `H_q = 0` for `q > 0` (`isZero_homology_td`) and `H₀ ≅ ℤ₂ ⊕ ℤ₂`
  (`h0TwoEquiv` applied to `bdOnePt 0`, `bdOnePt 1`);
* the low-degree transition `S⁰ ⇝ S¹` is the explicit step `bdEquivOne 0 : H₁(Bd 2) ≃ Hred0 (Bd 1)`
  in the induction, not a reduced-homology convention.

## 12. Definition of the mod-2 sphere fundamental class (WP6)

`SpineTask19.lineGen (h : IsLine M) : M` is the unique nonzero element of a one-dimensional
`ℤ₂`-vector space (`lineGen_ne_zero`, `eq_lineGen_of_ne_zero`, `eq_zero_or_eq_lineGen`).  Over
`ℤ₂` this makes the top class canonical without any orientation choice, while still being a
specified construction.

`SpineTask19.bdFundClass r : (singCx (Bd r)).homology (r-1)`:

* `r = 0`: `0` (the group is zero);
* `r = 1`: `ptCls (bdOnePt 0) + ptCls (bdOnePt 1)` — the reduced class `[p₊] + [p₋]` of `S⁰`;
* `r ≥ 2`: `lineGen (bd_isLine_top r _)`.

Proved: `bdFundClass_ne_zero` (nonzero for `r ≥ 1`), `bdFundClass_eq_lineGen` (it generates the
one-dimensional top homology for `r ≥ 2`, by `eq_zero_or_eq_lineGen`), and the exact recursive
Mayer–Vietoris relations `bdIsoSucc_bdFundClass` and `bdEquivOne_bdFundClass`.

## 13. Boundary-homology transfer theorem (WP7)

`SpineTask19.bd_isZero`, `SpineTask19.bd_isLine_top`, `SpineTask19.bd_isLine_zero`, all stated
for `Bd r = |∂Δ[r]|` and obtained through Task 17's own homeomorphism
`SpineTask17.boundaryRealizationSphereHomeo` (used to pull back the cover, so the transport is
along the actual Task-17 model).  `r = 1` uses `SpineTask17.boundaryOneHomeo`, `r = 0` uses
`SpineTask17.boundaryZero_isEmpty` together with `isZero_homology_of_isEmpty`.  The
distinguished boundary class is `bdFundClass r` (§12).

## 14. Relative standard-cell homology theorem (WP8)

In `Task19StandardCellHomology.lean`:

* `relIsoBd r q : H_{q+2}(|Δ[r]|,|∂Δ[r]|) ≅ H_{q+1}(|∂Δ[r]|)`;
* `relEquivOneBd r : H₁(|Δ[r]|,|∂Δ[r]|) ≃ₗ Hred0 (|∂Δ[r]|)` — this is the exact sequence
  `H₁(rel) → H₀(∂) → H₀(Δ)` with the explicitly identified kernel of WP2, and it is what settles
  `r = 1`;
* `isZero_rel_zero r s₀ : H₀(rel) = 0` whenever `|∂Δ[r]|` is nonempty (`r ≥ 1`), proved from
  `epi_pProj_zero` and surjectivity of `H₀(∂Δ) → H₀(Δ)`;
* `r = 0`: `|∂Δ[0]| = ∅`, and `pProj` in degree `0` is mono (empty source) and epi
  (`epi_pProj_zero`), hence `H₀(|Δ[0]|,∅) ≅ H₀(|Δ[0]|) ≅ ℤ₂`.

Nothing is derived from a positive-degree vanishing theorem that does not cover `H₀`.

## 15. Status of `StandardCellPairAcyclic`

**Closed.**  `SpineTask19.standardCellPairAcyclic (r : ℕ) : SpineTask14.StandardCellPairAcyclic r`,
proved for the *existing* Task-14 definition, unconditionally, for every `r`.
Axioms: `[propext, Classical.choice, Quot.sound]`.

## 16. Status of `StandardCellPairTop`

**Closed.**  `SpineTask19.standardCellPairTop (r : ℕ) : SpineTask14.StandardCellPairTop r`,
proved for the *existing* Task-14 definition, unconditionally, for every `r`.
Axioms: `[propext, Classical.choice, Quot.sound]`.

Blocker **B1 is therefore formally closed.**

## 17. Exact definition of the canonical relative generator

Two objects are supplied, and they must be distinguished.

**(a) The canonical top generator** (`Task19FundamentalClass.lean`):

```lean
def stdCellTopClass (r : ℕ) : relHomology (stdCellPair r) r := lineGen (isLine_relHomology_top r)
```

the unique nonzero element of the one-dimensional `H_r(|Δ[r]|,|∂Δ[r]|;ℤ₂)`.

**(b) The class of the identity `r`-simplex** (`Task19StandardCellGenerator.lean`):

```lean
def topSimp (r : ℕ) : (Δ[r]).obj (op ⦋r⦌) := ULift.up (𝟙 _)
def charSimp (r : ℕ) : Sing (Cell r) r :=
  (sSetTopAdj.unit.app (Δ[r])).app (op ⦋r⦌) (topSimp r)
def charChain (r : ℕ) : SSetChain (TopCat.toSSet.obj (Cell r)) r := Finsupp.single (charSimp r) 1
def relCharChain (r : ℕ) : (relChainCx (stdCellPair r)).X r := Submodule.Quotient.mk (charChain r)
def stdCellGenerator (r : ℕ) : relHomology (stdCellPair r) r :=
  hcls (relCharChain r) (relCharChain_mem_Zc r)
```

WP10.1 and WP10.2 are theorem-level:

* `charChain_boundary (m) :
   sSetBoundary _ m (charChain (m+1)) = sSetChainMap (stdCellPair (m+1)) m (bdFaceChain m)`
  — the singular boundary of the characteristic top simplex is carried by the realized
  boundary, and is exactly the sum of the characteristic simplices of its codimension-one
  faces (`bdFaceChain m = ∑ i, single (bdFaceSimp m i) 1`).  Proved from naturality of the
  adjunction unit at `∂Δ[r].ι` and at `(δ i).op`.
* `relCharChain_mem_Zc (r) : relCharChain r ∈ Zc (relChainCx (stdCellPair r)) r` — the quotient
  class is a relative cycle.

## 18. Proof that it is nonzero

* For **(a)**: `stdCellTopClass_ne_zero (r) : stdCellTopClass r ≠ 0`, for every `r`.
* For **(b)**: `stdCellGenerator_zero_ne_zero : stdCellGenerator 0 ≠ 0`, i.e. the `r = 0` case
  required by WP10, proved directly (`H₀(|Δ[0]|,∅) ≅ H₀(|Δ[0]|)` and the characteristic
  `0`-simplex is a point class).  **For `r ≥ 1` this is not proved** — see §24.

## 19. Proof that it generates

* `eq_zero_or_eq_stdCellTopClass (r) (x) : x = 0 ∨ x = stdCellTopClass r`;
* `exists_smul_stdCellTopClass (r) (x) : ∃ a : ZMod 2, x = a • stdCellTopClass r`;
* `stdCellTopEquiv (r) : relHomology (stdCellPair r) r ≃ₗ[ZMod 2] ZMod 2` with
  `stdCellTopEquiv_stdCellTopClass : stdCellTopEquiv r (stdCellTopClass r) = 1`.

This is the reusable interface asked for in §14 of the task; it is usable without re-opening
the internal sphere proof.  `stdCellGenerator_zero_eq : stdCellGenerator 0 = stdCellTopClass 0`
identifies the two objects in degree `0`.

## 20. Exact theorem relating the connecting image to the boundary generator

* `pairDelta_stdCellTopClass_succ (k) :
   pairDelta (stdCellPair (k+2)) _ (k+1) (stdCellTopClass (k+2)) = bdFundClass (k+2)`;
* `pairDelta_stdCellTopClass_one :
   pairDelta (stdCellPair 1) _ 0 (stdCellTopClass 1) = bdFundClass 1`.

So the canonical top relative generator does have connecting image exactly `β_r`.  What is
**not** proved is the corresponding statement with `stdCellGenerator r` in place of
`stdCellTopClass r` for `r ≥ 1`; see §24.

## 21. Status of the optional single-cell `J`

**Not pursued.**  The optional §16 record (`relJ_generator` transporting the simplicial
relative generator to `γ_r`) was not free: it needs the identification of `stdCellGenerator r`
with `stdCellTopClass r`, which is exactly the open point of §24.  Left for Task 20 as
permitted.

## 22. Confirmation that B3 remains open

`SpineTask14.RelJIsIso` is untouched.  No Task-19 declaration proves, assumes, or uses it, and
`Task14Comparison.oneSkeletonStep` still takes it as a hypothesis.  B3 remains open.

## 23. Confirmation that `geometricHmap` remains open

`NerveGeom.geometricHmap` and its bijectivity are untouched by Task 19; nothing in the Task-19
modules refers to them.  The global simplicial–singular comparison remains open.

## 24. First exact missing theorem

The full target of §13/§14 of the task was reached for the *canonical* generator but **not**
for the identity-simplex generator in positive degree.  The first exact missing theorem is:

```lean
theorem stdCellGenerator_ne_zero (r : ℕ) : SpineTask19.stdCellGenerator r ≠ 0
```

for `r ≥ 1` — equivalently (since the connecting map is injective in the relevant degree, by
`mono_pairDelta`, and by §20), the missing compatibility theorem is

```lean
theorem hcls_bdFaceChain_eq_bdFundClass (m : ℕ) :
    hcls (K := singCx (Bd (m+1))) (bdFaceChain m) _ = bdFundClass (m + 1)
```

i.e. *the sum of the codimension-one faces of the identity simplex represents the distinguished
mod-2 fundamental class of `|∂Δ[m+1]|`*.  For `m = 0` this needs only that the two vertices of
`|∂Δ[1]|` are distinct; for `m ≥ 1` the classical proof requires excision for the **non-open**
horn pair `(∂Δ[r], Λ^r_0)`, i.e. an open thickening of the horn together with a deformation
retraction onto it.  That infrastructure does not exist in the project and was judged outside
the scope of Task 19.

## Outcome

**Outcome B — B1 closed, canonical generator open.**

* All sphere homology required by the task is proved (§11), including the `S⁰` and `S⁰ ⇝ S¹`
  cases, from the Task-18 excision theorem via a binary Mayer–Vietoris engine (§9).
* Both existing Task-14 B1 propositions are proved unconditionally (§15, §16); blocker B1 is
  formally closed.
* The canonical mod-2 fundamental classes exist, are nonzero, generate, and satisfy the exact
  recursive and connecting relations (§12, §17a, §19, §20).
* The canonical relative class of the identity `r`-simplex is defined, is proved to be a
  relative cycle with boundary carried by the realized boundary, and is proved to be the
  generator for `r = 0`; the identification for `r ≥ 1` remains open, with the first exact
  missing theorem recorded in §24.

## Final verification

`lake build RequestProject` completes successfully; see the session log.  `#print axioms` on
every principal Task-19 declaration (module `Task19AxiomAudit.lean`) reports
`[propext, Classical.choice, Quot.sound]` and nothing else.  In particular **no `sorryAx`**.
