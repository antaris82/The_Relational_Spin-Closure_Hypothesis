# TASK 23 AUDIT — finite singular cell-family decomposition

**Principal outcome: C (partial).**  The excisive finite-cell geometry is closed — the
open/closed control in the realized pushout, the punctured-cell deformation retraction, its
descent through the pushout, the relative homotopy consequence, and the Task-18 excision step
are all *proved, sorry-free* — but the chain-level decomposition is **not** reached:
`IsIso (tgtDecomp X r q)` is **not** proved, and no finite-family `RelJIsIso` is obtained
unconditionally.  The exact missing theorems are §18.

Nothing anywhere in the project assumes the missing statements.

---

## 1. Production pin

* Lean `v4.28.0` (`lean-toolchain`, unchanged).
* Mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (`lake-manifest.json`, unchanged;
  `lakefile.toml` unchanged).
* No existing module was modified; no newer upstream result is imported.
* `relJ`, `cellRelJ`, `srcDecomp`, `tgtDecomp` are used exactly as they stand and are never
  replaced.

New modules (all in namespace `SpineTask23`):

| module | content |
| --- | --- |
| `RequestProject/Spine/Nerve/Task23PuncturedCell.lean` | WP2: radial deformation retraction of the punctured standard cell |
| `RequestProject/Spine/Nerve/Task23SkeletonTopology.lean` | WP1: open/closed control in the realized pushout |
| `RequestProject/Spine/Nerve/Task23PushoutRetraction.lean` | WP3: quotient presentation of `V`, descent of maps and homotopies, deformation retraction of `V` onto `A` |
| `RequestProject/Spine/Nerve/Task23RelativeHomotopy.lean` | WP4: `H_q^{sing}(V,A) = 0` |
| `RequestProject/Spine/Nerve/Task23Excision.lean` | WP5: `H_q(Y,A) ≅ H_q(Y,V)` and Task-18 excision at `(U,V)` |
| `RequestProject/Spine/Nerve/Task23StandardCellExcision.lean` | the single standard cell: `H_q(Δ°, Δ° \ b) ≅ H_q(Δ, ∂Δ)` |
| `RequestProject/Spine/Nerve/Task23FiniteTargetDecomp.lean` | WP7/WP8: the finite proposition, and the conditional `RelJIsIso` corollary |
| `RequestProject/Spine/Nerve/Task23AxiomAudit.lean` | `#print axioms` for every principal Task-23 declaration |

## 2. Exact Task-22 definitions reused

Reused verbatim, never replaced or redefined:

* `SpineTask22.tgtDecomp`, `SpineTask22.tgtSumMod`, `SpineTask22.topCellPairMap`;
* `SpineTask22.SingularCellFamilyAdditivity` (referenced only, in
  `SpineTask23.finiteSingularCellFamilyAdditivity_of_singularCellFamilyAdditivity`);
* `SpineTask22.relJIsIso_of_singularCellFamilyAdditivity` (used to derive the conditional
  `SpineTask23.relJIsIso_of_finite`);
* the Task-22 separation module is imported (`Task22CellSeparation`), and Task 23 re-derives the
  separation statements it needs directly in the *coproduct* form of the Task-15 square
  (`SpineTask23.topCellMap_eq_skInc_iff`, `preimage_topCellMap_range_skInc`), because
  `tgtDecomp` and Task-18 excision live on that side.

Also reused: `SpineTask15.skeletalIsPushout_toTop_coprod` (the realized pushout — never
reconstructed), `SpineTask15.realization_skInc_injective`, `SpineTask16.standardCellMono`,
`SpineTask17.simplexHomeo`, `SpineTask17.boundaryHomeo`, `SpineTask17.simplexGauge` and the
Task-17 gauge lemmas, `SpineTask17.isClosedEmbedding_realization_boundary`,
`SpineTask17.isOpen_compl_realized_boundary`, `SpineTask14.relChainCx`, `relChainCxMap`,
`relSC`, `relSC_shortExact`, `relSCMap`, `SpineTask18.subInc`, `incInterU`, `excisionMap`,
`excisionIso`, `SpineTask19.isIso_homologyMap_of_homotopyEquiv`.

## 3. `TopCat.isOpen_iff_of_isColimit` exists at the production pin

**Confirmed.**  `Mathlib/Topology/Category/TopCat/Limits/Basic.lean`, line 248:

```lean
lemma isOpen_iff_of_isColimit (X : Set c.pt) :
    IsOpen X ↔ ∀ (j : J), IsOpen (c.ι.app j ⁻¹' X)
```

together with `TopCat.coinduced_of_isColimit` (line 235).  The Task-22 audit statement that this
was missing is **incorrect** and is corrected here.  Task 23 uses it, and rebuilds no
final-topology theory.

## 4. `TopCat.isClosed_iff_of_isColimit` exists at the production pin

**Confirmed**, same file, line 255.  It is the engine of
`SpineTask23.isClosed_iff_of_isPushout` and `SpineTask23.isClosed_coprod_iff`.

## 5. The finiteness assumption used

`[Fintype (X.nonDegenerate r)]` appears in exactly one place: the principal (still open)
proposition `SpineTask23.FiniteSingularCellFamilyAdditivity` and its two corollaries in
`Task23FiniteTargetDecomp.lean`.

Every geometric theorem of Task 23 (WP1–WP5 and the single-cell statements) is proved for an
**arbitrary** cell family; the finiteness was genuinely not needed for them, and in particular
the barycentre set is closed for an arbitrary family (§7).  This is a strengthening of what was
requested for those steps, not a weakening: no theorem below is weaker than its finite form,
and the principal target retains the `Fintype` hypothesis exactly as required.

No local-finiteness theorem, no arbitrary-coproduct preservation, and no wedge axiom is used or
proved anywhere.

## 6. The old skeleton is closed

```lean
theorem SpineTask23.isClosed_range_skInc (X : SSet.{u}) (r : ℕ) :
    IsClosed (Set.range (SSet.toTop.map (skInc X r)))
```

Proof: `SpineTask23.isClosed_iff_of_isPushout` (from `TopCat.isClosed_iff_of_isColimit` applied
to the cocone of `SpineTask15.skeletalIsPushout_toTop_coprod`) reduces closedness of a subset of
`Y = |Sk X (r+1)|` to closedness of its two preimages.  The preimage in `|Sk X r|` is `univ`;
the preimage in `∐_σ |Δ[r]|` is `Set.range (topBdryMap X r)`
(`SpineTask23.preimage_topCellMap_range_skInc`, from the pushout description of the
identifications plus injectivity of `topBdryMap`), which is closed by
`SpineTask23.isClosed_range_sigmaMap` and Task 17's closed embedding
`isClosedEmbedding_realization_boundary`.

## 7. The barycentre set is closed

```lean
def SpineTask23.cellBary (r : ℕ) : ↥(SSet.toTop.obj (Δ[r] : SSet))      -- barycentre of the cell
def SpineTask23.baryPoint (X : SSet) (r : ℕ) (σ : X.nonDegenerate r)     -- its image in Y
def SpineTask23.barySet (X : SSet) (r : ℕ) : Set ↥(SSet.toTop.obj (Sk X (r+1)))
theorem SpineTask23.baryPoint_notMem_range_skInc … : baryPoint X r σ ∉ Set.range (skInc …)
theorem SpineTask23.isClosed_barySet (X : SSet) (r : ℕ) : IsClosed (barySet X r)
```

Proof: again by `isClosed_iff_of_isPushout`.  The preimage in `|Sk X r|` is empty (a barycentre
is not on the boundary of its cell, hence its cell point is not identified with any skeleton
point).  The preimage in `∐_σ |Δ[r]|` is `Set.range (cellBaryPt X r)`, whose preimage under each
coproduct leg is the single point `{cellBary r}`, closed because `|Δ[r]|` is Hausdorff
(Task 17).  **No finiteness of the family is used.**

## 8. Definition of `V`

```lean
def SpineTask23.puncturedNbhd (X : SSet) (r : ℕ) : Set ↥(SSet.toTop.obj (Sk X (r+1))) :=
  (barySet X r)ᶜ                                  -- V = Y \ B
def SpineTask23.openCells (X : SSet) (r : ℕ) : Set ↥(SSet.toTop.obj (Sk X (r+1))) :=
  (Set.range (SSet.toTop.map (skInc X r)))ᶜ       -- U = Y \ A
theorem SpineTask23.isOpen_puncturedNbhd … : IsOpen (puncturedNbhd X r)
theorem SpineTask23.isOpen_openCells … : IsOpen (openCells X r)
theorem SpineTask23.range_skInc_subset_puncturedNbhd … : range (skInc …) ⊆ puncturedNbhd X r
theorem SpineTask23.openCells_union_puncturedNbhd … : openCells X r ∪ puncturedNbhd X r = univ
```

## 9. The punctured-cell deformation retraction

In the Task-17 barycentric model `Σ_r = stdSimplex ℝ (Fin (r+1))`, with `bary r` and the
Task-17 gauge `simplexGauge`, for `x ≠ bary` and `t ∈ [0,1]`

```
H t x = bary + ((1-t) + t·gaugeAt r x)⁻¹ • (x - bary).
```

`SpineTask23.radialHomotopy`, `SpineTask23.radialRetract`, and their transports to the realized
cell along `SpineTask17.simplexHomeo` / `SpineTask17.boundaryHomeo`:

```lean
def SpineTask23.puncturedCell (r : ℕ) : Set ↥(SSet.toTop.obj (Δ[r] : SSet)) := {cellBary r}ᶜ
def SpineTask23.cellRetract (r : ℕ) : C(↥(puncturedCell r), ↥(SSet.toTop.obj (∂Δ[r] …)))
def SpineTask23.cellHomotopy (r : ℕ) : C(I × ↥(puncturedCell r), ↥(puncturedCell r))
theorem SpineTask23.cellHomotopy_zero … : cellHomotopy r (0, x) = x
theorem SpineTask23.cellHomotopy_one  … : ↑(cellHomotopy r (1, x)) = cellBdryIncl r (cellRetract r x)
theorem SpineTask23.cellRetract_bdryToPunctured … : cellRetract r (bdryToPunctured r b) = b
```

All continuity is proved (`continuous_radialFun_pair`), and the case `r = 0` needs no separate
treatment: `Σ_0` is a single point, which *is* the barycentre, so the punctured cell is empty
and every statement is vacuous there.

## 10. The boundary-fixing property

```lean
theorem SpineTask23.cellHomotopy_bdry (r : ℕ) (t : I) (b) :
    cellHomotopy r (t, bdryToPunctured r b) = bdryToPunctured r b
```

i.e. the homotopy fixes `|∂Δ[r]|` pointwise at every time (in the model:
`radialHomotopy_of_bdLocus`, because the gauge is `1` exactly on the boundary locus, so the
scaling factor is `1`).

## 11. Descent through the pushout

`Task23PushoutRetraction.lean`.  The total space and the quotient presentation

```lean
abbrev SpineTask23.Tot (X : SSet) (r : ℕ) :=
  ↥(SSet.toTop.obj (Sk X r)) ⊕ (Σ _ : X.nonDegenerate r, ↥(puncturedCell r))
def SpineTask23.totMap : Tot X r → ↥(puncturedNbhd X r)
theorem SpineTask23.isQuotientMap_totMap : Topology.IsQuotientMap (totMap X r)
```

`isQuotientMap_totMap` is proved from `isOpen_iff_of_isPushout` (hence from
`TopCat.isOpen_iff_of_isColimit`) together with openness of `V` in `Y` and of the punctured cell
in `|Δ[r]|`.  Maps and homotopies are then descended by

```lean
theorem SpineTask23.descend          (g : Tot X r → Z) (hg : Continuous g) (hwd : …) : ∃ f : C(↥V, Z), ∀ w, f (totMap X r w) = g w
theorem SpineTask23.descendHomotopy  (G : I × Tot X r → Z) (hG : Continuous G) (hwd : …) : ∃ F : C(I × ↥V, Z), ∀ t w, F (t, totMap X r w) = G (t, w)
```

the second using the pinned `Topology.IsQuotientMap.continuous_lift_prod_right` (the interval is
locally compact).  **Joint continuity of the descended homotopy is proved, not assumed**; no
informal pointwise gluing occurs.  Endpoint:

```lean
def     SpineTask23.skToV     : C(↥(SSet.toTop.obj (Sk X r)), ↥(puncturedNbhd X r))
def     SpineTask23.vRetract  : C(↥(puncturedNbhd X r), ↥(SSet.toTop.obj (Sk X r)))
def     SpineTask23.vHomotopy : C(I × ↥(puncturedNbhd X r), ↥(puncturedNbhd X r))
theorem SpineTask23.vRetract_skToV  (x) : vRetract X r (skToV X r x) = x
theorem SpineTask23.vHomotopy_zero  (v) : vHomotopy X r (0, v) = v
theorem SpineTask23.vHomotopy_one   (v) : vHomotopy X r (1, v) = skToV X r (vRetract X r v)
theorem SpineTask23.vHomotopy_fix (t x) : vHomotopy X r (t, skToV X r x) = skToV X r x
```

Well-definedness of the descended data uses the exact attaching maps
(`SpineTask23.exists_bdry_of_totMap_inl_inr`, `retrTot_wd`, `homTot_wd`) and the
boundary-fixing property of §10.

## 12. The relative homotopy consequence

```lean
def     SpineTask23.vHomotopyEquiv : ContinuousMap.HomotopyEquiv ↥|Sk X r| ↥V
theorem SpineTask23.isZero_relHomology_of_quasiIso {S T : SSet} (f : S ⟶ T)
    (hf : ∀ n, Function.Injective (f.app n))
    (hq : ∀ q, IsIso (HomologicalComplex.homologyMap (sSetChainComplexFunctor.map f) q)) (q : ℕ) :
    IsZero ((relChainCx f).homology q)
theorem SpineTask23.isZero_relHomology_skToV (X r q) :
    IsZero ((relChainCx (TopCat.toSSet.map (skToVMap X r))).homology q)
```

i.e. **`H_q^{sing}(V, A; ℤ₂) = 0` for every `q`**.  Inputs: the Task-18/Task-19 absolute
homotopy invariance (`SpineTask19.isIso_homologyMap_of_homotopyEquiv`), the Task-14 relative
short exact sequence, and the pinned `HomologicalComplex.HomologySequence.quasiIso_τ₃`.  No new
theory of relative homotopy equivalences was built.

## 13. The finite disjoint-union homology theorem

**Not obtained** — see §18(1).  Nothing in the project assumes it.

## 14. The excision theorem used

`SpineTask18.excisionIso` / `SpineTask18.isIso_homologyMap_excisionMap`, applied twice, with all
hypotheses discharged by Task-23 theorems:

```lean
def SpineTask23.excisionIsoCells (X r q) :          -- U = Y \ A, V = Y \ B
    (relSingChainCx (SpineTask18.incInterU (openCells X r) (puncturedNbhd X r))).homology q
      ≅ (relSingChainCx (SpineTask18.subInc (puncturedNbhd X r))).homology q
def SpineTask23.stdExcisionIso (r q) :              -- Δ° = |Δ[r]| \ |∂Δ[r]|, |Δ[r]| \ {b_r}
    (relSingChainCx (SpineTask18.incInterU (openStdCell r) (puncturedCell r))).homology q
      ≅ (relSingChainCx (SpineTask18.subInc (puncturedCell r))).homology q
```

together with the two comparisons of pairs

```lean
theorem SpineTask23.isIso_homologyMap_pairAV  (X r q) :  -- H_q(Y,A) ≅ H_q(Y,V)
theorem SpineTask23.isIso_homologyMap_stdPair (r q)   :  -- H_q(Δ,∂Δ) ≅ H_q(Δ, Δ \ {b_r})
```

and the resulting composites

```lean
def SpineTask23.cellPairIso (X r q) :
    H_q^{sing}(U, U ∩ V) ≅ H_q^{sing}(|Sk X (r+1)|, |Sk X r|)
def SpineTask23.stdCellIso (r q) :
    H_q^{sing}(Δ°, Δ° \ {b_r}) ≅ H_q^{sing}(|Δ[r]|, |∂Δ[r]|)
```

Both comparisons of pairs are instances of the general lemma
`SpineTask23.isIso_homologyMap_relChainCxMap` (a map of pairs whose two absolute comparisons are
quasi-isomorphisms induces an isomorphism on relative homology).

## 15. The theorem proving `IsIso (tgtDecomp X r q)`

**None.**  Not reached; see §18.

## 16. The finite-family `RelJIsIso` corollary

Only conditional, and marked as such:

```lean
def     SpineTask23.FiniteSingularCellFamilyAdditivity (X : SSet) (r : ℕ)
          [Fintype (X.nonDegenerate r)] : Prop := ∀ q, IsIso (tgtDecomp X r q)
theorem SpineTask23.relJIsIso_of_finite (X : SSet) (r : ℕ) [Fintype (X.nonDegenerate r)]
          (h : FiniteSingularCellFamilyAdditivity X r) : SpineTask14.RelJIsIso X r
```

Its hypothesis is proved nowhere.  This also records the **Task-22 documentation/type
mismatch** requested in the task statement: `SpineTask22.SingularCellFamilyAdditivity` carries
no finiteness hypothesis although the intended downstream theorem is finite-family only; the
frozen Task-22 definition is left untouched, and the correctly named finite proposition is added
alongside it (`SpineTask23.finiteSingularCellFamilyAdditivity_of_singularCellFamilyAdditivity`
records that the finite one is implied by the Task-22 one, so nothing was smuggled in).

## 17. Arbitrary-family B3

**Still open**, and untouched.  `SpineTask14.RelJIsIso` remains an unproved `Prop`-valued
definition; `SpineTask16.skeletalInduction` and `SpineTask16.finiteDimensional_homologyIso`
remain conditional on it exactly as before.  No skeletal induction, no filtered-colimit
compatibility, no finite-subcomplex factorization, no wedge axiom, no local finiteness, no
cellular-homology theorem, no `geometricHmap`, no nerve theorem, no `w₂(TM)` occurs in Task 23.

## 18. The first exact missing theorems

Task 23 reduced the principal target to exactly two statements, in this order.

> **Missing (1) — the coproduct pair and its finite additivity.**  For a *finite* family
> `X.nonDegenerate r`, a homeomorphism of pairs
>
> ```
> (U, U ∩ V)  ≅  (∐_σ Δ°_σ , ∐_σ (Δ°_σ \ {b_σ}))
> ```
>
> where `U = |Sk X (r+1)| \ |Sk X r|`, `V = |Sk X (r+1)| \ B`, `Δ°_σ = |Δ[r]| \ |∂Δ[r]|` — the
> underlying bijection is Task-22's `compl_range_skInc` together with
> `SpineTask23.preimage_topCellMap_range_skInc`, and the topological statement is available from
> `SpineTask23.isOpen_iff_of_isPushout`; and then the finite disjoint-union theorem
>
> ```
> H_q^{sing}(∐_σ U_σ, ∐_σ W_σ; ℤ₂) ≅ ⊕_σ H_q^{sing}(U_σ, W_σ; ℤ₂).
> ```
>
> The intended proof is the connectedness route: the geometric standard simplex `Δ^q` is convex,
> hence preconnected, so a singular simplex into a topological coproduct has image inside a
> single component; this splits the singular chain modules as `Finsupp` direct sums, compatibly
> with the boundary and with the relative quotient.  *None of this is formalized yet*, and no
> arbitrary-coproduct preservation is needed for it.

> **Missing (2) — agreement with `tgtDecomp`.**  That the composite isomorphism
>
> ```
> ⊕_σ H_q^{sing}(|Δ[r]|,|∂Δ[r]|)
>   ≅ ⊕_σ H_q^{sing}(Δ°_σ, Δ°_σ \ {b_σ})       (stdCellIso, componentwise)
>   ≅ H_q^{sing}(U, U ∩ V)                      (Missing (1))
>   ≅ H_q^{sing}(|Sk X (r+1)|, |Sk X r|)        (cellPairIso)
> ```
>
> **is** the existing `SpineTask22.tgtDecomp X r q`, i.e. that its `σ`-component is the map
> induced by the realized characteristic map `|cellChar X r σ|`.  All the maps involved are
> induced by maps of pairs, so the statement is a chain-level commuting-diagram identity; it is
> not formalized.

Only after (1) and (2) does `SpineTask23.FiniteSingularCellFamilyAdditivity` follow, and then —
by the already proved `SpineTask23.relJIsIso_of_finite` (i.e. Task 22's decomposition square) —
the finite-cell-family form of B3.

---

## Verification

* `lake build RequestProject` → **Build completed successfully (8266 jobs)**, including the
  pre-existing spine firewall audit (`SPINE FIREWALL AUDIT: all checks passed`).
* `RequestProject/Spine/Nerve/Task23AxiomAudit.lean` runs `#print axioms` on every principal
  Task-23 declaration; each reports exactly `[propext, Classical.choice, Quot.sound]` — in
  particular **no `sorryAx`**.
* No `sorry`, `admit`, new `axiom`, `@[implemented_by]` or `native_decide` occurs in the new
  modules.
* No existing module, the toolchain, `lakefile.toml` or `lake-manifest.json` was modified.
