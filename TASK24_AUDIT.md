# TASK 24 AUDIT — completion of Task 23: relative cell-sum chain isomorphism and finite `tgtDecomp`

**Outcome: A — Task 23 fully completed in finite scope.**

`IsIso (tgtDecomp X r q)` is proved for every `q` under `[Fintype ↑(X.nonDegenerate r)]`, with
`tgtDecomp` the *frozen Task-22 map* (no replacement definition), and the finite-family
`SpineTask14.RelJIsIso X r` is derived from it.  The arbitrary-family statement remains open
and was deliberately not attempted.

---

## 1. Provenance repair (required by §14 of the task)

1. **Task 23 ended “Out of Budget”**, in the middle of WP6.
2. The recorded `TASK23_AUDIT.md` was written *before* the final Task-23 source tree was
   complete, and therefore **does not mention** the two modules
   * `RequestProject/Spine/Nerve/Task23CellSum.lean`
   * `RequestProject/Spine/Nerve/Task23FinsuppComplex.lean`
3. Both modules **were present in the supplied final Task-23 archive** and are the recorded
   starting point of Task 24.
4. **Task 24 reused them; it did not reconstruct them.**  No declaration of either module was
   restated, renamed or duplicated in the Task-24 modules; they are imported.
5. **Compilation status of the inherited modules.**
   * `Task23FinsuppComplex.lean` compiled **unchanged** (one pre-existing style warning:
     `[DecidableEq α]` is an unused section variable in `isIso_sumHomologyMap`; not touched,
     since the theorem statement is inherited and frozen).
   * `Task23CellSum.lean` **did not compile** in the pinned environment: `exists_cellIncl`
     failed with *“don't know how to synthesize implicit argument `σ`”*.  A one-token,
     mathematically conservative repair was applied — the implicit argument is now supplied,
     `refine mem_openStdCell_of_cellPt (σ := σ) X r ?_`.  No statement was changed; see
     `TASK24_FAILBUILDS.md`, entry F1.  This is the only edit made to inherited Task-23
     material.

---

## 6. Task-23 declarations reused (not reproved)

Geometric / excisive side (`Task23SkeletonTopology`, `Task23PuncturedCell`,
`Task23PushoutRetraction`, `Task23RelativeHomotopy`, `Task23Excision`,
`Task23StandardCellExcision`):

`openCells`, `puncturedNbhd`, `barySet`, `baryPoint`, `openStdCell`, `puncturedCell`,
`cellBary`, `isOpen_openCells`, `isOpen_puncturedNbhd`, `openCells_union_puncturedNbhd`,
`skToV`/`skToVMap`, `vRetract`, `vHomotopy`, `vHomotopyEquiv`, `pairAV`, `pairAVIso`,
`excisionIsoCells`, **`cellPairIso`**, `bdryHomotopyEquiv`, `stdPairMap`, `stdPairIso`,
`stdExcisionIso`, **`stdCellIso`**, `SpineTask18.excisionMap`, `SpineTask18.excisionIso`,
`SpineTask18.incInterU`, `SpineTask18.subInc`, `SpineTask18.subTop`,
`SpineTask18.mem_range_sSetChainMap`, `SpineTask18.mem_of_single`.

Post-audit Task-23 modules:

`cellPt`, `cellPt_eq`, `continuous_cellPt`, `cellPt_mem_openCells`, `cellPt_mem_barySet_iff`,
`cellIncl`, `cellInclMap`, `cellIncl_injective`, `cellIncl_component`, `isOpenMap_cellIncl`,
`exists_cellIncl`, `exists_cellIncl_lift`, `cellSingMap`, **`bijective_cellSingMap`**,
**`cellSingMap_mem_range_incInterU_iff`**, `finsuppCx`, `finsuppCx_d`, `finsuppCxι`,
`finsuppCxπ`, `sumHomologyMap`, `sumHomologyMap_single`, `isIso_sumHomologyMap`,
**`isIso_sumHomologyMap_of_iso`**.

Task-22 declarations reused (frozen, unmodified): `topCellPairMap`, **`tgtDecomp`**,
`tgtDecomp_single`, `tgtSumMod`, `srcDecomp`, `isIso_srcDecomp`, `sumCellRelJ`,
`isIso_sumCellRelJ`, `relJ_decomposition_square`, `homologyMap_relJ_eq`,
`relJIsIso_of_singularCellFamilyAdditivity`, `SingularCellFamilyAdditivity`,
`relChainCxMap_comp`, `relChainCxMap_eq_of_v`.

---

## 7. Exact construction of Θ_abs (WP1 + WP2)

New generic layer in `Task24RelativeCellSum.lean` (kept minimal, no new subtree):

* `SpineTask24.finsuppCxDesc F : finsuppCx α C ⟶ K` — the map out of the `α`-fold direct sum
  determined by a family of chain maps `F s : C ⟶ K`; degreewise `Finsupp.lsum`.  Its defining
  property is `finsuppCxι_desc : finsuppCxι α C s ≫ finsuppCxDesc F = F s`.  No finiteness is
  used.
* `SpineTask24.famChainMap φ` for `φ : α → (S ⟶ T)` a family of maps of simplicial sets:
  `famChainMap φ = finsuppCxDesc (fun s => sSetChainComplexFunctor.map (φ s))`.
* `SpineTask24.thetaAbs X r := famChainMap (cellSSetMap X r)` where
  `cellSSetMap X r σ = TopCat.toSSet.map (cellInclMap X r σ)`:

  `Θ_abs : ⊕_{σ ∈ X.nonDegenerate r} C_*^{sing}(Δ°) ⟶ C_*^{sing}(U)`.

Theorem-level facts required by §5 of the task:

1. *agreement with the cell inclusion on a basis generator*:
   `famChainMap_f_single`/`famChainMapDeg_single` —
   `Θ_abs (single σ c) = sSetChainMap (Sing(cellIncl σ)) c`, i.e. on `single σ (single s 1)` it
   is the generator `cellSingMap X r q (σ, s)`;
2. *bijectivity*: `bijective_famChainMapDeg`, from the **coordinate formula**
   `famChainMapDeg_apply : Θ_abs(d) (cellSingMap (σ,s)) = d σ s` (injectivity) and from
   `SpineTask18.mem_of_single` applied to the generators (surjectivity).  The only geometric
   input is `bijective_cellSingMap`;
3. *the inverse selects the unique cell*: this is exactly the content of the coordinate formula
   together with the bijectivity of `cellSingMap`; no explicit inverse formula is written, in
   accordance with §5.

`isIso_thetaAbs : IsIso (thetaAbs X r)` via `HomologicalComplex.Hom.isIso_of_components`.

## 8. Boundary compatibility (WP2)

`Θ_abs` is **not** merely a degreewise module equivalence.  It is assembled as
`finsuppCxDesc` of a family of chain maps, so `HomologicalComplex.Hom.comm` holds by
construction; the two inputs are:

* each component `sSetChainComplexFunctor.map (Sing(cellIncl X r σ))` is a chain map — this is
  the naturality of the singular boundary, i.e. precisely the statement that every face of a
  singular simplex lying in the open cell of `σ` again lies in the open cell of `σ`, because a
  face is a precomposition with a simplex face map;
* the differential of `finsuppCx α C` is `Finsupp.mapRange` of the differential of `C`
  (`SpineTask23.finsuppCx_d`), so the descended square is checked on `Finsupp.single`
  generators (`finsuppCxDesc`, field `comm'`).

## 9. Exact construction of Θ_rel (WP3)

* `cellInclInterMap X r σ : subTop (Δ° ∩ (Δ°∖{b_r})) ⟶ subTop (U ∩ V)` — the cell inclusion of
  pairs, with `cellInclInter_square` the commuting square of spaces and `cellSSet_square` its
  image under `Sing`.  Membership in `V = Y ∖ B` is the inherited `cellPt_mem_barySet_iff`.
* `SpineTask24.famRelChainMap f f' φ ψ hsq := finsuppCxDesc (fun s => relChainCxMap f f' (ψ s) (φ s) (hsq s))`
  — the direct-sum comparison of *relative* complexes, built with the project's own
  `SpineTask14.relChainCx`/`relChainCxMap`.  No new relative-chain definition was introduced.
* `SpineTask24.thetaRel X r`:

  `Θ_rel : ⊕_{σ} C_*^{sing}(Δ°, Δ°∖{b_r}) ⟶ C_*^{sing}(U, U ∩ V)`,

  with `finsuppCxι_thetaRel : finsuppCxι _ _ σ ≫ Θ_rel = cellRelPairMap X r σ`.
* `isIso_famRelChainMap` (hence `isIso_thetaRel`): degreewise bijectivity of the quotient map.
  Surjectivity is lifted from `Θ_abs` through `famRelChainMapDeg_mapRangeMk`
  (`Θ_rel ∘ (⊕ mk) = mk ∘ Θ_abs`) and `mapRangeMk_surjective`.  Injectivity uses
  `SpineTask18.mem_range_sSetChainMap` (a chain lies in the subcomplex iff every simplex of its
  support does), the coordinate formula, and **the inherited relative criterion**
  `cellSingMap_mem_range_incInterU_iff`, which is the only place where the relative structure
  enters.  `Θ_rel` is an actual isomorphism of chain complexes, not an abstract existence
  statement.

## 10. Finite relative homology decomposition (WP4)

`SpineTask24.sumCellHomology X r q := SpineTask23.sumHomologyMap (fun σ => finsuppCxι _ _ σ ≫ thetaRel X r) q`
with `sumCellHomology_single : single σ m ↦ H_q(cellRelPairMap X r σ) m`, and

`isIso_sumCellHomology [Fintype ↑(X.nonDegenerate r)] : IsIso (sumCellHomology X r q)`

proved by the inherited `SpineTask23.isIso_sumHomologyMap_of_iso` applied to `Θ_rel`.  This is

  `⊕_{σ} H_q^{sing}(Δ°, Δ°∖{b_r}) ≅ H_q^{sing}(U, U ∩ V)`,

the finite disjoint-union blocker recorded by Task 23.  `Fintype` is used **here only**.

## 11. Exact equality with `tgtDecomp` (WP5 + WP6)

Transport (WP5), in `Task24FiniteTargetDecomp.lean`, all at chain level:

* `stdToNbhdMap X r σ : subTop(|Δ[r]|∖{b_r}) ⟶ subTop(Y∖B)` and
  `cellVPairMap X r σ : C_*^{sing}(|Δ[r]|, |Δ[r]|∖{b_r}) ⟶ C_*^{sing}(Y, Y∖B)`;
* `excision_cell_square` :
  `excisionMap(Δ°,Δ°∖{b}) ≫ cellVPairMap σ = cellRelPairMap σ ≫ excisionMap(U,V)`.
  Both sides are `relChainCxMap` of the *same* square, by `relChainCxMap_comp` and
  `relChainCxMap_eq_of_v`; the geometric input is
  `subInc Δ° ≫ |cellChar X r σ| = cellIncl X r σ ≫ subInc U`, i.e. `cellPt_eq`;
* `stdPair_cell_square` : `stdPairMap ≫ cellVPairMap σ = topCellPairMap X r σ ≫ pairAV`;
* `cell_decomposition_square` (homology):

  `stdCellIso.hom ≫ H_q(topCellPairMap X r σ) = H_q(cellRelPairMap X r σ) ≫ cellPairIso.hom`.

WP6, the principal conceptual endpoint:

```lean
theorem SpineTask24.mapRangeStd_tgtDecomp (X : SSet) (r q : ℕ) :
    mapRangeStd X r q ≫ tgtDecomp X r q = sumCellHomology X r q ≫ (cellPairIso X r q).hom
```

where `mapRangeStd X r q = Finsupp.mapRange (stdCellIso r q).hom`, an isomorphism
(`isIso_mapRangeStd`).  The proof is extensionality on `Finsupp.single σ m`
(`Finsupp.lhom_ext`), followed by `tgtDecomp_single` and `sumCellHomology_single`; it then
reduces to `cell_decomposition_square`, i.e. componentwise to the fact that both constructions
are induced by *the same actual cell inclusion*.  No extensionality axiom and no replacement
definition were introduced; `tgtDecomp` is the frozen Task-22 declaration.

## 12. `IsIso (tgtDecomp X r q)` (WP7)

```lean
theorem SpineTask24.isIso_tgtDecomp_finite (X : SSet) (r q : ℕ)
    [Fintype ↑(X.nonDegenerate r)] : IsIso (tgtDecomp X r q)
```

by rewriting `tgtDecomp = inv (mapRangeStd) ≫ sumCellHomology ≫ cellPairIso.hom`, all three
factors isomorphisms.  Packaged as `singularCellFamilyAdditivity_finite`
(`SpineTask22.SingularCellFamilyAdditivity X r`) and
`finiteSingularCellFamilyAdditivity_finite` (`SpineTask23.FiniteSingularCellFamilyAdditivity`).

## 13. Finite-family `RelJIsIso` (WP8)

```lean
theorem SpineTask24.relJIsIso_finite (X : SSet) (r : ℕ)
    [Fintype ↑(X.nonDegenerate r)] : SpineTask14.RelJIsIso X r
```

derived, with no new topology, from the frozen Task-22 corollary
`relJIsIso_of_singularCellFamilyAdditivity`, whose proof is exactly
`srcDecomp⁻¹ ≫ (⊕_σ H_*(cellRelJ)) ≫ tgtDecomp` with all three factors isomorphisms
(`isIso_srcDecomp`, `isIso_sumCellRelJ`, and now WP7).

## 14. Arbitrary-family B3 remains open

`SpineTask14.RelJIsIso X r` **without** `[Fintype ↑(X.nonDegenerate r)]` is *not* proved and
*not* assumed anywhere.  Nothing in this task removes the finiteness hypothesis, and no
finite-support reduction to arbitrary families was begun.  Likewise untouched: arbitrary
coproduct preservation, local finiteness, wedge axioms, filtered colimits, compact supports,
skeletal induction, the global simplicial–singular comparison, the Nerve theorem, `w₂(TM)`.

---

## Declaration classification

| status | declarations |
| --- | --- |
| inherited Task-23, unchanged | everything listed in §6 except `exists_cellIncl` |
| repaired Task-23 | `SpineTask23.exists_cellIncl` (proof-only, implicit argument supplied; statement unchanged) |
| new Task-24 | `finsuppCxDescMap`, `finsuppCxDescMap_single`, `finsuppCxDesc`, `finsuppCxDesc_f_single`, `finsuppCxι_desc`, `famSimp`, `famChainMap`, `famChainMapDeg`, `famChainMap_f_hom`, `famChainMapDeg_single`, `famSimp_injective_component`, `famChainMapDeg_apply`, `injective_famChainMapDeg`, `surjective_famChainMapDeg`, `bijective_famChainMapDeg`, `isIso_famChainMap`, `famRelChainMap`, `famRelChainMapDeg`, `famRelChainMap_f_hom`, `famRelChainMapDeg_single`, `mapRangeMk`, `mapRangeMk_single`, `mapRangeMk_apply`, `famRelChainMapDeg_mapRangeMk`, `mapRangeMk_surjective`, `injective_famRelChainMapDeg`, `surjective_famRelChainMapDeg`, `isIso_famRelChainMap`, `cellInclInterMap`, `cellInclInter_square`, `cellSSetMap`, `cellSSetInterMap`, `cellSSet_square`, `famSimp_cellSSetMap`, `bijective_famSimp_cell`, `thetaAbs`, `isIso_thetaAbs`, `cellRelPairMap`, `thetaRel`, `finsuppCxι_thetaRel`, `isIso_thetaRel`, `sumCellHomology`, `sumCellHomology_single`, `isIso_sumCellHomology`, `stdToNbhdMap`, `subInc_cellChar`, `subInc_puncturedCell_square`, `cellVPairMap`, `excision_cell_square`, `stdPair_cell_square`, `homology_stdPair_cell_square`, `homology_excision_cell_square`, `cell_decomposition_square`, `mapRangeStd`, `bijective_stdCellIso_hom`, `isIso_mapRangeStd`, `mapRangeStd_tgtDecomp`, `isIso_tgtDecomp_finite`, `singularCellFamilyAdditivity_finite`, `finiteSingularCellFamilyAdditivity_finite`, `relJIsIso_finite` |

## Build and axiom audit

* `lake build RequestProject` — completes with no errors, and now includes the two post-audit
  Task-23 modules in an actual verified build.
* `RequestProject/Spine/Nerve/Task24AxiomAudit.lean` prints the axioms of every principal
  inherited and new declaration listed above.  Every one reports exactly
  `[propext, Classical.choice, Quot.sound]`.  **No `sorryAx`.**
* No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` or `@[implemented_by]` occurs in the
  Task-24 sources; `lean-toolchain` and `lake-manifest.json` are unchanged.

## Files

* `RequestProject/Spine/Nerve/Task24RelativeCellSum.lean` (WP1–WP4)
* `RequestProject/Spine/Nerve/Task24FiniteTargetDecomp.lean` (WP5–WP8)
* `RequestProject/Spine/Nerve/Task24AxiomAudit.lean`
* `TASK24_AUDIT.md`, `TASK24_FAILBUILDS.md`
* one-line repair in `RequestProject/Spine/Nerve/Task23CellSum.lean`
