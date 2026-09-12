# TASK 20 AUDIT — Identification of the canonical standard-cell generator

## 1. Exact production pin

* Lean `v4.28.0` (`lean-toolchain`, unchanged).
* Mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (`lake-manifest.json`, unchanged).
* `lakefile.toml` unchanged; no new dependency, no new import of upstream material
  unavailable at the pin.

## 2. Exact reused Task-19 (and earlier) declarations

Nothing frozen was redefined, replaced or renamed.  Task 20 consumes:

**Task 19 (`RequestProject/Spine/Nerve/Task19StandardCellGenerator.lean`)**

* `SpineTask19.bdFundClass`, `bdFundClass_ne_zero`, `bdFundClass_eq_lineGen`,
  `bdIsoSucc`, `bdIsoSucc_bdFundClass`, `bdEquivOne`, `bdEquivOne_bdFundClass`;
* `SpineTask19.lineGen`, `eq_lineGen_of_ne_zero`, `bd_isLine_top`, `bd_isZero`,
  `sphere_homology`, `isLine_relHomology_top`, `isZero_rel_zero`;
* `SpineTask19.stdCellTopClass`, `stdCellTopClass_ne_zero`,
  `eq_zero_or_eq_stdCellTopClass`, `stdCellTopEquiv`, `stdCellTopEquiv_stdCellTopClass`;
* `SpineTask19.pairDelta_stdCellTopClass_one`, `pairDelta_stdCellTopClass_succ`;
* `SpineTask19.charSimp`, `charChain_boundary`, `relCharChain`, `relCharChain_mem_Zc`,
  `stdCellGenerator`, `stdCellGenerator_zero_ne_zero`, `stdCellGenerator_zero_eq`;
* the face-sum data `SpineTask19.bdFaceSimp`, `bdFaceChain`, `stdCellPair_bdFaceSimp`;
* `SpineTask19.standardCellPairAcyclic`, `standardCellPairTop`.

**Earlier tasks**

* Task 14: `SpineTask14.stdCellPair`, `stdCellPair_injective`, `relChainCx`,
  `relChainCxMap`, `RelChainMod`, `relBoundary`, `relBoundary_mk`, `pairDelta`,
  `StandardCellPairAcyclic`, `StandardCellPairTop`;
* Task 13/15: `SSetChain`, `sSetChainMap`, `sSetChainMap_single`, `sSetBoundary`,
  `sSetBoundary_single`, `singCx`, `hcls`, `hcls_eq_zero_iff`, `hcls_congr`,
  `homologyMap_hcls`, `Zc`, `mem_Zc_zero`, `mem_Zc_succ`;
* Task 16: `SpineTask16.faceMap`, `bdCoord`, `range_bdCoord`, `topSimp`, `faceSimp`;
* Task 17: `SpineTask17.Bd`, `bdLocus`, `boundaryHomeo`, `continuous_subCoord`;
* Task 18: `SpineTask18.subTop`, `subInc`, `incInterU`, `excisionIso`,
  `isIso_homologyMap_excisionMap`.

## 3. Proof route used

**Route A/B hybrid** — the explicit face-sum cycle is *detected* (Route B: shown
nonzero) by an induction that reuses the *existing* Task-18 excision isomorphism, and
the resulting nonvanishing is then upgraded to the *equality* with `bdFundClass`
(Route A conclusion) through the frozen one-dimensionality statement
`SpineTask19.eq_lineGen_of_ne_zero` together with `bdFundClass_eq_lineGen`.

No new Mayer–Vietoris machinery, no general horn homology, no new sphere homology and
no new excision theory were developed.  Route C (a fresh local excision pair) was not
needed.

The inductive step (`SpineTask20.hcls_bdFaceChain_step`) works as follows.  Split the
face-sum cycle in `|∂Δ[n+2]|` into the part carried by the faces `i ≠ 0` (contained in
the open set `Uset`, the complement of the barycentre of the `0`-th face) and the
remaining face `0` (contained in `Vset`, the complement of the `0`-th vertex).  The
boundary of the `U`-part is the image of the face-sum cycle of `|∂Δ[n+1]|` under the
`0`-th face inclusion `gIn`, which lands in `Uset ∩ Vset` and admits an honest
continuous **retraction** `retr` (only a retraction is needed, no homotopy), hence is
injective on homology.  Therefore the relative class in `H(Uset, Uset ∩ Vset)` is
nonzero, and the Task-18 excision isomorphism transports the nonvanishing back to
`H_{n+1}(|∂Δ[n+2]|; ℤ/2)`.

## 4. Exact face-sum cycle definition reused

`SpineTask19.bdFaceChain`, verbatim from Task 19:

```lean
def bdFaceSimp (m : ℕ) (i : Fin (m + 2)) : Sing (Bd.{u} (m + 1)) m
def bdFaceChain (m : ℕ) : SSetChain (TopCat.toSSet.obj (Bd.{u} (m + 1))) m :=
  ∑ i : Fin (m + 2), Finsupp.single (bdFaceSimp.{u} m i) 1
```

Its cycle property is `SpineTask20.bdFaceChain_mem_Zc`.

## 5. Exact theorem identifying its homology class

```lean
theorem SpineTask20.hcls_bdFaceChain_eq_bdFundClass (m : ℕ) :
    hcls (K := singCx (Bd.{u} (m + 1))) (bdFaceChain.{u} m) (bdFaceChain_mem_Zc m)
      = bdFundClass.{u} (m + 1)
```

with the detection statement

```lean
theorem SpineTask20.hcls_bdFaceChain_ne_zero (m : ℕ) :
    hcls (K := singCx (Bd.{u} (m + 1))) (bdFaceChain.{u} m) (bdFaceChain_mem_Zc m) ≠ 0
```

proved from the base case `hcls_bdFaceChain_zero` and the inductive step
`hcls_bdFaceChain_step`.

## 6. Status of `pairDelta_stdCellGenerator`

**Proved.**

```lean
theorem SpineTask20.pairDelta_stdCellGenerator (k : ℕ) :
    (pairDelta (stdCellPair.{u} (k + 1)) (stdCellPair_injective.{u} (k + 1)) k).hom
        (stdCellGenerator.{u} (k + 1))
      = bdFundClass.{u} (k + 1)
```

(The hypothesis `0 < r` is expressed by the shape `r = k + 1`, matching the existing
Task-19 API for `pairDelta`.)

## 7. Status of `stdCellGenerator_ne_zero`

**Proved** for every `r : ℕ`:

```lean
theorem SpineTask20.stdCellGenerator_ne_zero (r : ℕ) : stdCellGenerator.{u} r ≠ 0
```

`r = 0` reuses `SpineTask19.stdCellGenerator_zero_ne_zero`.

## 8. Status of `stdCellGenerator_eq_stdCellTopClass`

**Proved** for every `r : ℕ`:

```lean
theorem SpineTask20.stdCellGenerator_eq_stdCellTopClass (r : ℕ) :
    stdCellGenerator.{u} r = stdCellTopClass.{u} r
```

## 9. Optional single-cell `relJ` corollary

**Obtained**, as a short corollary only:

```lean
def SpineTask20.cellRelJ (r : ℕ) :
    relChainCx ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι) ⟶ relChainCx (stdCellPair.{u} r)

theorem SpineTask20.homologyMap_cellRelJ_top (r : ℕ) :
    (HomologicalComplex.homologyMap (cellRelJ.{u} r) r).hom
        (hcls (Submodule.Quotient.mk (Finsupp.single (topSimp.{u} r) (1 : ZMod 2)))
          (simplicialTop_mem_Zc.{u} r))
      = stdCellGenerator.{u} r
```

i.e. the simplicial top generator is sent to `γ_r`.  No claim that `cellRelJ` is an
isomorphism is made or used.

## 10. B3

**B3 remains open and untouched.**  `SpineTask14.RelJIsIso` (and the global comparison
theory generally) is neither proved, assumed, nor referenced by any Task-20
declaration.  Task 20 also does not touch `finiteDimensional_homologyIso`,
`geometricHmap`, the nerve theorem or `w₂(TM)` transport.

## 11. First exact missing theorem if the goal failed

Not applicable — the goal did not fail.

## Outcome

**Outcome A — canonical generator identified.**
`stdCellGenerator r = stdCellTopClass r` is proved for every `r`.

## Modules added

* `RequestProject/Spine/Nerve/Task20Coords.lean` — coordinate geometry of the boundary
  locus and the continuous radial retraction `coordRetr`.
* `RequestProject/Spine/Nerve/Task20FaceMaps.lean` — the codimension-one face maps of
  `∂Δ[m+1]`, their boundary coordinates and injectivity of the induced chain maps.
* `RequestProject/Spine/Nerve/Task20Cover.lean` — the two-set open cover `Uset`, `Vset`
  of `|∂Δ[n+2]|`, the `0`-th face inclusion `gIn` into the intersection, and its
  retraction `retr`.
* `RequestProject/Spine/Nerve/Task20CanonicalGenerator.lean` — the principal module.
* `RequestProject/Spine/Nerve/Task20AxiomAudit.lean` — `#print axioms` audit.

## Final verification

`lake build RequestProject` → `Build completed successfully (8250 jobs).`
(includes the whole spine and the firewall audit, which reports
`SPINE FIREWALL AUDIT: all checks passed`).

`#print axioms` (see `Task20AxiomAudit.lean`) reports, for **every** Task-20
declaration, including

* `SpineTask20.pairDelta_stdCellGenerator`,
* `SpineTask20.stdCellGenerator_ne_zero`,
* `SpineTask20.stdCellGenerator_eq_stdCellTopClass`,
* `SpineTask20.hcls_bdFaceChain_eq_bdFundClass`,
* `SpineTask20.hcls_bdFaceChain_step`, `hcls_bdFaceChain_zero`,
  `hcls_interChain_ne_zero`, `gIn_comp_retr`, `coordRetr`,

exactly

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`.  No `sorry`, `admit`, new `axiom`, `native_decide` or
`@[implemented_by]` occurs anywhere in the Task-20 modules.
