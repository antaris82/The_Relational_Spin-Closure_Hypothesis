# TASK19_FAILBUILDS.md — Task 19 failure ledger

Every failed elaboration or proof attempt encountered while building the Task-19 modules is
recorded here, together with its diagnosis and repair.  Repaired failures remain in the ledger.
No entry changed a mathematical statement unless explicitly noted in the last column.

Legend for the *error class* column:

* `E-NAME` — unknown identifier/constant, or wrong name;
* `E-ELAB` — elaboration/unification failure (type mismatch, motive, universe);
* `E-TAC` — tactic failure (`rw` pattern not found, `simp` no progress, …);
* `E-INST` — instance not synthesised;
* `E-LINT` — linter error/warning (unused section variable);
* `E-KERNEL` — kernel-level failure (cascade from an earlier error).

| # | Module | Failing declaration | Error class | Diagnosis | Repair | Statement changed? |
|---|--------|--------------------|-------------|-----------|--------|--------------------|
| 1 | `Task19Homology` | `hcls_eq_zero_iff` | `E-TAC` | First attempt used a `simpa`/`▸` chain that could not see through `hIso`. | Rewritten with the explicit injectivity lemma `hIso_inv_injective`. | no |
| 2 | `Task19Homology` | `scN`, `hIsoSc` | `E-ELAB` | `ComplexShape.down ℕ`'s `prev`/`next` are not definitionally `q+1`/`q-1`. | Introduced `scN K q := K.sc' (q+1) q (q-1)` together with `next_eq q : next q = q - 1`. | no |
| 3 | `Task19Homology` | `lhmd` (field `commf'`) | `E-ELAB` | Term-mode `Subtype.ext (…)` gave "application type mismatch"; the required direction was also non-`symm`. | `refine … ?_; exact comm_apply q φ x`. | no |
| 4 | `Task19Homology` | `homologyMap_comm_hIso` | `E-ELAB` | Instance-argument mismatch between `Preadditive.preadditiveHasZeroMorphisms` and the inferred zero-morphism structure blocked `congrArg`. | Replaced by `congr 1`. | no |
| 5 | `Task19HZero` | `homologyMap_ptCls` | `E-TAC` | `rw [singMap_constSimp]` never matched (coercion of `ConcreteCategory.hom`). | Replaced by `show … ; exact singMap_constSimp g x 0 1`. | no |
| 6 | `Task19HZero` | `Δs0_eq` | `E-INST` | `Subsingleton (Fin (0+1))` not found. | `by fin_cases i; rfl`. | no |
| 7 | `Task19Discrete` | `isZero_homology_td` | `E-NAME` | `ModuleCat.isZero_iff` does not exist. | Correct name is `ModuleCat.isZero_iff_subsingleton` (no explicit argument). | no |
| 8 | `Task19Discrete` | `isZero_homology_td` | `E-TAC` | `push_cast` turns `((k+k+1 : ℕ) : ZMod 2)` into `↑k + ↑k + 1`, which `decide` cannot close. | Closing rewrite `rw [mod2_add_self, zero_add]`. | no |
| 9 | `Task19SphereGeometry` | `Equat` | `E-ELAB` | Declared inside an `include hv` region although it does not mention `hv`. | Took `v` as an explicit argument: `Equat (v : E)`. | no |
| 10 | `Task19SphereGeometry` | `equatInc` | `E-ELAB` | Inlining the membership proof produced `unknown free variable _fvar…`. | Split into `equatPt` / `equatPt_mem`. | no |
| 11 | `Task19SphereGeometry` | several | `E-LINT` | Unused section variables (`isOpen_Uset`, `isOpen_Vset`, `ocomp_eq_self_of_mem`, `ocomp_equatPt`, `ocomp_equatPt_ne_zero`, `unit_ne_zero`). | `omit … in` before each declaration. | no |
| 12 | `Task19BoundaryCover` | `preimageSubtypeHomeo` | `E-NAME` | Naming it `Homeomorph.preimageSubtype` inside `namespace SpineTask19` shadowed dot notation on `Homeomorph`. | Renamed `preimageSubtypeHomeo`. | no |
| 13 | `Task19BoundaryCover` | `Bd` | `E-NAME` | `∂Δ[r]` notation unavailable. | Added `open Simplicial SSet`. | no |
| 14 | `Task19BoundaryCover` | `bdInterHomotopyEquiv` | `E-NAME` | `Homeomorph.toContinuousMap` does not exist. | Used `Homeomorph.toHomotopyEquiv`. | no |
| 15 | `Task19MayerVietoris` | `mv_range_delta_one` | `E-LINT` | Automatically included `[ContractibleSpace ↑U]` unused. | `omit [ContractibleSpace ↥U] in`. | no |
| 16 | `Task19Reduced` | `sum_ptCls_mem`, `twoRedMap`, `twoRedMap_bijective`, `hred0TwoEquiv` | `E-ELAB` | `include hne`/`include hall` do not affect `def`s, and an `omit … hne in` on `sum_ptCls_mem` desynchronised the call sites. | The whole `TwoPoint` section was rewritten with **explicit** binders for `p₀ p₁ hne hall` in every declaration. | no |
| 17 | `Task19Reduced` | `mono_homologyMap_zero` | `E-TAC` | Direct `simp` could not use naturality of the augmentation. | `fun t s h => …` plus `rw [← augH_natural g t, ← augH_natural g s, h]`. | no |
| 18 | `Task19Reduced` | `twoRedMap_bijective` | `E-TAC` | The step `b = a` from `a + b = 0` needed the `ZMod 2` case split, and the goal shape had to be fixed first. | `have key : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide`, then a `show` before `rw [hba, smul_add]`. | no |
| 19 | `Task19BoundaryHomology` | `isZero_homology_of_isEmpty` | `E-ELAB` | `absurd a hempty.false` mis-typed (`IsEmpty.false : ∀ a, False`). | `exact (hempty.false a).elim`. | no |
| 20 | `Task19BoundaryHomology` | `mvOneEquiv` | `E-ELAB` | `obtain ⟨u₀⟩ : Nonempty ↥U` inside a `def` whose target is a `Type`: `Nonempty.casesOn` can only eliminate into `Prop`.  Also `include hU hV hUV` has no effect on a `def`. | Explicit binders for `U V hU hV hUV`, and `have u₀ : ↥U := Classical.arbitrary ↥U`. | no |
| 21 | `Task19BoundaryHomology` | `bdOnePt_all` | `E-TAC` | `fin_cases h : …` is not valid syntax here. | `have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide` and `rcases`. | no |
| 22 | `Task19BoundaryHomology` | `pathConnected_Bd` | `E-ELAB` | `pathConnectedSpace_of_homeo` takes its hypothesis as an **instance**, not an explicit argument. | Supplied it with `haveI` before `exact`. | no |
| 23 | `Task19BoundaryHomology` | `sphere_homology` | `E-INST` | `TotallyDisconnectedSpace ↥(Bd (0 + 1))` not found by instance search (reducibility of `0 + 1`). | `haveI … := totallyDisconnected_Bd_one` at the start of the `zero` branch. | no |
| 24 | `Task19BoundaryHomology` | `sphere_homology` | `E-ELAB` | A tactic-mode `match q, hq0 with` does not specialise the induction hypotheses that mention `n`. | Replaced by `rcases q with _ | _ | m` and `rcases n with _ | k`. | no |
| 25 | `Task19StandardCellHomology` | `epi_pProj_zero` | `E-NAME` | `sSetChainMap` is in namespace `NerveGeom`. | Added `NerveGeom` to the `open` list. | no |
| 26 | `Task19StandardCellHomology` | `epi_pProj_zero` | `E-ELAB` | Deterministic `whnf` heartbeat timeout, cascading from #25. | Disappeared once the name resolved. | no |
| 27 | `Task19StandardCellHomology` | `pIota_comp_pProj` | `E-TAC` | `rw [(relSC f).zero]` did not match: the composite had already been unfolded to `sSetChainComplexFunctor.map f ≫ relProj f`. | Introduced `have h : … = 0 := (relSC f).zero` and rewrote with `h`. | no |
| 28 | `Task19StandardCellHomology` | `epi_pProj_zero` | `E-TAC` | Residual goal `hcls ((relProj f).f 0 w) _ = hcls (mk w) _`. | Closed with `hcls_congr _ _ (relProj_f_apply f 0 w)`. | no |
| 29 | `Task19StandardCellHomology` | `subsingleton_Hred0_of_isZero` | `E-NAME` | `Subtype.instSubsingleton` does not exist. | `⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩`. | no |
| 30 | `Task19StandardCellHomology` | `standardCellPairAcyclic` | `E-INST` | `Subsingleton ↥(Hred0 …)` is an instance argument of `isZero_of_equiv_subsingleton`, not an explicit one. | Provided via `haveI` before each `exact`. | no |
| 31 | `Task19StandardCellHomology` | `isLine_relHomology_top` | `E-ELAB` | `(⟨h0Equiv t₀⟩ : IsLine …).of_iso` resolved dot notation against `Nonempty`, since `IsLine` unfolded during ascription. | Bound `have hline : IsLine … := ⟨h0Equiv t₀⟩` and called `IsLine.of_iso hline …` by name. | no |
| 32 | `Task19FundamentalClass` | `pairDelta_stdCellTopClass_one` | `E-TAC` | `rw [congrArg Subtype.val hc, map_zero]` rewrote in the wrong order (the subtype coercion was not present in the goal). | `refine … (hmono ?_); rw [map_zero]; exact congrArg Subtype.val hc`. | no |
| 33 | `Task19StandardCellGenerator` | `stdCellPair_bdFaceSimp` | `E-ELAB` | `congrFun` applied directly to `sSetTopAdj.unit.naturality ι`, which is an equation of **morphisms of simplicial sets**, not of functions. | Took `NatTrans.app … (op ⦋m⦌)` first via `congrArg`, then `congrFun`. | no |

## Attempts abandoned (recorded, not repaired)

| # | Target | Diagnosis | Status |
|---|--------|-----------|--------|
| A1 | `HomologicalComplex.HomologySequence.epi_homologyMap_of_epi_of_not_rel` | No such lemma exists in the pinned Mathlib: the bottom-degree surjectivity of `H₀(T) → H₀(T,S)` is not available off the shelf. | Replaced by the project-local `SpineTask19.epi_pProj_zero`, proved directly from surjectivity of `Submodule.mkQ` plus `hcls_surjective`. |
| A2 | `stdCellGenerator_ne_zero r` for `r ≥ 1` | Requires identifying the class of the sum of the codimension-one faces with the distinguished boundary class `β_r`.  Classically this needs excision applied to the (non-open) horn pair `(∂Δ[r], Λ^r_0)`, i.e. an open thickening of the horn together with a deformation retraction onto it.  That infrastructure does not exist in the project and was judged out of scope for Task 19. | **Open.**  See the outcome section of `TASK19_AUDIT.md`. |
| A3 | Linearisation (affine-approximation) functional as a shortcut for A2 | Checked and rejected on mathematical grounds: the complex of affine chains with vertices in `∂Δ^r` is the full ordered complex on that vertex set, hence acyclic, so the linearisation map kills the relative class.  A mod-2 degree functional at the barycentre is therefore *not* a relative cocycle for that pair. | Abandoned before any Lean code was written. |
