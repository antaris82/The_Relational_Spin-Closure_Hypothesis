import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import RequestProject.Spine.AlgebraicTopology.SkeletalAttachment
import RequestProject.Spine.AlgebraicTopology.RealizationColimits

/-!
# Task 15, WP1 : the concrete skeletal pushout square, and its realization

Task 14 proved two things separately:

* a **concrete** skeletal cell-attachment universal property, in the bespoke form
  `AttachData` / `attachExtend` / `attachExtend_unique` (`Task14SkeletalAttachment`);
* a **generic** transport theorem, `toTop_isPushout`, saying that geometric realization carries
  a `CategoryTheory.IsPushout` square to a `CategoryTheory.IsPushout` square
  (`Task14Comparison`).

What was missing was their *theorem-level composition*: the concrete square was never packaged
as an actual `CategoryTheory.IsPushout`, so the generic theorem could not be applied to it.
This module closes that gap.

## Contents

* `attachSrc`, `attachTgt` — the coproducts `∐_{σ ∈ NDeg_r} ∂Δ[r]` and `∐_{σ ∈ NDeg_r} Δ[r]`.
* `attachMap`, `cellMap`, `bdryMap` — the three structural maps.  The attaching maps are the
  canonical ones, `σ · (−)`, i.e. the Yoneda transposes of the nondegenerate simplices; nothing
  is chosen.
* `skeletalIsPushout` — **the concrete square is a pushout of simplicial sets.**
* `skeletalIsPushout_toTop` — **its realization is a pushout of topological spaces**, obtained
  by applying the Task-14 generic theorem to the Task-14 concrete square.
* `skeletalIsPushout_toTop_coprod` — the same square written with the coproducts
  `∐_σ |∂Δ[r]|` and `∐_σ |Δ[r]|` of the realized cells, using that a left adjoint preserves
  coproducts.

Nothing here is assumed: `skeletalIsPushout` is proved from the Task-14 universal property
(`attachExtend`, `attachExtend_comp_skInc`, `attachExtend_cell`, `attachExtend_unique`) and
nothing else.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet SpineTask13 SpineTask14

universe u

namespace SpineTask15

variable (X : SSet.{u}) (r : ℕ)

/-! ## The three structural maps of the square -/

/-- The characteristic map of the cell of a nondegenerate `r`-simplex, as a map to `X`:
the Yoneda transpose `σ · (−)` of `σ` itself. -/
def charTot (σ : X.nonDegenerate r) : (Δ[r] : SSet.{u}) ⟶ X := yonedaEquiv.symm σ.1

@[simp]
theorem charTot_app {σ : X.nonDegenerate r} {m : SimplexCategoryᵒᵖ} (y : (Δ[r] : SSet.{u}).obj m) :
    (charTot X r σ).app m y = X.map y.down.op σ.1 := rfl

theorem range_charTot_le (σ : X.nonDegenerate r) :
    Subcomplex.range (charTot X r σ) ≤ X.skeleton (r + 1) := by
  rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff, charTot,
    Equiv.apply_symm_apply]
  exact X.mem_skeleton σ.1 (Nat.lt_succ_self r)

theorem range_attach_le (σ : X.nonDegenerate r) :
    Subcomplex.range ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι ≫ charTot X r σ)
      ≤ X.skeleton r := by
  rintro ⟨m⟩ x ⟨y, rfl⟩
  induction m using SimplexCategory.rec with | _ k =>
  have hh : ¬ Epi (y.1.down : (⦋k⦌ : SimplexCategory) ⟶ ⦋r⦌) := by
    rw [SimplexCategory.epi_iff_surjective]
    exact y.2
  exact mem_skeleton_of_not_epi σ y.1.down hh

/-- The characteristic map of the cell, landing in the `r`-skeleton. -/
def cellChar (σ : X.nonDegenerate r) : (Δ[r] : SSet.{u}) ⟶ Sk X (r + 1) :=
  Subcomplex.lift (charTot X r σ) (range_charTot_le X r σ)

/-- The canonical attaching map `∂Δ[r] ⟶ K^{(r-1)}` of the cell of `σ`. -/
def cellAttach (σ : X.nonDegenerate r) :
    ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ Sk X r :=
  Subcomplex.lift ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι ≫ charTot X r σ)
    (range_attach_le X r σ)

theorem cellChar_yonedaEquiv (σ : X.nonDegenerate r) :
    yonedaEquiv (cellChar X r σ) = cellSimplex σ := by
  refine Subtype.ext ?_
  show (charTot X r σ).app (op (SimplexCategory.mk r)) (ULift.up (𝟙 _)) = σ.1
  rw [charTot_app]
  simp

theorem cellAttach_comm (σ : X.nonDegenerate r) :
    cellAttach X r σ ≫ skInc X r
      = (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι ≫ cellChar X r σ := by
  apply (cancel_mono (X.skeleton (r + 1)).ι).1
  rfl

/-! ## The square -/

/-- `∐_{σ ∈ NDeg_r(X)} ∂Δ[r]`. -/
abbrev attachSrc : SSet.{u} := ∐ fun _ : X.nonDegenerate r => ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex) : SSet.{u})

/-- `∐_{σ ∈ NDeg_r(X)} Δ[r]`. -/
abbrev attachTgt : SSet.{u} := ∐ fun _ : X.nonDegenerate r => (Δ[r] : SSet.{u})

/-- The coproduct of the boundary inclusions. -/
def bdryMap : attachSrc X r ⟶ attachTgt X r :=
  Limits.Sigma.map fun _ => (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι

/-- The total attaching map `∐_σ ∂Δ[r] ⟶ K^{(r-1)}`. -/
def attachMap : attachSrc X r ⟶ Sk X r := Sigma.desc (cellAttach X r)

/-- The total characteristic map `∐_σ Δ[r] ⟶ K^{(r)}`. -/
def cellMap : attachTgt X r ⟶ Sk X (r + 1) := Sigma.desc (cellChar X r)

theorem attach_commSq : CommSq (attachMap X r) (bdryMap X r) (skInc X r) (cellMap X r) where
  w := by
    refine Sigma.hom_ext _ _ fun σ => ?_
    simp only [attachMap, bdryMap, cellMap, colimit.ι_desc, Cofan.mk_ι_app,
      ι_colimMap_assoc, Discrete.natTrans_app, colimit.ι_desc_assoc]
    exact cellAttach_comm X r σ


/-! ## WP1(1) : the concrete square is a pushout -/

variable {X r}

/-- The Task-14 `AttachData` extracted from a cocone under the concrete skeletal square.
This is the bridge between the bespoke universal property of Task 14 and the categorical
notion of a pushout. -/
def coconeAttachData {Y : SSet.{u}} (a : Sk X r ⟶ Y) (b : attachTgt X r ⟶ Y)
    (w : attachMap X r ≫ a = bdryMap X r ≫ b) : AttachData X r Y where
  base := a
  cell σ := yonedaEquiv (Sigma.ι (fun _ : X.nonDegenerate r => (Δ[r] : SSet.{u})) σ ≫ b)
  compat := by
    intro n h hh σ
    have key : cellAttach X r σ ≫ a
        = (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι ≫
            (Sigma.ι (fun _ : X.nonDegenerate r => (Δ[r] : SSet.{u})) σ ≫ b) := by
      have h1 : Sigma.ι (fun _ : X.nonDegenerate r =>
            ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex) : SSet.{u})) σ ≫ attachMap X r
          = cellAttach X r σ := by
        simp [attachMap]
      rw [← h1, Category.assoc, w, ← Category.assoc, bdryMap, Sigma.ι_map, Category.assoc]
    have hmem : (ULift.up h : (Δ[r] : SSet.{u}).obj (op (SimplexCategory.mk n)))
        ∈ (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).obj (op (SimplexCategory.mk n)) := fun hs =>
      hh (SimplexCategory.epi_iff_surjective.2 hs)
    have hx : (Δ[r] : SSet.{u}).map h.op
          (ULift.up (𝟙 (SimplexCategory.mk r))) = ULift.up h := by
      show ULift.up (h ≫ 𝟙 _) = ULift.up h
      rw [Category.comp_id]
    have step1 : Y.map h.op
        (yonedaEquiv (Sigma.ι (fun _ : X.nonDegenerate r => (Δ[r] : SSet.{u})) σ ≫ b))
        = (Sigma.ι (fun _ : X.nonDegenerate r => (Δ[r] : SSet.{u})) σ ≫ b).app
            (op (SimplexCategory.mk n)) (ULift.up h) := by
      have hnat := FunctorToTypes.naturality (Δ[r] : SSet.{u}) Y
        (Sigma.ι (fun _ : X.nonDegenerate r => (Δ[r] : SSet.{u})) σ ≫ b) h.op
        (ULift.up (𝟙 (SimplexCategory.mk r)))
      rw [hx] at hnat
      exact hnat.symm
    rw [step1]
    show ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι ≫
        (Sigma.ι (fun _ : X.nonDegenerate r => (Δ[r] : SSet.{u})) σ ≫ b)).app
          (op (SimplexCategory.mk n)) ⟨ULift.up h, hmem⟩ = _
    rw [← key]
    rfl


variable {Y : SSet.{u}}

/-- The map out of the `r`-skeleton determined by a cocone under the square. -/
def pushoutDesc (a : Sk X r ⟶ Y) (b : attachTgt X r ⟶ Y)
    (w : attachMap X r ≫ a = bdryMap X r ≫ b) : Sk X (r + 1) ⟶ Y :=
  attachExtend (coconeAttachData a b w)

theorem pushoutDesc_left (a : Sk X r ⟶ Y) (b : attachTgt X r ⟶ Y)
    (w : attachMap X r ≫ a = bdryMap X r ≫ b) :
    skInc X r ≫ pushoutDesc a b w = a :=
  attachExtend_comp_skInc _

theorem cellMap_ι (σ : X.nonDegenerate r) :
    Sigma.ι (fun _ : X.nonDegenerate r => (Δ[r] : SSet.{u})) σ ≫ cellMap X r
      = cellChar X r σ := by
  simp [cellMap]

theorem pushoutDesc_right (a : Sk X r ⟶ Y) (b : attachTgt X r ⟶ Y)
    (w : attachMap X r ≫ a = bdryMap X r ≫ b) :
    cellMap X r ≫ pushoutDesc a b w = b := by
  refine Sigma.hom_ext _ _ fun σ => ?_
  rw [← Category.assoc, cellMap_ι]
  refine yonedaEquiv.injective ?_
  rw [yonedaEquiv_comp, cellChar_yonedaEquiv]
  exact attachExtend_cell _ σ

theorem pushoutDesc_uniq (a : Sk X r ⟶ Y) (b : attachTgt X r ⟶ Y)
    (w : attachMap X r ≫ a = bdryMap X r ≫ b) (m : Sk X (r + 1) ⟶ Y)
    (h₁ : skInc X r ≫ m = a) (h₂ : cellMap X r ≫ m = b) :
    m = pushoutDesc a b w := by
  refine attachExtend_unique _ m h₁ fun σ => ?_
  have hσ : cellChar X r σ ≫ m
      = Sigma.ι (fun _ : X.nonDegenerate r => (Δ[r] : SSet.{u})) σ ≫ b := by
    rw [← h₂, ← Category.assoc, cellMap_ι]
  have : yonedaEquiv (cellChar X r σ ≫ m)
      = yonedaEquiv (Sigma.ι (fun _ : X.nonDegenerate r => (Δ[r] : SSet.{u})) σ ≫ b) := by
    rw [hσ]
  rwa [yonedaEquiv_comp, cellChar_yonedaEquiv] at this

variable (X r)

/-- **WP1(1) — the concrete skeletal attachment square, packaged as a `CategoryTheory.IsPushout`.**

```
∐_{σ ∈ NDeg_r(K)} ∂Δ[r] ──────▶ K^{(r-1)}
        │                            │
        ▼                            ▼
∐_{σ ∈ NDeg_r(K)}  Δ[r]  ──────▶ K^{(r)}
```

The proof is exactly the Task-14 universal property (`attachExtend`,
`attachExtend_comp_skInc`, `attachExtend_cell`, `attachExtend_unique`); no new mathematical
input is used, and no different attaching maps are chosen. -/
theorem skeletalIsPushout :
    IsPushout (attachMap X r) (bdryMap X r) (skInc X r) (cellMap X r) :=
  IsPushout.of_isColimit' (attach_commSq X r)
    (PushoutCocone.IsColimit.mk _ (fun s => pushoutDesc s.inl s.inr s.condition)
      (fun _ => pushoutDesc_left _ _ _) (fun _ => pushoutDesc_right _ _ _)
      (fun _ m h₁ h₂ => pushoutDesc_uniq _ _ _ m h₁ h₂))

/-! ## WP1(2)–(3) : the realized square -/

/-- **WP1(2)–(3) — the realized skeletal square is a topological pushout.**

This is the theorem-level composition that Task 14 was missing: the *concrete* square
`skeletalIsPushout` fed into the *generic* transport theorem `SpineTask14.toTop_isPushout`. -/
theorem skeletalIsPushout_toTop :
    IsPushout (SSet.toTop.map (attachMap X r)) (SSet.toTop.map (bdryMap X r))
      (SSet.toTop.map (skInc X r)) (SSet.toTop.map (cellMap X r)) :=
  SpineTask14.toTop_isPushout (skeletalIsPushout X r)


/-- `∐_{σ ∈ NDeg_r(K)} |∂Δ[r]|`, the coproduct of the realized cell boundaries. -/
abbrev topAttachSrc : TopCat.{u} :=
  ∐ fun _ : X.nonDegenerate r =>
    SSet.toTop.obj ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex) : SSet.{u})

/-- `∐_{σ ∈ NDeg_r(K)} |Δ[r]|`, the coproduct of the realized cells. -/
abbrev topAttachTgt : TopCat.{u} :=
  ∐ fun _ : X.nonDegenerate r => SSet.toTop.obj (Δ[r] : SSet.{u})

/-- The coproduct of the realized boundary inclusions `|∂Δ[r]| ⟶ |Δ[r]|`. -/
def topBdryMap : topAttachSrc X r ⟶ topAttachTgt X r :=
  Limits.Sigma.map fun _ => SSet.toTop.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι

/-- The realized total attaching map `∐_σ |∂Δ[r]| ⟶ |K^{(r-1)}|`. -/
def topAttachMap : topAttachSrc X r ⟶ SSet.toTop.obj (Sk X r) :=
  Sigma.desc fun σ => SSet.toTop.map (cellAttach X r σ)

/-- The realized total characteristic map `∐_σ |Δ[r]| ⟶ |K^{(r)}|`. -/
def topCellMap : topAttachTgt X r ⟶ SSet.toTop.obj (Sk X (r + 1)) :=
  Sigma.desc fun σ => SSet.toTop.map (cellChar X r σ)

/-- **WP1(3) — the realized skeletal square, written with the coproducts of the realized
cells.**

```
∐_{σ ∈ NDeg_r(K)} |∂Δ[r]| ──────▶ |K^{(r-1)}|
        │                              │
        ▼                              ▼
∐_{σ ∈ NDeg_r(K)}  |Δ[r]|  ──────▶ |K^{(r)}|
```

is a pushout of topological spaces.  Obtained from `skeletalIsPushout_toTop` by transporting
along the canonical comparison isomorphisms `∐_σ |Δ[r]| ≅ |∐_σ Δ[r]|`, which exist because
geometric realization is a left adjoint. -/
theorem skeletalIsPushout_toTop_coprod :
    IsPushout (topAttachMap X r) (topBdryMap X r) (SSet.toTop.map (skInc X r))
      (topCellMap X r) := by
  refine (skeletalIsPushout_toTop X r).of_iso'
    (PreservesCoproduct.iso SSet.toTop
      (fun _ : X.nonDegenerate r =>
        ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex) : SSet.{u}))).symm
    (Iso.refl _)
    (PreservesCoproduct.iso SSet.toTop
      (fun _ : X.nonDegenerate r => (Δ[r] : SSet.{u}))).symm
    (Iso.refl _) ?_ ?_ ?_ ?_
  · show sigmaComparison _ _ ≫ _ = _ ≫ 𝟙 _
    rw [Category.comp_id, attachMap, topAttachMap, sigmaComparison_map_desc]
  · show sigmaComparison _ _ ≫ _ = _ ≫ sigmaComparison _ _
    refine Sigma.hom_ext _ _ fun σ => ?_
    rw [← Category.assoc, ι_comp_sigmaComparison, bdryMap, ← Functor.map_comp, Sigma.ι_map,
      Functor.map_comp, topBdryMap, ← Category.assoc, Sigma.ι_map, Category.assoc,
      ι_comp_sigmaComparison]
  · simp
  · show sigmaComparison _ _ ≫ _ = _ ≫ 𝟙 _
    rw [Category.comp_id, cellMap, topCellMap, sigmaComparison_map_desc]

end SpineTask15
