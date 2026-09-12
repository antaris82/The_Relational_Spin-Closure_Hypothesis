import RequestProject.Spine.Nerve.Geometry.RelativeHomotopy
import RequestProject.Spine.AlgebraicTopology.Excision

/-!
# Task 23, WP5 — excision for the finite cell family

With `A = |Sk X r| ⊆ V = Y \ B ⊆ Y = |Sk X (r+1)|` and `U = Y \ A` (Task 23 WP1), this module

* proves the general comparison lemma `isIso_homologyMap_relChainCxMap`: a map of pairs whose
  two absolute comparison maps are quasi-isomorphisms induces an isomorphism of relative
  homology (a consequence of the pinned `HomologicalComplex.HomologySequence.quasiIso_τ₃`);
* deduces `isIso_homologyMap_pairAV` — **`H_q^{sing}(Y, A) ≅ H_q^{sing}(Y, V)`** — from the
  Task 23 WP4 deformation retraction;
* instantiates the Task-18 excision theorem at the excisive pair `(U, V)`, giving
  `excisionIsoCells : H_q^{sing}(U, U ∩ V) ≅ H_q^{sing}(Y, V)`;
* composes the two into `cellPairIso : H_q^{sing}(U, U ∩ V) ≅ H_q^{sing}(Y, A)`.

All hypotheses of the Task-18 excision theorem (`U`, `V` open, `U ∪ V = Y`) are the Task 23 WP1
theorems; nothing is assumed.
-/

noncomputable section

open CategoryTheory Limits Simplicial SSet NerveGeom SpineTask13 SpineTask14 SpineTask15
  SpineTask18 SpineTask19

universe u

namespace SpineTask23

/-! ## A general comparison lemma for maps of pairs -/

theorem isIso_homologyMap_relChainCxMap {S T S' T' : SSet.{u}} (f : S ⟶ T) (f' : S' ⟶ T')
    (u : S ⟶ S') (v : T ⟶ T') (hsq : f ≫ v = u ≫ f')
    (hf : ∀ n, Function.Injective (f.app n)) (hf' : ∀ n, Function.Injective (f'.app n))
    (hu : ∀ q, IsIso (HomologicalComplex.homologyMap (sSetChainComplexFunctor.map u) q))
    (hv : ∀ q, IsIso (HomologicalComplex.homologyMap (sSetChainComplexFunctor.map v) q))
    (q : ℕ) : IsIso (HomologicalComplex.homologyMap (relChainCxMap f f' u v hsq) q) := by
  set φ : relSC f ⟶ relSC f' := relSCMap f f' u v hsq with hφ
  have hse₁ : (relSC f).ShortExact := relSC_shortExact _ hf
  have hse₂ : (relSC f').ShortExact := relSC_shortExact _ hf'
  have hτ₁ : QuasiIso φ.τ₁ := ⟨fun i => (quasiIsoAt_iff_isIso_homologyMap _ i).2 (hu i)⟩
  have hτ₂ : QuasiIso φ.τ₂ := ⟨fun i => (quasiIsoAt_iff_isIso_homologyMap _ i).2 (hv i)⟩
  have hτ₃ : QuasiIso φ.τ₃ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hse₁ hse₂ hτ₁ hτ₂
  have h : φ.τ₃ = relChainCxMap f f' u v hsq := rfl
  rw [← h]
  exact (quasiIsoAt_iff_isIso_homologyMap _ q).1 (hτ₃.quasiIsoAt q)

theorem isIso_homologyMap_id (S : SSet.{u}) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (sSetChainComplexFunctor.map (𝟙 S)) q) := by
  rw [sSetChainComplexFunctor.map_id, HomologicalComplex.homologyMap_id]
  infer_instance

section Skeleton

variable (X : SSet.{u}) (r : ℕ)

/-! ## `H_q(Y, A) ≅ H_q(Y, V)` -/

/-- The inclusion `V ⟶ Y`. -/
abbrev vIncY : SpineTask18.subTop (puncturedNbhd X r) ⟶ SSet.toTop.obj (Sk X (r + 1)) :=
  SpineTask18.subInc (puncturedNbhd X r)

theorem skToVMap_vIncY : skToVMap X r ≫ vIncY X r = SSet.toTop.map (skInc X r) := by
  refine ConcreteCategory.hom_ext _ _ fun x => ?_
  rfl

theorem square_AV :
    TopCat.toSSet.map (SSet.toTop.map (skInc X r)) ≫ 𝟙 _
      = TopCat.toSSet.map (skToVMap X r) ≫ TopCat.toSSet.map (vIncY X r) := by
  rw [Category.comp_id, ← TopCat.toSSet.map_comp, skToVMap_vIncY]

/-- **The comparison of pairs `(Y, A) ⟶ (Y, V)`.** -/
def pairAV : relChainCx (TopCat.toSSet.map (SSet.toTop.map (skInc X r)))
    ⟶ relChainCx (TopCat.toSSet.map (vIncY X r)) :=
  relChainCxMap (TopCat.toSSet.map (SSet.toTop.map (skInc X r)))
    (TopCat.toSSet.map (vIncY X r)) (TopCat.toSSet.map (skToVMap X r)) (𝟙 _) (square_AV X r)

/-- **WP5(1).  `H_q^{sing}(Y, A) ≅ H_q^{sing}(Y, V)`.** -/
theorem isIso_homologyMap_pairAV (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (pairAV X r) q) :=
  isIso_homologyMap_relChainCxMap _ _ _ _ (square_AV X r)
    (toSSet_map_injective _ (skInc_injective X r))
    (toSSet_map_injective _ (SpineTask18.subInc_injective _))
    (isIso_homologyMap_skToV X r) (isIso_homologyMap_id _) q

/-- `H_q^{sing}(Y, A) ≅ H_q^{sing}(Y, V)`, as an isomorphism. -/
def pairAVIso (q : ℕ) :
    (relChainCx (TopCat.toSSet.map (SSet.toTop.map (skInc X r)))).homology q
      ≅ (relChainCx (TopCat.toSSet.map (vIncY X r))).homology q :=
  haveI := isIso_homologyMap_pairAV X r q
  asIso (HomologicalComplex.homologyMap (pairAV X r) q)

/-! ## Excision -/

/-- **WP5(2).  Excision at the excisive pair `(U, V)`.**
`H_q^{sing}(U, U ∩ V) ≅ H_q^{sing}(Y, V)`. -/
def excisionIsoCells (q : ℕ) :
    (relSingChainCx (SpineTask18.incInterU (openCells X r) (puncturedNbhd X r))).homology q
      ≅ (relSingChainCx (SpineTask18.subInc (puncturedNbhd X r))).homology q :=
  SpineTask18.excisionIso (openCells X r) (puncturedNbhd X r) (isOpen_openCells X r)
    (isOpen_puncturedNbhd X r) (openCells_union_puncturedNbhd X r) q

/-- **WP5(3).  The excision comparison for the attached cell family.**
`H_q^{sing}(U, U ∩ V) ≅ H_q^{sing}(Y, A)`, where `U` is the union of the open cells. -/
def cellPairIso (q : ℕ) :
    (relSingChainCx (SpineTask18.incInterU (openCells X r) (puncturedNbhd X r))).homology q
      ≅ (relChainCx (TopCat.toSSet.map (SSet.toTop.map (skInc X r)))).homology q :=
  (excisionIsoCells X r q).trans (pairAVIso X r q).symm

end Skeleton

end SpineTask23
