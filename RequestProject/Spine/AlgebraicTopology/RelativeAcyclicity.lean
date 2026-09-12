import RequestProject.Spine.AlgebraicTopology.RelativeLES

/-!
# Acyclicity of a relative chain complex along a quasi-isomorphism

Generic simplicial homological algebra: if `f : S ⟶ T` is degreewise injective and induces an
isomorphism on the homology of the simplicial chain complexes, then the relative complex
`C_*(T,S) = C_*(T)/im C_*(S)` is acyclic.  The proof is the long exact sequence of the pair,
compared with the (degreewise zero) relative complex of the identity of `S`.

Nothing here mentions a nerve, a cover, a skeleton, a cell or a topological space; the
declaration keeps its historical `SpineTask23` namespace so that no downstream statement had
to be edited.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial SSet NerveGeom SpineTask14

universe u

namespace SpineTask23

/-- If the chain map induced by a degreewise injective `f : S ⟶ T` is a quasi-isomorphism, the
relative chain complex `C_*(T,S)` is acyclic. -/
theorem isZero_relHomology_of_quasiIso {S T : SSet.{u}} (f : S ⟶ T)
    (hf : ∀ n, Function.Injective (f.app n))
    (hq : ∀ q, IsIso (HomologicalComplex.homologyMap (sSetChainComplexFunctor.map f) q))
    (q : ℕ) : IsZero ((relChainCx f).homology q) := by
  -- the morphism of short exact sequences `(C(S) → C(S) → C(S,S)) ⟶ (C(S) → C(T) → C(T,S))`
  have hsq : (𝟙 S) ≫ f = (𝟙 S) ≫ f := rfl
  set φ : relSC (𝟙 S) ⟶ relSC f := relSCMap (𝟙 S) f (𝟙 S) f hsq with hφ
  have hid : ∀ n, Function.Injective (NatTrans.app (𝟙 S) n) := fun n x y h => h
  have hse₁ : (relSC (𝟙 S)).ShortExact := relSC_shortExact _ hid
  have hse₂ : (relSC f).ShortExact := relSC_shortExact _ hf
  have hτ₁ : QuasiIso φ.τ₁ := by
    have : φ.τ₁ = 𝟙 _ := by
      show sSetChainComplexFunctor.map (𝟙 S) = 𝟙 _
      exact sSetChainComplexFunctor.map_id S
    rw [this]
    infer_instance
  have hτ₂ : QuasiIso φ.τ₂ := by
    have hmap : φ.τ₂ = sSetChainComplexFunctor.map f := rfl
    rw [hmap]
    exact ⟨fun i => (quasiIsoAt_iff_isIso_homologyMap _ i).2 (hq i)⟩
  haveI := hτ₁
  haveI := hτ₂
  have hτ₃ : QuasiIso φ.τ₃ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hse₁ hse₂ hτ₁ hτ₂
  -- the source is acyclic because `C_*(S,S)` is degreewise zero
  have hzeroX : IsZero ((relChainCx (𝟙 S)).X q) := by
    have hsub : Subsingleton (RelChainMod (𝟙 S) q) := by
      constructor
      intro a b
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      have hx : ∀ z : SSetChain S q, (Submodule.Quotient.mk z :
          SSetChain S q ⧸ LinearMap.range (sSetChainMap (𝟙 S) q)) = 0 := by
        intro z
        refine (Submodule.Quotient.mk_eq_zero _).2 ⟨z, ?_⟩
        show sSetChainMap (𝟙 S) q z = z
        show Finsupp.mapDomain _ z = z
        exact Finsupp.mapDomain_id
      rw [hx x, hx y]
    exact @ModuleCat.isZero_of_subsingleton _ _ _ hsub
  have hzero : IsZero ((relChainCx (𝟙 S)).homology q) :=
    ShortComplex.isZero_homology_of_isZero_X₂ ((relChainCx (𝟙 S)).sc q) hzeroX
  haveI : IsIso (HomologicalComplex.homologyMap φ.τ₃ q) :=
    (quasiIsoAt_iff_isIso_homologyMap _ q).1 (hτ₃.quasiIsoAt q)
  exact IsZero.of_iso hzero (asIso (HomologicalComplex.homologyMap φ.τ₃ q)).symm
end SpineTask23
