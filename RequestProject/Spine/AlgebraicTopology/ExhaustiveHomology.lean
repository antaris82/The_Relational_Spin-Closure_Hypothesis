import RequestProject.Spine.AlgebraicTopology.HomologyElements

/-!
# Homology of an exhausted chain complex

Let `A` and `B` be chain complexes of `R`-modules which are *exhausted* by two `ℕ`-indexed
families of subcomplexes: chain maps `cA.app r : FA.obj r ⟶ A` and `cB.app r : FB.obj r ⟶ B`
which are degreewise injective, compatible with the transition maps of the families, and such
that every chain of `A` (resp. `B`) comes from some stage.  Let `J : FA ⟶ FB` be a map of
families and `JG : A ⟶ B` a map compatible with it.

**If `J.app r` is a homology isomorphism at every stage `r`, then so is `JG`.**

This is the elementary "compact support" assembly: no colimit of chain complexes is formed and
no exactness of filtered colimits is invoked.  Only three chases are needed:

* `exists_stage_cycle` — a cycle whose underlying chain comes from a stage comes from a cycle of
  that stage, with the same homology class;
* `exists_stage_homology_class` — every homology class of an exhausted complex comes from a
  finite stage;
* `exists_later_stage_zero` — a class of a finite stage which dies globally already dies at some
  later finite stage.

The main theorem `isIso_homologyMap_of_exhaustive` combines them.  The two families are
unrelated except through `J`; in the application `A` is the simplicial chain complex of a
simplicial set `K`, `B` the singular chain complex of `|K|`, and the two families are the
skeleta of `K` and their realizations.
-/

noncomputable section

open CategoryTheory Limits

universe u v

namespace SpineExhaustion

variable {R : Type v} [Ring R]

section Elementary

variable {X Y Z : ChainComplex (ModuleCat.{u} R) ℕ}

/-- Equal maps of modules act equally on elements. -/
theorem mcCongr {M N : ModuleCat.{u} R} {f g : M ⟶ N} (h : f = g) (x : M) :
    f.hom x = g.hom x := by rw [h]

/-- A composite of maps of modules acts as the composite of the actions. -/
theorem mcComp {M N P : ModuleCat.{u} R} (f : M ⟶ N) (g : N ⟶ P) (x : M) :
    (f ≫ g).hom x = g.hom (f.hom x) := rfl

/-- Equal chain maps act equally on chains. -/
theorem hom_f_apply {f g : X ⟶ Y} (h : f = g) (i : ℕ) (x : X.X i) :
    (f.f i).hom x = (g.f i).hom x := by rw [h]

/-- A composite of chain maps acts as the composite of the actions. -/
theorem comp_f_apply (f : X ⟶ Y) (g : Y ⟶ Z) (i : ℕ) (x : X.X i) :
    ((f ≫ g).f i).hom x = (g.f i).hom ((f.f i).hom x) := rfl

end Elementary

section Stage

variable {X Y : ChainComplex (ModuleCat.{u} R) ℕ}

/-- If a chain map is degreewise injective and the underlying chain of a cycle of the target
comes from the source, then it comes from a cycle of the source, and the homology classes
correspond. -/
theorem exists_stage_cycle (c : X ⟶ Y) (hinj : ∀ i, Function.Injective ((c.f i).hom)) (q : ℕ)
    (z : Y.cycles q) (w : X.X q) (hw : ((c.f q).hom) w = (Y.iCycles q).hom z) :
    ∃ v : X.cycles q, (X.iCycles q).hom v = w ∧
      (HomologicalComplex.homologyMap c q).hom ((X.homologyπ q).hom v)
        = (Y.homologyπ q).hom z := by
  have hzero : (Y.dFrom q).hom ((Y.iCycles q).hom z) = 0 :=
    mcCongr (ShortComplex.iCycles_g (Y.sc q)) z
  have hcomm := mcCongr (c.comm_from q) w
  simp only [mcComp] at hcomm
  have hdX : (X.dFrom q).hom w = 0 := by
    apply hinj ((ComplexShape.down ℕ).next q)
    rw [map_zero]
    rw [← hcomm, hw, hzero]
  obtain ⟨v, hv⟩ := SpineChainElements.exists_cycle q w hdX
  refine ⟨v, hv, ?_⟩
  have hcy : (HomologicalComplex.cyclesMap c q).hom v = z := by
    apply SpineChainElements.iCycles_injective (K := Y) q
    have h := mcCongr (HomologicalComplex.cyclesMap_i c q) v
    simp only [mcComp] at h
    rw [h, hv, hw]
  have hnat := mcCongr (HomologicalComplex.homologyπ_naturality c q) v
  simp only [mcComp] at hnat
  rw [hnat, hcy]

end Stage

section Main

variable {FA FB : ℕ ⥤ ChainComplex (ModuleCat.{u} R) ℕ}
  {A B : ChainComplex (ModuleCat.{u} R) ℕ}

/-- Compatibility of a cocone with the transition maps of an `ℕ`-indexed family. -/
theorem cocone_comp {F : ℕ ⥤ ChainComplex (ModuleCat.{u} R) ℕ}
    {C : ChainComplex (ModuleCat.{u} R) ℕ} (c : F ⟶ (Functor.const ℕ).obj C) {r s : ℕ}
    (h : r ≤ s) : F.map (homOfLE h) ≫ c.app s = c.app r := by
  have h2 := c.naturality (homOfLE h)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h2
  exact h2

/-- A homology class of a complex exhausted by a family of degreewise injective subcomplexes
comes from a finite stage. -/
theorem exists_stage_homology_class (cB : FB ⟶ (Functor.const ℕ).obj B)
    (hinj : ∀ r i, Function.Injective (((cB.app r).f i).hom))
    (hexh : ∀ (i : ℕ) (x : B.X i), ∃ (r : ℕ) (y : (FB.obj r).X i), (((cB.app r).f i).hom) y = x)
    (q : ℕ) (y : B.homology q) :
    ∃ (r : ℕ) (u : (FB.obj r).homology q),
      (HomologicalComplex.homologyMap (cB.app r) q).hom u = y := by
  obtain ⟨z, hz⟩ := SpineChainElements.homologyπ_surjective (K := B) q y
  obtain ⟨r, w, hw⟩ := hexh q ((B.iCycles q).hom z)
  obtain ⟨v, _, hv⟩ := exists_stage_cycle (cB.app r) (hinj r) q z w hw
  exact ⟨r, ((FB.obj r).homologyπ q).hom v, hv.trans hz⟩

/-- A homology class of a finite stage which dies in the exhausted complex already dies at some
later finite stage. -/
theorem exists_later_stage_zero (cB : FB ⟶ (Functor.const ℕ).obj B)
    (hinj : ∀ r i, Function.Injective (((cB.app r).f i).hom))
    (hexh : ∀ (i : ℕ) (x : B.X i), ∃ (r : ℕ) (y : (FB.obj r).X i), (((cB.app r).f i).hom) y = x)
    (q r : ℕ) (u : (FB.obj r).homology q)
    (hu : (HomologicalComplex.homologyMap (cB.app r) q).hom u = 0) :
    ∃ (s : ℕ) (h : r ≤ s),
      (HomologicalComplex.homologyMap (FB.map (homOfLE h)) q).hom u = 0 := by
  obtain ⟨z, hz⟩ := SpineChainElements.homologyπ_surjective (K := FB.obj r) q u
  have hzB : (B.homologyπ q).hom ((HomologicalComplex.cyclesMap (cB.app r) q).hom z) = 0 := by
    have h := mcCongr
      (HomologicalComplex.homologyπ_naturality (cB.app r) q) z
    simp only [mcComp, Functor.const_obj_obj] at h
    have h2 : (HomologicalComplex.homologyMap (cB.app r) q).hom
        (((FB.obj r).homologyπ q).hom z) = 0 := by rw [hz]; exact hu
    exact h.symm.trans h2
  obtain ⟨b, hb⟩ := (SpineChainElements.homologyπ_eq_zero_iff (K := B) q _).1 hzB
  obtain ⟨s₀, b₀, hb₀⟩ := hexh (q + 1) b
  refine ⟨max r s₀, le_max_left _ _, ?_⟩
  set s := max r s₀ with hs
  set t : FB.obj r ⟶ FB.obj s := FB.map (homOfLE (le_max_left r s₀)) with ht
  set b₁ : (FB.obj s).X (q + 1) :=
    ((FB.map (homOfLE (le_max_right r s₀))).f (q + 1)).hom b₀ with hb₁
  have hb₁B : (((cB.app s).f (q + 1)).hom) b₁ = b := by
    have h := hom_f_apply (cocone_comp cB (le_max_right r s₀)) (q + 1) b₀
    rw [comp_f_apply] at h
    rw [hb₁, h]
    exact hb₀
  have hzs : ((FB.obj s).homologyπ q).hom
      ((HomologicalComplex.cyclesMap t q).hom z) = 0 := by
    refine SpineChainElements.homologyπ_eq_zero q _ b₁ ?_
    apply hinj s q
    have hleft : (((cB.app s).f q).hom) (((FB.obj s).d (q + 1) q).hom b₁)
        = (B.d (q + 1) q).hom b := by
      have h := mcCongr ((cB.app s).comm (q + 1) q) b₁
      simp only [mcComp, Functor.const_obj_obj] at h
      have h2 : (B.d (q + 1) q).hom ((((cB.app s).f (q + 1)).hom) b₁)
          = (B.d (q + 1) q).hom b := by rw [hb₁B]
      exact h.symm.trans h2
    have e1 : (((cB.app s).f q).hom)
        (((FB.obj s).iCycles q).hom ((HomologicalComplex.cyclesMap t q).hom z))
        = (B.iCycles q).hom
          ((HomologicalComplex.cyclesMap (cB.app s) q).hom
            ((HomologicalComplex.cyclesMap t q).hom z)) := by
      have h := mcCongr (HomologicalComplex.cyclesMap_i (cB.app s) q)
        ((HomologicalComplex.cyclesMap t q).hom z)
      simp only [mcComp, Functor.const_obj_obj] at h
      exact h.symm
    have e2 : (HomologicalComplex.cyclesMap (cB.app s) q).hom
        ((HomologicalComplex.cyclesMap t q).hom z)
        = (HomologicalComplex.cyclesMap (cB.app r) q).hom z := by
      have h2 : HomologicalComplex.cyclesMap t q ≫ HomologicalComplex.cyclesMap (cB.app s) q
          = HomologicalComplex.cyclesMap (cB.app r) q := by
        rw [← HomologicalComplex.cyclesMap_comp, ht, cocone_comp cB]
      have h := mcCongr h2 z
      simp only [mcComp, Functor.const_obj_obj] at h
      exact h
    calc (((cB.app s).f q).hom) (((FB.obj s).d (q + 1) q).hom b₁)
        = (B.d (q + 1) q).hom b := hleft
      _ = (B.iCycles q).hom ((HomologicalComplex.cyclesMap (cB.app r) q).hom z) := hb
      _ = (B.iCycles q).hom ((HomologicalComplex.cyclesMap (cB.app s) q).hom
            ((HomologicalComplex.cyclesMap t q).hom z)) := congrArg _ e2.symm
      _ = (((cB.app s).f q).hom) (((FB.obj s).iCycles q).hom
            ((HomologicalComplex.cyclesMap t q).hom z)) := e1.symm
  have hnat := mcCongr
    (HomologicalComplex.homologyπ_naturality t q) z
  simp only [mcComp] at hnat
  rw [← hz, hnat, hzs]

variable (cA : FA ⟶ (Functor.const ℕ).obj A) (cB : FB ⟶ (Functor.const ℕ).obj B)
  (J : FA ⟶ FB) (JG : A ⟶ B)

/-- **The assembly theorem.**  If two exhausted chain complexes are compared by a map of
exhausting families which is a homology isomorphism at every finite stage, then the induced map
of the exhausted complexes is a homology isomorphism. -/
theorem isIso_homologyMap_of_exhaustive
    (hsq : ∀ r, J.app r ≫ cB.app r = cA.app r ≫ JG)
    (hAinj : ∀ r i, Function.Injective (((cA.app r).f i).hom))
    (hBinj : ∀ r i, Function.Injective (((cB.app r).f i).hom))
    (hAexh : ∀ (i : ℕ) (x : A.X i), ∃ (r : ℕ) (y : (FA.obj r).X i), (((cA.app r).f i).hom) y = x)
    (hBexh : ∀ (i : ℕ) (x : B.X i), ∃ (r : ℕ) (y : (FB.obj r).X i), (((cB.app r).f i).hom) y = x)
    (hstage : ∀ r q, IsIso (HomologicalComplex.homologyMap (J.app r) q)) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap JG q) := by
  have hsq' : ∀ r, HomologicalComplex.homologyMap (J.app r) q
      ≫ HomologicalComplex.homologyMap (cB.app r) q
      = HomologicalComplex.homologyMap (cA.app r) q
        ≫ HomologicalComplex.homologyMap JG q := by
    intro r
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hsq r]
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap JG q).hom := by
    intro y
    obtain ⟨r, u, hu⟩ := exists_stage_homology_class cB hBinj hBexh q y
    haveI := hstage r q
    obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective
      (HomologicalComplex.homologyMap (J.app r) q)).1 inferInstance u
    refine ⟨(HomologicalComplex.homologyMap (cA.app r) q).hom a, ?_⟩
    have h := mcCongr (hsq' r) a
    simp only [mcComp, Functor.const_obj_obj] at h
    have h2 : (HomologicalComplex.homologyMap (cB.app r) q).hom
        ((HomologicalComplex.homologyMap (J.app r) q).hom a) = y := by rw [ha]; exact hu
    exact h.symm.trans h2
  have hinj : Function.Injective (HomologicalComplex.homologyMap JG q).hom := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, hz⟩ := SpineChainElements.homologyπ_surjective (K := A) q x
    obtain ⟨r, w, hw⟩ := hAexh q ((A.iCycles q).hom z)
    obtain ⟨v, _, hv⟩ := exists_stage_cycle (cA.app r) (hAinj r) q z w hw
    set a : (FA.obj r).homology q := ((FA.obj r).homologyπ q).hom v with ha
    have hax : (HomologicalComplex.homologyMap (cA.app r) q).hom a = x := hv.trans hz
    have hzero : (HomologicalComplex.homologyMap (cB.app r) q).hom
        ((HomologicalComplex.homologyMap (J.app r) q).hom a) = 0 := by
      have h := mcCongr (hsq' r) a
      simp only [mcComp, Functor.const_obj_obj] at h
      have h2 : (HomologicalComplex.homologyMap JG q).hom
          ((HomologicalComplex.homologyMap (cA.app r) q).hom a) = 0 := by rw [hax]; exact hx
      exact h.trans h2
    obtain ⟨s, hrs, hs⟩ := exists_later_stage_zero cB hBinj hBexh q r _ hzero
    haveI := hstage s q
    have hJnat : HomologicalComplex.homologyMap (FA.map (homOfLE hrs)) q
        ≫ HomologicalComplex.homologyMap (J.app s) q
        = HomologicalComplex.homologyMap (J.app r) q
          ≫ HomologicalComplex.homologyMap (FB.map (homOfLE hrs)) q := by
      rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        J.naturality (homOfLE hrs)]
    have hstep : (HomologicalComplex.homologyMap (J.app s) q).hom
        ((HomologicalComplex.homologyMap (FA.map (homOfLE hrs)) q).hom a) = 0 := by
      have h := mcCongr hJnat a
      simp only [mcComp] at h
      rw [h, hs]
    have hzero' : (HomologicalComplex.homologyMap (FA.map (homOfLE hrs)) q).hom a = 0 := by
      have hmono : Function.Injective (HomologicalComplex.homologyMap (J.app s) q).hom :=
        (ModuleCat.mono_iff_injective _).1 inferInstance
      apply hmono
      rw [map_zero]
      exact hstep
    have hAcomp : HomologicalComplex.homologyMap (FA.map (homOfLE hrs)) q
        ≫ HomologicalComplex.homologyMap (cA.app s) q
        = HomologicalComplex.homologyMap (cA.app r) q := by
      rw [← HomologicalComplex.homologyMap_comp, cocone_comp cA hrs]
    have h := mcCongr hAcomp a
    simp only [mcComp, Functor.const_obj_obj] at h
    have h2 : (HomologicalComplex.homologyMap (cA.app s) q).hom
        ((HomologicalComplex.homologyMap (FA.map (homOfLE hrs)) q).hom a) = 0 := by
      rw [hzero', map_zero]
    exact hax.symm.trans (h.symm.trans h2)
  haveI : Mono (HomologicalComplex.homologyMap JG q) := (ModuleCat.mono_iff_injective _).2 hinj
  haveI : Epi (HomologicalComplex.homologyMap JG q) := (ModuleCat.epi_iff_surjective _).2 hsurj
  exact isIso_of_mono_of_epi _

end Main

end SpineExhaustion
