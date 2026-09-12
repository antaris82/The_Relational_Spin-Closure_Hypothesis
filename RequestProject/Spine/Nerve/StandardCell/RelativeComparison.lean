import RequestProject.Spine.AlgebraicTopology.NormalizationNaturality
import RequestProject.Spine.Nerve.StandardCell.CanonicalGenerator

/-!
# Task 21 : the single standard-cell relative comparison is an isomorphism

This module proves that the **frozen** relative comparison of Task 20,

`SpineTask20.cellRelJ r : C_*^{simp}(Δ[r],∂Δ[r];ℤ₂) ⟶ C_*^{sing}(|Δ[r]|,|∂Δ[r]|;ℤ₂)`,

induced by the unit `η` of the realization/singular adjunction, induces an **isomorphism on
homology in every degree**.

The two inputs are:

* the target side, Task 19 (blocker B1): `standardCellPairAcyclic` (vanishing away from `r`)
  and `isLine_relHomology_top` / `stdCellTopClass` (one-dimensionality in degree `r`);
* the generator side, Task 20: `homologyMap_cellRelJ_top`, `stdCellGenerator_ne_zero`,
  `stdCellGenerator_eq_stdCellTopClass`.

The source side — the *simplicial* relative homology of `(Δ[r],∂Δ[r])` — was **not** available
in the project, so it is computed here, directly on the chain level, from the Task-13
normalization data (`proj = P∞`, `normHtpy`) plus the naturality of the homotopy supplied by
`Task21Normalization`:

* `single_mem_degen_of_surjective` — in a degree `q ≠ r` every *surjective* simplex of `Δ[r]` is
  degenerate, and every non-surjective simplex lies in `∂Δ[r]`; hence
* `proj_mem_range` — `P∞` lands in the chains of the boundary in every degree `q ≠ r`, so the
  induced projector on the relative complex is zero, and the normalization homotopy exhibits
  every relative cycle as a relative boundary:
* `isZero_simpRel_homology` — `H_q^{simp}(Δ[r],∂Δ[r];ℤ₂) = 0` for `q ≠ r`;
* `exists_smul_relTop` — in degree `r` the relative chain module is spanned by the class of the
  identity `r`-simplex, so `H_r^{simp}(Δ[r],∂Δ[r];ℤ₂)` is spanned by `e_r`.

The endpoint is `isIso_homologyMap_cellRelJ` (all degrees), packaged also as
`quasiIso_cellRelJ`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet NerveGeom SpineTask13
  SpineTask14 SpineTask19 SpineTask20

universe u

namespace SpineTask21

/-! ## The simplicial standard cell pair -/

/-- The boundary inclusion `∂Δ[r] ⟶ Δ[r]` of simplicial sets: the source of the frozen
comparison `cellRelJ r`. -/
abbrev bdIncl (r : ℕ) :
    ((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ (Δ[r] : SSet.{u}) :=
  (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι

/-- The relative **simplicial** chain complex `C_*(Δ[r],∂Δ[r];ℤ₂)`. -/
abbrev simpRel (r : ℕ) : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ := relChainCx (bdIncl.{u} r)

/-- The simplicial top generator: the class of the identity `r`-simplex. -/
abbrev relTopChain (r : ℕ) : (simpRel.{u} r).X r :=
  Submodule.Quotient.mk (Finsupp.single (topSimp.{u} r) (1 : ZMod 2))

/-- The relative simplicial top class `e_r`. -/
def simpTopClass (r : ℕ) : (simpRel.{u} r).homology r :=
  hcls (relTopChain.{u} r) (simplicialTop_mem_Zc.{u} r)

/-! ## Chains carried by the boundary -/

/-- A non-surjective simplex of `Δ[r]` spans a chain coming from `∂Δ[r]`. -/
theorem single_mem_range_of_not_surjective (r q : ℕ) (s : (Δ[r] : SSet.{u}).obj (op ⦋q⦌))
    (hs : ¬ Function.Surjective (stdSimplex.asOrderHom s)) (c : ZMod 2) :
    Finsupp.single s c ∈ LinearMap.range (sSetChainMap (bdIncl.{u} r) q) :=
  ⟨Finsupp.single ⟨s, hs⟩ c, by rw [sSetChainMap_single]; rfl⟩

/-- A surjective simplex of `Δ[r]` in a degree `q ≠ r` is degenerate. -/
theorem single_mem_degen_of_surjective (r : ℕ) : ∀ (q : ℕ), q ≠ r →
    ∀ (s : (Δ[r] : SSet.{u}).obj (op ⦋q⦌)),
      Function.Surjective (stdSimplex.asOrderHom s) → ∀ (c : ZMod 2),
      Finsupp.single s c ∈ degenSubmodule (Δ[r] : SSet.{u}) q := by
  rintro (_ | m) hqr s hs c
  · have h1 := Fintype.card_le_of_surjective _ hs
    simp only [Fintype.card_fin, SimplexCategory.len_mk] at h1
    exact absurd (by omega : 0 = r) hqr
  · have hni : ¬ Function.Injective (stdSimplex.objEquiv s).toOrderHom := by
      intro hinj
      have h1 := Fintype.card_le_of_surjective _ hs
      have h2 := Fintype.card_le_of_injective _ hinj
      simp only [Fintype.card_fin, SimplexCategory.len_mk] at h1 h2
      exact hqr (by omega)
    obtain ⟨i, θ', hθ⟩ := SimplexCategory.eq_σ_comp_of_not_injective _ hni
    have hs' : s = (Δ[r] : SSet.{u}).σ i (stdSimplex.objEquiv.symm θ') := by
      rw [SimplicialObject.σ, stdSimplex.map_apply, Equiv.apply_symm_apply]
      simp only [Quiver.Hom.unop_op]
      rw [← hθ, Equiv.symm_apply_apply]
    rw [hs']
    exact single_degen_mem i _ c

/-- Naturality of the Dold–Kan projector, in the element form used below. -/
theorem proj_natural {S T : SSet.{u}} (φ : S ⟶ T) (q : ℕ) (x : SSetChain S q) :
    proj T q (sSetChainMap φ q x) = sSetChainMap φ q (proj S q x) := by
  have h := congrFun (congrArg DFunLike.coe (normInc_natural φ q)) (Submodule.Quotient.mk x)
  simpa using h

/-- **The key source-side vanishing.**  Away from degree `r` the Dold–Kan projector of `Δ[r]`
lands in the chains carried by the boundary. -/
theorem proj_mem_range (r q : ℕ) (hqr : q ≠ r) (x : SSetChain (Δ[r] : SSet.{u}) q) :
    proj (Δ[r] : SSet.{u}) q x ∈ LinearMap.range (sSetChainMap (bdIncl.{u} r) q) := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | single s c =>
      by_cases hs : Function.Surjective (stdSimplex.asOrderHom s)
      · rw [proj_degen_zero _ _ (single_mem_degen_of_surjective r q hqr s hs c)]
        exact Submodule.zero_mem _
      · obtain ⟨y, hy⟩ := single_mem_range_of_not_surjective r q s hs c
        exact ⟨proj _ q y, by rw [← proj_natural, hy]⟩

/-! ## Source-side homology away from the top degree -/

/-- **The source-side calculation, non-top degrees.**
`H_q^{simp}(Δ[r],∂Δ[r];ℤ₂) = 0` for `q ≠ r`. -/
theorem isZero_simpRel_homology (r q : ℕ) (hqr : q ≠ r) :
    IsZero ((simpRel.{u} r).homology q) := by
  refine ModuleCat.isZero_iff_subsingleton.2 (subsingleton_of_forall_eq 0 fun t => ?_)
  obtain ⟨z, hz, rfl⟩ := hcls_surjective t
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [hcls_eq_zero_iff]
  refine ⟨Submodule.Quotient.mk (normHtpy (Δ[r] : SSet.{u}) q x), ?_⟩
  rw [relChainCx_d]
  show Submodule.Quotient.mk
    (sSetBoundary (Δ[r] : SSet.{u}) q (normHtpy (Δ[r] : SSet.{u}) q x)) = _
  refine (Submodule.Quotient.eq _).2 ?_
  match q with
  | 0 =>
      have h := congrFun (congrArg DFunLike.coe (normHtpy_zero (Δ[r] : SSet.{u}))) x
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply] at h
      rw [h]
      obtain ⟨y, hy⟩ := proj_mem_range r 0 hqr x
      refine ⟨y, ?_⟩
      rw [hy]
      abel
  | (m + 1) =>
      have h := congrFun (congrArg DFunLike.coe (normHtpy_succ (Δ[r] : SSet.{u}) m)) x
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply] at h
      -- `hz` says the boundary of `x` is carried by `∂Δ[r]`
      have hbd : sSetBoundary (Δ[r] : SSet.{u}) m x
          ∈ LinearMap.range (sSetChainMap (bdIncl.{u} r) m) := by
        have hz' : relBoundary (bdIncl.{u} r) m (Submodule.Quotient.mk x) = 0 := by
          have := hz
          rw [mem_Zc_succ, relChainCx_d] at this
          exact this
        rw [relBoundary_mk] at hz'
        exact (Submodule.Quotient.mk_eq_zero _).1 hz'
      obtain ⟨w, hw⟩ := hbd
      obtain ⟨y, hy⟩ := proj_mem_range r (m + 1) hqr x
      refine ⟨y + normHtpy _ m w, ?_⟩
      have hhw : normHtpy (Δ[r] : SSet.{u}) m (sSetBoundary (Δ[r] : SSet.{u}) m x)
          = sSetChainMap (bdIncl.{u} r) (m + 1) (normHtpy _ m w) := by
        rw [← hw, normHtpy_natural]
      have key : sSetBoundary (Δ[r] : SSet.{u}) (m + 1) (normHtpy (Δ[r] : SSet.{u}) (m + 1) x)
          = x + (proj (Δ[r] : SSet.{u}) (m + 1) x
            + normHtpy (Δ[r] : SSet.{u}) m (sSetBoundary (Δ[r] : SSet.{u}) m x)) :=
        calc sSetBoundary (Δ[r] : SSet.{u}) (m + 1) (normHtpy (Δ[r] : SSet.{u}) (m + 1) x)
            = sSetBoundary (Δ[r] : SSet.{u}) (m + 1) (normHtpy (Δ[r] : SSet.{u}) (m + 1) x)
              + (normHtpy (Δ[r] : SSet.{u}) m (sSetBoundary (Δ[r] : SSet.{u}) m x)
                + normHtpy (Δ[r] : SSet.{u}) m (sSetBoundary (Δ[r] : SSet.{u}) m x)) := by
              rw [z2_add_self_gen, add_zero]
          _ = (sSetBoundary (Δ[r] : SSet.{u}) (m + 1) (normHtpy (Δ[r] : SSet.{u}) (m + 1) x)
                + normHtpy (Δ[r] : SSet.{u}) m (sSetBoundary (Δ[r] : SSet.{u}) m x))
              + normHtpy (Δ[r] : SSet.{u}) m (sSetBoundary (Δ[r] : SSet.{u}) m x) := by abel
          _ = (x + proj (Δ[r] : SSet.{u}) (m + 1) x)
              + normHtpy (Δ[r] : SSet.{u}) m (sSetBoundary (Δ[r] : SSet.{u}) m x) := by rw [h]
          _ = _ := by abel
      rw [map_add, hy, ← hhw, key]
      abel

/-! ## Source-side degree `r` : the relative module is spanned by the top simplex -/

/-- In degree `r` every relative simplicial chain of `(Δ[r],∂Δ[r])` is a multiple of the class
of the identity `r`-simplex. -/
theorem exists_smul_relTop (r : ℕ) (x : SSetChain (Δ[r] : SSet.{u}) r) :
    ∃ c : ZMod 2, (Submodule.Quotient.mk x : RelChainMod (bdIncl.{u} r) r)
      = c • relTopChain.{u} r := by
  induction x using Finsupp.induction_linear with
  | zero => exact ⟨0, by rw [zero_smul]; rfl⟩
  | add f g hf hg =>
      obtain ⟨a, ha⟩ := hf
      obtain ⟨b, hb⟩ := hg
      refine ⟨a + b, ?_⟩
      rw [add_smul, ← ha, ← hb]
      rfl
  | single s c =>
      by_cases hs : Function.Surjective (stdSimplex.asOrderHom s)
      · have hepi : Epi (stdSimplex.objEquiv s) := by
          rw [SimplexCategory.epi_iff_surjective]
          exact hs
        have hid : s = topSimp.{u} r :=
          stdSimplex.objEquiv.injective
            ((SimplexCategory.eq_id_of_epi (stdSimplex.objEquiv s)).trans rfl)
        refine ⟨c, ?_⟩
        rw [hid, ← Submodule.Quotient.mk_smul]
        refine congrArg _ ?_
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      · exact ⟨0, by
          rw [zero_smul]
          exact (Submodule.Quotient.mk_eq_zero _).2
            (single_mem_range_of_not_surjective r r s hs c)⟩

/-- Every class in `H_r^{simp}(Δ[r],∂Δ[r];ℤ₂)` is a multiple of `e_r`. -/
theorem exists_smul_simpTopClass (r : ℕ) (t : (simpRel.{u} r).homology r) :
    ∃ c : ZMod 2, t = c • simpTopClass.{u} r := by
  obtain ⟨z, hz, rfl⟩ := hcls_surjective t
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨c, hc⟩ := exists_smul_relTop.{u} r x
  refine ⟨c, ?_⟩
  rw [simpTopClass, ← hcls_smul c (relTopChain.{u} r) (simplicialTop_mem_Zc.{u} r)]
  exact hcls_congr _ _ hc

/-! ## The comparison in the top degree -/

/-- The frozen comparison sends the simplicial top class to the canonical singular
generator. -/
theorem homologyMap_cellRelJ_simpTopClass (r : ℕ) :
    (HomologicalComplex.homologyMap (cellRelJ.{u} r) r).hom (simpTopClass.{u} r)
      = stdCellGenerator.{u} r :=
  homologyMap_cellRelJ_top.{u} r

/-- **Top degree.**  The comparison is bijective in degree `r`. -/
theorem bijective_homologyMap_cellRelJ_top (r : ℕ) :
    Function.Bijective ((HomologicalComplex.homologyMap (cellRelJ.{u} r) r).hom) := by
  constructor
  · -- injectivity
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨c, rfl⟩ := exists_smul_simpTopClass.{u} r t
    rw [map_smul, homologyMap_cellRelJ_simpTopClass] at ht
    have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hcases c with rfl | rfl
    · rw [zero_smul]
    · rw [one_smul] at ht
      exact absurd ht (stdCellGenerator_ne_zero.{u} r)
  · -- surjectivity
    intro y
    rcases eq_zero_or_eq_stdCellTopClass.{u} r y with rfl | rfl
    · exact ⟨0, map_zero _⟩
    · exact ⟨simpTopClass.{u} r, by
        rw [homologyMap_cellRelJ_simpTopClass, stdCellGenerator_eq_stdCellTopClass]⟩

/-! ## The principal endpoint -/

/-- **The principal theorem of Task 21.**  For every `r` and every degree `q` the frozen
single-cell relative comparison

`H_q^{simp}(Δ[r],∂Δ[r];ℤ₂) ⟶ H_q^{sing}(|Δ[r]|,|∂Δ[r]|;ℤ₂)`

induced by `J = C_*(η)` is an isomorphism. -/
theorem isIso_homologyMap_cellRelJ (r q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cellRelJ.{u} r) q) := by
  by_cases hqr : q = r
  · subst hqr
    exact (ConcreteCategory.isIso_iff_bijective _).2 (bijective_homologyMap_cellRelJ_top.{u} q)
  · haveI hsrc : Subsingleton ((simpRel.{u} r).homology q) :=
      ModuleCat.isZero_iff_subsingleton.1 (isZero_simpRel_homology.{u} r q hqr)
    haveI htgt : Subsingleton ((relChainCx (stdCellPair.{u} r)).homology q) :=
      ModuleCat.isZero_iff_subsingleton.1 (standardCellPairAcyclic.{u} r q hqr)
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a b _ => Subsingleton.elim a b,
      fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- The single-cell comparison as an isomorphism of homology modules:
`H_q^{simp}(Δ[r],∂Δ[r];ℤ₂) ≅ H_q^{sing}(|Δ[r]|,|∂Δ[r]|;ℤ₂)`, realised by the frozen `J`. -/
def homologyIso_cellRelJ (r q : ℕ) :
    (simpRel.{u} r).homology q ≅ relHomology (stdCellPair.{u} r) q :=
  haveI := isIso_homologyMap_cellRelJ.{u} r q
  asIso (HomologicalComplex.homologyMap (cellRelJ.{u} r) q)

/-- **The source-side calculation, top degree.**  `H_r^{simp}(Δ[r],∂Δ[r];ℤ₂)` is
one-dimensional.  (Transported from the target side through the comparison, which is now known
to be an isomorphism.) -/
theorem isLine_simpRel_homology_top (r : ℕ) : IsLine ((simpRel.{u} r).homology r) :=
  IsLine.of_iso (isLine_relHomology_top.{u} r) (homologyIso_cellRelJ.{u} r r).symm

/-- The simplicial top class is nonzero, so it generates `H_r^{simp}(Δ[r],∂Δ[r];ℤ₂)`. -/
theorem simpTopClass_ne_zero (r : ℕ) : simpTopClass.{u} r ≠ 0 := by
  intro h
  refine stdCellGenerator_ne_zero.{u} r ?_
  rw [← homologyMap_cellRelJ_simpTopClass, h, map_zero]

/-- **Optional packaging.**  The frozen single-cell relative comparison is a
quasi-isomorphism. -/
instance quasiIso_cellRelJ (r : ℕ) : QuasiIso (cellRelJ.{u} r) where
  quasiIsoAt q := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact isIso_homologyMap_cellRelJ.{u} r q

end SpineTask21
