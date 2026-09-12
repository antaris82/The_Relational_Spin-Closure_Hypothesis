import Mathlib
import RequestProject.Spine.E1.SpinDeterminant
import RequestProject.Spine.E1.Shell

/-!
# Task 11, Phase V (completion) : the induced action is onto the intrinsic Lorentz group

`RequestProject/Task11SpinDet.lean` closed the determinant obligation: a spin element
`g ∈ Cl₃(ℝ)` induces an element `spinLorEquiv hg` of the intrinsic Lorentz group `G_L` of
the carrier `𝒮`.  The remaining Phase-V item recorded as `NOT_YET_FORMALIZED` was
**surjectivity**: that *every* element of `G_L` arises this way.  This module closes it.

## The argument

* **boost part.**  For `F ∈ G_L` put `p := F(1_𝒮)`.  Then `N(p) = 1` and `p ∈ ConeS`, so
  `p₀ ≥ 0`, and the paravector square root `β := A(√p)` of §Task11SpinDet satisfies
  `spinLor β (1_𝒮) = p`, since `β · A(1) · reverse β = β·β = A(p)`.
* **rotation part.**  Hence `(spinLorEquiv hβ)⁻¹ ∘ F` fixes `1_𝒮`, and by Task 10's
  stabilizer theorem it is `rotToSpin R` for a rotation `R` of the spatial part.  Every
  such `R` is a product of hyperplane reflections (Cartan–Dieudonné, from Mathlib), and a
  hyperplane reflection in the unit vector `u` is implemented in `Cl₃(ℝ)` by
  `spinLor (ι u) x = (x₀, 2⟪u,x⟫u − x)` — that is, by *minus* the reflection on the spatial
  part.  A product of `k` reflections is therefore implemented up to the sign `(−1)^k`,
  and `det R = (−1)^k = 1` forces `k` to be even, so the sign disappears
  (`SpinCore.exists_spin_of_rot`).
* Multiplying the two factors gives a spin element inducing `F`
  (`SpinCore.spinLor_surjective_onto_GLor`).

Together with `SpinCore.kernel_exactly_pm_one` this exhibits `G_L` as the quotient of the
intrinsic spin group by `{±1}`.
-/

noncomputable section

open CliffordAlgebra
open scoped RealInnerProductSpace

namespace SpinCore

open SpinCore

/-! ## Hyperplane reflections of the spatial part -/

/-- The hyperplane reflection attached to a unit vector of `ℝ³`. -/
def hyperRefl (u : Fin 3 → ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := x - (2 * sip u x) • u
  map_add' x y := by rw [sip_add_right u x y]; module
  map_smul' r x := by
    simp only [sip_smul_right r u x, RingHom.id_apply]; module

theorem hyperRefl_apply (u x : Fin 3 → ℝ) : hyperRefl u x = x - (2 * sip u x) • u := rfl

/-- The composite of the reflections attached to a list of unit vectors. -/
def hyperReflProd : List (Fin 3 → ℝ) → ((Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
  | [] => LinearMap.id
  | u :: l => (hyperRefl u).comp (hyperReflProd l)

@[simp] theorem hyperReflProd_nil : hyperReflProd [] = LinearMap.id := rfl

@[simp] theorem hyperReflProd_cons (u : Fin 3 → ℝ) (l : List (Fin 3 → ℝ)) :
    hyperReflProd (u :: l) = (hyperRefl u).comp (hyperReflProd l) := rfl

theorem det_hyperRefl {u : Fin 3 → ℝ} (hu : sip u u = 1) :
    LinearMap.det (hyperRefl u) = -1 := by
  classical
  have hb := LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 3)) (hyperRefl u)
  rw [← hb]
  have hentry : ∀ i j, (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3))
      (hyperRefl u)) i j = (if i = j then (1 : ℝ) else 0) - 2 * u j * u i := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    simp [hyperRefl_apply, sip, Pi.basisFun_apply]
    fin_cases j <;> fin_cases i <;> simp
  rw [Matrix.det_fin_three]
  simp only [hentry]
  norm_num [Fin.ext_iff]
  simp only [sip] at hu
  linear_combination (-2 : ℝ) * hu

theorem det_hyperReflProd : ∀ {l : List (Fin 3 → ℝ)}, (∀ u ∈ l, sip u u = 1) →
    LinearMap.det (hyperReflProd l) = (-1 : ℝ) ^ l.length
  | [], _ => by simp
  | u :: l, h => by
      have hu : sip u u = 1 := h u (by simp)
      have hl : ∀ w ∈ l, sip w w = 1 := fun w hw => h w (by simp [hw])
      rw [hyperReflProd_cons, LinearMap.det_comp, det_hyperRefl hu, det_hyperReflProd hl]
      simp [pow_succ]

/-! ## Clifford implementation of a reflection -/

theorem iota_mul_iota_swap (u w : Fin 3 → ℝ) :
    ι q3 u * ι q3 w = algebraMap ℝ Cl3 (2 * sip u w) - ι q3 w * ι q3 u := by
  have h := ι_mul_ι_add_swap (Q := q3) u w
  rw [polar_q3] at h
  linear_combination (norm := noncomm_ring) h

/-- A unit vector of `ℝ³`, viewed in `Cl₃(ℝ)`, induces *minus* the hyperplane reflection on
the spatial part of the carrier. -/
theorem spinLor_iota_vec {u : Fin 3 → ℝ} (hu : sip u u = 1) (x : LorentzCarrier) :
    spinLor (ι q3 u) x = (x.1, (2 * sip u x.2) • u - x.2) := by
  refine spinLor_unique ?_
  have husq : ι q3 u * ι q3 u = 1 := by
    rw [clifford_square_convention, hu, map_one]
  show spinToCl (x.1, (2 * sip u x.2) • u - x.2)
      = ι q3 u * spinToCl x * reverse (Q := q3) (ι q3 u)
  rw [reverse_ι, spinToCl_apply, spinToCl_apply, map_sub, map_smul, mul_add, add_mul]
  have hkey : ι q3 u * ι q3 x.2 * ι q3 u = (2 * sip u x.2) • ι q3 u - ι q3 x.2 := by
    rw [iota_mul_iota_swap u x.2, sub_mul, mul_assoc, husq, mul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [hkey, ← Algebra.commutes, mul_assoc, husq, mul_one]

theorem cconj_iota (u : Fin 3 → ℝ) : cconj (ι q3 u) = -ι q3 u := by
  rw [cconj, reverse_ι, involute_ι]

/-- **Versor realization.**  A list of unit vectors of `ℝ³` gives a Clifford element
implementing the corresponding product of reflections, up to the sign `(−1)^length`. -/
theorem exists_versor_of_list : ∀ {l : List (Fin 3 → ℝ)}, (∀ u ∈ l, sip u u = 1) →
    ∃ g : Cl3, g * cconj g = ((-1 : ℝ) ^ l.length) • (1 : Cl3)
      ∧ cconj g * g = ((-1 : ℝ) ^ l.length) • (1 : Cl3)
      ∧ ∀ x : LorentzCarrier, spinLor g x = (x.1, ((-1 : ℝ) ^ l.length) • (hyperReflProd l) x.2)
  | [], _ => by
      refine ⟨1, by simp, by simp, fun x => ?_⟩
      simp only [spinLor_one, List.length_nil, pow_zero, one_smul, hyperReflProd_nil,
        LinearMap.id_coe, id_eq]
  | u :: l, h => by
      have hu : sip u u = 1 := h u (by simp)
      have hl : ∀ w ∈ l, sip w w = 1 := fun w hw => h w (by simp [hw])
      obtain ⟨g, hg1, hg2, hg3⟩ := exists_versor_of_list hl
      have husq : ι q3 u * ι q3 u = 1 := by
        rw [clifford_square_convention, hu, map_one]
      refine ⟨ι q3 u * g, ?_, ?_, ?_⟩
      · rw [cconj_mul, cconj_iota]
        calc ι q3 u * g * (cconj g * -ι q3 u)
            = ι q3 u * (g * cconj g) * -ι q3 u := by noncomm_ring
          _ = ι q3 u * (((-1 : ℝ) ^ l.length) • (1 : Cl3)) * -ι q3 u := by rw [hg1]
          _ = ((-1 : ℝ) ^ (u :: l).length) • (1 : Cl3) := by
              rw [mul_smul_comm, mul_one, smul_mul_assoc, mul_neg, husq]
              simp [pow_succ]
      · rw [cconj_mul, cconj_iota]
        calc cconj g * -ι q3 u * (ι q3 u * g)
            = -(cconj g * (ι q3 u * ι q3 u) * g) := by noncomm_ring
          _ = -(cconj g * g) := by rw [husq, mul_one]
          _ = ((-1 : ℝ) ^ (u :: l).length) • (1 : Cl3) := by
              rw [hg2]
              simp [pow_succ]
      · intro x
        rw [spinLor_mul, hg3 x, spinLor_iota_vec hu]
        refine Prod.ext rfl ?_
        show (2 * sip u (((-1 : ℝ) ^ l.length) • (hyperReflProd l) x.2)) • u
            - ((-1 : ℝ) ^ l.length) • (hyperReflProd l) x.2
          = ((-1 : ℝ) ^ (u :: l).length) • (hyperReflProd (u :: l)) x.2
        rw [sip_smul_right, hyperReflProd_cons]
        show _ = ((-1 : ℝ) ^ (l.length + 1)) • (hyperRefl u ((hyperReflProd l) x.2))
        rw [hyperRefl_apply, pow_succ]
        module

/-! ## From Mathlib's Cartan–Dieudonné theorem to lists of unit vectors -/

/-- The Euclidean model of the spatial part. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The coordinate isomorphism between the Euclidean model and `ℝ³`. -/
def ofE : E3 ≃ₗ[ℝ] (Fin 3 → ℝ) := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)

theorem inner_E (x y : E3) : ⟪x, y⟫ = sip (ofE x) (ofE y) := by
  simp [PiLp.inner_apply, sip, Fin.sum_univ_three, ofE]
  ring

theorem norm_sq_E (v : E3) : ‖v‖ ^ 2 = sip (ofE v) (ofE v) := by
  rw [← real_inner_self_eq_norm_sq, inner_E]

/-- Mathlib's hyperplane reflection of the Euclidean model, attached to a vector. -/
def reflE (v : E3) : E3 ≃ₗᵢ[ℝ] E3 := Submodule.reflection ((ℝ ∙ v)ᗮ)

theorem reflE_apply (v y : E3) : reflE v y = y - ((2 * ⟪v, y⟫) / ‖v‖ ^ 2) • v := by
  show ((ℝ ∙ v)ᗮ.reflection) y = _
  rw [Submodule.reflection_apply, Submodule.starProjection_orthogonal]
  simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply, ContinuousLinearMap.coe_id', id_eq,
    Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, smul_sub, two_smul]
  module

/-- Every finite product of Mathlib hyperplane reflections of the Euclidean model is the
transport of a product of `hyperRefl`'s along a list of unit vectors. -/
theorem reflList_translate : ∀ l : List E3, ∃ l' : List (Fin 3 → ℝ),
    (∀ u ∈ l', sip u u = 1) ∧
    ∀ x : E3, ofE ((List.map reflE l).prod x) = hyperReflProd l' (ofE x)
  | [] => ⟨[], by simp, fun x => by simp⟩
  | v :: l => by
      obtain ⟨l', hl', hpl⟩ := reflList_translate l
      have hstep : ∀ x : E3, ((List.map reflE (v :: l)).prod) x
          = reflE v (((List.map reflE l).prod) x) := by
        intro x
        rw [List.map_cons, List.prod_cons]
        rfl
      by_cases hv : v = 0
      · refine ⟨l', hl', fun x => ?_⟩
        rw [hstep x, reflE_apply, hv]
        simp only [inner_zero_left, mul_zero, norm_zero, smul_zero, sub_zero]
        exact hpl x
      · have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
        refine ⟨(‖v‖⁻¹ • ofE v) :: l', ?_, fun x => ?_⟩
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu'
          · rw [sip_smul_left, sip_smul_right, ← norm_sq_E]
            field_simp
          · exact hl' u hu'
        · rw [hstep x, reflE_apply, map_sub, map_smul, hyperReflProd_cons,
            LinearMap.comp_apply, ← hpl x, hyperRefl_apply, sip_smul_left, inner_E, smul_smul]
          congr 1
          field_simp

/-- Every rotation of the spatial part is a product of reflections in unit vectors. -/
theorem exists_reflList {R : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)}
    (hR : ∀ u v, sip (R u) (R v) = sip u v) :
    ∃ l : List (Fin 3 → ℝ), (∀ u ∈ l, sip u u = 1) ∧ ∀ x, R x = hyperReflProd l x := by
  let R' : E3 ≃ₗ[ℝ] E3 := ofE.trans (R.trans ofE.symm)
  have hinner : ∀ x y : E3, ⟪R' x, R' y⟫ = ⟪x, y⟫ := by
    intro x y
    rw [inner_E, inner_E]
    show sip (ofE (ofE.symm (R (ofE x)))) (ofE (ofE.symm (R (ofE y)))) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hR _ _
  let phi : E3 ≃ₗᵢ[ℝ] E3 := LinearEquiv.isometryOfInner R' hinner
  obtain ⟨l, -, hprod⟩ := phi.reflections_generate_dim
  have hprod' : ∀ y : E3, ((List.map reflE l).prod) y = phi y := by
    intro y; rw [hprod]; rfl
  obtain ⟨l', hl', hpl⟩ := reflList_translate l
  refine ⟨l', hl', fun x => ?_⟩
  have hx := hpl (ofE.symm x)
  rw [hprod'] at hx
  have hphi : phi (ofE.symm x) = ofE.symm (R x) := by
    show ofE.symm (R (ofE (ofE.symm x))) = _
    rw [LinearEquiv.apply_symm_apply]
  rw [hphi, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hx
  exact hx

/-! ## Realizing rotations and boosts by spin elements -/

/-- **Every spatial rotation is induced by a spin element.** -/
theorem exists_spin_of_rot {R : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)} (hR : R ∈ RotV) :
    ∃ g : Cl3, ∃ _ : IsSpinElem g, ∀ x : LorentzCarrier, spinLor g x = rotToSpin R x := by
  obtain ⟨h1, h2⟩ := hR
  obtain ⟨l, hl, hRl⟩ := exists_reflList h1
  obtain ⟨g, hg1, hg2, hg3⟩ := exists_versor_of_list hl
  have hdet : ((-1 : ℝ) ^ l.length) = 1 := by
    have hd : LinearMap.det (hyperReflProd l) = (-1 : ℝ) ^ l.length := det_hyperReflProd hl
    have hRd : LinearMap.det (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) = LinearMap.det (hyperReflProd l) :=
      congrArg LinearMap.det (LinearMap.ext hRl)
    rw [h2, hd] at hRd
    exact hRd.symm
  rw [hdet] at hg1 hg2 hg3
  refine ⟨g, ⟨by rw [hg1, one_smul], by rw [hg2, one_smul]⟩, fun x => ?_⟩
  rw [hg3 x, rotToSpin_apply, one_smul, hRl x.2]

/-- **Every point of the unit shell in the forward cone is reached from `1_𝒮`.** -/
theorem exists_spin_boost {p : LorentzCarrier} (hN : NS p = 1) (hp : 0 ≤ p.1) :
    ∃ g : Cl3, ∃ _ : IsSpinElem g, spinLor g sOne = p := by
  refine ⟨spinToCl (paraSqrt p), isSpinElem_spinToCl (NS_paraSqrt hN hp), ?_⟩
  refine spinLor_unique ?_
  show spinToCl p = spinToCl (paraSqrt p) * spinToCl sOne
      * reverse (Q := q3) (spinToCl (paraSqrt p))
  rw [reverse_spinToCl, spinToCl_sOne, mul_one, paraSqrt_sq hN hp]

/-! ## Surjectivity -/

/-- **Phase V (completion).**  Every element of the intrinsic Lorentz group of the carrier
is induced by a spin element of `Cl₃(ℝ)`. -/
theorem spinLor_surjective_onto_GLor {F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier} (hF : F ∈ GLor) :
    ∃ g : Cl3, ∃ hg : IsSpinElem g, spinLorEquiv hg = F := by
  -- the image of the unit is a unit-norm forward paravector
  have hone : sOne ∈ ConeS := ⟨sOne, (sJ_one_left sOne).symm⟩
  have hNS : NS (F sOne) = 1 := by
    rw [hF.1.1 sOne]
    simp [NS, sOne, sip]
  have hcone : F sOne ∈ ConeS := (hF.1.2 sOne).1 hone
  have hp0 : 0 ≤ (F sOne).1 := ((mem_coneS_iff _).1 hcone).1
  obtain ⟨b, hb, hbone⟩ := exists_spin_boost hNS hp0
  -- the residual map fixes the unit
  set G : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier := (spinLorEquiv hb)⁻¹ * F with hG
  have hGmem : G ∈ GLor := Subgroup.mul_mem _ (Subgroup.inv_mem _ (spinLorEquiv_mem_GLor hb)) hF
  have hGone : G sOne = sOne := by
    show (spinLorEquiv hb).symm (F sOne) = sOne
    rw [← hbone]
    exact (spinLorEquiv hb).symm_apply_apply sOne
  obtain ⟨R, hR, hGR⟩ := (SpinCore.stabOne_iff G).1 ⟨hGmem, hGone⟩
  obtain ⟨g₂, hg₂, hg₂R⟩ := exists_spin_of_rot hR
  refine ⟨b * g₂, isSpinElem_mul hb hg₂, ?_⟩
  refine LinearEquiv.ext fun x => ?_
  show spinLor (b * g₂) x = F x
  rw [spinLor_mul]
  have hx : G x = spinLor g₂ x := by rw [hGR]; exact (hg₂R x).symm
  have hFx : F x = spinLor b (G x) := by
    show F x = spinLorEquiv hb (G x)
    rw [hG]
    show F x = spinLorEquiv hb ((spinLorEquiv hb).symm (F x))
    rw [(spinLorEquiv hb).apply_symm_apply]
  rw [hFx, hx]

/-- **Phase V (completion), bundled.**  The intrinsic Lorentz group of the carrier is
exactly the set of maps induced by spin elements of `Cl₃(ℝ)`. -/
theorem mem_GLor_iff_spinLor (F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) :
    F ∈ GLor ↔ ∃ g : Cl3, ∃ hg : IsSpinElem g, spinLorEquiv hg = F := by
  refine ⟨fun hF => spinLor_surjective_onto_GLor hF, ?_⟩
  rintro ⟨g, hg, rfl⟩
  exact spinLorEquiv_mem_GLor hg

end SpinCore
