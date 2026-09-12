import Mathlib
import RequestProject.Experiment1.DetPreservingRep

/-!
# Task 5, part III : the exact kernel, the intrinsic quotient, and its identifications

* Sections 8, 17 — the kernel of the congruence representation of `G_det` is *exactly* the
  scalar unit circle (proved in the direction *trivial action ⇒ scalar unit matrix*);
* Section 12 — the product decomposition `G_det = U(1)_scalar · SL(2, ℂ)` and the intersection
  `U(1)_scalar ∩ SL(2, ℂ) = {±I}`;
* Section 13 — `G_det / U(1)_scalar ≃* SO⁺(1,3)`;
* Section 14 — `G_det / U(1)_scalar ≃* SL(2, ℂ) / {±I}`, by the map induced by the inclusion;
* Sections 15, 19, 21, 25 — the reclassification of `det A = 1`, the `1+1` restriction, the
  countertests and the bundled dependency theorem.

No physical interpretation is asserted anywhere.
-/

noncomputable section

open Matrix Complex Herm2 Mink4
open scoped Pointwise

namespace SpinLorentz

/-! ## The scalar circle as a subgroup of `G_det` -/

/-- The scalar embedding, corestricted to `G_det`. -/
def scalarHomG : Circle →* DetPreservingCongruence :=
  MonoidHom.codRestrict scalarHom DetPreservingCongruence
    (fun lam => scalarCircle_le_detPreserving ⟨lam, rfl⟩)

@[simp] theorem coe_scalarHomG (lam : Circle) :
    ((scalarHomG lam : DetPreservingCongruence) : GL2C) = scalarHom lam := rfl

theorem scalarHomG_injective : Function.Injective scalarHomG := by
  intro lam mu h
  apply scalarHom_injective
  have := congrArg (fun A : DetPreservingCongruence => (A : GL2C)) h
  simpa using this

/-- **Section 6.** The scalar unit-phase subgroup, as a subgroup of `G_det`. -/
def scalarCircleG : Subgroup DetPreservingCongruence := scalarHomG.range

theorem mem_scalarCircleG_iff (A : DetPreservingCongruence) :
    A ∈ scalarCircleG ↔ (A : GL2C) ∈ scalarCircle := by
  constructor
  · rintro ⟨lam, rfl⟩
    exact ⟨lam, rfl⟩
  · rintro ⟨lam, hlam⟩
    exact ⟨lam, Subtype.ext hlam⟩

/-- **Section 6.** `U(1)_scalar` is central in `G_det`. -/
theorem scalarCircleG_central : scalarCircleG ≤ Subgroup.center DetPreservingCongruence := by
  intro A hA
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have hcen := scalarCircle_central ((mem_scalarCircleG_iff A).1 hA)
  rw [Subgroup.mem_center_iff] at hcen
  exact hcen (g : GL2C)

/-! ## Sections 8, 17 : the exact kernel -/

/-- **Sections 8, 17.** An element of `G_det` acts trivially on the whole Hermitian carrier if
and only if it is a scalar unit matrix.  The nontrivial direction is
*trivial congruence action ⇒ scalar unit complex matrix*. -/
theorem trivial_action_iff_scalarCircleG (A : DetPreservingCongruence) :
    (∀ H : M2, H.IsHermitian → ((A : GL2C) : M2) * H * ((A : GL2C) : M2)ᴴ = H)
      ↔ A ∈ scalarCircleG := by
  constructor
  · intro h
    rw [mem_scalarCircleG_iff, mem_scalarCircle_iff]
    exact eq_scalar_of_congr_trivial h
  · intro hA H _
    exact scalarCircle_acts_trivially ((mem_scalarCircleG_iff A).1 hA) H

/-- **Sections 8, 17.** The kernel of the congruence representation of `G_det` is exactly the
scalar unit circle. -/
theorem detPreserving_rep_kernel : repGSO.ker = scalarCircleG := by
  ext A
  rw [repGSO_mem_ker_iff, repG4_eq_one_iff, trivial_action_iff_scalarCircleG]

instance scalarCircleG_normal : scalarCircleG.Normal := by
  rw [← detPreserving_rep_kernel]
  exact MonoidHom.normal_ker repGSO

/-! ## Section 10, 12 : `SL(2, ℂ)` representatives and the product decomposition -/

/-- The inclusion `SL(2, ℂ) → G_det`. -/
def SLtoGdet : SL2C →* DetPreservingCongruence :=
  MonoidHom.codRestrict SLtoGL DetPreservingCongruence (fun B => SL_le_detPreserving ⟨B, rfl⟩)

@[simp] theorem coe_SLtoGdet (B : SL2C) :
    ((SLtoGdet B : DetPreservingCongruence) : GL2C) = SLtoGL B := rfl

theorem SLtoGdet_injective : Function.Injective SLtoGdet := by
  intro B C h
  apply SLtoGL_injective
  have := congrArg (fun A : DetPreservingCongruence => (A : GL2C)) h
  simpa using this

/-- **Section 12.** Every element of `G_det` is an `SL(2, ℂ)` element times a scalar unit
phase. -/
theorem exists_scalar_mul_SL (A : DetPreservingCongruence) :
    ∃ (B : SL2C) (s : DetPreservingCongruence), s ∈ scalarCircleG ∧ A = SLtoGdet B * s := by
  obtain ⟨lam, B, hlam, hBeq, _⟩ := exists_SL_representative A.2
  have hlamne : lam ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlam
    norm_num at hlam
  have hmu : ‖lam⁻¹‖ = 1 := by rw [norm_inv, hlam, inv_one]
  refine ⟨B, scalarHomG ⟨lam⁻¹, by simpa [Submonoid.unitSphere] using hmu⟩, ⟨_, rfl⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  show ((A : GL2C) : M2) = (B : M2) * ((lam⁻¹ : ℂ) • (1 : M2))
  rw [hBeq, Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hlamne, one_smul]

/-- **Section 12.** The same decomposition, phrased inside `GL(2, ℂ)`. -/
theorem exists_scalar_mul_SL_GL {A : GL2C} (hA : A ∈ DetPreservingCongruence) :
    ∃ (B : SL2C) (s : GL2C), s ∈ scalarCircle ∧ A = SLtoGL B * s := by
  obtain ⟨B, s, hs, hEq⟩ := exists_scalar_mul_SL ⟨A, hA⟩
  refine ⟨B, (s : GL2C), (mem_scalarCircleG_iff s).1 hs, ?_⟩
  have := congrArg (fun x : DetPreservingCongruence => (x : GL2C)) hEq
  simpa using this

/-- **Section 12.** `G_det = U(1)_scalar · SL(2, ℂ)` as subgroups of `GL(2, ℂ)`. -/
theorem detPreserving_eq_scalarCircle_mul_SL :
    DetPreservingCongruence = scalarCircle ⊔ SLimage := by
  apply le_antisymm
  · intro A hA
    obtain ⟨B, s, hs, rfl⟩ := exists_scalar_mul_SL_GL hA
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨B, rfl⟩) (Subgroup.mem_sup_left hs)
  · exact sup_le scalarCircle_le_detPreserving SL_le_detPreserving

/-- **Section 12.** The same statement as an equality of sets, with the pointwise product. -/
theorem detPreserving_set_eq_scalarCircle_mul_SL :
    (DetPreservingCongruence : Set GL2C) = (SLimage : Set GL2C) * (scalarCircle : Set GL2C) := by
  ext A
  constructor
  · intro hA
    obtain ⟨B, s, hs, rfl⟩ := exists_scalar_mul_SL_GL hA
    exact ⟨SLtoGL B, ⟨B, rfl⟩, s, hs, rfl⟩
  · rintro ⟨x, hx, s, hs, rfl⟩
    exact Subgroup.mul_mem _ (SL_le_detPreserving hx) (scalarCircle_le_detPreserving hs)

/-- **Section 12.** `U(1)_scalar ∩ SL(2, ℂ) = {±I}`. -/
theorem scalarCircle_inter_SL (A : GL2C) :
    A ∈ scalarCircle ⊓ SLimage ↔ ((A : M2) = 1 ∨ (A : M2) = -1) := by
  constructor
  · rintro ⟨hs, B, hB⟩
    obtain ⟨lam, _, hAeq⟩ := (mem_scalarCircle_iff A).1 hs
    have hdet : (A : M2).det = 1 := by
      rw [← hB, coe_SLtoGL, Matrix.SpecialLinearGroup.det_coe]
    rw [hAeq, Matrix.det_smul] at hdet
    simp only [Fintype.card_fin, Matrix.det_one, mul_one] at hdet
    have hlam : lam = 1 ∨ lam = -1 := by
      have : lam ^ 2 = (1 : ℂ) ^ 2 := by rw [hdet]; ring
      simpa using sq_eq_sq_imp this
    rcases hlam with rfl | rfl
    · left; rw [hAeq, one_smul]
    · right; rw [hAeq]; ext i j; simp
  · intro h
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [mem_scalarCircle_iff]
      rcases h with h | h
      · exact ⟨1, by norm_num, by rw [h, one_smul]⟩
      · refine ⟨-1, by norm_num, ?_⟩
        rw [h]; ext i j; simp
    · rcases h with h | h
      · refine ⟨1, ?_⟩
        apply Units.ext
        rw [coe_SLtoGL, h]
        rfl
      · refine ⟨-1, ?_⟩
        apply Units.ext
        rw [coe_SLtoGL, h]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.SpecialLinearGroup.coe_neg]

/-! ## Section 13 : the intrinsic quotient -/

/-- **Section 13.** The intrinsic quotient `G_det / U(1)_scalar`. -/
abbrev DetQuotient := DetPreservingCongruence ⧸ scalarCircleG

/-- **Section 13, primary theorem.** The congruence representation descends to a group
isomorphism from the intrinsic quotient onto the independently defined proper orthochronous
Lorentz group. -/
def detPreservingQuotient_mulEquiv_SO13Plus : DetQuotient ≃* Mink4.SO13Plus :=
  (QuotientGroup.quotientMulEquivOfEq detPreserving_rep_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective repGSO repGSO_surjective)

/-! ## Section 14 : comparison with the Task 4 quotient -/

theorem negPM_le_comap_scalarCircleG : negPM ≤ scalarCircleG.comap SLtoGdet := by
  rintro B (rfl | rfl)
  · simp
  · rw [Subgroup.mem_comap, mem_scalarCircleG_iff, mem_scalarCircle_iff]
    refine ⟨-1, by norm_num, ?_⟩
    rw [coe_SLtoGdet, coe_SLtoGL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_neg]

/-- **Section 14.** The map on quotients induced by the inclusion `SL(2, ℂ) ↪ G_det`. -/
def quotMap : SL2C ⧸ negPM →* DetQuotient :=
  QuotientGroup.map negPM scalarCircleG SLtoGdet negPM_le_comap_scalarCircleG

theorem quotMap_mk (B : SL2C) : quotMap (B : SL2C ⧸ negPM) = (SLtoGdet B : DetQuotient) := rfl

theorem quotMap_injective : Function.Injective quotMap := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective x
  rw [quotMap_mk, QuotientGroup.eq_one_iff, mem_scalarCircleG_iff, mem_scalarCircle_iff] at hx
  obtain ⟨lam, _, hBeq⟩ := hx
  rw [coe_SLtoGdet, coe_SLtoGL] at hBeq
  have hdet : (B : M2).det = 1 := Matrix.SpecialLinearGroup.det_coe B
  rw [hBeq, Matrix.det_smul] at hdet
  simp only [Fintype.card_fin, Matrix.det_one, mul_one] at hdet
  have hlam : lam = 1 ∨ lam = -1 := by
    have : lam ^ 2 = (1 : ℂ) ^ 2 := by rw [hdet]; ring
    simpa using sq_eq_sq_imp this
  rw [QuotientGroup.eq_one_iff, mem_negPM]
  rcases hlam with rfl | rfl
  · left
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hBeq, one_smul]
    rfl
  · right
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hBeq]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_neg]

theorem quotMap_surjective : Function.Surjective quotMap := by
  intro y
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨B, s, hs, hEq⟩ := exists_scalar_mul_SL A
  refine ⟨(B : SL2C ⧸ negPM), ?_⟩
  rw [quotMap_mk, hEq]
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff s).2 hs, mul_one]

/-- **Section 14.** `SL(2, ℂ)/{±I} ≃* G_det / U(1)_scalar`, via the map induced by the
inclusion. -/
def SLQuotient_mulEquiv_detPreservingQuotient : (SL2C ⧸ negPM) ≃* DetQuotient :=
  MulEquiv.ofBijective quotMap ⟨quotMap_injective, quotMap_surjective⟩

/-- **Section 14.** `G_det / U(1)_scalar ≃* SL(2, ℂ)/{±I}`. -/
def detPreservingQuotient_mulEquiv_SLQuotient : DetQuotient ≃* (SL2C ⧸ negPM) :=
  SLQuotient_mulEquiv_detPreservingQuotient.symm

/-! ## Section 15 : `det A = 1` is a normalization, not a Lorentz restriction -/

/-- **Section 15.** The false interpretation is refuted: there is a determinant-preserving
`A` with `det A ≠ 1`. -/
theorem det_ne_one_of_some_detPreserving :
    ∃ A : GL2C, A ∈ DetPreservingCongruence ∧ (A : M2).det ≠ 1 :=
  ⟨diagI, diagI_mem_detPreserving, by rw [det_diagI]; simpa using (by simp [Complex.ext_iff] :
    Complex.I ≠ 1)⟩

/-- **Section 15.** Restricting to `det A = 1` does not change the induced Lorentz group: the
`SL(2, ℂ)` representation and the `G_det` representation have the same image, all of
`SO⁺(1,3)`. -/
theorem SL_and_detPreserving_same_image (L : Mink4.SO13Plus) :
    (∃ B : SL2C, repSO B = L) ∧ (∃ A : DetPreservingCongruence, repGSO A = L) :=
  ⟨repSO_surjective L, repGSO_surjective L⟩

/-! ## Section 19 : the `1+1` diagonal restriction only depends on the phase class -/

/-- **Section 19.** For any unit phase `λ`, the congruence action of `λ A_η` on the diagonal
sector is the action of `A_η`, namely the reciprocal `1+1` boost. -/
theorem v4_action_depends_only_on_phase_class {lam : ℂ} (hlam : ‖lam‖ = 1) (η u v : ℝ) :
    (lam • ((boostLift η : SL2C) : M2)) * Herm2.D u v * (lam • ((boostLift η : SL2C) : M2))ᴴ
      = ((boostLift η : SL2C) : M2) * Herm2.D u v * ((boostLift η : SL2C) : M2)ᴴ ∧
    (lam • ((boostLift η : SL2C) : M2)) * Herm2.D u v * (lam • ((boostLift η : SL2C) : M2))ᴴ
      = Herm2.D (Real.exp η * u) (Real.exp (-η) * v) := by
  refine ⟨congr_smul_eq hlam _ _, ?_⟩
  rw [congr_smul_eq hlam, diagonal_boost]

/-! ## Section 21 : a non-scalar determinant-preserving element is not in the kernel -/

theorem diagTwo_congr_ne (H : M2) (hH : H = Herm2.PP) :
    ((diagTwo : SL2C) : M2) * H * ((diagTwo : SL2C) : M2)ᴴ ≠ H := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  rw [hH] at h00
  simp [diagTwo, Herm2.PP, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply]
    at h00
  norm_num [Complex.ext_iff] at h00

/-- **Section 21.** An explicit non-scalar element of `G_det` that moves a Hermitian matrix. -/
theorem exists_nonscalar_not_in_kernel :
    ∃ (A : DetPreservingCongruence) (H : M2), H.IsHermitian ∧ A ∉ scalarCircleG ∧
      ((A : GL2C) : M2) * H * ((A : GL2C) : M2)ᴴ ≠ H := by
  refine ⟨SLtoGdet diagTwo, Herm2.PP, ?_, ?_, ?_⟩
  · rw [Herm2.PP]
    unfold Matrix.IsHermitian
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · intro hmem
    rw [← trivial_action_iff_scalarCircleG] at hmem
    exact diagTwo_congr_ne Herm2.PP rfl (hmem Herm2.PP (by
      rw [Herm2.PP]
      unfold Matrix.IsHermitian
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]))
  · exact diagTwo_congr_ne Herm2.PP rfl

/-! ## Section 25 : the corrected dependency theorem -/

/-- **Section 25.** The corrected dependency theorem of Task 5.  Every clause refers to the
actual intrinsically defined group, its congruence representation, its kernel, the quotient and
the two group equivalences.

1. `G_det` — defined by determinant preservation alone — is exactly `{A : ‖det A‖ = 1}`;
2. the kernel of its congruence representation is exactly the central scalar unit circle;
3. the quotient by that kernel is isomorphic to the independently defined `SO⁺(1,3)`;
4. `SL(2, ℂ)` is contained in `G_det`, *strictly*;
5. every element of `G_det` is an `SL(2, ℂ)` element times a scalar unit phase, and the
   normalizing phase is unique up to sign;
6. `U(1)_scalar ∩ SL(2, ℂ) = {±I}`;
7. the quotient is also isomorphic to `SL(2, ℂ)/{±I}`. -/
theorem group_dependency_theorem_v5 :
    (∀ A : GL2C, A ∈ DetPreservingCongruence ↔ ‖(A : M2).det‖ = 1) ∧
    repGSO.ker = scalarCircleG ∧
    scalarCircleG ≤ Subgroup.center DetPreservingCongruence ∧
    Nonempty (DetQuotient ≃* Mink4.SO13Plus) ∧
    SLimage < DetPreservingCongruence ∧
    DetPreservingCongruence = scalarCircle ⊔ SLimage ∧
    (∀ A : DetPreservingCongruence, ∃ (B : SL2C) (s : DetPreservingCongruence),
      s ∈ scalarCircleG ∧ A = SLtoGdet B * s) ∧
    (∀ A : GL2C, A ∈ scalarCircle ⊓ SLimage ↔ ((A : M2) = 1 ∨ (A : M2) = -1)) ∧
    Nonempty (DetQuotient ≃* (SL2C ⧸ negPM)) :=
  ⟨mem_detPreserving_iff_norm_det_eq_one, detPreserving_rep_kernel, scalarCircleG_central,
    ⟨detPreservingQuotient_mulEquiv_SO13Plus⟩, SL_lt_detPreserving,
    detPreserving_eq_scalarCircle_mul_SL, exists_scalar_mul_SL, scalarCircle_inter_SL,
    ⟨detPreservingQuotient_mulEquiv_SLQuotient⟩⟩

end SpinLorentz

/-! ## Axiom audit -/

#print axioms SpinLorentz.mem_detPreserving_iff_norm_det_eq_one
#print axioms SpinLorentz.detPreserving_rep_kernel
#print axioms SpinLorentz.exists_SL_representative
#print axioms SpinLorentz.SL_representative_ambiguity
#print axioms SpinLorentz.detPreservingQuotient_mulEquiv_SO13Plus
#print axioms SpinLorentz.detPreservingQuotient_mulEquiv_SLQuotient
#print axioms SpinLorentz.exists_unit_phase_det_one
#print axioms SpinLorentz.SL_representative_pm
#print axioms SpinLorentz.twoGL_not_detPreserving
#print axioms SpinLorentz.circle_exists_square_root
#print axioms SpinLorentz.SL_lt_detPreserving
#print axioms SpinLorentz.v4_action_depends_only_on_phase_class
#print axioms SpinLorentz.group_dependency_theorem_v5
