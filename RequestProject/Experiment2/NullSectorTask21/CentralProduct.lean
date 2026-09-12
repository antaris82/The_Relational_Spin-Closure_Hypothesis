import RequestProject.Experiment2.NullSectorTask21.CentralComplex

/-!
# Task 21, Packages I and J: the core/centre intersection and the central product

**IDENTIFICATION / COMPARISON MODULE.**

Package I computes the intersection of the intrinsic invertible centre with the intrinsic
core carrier, using the intrinsic carrier equations only (item 86) and keeping the signs as
actual carrier elements (item 87).

Package J then tests whether the full internal carrier is the central product of the two:
the multiplication map from the direct product is shown to be a homomorphism, surjective,
and its kernel is computed exactly.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask21

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20

open Quaternion

/-! ## Package I — the intersection -/

theorem zc_neg_one_zero : zc (-1 : ℝ) 0 = -w1 := by
  funext i; fin_cases i <;> simp [zc, w1, wS]

theorem neg_w1_mem_CUnit : (-w1 : W) ∈ CUnit :=
  ⟨-1, 0, by norm_num, zc_neg_one_zero.symm⟩

theorem negOne_mem_CUnitG : WG.negOne ∈ CUnitG := neg_w1_mem_CUnit

/-- **PACKAGE I, principal (item 85).**  An element which is both central-invertible and in
the core carrier is exactly one of the two signs.  The proof uses only the intrinsic
coefficient equations of the two carriers. -/
theorem CUnit_inter_Lift {x : W} (hc : x ∈ CUnit) (hl : x ∈ Lift) : x = w1 ∨ x = -w1 := by
  obtain ⟨a, b, -, hz⟩ := hc
  obtain ⟨c, v, hnorm, hlv⟩ := hl
  have h0 : a = c := by
    have h := hz.symm.trans hlv
    have := congrFun h 0
    simpa [w1] using this
  have h4 : v.2.2 = 0 := by
    have h := hz.symm.trans hlv
    have h4' := congrFun h 4
    simp [w1] at h4'
    linarith
  have h5 : v.2.1 = 0 := by
    have h := hz.symm.trans hlv
    have h5' := congrFun h 5
    simp [w1] at h5'
    linarith
  have h6 : v.1 = 0 := by
    have h := hz.symm.trans hlv
    have h6' := congrFun h 6
    simp [w1] at h6'
    linarith
  have hv : v = (0, 0, 0) := Prod.ext h6 (Prod.ext h5 h4)
  rw [hv] at hlv hnorm
  simp only [h3, dot3] at hnorm
  have hc2 : c ^ 2 = 1 := by simpa using hnorm
  have hJ : Jmap ((0 : ℝ), (0 : ℝ), (0 : ℝ)) = 0 := Jmap_zero
  rw [hJ, sub_zero] at hlv
  have hfac : (c - 1) * (c + 1) = 0 := by nlinarith [hc2]
  have hcases : c = 1 ∨ c = -1 := by
    rcases mul_eq_zero.1 hfac with h'' | h''
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hcases with h | h
  · left; rw [hlv, h, one_smul]
  · right; rw [hlv, h]; module

/-- **PACKAGE I, packaged form.** -/
theorem inter_CUnitG_LiftG :
    ((CUnitG ⊓ LiftG : Subgroup WG) : Set WG) = {1, WG.negOne} := by
  ext u
  constructor
  · rintro ⟨hc, hl⟩
    rcases CUnit_inter_Lift hc hl with h | h
    · exact Or.inl (WG.ext h)
    · exact Or.inr (WG.ext h)
  · rintro (rfl | rfl)
    · exact ⟨w1_mem_CUnit, w1_mem_Lift⟩
    · exact ⟨negOne_mem_CUnitG, negOne_mem_LiftG⟩

/-! ## Package J — the central product -/

/-- The sign element inside the packaged centre. -/
def cNegOne : CUnitG := ⟨WG.negOne, negOne_mem_CUnitG⟩

/-- The sign element inside the packaged core. -/
def lNegOne : LiftG := ⟨WG.negOne, negOne_mem_LiftG⟩

theorem central_swap {z g z' g' : W} (hz' : z' ∈ CUnit) :
    (z ⋆ g) ⋆ (z' ⋆ g') = (z ⋆ z') ⋆ (g ⋆ g') := by
  obtain ⟨c, d, -, rfl⟩ := hz'
  rw [mul_assoc_W, ← mul_assoc_W g (zc c d) g', ← NullSectorTask20.zc_central c d g,
    mul_assoc_W, ← mul_assoc_W]

/-- **PACKAGE J (item 89).**  The multiplication map from the direct product of the centre
and the core to the full internal carrier. -/
def mu : CUnitG × LiftG →* LiftZG where
  toFun zg := ⟨(zg.1 : WG) * (zg.2 : WG),
    ⟨(zg.1 : WG).val, zg.1.2, (zg.2 : WG).val, zg.2.2, rfl⟩⟩
  map_one' := by
    refine Subtype.ext ?_
    simp only [Prod.fst_one, Prod.snd_one, OneMemClass.coe_one, mul_one]
  map_mul' a b := by
    refine Subtype.ext (WG.ext ?_)
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, WG.mul_val]
    exact (central_swap b.1.2).symm

@[simp] theorem mu_val (z : CUnitG) (g : LiftG) :
    ((mu (z, g) : LiftZG) : WG) = (z : WG) * (g : WG) := rfl

/-- **PACKAGE J (item 91).**  The multiplication map is surjective onto the full internal
carrier. -/
theorem mu_surjective : Function.Surjective mu := by
  rintro ⟨u, z, hz, g, hg, huv⟩
  refine ⟨(⟨WG.ofInvertible (isInvertible_of_mem_LiftZ (CUnit_subset_LiftZ hz)), hz⟩,
    ⟨WG.ofInvertible (isInvertible_of_mem_Lift hg), hg⟩), ?_⟩
  refine Subtype.ext (WG.ext ?_)
  show z ⋆ g = u.val
  exact huv.symm

/-- **PACKAGE J (items 92–93).**  The kernel of the multiplication map is exactly the
diagonal sign pair. -/
theorem ker_mu : (mu.ker : Set (CUnitG × LiftG)) = {(1, 1), (cNegOne, lNegOne)} := by
  ext zg
  constructor
  · intro h
    have hval : (zg.1 : WG) * (zg.2 : WG) = 1 :=
      congrArg (fun u : LiftZG => (u : WG)) (MonoidHom.mem_ker.1 h)
    have hg : (zg.2 : WG) = ((zg.1 : WG))⁻¹ := (inv_eq_of_mul_eq_one_right hval).symm
    have hgmem : (zg.2 : WG) ∈ CUnitG := by
      rw [hg]; exact Subgroup.inv_mem _ zg.1.2
    rcases CUnit_inter_Lift hgmem zg.2.2 with h1 | h1
    · left
      have hg2 : (zg.2 : WG) = 1 := WG.ext h1
      have hz2 : (zg.1 : WG) = 1 := by
        have h2 := hval
        rw [hg2, mul_one] at h2
        exact h2
      exact Prod.ext (Subtype.ext hz2) (Subtype.ext hg2)
    · right
      have hg2 : (zg.2 : WG) = WG.negOne := WG.ext h1
      have hz2 : (zg.1 : WG) = WG.negOne := by
        have h2 := hval
        rw [hg2] at h2
        calc (zg.1 : WG) = ((zg.1 : WG) * WG.negOne) * WG.negOne := by
              rw [mul_assoc, WG.negOne_mul_negOne, mul_one]
          _ = WG.negOne := by rw [h2, one_mul]
      exact Prod.ext (Subtype.ext hz2) (Subtype.ext hg2)
  · rintro (h | h) <;> rw [h] <;> refine MonoidHom.mem_ker.2 ?_
    · exact map_one mu
    · refine Subtype.ext (WG.ext ?_)
      show (-w1 : W) ⋆ (-w1) = w1
      rw [neg_mul_W, mul_neg_W, one_mul_W, neg_neg]

/-- **PACKAGE J (item 94), principal.**  The full internal carrier is exactly the central
product: the quotient of the direct product of the centre and the core by the diagonal sign
pair. -/
noncomputable def centralProductEquiv : ((CUnitG × LiftG) ⧸ mu.ker) ≃* LiftZG :=
  QuotientGroup.quotientKerEquivOfSurjective mu mu_surjective

/-! ## Transport to the standard models (item 95) -/

/-- The standard-side multiplication map, obtained by transporting `mu` through the
Package-H and Package-A identifications. -/
noncomputable def muStd : ℂˣ × UQ →* LiftZG :=
  mu.comp ((cUnitComplexEquiv.symm.prodCongr liftQuatEquiv).toMonoidHom)

theorem muStd_surjective : Function.Surjective muStd := by
  intro u
  obtain ⟨zg, hzg⟩ := mu_surjective u
  exact ⟨(cUnitComplexEquiv.symm.prodCongr liftQuatEquiv).symm zg, by
    simp only [muStd, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, hzg]⟩

theorem UQ_neg_one_mem : (-1 : ℍ) ∈ Metric.sphere (0 : ℍ) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_neg, norm_one]

/-- The sign element of the unit quaternion group. -/
noncomputable def uqNegOne : UQ := ⟨-1, UQ_neg_one_mem⟩

theorem cUnitComplexEquiv_cNegOne : cUnitComplexEquiv cNegOne = -1 := by
  refine Units.ext ?_
  show toComplex (-w1 : W) = ((-1 : ℂˣ) : ℂ)
  rw [← zc_neg_one_zero, toComplex_zc]
  refine Complex.ext ?_ ?_ <;> simp

theorem liftQuatEquiv_uqNegOne : liftQuatEquiv uqNegOne = lNegOne := by
  refine Subtype.ext (WG.ext ?_)
  show fromQuat ((uqNegOne : UQ) : ℍ) = -w1
  show fromQuat (-1 : ℍ) = -w1
  have h : fromQuat (-1 : ℍ) = -fromQuat (1 : ℍ) := by
    refine funext fun i => ?_
    fin_cases i <;> simp [fromQuat, w1, Jmap, wP, wQ, wR]
  rw [h, fromQuat_one]

theorem mem_ker_mu_iff (x : CUnitG × LiftG) :
    x ∈ mu.ker ↔ (x = (1, 1) ∨ x = (cNegOne, lNegOne)) := by
  constructor
  · intro hx; exact (Set.ext_iff.1 ker_mu x).1 hx
  · intro hx; exact (Set.ext_iff.1 ker_mu x).2 hx

theorem ker_muStd : (muStd.ker : Set (ℂˣ × UQ)) = {(1, 1), (-1, uqNegOne)} := by
  ext zq
  have hiso : zq ∈ muStd.ker ↔
      (cUnitComplexEquiv.symm.prodCongr liftQuatEquiv) zq ∈ mu.ker := Iff.rfl
  constructor
  · intro h
    rcases (mem_ker_mu_iff _).1 (hiso.1 h) with hc | hc
    · left
      have h1 : cUnitComplexEquiv.symm zq.1 = 1 := congrArg Prod.fst hc
      have h2 : liftQuatEquiv zq.2 = 1 := congrArg Prod.snd hc
      refine Prod.ext ?_ ?_
      · have h3 := congrArg cUnitComplexEquiv h1
        rwa [MulEquiv.apply_symm_apply, map_one] at h3
      · have h3 := congrArg liftQuatEquiv.symm h2
        rwa [MulEquiv.symm_apply_apply, map_one] at h3
    · right
      have h1 : cUnitComplexEquiv.symm zq.1 = cNegOne := congrArg Prod.fst hc
      have h2 : liftQuatEquiv zq.2 = lNegOne := congrArg Prod.snd hc
      refine Prod.ext ?_ ?_
      · have h3 := congrArg cUnitComplexEquiv h1
        rwa [MulEquiv.apply_symm_apply, cUnitComplexEquiv_cNegOne] at h3
      · have h3 := congrArg liftQuatEquiv.symm h2
        rwa [MulEquiv.symm_apply_apply, ← liftQuatEquiv_uqNegOne,
          MulEquiv.symm_apply_apply] at h3
  · intro h
    refine hiso.2 ((mem_ker_mu_iff _).2 ?_)
    rcases h with h | h
    · left
      rw [h]
      exact Prod.ext (map_one cUnitComplexEquiv.symm) (map_one liftQuatEquiv)
    · right
      rw [h]
      refine Prod.ext ?_ ?_
      · show cUnitComplexEquiv.symm (-1) = cNegOne
        rw [← cUnitComplexEquiv_cNegOne, MulEquiv.symm_apply_apply]
      · exact liftQuatEquiv_uqNegOne

/-- **PACKAGE J (item 95).**  The transported central-product description of the full
internal carrier. -/
noncomputable def liftZStandardEquiv : ((ℂˣ × UQ) ⧸ muStd.ker) ≃* LiftZG :=
  QuotientGroup.quotientKerEquivOfSurjective muStd muStd_surjective

end NullSectorTask21
