import RequestProject.Experiment2.NullSectorTask20.LiftCarrier

/-!
# Task 20, Layer 2 (Package C, part 2): the projection, its kernel, its centre

Phase A only.  The intrinsic projection from an internal carrier to the visible objects is
the inherited conjugation action written for an arbitrary invertible internal element.  The
module then computes, exactly:

* the projection of a reference implementer (it is the inherited visible family);
* multiplicativity of the projection;
* the kernel of the projection restricted to the internal **core** carrier — exactly two
  elements, `1` and `-1`;
* the kernel of the projection restricted to the **full** internal carrier — exactly the
  invertible central elements, a carrier containing a continuous injective one-parameter
  family;
* the centre of the full internal carrier — exactly the invertible central elements, hence
  equal to the kernel of the full projection, while the kernel of the core projection is a
  proper subcarrier of it;
* the inherited internal sign under a full turn of the parameter.
-/

namespace NullSectorTask20

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19

/-! ## Inverses in the inherited carrier -/

/-- **NEUTRAL DEFINITION.**  Two-sided invertibility in the inherited carrier. -/
def IsInvertible (u : W) : Prop := ∃ y : W, u ⋆ y = w1 ∧ y ⋆ u = w1

theorem inverse_unique {u a b : W} (ha : u ⋆ a = w1) (hb : b ⋆ u = w1) : a = b := by
  calc a = w1 ⋆ a := (one_mul_W a).symm
    _ = (b ⋆ u) ⋆ a := by rw [hb]
    _ = b ⋆ (u ⋆ a) := mul_assoc_W b u a
    _ = b := by rw [ha, mul_one_W]

/-- **NEUTRAL DEFINITION.**  A chosen inverse; it is the genuine inverse whenever one
exists, by uniqueness of two-sided inverses. -/
noncomputable def invW (u : W) : W :=
  Classical.epsilon fun y : W => u ⋆ y = w1 ∧ y ⋆ u = w1

theorem invW_spec {u : W} (hu : IsInvertible u) : u ⋆ invW u = w1 ∧ invW u ⋆ u = w1 :=
  Classical.epsilon_spec hu

theorem invW_eq {u y : W} (h1 : u ⋆ y = w1) (h2 : y ⋆ u = w1) : invW u = y :=
  inverse_unique (invW_spec ⟨y, h1, h2⟩).1 h2

theorem isInvertible_of_mem_Lift {u : W} (hu : u ∈ Lift) : IsInvertible u := by
  obtain ⟨u', -, h1, h2⟩ := Lift_inv_mem hu
  exact ⟨u', h1, h2⟩

theorem isInvertible_of_mem_LiftZ {u : W} (hu : u ∈ LiftZ) : IsInvertible u := by
  obtain ⟨u', -, h1, h2⟩ := LiftZ_inv_mem hu
  exact ⟨u', h1, h2⟩

/-! ## The projection -/

/-- **NEUTRAL DEFINITION (Package C).**  The intrinsic projection: the conjugation action of
an invertible internal element on the inherited carrier. -/
noncomputable def proj (u : W) : W →ₗ[ℝ] W where
  toFun x := (u ⋆ x) ⋆ invW u
  map_add' := by intro x y; simp only [mul_add_W, add_mul_W]
  map_smul' := by intro c x; simp only [mul_smul_W, smul_mul_W, RingHom.id_apply]

@[simp] theorem proj_apply (u x : W) : proj u x = (u ⋆ x) ⋆ invW u := rfl

/-- **DERIVED.**  On a reference implementer the projection is exactly the inherited visible
family. -/
theorem proj_Un {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) : proj (Un n θ) = PhiGen n θ := by
  have hinv : invW (Un n θ) = Un n (-θ) := invW_eq (Un_mul_neg hn θ) (Un_neg_mul hn θ)
  refine LinearMap.ext fun x => ?_
  simp only [proj_apply, hinv, PhiGen_apply]

theorem proj_w1 : proj w1 = LinearMap.id := by
  have hinv : invW w1 = w1 := invW_eq (mul_one_W w1) (one_mul_W w1)
  refine LinearMap.ext fun x => ?_
  rw [proj_apply, hinv, one_mul_W, mul_one_W, LinearMap.id_apply]

/-- **DERIVED.**  The projection is multiplicative on invertible elements. -/
theorem proj_mul {u v : W} (hu : IsInvertible u) (hv : IsInvertible v) :
    proj (u ⋆ v) = (proj u).comp (proj v) := by
  obtain ⟨hu1, hu2⟩ := invW_spec hu
  obtain ⟨hv1, hv2⟩ := invW_spec hv
  have hinv : invW (u ⋆ v) = invW v ⋆ invW u := by
    refine invW_eq ?_ ?_
    · calc (u ⋆ v) ⋆ (invW v ⋆ invW u) = (u ⋆ (v ⋆ invW v)) ⋆ invW u := by
            rw [mul_assoc_W, mul_assoc_W, mul_assoc_W]
        _ = w1 := by rw [hv1, mul_one_W, hu1]
    · calc (invW v ⋆ invW u) ⋆ (u ⋆ v) = (invW v ⋆ (invW u ⋆ u)) ⋆ v := by
            rw [mul_assoc_W, mul_assoc_W, mul_assoc_W]
        _ = w1 := by rw [hu2, mul_one_W, hv2]
  refine LinearMap.ext fun x => ?_
  simp only [proj_apply, hinv, LinearMap.comp_apply, mul_assoc_W]

/-- **DERIVED.**  An invertible central element projects to the identity. -/
theorem proj_central {u : W} (hu : IsInvertible u) (hc : ∀ x : W, u ⋆ x = x ⋆ u) :
    proj u = LinearMap.id := by
  obtain ⟨h1, -⟩ := invW_spec hu
  refine LinearMap.ext fun x => ?_
  rw [proj_apply, hc x, mul_assoc_W, h1, mul_one_W, LinearMap.id_apply]

theorem proj_zc {a b : ℝ} (hab : ¬ (a = 0 ∧ b = 0)) : proj (zc a b) = LinearMap.id :=
  proj_central (isInvertible_of_mem_LiftZ (CUnit_subset_LiftZ ⟨a, b, hab, rfl⟩))
    (zc_central a b)

/-- **DERIVED.**  A central invertible factor is invisible to the projection. -/
theorem proj_central_mul {z g : W} (hz : z ∈ CUnit) (hg : IsInvertible g) :
    proj (z ⋆ g) = proj g := by
  obtain ⟨a, b, hab, rfl⟩ := hz
  have hzi : IsInvertible (zc a b) :=
    isInvertible_of_mem_LiftZ (CUnit_subset_LiftZ ⟨a, b, hab, rfl⟩)
  rw [proj_mul hzi hg, proj_zc hab]
  exact LinearMap.ext fun x => rfl

/-! ## The kernel over the internal core carrier -/

theorem w1_ne_neg_w1 : (w1 : W) ≠ -w1 := by
  intro h
  have h0 := congrFun h 0
  norm_num [w1] at h0

/-- **PACKAGE C, principal.**  The kernel of the projection restricted to the internal core
carrier consists of exactly two elements. -/
theorem kernel_core : {u : W | u ∈ Lift ∧ proj u = LinearMap.id} = {w1, -w1} := by
  ext u
  constructor
  · rintro ⟨hu, hid⟩
    obtain ⟨n, θ, hn, rfl⟩ := (mem_Lift_iff_exists_Un u).1 hu
    have hP0 : PhiGen n 0 = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      rw [PhiGen_apply, neg_zero, Un_zero, one_mul_W, mul_one_W, LinearMap.id_apply]
    have hP : PhiGen n θ = PhiGen n 0 := by rw [← proj_Un hn θ, hid, hP0]
    obtain ⟨e, he, hUn⟩ := (coincidence_iff hn hn θ 0).1 hP
    rw [Un_zero] at hUn
    rcases he with rfl | rfl
    · left; rw [hUn, one_smul]
    · right; rw [hUn]; module
  · intro hu
    rcases hu with rfl | rfl
    · exact ⟨w1_mem_Lift, proj_w1⟩
    · refine ⟨neg_w1_mem_Lift, ?_⟩
      have hinv : invW (-w1 : W) = -w1 := by
        refine invW_eq ?_ ?_ <;>
          rw [neg_mul_W, mul_neg_W, one_mul_W, neg_neg]
      refine LinearMap.ext fun x => ?_
      rw [proj_apply, hinv, neg_mul_W, one_mul_W, neg_mul_W, mul_neg_W, mul_one_W, neg_neg,
        LinearMap.id_apply]

/-- **PACKAGE C.**  The kernel of the core projection has exactly two distinct elements. -/
theorem kernel_core_two : (w1 : W) ∈ {u : W | u ∈ Lift ∧ proj u = LinearMap.id} ∧
    (-w1 : W) ∈ {u : W | u ∈ Lift ∧ proj u = LinearMap.id} ∧ (w1 : W) ≠ -w1 := by
  refine ⟨?_, ?_, w1_ne_neg_w1⟩ <;> rw [kernel_core]
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## The kernel over the full internal carrier -/

/-- **PACKAGE C, principal.**  The kernel of the projection restricted to the full internal
carrier is exactly the set of invertible central elements. -/
theorem kernel_full : {u : W | u ∈ LiftZ ∧ proj u = LinearMap.id} = CUnit := by
  ext u
  constructor
  · rintro ⟨⟨z, hz, g, hg, rfl⟩, hid⟩
    have hgid : proj g = LinearMap.id := by
      rw [← proj_central_mul hz (isInvertible_of_mem_Lift hg)]; exact hid
    have hgmem : g ∈ ({w1, -w1} : Set W) := by
      rw [← kernel_core]; exact ⟨hg, hgid⟩
    obtain ⟨a, b, hab, rfl⟩ := hz
    rcases hgmem with rfl | rfl
    · rw [mul_one_W]; exact ⟨a, b, hab, rfl⟩
    · refine ⟨-a, -b, ?_, ?_⟩
      · rintro ⟨h1, h2⟩
        exact hab ⟨by linarith, by linarith⟩
      · rw [mul_neg_W, mul_one_W, zc, zc]
        module
  · intro hu
    exact ⟨CUnit_subset_LiftZ hu, by obtain ⟨a, b, hab, rfl⟩ := hu; exact proj_zc hab⟩

/-- **PACKAGE C.**  The kernel of the full projection contains a continuous injective
one-parameter family, built from the inherited central one-parameter elements.  It is
therefore *not* discrete, in contrast with the two-element kernel of the core
projection. -/
theorem kernel_full_continuum :
    Continuous (fun t : ℝ => zexp 1 0 t) ∧ Function.Injective (fun t : ℝ => zexp 1 0 t) ∧
      ∀ t : ℝ, zexp 1 0 t ∈ CUnit ∧ proj (zexp 1 0 t) = LinearMap.id := by
  have hform : ∀ t : ℝ, zexp 1 0 t = zc (Real.exp t) 0 := by
    intro t
    simp [zexp]
  refine ⟨?_, ?_, ?_⟩
  · rw [continuous_pi_iff]
    intro i
    simp only [hform]
    fin_cases i <;> simp [zc, w1, wS] <;> fun_prop
  · intro s t hst
    simp only [hform] at hst
    have := (zc_injective hst).1
    exact Real.exp_injective this
  · intro t
    have hne : ¬ (Real.exp t = 0 ∧ (0 : ℝ) = 0) := by
      rintro ⟨h, -⟩
      exact (Real.exp_pos t).ne' h
    exact ⟨⟨Real.exp t, 0, hne, hform t⟩, by rw [hform t]; exact proj_zc hne⟩

/-- **PACKAGE C.**  The two kernels are genuinely different: the core kernel is a proper
subset of the full kernel. -/
theorem kernel_core_ssubset_kernel_full :
    ({w1, -w1} : Set W) ⊂ CUnit := by
  constructor
  · rintro u (rfl | rfl)
    · exact w1_mem_CUnit
    · exact ⟨-1, 0, by norm_num, by rw [zc]; module⟩
  · intro hsub
    have hmem : zexp 1 0 1 ∈ ({w1, -w1} : Set W) := hsub (kernel_full_continuum.2.2 1).1
    have hform : zexp 1 0 1 = zc (Real.exp 1) 0 := by simp [zexp]
    have hlt : (1 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (x := 1) (by norm_num)
      linarith
    rcases hmem with h | h
    · rw [hform] at h
      have : Real.exp 1 = 1 := by
        have h0 := congrFun h 0
        simp [zc, w1, wS] at h0
      linarith
    · rw [hform] at h
      have : Real.exp 1 = -1 := by
        have h0 := congrFun h 0
        simpa [zc, w1, wS] using h0
      linarith

/-! ## The centre of the full internal carrier -/

/-- **NEUTRAL DEFINITION.**  The centre of a subcarrier. -/
def CentreOf (S : Set W) : Set W := {u : W | u ∈ S ∧ ∀ x ∈ S, u ⋆ x = x ⋆ u}

theorem e2_isUnitAxis : IsUnitAxis ((0, 1, 0) : Vec3) := by
  simp [IsUnitAxis, h3, dot3]

theorem Un_pi (n : Vec3) : Un n Real.pi = -Jmap n := by
  have h : Real.pi / 2 = Real.pi / 2 := rfl
  rw [Un, Real.cos_pi_div_two, Real.sin_pi_div_two]
  module

theorem spat_eq_neg_wS_mul_Jmap (n : Vec3) : spat n = -(wS ⋆ Jmap n) := by
  rw [Jmap_eq_central_mul, ← mul_assoc_W, wS_sq, neg_mul_W, one_mul_W, neg_neg]

/-- **PACKAGE C, principal.**  The centre of the full internal carrier is exactly the set of
invertible central elements — hence equal to the kernel of the full projection, and strictly
larger than the kernel of the core projection. -/
theorem centre_LiftZ : CentreOf LiftZ = CUnit := by
  ext u
  constructor
  · rintro ⟨hu, hcomm⟩
    have hJ : ∀ n : Vec3, IsUnitAxis n → u ⋆ Jmap n = Jmap n ⋆ u := by
      intro n hn
      have hmem : Un n Real.pi ∈ LiftZ := Lift_subset_LiftZ (Un_mem_Lift hn Real.pi)
      have := hcomm _ hmem
      rw [Un_pi] at this
      have h2 : -(u ⋆ Jmap n) = -(Jmap n ⋆ u) := by
        rw [← mul_neg_W, ← neg_mul_W]; exact this
      exact neg_injective h2
    have hspat : ∀ n : Vec3, IsUnitAxis n → u ⋆ spat n = spat n ⋆ u := by
      intro n hn
      rw [spat_eq_neg_wS_mul_Jmap, mul_neg_W, neg_mul_W]
      congr 1
      calc u ⋆ (wS ⋆ Jmap n) = (u ⋆ wS) ⋆ Jmap n := (mul_assoc_W _ _ _).symm
        _ = (wS ⋆ u) ⋆ Jmap n := by rw [← wS_central u]
        _ = wS ⋆ (u ⋆ Jmap n) := mul_assoc_W _ _ _
        _ = wS ⋆ (Jmap n ⋆ u) := by rw [hJ n hn]
        _ = (wS ⋆ Jmap n) ⋆ u := (mul_assoc_W _ _ _).symm
    have hA : u ⋆ wA = wA ⋆ u := by
      have := hspat (1, 0, 0) e1_isUnitAxis
      rwa [spat_wA] at this
    have hB : u ⋆ wB = wB ⋆ u := by
      have := hspat (0, 1, 0) e2_isUnitAxis
      rwa [spat_wB] at this
    have hZ : u ∈ (Z : Set W) := by
      rw [← centralizer_pair_eq_Z]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hA
      · exact hB
    obtain ⟨a, b, hab⟩ := (mem_Z_iff u).1 hZ
    have hzc : u = zc a b := by rw [hab, zc]
    have hne : ¬ (a = 0 ∧ b = 0) := by
      rintro ⟨rfl, rfl⟩
      obtain ⟨y, h1, -⟩ := isInvertible_of_mem_LiftZ hu
      rw [hzc] at h1
      have : (0 : W) ⋆ y = w1 := by
        have hz0 : zc (0 : ℝ) (0 : ℝ) = (0 : W) := by rw [zc]; module
        rwa [hz0] at h1
      rw [zero_mul_W] at this
      have h0 := congrFun this 0
      norm_num [w1] at h0
    exact ⟨a, b, hne, hzc⟩
  · intro hu
    refine ⟨CUnit_subset_LiftZ hu, ?_⟩
    obtain ⟨a, b, -, rfl⟩ := hu
    intro x _
    exact zc_central a b x

/-- **PACKAGE C, principal.**  The kernel of the full projection is exactly the centre of
the full internal carrier, while the kernel of the core projection is a proper subcarrier of
that centre.  The answer to "is the kernel the full centre?" therefore *depends on the
chosen internal subcarrier*, and is recorded here as such. -/
theorem kernel_vs_centre :
    {u : W | u ∈ LiftZ ∧ proj u = LinearMap.id} = CentreOf LiftZ ∧
      ({w1, -w1} : Set W) ⊂ CentreOf LiftZ ∧
      {u : W | u ∈ Lift ∧ proj u = LinearMap.id} = ({w1, -w1} : Set W) := by
  refine ⟨by rw [kernel_full, centre_LiftZ], ?_, kernel_core⟩
  rw [centre_LiftZ]
  exact kernel_core_ssubset_kernel_full

/-! ## The inherited internal sign under a full turn -/

/-- **PACKAGE C (item 35).**  A full turn of the parameter is invisible below, but changes
the internal element by the inherited central sign; a double full turn returns the internal
element itself.  The sign is *not* an extra postulate: it is the value `Un n (2π) = -1`. -/
theorem full_turn_sign (n : Vec3) :
    Un n (2 * Real.pi) = -w1 ∧ Un n (4 * Real.pi) = w1 ∧
      proj (Un n (2 * Real.pi)) = LinearMap.id ∧ Un n (2 * Real.pi) ≠ Un n 0 := by
  refine ⟨Un_two_pi n, Un_four_pi n, ?_, ?_⟩
  · rw [Un_two_pi n]
    have hmem : (-w1 : W) ∈ ({w1, -w1} : Set W) := Or.inr rfl
    rw [← kernel_core] at hmem
    exact hmem.2
  · rw [Un_two_pi n, Un_zero]
    exact fun h => w1_ne_neg_w1 h.symm

end NullSectorTask20
