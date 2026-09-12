import RequestProject.Experiment2.NullSectorTask20.SafeBase

/-!
# Task 20, Layer 1 (Package C, part 1): the intrinsic internal carriers

Phase A only.  Two internal carriers are frozen here, both generated **inside the inherited
carrier `W`** by objects that already exist in the reconstruction:

* `Lift` — the smallest set containing every reference implementer `Un n θ` and closed under
  the inherited product and inherited inversion.  It is described intrinsically as the set
  of elements `a • 1 - J v` with `a² + ⟨v,v⟩ = 1`, and this description is *proved* to
  coincide with the set of reference implementers (`mem_Lift_iff_exists_Un`).
* `LiftZ` — the carrier obtained by additionally admitting the invertible elements of the
  exact centre, i.e. all products `z ⋆ g` with `z` an invertible central element and
  `g ∈ Lift`.  No central factor is quotiented out anywhere.

Everything in this module is elementary algebra inside `W`; no topology is used.
-/

namespace NullSectorTask20

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19

/-! ## Elementary facts about the inherited spatial form -/

theorem h3_self_nonneg (v : Vec3) : 0 ≤ h3 v v := by
  simp only [h3, dot3]
  nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]

theorem h3_self_eq_zero_iff (v : Vec3) : h3 v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    simp only [h3, dot3] at h
    have h1 : v.1 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    have h2 : v.2.1 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    have h3' : v.2.2 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    exact Prod.ext h1 (Prod.ext h2 h3')
  · rintro rfl; simp [h3, dot3]

theorem Jmap_zero : Jmap (0 : Vec3) = 0 := by
  funext i; fin_cases i <;> simp [Jmap, wP, wQ, wR]

theorem Jmap_neg (v : Vec3) : Jmap (-v) = -Jmap v := by
  have := Jmap_linear.2 (-1 : ℝ) v
  simpa [neg_smul] using this

/-! ## The internal core carrier -/

/-- **NEUTRAL DEFINITION (Package C).**  The intrinsic internal core carrier: the elements
of the inherited carrier of the shape `a • 1 - J v` normalized by `a² + ⟨v,v⟩ = 1`. -/
def Lift : Set W := {u : W | ∃ (a : ℝ) (v : Vec3), a ^ 2 + h3 v v = 1 ∧ u = a • w1 - Jmap v}

theorem mem_Lift {a : ℝ} {v : Vec3} (h : a ^ 2 + h3 v v = 1) : a • w1 - Jmap v ∈ Lift :=
  ⟨a, v, h, rfl⟩

theorem w1_mem_Lift : w1 ∈ Lift :=
  ⟨1, 0, by simp [h3, dot3], by simp [Jmap_zero]⟩

theorem neg_w1_mem_Lift : -w1 ∈ Lift :=
  ⟨-1, 0, by simp [h3, dot3], by rw [Jmap_zero]; module⟩

/-- **DERIVED.**  Every reference implementer lies in the internal core carrier. -/
theorem Un_mem_Lift {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) : Un n θ ∈ Lift := by
  refine ⟨Real.cos (θ / 2), Real.sin (θ / 2) • n, ?_, ?_⟩
  · have hnn : h3 n n = 1 := hn
    have : h3 (Real.sin (θ / 2) • n) (Real.sin (θ / 2) • n)
        = Real.sin (θ / 2) ^ 2 * h3 n n := by
      simp only [h3, dot3]; simp [Prod.smul_def]; ring
    rw [this, hnn]
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  · rw [Un, Jmap_linear.2]

/-! ## The exact product rule of the internal core carrier -/

/-- **DERIVED.**  The exact product of two elements written in the normal form of the
internal core carrier. -/
theorem quat_mul (a b : ℝ) (v w : Vec3) :
    (a • w1 - Jmap v) ⋆ (b • w1 - Jmap w)
      = (a * b - h3 v w) • w1 - Jmap (a • w + b • v + spCross v w) := by
  simp only [sub_mul_W, mul_sub_W, smul_mul_W, mul_smul_W, one_mul_W, mul_one_W, Jmap_mul,
    Jmap_linear.1, Jmap_linear.2]
  module

/-- **DERIVED.**  The normalization is multiplicative: the exact four-term identity behind
closure of the internal core carrier. -/
theorem quat_norm_mul (a b : ℝ) (v w : Vec3) :
    (a * b - h3 v w) ^ 2
        + h3 (a • w + b • v + spCross v w) (a • w + b • v + spCross v w)
      = (a ^ 2 + h3 v v) * (b ^ 2 + h3 w w) := by
  simp only [h3, dot3, spCross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- **PACKAGE C.**  The internal core carrier is closed under the inherited product. -/
theorem Lift_mul_mem {u u' : W} (hu : u ∈ Lift) (hu' : u' ∈ Lift) : u ⋆ u' ∈ Lift := by
  obtain ⟨a, v, ha, rfl⟩ := hu
  obtain ⟨b, w, hb, rfl⟩ := hu'
  refine ⟨a * b - h3 v w, a • w + b • v + spCross v w, ?_, quat_mul a b v w⟩
  rw [quat_norm_mul a b v w, ha, hb]
  ring

/-- **PACKAGE C.**  The internal core carrier is closed under inherited inversion: every
element has a two-sided inverse inside the carrier, given by the explicit reflection of the
generator part. -/
theorem Lift_inv_mem {u : W} (hu : u ∈ Lift) :
    ∃ u' ∈ Lift, u ⋆ u' = w1 ∧ u' ⋆ u = w1 := by
  obtain ⟨a, v, ha, rfl⟩ := hu
  refine ⟨a • w1 + Jmap v, ⟨a, -v, by simpa [h3, dot3] using ha, by rw [Jmap_neg]; module⟩,
    ?_, ?_⟩
  · have h1 : a • w1 + Jmap v = a • w1 - Jmap (-v) := by rw [Jmap_neg]; module
    rw [h1, quat_mul a a v (-v)]
    have hv : h3 v (-v) = -h3 v v := by simp [h3, dot3]; ring
    have hc : a • (-v) + a • v + spCross v (-v) = 0 := by
      simp only [spCross]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [Prod.smul_def] <;> ring
    rw [hv, hc, Jmap_zero]
    have : a * a - -h3 v v = 1 := by nlinarith [ha]
    rw [this]
    module
  · have h1 : a • w1 + Jmap v = a • w1 - Jmap (-v) := by rw [Jmap_neg]; module
    rw [h1, quat_mul a a (-v) v]
    have hv : h3 (-v) v = -h3 v v := by simp [h3, dot3]; ring
    have hc : a • v + a • (-v) + spCross (-v) v = 0 := by
      simp only [spCross]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [Prod.smul_def] <;> ring
    rw [hv, hc, Jmap_zero]
    have : a * a - -h3 v v = 1 := by nlinarith [ha]
    rw [this]
    module

/-! ## The internal core carrier is exactly the set of reference implementers -/

/-- **PACKAGE C, principal.**  The intrinsic normal-form description of the internal core
carrier coincides exactly with the set of inherited reference implementers.  In particular
`Lift` is the smallest set containing all `Un n θ` and closed under product and inversion,
and it is generated by the reference implementers alone. -/
theorem Lift_repr_Icc {u : W} (hu : u ∈ Lift) :
    ∃ (n : Vec3) (ψ : ℝ), IsUnitAxis n ∧ 0 ≤ ψ ∧ ψ ≤ 2 * Real.pi ∧ u = Un n ψ := by
  obtain ⟨a, v, ha, rfl⟩ := hu
  have hv0 : 0 ≤ h3 v v := h3_self_nonneg v
  have ha1 : a ^ 2 ≤ 1 := by linarith
  have hle : -1 ≤ a ∧ a ≤ 1 := by
    constructor <;> nlinarith [ha1]
  set ψ : ℝ := 2 * Real.arccos a with hψ
  have hhalf : ψ / 2 = Real.arccos a := by rw [hψ]; ring
  have hψ0 : 0 ≤ ψ := by rw [hψ]; linarith [Real.arccos_nonneg a]
  have hψ2 : ψ ≤ 2 * Real.pi := by rw [hψ]; linarith [Real.arccos_le_pi a]
  have hcos : Real.cos (ψ / 2) = a := by rw [hhalf, Real.cos_arccos hle.1 hle.2]
  have hsin : Real.sin (ψ / 2) = Real.sqrt (h3 v v) := by
    rw [hhalf, Real.sin_arccos]
    congr 1
    nlinarith [ha]
  by_cases hv : v = 0
  · subst hv
    refine ⟨e1, ψ, e1_isUnitAxis, hψ0, hψ2, ?_⟩
    rw [Un, hcos, hsin]
    simp [h3, dot3, Jmap_zero]
  · have hpos : 0 < h3 v v := lt_of_le_of_ne hv0 (fun h => hv ((h3_self_eq_zero_iff v).1 h.symm))
    set s : ℝ := Real.sqrt (h3 v v) with hs
    have hspos : 0 < s := Real.sqrt_pos.2 hpos
    have hsq : s ^ 2 = h3 v v := Real.sq_sqrt (le_of_lt hpos)
    refine ⟨s⁻¹ • v, ψ, ?_, hψ0, hψ2, ?_⟩
    · show h3 (s⁻¹ • v) (s⁻¹ • v) = 1
      have : h3 (s⁻¹ • v) (s⁻¹ • v) = s⁻¹ ^ 2 * h3 v v := by
        simp only [h3, dot3]; simp [Prod.smul_def]; ring
      rw [this, ← hsq]
      field_simp
    · rw [Un, hcos, hsin, Jmap_linear.2]
      have : s • (s⁻¹ • Jmap v) = Jmap v := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hspos), one_smul]
      rw [this]

/-- **PACKAGE C, principal.**  The intrinsic normal-form description of the internal core
carrier coincides exactly with the set of inherited reference implementers. -/
theorem mem_Lift_iff_exists_Un (u : W) :
    u ∈ Lift ↔ ∃ (n : Vec3) (θ : ℝ), IsUnitAxis n ∧ u = Un n θ := by
  constructor
  · intro hu
    obtain ⟨n, ψ, hn, -, -, h⟩ := Lift_repr_Icc hu
    exact ⟨n, ψ, hn, h⟩
  · rintro ⟨n, θ, hn, rfl⟩
    exact Un_mem_Lift hn θ

/-! ## The central factors -/

/-- **DERIVED.**  Elements of the inherited central plane commute with everything. -/
theorem zc_central (a b : ℝ) (x : W) : zc a b ⋆ x = x ⋆ zc a b := by
  rw [zc, add_mul_W, mul_add_W, smul_mul_W, smul_mul_W, mul_smul_W, mul_smul_W, one_mul_W,
    mul_one_W, wS_central]

/-- **NEUTRAL DEFINITION (Package C).**  The invertible elements of the exact centre. -/
def CUnit : Set W := {z : W | ∃ a b : ℝ, ¬ (a = 0 ∧ b = 0) ∧ z = zc a b}

theorem w1_mem_CUnit : w1 ∈ CUnit := ⟨1, 0, by norm_num, by rw [zc_one_zero]⟩

theorem CUnit_mul_mem {z z' : W} (hz : z ∈ CUnit) (hz' : z' ∈ CUnit) : z ⋆ z' ∈ CUnit := by
  obtain ⟨a, b, hab, rfl⟩ := hz
  obtain ⟨c, d, hcd, rfl⟩ := hz'
  refine ⟨a * c - b * d, a * d + b * c, ?_, zc_mul_zc a b c d⟩
  rintro ⟨h1, h2⟩
  have hab' : 0 < a ^ 2 + b ^ 2 := by
    rcases not_and_or.1 hab with h | h
    · have := sq_nonneg b; positivity
    · have := sq_nonneg a; positivity
  have hcd' : 0 < c ^ 2 + d ^ 2 := by
    rcases not_and_or.1 hcd with h | h
    · have := sq_nonneg d; positivity
    · have := sq_nonneg c; positivity
  nlinarith [h1, h2, hab', hcd']

theorem CUnit_inv_mem {z : W} (hz : z ∈ CUnit) : ∃ z' ∈ CUnit, z ⋆ z' = w1 ∧ z' ⋆ z = w1 := by
  obtain ⟨a, b, hab, rfl⟩ := hz
  have hpos : 0 < a ^ 2 + b ^ 2 := by
    rcases not_and_or.1 hab with h | h
    · have := sq_nonneg b; positivity
    · have := sq_nonneg a; positivity
  refine ⟨zc (a / (a ^ 2 + b ^ 2)) (-b / (a ^ 2 + b ^ 2)), ⟨_, _, ?_, rfl⟩, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    have ha : a = 0 := by
      field_simp at h1
      linarith [h1]
    have hb : b = 0 := by
      field_simp at h2
      linarith [h2]
    exact hab ⟨ha, hb⟩
  · rw [zc_mul_zc]
    have e1' : a * (a / (a ^ 2 + b ^ 2)) - b * (-b / (a ^ 2 + b ^ 2)) = 1 := by
      field_simp; ring
    have e2' : a * (-b / (a ^ 2 + b ^ 2)) + b * (a / (a ^ 2 + b ^ 2)) = 0 := by
      field_simp
      ring
    rw [e1', e2', zc_one_zero]
  · rw [zc_mul_zc]
    have e1' : a / (a ^ 2 + b ^ 2) * a - -b / (a ^ 2 + b ^ 2) * b = 1 := by
      field_simp; ring
    have e2' : a / (a ^ 2 + b ^ 2) * b + -b / (a ^ 2 + b ^ 2) * a = 0 := by
      field_simp
      ring
    rw [e1', e2', zc_one_zero]

/-! ## The full internal carrier -/

/-- **NEUTRAL DEFINITION (Package C).**  The full internal carrier: invertible central
factors times elements of the internal core carrier.  No central factor is discarded. -/
def LiftZ : Set W := {u : W | ∃ z ∈ CUnit, ∃ g ∈ Lift, u = z ⋆ g}

theorem Lift_subset_LiftZ : Lift ⊆ LiftZ := fun g hg =>
  ⟨w1, w1_mem_CUnit, g, hg, (one_mul_W g).symm⟩

theorem CUnit_subset_LiftZ : CUnit ⊆ LiftZ := fun z hz =>
  ⟨z, hz, w1, w1_mem_Lift, (mul_one_W z).symm⟩

/-- **PACKAGE C.**  The full internal carrier is closed under the inherited product. -/
theorem LiftZ_mul_mem {u u' : W} (hu : u ∈ LiftZ) (hu' : u' ∈ LiftZ) : u ⋆ u' ∈ LiftZ := by
  obtain ⟨z, hz, g, hg, rfl⟩ := hu
  obtain ⟨z', hz', g', hg', rfl⟩ := hu'
  refine ⟨z ⋆ z', CUnit_mul_mem hz hz', g ⋆ g', Lift_mul_mem hg hg', ?_⟩
  obtain ⟨c, d, -, rfl⟩ := hz'
  rw [mul_assoc_W, ← mul_assoc_W g (zc c d) g', ← zc_central c d g, mul_assoc_W,
    ← mul_assoc_W]

/-- **PACKAGE C.**  The full internal carrier is closed under inherited inversion. -/
theorem LiftZ_inv_mem {u : W} (hu : u ∈ LiftZ) :
    ∃ u' ∈ LiftZ, u ⋆ u' = w1 ∧ u' ⋆ u = w1 := by
  obtain ⟨z, hz, g, hg, rfl⟩ := hu
  obtain ⟨zi, hzi, hz1, hz2⟩ := CUnit_inv_mem hz
  obtain ⟨gi, hgi, hg1, hg2⟩ := Lift_inv_mem hg
  refine ⟨zi ⋆ gi, ⟨zi, hzi, gi, hgi, rfl⟩, ?_, ?_⟩
  · obtain ⟨c, d, -, rfl⟩ := hzi
    calc (z ⋆ g) ⋆ (zc c d ⋆ gi) = (z ⋆ zc c d) ⋆ (g ⋆ gi) := by
          rw [mul_assoc_W, ← mul_assoc_W g (zc c d) gi, ← zc_central c d g, mul_assoc_W,
            ← mul_assoc_W]
      _ = w1 := by rw [hz1, hg1, mul_one_W]
  · obtain ⟨c, d, -, rfl⟩ := hz
    calc (zi ⋆ gi) ⋆ (zc c d ⋆ g) = (zi ⋆ zc c d) ⋆ (gi ⋆ g) := by
          rw [mul_assoc_W, ← mul_assoc_W gi (zc c d) g, ← zc_central c d gi, mul_assoc_W,
            ← mul_assoc_W]
      _ = w1 := by rw [hz2, hg2, mul_one_W]

end NullSectorTask20
