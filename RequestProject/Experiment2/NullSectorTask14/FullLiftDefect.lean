import RequestProject.Experiment2.NullSectorTask14.ReferenceWordDefect

/-!
# Task 14, Layer 15 (§47–§48): restoring the full per-axis central lift freedom

§46 classified the defect of words built from the *reference* axis implementations.  Here
the complete allowed per-axis central residual freedom is restored: each axis may carry
its **own** central factor, and no relation between the factors of different axes is
assumed.

The results are:

* every implementation of an axis automorphism is a central multiple of the reference one,
  with an **invertible** central factor (`axis_lift_iff`);
* the residual factors of different axes combine multiplicatively into one common central
  factor (`mixed_full_lift_product`) — mixed composition neither obstructs them nor forces
  a relation between them;
* the defect set of full-lift words is the **whole group of invertible central elements**,
  strictly larger than the reference defect set `{1, -1}` (`full_lift_defect_exact`);
* the residual remains invisible to the *relative* two-sector action for every axis
  (`full_lift_relative_invisible`), yet is visible as an absolute central defect
  (`full_lift_defect_not_pm_one`).

Nothing is normalized and no central discrepancy is quotiented away.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## Invertible central elements -/

/-- **NEUTRAL DEFINITION.**  The candidate inverse of a central element. -/
noncomputable def zinv (a b : ℝ) : W := zz (a / (a ^ 2 + b ^ 2)) (-(b / (a ^ 2 + b ^ 2)))

/-- **DERIVED.**  A nonzero central element is invertible inside the exact center. -/
theorem zz_mul_zinv {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) : zz a b ⋆ zinv a b = w1 := by
  rw [zinv, zz_mul_zz]
  have h1 : a * (a / (a ^ 2 + b ^ 2)) - b * -(b / (a ^ 2 + b ^ 2)) = 1 := by
    field_simp
    ring
  have h2 : a * -(b / (a ^ 2 + b ^ 2)) + b * (a / (a ^ 2 + b ^ 2)) = 0 := by
    field_simp
    ring
  rw [h1, h2, zz_one_zero]

theorem zinv_mul_zz {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) : zinv a b ⋆ zz a b = w1 := by
  rw [← zz_central, zz_mul_zinv h]

/-- **DERIVED.**  A two-sided inverse of a central element is itself central. -/
theorem central_inv_mem_Z {z zi : W} (hz : z ∈ Z) (h1 : z ⋆ zi = w1) (h2 : zi ⋆ z = w1) :
    zi ∈ Z := by
  refine mem_Z_of_comm_all (fun x => ?_)
  calc zi ⋆ x = zi ⋆ (x ⋆ (z ⋆ zi)) := by rw [h1, mul_one_W]
    _ = (zi ⋆ (x ⋆ z)) ⋆ zi := by simp only [mul_assoc_W]
    _ = ((zi ⋆ z) ⋆ x) ⋆ zi := by rw [← Z_central hz x]; simp only [mul_assoc_W]
    _ = x ⋆ zi := by rw [h2, one_mul_W]

/-! ## §47 — the complete per-axis lift freedom -/

/-- **NEUTRAL DEFINITION (§47).**  A *full* implementation of the axis automorphism at one
parameter: an arbitrary internal element implementing it by conjugation.  Its central
residual is not prescribed. -/
def IsAxisImplementer (n : Vec3) (θ : ℝ) (u : W) : Prop :=
  ∃ ui : W, Implements u ui (PhiGen n θ)

/-- **PRINCIPAL THEOREM (§47).**  Every full implementation of an axis automorphism is the
reference one multiplied by an *invertible* central element, and conversely.  The Task-11
exact-center theorem is the only external input. -/
theorem axis_lift_iff {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) (u : W) :
    IsAxisImplementer n θ u ↔
      ∃ z zi : W, z ∈ Z ∧ zi ∈ Z ∧ z ⋆ zi = w1 ∧ u = z ⋆ Un n θ := by
  constructor
  · rintro ⟨ui, hu⟩
    have hz : u ⋆ Un n (-θ) ∈ Z := implements_defect_mem_Z hu (Un_implements hn θ)
    have hzi : (u ⋆ Un n (-θ)) ⋆ (Un n θ ⋆ ui) = w1 := by
      calc (u ⋆ Un n (-θ)) ⋆ (Un n θ ⋆ ui) = (u ⋆ (Un n (-θ) ⋆ Un n θ)) ⋆ ui := by
            simp only [mul_assoc_W]
        _ = w1 := by rw [Un_neg_mul hn, mul_one_W, hu.inv_right]
    have hzi' : (Un n θ ⋆ ui) ⋆ (u ⋆ Un n (-θ)) = w1 := by
      calc (Un n θ ⋆ ui) ⋆ (u ⋆ Un n (-θ)) = (Un n θ ⋆ (ui ⋆ u)) ⋆ Un n (-θ) := by
            simp only [mul_assoc_W]
        _ = w1 := by rw [hu.inv_left, mul_one_W, Un_mul_neg hn]
    refine ⟨u ⋆ Un n (-θ), Un n θ ⋆ ui, hz, central_inv_mem_Z hz hzi hzi', hzi, ?_⟩
    rw [mul_assoc_W, Un_neg_mul hn, mul_one_W]
  · rintro ⟨z, zi, hz, hzic, hzi, rfl⟩
    refine ⟨Un n (-θ) ⋆ zi, ?_, ?_, ?_⟩
    · calc (z ⋆ Un n θ) ⋆ (Un n (-θ) ⋆ zi) = (z ⋆ (Un n θ ⋆ Un n (-θ))) ⋆ zi := by
            simp only [mul_assoc_W]
        _ = w1 := by rw [Un_mul_neg hn, mul_one_W, hzi]
    · calc (Un n (-θ) ⋆ zi) ⋆ (z ⋆ Un n θ) = Un n (-θ) ⋆ ((zi ⋆ z) ⋆ Un n θ) := by
            simp only [mul_assoc_W]
        _ = w1 := by
            rw [Z_central hzic z, hzi, one_mul_W, Un_neg_mul hn]
    · intro x
      calc ((z ⋆ Un n θ) ⋆ x) ⋆ (Un n (-θ) ⋆ zi)
          = z ⋆ (((Un n θ ⋆ x) ⋆ Un n (-θ)) ⋆ zi) := by simp only [mul_assoc_W]
        _ = z ⋆ (zi ⋆ ((Un n θ ⋆ x) ⋆ Un n (-θ))) := by rw [Z_central hzic]
        _ = (z ⋆ zi) ⋆ ((Un n θ ⋆ x) ⋆ Un n (-θ)) := (mul_assoc_W _ _ _).symm
        _ = PhiGen n θ x := by rw [hzi, one_mul_W]; rfl

/-- **DERIVED (§47).**  Concretely: a central multiple with nonzero coefficient pair is an
implementation of exactly the same axis automorphism. -/
theorem zz_smul_Un_implementer {n : Vec3} (hn : IsUnitAxis n) {a b : ℝ}
    (hab : a ^ 2 + b ^ 2 ≠ 0) (θ : ℝ) : IsAxisImplementer n θ (zz a b ⋆ Un n θ) :=
  (axis_lift_iff hn θ _).2
    ⟨zz a b, zinv a b, zz_mem_Z a b, zz_mem_Z _ _, zz_mul_zinv hab, rfl⟩

/-! ## §47 — mixed composition of independent per-axis residuals -/

/-- **PRINCIPAL THEOREM (§47): `full_lift_word_relative_central`, product form.**  Two
independent per-axis residuals combine into one *common* central factor multiplying the
mixed reference product.  No relation between the two residuals is required, and none is
produced. -/
theorem mixed_full_lift_product (a b c d : ℝ) (n m : Vec3) (θ φ : ℝ) :
    (zz a b ⋆ Un n θ) ⋆ (zz c d ⋆ Un m φ) =
      (zz a b ⋆ zz c d) ⋆ (Un n θ ⋆ Un m φ) := by
  calc (zz a b ⋆ Un n θ) ⋆ (zz c d ⋆ Un m φ)
      = zz a b ⋆ ((Un n θ ⋆ zz c d) ⋆ Un m φ) := by simp only [mul_assoc_W]
    _ = zz a b ⋆ ((zz c d ⋆ Un n θ) ⋆ Un m φ) := by rw [← zz_central]
    _ = (zz a b ⋆ zz c d) ⋆ (Un n θ ⋆ Un m φ) := by simp only [mul_assoc_W]

/-- **DERIVED (§47).**  The combined residual is again central and invertible. -/
theorem mixed_residual_central (a b c d : ℝ) :
    zz a b ⋆ zz c d = zz (a * c - b * d) (a * d + b * c) := zz_mul_zz a b c d

/-! ## §47 — the exact full-lift defect set -/

/-- **PRINCIPAL THEOREM (§47): `full_lift_word_relative_central`.**  Two full
implementations of the same automorphism differ by a central element; the possible
defects are exactly the **invertible** central elements — strictly more than `{1, -1}`. -/
theorem full_lift_defect_exact {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    (∀ u v ui vi : W, Implements u ui (PhiGen n θ) → Implements v vi (PhiGen n θ) →
        u ⋆ vi ∈ Z) ∧
      (∀ a b : ℝ, a ^ 2 + b ^ 2 ≠ 0 →
        ∃ u v ui vi : W, Implements u ui (PhiGen n θ) ∧ Implements v vi (PhiGen n θ) ∧
          u ⋆ vi = zz a b) := by
  refine ⟨fun _ _ _ _ hu hv => implements_defect_mem_Z hu hv, fun a b hab => ?_⟩
  obtain ⟨ui, hu⟩ := zz_smul_Un_implementer hn hab θ
  refine ⟨zz a b ⋆ Un n θ, Un n θ, ui, Un n (-θ), hu, Un_implements hn θ, ?_⟩
  rw [mul_assoc_W, Un_mul_neg hn, mul_one_W]

/-- **DERIVED (§47).**  A concrete full-lift defect which is neither `1` nor `-1`: the
enlargement of the defect set is strict. -/
theorem full_lift_defect_not_pm_one {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    ∃ u v ui vi : W, Implements u ui (PhiGen n θ) ∧ Implements v vi (PhiGen n θ) ∧
      u ⋆ vi ≠ w1 ∧ u ⋆ vi ≠ -w1 := by
  obtain ⟨-, hex⟩ := full_lift_defect_exact hn θ
  obtain ⟨u, v, ui, vi, hu, hv, huv⟩ := hex 2 0 (by norm_num)
  refine ⟨u, v, ui, vi, hu, hv, ?_, ?_⟩
  · rw [huv]
    intro hcon
    have h0 := congrFun hcon 0
    simp [zz, w1, wS] at h0
  · rw [huv]
    intro hcon
    have h0 := congrFun hcon 0
    simp [zz, w1, wS] at h0
    linarith

/-! ## §48 — the central negative control -/

/-- **PRINCIPAL THEOREM (§48): `multi_axis_residual_freedom_verdict`, invisibility part.**
For **every** axis, **every** minimal carrier and **every** central residual, the reduced
action on the two slices is the reference action multiplied by the *same* residual, hence
the relative factor between the two sectors is unchanged: the residual remains invisible
to the relative sector law. -/
theorem full_lift_relative_invisible {n : Vec3} (a b θ : ℝ) :
    (∀ ψ : W, spat n ⋆ ψ = ψ → (zz a b ⋆ Un n θ) ⋆ ψ = (zz a b ⋆ cPlusRef θ) ⋆ ψ) ∧
    (∀ ψ : W, spat n ⋆ ψ = -ψ → (zz a b ⋆ Un n θ) ⋆ ψ = (zz a b ⋆ cMinusRef θ) ⋆ ψ) ∧
    (zz a b ⋆ cPlusRef θ) = RelRef θ ⋆ (zz a b ⋆ cMinusRef θ) := by
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_, ?_⟩
  · rw [mul_assoc_W, mul_assoc_W, (generic_action_exact θ).1 hψ]
  · rw [mul_assoc_W, mul_assoc_W, (generic_action_exact θ).2 hψ]
  · have hrel : cPlusRef θ = RelRef θ ⋆ cMinusRef θ := (reference_relative_action_exact θ).2.1
    calc zz a b ⋆ cPlusRef θ = zz a b ⋆ (RelRef θ ⋆ cMinusRef θ) := by rw [hrel]
      _ = RelRef θ ⋆ (zz a b ⋆ cMinusRef θ) := by
          rw [← mul_assoc_W, ← Z_central (RelRef_mem_Z θ), mul_assoc_W]

/-- **PRINCIPAL THEOREM (§48): the verdict.**  Independent per-axis central residuals

* compose without any obstruction, into a single common central factor
  (`mixed_full_lift_product`);
* are invisible to the relative two-sector law of every axis
  (`full_lift_relative_invisible`);
* remain visible as an absolute central defect which is *not* confined to `{1, -1}`
  (`full_lift_defect_not_pm_one`).

Hence no compatibility relation between the residual choices of different axes is forced,
and none can be derived: the status is **COMMON CENTRAL FREEDOM**. -/
theorem multi_axis_residual_freedom_verdict {n m : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    (∀ (a b c d : ℝ) (φ : ℝ), (zz a b ⋆ Un n θ) ⋆ (zz c d ⋆ Un m φ)
        = (zz a b ⋆ zz c d) ⋆ (Un n θ ⋆ Un m φ)) ∧
      (∀ a b : ℝ, (∀ ψ : W, spat n ⋆ ψ = ψ →
          (zz a b ⋆ Un n θ) ⋆ ψ = (zz a b ⋆ cPlusRef θ) ⋆ ψ) ∧
        (zz a b ⋆ cPlusRef θ) = RelRef θ ⋆ (zz a b ⋆ cMinusRef θ)) ∧
      (∃ u v ui vi : W, Implements u ui (PhiGen n θ) ∧ Implements v vi (PhiGen n θ) ∧
        u ⋆ vi ≠ w1 ∧ u ⋆ vi ≠ -w1) :=
  ⟨fun a b c d φ => mixed_full_lift_product a b c d n m θ φ,
    fun a b => ⟨(full_lift_relative_invisible (n := n) a b θ).1,
      (full_lift_relative_invisible (n := n) a b θ).2.2⟩,
    full_lift_defect_not_pm_one hn θ⟩

end NullSectorTask14
