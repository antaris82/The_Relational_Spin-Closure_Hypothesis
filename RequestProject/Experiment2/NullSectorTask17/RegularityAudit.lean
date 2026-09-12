import RequestProject.Experiment2.NullSectorTask17.Reconstruction

/-!
# Task 17, Package G: the stronger regularity audit

Only now, after the continuous local classification is complete (Packages B–E), is a
strictly stronger regularity notion introduced (§57): a family is *jointly `C¹`* when it is
jointly regular and its two recovered rate functions are restrictions of continuously
differentiable functions of the direction.

The audit result (§58, §59) is an **equivalence**, not a heuristic remark:

* every explicit local model is jointly `C¹`, so the set of admissible integer labels on an
  inherited domain is the same for the `C¹` and for the continuous classification;
* the `C¹` local classification theorem is literally the continuous one;
* the overlap factors between `C¹` representatives are the same central elements as before;
* the admissible domains are unchanged: every antipodal-free domain, and also the
  antipodal two-point domain, carries a `C¹` exact representative.

Hence joint `C¹` regularity restricts neither labels, nor domains, nor overlap factors.
-/

namespace NullSectorTask17

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16

/-! ## §57 — the stronger notion -/

/-- **NEUTRAL DEFINITION (§57).**  A jointly `C¹` family: jointly regular, and presented by
two continuously differentiable rate functions of the direction.  This is introduced only
after the continuous classification is complete. -/
def IsC1JointlyRegularFamily (U : Vec3 → ℝ → W) : Prop :=
  IsJointlyRegularFamily U ∧ ∃ a b : Vec3 → ℝ, ContDiff ℝ 1 a ∧ ContDiff ℝ 1 b ∧
    ∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, U n θ = zexp (a n) (b n) θ ⋆ Un n θ

theorem IsC1JointlyRegularFamily.toJointlyRegular {U : Vec3 → ℝ → W}
    (h : IsC1JointlyRegularFamily U) : IsJointlyRegularFamily U := h.1

/-! ## §58 — the labels are unchanged -/

/-- **DERIVED (§58).**  Every explicit local model is jointly `C¹`. -/
theorem locFam_c1 (k : ℤ) : IsC1JointlyRegularFamily (locFam k) :=
  ⟨locFam_jointlyRegular k, fun _ => 0, fun _ => (k : ℝ) + 1 / 2, contDiff_const,
    contDiff_const, fun _ _ _ => rfl⟩

/-- **PRINCIPAL THEOREM (§58), labels.**  On a nonempty inherited domain the integer labels
realized by jointly `C¹` exact representatives are exactly the integer labels realized by
jointly regular (continuous) exact representatives: all of `ℤ`. -/
theorem c1_labels_unrestricted (v : Vec3) (k : ℤ) :
    IsC1JointlyRegularFamily (locFam k) ∧ IsTransformationValuedOn (Dom v) (locFam k) ∧
      ∀ n ∈ Dom v, rateBeta (locFam k) n = (k : ℝ) + 1 / 2 :=
  ⟨locFam_c1 k, locFam_transformationValuedOn k v, fun _ hn => (locFam_rates k hn.1).2⟩

/-- **PRINCIPAL THEOREM (§59).**  The `C¹` local classification is *equivalent* to the
continuous one: a jointly `C¹` family is exact on a nonempty inherited domain iff it
coincides there with exactly one explicit local model — the same statement, with the same
label set, as the continuous classification. -/
theorem c1_local_family_classification {U : Vec3 → ℝ → W} (hU : IsC1JointlyRegularFamily U)
    {v : Vec3} (hv : v ≠ 0) :
    IsTransformationValuedOn (Dom v) U ↔ ∃! k : ℤ, ∀ n ∈ Dom v, ∀ θ : ℝ,
      U n θ = locFam k n θ :=
  local_family_classification hU.toJointlyRegular hv

/-! ## §58 — the domains are unchanged -/

/-- **PRINCIPAL THEOREM (§58), domains.**  Every antipodal-free set of unit directions
carries a jointly `C¹` exact representative, so the stronger regularity does not shrink the
class of admissible domains. -/
theorem c1_antipodalFree_admissible {D : Set Vec3} (hunit : ∀ n ∈ D, IsUnitAxis n)
    (hfree : AntipodalFree D) :
    ∃ U : Vec3 → ℝ → W, IsC1JointlyRegularFamily U ∧ IsTransformationValuedOn D U :=
  ⟨locFam 0, locFam_c1 0, (antipodalFree_admissible hunit hfree).1 0⟩

/-- **PRINCIPAL THEOREM (§58), domains with an antipodal pair.**  The two-point admissible
domain of Package D also carries a jointly `C¹` exact representative: its rate function is
linear in the direction. -/
theorem c1_antipodal_pair_admissible {n : Vec3} (hn : IsUnitAxis n) :
    ∃ U : Vec3 → ℝ → W, IsC1JointlyRegularFamily U ∧
      IsTransformationValuedOn ({n, -n} : Set Vec3) U := by
  classical
  set b : Vec3 → ℝ := fun m => (1 / 2) * h3 m n with hb
  have hnnu : IsUnitAxis (-n) := isUnitAxis_neg hn
  have hnn : h3 n n = 1 := hn
  have hbn : b n = 1 / 2 := by
    have hval : b n = 1 / 2 * h3 n n := rfl
    rw [hval, hnn]; ring
  have hbneg : b (-n) = -(1 / 2) := by
    have hval : b (-n) = 1 / 2 * h3 (-n) n := rfl
    rw [hval, h3_neg_self hn]; ring
  have hunit : ∀ m ∈ ({n, -n} : Set Vec3), IsUnitAxis m := by
    rintro m (rfl | rfl)
    · exact hn
    · exact hnnu
  have hhalf : ∀ m ∈ ({n, -n} : Set Vec3), ∃ k : ℤ, b m = (k : ℝ) + 1 / 2 := by
    rintro m (rfl | rfl)
    · exact ⟨0, by rw [hbn]; norm_num⟩
    · exact ⟨-1, by rw [hbneg]; norm_num⟩
  have hodd : ∀ m ∈ ({n, -n} : Set Vec3), -m ∈ ({n, -n} : Set Vec3) → b (-m) = -b m := by
    rintro m (rfl | rfl) -
    · rw [hbn, hbneg]
    · rw [neg_neg, hbn, hbneg]; ring
  have hcontb : Continuous fun s : Sph => b (s : Vec3) :=
    continuous_const.mul ((continuous_h3_left n).comp continuous_subtype_val)
  have hsmooth : ContDiff ℝ 1 b := by
    have hlin : ContDiff ℝ 1 fun m : Vec3 => h3 m n := by
      simp only [h3, dot3]
      have h1 : ContDiff ℝ 1 fun m : Vec3 => m.1 := contDiff_fst
      have h2 : ContDiff ℝ 1 fun m : Vec3 => m.2.1 := contDiff_snd.fst
      have h3' : ContDiff ℝ 1 fun m : Vec3 => m.2.2 := contDiff_snd.snd
      exact ((h1.mul contDiff_const).add (h2.mul contDiff_const)).add (h3'.mul contDiff_const)
    exact contDiff_const.mul hlin
  refine ⟨famOf (fun _ => 0) b, ⟨jointlyRegular_famOf continuous_const hcontb,
    fun _ => 0, b, contDiff_const, hsmooth, fun m _ θ => rfl⟩,
    famOfZ_exact_on hunit hhalf hodd⟩

/-! ## §58 — the overlap factors are unchanged -/

/-- **PRINCIPAL THEOREM (§58), overlap factors.**  The transition factor between two
jointly `C¹` exact representatives on domains containing the direction is the same central
one-parameter element attached to an integer as in the continuous classification. -/
theorem c1_overlap_same {U V : Vec3 → ℝ → W} (hU : IsC1JointlyRegularFamily U)
    (hV : IsC1JointlyRegularFamily V) {DU DV : Set Vec3}
    (hexU : IsTransformationValuedOn DU U) (hexV : IsTransformationValuedOn DV V)
    {n : Vec3} (hnU : n ∈ DU) (hnV : n ∈ DV) (hn : IsUnitAxis n) :
    ∃ j : ℤ, ∀ θ : ℝ, ovl U V n θ = zexp 0 (j : ℝ) θ :=
  ovl_integer hU.toJointlyRegular hV.toJointlyRegular hexU hexV hnU hnV hn

end NullSectorTask17
