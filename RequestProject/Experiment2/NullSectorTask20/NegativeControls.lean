import RequestProject.Experiment2.NullSectorTask20.SectionObstruction

/-!
# Task 20, Layer 8 (Package L): anti-overclaim controls

Phase A only.  Each control below is a *formal* statement blocking one of the inferences
prohibited by Package L.  None of them mentions any conventional structure; each is a
theorem about the reconstructed objects that would have to be false if the corresponding
naive identification were made.

1. *Two-valuedness does not determine the kernel.*  The kernel of the projection on the
   internal core carrier has exactly two elements, but the kernel of the projection on the
   full internal carrier — the carrier one is forced to use if no central factor is
   discarded — is a strictly larger set containing a continuous injective one-parameter
   family.  So "there is a two-valued ambiguity" is *not* enough to pin down the internal
   object.
2. *A shared central sign does not determine the label.*  All allowed labels give the same
   value after a full turn, yet distinct labels give genuinely distinct central factors.
3. *Reduction of the relative integer data loses information.*
4. *Set-theoretic direction coverage is strictly weaker than relation completeness.*
5. *The internal choice exists; only continuity fails.*  So no nonexistence statement here
   may be read as a set-theoretic impossibility.
6. *The discrete rate set is not the source of the global obstruction*: the obstruction
   already holds for the non-discrete family of strictly positive rates.
-/

namespace NullSectorTask20

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19

/-- **PACKAGE L, principal.**  The six anti-overclaim controls, collected. -/
theorem anti_overclaim_controls :
    (({w1, -w1} : Set W) ⊂ CentreOf LiftZ) ∧
      (Continuous (fun t : ℝ => zexp 1 0 t) ∧ Function.Injective (fun t : ℝ => zexp 1 0 t) ∧
        ∀ t : ℝ, zexp 1 0 t ∈ CUnit ∧ proj (zexp 1 0 t) = LinearMap.id) ∧
      (∃ b b' : ℝ, b ∈ HalfOddSet ∧ b' ∈ HalfOddSet ∧ (∃ k : ℤ, b' = b + 2 * (k : ℝ)) ∧
        (∃ θ : ℝ, labelBridge b θ ≠ labelBridge b' θ) ∧
        labelBridge b (2 * Real.pi) = labelBridge b' (2 * Real.pi)) ∧
      (CoversDirections Dom ∧ ¬ SystemRelationComplete Dom inhSystem) ∧
      (∃ σ : VisParam → W, (∀ p : VisParam, σ p ∈ Lift) ∧
        (∀ p : VisParam, proj (σ p) = visMap p) ∧
        (∀ p q : VisParam, visRel p q → σ p = σ q)) ∧
      ¬ ∃ b : Vec3 → ℝ, RateCont b ∧ RateRev b ∧ ∀ n : Vec3, IsUnitAxis n → 0 < b n := by
  refine ⟨?_, kernel_full_continuum, reduction_loses_information, ?_,
    exists_quotient_compatible_lift, no_positive_odd_rate⟩
  · rw [centre_LiftZ]; exact kernel_core_ssubset_kernel_full
  · exact ⟨coverage_not_relationComplete.1, coverage_not_relationComplete.2.2.2⟩

end NullSectorTask20
