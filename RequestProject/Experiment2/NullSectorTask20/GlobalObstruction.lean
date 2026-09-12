import RequestProject.Experiment2.NullSectorTask20.ReversalQuotient

/-!
# Task 20, Layer 6 (Package G): the obstruction re-expressed, and its minimal form

Phase A only.  The three inherited rate conditions are frozen unchanged
(`RateCont`, `RateHalfOdd`, `RateRev`), and the inherited minimality theorem — the three are
jointly unsatisfiable while every proper subset is realizable — is preserved by re-export.

The new content is the answer to items 62 and 63:

* the **smallest intrinsic statement** from which the nonexistence results follow is
  `exists_zero_of_odd`: a continuous real rate that is odd under reversal has a zero.  It
  uses only preconnectedness of the direction carrier and the involution;
* consequently the discrete half-odd restriction is **not essential**: the obstruction holds
  verbatim for *any* value set avoiding zero, discrete or not, and the explicit non-discrete
  instance (strictly positive rates) is recorded;
* what the half-odd set contributes is exactly one thing: it avoids zero.  Removing that
  single feature makes the obstruction disappear (the identically vanishing rate).
-/

namespace NullSectorTask20

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19

/-! ## Item 62 — the minimal intrinsic statement -/

/-- **PACKAGE G (item 62), principal.**  The minimal intrinsic obstruction: no continuous
reversal-odd rate can avoid the value zero.  Neither discreteness nor any arithmetic property
of the value set is used. -/
theorem no_continuous_odd_rate_avoiding_zero {S : Set ℝ} (h0 : (0 : ℝ) ∉ S) :
    ¬ ∃ b : Vec3 → ℝ, RateCont b ∧ RateRev b ∧ ∀ n : Vec3, IsUnitAxis n → b n ∈ S := by
  rintro ⟨b, hcont, hrev, hval⟩
  obtain ⟨s, hs⟩ := exists_zero_of_odd (f := fun s : Sph => b (s : Vec3)) hcont
    (fun s => by simpa [negSph] using hrev (s : Vec3) s.2)
  exact h0 (hs ▸ hval (s : Vec3) s.2)

/-- **PACKAGE G (item 63), principal.**  The inherited three-condition obstruction is exactly
the previous statement applied to the local exact rate set: the only property of that set
which is used is that it does not contain zero. -/
theorem obstruction_from_minimal :
    ¬ ∃ b : Vec3 → ℝ, RateCont b ∧ RateHalfOdd b ∧ RateRev b := by
  rintro ⟨b, hcont, hhalf, hrev⟩
  exact no_continuous_odd_rate_avoiding_zero (S := HalfOddSet) zero_notMem_halfOddSet
    ⟨b, hcont, hrev, fun n hn => hhalf n hn⟩

/-- **PACKAGE G (item 63).**  A non-discrete instance of the same obstruction: there is no
continuous reversal-odd rate with strictly positive values.  Discreteness therefore plays no
role in the mechanism. -/
theorem no_positive_odd_rate :
    ¬ ∃ b : Vec3 → ℝ, RateCont b ∧ RateRev b ∧ ∀ n : Vec3, IsUnitAxis n → 0 < b n := by
  refine fun h => no_continuous_odd_rate_avoiding_zero (S := {x : ℝ | 0 < x}) ?_ ?_
  · exact fun hmem => lt_irrefl (0 : ℝ) hmem
  · obtain ⟨b, hc, hr, hp⟩ := h
    exact ⟨b, hc, hr, fun n hn => hp n hn⟩

/-- **PACKAGE G (item 64).**  Countermodels: removing any single one of the three conditions
makes the remaining two realizable, with the inherited explicit witnesses; and removing the
single feature "zero is excluded" from the value set destroys the obstruction, since the
identically vanishing rate is continuous and reversal-odd. -/
theorem obstruction_countermodels :
    (RateHalfOdd signRate ∧ RateRev signRate ∧ ¬ RateCont signRate) ∧
      (RateCont rateZero ∧ RateRev rateZero ∧ ¬ RateHalfOdd rateZero) ∧
      (RateCont rateHalf ∧ RateHalfOdd rateHalf ∧ ¬ RateRev rateHalf) ∧
      (∃ b : Vec3 → ℝ, RateCont b ∧ RateRev b ∧
        ∀ n : Vec3, IsUnitAxis n → b n ∈ ({x : ℝ | x = 0} : Set ℝ)) :=
  ⟨⟨signRate_halfOdd', signRate_rev, signRate_not_cont⟩,
    ⟨rateZero_cont, rateZero_rev, rateZero_not_halfOdd⟩,
    ⟨rateHalf_cont, rateHalf_halfOdd, rateHalf_not_rev⟩,
    ⟨rateZero, rateZero_cont, rateZero_rev, fun _ _ => rfl⟩⟩

/-- **PACKAGE G (items 59–61).**  The inherited statements are preserved unchanged: the
obstruction at the level of rates, at the level of primitive bridges, and at the level of
globally exact families, together with the inherited equivalence between a globally exact
family and a primitive bridge with globally exact reconstruction. -/
theorem obstruction_all_levels :
    (¬ ∃ b : Vec3 → ℝ, RateCont b ∧ RateHalfOdd b ∧ RateRev b) ∧
      (¬ ∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsTransformationValued (recon c)) ∧
      (¬ ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧ IsTransformationValued U) ∧
      ((∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsTransformationValued (recon c)) ↔
        ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧ IsTransformationValued U) :=
  ⟨obstruction_from_minimal, no_global_rate_and_no_primitive_global_bridge.2,
    obstruction_family_level, primitiveBridge_iff_globalExactFamily⟩

end NullSectorTask20
