import RequestProject.Experiment2.NullSectorTask19.PrimitiveBridge

/-!
# Task 19, Package C: exact minimality of the three-condition obstruction

Task 18 located the global obstruction in the joint incompatibility of three conditions on
a rate function and showed each *pair* realizable.  Package C turns this into a **logical**
statement about a set of three conditions, and separates the three levels at which it can
be read.

* §25, §26.  The three conditions are indexed by an explicit three-element type
  `RateCond`, and satisfiability of a *set* of conditions is defined.  The full set is
  unsatisfiable (`rate_conditions_unsat`).
* §27, §28, §29.  Each single condition can be removed, and existence is restored: the
  three explicit witnesses `signRate` (half-odd and reversal-odd, discontinuous),
  `rateZero` (continuous and reversal-odd, not half-odd), `rateHalf` (continuous and
  half-odd, not reversal-odd).  These are stated separately.
* §30.  Consequently the three conditions form an **exact minimal unsatisfiable set**:
  the full set is unsatisfiable and *every proper subset* is satisfiable.  The terminology
  is justified because both halves are formally proved, in exactly that quantifier form.
* §31.  Three separate theorems: the pure rate statement, the corresponding statement about
  primitive bridges, and the consequence for globally exact internal families.  None of
  them is derived from the others by definitional inclusion.
* §32.  The three witnesses are preserved as explicit negative controls.
-/

namespace NullSectorTask19

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18

/-! ## §25 — the three conditions as a set -/

/-- **NEUTRAL DEFINITION (§25).**  An index for the three rate conditions. -/
inductive RateCond
  | cont
  | halfOdd
  | rev
  deriving DecidableEq, Fintype

/-- **NEUTRAL DEFINITION (§25).**  What each index requires of a rate function. -/
def RateCond.holds : RateCond → (Vec3 → ℝ) → Prop
  | .cont, b => RateCont b
  | .halfOdd, b => RateHalfOdd b
  | .rev, b => RateRev b

/-- **NEUTRAL DEFINITION (§25).**  A set of conditions is satisfiable when one rate
function satisfies all of them. -/
def SatisfiableSet (S : Finset RateCond) : Prop := ∃ b : Vec3 → ℝ, ∀ x ∈ S, x.holds b

theorem SatisfiableSet.mono {S T : Finset RateCond} (hST : S ⊆ T) (h : SatisfiableSet T) :
    SatisfiableSet S := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun x hx => hb x (hST hx)⟩

/-! ## §26 — the full set is unsatisfiable -/

/-- **PRINCIPAL THEOREM (§26).**  No rate function is at once continuous on the unit
directions, half-odd at every unit direction, and odd under reversal. -/
theorem no_rate_all_three :
    ¬ ∃ b : Vec3 → ℝ, RateCont b ∧ RateHalfOdd b ∧ RateRev b := by
  rintro ⟨b, hcont, hhalf, hodd⟩
  exact no_global_halfodd_odd_rate ⟨b, hcont, fun n hn => hhalf n hn, hodd⟩

/-- **PRINCIPAL THEOREM (§26), set form.**  The full set of the three conditions is
unsatisfiable. -/
theorem rate_conditions_unsat : ¬ SatisfiableSet (Finset.univ : Finset RateCond) := by
  rintro ⟨b, hb⟩
  exact no_rate_all_three
    ⟨b, hb .cont (Finset.mem_univ _), hb .halfOdd (Finset.mem_univ _),
      hb .rev (Finset.mem_univ _)⟩

/-! ## §27, §28, §29 — removing one condition restores existence -/

/-- **PRINCIPAL THEOREM (§27).**  Removing **continuity** restores existence: an explicit
rate is half-odd everywhere and odd under reversal. -/
theorem drop_continuity :
    ∃ b : Vec3 → ℝ, RateHalfOdd b ∧ RateRev b ∧ ¬ RateCont b :=
  ⟨signRate, signRate_halfOdd', signRate_rev, signRate_not_cont⟩

/-- **PRINCIPAL THEOREM (§28).**  Removing **half-oddness** restores existence: an explicit
rate is continuous and odd under reversal. -/
theorem drop_halfOddness :
    ∃ b : Vec3 → ℝ, RateCont b ∧ RateRev b ∧ ¬ RateHalfOdd b :=
  ⟨rateZero, rateZero_cont, rateZero_rev, rateZero_not_halfOdd⟩

/-- **PRINCIPAL THEOREM (§29).**  Removing **reversal oddness** restores existence: an
explicit rate is continuous and half-odd everywhere. -/
theorem drop_reversalOddness :
    ∃ b : Vec3 → ℝ, RateCont b ∧ RateHalfOdd b ∧ ¬ RateRev b :=
  ⟨rateHalf, rateHalf_cont, rateHalf_halfOdd, rateHalf_not_rev⟩

/-! ### the three pairs, as satisfiable sets -/

theorem sat_halfOdd_rev : SatisfiableSet {RateCond.halfOdd, RateCond.rev} := by
  refine ⟨signRate, ?_⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact signRate_halfOdd'
  · exact signRate_rev

theorem sat_cont_rev : SatisfiableSet {RateCond.cont, RateCond.rev} := by
  refine ⟨rateZero, ?_⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact rateZero_cont
  · exact rateZero_rev

theorem sat_cont_halfOdd : SatisfiableSet {RateCond.cont, RateCond.halfOdd} := by
  refine ⟨rateHalf, ?_⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact rateHalf_cont
  · exact rateHalf_halfOdd

/-! ## §30 — exact minimality -/

/-- **PRINCIPAL THEOREM (§30).**  *Every proper subset* of the three conditions is
satisfiable. -/
theorem sat_of_ssubset {S : Finset RateCond} (hS : S ⊂ Finset.univ) : SatisfiableSet S := by
  obtain ⟨x, -, hx⟩ := Finset.exists_of_ssubset hS
  cases x with
  | cont =>
    refine SatisfiableSet.mono ?_ sat_halfOdd_rev
    intro y hy
    have hyc : y ≠ RateCond.cont := by rintro rfl; exact hx hy
    cases y with
    | cont => exact absurd rfl hyc
    | halfOdd => simp
    | rev => simp
  | halfOdd =>
    refine SatisfiableSet.mono ?_ sat_cont_rev
    intro y hy
    have hyc : y ≠ RateCond.halfOdd := by rintro rfl; exact hx hy
    cases y with
    | cont => simp
    | halfOdd => exact absurd rfl hyc
    | rev => simp
  | rev =>
    refine SatisfiableSet.mono ?_ sat_cont_halfOdd
    intro y hy
    have hyc : y ≠ RateCond.rev := by rintro rfl; exact hx hy
    cases y with
    | cont => simp
    | halfOdd => simp
    | rev => exact absurd rfl hyc

/-- **PRINCIPAL THEOREM (§30).**  The three rate conditions form an **exact minimal
unsatisfiable set**: the whole set is unsatisfiable and every proper subset is satisfiable.
Both halves are proved, in exactly this quantifier form. -/
theorem three_conditions_minimal_unsatisfiable :
    ¬ SatisfiableSet (Finset.univ : Finset RateCond) ∧
      ∀ S : Finset RateCond, S ⊂ Finset.univ → SatisfiableSet S :=
  ⟨rate_conditions_unsat, fun _ hS => sat_of_ssubset hS⟩

/-! ## §31 — the three levels, separated -/

/-- **PRINCIPAL THEOREM (§31a), rate level.**  Repeated for the record: the pure rate
statement. -/
theorem obstruction_rate_level :
    ¬ ∃ b : Vec3 → ℝ, RateCont b ∧ RateHalfOdd b ∧ RateRev b := no_rate_all_three

/-- **PRINCIPAL THEOREM (§31b), primitive bridge level.**  No primitive bridge has a
vanishing first rate together with a half-odd, reversal-odd directional rate.  The
statement is about the *rates of a primitive bridge*, not about exactness. -/
theorem obstruction_primitiveBridge_level :
    ¬ ∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧
      (∀ n : Vec3, IsUnitAxis n → primRateA c n = 0) ∧ RateHalfOdd (primRateB c) ∧
      RateRev (primRateB c) := by
  rintro ⟨c, hc, hA, hhalf, hodd⟩
  exact no_global_rate_and_no_primitive_global_bridge.2
    ⟨c, hc, (recon_globallyExact_iff hc).2 ⟨hA, hhalf, hodd⟩⟩

/-- **PRINCIPAL THEOREM (§31c), family level.**  No globally exact jointly regular family
exists.  This is the inherited endpoint, restated as the third, logically separate,
reading. -/
theorem obstruction_family_level :
    ¬ ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧ IsTransformationValued U :=
  no_global_jointly_regular_transformationValued

/-! ## §32 — the witnesses, preserved as controls -/

/-- **NEGATIVE CONTROLS (§32).**  The three explicit witnesses for the three pairwise
satisfiable cases, retained. -/
theorem three_witnesses_preserved :
    (RateHalfOdd signRate ∧ RateRev signRate ∧ ¬ RateCont signRate) ∧
      (RateCont rateZero ∧ RateRev rateZero ∧ ¬ RateHalfOdd rateZero) ∧
      (RateCont rateHalf ∧ RateHalfOdd rateHalf ∧ ¬ RateRev rateHalf) :=
  ⟨⟨signRate_halfOdd', signRate_rev, signRate_not_cont⟩,
    ⟨rateZero_cont, rateZero_rev, rateZero_not_halfOdd⟩,
    ⟨rateHalf_cont, rateHalf_halfOdd, rateHalf_not_rev⟩⟩

end NullSectorTask19
