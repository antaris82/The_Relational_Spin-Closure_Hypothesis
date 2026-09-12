import RequestProject.Experiment2.NullSectorTask14.CarrierFamilyAction

/-!
# Task 14, Layer 19 (§59–§60): the common fixed locus of two nonparallel axes

Task 13 reduced the one-axis carrier-family fixed locus to exactly two carriers.  Here the
question is settled for two independently reconstructed axes:

* `generic_fixed_carrier_iff` — for a unit axis the globally fixed minimal carriers are
  exactly the two sphere points `±n`;
* `no_common_fixed_carrier` — for nonparallel unit axes there is **no** minimal carrier
  fixed by both families: verdict `NO COMMON FIXED CARRIER`;
* `one_axis_fixed_locus_moved` — the two-point fixed locus of one axis is genuinely moved
  by the other;
* `two_axis_selection_verdict` — a second nonparallel axis selects **none**: it does not
  resolve the one-axis two-point ambiguity, it destroys it.

No physical interpretation of the sphere is attached.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## The half-parameter coordinate action -/

theorem rotv_pi (n p : Vec3) : rotv n Real.pi p = (2 * h3 n p) • n - p := by
  rw [rotv, Real.cos_pi, Real.sin_pi]
  module

theorem unitAxis_iff_sumsq (p : Vec3) :
    IsUnitAxis p ↔ p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = 1 := by
  simp only [IsUnitAxis, h3, dot3_apply]
  constructor <;> intro h <;> nlinarith [h]

theorem h3_smul_left (t : ℝ) (n m : Vec3) : h3 (t • n) m = t * h3 n m := by
  simp [h3]; ring

theorem h3_smul_right (t : ℝ) (n m : Vec3) : h3 n (t • m) = t * h3 n m := by
  simp [h3]; ring

/-! ## §59 — the exact fixed locus of one axis -/

/-- **PRINCIPAL THEOREM (§59).**  For every unit axis, the minimal carriers fixed by the
whole axis family are exactly the two sphere points `±n`.  The proof uses only the derived
coordinate action and the Task-13 sphere parametrization. -/
theorem generic_fixed_carrier_iff {n p : Vec3} (hn : IsUnitAxis n) (hp : IsUnitAxis p) :
    (∀ θ : ℝ, Submodule.map (PhiGen n θ) (Lgen (esphv p)) = Lgen (esphv p)) ↔
      p = n ∨ p = -n := by
  constructor
  · intro hfix
    have hπ := hfix Real.pi
    rw [generic_carrier_family_action hn] at hπ
    have hnorm : (rotv n Real.pi p).1 ^ 2 + (rotv n Real.pi p).2.1 ^ 2
        + (rotv n Real.pi p).2.2 ^ 2 = 1 := by
      rw [← unitAxis_iff_sumsq]
      have := rotv_preserves_form hn Real.pi p
      rw [IsUnitAxis, this]
      exact hp
    obtain ⟨h1, h2, h3'⟩ := Lgen_esph_inj hnorm hπ
    have hvec : rotv n Real.pi p = p := Prod.ext h1 (Prod.ext h2 h3')
    rw [rotv_pi] at hvec
    have hsm : (h3 n p) • n = p := by
      have h2v : ((2 : ℝ) * h3 n p) • n = (2 : ℝ) • p := by
        linear_combination (norm := module) hvec
      have := congrArg (fun v : Vec3 => (2⁻¹ : ℝ) • v) h2v
      simp only [smul_smul] at this
      rw [show (2⁻¹ : ℝ) * (2 * h3 n p) = h3 n p by ring,
        show (2⁻¹ : ℝ) * 2 = (1 : ℝ) by norm_num, one_smul] at this
      exact this
    have ht : h3 n p * h3 n p = 1 := by
      have := hp
      rw [IsUnitAxis, ← hsm, h3_smul_left, h3_smul_right, hn] at this
      nlinarith [this]
    have : h3 n p = 1 ∨ h3 n p = -1 := by
      rcases mul_eq_zero.1 (show (h3 n p - 1) * (h3 n p + 1) = 0 by nlinarith [ht]) with h | h
      · left; linarith
      · right; linarith
    rcases this with h | h
    · left; rw [← hsm, h, one_smul]
    · right; rw [← hsm, h]; module
  · rintro (rfl | rfl) <;> intro θ <;> rw [generic_carrier_family_action hn]
    · rw [rotv_axis hn]
    · rw [rotv_neg_axis hn]

/-! ## §59 — nonparallel axes have no common fixed carrier -/

/-- **PRINCIPAL THEOREM (§59): `common_fixed_locus`, verdict
`NO COMMON FIXED CARRIER`.**  For two nonparallel unit axes no minimal left carrier is
globally fixed by both reconstructed families. -/
theorem no_common_fixed_carrier {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m)
    (hne : n ≠ m) (hne' : n ≠ -m) {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    ¬ ((∀ θ : ℝ, Submodule.map (PhiGen n θ) L = L) ∧
       (∀ φ : ℝ, Submodule.map (PhiGen m φ) L = L)) := by
  rintro ⟨hfn, hfm⟩
  obtain ⟨p₁, p₂, p₃, hnorm, rfl⟩ := minimal_eq_Lgen_esph hL
  have hp : IsUnitAxis (p₁, p₂, p₃) := (unitAxis_iff_sumsq _).2 (by simpa using hnorm)
  have hesph : esphv (p₁, p₂, p₃) = esph p₁ p₂ p₃ := rfl
  have hA : (p₁, p₂, p₃) = n ∨ (p₁, p₂, p₃) = -n := by
    refine (generic_fixed_carrier_iff hn hp).1 (fun θ => ?_)
    rw [hesph]; exact hfn θ
  have hB : (p₁, p₂, p₃) = m ∨ (p₁, p₂, p₃) = -m := by
    refine (generic_fixed_carrier_iff hm hp).1 (fun φ => ?_)
    rw [hesph]; exact hfm φ
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact hne (hA ▸ hB)
  · exact hne' (hA ▸ hB)
  · refine absurd ?_ hne'
    have h1 : -n = m := by rw [← hA, hB]
    simpa using congrArg (fun v : Vec3 => -v) h1
  · refine absurd ?_ hne
    have h1 : -n = -m := by rw [← hA, hB]
    simpa using congrArg (fun v : Vec3 => -v) h1

/-! ## §58, §60 — the one-axis fixed locus is moved by a second axis -/

/-- **PRINCIPAL THEOREM (§58).**  Each of the two carriers fixed by the first axis family
is moved by the second, nonparallel one. -/
theorem one_axis_fixed_locus_moved {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m)
    (hne : m ≠ n) (hne' : m ≠ -n) :
    (∃ φ : ℝ, Submodule.map (PhiGen m φ) (Lgen (esphv n)) ≠ Lgen (esphv n)) ∧
    (∃ φ : ℝ, Submodule.map (PhiGen m φ) (Lgen (esphv (-n))) ≠ Lgen (esphv (-n))) := by
  have hnegn : IsUnitAxis (-n) := by
    rw [unitAxis_iff_sumsq] at hn ⊢
    simpa using hn
  constructor
  · by_contra hcon
    push_neg at hcon
    rcases (generic_fixed_carrier_iff hm hn).1 hcon with h | h
    · exact hne h.symm
    · refine hne' ?_
      have h2 : -n = m := by simpa using congrArg (fun v : Vec3 => -v) h
      exact h2.symm
  · by_contra hcon
    push_neg at hcon
    rcases (generic_fixed_carrier_iff hm hnegn).1 hcon with h | h
    · exact hne' h.symm
    · refine hne ?_
      have h2 : n = m := by simpa using congrArg (fun v : Vec3 => -v) h
      exact h2.symm

/-- **PRINCIPAL THEOREM (§60): `two_axis_selection_verdict`.**  Two independently
reconstructed nonparallel axes select **no** minimal carrier at all: the one-axis
two-point ambiguity is not resolved by adding a second axis, it is removed together with
every fixed carrier.  No interpretation as a selection of a state is attached. -/
theorem two_axis_selection_verdict {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m)
    (hne : n ≠ m) (hne' : n ≠ -m) :
    (∀ L : Submodule ℝ W, IsMinimalLeftCarrier L →
        ¬ ((∀ θ : ℝ, Submodule.map (PhiGen n θ) L = L) ∧
           (∀ φ : ℝ, Submodule.map (PhiGen m φ) L = L))) ∧
      (∀ p : Vec3, IsUnitAxis p →
        ((∀ θ : ℝ, Submodule.map (PhiGen n θ) (Lgen (esphv p)) = Lgen (esphv p)) ↔
          p = n ∨ p = -n)) :=
  ⟨fun _ hL => no_common_fixed_carrier hn hm hne hne' hL,
    fun _ hp => generic_fixed_carrier_iff hn hp⟩

end NullSectorTask14
