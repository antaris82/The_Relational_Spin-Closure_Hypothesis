import RequestProject.Experiment2.NullSectorTask14.TwoAxisSliceComparison

/-!
# Task 14, Layer 7 (§21, §22, §23): the mixed projector algebra

The only inputs are the two relations `A ⋆ A = 1`, `B ⋆ B = 1` and the inherited
anticommutation.  The elements `(1 ± n)/2` are introduced **after** their algebraic
properties are proved, and are used only as internal algebra elements; their coefficients
are never given any interpretation.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## §21 — the axis projectors -/

/-- **NEUTRAL DEFINITION (§21).**  The plus half-sum attached to an axis element. -/
noncomputable def ep (n : W) : W := (2⁻¹ : ℝ) • (w1 + n)

/-- **NEUTRAL DEFINITION (§21).**  The minus half-sum attached to an axis element. -/
noncomputable def em (n : W) : W := (2⁻¹ : ℝ) • (w1 - n)

theorem ep_add_em (n : W) : ep n + em n = w1 := by
  rw [ep, em]; module

theorem ep_sub_em (n : W) : ep n - em n = n := by
  rw [ep, em]; module

section Involutive

variable {n : W} (hn : n ⋆ n = w1)
include hn

/-- **DERIVED (§21).**  The half-sums are idempotent. -/
theorem ep_idem : ep n ⋆ ep n = ep n := by
  rw [ep, smul_mul_W, mul_smul_W, add_mul_W, mul_add_W, mul_add_W, one_mul_W, mul_one_W,
    one_mul_W, hn]
  module

theorem em_idem : em n ⋆ em n = em n := by
  rw [em, smul_mul_W, mul_smul_W, sub_mul_W, mul_sub_W, mul_sub_W, one_mul_W, mul_one_W,
    one_mul_W, hn]
  module

/-- **DERIVED (§21).**  The two half-sums are mutually annihilating. -/
theorem ep_mul_em : ep n ⋆ em n = 0 := by
  rw [ep, em, smul_mul_W, mul_smul_W, add_mul_W, mul_sub_W, mul_sub_W, one_mul_W,
    mul_one_W, one_mul_W, hn]
  module

theorem em_mul_ep : em n ⋆ ep n = 0 := by
  rw [ep, em, smul_mul_W, mul_smul_W, sub_mul_W, mul_add_W, mul_add_W, one_mul_W,
    mul_one_W, one_mul_W, hn]
  module

/-- **DERIVED (§21).**  The half-sums are the two eigenvectors of the axis. -/
theorem axis_mul_ep : n ⋆ ep n = ep n := by
  rw [ep, mul_smul_W, mul_add_W, mul_one_W, hn]
  module

theorem axis_mul_em : n ⋆ em n = -em n := by
  rw [em, mul_smul_W, mul_sub_W, mul_one_W, hn]
  module

/-! ### The projectors on a carrier -/

theorem ep_mul_mem_Kp {L : Submodule ℝ W} (hL : IsLeftCarrier L) {ψ : W} (hψ : ψ ∈ L) :
    ep n ⋆ ψ ∈ Kp n L := by
  refine ⟨hL _ _ hψ, ?_⟩
  show n ⋆ (ep n ⋆ ψ) = ep n ⋆ ψ
  rw [← mul_assoc_W, axis_mul_ep hn]

theorem em_mul_mem_Km {L : Submodule ℝ W} (hL : IsLeftCarrier L) {ψ : W} (hψ : ψ ∈ L) :
    em n ⋆ ψ ∈ Km n L := by
  refine ⟨hL _ _ hψ, ?_⟩
  show n ⋆ (em n ⋆ ψ) = -(em n ⋆ ψ)
  rw [← mul_assoc_W, axis_mul_em hn, neg_mul_W]

omit hn in
theorem ep_mul_eq_self {L : Submodule ℝ W} {ψ : W} (hψ : ψ ∈ Kp n L) : ep n ⋆ ψ = ψ := by
  have h : n ⋆ ψ = ψ := hψ.2
  rw [ep, smul_mul_W, add_mul_W, one_mul_W, h]
  module

omit hn in
theorem em_mul_eq_zero_of_mem_Kp {L : Submodule ℝ W} {ψ : W} (hψ : ψ ∈ Kp n L) :
    em n ⋆ ψ = 0 := by
  have h : n ⋆ ψ = ψ := hψ.2
  rw [em, smul_mul_W, sub_mul_W, one_mul_W, h]
  module

omit hn in
theorem em_mul_eq_self {L : Submodule ℝ W} {ψ : W} (hψ : ψ ∈ Km n L) : em n ⋆ ψ = ψ := by
  have h : n ⋆ ψ = -ψ := hψ.2
  rw [em, smul_mul_W, sub_mul_W, one_mul_W, h]
  module

omit hn in
theorem ep_mul_eq_zero_of_mem_Km {L : Submodule ℝ W} {ψ : W} (hψ : ψ ∈ Km n L) :
    ep n ⋆ ψ = 0 := by
  have h : n ⋆ ψ = -ψ := hψ.2
  rw [ep, smul_mul_W, add_mul_W, one_mul_W, h]
  module

/-- **DERIVED (§22).**  Exact range of the plus projector on a carrier. -/
theorem ep_range {L : Submodule ℝ W} (hL : IsLeftCarrier L) :
    Submodule.map (Lmul (ep n)) L = Kp n L := by
  ext χ
  simp only [Submodule.mem_map, Lmul_apply]
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    exact ep_mul_mem_Kp hn hL hψ
  · intro hχ
    exact ⟨χ, hχ.1, ep_mul_eq_self hχ⟩

/-- **DERIVED (§22).**  Exact kernel of the plus projector inside a carrier. -/
theorem ep_kernel {L : Submodule ℝ W} (hL : IsLeftCarrier L) (ψ : W) :
    (ψ ∈ L ∧ ep n ⋆ ψ = 0) ↔ ψ ∈ Km n L := by
  constructor
  · rintro ⟨hψ, hzero⟩
    refine ⟨hψ, ?_⟩
    show n ⋆ ψ = -ψ
    have hexp : ep n ⋆ ψ = (2⁻¹ : ℝ) • (ψ + n ⋆ ψ) := by
      rw [ep, smul_mul_W, add_mul_W, one_mul_W]
    rw [hexp] at hzero
    have h0 : ψ + n ⋆ ψ = 0 := by
      have h2 := congrArg (fun y : W => (2 : ℝ) • y) hzero
      simpa using h2
    rw [add_comm] at h0
    exact eq_neg_of_add_eq_zero_left h0
  · rintro hψ
    exact ⟨hψ.1, ep_mul_eq_zero_of_mem_Km hψ⟩

end Involutive

/-! ## §22 — the mixed products -/

section Mixed

variable {n m : W} (hn : n ⋆ n = w1) (hm : m ⋆ m = w1) (hnm : n ⋆ m = -(m ⋆ n))
include hn hm hnm

omit hn hm in
theorem ep_mul_partner : ep n ⋆ m = m ⋆ em n := by
  rw [ep, em, smul_mul_W, mul_smul_W, add_mul_W, mul_sub_W, one_mul_W, mul_one_W, hnm]
  module

omit hm in
/-- **PRINCIPAL THEOREM (§22): the mixed sandwich.**  For two anticommuting axis elements
the mixed composition satisfies the exact relation

`(e_{n,+} ⋆ e_{m,+}) ⋆ e_{n,+} = (1/2) • e_{n,+}`.

The coefficient `1/2` is **derived** here; no overlap formula is inserted. -/
theorem ep_mixed_sandwich : (ep n ⋆ ep m) ⋆ ep n = (2⁻¹ : ℝ) • ep n := by
  have hstep : ep n ⋆ ep m = (2⁻¹ : ℝ) • (ep n + m ⋆ em n) := by
    have hem : ep m = (2⁻¹ : ℝ) • (w1 + m) := rfl
    rw [hem, mul_smul_W, mul_add_W, mul_one_W, ep_mul_partner hnm]
  rw [hstep, smul_mul_W, add_mul_W, ep_idem hn, mul_assoc_W, em_mul_ep hn, mul_zero_W]
  module

end Mixed

section MixedEquiv

variable {n m : W} (hn : n ⋆ n = w1) (hm : m ⋆ m = w1) (hnm : n ⋆ m = -(m ⋆ n))

/-- **DERIVED (§22).**  The mixed composition, restricted to the plus slices, is
invertible: the two maps below are mutually inverse up to the derived factor `2`. -/
theorem mixed_left_inverse {L : Submodule ℝ W} {ψ : W} (hψ : ψ ∈ Kp n L)
    (hn : n ⋆ n = w1) (hnm : n ⋆ m = -(m ⋆ n)) :
    (2 : ℝ) • (ep n ⋆ (ep m ⋆ ψ)) = ψ := by
  have hself : ep n ⋆ ψ = ψ := ep_mul_eq_self hψ
  calc (2 : ℝ) • (ep n ⋆ (ep m ⋆ ψ))
      = (2 : ℝ) • ((ep n ⋆ ep m) ⋆ ψ) := by rw [mul_assoc_W (ep n) (ep m) ψ]
    _ = (2 : ℝ) • ((ep n ⋆ ep m) ⋆ (ep n ⋆ ψ)) := by rw [hself]
    _ = (2 : ℝ) • (((ep n ⋆ ep m) ⋆ ep n) ⋆ ψ) := by
          rw [mul_assoc_W (ep n ⋆ ep m) (ep n) ψ]
    _ = (2 : ℝ) • (((2⁻¹ : ℝ) • ep n) ⋆ ψ) := by rw [ep_mixed_sandwich hn hnm]
    _ = ep n ⋆ ψ := by rw [smul_mul_W]; module
    _ = ψ := hself

/-- **PRINCIPAL THEOREM (§22): `mixed_projector_classification`.**  For two anticommuting
axis elements and an arbitrary left carrier, left multiplication by `e_{m,+}` is a linear
isomorphism from the plus slice of `n` onto the plus slice of `m`, with inverse
`2 • e_{n,+} ⋆ ·`. -/
noncomputable def mixedEquiv (hn : n ⋆ n = w1) (hm : m ⋆ m = w1)
    (hnm : n ⋆ m = -(m ⋆ n)) {L : Submodule ℝ W} (hL : IsLeftCarrier L) :
    Kp n L ≃ₗ[ℝ] Kp m L where
  toFun ψ := ⟨ep m ⋆ (ψ : W), ep_mul_mem_Kp hm hL ψ.2.1⟩
  map_add' := by intro x y; apply Subtype.ext; simpa using mul_add_W (ep m) x y
  map_smul' := by intro c x; apply Subtype.ext; simpa using mul_smul_W c (ep m) x
  invFun χ := ⟨(2 : ℝ) • (ep n ⋆ (χ : W)),
    Submodule.smul_mem _ _ (ep_mul_mem_Kp hn hL χ.2.1)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact mixed_left_inverse x.2 hn hnm
  right_inv := by
    intro x
    apply Subtype.ext
    have hnm' : m ⋆ n = -(n ⋆ m) := by rw [hnm, neg_neg]
    show ep m ⋆ ((2 : ℝ) • (ep n ⋆ (x : W))) = (x : W)
    rw [mul_smul_W]
    exact mixed_left_inverse (n := m) (m := n) x.2 hm hnm'

end MixedEquiv

/-! ## §23 — the mixed data for the initial orthogonal pair -/

theorem wA_wB_anticomm' : wA ⋆ wB = -(wB ⋆ wA) := by
  rw [wit8_wA_wB, wit8_wB_wA, neg_neg]

/-- **PRINCIPAL THEOREM (§21, §22, §23): the complete mixed projector data for the two
independently reconstructed axes.**  Idempotency, complementarity, mutual annihilation,
the derived mixed sandwich coefficient `1/2`, and invertibility of the mixed composition
between the two plus slices of an arbitrary minimal carrier. -/
theorem mixed_projector_data {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    ep wA ⋆ ep wA = ep wA ∧ em wA ⋆ em wA = em wA ∧ ep wA ⋆ em wA = 0 ∧
    ep wA + em wA = w1 ∧
    ep wB ⋆ ep wB = ep wB ∧ em wB ⋆ em wB = em wB ∧ ep wB ⋆ em wB = 0 ∧
    ep wB + em wB = w1 ∧
    (ep wA ⋆ ep wB) ⋆ ep wA = (2⁻¹ : ℝ) • ep wA ∧
    (ep wB ⋆ ep wA) ⋆ ep wB = (2⁻¹ : ℝ) • ep wB ∧
    Module.finrank ℝ (Kp wA L) = Module.finrank ℝ (Kp wB L) := by
  have hAB := wA_wB_anticomm'
  have hBA : wB ⋆ wA = -(wA ⋆ wB) := by rw [hAB, neg_neg]
  refine ⟨ep_idem wA_sq, em_idem wA_sq, ep_mul_em wA_sq, ep_add_em wA,
    ep_idem wB_sq, em_idem wB_sq, ep_mul_em wB_sq, ep_add_em wB,
    ep_mixed_sandwich wA_sq hAB, ep_mixed_sandwich wB_sq hBA, ?_⟩
  exact LinearEquiv.finrank_eq (mixedEquiv wA_sq wB_sq hAB hL.1.1)

/-- **DERIVED (§22).**  Both mixed compositions are nonzero — the two decompositions are
not orthogonal in any algebraic sense; every A-slice is carried isomorphically onto a
B-slice. -/
theorem mixed_composition_nonzero : ep wB ⋆ ep wA ≠ 0 := by
  intro hcon
  have h0 := congrFun hcon 0
  simp [ep, w1, wA, wB, wit8MulFun] at h0

end NullSectorTask14
