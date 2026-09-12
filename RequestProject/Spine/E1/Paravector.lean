import Mathlib
import RequestProject.Spine.E1.SpinElement
import RequestProject.Spine.E1.CliffordMonomial

/-!
# Task 11, Phase V : paravector preservation and the induced action on the carrier

Phase V (`RequestProject/Task11Spin.lean`) constructed the intrinsic spin condition
`IsSpinElem g` inside `Cl₃(ℝ)` and the twisted action `spinAct g x = g A(x) (reverse g)`,
and proved that a spin element preserves the intrinsic quadratic form in its Clifford
form.  Three items were recorded as `NOT_YET_FORMALIZED`:

1. that `spinAct g x` again lies in the embedded carrier `A(𝒮)` (paravector preservation);
2. that the induced map on `𝒮` lands in the intrinsic Lorentz group;
3. that its kernel is exactly `{±1}`.

This module closes 1 and (for the *wide* intrinsic group `G_L^wide`, i.e. norm and cone
preservation) 2; the determinant condition and item 3 are discussed at the end.

## The argument

* `SpinCore.exists_para_decomp` : every element of `Cl₃(ℝ)` is `A(p) + ω A(q)` with
  `p, q ∈ 𝒮`.  This is the eight-monomial spanning statement of Task 9 together with the
  three identities `e₀e₁ = ω e₂`, `e₀e₂ = -ω e₁`, `e₁e₂ = ω e₀`; no linear independence
  and no matrix model is used.
* `SpinCore.reverse_fixed_iff_para` : `reverse z = z` **iff** `z` is a paravector.  The
  nontrivial direction is immediate from the decomposition: reversion fixes `A(p)` and
  negates `ω A(q)`, and `ω` is invertible.
* `SpinCore.spinAct_reverse` : `spinAct g x` is reversion-fixed for *every* `g` (the spin
  condition is not needed), hence is a paravector; `SpinCore.spinLor g` is the induced map
  on `𝒮`, well defined because `A` is injective (`SpinCore.spinToCl_injective`).
* `SpinCore.spinLor_mul`, `SpinCore.spinLor_one`, `SpinCore.spinLor_neg_one` : the action law and
  the fact that `±1` act trivially.
* `SpinCore.NS_spinLor` : a spin element preserves `N` on the carrier.
* `SpinCore.spinLor_mem_coneS` : it preserves the square cone.  A cone element is a Jordan
  square `y ∘ y`, and `A(y ∘ y) = A(y)²`, so its image is `w · reverse w` with
  `w = g A(y)`; the time component of such an element is `¼ tr(M Mᵀ) ≥ 0` in the faithful
  real `4 × 4` frame of Phase IV (`FRAME_CHOICE`: the frame is a proof device, it occurs in
  no statement).
* `SpinCore.spinLorEquiv_mem_GLorWide` : the induced map is an element of the intrinsic wide
  Lorentz group `SpinCore.GLorWide`.

Proved downstream, not here: `det = 1`, i.e. membership in `SpinCore.GLor`
(`SpinDeterminant`); and surjectivity of `g ↦ spinLor g` onto the intrinsic group
(`DoubleCover`).  For the kernel see `SpinCore.spinLor_eq_id_of_pm_one` (the easy
inclusion) — the reverse inclusion is `SpinCore.kernel_exactly_pm_one` below, whose proof
uses the exact centre `SpinCore.center_Cl3` of `RequestProject.Spine.E1.CliffordMonomial`.
That centre theorem is now proved intrinsically, so nothing in this module depends on the
complex matrix model or on the `SL(2,ℂ)` comparison.
-/

noncomputable section

open CliffordAlgebra Matrix

namespace SpinCore

open SpinCore

/-! ## `A` is injective -/

theorem spinToCl_injective : Function.Injective spinToCl := by
  intro x y hxy
  have h : spinToCl (x - y) = 0 := by
    rw [show x - y = x + (-1 : ℝ) • y by module, spinToCl_add, spinToCl_smul, hxy]
    module
  have hz : x - y = 0 := by
    set z := x - y with hzdef
    have hm := congrArg repCl h
    rw [map_zero] at hm
    have hz1 : repCl (spinToCl z)
        = z.1 • (1 : Matrix (Fin 4) (Fin 4) ℝ)
          + z.2 0 • repA 0 + z.2 1 • repA 1 + z.2 2 • repA 2 := by
      rw [spinToCl_apply, map_add, AlgHom.commutes]
      have hv : ι q3 z.2 = z.2 0 • cle 0 + z.2 1 • cle 1 + z.2 2 • cle 2 := by
        rw [ι_eq_sum]
      rw [hv]
      simp only [map_add, map_smul, repCl_cle, Algebra.algebraMap_eq_smul_one]
      abel
    rw [hz1] at hm
    have e00 := congrFun (congrFun hm 0) 0
    have e22 := congrFun (congrFun hm 2) 2
    have e02 := congrFun (congrFun hm 0) 2
    have e03 := congrFun (congrFun hm 0) 3
    simp [repA, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      Matrix.zero_apply, smul_eq_mul] at e00 e22 e02 e03
    apply Prod.ext
    · show z.1 = 0; linarith
    · funext i
      fin_cases i <;> simp <;> linarith
  have := sub_eq_zero.mp hz
  exact this

/-! ## The paravector decomposition of `Cl₃(ℝ)` -/

theorem cle_01 : cle 0 * cle 1 = omega * cle 2 := by
  rw [omega]
  rw [mul_assoc, cle_sq, mul_one]

theorem cle_12 : cle 1 * cle 2 = omega * cle 0 := by
  have h : omega * cle 0 = cle 0 * cle 1 * cle 2 * cle 0 := by rw [omega]
  rw [h]
  symm
  calc cle 0 * cle 1 * cle 2 * cle 0
      = cle 0 * cle 1 * (cle 2 * cle 0) := by rw [mul_assoc]
    _ = cle 0 * cle 1 * -(cle 0 * cle 2) := by rw [t20]
    _ = -(cle 0 * (cle 1 * cle 0) * cle 2) := by noncomm_ring
    _ = -(cle 0 * -(cle 0 * cle 1) * cle 2) := by rw [t10]
    _ = cle 0 * cle 0 * (cle 1 * cle 2) := by noncomm_ring
    _ = cle 1 * cle 2 := by rw [cle_sq, one_mul]

theorem cle_02 : cle 0 * cle 2 = -(omega * cle 1) := by
  have h : omega * cle 1 = cle 0 * cle 1 * cle 2 * cle 1 := by rw [omega]
  have h2 : cle 0 * cle 1 * cle 2 * cle 1 = -(cle 0 * cle 2) :=
    calc cle 0 * cle 1 * cle 2 * cle 1
        = cle 0 * cle 1 * (cle 2 * cle 1) := by rw [mul_assoc]
      _ = cle 0 * cle 1 * -(cle 1 * cle 2) := by rw [t21]
      _ = -(cle 0 * (cle 1 * cle 1) * cle 2) := by noncomm_ring
      _ = -(cle 0 * cle 2) := by rw [cle_sq, mul_one]
  rw [h, h2, neg_neg]

/-- The spatial embedding of a vector, as an element of the carrier. -/
theorem spinToCl_spatial (v : Fin 3 → ℝ) : spinToCl ((0 : ℝ), v) = ι q3 v := by
  rw [spinToCl_apply]
  simp

theorem spinToCl_cle (i : Fin 3) : spinToCl ((0 : ℝ), evec i) = cle i := by
  rw [spinToCl_spatial]; rfl

theorem spinToCl_sOne : spinToCl sOne = 1 := by
  rw [spinToCl_apply]
  simp [sOne]

/-- The set of elements `A(p) + ω A(q)`. -/
def ParaSum : Submodule ℝ Cl3 where
  carrier := {z | ∃ p q : LorentzCarrier, z = spinToCl p + omega * spinToCl q}
  add_mem' := by
    rintro _ _ ⟨p, q, rfl⟩ ⟨p', q', rfl⟩
    exact ⟨p + p', q + q', by rw [spinToCl_add, spinToCl_add, mul_add]; abel⟩
  zero_mem' := ⟨0, 0, by
    have h : spinToCl (0 : LorentzCarrier) = 0 := by
      rw [show (0 : LorentzCarrier) = (0 : ℝ) • (0 : LorentzCarrier) by module, spinToCl_smul, zero_smul]
    rw [h]; simp⟩
  smul_mem' := by
    rintro r _ ⟨p, q, rfl⟩
    exact ⟨r • p, r • q, by rw [spinToCl_smul, spinToCl_smul, smul_add, mul_smul_comm]⟩

theorem mem_ParaSum {z : Cl3} :
    z ∈ ParaSum ↔ ∃ p q : LorentzCarrier, z = spinToCl p + omega * spinToCl q := Iff.rfl

theorem mono_mem_ParaSum (j : Fin 8) : SpinCore.mono j ∈ ParaSum := by
  have hzero : spinToCl (0 : LorentzCarrier) = 0 := by
    rw [show (0 : LorentzCarrier) = (0 : ℝ) • (0 : LorentzCarrier) by module, spinToCl_smul, zero_smul]
  fin_cases j
  · exact ⟨sOne, 0, by rw [spinToCl_sOne, hzero]; simp [SpinCore.mono]⟩
  · exact ⟨((0 : ℝ), evec 0), 0, by rw [spinToCl_cle, hzero]; simp [SpinCore.mono]⟩
  · exact ⟨((0 : ℝ), evec 1), 0, by rw [spinToCl_cle, hzero]; simp [SpinCore.mono]⟩
  · exact ⟨((0 : ℝ), evec 2), 0, by rw [spinToCl_cle, hzero]; simp [SpinCore.mono]⟩
  · refine ⟨0, ((0 : ℝ), evec 2), ?_⟩
    rw [spinToCl_cle, hzero]
    show cle 0 * cle 1 = 0 + omega * cle 2
    rw [cle_01, zero_add]
  · exact ⟨0, -((0 : ℝ), evec 1), by
      have h : spinToCl (-((0 : ℝ), evec 1)) = -cle 1 := by
        rw [show -((0 : ℝ), evec 1) = (-1 : ℝ) • ((0 : ℝ), evec 1) by module,
          spinToCl_smul, spinToCl_cle]
        module
      rw [h, hzero]
      show cle 0 * cle 2 = 0 + omega * -cle 1
      rw [cle_02, zero_add, mul_neg]⟩
  · refine ⟨0, ((0 : ℝ), evec 0), ?_⟩
    rw [spinToCl_cle, hzero]
    show cle 1 * cle 2 = 0 + omega * cle 0
    rw [cle_12, zero_add]
  · exact ⟨0, sOne, by rw [spinToCl_sOne, hzero]; simp [SpinCore.mono]⟩

/-- **Phase V.**  Every element of `Cl₃(ℝ)` decomposes as `A(p) + ω A(q)`. -/
theorem exists_para_decomp (z : Cl3) : ∃ p q : LorentzCarrier, z = spinToCl p + omega * spinToCl q := by
  have htop : SpinCore.monoSpan ≤ ParaSum := by
    rw [SpinCore.monoSpan]
    exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact mono_mem_ParaSum j)
  have hz : z ∈ SpinCore.monoSpan := by rw [SpinCore.monoSpan_eq_top]; trivial
  exact htop hz

/-! ## Reversion-fixed elements are exactly the paravectors -/

theorem reverse_omega_mul (z : Cl3) :
    reverse (Q := q3) (omega * z) = -(omega * reverse (Q := q3) z) := by
  rw [reverse.map_mul, reverse_omega, mul_neg, omega_central]

/-- **Phase V.**  An element of `Cl₃(ℝ)` is fixed by reversion exactly when it is a
paravector, i.e. lies in the embedded carrier `A(𝒮)`. -/
theorem reverse_fixed_iff_para (z : Cl3) :
    reverse (Q := q3) z = z ↔ ∃ p : LorentzCarrier, z = spinToCl p := by
  constructor
  · intro hz
    obtain ⟨p, q, rfl⟩ := exists_para_decomp z
    have hrev : reverse (Q := q3) (spinToCl p + omega * spinToCl q)
        = spinToCl p - omega * spinToCl q := by
      rw [map_add, reverse_spinToCl, reverse_omega_mul, reverse_spinToCl]
      abel
    rw [hrev] at hz
    have hq : omega * spinToCl q = 0 := by
      have h2 : (2 : ℝ) • (omega * spinToCl q) = 0 := by
        have := sub_eq_iff_eq_add.mp hz
        have h' : omega * spinToCl q + omega * spinToCl q = 0 := by
          linear_combination (norm := abel) -this
        calc (2 : ℝ) • (omega * spinToCl q)
            = omega * spinToCl q + omega * spinToCl q := by module
          _ = 0 := h'
      have := smul_eq_zero.mp h2
      rcases this with h | h
      · norm_num at h
      · exact h
    have hq0 : spinToCl q = 0 := by
      have : omega * (omega * spinToCl q) = 0 := by rw [hq, mul_zero]
      rw [← mul_assoc, omega_sq, neg_mul, one_mul, neg_eq_zero] at this
      exact this
    exact ⟨p, by rw [hq, add_zero]⟩
  · rintro ⟨p, rfl⟩
    exact reverse_spinToCl p

/-! ## The induced action on the carrier -/

theorem spinAct_reverse (g : Cl3) (x : LorentzCarrier) :
    reverse (Q := q3) (spinAct g x) = spinAct g x := by
  simp only [spinAct, reverse.map_mul, reverse_reverse, reverse_spinToCl]
  rw [mul_assoc]

theorem spinAct_mem_para (g : Cl3) (x : LorentzCarrier) : ∃ y : LorentzCarrier, spinAct g x = spinToCl y :=
  (reverse_fixed_iff_para _).1 (spinAct_reverse g x)

/-- The map induced on the carrier by a Clifford element. -/
def spinLor (g : Cl3) (x : LorentzCarrier) : LorentzCarrier := (spinAct_mem_para g x).choose

@[simp] theorem spinToCl_spinLor (g : Cl3) (x : LorentzCarrier) :
    spinToCl (spinLor g x) = spinAct g x := (spinAct_mem_para g x).choose_spec.symm

theorem spinLor_unique {g : Cl3} {x y : LorentzCarrier} (h : spinToCl y = spinAct g x) :
    spinLor g x = y :=
  spinToCl_injective (by rw [spinToCl_spinLor, h])

@[simp] theorem spinLor_one (x : LorentzCarrier) : spinLor 1 x = x :=
  spinLor_unique (by rw [spinAct_one])

@[simp] theorem spinLor_neg_one (x : LorentzCarrier) : spinLor (-1) x = x :=
  spinLor_unique (by rw [spinAct_neg_one])

theorem spinLor_add (g : Cl3) (x y : LorentzCarrier) :
    spinLor g (x + y) = spinLor g x + spinLor g y := by
  refine spinLor_unique ?_
  rw [spinToCl_add, spinToCl_spinLor, spinToCl_spinLor]
  simp only [spinAct, spinToCl_add]
  noncomm_ring

theorem spinLor_smul (g : Cl3) (r : ℝ) (x : LorentzCarrier) :
    spinLor g (r • x) = r • spinLor g x := by
  refine spinLor_unique ?_
  rw [spinToCl_smul, spinToCl_spinLor]
  simp only [spinAct, spinToCl_smul, mul_smul_comm, smul_mul_assoc]

/-- The induced map, as a linear map on the carrier. -/
def spinLorLin (g : Cl3) : LorentzCarrier →ₗ[ℝ] LorentzCarrier where
  toFun := spinLor g
  map_add' := spinLor_add g
  map_smul' r x := spinLor_smul g r x

@[simp] theorem spinLorLin_apply (g : Cl3) (x : LorentzCarrier) : spinLorLin g x = spinLor g x := rfl

/-- The action law: the induced maps compose. -/
theorem spinLor_mul (g h : Cl3) (x : LorentzCarrier) :
    spinLor (g * h) x = spinLor g (spinLor h x) := by
  refine spinLor_unique ?_
  rw [spinToCl_spinLor]
  show spinAct g (spinLor h x) = spinAct (g * h) x
  simp only [spinAct, spinToCl_spinLor, reverse.map_mul]
  noncomm_ring

/-! ## Preservation of the intrinsic quadratic form -/

theorem algebraMap_Cl3_injective : Function.Injective (algebraMap ℝ Cl3) := by
  intro r s hrs
  have hm := congrArg repCl hrs
  rw [AlgHom.commutes, AlgHom.commutes] at hm
  have := congrFun (congrFun hm 0) 0
  simpa [Matrix.algebraMap_eq_diagonal, Matrix.diagonal] using this

/-- **Phase V.**  A spin element preserves the intrinsic quadratic form of the carrier. -/
theorem NS_spinLor {g : Cl3} (hg : IsSpinElem g) (x : LorentzCarrier) : NS (spinLor g x) = NS x := by
  have h1 := spinAct_norm hg x
  have h2 := spinToCl_norm (spinLor g x)
  rw [spinToCl_spinLor] at h2
  rw [h2] at h1
  exact algebraMap_Cl3_injective h1

/-- The two induced maps of a spin element and its conjugate are mutually inverse. -/
theorem spinLor_cconj_left {g : Cl3} (hg : IsSpinElem g) (x : LorentzCarrier) :
    spinLor (cconj g) (spinLor g x) = x := by
  rw [← spinLor_mul, hg.2, spinLor_one]

theorem spinLor_cconj_right {g : Cl3} (hg : IsSpinElem g) (x : LorentzCarrier) :
    spinLor g (spinLor (cconj g) x) = x := by
  rw [← spinLor_mul, hg.1, spinLor_one]

/-- The induced map of a spin element, as a linear automorphism of the carrier. -/
def spinLorEquiv {g : Cl3} (hg : IsSpinElem g) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier :=
  LinearEquiv.ofLinear (spinLorLin g) (spinLorLin (cconj g))
    (LinearMap.ext fun x => spinLor_cconj_right hg x)
    (LinearMap.ext fun x => spinLor_cconj_left hg x)

@[simp] theorem spinLorEquiv_apply {g : Cl3} (hg : IsSpinElem g) (x : LorentzCarrier) :
    spinLorEquiv hg x = spinLor g x := rfl

/-! ## Preservation of the square cone

The time component of a paravector is recovered from the faithful real `4 × 4` frame of
Phase IV as `¼ tr`, and the image of a cone element is of the form `w · reverse w`, whose
frame matrix is `M Mᵀ`. -/

theorem repLin_transpose (v : Fin 3 → ℝ) : (repLin v)ᵀ = repLin v := by
  show (v 0 • repA 0 + v 1 • repA 1 + v 2 • repA 2)ᵀ
      = v 0 • repA 0 + v 1 • repA 1 + v 2 • repA 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [repA]

/-- Reversion is implemented by matrix transposition in the real `4 × 4` frame. -/
theorem repCl_reverse (z : Cl3) : repCl (reverse (Q := q3) z) = (repCl z)ᵀ := by
  induction z using CliffordAlgebra.induction with
  | algebraMap r =>
      rw [reverse.commutes, AlgHom.commutes,
        Matrix.algebraMap_eq_diagonal, Matrix.diagonal_transpose]
  | ι v =>
      rw [reverse_ι]
      show repCl (ι q3 v) = (repCl (ι q3 v))ᵀ
      rw [repCl, CliffordAlgebra.lift_ι_apply, repLin_transpose]
  | mul a b ha hb =>
      rw [reverse.map_mul, map_mul, map_mul, ha, hb, Matrix.transpose_mul]
  | add a b ha hb =>
      simp only [map_add, ha, hb, Matrix.transpose_add]

theorem trace_repCl_spinToCl (p : LorentzCarrier) :
    Matrix.trace (repCl (spinToCl p)) = 4 * p.1 := by
  have hz1 : repCl (spinToCl p)
      = p.1 • (1 : Matrix (Fin 4) (Fin 4) ℝ)
        + p.2 0 • repA 0 + p.2 1 • repA 1 + p.2 2 • repA 2 := by
    rw [spinToCl_apply, map_add, AlgHom.commutes]
    have hv : ι q3 p.2 = p.2 0 • cle 0 + p.2 1 • cle 1 + p.2 2 • cle 2 := by
      rw [ι_eq_sum]
    rw [hv]
    simp only [map_add, map_smul, repCl_cle, Algebra.algebraMap_eq_smul_one]
    abel
  rw [hz1]
  simp [Matrix.trace, Matrix.diag, repA, Fin.sum_univ_four]
  ring

theorem trace_mul_transpose_nonneg (M : Matrix (Fin 4) (Fin 4) ℝ) :
    0 ≤ Matrix.trace (M * Mᵀ) := by
  have h : Matrix.trace (M * Mᵀ) = ∑ i, ∑ j, (M i j) ^ 2 := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, sq]
  rw [h]
  positivity

/-- The time component of `w · reverse w` is nonnegative. -/
theorem fst_nonneg_of_mul_reverse {p : LorentzCarrier} {w : Cl3}
    (hp : spinToCl p = w * reverse (Q := q3) w) : 0 ≤ p.1 := by
  have h := trace_repCl_spinToCl p
  rw [hp, map_mul, repCl_reverse] at h
  have hnn := trace_mul_transpose_nonneg (repCl w)
  rw [h] at hnn
  linarith

theorem spinToCl_sJ_self (y : LorentzCarrier) : spinToCl (sJ y y) = spinToCl y * spinToCl y := by
  have h := clifford_jordan y y
  rw [← h]
  module

/-- **Phase V.**  A spin element preserves the intrinsic square cone. -/
theorem spinLor_mem_coneS {g : Cl3} (hg : IsSpinElem g) {x : LorentzCarrier} (hx : x ∈ ConeS) :
    spinLor g x ∈ ConeS := by
  obtain ⟨y, rfl⟩ := hx
  set w := g * spinToCl y with hw
  have hkey : spinToCl (spinLor g (sJ y y)) = w * reverse (Q := q3) w := by
    rw [spinToCl_spinLor]
    simp only [spinAct, spinToCl_sJ_self, hw, reverse.map_mul, reverse_spinToCl]
    noncomm_ring
  refine (mem_coneS_iff _).2 ⟨fst_nonneg_of_mul_reverse hkey, ?_⟩
  rw [NS_spinLor hg]
  exact coneS_NS_nonneg ⟨y, rfl⟩

/-- **Phase V.**  The induced map of a spin element is an element of the intrinsic wide
Lorentz group of the carrier: it preserves `N` and the square cone. -/
theorem spinLorEquiv_mem_GLorWide {g : Cl3} (hg : IsSpinElem g) :
    spinLorEquiv hg ∈ GLorWide := by
  refine ⟨fun x => NS_spinLor hg x, fun x => ⟨fun hx => spinLor_mem_coneS hg hx, fun hx => ?_⟩⟩
  have h2 : spinLor (cconj g) (spinLor g x) ∈ ConeS :=
    spinLor_mem_coneS (isSpinElem_cconj hg) hx
  rwa [spinLor_cconj_left hg] at h2

/-! ## The kernel of the induced action

The easy inclusion `{±1} ⊆ ker` is `spinLor_one` and `spinLor_neg_one`.  The reverse
inclusion uses the exact centre `SpinCore.center_Cl3` of
`RequestProject.Spine.E1.CliffordMonomial`, which is now proved intrinsically from the
monomial frame; no complex matrix model and no `SL(2,ℂ)` comparison is involved. -/

theorem involute_omega : involute (Q := q3) omega = -omega := by
  rw [omega]
  simp only [map_mul, cle, involute_ι]
  noncomm_ring

theorem cconj_of_central (a b : ℝ) :
    cconj (a • (1 : Cl3) + b • omega) = a • (1 : Cl3) + b • omega := by
  have hr : reverse (Q := q3) (a • (1 : Cl3) + b • omega) = a • (1 : Cl3) - b • omega := by
    rw [map_add, map_smul, map_smul, reverse.map_one, reverse_omega]
    module
  rw [cconj, hr, map_sub, map_smul, map_smul, map_one, involute_omega]
  module

/-- If the induced map is the identity, the spin element is `±1`. -/
theorem eq_pm_one_of_spinLor_eq_id {g : Cl3} (hg : IsSpinElem g)
    (h : ∀ x : LorentzCarrier, spinLor g x = x) : g = 1 ∨ g = -1 := by
  -- the action condition, transported to the Clifford algebra
  have hact : ∀ x : LorentzCarrier, g * spinToCl x * reverse (Q := q3) g = spinToCl x := by
    intro x
    have := spinToCl_spinLor g x
    rw [h x] at this
    exact this.symm
  -- reversion and Clifford conjugation agree on `g`
  have hone : g * reverse (Q := q3) g = 1 := by
    have := hact sOne
    rwa [spinToCl_sOne, mul_one] at this
  have hrev : reverse (Q := q3) g = cconj g := by
    have h1 : cconj g * (g * reverse (Q := q3) g) = cconj g * (g * cconj g) := by
      rw [hone, hg.1]
    rw [← mul_assoc, ← mul_assoc, hg.2, one_mul, one_mul] at h1
    exact h1
  -- `g` commutes with every paravector, hence with everything
  have hcomm : ∀ x : LorentzCarrier, g * spinToCl x = spinToCl x * g := by
    intro x
    have h1 := hact x
    have h2 : g * spinToCl x * reverse (Q := q3) g * g = spinToCl x * g := by
      rw [h1]
    rw [hrev, mul_assoc (g * spinToCl x), hg.2, mul_one] at h2
    exact h2
  have hcent : ∀ y : Cl3, g * y = y * g := by
    have hle : (⊤ : Subalgebra ℝ Cl3) ≤ Subalgebra.centralizer ℝ ({g} : Set Cl3) := by
      rw [← adjoin_spinToCl_eq_top]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨x, rfl⟩
      exact (Subalgebra.mem_centralizer_iff ℝ).2 (by rintro _ rfl; exact hcomm x)
    intro y
    have : y ∈ Subalgebra.centralizer ℝ ({g} : Set Cl3) := hle (by trivial)
    exact ((Subalgebra.mem_centralizer_iff ℝ).1 this) g rfl
  obtain ⟨a, b, rfl⟩ := (center_Cl3 g).1 hcent
  -- the spin condition forces `b = 0` and `a = ±1`
  have hsq : (a • (1 : Cl3) + b • omega) * (a • (1 : Cl3) + b • omega) = 1 := by
    have := hg.1
    rwa [cconj_of_central] at this
  have hexp : (a • (1 : Cl3) + b • omega) * (a • (1 : Cl3) + b • omega)
      = (a * a - b * b) • (1 : Cl3) + (2 * (a * b)) • omega := by
    have hsq2 : omega * omega = -1 := omega_sq
    simp only [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul,
      mul_one, hsq2, sub_smul, add_smul, smul_neg, two_mul]
    module
  rw [hexp] at hsq
  have hz : (a * a - b * b - 1) • (1 : Cl3) + (2 * (a * b)) • omega = 0 := by
    linear_combination (norm := module) hsq
  obtain ⟨h1, h2⟩ := one_omega_indep hz
  have hb : b = 0 := by
    rcases mul_eq_zero.mp (by linarith : a * b = 0) with ha0 | hb0
    · exfalso
      rw [ha0] at h1
      nlinarith [sq_nonneg b]
    · exact hb0
  have ha : a = 1 ∨ a = -1 := by
    rw [hb] at h1
    have : (a - 1) * (a + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases ha with rfl | rfl
  · left; rw [hb]; module
  · right; rw [hb]; module

/-- **Phase V.**  For spin elements the kernel of the induced action is exactly `{±1}`. -/
theorem kernel_exactly_pm_one {g : Cl3} (hg : IsSpinElem g) :
    (∀ x : LorentzCarrier, spinLor g x = x) ↔ (g = 1 ∨ g = -1) := by
  constructor
  · exact eq_pm_one_of_spinLor_eq_id hg
  · rintro (rfl | rfl) x
    · exact spinLor_one x
    · exact spinLor_neg_one x

end SpinCore
