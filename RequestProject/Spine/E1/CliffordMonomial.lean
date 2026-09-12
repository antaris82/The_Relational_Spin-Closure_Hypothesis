import Mathlib
import RequestProject.Spine.E1.CliffordHodgeBridge

/-!
# Spine / E1 : the monomial frame of `Cl₃(ℝ)`, its faithfulness, and the exact centre

This module is part of the **intrinsic** experiment-1 spin core.  It supplies the two
structural facts about the real Clifford algebra `Cl₃(ℝ)` that the intrinsic double-cover
argument needs, and it proves them without any complex matrix model:

* `SpinCore.monoSpan_eq_top` — the eight monomials `1, e₀, e₁, e₂, e₀e₁, e₀e₂, e₁e₂, ω`
  span `Cl₃(ℝ)` over `ℝ` (`SpinCore.exists_monoComb` in coordinate form);
* `SpinCore.monoComb_coeffs_eq_zero` — they are linearly independent, proved by evaluating
  in the faithful **real** `4 × 4` frame `SpinCore.repCl` of
  `RequestProject.Spine.E1.CliffordHodgeBridge`;
* `SpinCore.one_omega_indep` — in particular `1` and the pseudoscalar `ω` are independent;
* `SpinCore.comm_cle01_iff` / **`SpinCore.center_Cl3`** — an element commuting with the two
  generators `e₀, e₁` (a fortiori a central element) is a real combination `a·1 + b·ω`, so
  `Z(Cl₃(ℝ)) = ℝ ⊕ ℝω`.

**Import firewall.**  `Mathlib` plus the intrinsic Clifford layer only.  In particular the
complex `2 × 2` matrix model `RequestProject.Spine.E1.MatrixModel`, the Pauli
representation `RequestProject.Spine.E1.PauliRepresentation` and the `SL(2,ℂ)` comparison
are *not* imported: no Hermitian matrix and no complex algebra occurs in the closure of
this module.  The real `4 × 4` frame `repCl` is a proof device — a frame choice — and
occurs in no statement of this module.

**Provenance.**  The monomial block (`mono` … `monoComb_expand`) is moved unchanged from
`RequestProject.Spine.E1.PauliRepresentation`, where it sat behind the complex matrix
model although it never used it.  `one_omega_indep` was proved there through the Pauli
representation `rho` and is reconstructed here from `repCl`; `center_Cl3` was proved there
from the centre of `M₂(ℂ)` and is reconstructed here by an intrinsic sign computation on
the monomial frame.  No statement is strengthened.
-/

noncomputable section

open CliffordAlgebra

namespace SpinCore

/-! ## The eight monomials -/

/-- The eight monomials in the generators. -/
def mono : Fin 8 → Cl3
  | 0 => 1
  | 1 => cle 0
  | 2 => cle 1
  | 3 => cle 2
  | 4 => cle 0 * cle 1
  | 5 => cle 0 * cle 2
  | 6 => cle 1 * cle 2
  | 7 => omega

/-- The real span of the eight monomials. -/
def monoSpan : Submodule ℝ Cl3 := Submodule.span ℝ (Set.range mono)

theorem one_mem_monoSpan : (1 : Cl3) ∈ monoSpan :=
  Submodule.subset_span ⟨0, rfl⟩

theorem mono_mem (j : Fin 8) : mono j ∈ monoSpan := Submodule.subset_span ⟨j, rfl⟩

/-- Normalising rewrite system for words in the three generators. -/
local macro "cliff" : tactic => `(tactic|
  simp only [mono, omega, mul_assoc, s10, s20, s21, t10, t20, t21, cle_sq_mul, cle_sq,
    mul_neg, neg_neg, neg_mul, mul_one, one_mul])

theorem cle0_mul_mono (j : Fin 8) : cle 0 * mono j ∈ monoSpan := by
  have h0 : cle 0 * mono 0 = mono 1 := by cliff
  have h1 : cle 0 * mono 1 = mono 0 := by cliff
  have h2 : cle 0 * mono 2 = mono 4 := by cliff
  have h3 : cle 0 * mono 3 = mono 5 := by cliff
  have h4 : cle 0 * mono 4 = mono 2 := by cliff
  have h5 : cle 0 * mono 5 = mono 3 := by cliff
  have h6 : cle 0 * mono 6 = mono 7 := by cliff
  have h7 : cle 0 * mono 7 = mono 6 := by cliff
  fin_cases j
  exacts [h0 ▸ mono_mem 1, h1 ▸ mono_mem 0, h2 ▸ mono_mem 4, h3 ▸ mono_mem 5,
    h4 ▸ mono_mem 2, h5 ▸ mono_mem 3, h6 ▸ mono_mem 7, h7 ▸ mono_mem 6]

theorem cle1_mul_mono (j : Fin 8) : cle 1 * mono j ∈ monoSpan := by
  have h0 : cle 1 * mono 0 = mono 2 := by cliff
  have h1 : cle 1 * mono 1 = -mono 4 := by cliff
  have h2 : cle 1 * mono 2 = mono 0 := by cliff
  have h3 : cle 1 * mono 3 = mono 6 := by cliff
  have h4 : cle 1 * mono 4 = -mono 1 := by cliff
  have h5 : cle 1 * mono 5 = -mono 7 := by cliff
  have h6 : cle 1 * mono 6 = mono 3 := by cliff
  have h7 : cle 1 * mono 7 = -mono 5 := by cliff
  fin_cases j
  exacts [h0 ▸ mono_mem 2, h1 ▸ (neg_mem (mono_mem 4)), h2 ▸ mono_mem 0, h3 ▸ mono_mem 6,
    h4 ▸ (neg_mem (mono_mem 1)), h5 ▸ (neg_mem (mono_mem 7)), h6 ▸ mono_mem 3,
    h7 ▸ (neg_mem (mono_mem 5))]

theorem cle2_mul_mono (j : Fin 8) : cle 2 * mono j ∈ monoSpan := by
  have h0 : cle 2 * mono 0 = mono 3 := by cliff
  have h1 : cle 2 * mono 1 = -mono 5 := by cliff
  have h2 : cle 2 * mono 2 = -mono 6 := by cliff
  have h3 : cle 2 * mono 3 = mono 0 := by cliff
  have h4 : cle 2 * mono 4 = mono 7 := by cliff
  have h5 : cle 2 * mono 5 = -mono 1 := by cliff
  have h6 : cle 2 * mono 6 = -mono 2 := by cliff
  have h7 : cle 2 * mono 7 = mono 4 := by cliff
  fin_cases j
  exacts [h0 ▸ mono_mem 3, h1 ▸ (neg_mem (mono_mem 5)), h2 ▸ (neg_mem (mono_mem 6)),
    h3 ▸ mono_mem 0, h4 ▸ mono_mem 7, h5 ▸ (neg_mem (mono_mem 1)),
    h6 ▸ (neg_mem (mono_mem 2)), h7 ▸ mono_mem 4]

theorem cle_mul_mono (i : Fin 3) (j : Fin 8) : cle i * mono j ∈ monoSpan := by
  fin_cases i
  exacts [cle0_mul_mono j, cle1_mul_mono j, cle2_mul_mono j]

/-- Left multiplication by a generator preserves the span of the eight monomials. -/
theorem cle_mul_mem_monoSpan (i : Fin 3) {x : Cl3} (hx : x ∈ monoSpan) :
    cle i * x ∈ monoSpan := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨j, rfl⟩ := hy; exact cle_mul_mono i j
  | zero => simp
  | add y z hy hz ihy ihz => rw [mul_add]; exact add_mem ihy ihz
  | smul a y hy ih => rw [Algebra.mul_smul_comm]; exact Submodule.smul_mem _ _ ih

/-- The three generators already generate the whole algebra. -/
theorem adjoin_cle_top : Algebra.adjoin ℝ (Set.range cle) = ⊤ := by
  have h1 : Algebra.adjoin ℝ (Set.range (ι q3)) ≤ Algebra.adjoin ℝ (Set.range cle) := by
    apply Algebra.adjoin_le
    rintro _ ⟨v, rfl⟩
    rw [ι_eq_sum]
    have hm : ∀ i : Fin 3, cle i ∈ Algebra.adjoin ℝ (Set.range cle) := fun i =>
      Algebra.subset_adjoin ⟨i, rfl⟩
    exact add_mem (add_mem (Subalgebra.smul_mem _ (hm 0) _) (Subalgebra.smul_mem _ (hm 1) _))
      (Subalgebra.smul_mem _ (hm 2) _)
  rw [adjoin_range_ι] at h1
  exact top_le_iff.1 h1

/-- **Spanning.**  The eight monomials span `Cl₃(ℝ)` over `ℝ`. -/
theorem monoSpan_eq_top : monoSpan = ⊤ := by
  have hclos : ∀ x ∈ Submonoid.closure (Set.range cle), x ∈ monoSpan := by
    intro x hx
    induction hx using Submonoid.closure_induction_left with
    | one => exact one_mem_monoSpan
    | mul_left g hg y hy ih => obtain ⟨i, rfl⟩ := hg; exact cle_mul_mem_monoSpan i ih
  have hspan : Submodule.span ℝ ((Submonoid.closure (Set.range cle) : Submonoid Cl3) : Set Cl3)
      ≤ monoSpan := Submodule.span_le.2 hclos
  rw [← Algebra.adjoin_eq_span ℝ (Set.range cle), adjoin_cle_top] at hspan
  exact top_le_iff.1 hspan

/-- The coordinate map `ℝ⁸ → Cl₃(ℝ)`. -/
def monoComb (c : Fin 8 → ℝ) : Cl3 := ∑ i, c i • mono i

theorem exists_monoComb (x : Cl3) : ∃ c : Fin 8 → ℝ, monoComb c = x := by
  have hx : x ∈ monoSpan := by rw [monoSpan_eq_top]; trivial
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx

theorem monoComb_expand (c : Fin 8 → ℝ) :
    monoComb c = c 0 • 1 + c 1 • cle 0 + c 2 • cle 1 + c 3 • cle 2 + c 4 • (cle 0 * cle 1)
      + c 5 • (cle 0 * cle 2) + c 6 • (cle 1 * cle 2) + c 7 • omega := by
  simp only [monoComb, Fin.sum_univ_eight, mono]

/-! ## Faithfulness of the monomial frame

The eight monomials are linearly independent.  This is decided in the faithful *real*
`4 × 4` frame `repCl`; the frame is a proof device and occurs in no statement. -/

/-- **Linear independence of the eight monomials.** -/
theorem monoComb_coeffs_eq_zero (c : Fin 8 → ℝ) (h : monoComb c = 0) : ∀ i, c i = 0 := by
  have hm := congrArg repCl h
  rw [monoComb_expand] at hm
  simp only [map_add, map_smul, map_mul, map_zero, map_one, repCl_cle, omega] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e02 := congrFun (congrFun hm 0) 2
  have e03 := congrFun (congrFun hm 0) 3
  have e20 := congrFun (congrFun hm 2) 0
  have e22 := congrFun (congrFun hm 2) 2
  have e23 := congrFun (congrFun hm 2) 3
  have e30 := congrFun (congrFun hm 3) 0
  simp only [repA, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply,
    Matrix.of_apply, Matrix.zero_apply, Fin.sum_univ_succ, Fin.isValue, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one] at e00 e01 e02 e03 e20 e22 e23 e30
  intro i
  fin_cases i <;> simp at e00 e01 e02 e03 e20 e22 e23 e30 ⊢ <;> linarith

/-- Two monomial combinations agree only if their coefficients do. -/
theorem monoComb_injective {c d : Fin 8 → ℝ} (h : monoComb c = monoComb d) : c = d := by
  have hz : monoComb (c - d) = 0 := by
    simp only [monoComb, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    rw [show (∑ i, c i • mono i) = monoComb c from rfl,
      show (∑ i, d i • mono i) = monoComb d from rfl, h, sub_self]
  funext i
  have := monoComb_coeffs_eq_zero (c - d) hz i
  simpa [sub_eq_zero] using this

/-- **Linear independence of `1` and the pseudoscalar.** -/
theorem one_omega_indep {a b : ℝ} (h : a • (1 : Cl3) + b • omega = 0) : a = 0 ∧ b = 0 := by
  have hc : monoComb ![a, 0, 0, 0, 0, 0, 0, b] = 0 := by
    rw [monoComb_expand]
    simpa using h
  have h0 := monoComb_coeffs_eq_zero _ hc 0
  have h7 := monoComb_coeffs_eq_zero _ hc 7
  simp only [Matrix.cons_val_zero] at h0
  refine ⟨h0, ?_⟩
  simpa using h7

/-! ## The exact centre of `Cl₃(ℝ)`

Conjugation by a generator multiplies each monomial by a sign; an element fixed by
conjugation with `e₀` and with `e₁` therefore has only its `1` and `ω` coefficients left.
No matrix model enters the statement, and only the real frame above enters the proof. -/

theorem cle0_conj_monoComb (c : Fin 8 → ℝ) :
    cle 0 * monoComb c * cle 0
      = monoComb ![c 0, c 1, -c 2, -c 3, -c 4, -c 5, c 6, c 7] := by
  have h0 : cle 0 * mono 0 * cle 0 = mono 0 := by cliff
  have h1 : cle 0 * mono 1 * cle 0 = mono 1 := by cliff
  have h2 : cle 0 * mono 2 * cle 0 = -mono 2 := by cliff
  have h3 : cle 0 * mono 3 * cle 0 = -mono 3 := by cliff
  have h4 : cle 0 * mono 4 * cle 0 = -mono 4 := by cliff
  have h5 : cle 0 * mono 5 * cle 0 = -mono 5 := by cliff
  have h6 : cle 0 * mono 6 * cle 0 = mono 6 := by cliff
  have h7 : cle 0 * mono 7 * cle 0 = mono 7 := by cliff
  simp only [monoComb, Fin.sum_univ_eight, add_mul, mul_add, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, h0, h1, h2, h3, h4, h5, h6, h7, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simp only [Matrix.cons_val, smul_neg]
  module

theorem cle1_conj_monoComb (c : Fin 8 → ℝ) :
    cle 1 * monoComb c * cle 1
      = monoComb ![c 0, -c 1, c 2, -c 3, -c 4, c 5, -c 6, c 7] := by
  have h0 : cle 1 * mono 0 * cle 1 = mono 0 := by cliff
  have h1 : cle 1 * mono 1 * cle 1 = -mono 1 := by cliff
  have h2 : cle 1 * mono 2 * cle 1 = mono 2 := by cliff
  have h3 : cle 1 * mono 3 * cle 1 = -mono 3 := by cliff
  have h4 : cle 1 * mono 4 * cle 1 = -mono 4 := by cliff
  have h5 : cle 1 * mono 5 * cle 1 = mono 5 := by cliff
  have h6 : cle 1 * mono 6 * cle 1 = -mono 6 := by cliff
  have h7 : cle 1 * mono 7 * cle 1 = mono 7 := by cliff
  simp only [monoComb, Fin.sum_univ_eight, add_mul, mul_add, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, h0, h1, h2, h3, h4, h5, h6, h7, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simp only [Matrix.cons_val, smul_neg]
  module

/-- **The centre, in generator form.**  An element commuting with the two generators `e₀`
and `e₁` is a real combination of `1` and the pseudoscalar `ω`. -/
theorem eq_scalar_add_omega_of_comm_cle01 {x : Cl3} (h0 : cle 0 * x = x * cle 0)
    (h1 : cle 1 * x = x * cle 1) : ∃ a b : ℝ, x = a • (1 : Cl3) + b • omega := by
  obtain ⟨c, rfl⟩ := exists_monoComb x
  -- conjugation by `e₀` fixes `monoComb c`
  have hc0 : monoComb ![c 0, c 1, -c 2, -c 3, -c 4, -c 5, c 6, c 7] = monoComb c := by
    rw [← cle0_conj_monoComb, h0, mul_assoc, cle_sq, mul_one]
  have hc1 : monoComb ![c 0, -c 1, c 2, -c 3, -c 4, c 5, -c 6, c 7] = monoComb c := by
    rw [← cle1_conj_monoComb, h1, mul_assoc, cle_sq, mul_one]
  have hd0 := monoComb_injective hc0
  have hd1 := monoComb_injective hc1
  have e2 : -c 2 = c 2 := congrFun hd0 2
  have e3 : -c 3 = c 3 := congrFun hd0 3
  have e4 : -c 4 = c 4 := congrFun hd0 4
  have e5 : -c 5 = c 5 := congrFun hd0 5
  have e1' : -c 1 = c 1 := congrFun hd1 1
  have e6 : -c 6 = c 6 := congrFun hd1 6
  refine ⟨c 0, c 7, ?_⟩
  rw [monoComb_expand]
  rw [show c 1 = 0 by linarith, show c 2 = 0 by linarith, show c 3 = 0 by linarith,
    show c 4 = 0 by linarith, show c 5 = 0 by linarith, show c 6 = 0 by linarith]
  module

/-- **The exact centre.**  An element of `Cl₃(ℝ)` is central exactly when it is a real
combination of `1` and the pseudoscalar `ω`; that is, `Z(Cl₃(ℝ)) = ℝ ⊕ ℝω`. -/
theorem center_Cl3 (x : Cl3) :
    (∀ y : Cl3, x * y = y * x) ↔ ∃ a b : ℝ, x = a • (1 : Cl3) + b • omega := by
  constructor
  · intro hx
    exact eq_scalar_add_omega_of_comm_cle01 (hx (cle 0)).symm (hx (cle 1)).symm
  · rintro ⟨a, b, rfl⟩ y
    rw [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, omega_central]

end SpinCore
