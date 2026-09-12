import Mathlib
import RequestProject.Spine.E1.Coords
import RequestProject.Spine.E1.Paravector

/-!
# Task 11, Phase V (completion) : the induced maps have determinant `1`

`RequestProject/Task11Paravector.lean` proved that a spin element `g ∈ Cl₃(ℝ)` induces a
linear automorphism `spinLorEquiv` of the carrier `𝒮` which preserves the intrinsic
quadratic form `N` and the square cone, i.e. lies in the *wide* intrinsic Lorentz group
`G_L^wide`.  The determinant condition — membership in `G_L` itself — was recorded as
`NOT_YET_FORMALIZED`.  This module closes that gap **intrinsically**: no `M₂(ℂ)`, no
`SL(2,ℂ)`, no Hermitian comparison layer.

## The argument

`SpinCore.det_sq_of_NS_preserving` already gives `det² = 1`, so only the *sign* is at stake.
The sign is fixed by exhibiting every spin element as a product of two squares:

* **paravector square roots.**  If `p ∈ 𝒮` has `N(p) = 1` and `p₀ ≥ 0`, then
  `A(p) = A(√p)²` with `√p := (2(1+p₀))^{-1/2} · (1 + p)`, and `N(√p) = 1`, `(√p)₀ ≥ 0`
  (`SpinCore.paraSqrt_sq`, `SpinCore.NS_paraSqrt`).  This uses only the paravector
  Cayley–Hamilton identity `A(p)² = 2p₀ A(p) − N(p)` (`SpinCore.spinToCl_sq`).
* **polar decomposition.**  For a spin element `g`, `h := g · reverse g` is reversion-fixed,
  hence a paravector `A(p)` with `N(p) = 1` and `p₀ ≥ 0`; with `β := A(√p)` one has
  `g = β · r` where `r := cconj β · g` satisfies `r · reverse r = 1`.
* **rotors are squares.**  `r · reverse r = 1` together with the spin condition forces
  `reverse r = cconj r`, i.e. `reverse r` is fixed by the grade involution, hence
  `r = a + ω ι(v)` with `a² + ⟪v,v⟫ = 1` (`SpinCore.even_decomp`); such an `r` is the square
  of `s = α + ω ι((2α)^{-1} v)`, `α = √((1+a)/2)`, and `r = −1 = (ω e₀)²` in the degenerate
  case `a = −1` (`SpinCore.rotor_is_square`).

Consequently `g = (b·b)·(s·s)` (`SpinCore.spin_eq_product_of_squares`), so
`det (spinLor g) = det(spinLor b)² · det(spinLor s)² ≥ 0`, and with `det² = 1` we get
`det = 1` (`SpinCore.spinLorEquiv_det`), i.e. `spinLorEquiv hg ∈ G_L`
(`SpinCore.spinLorEquiv_mem_GLor`).
-/

noncomputable section

open CliffordAlgebra

namespace SpinCore

open SpinCore

/-! ## Linearity of the paravector embedding -/

theorem spinToCl_zero : spinToCl (0 : LorentzCarrier) = 0 := by
  rw [show (0 : LorentzCarrier) = (0 : ℝ) • (0 : LorentzCarrier) by module, spinToCl_smul, zero_smul]

theorem spinToCl_neg (x : LorentzCarrier) : spinToCl (-x) = -spinToCl x := by
  rw [show -x = (-1 : ℝ) • x by module, spinToCl_smul]
  module

theorem spinToCl_sub (x y : LorentzCarrier) : spinToCl (x - y) = spinToCl x - spinToCl y := by
  rw [sub_eq_add_neg, spinToCl_add, spinToCl_neg, sub_eq_add_neg]

theorem spinToCl_eq_zero {x : LorentzCarrier} (h : spinToCl x = 0) : x = 0 :=
  spinToCl_injective (by rw [h, spinToCl_zero])

/-! ## Paravector arithmetic -/

/-- The carrier-level conjugation `(a, v) ↦ (a, −v)`. -/
def sconj (p : LorentzCarrier) : LorentzCarrier := (p.1, -p.2)

@[simp] theorem sconj_fst (p : LorentzCarrier) : (sconj p).1 = p.1 := rfl
@[simp] theorem sconj_snd (p : LorentzCarrier) : (sconj p).2 = -p.2 := rfl

theorem spinToClBar_eq (p : LorentzCarrier) : spinToClBar p = spinToCl (sconj p) := by
  simp [spinToClBar, spinToCl, sconj, sub_eq_add_neg]

/-- Clifford conjugation of a paravector is the carrier conjugation. -/
theorem cconj_spinToCl (p : LorentzCarrier) : cconj (spinToCl p) = spinToClBar p := by
  rw [cconj, reverse_spinToCl, involute_spinToCl]

/-- A unit-norm paravector is a spin element. -/
theorem isSpinElem_spinToCl {p : LorentzCarrier} (h : NS p = 1) : IsSpinElem (spinToCl p) := by
  constructor
  · rw [cconj_spinToCl, spinToCl_mul_bar, h, map_one]
  · rw [cconj_spinToCl, bar_mul_spinToCl, h, map_one]

/-- **Paravector Cayley–Hamilton.**  `A(p)² = 2p₀ A(p) − N(p)`. -/
theorem spinToCl_sq (p : LorentzCarrier) :
    spinToCl p * spinToCl p = (2 * p.1) • spinToCl p - algebraMap ℝ Cl3 (NS p) := by
  obtain ⟨a, u⟩ := p
  have hu : ι q3 u * ι q3 u = algebraMap ℝ Cl3 (sip u u) := clifford_square_convention u
  have hc : algebraMap ℝ Cl3 a * ι q3 u = a • ι q3 u := algebraMap_mul_ι a u
  have hc' : ι q3 u * algebraMap ℝ Cl3 a = a • ι q3 u := ι_mul_algebraMap a u
  show (algebraMap ℝ Cl3 a + ι q3 u) * (algebraMap ℝ Cl3 a + ι q3 u)
      = (2 * a) • (algebraMap ℝ Cl3 a + ι q3 u) - algebraMap ℝ Cl3 (a ^ 2 - sip u u)
  have hsq : algebraMap ℝ Cl3 a * algebraMap ℝ Cl3 a = algebraMap ℝ Cl3 (a * a) := by
    rw [← map_mul]
  have hexpand : (algebraMap ℝ Cl3 a + ι q3 u) * (algebraMap ℝ Cl3 a + ι q3 u)
      = algebraMap ℝ Cl3 (a * a) + (a • ι q3 u + a • ι q3 u)
        + algebraMap ℝ Cl3 (sip u u) := by
    rw [mul_add, add_mul, add_mul, hsq, hc, hc', hu]
    abel
  rw [show a ^ 2 = a * a from pow_two a]
  simp only [Algebra.algebraMap_eq_smul_one] at hexpand ⊢
  rw [hexpand, sub_smul]
  module

/-! ## Square roots of unit paravectors in the forward cone -/

/-- The canonical paravector square root of a unit paravector with `p₀ ≥ 0`. -/
def paraSqrt (p : LorentzCarrier) : LorentzCarrier := (Real.sqrt (2 * (1 + p.1)))⁻¹ • (sOne + p)

theorem one_le_fst {p : LorentzCarrier} (h : NS p = 1) (hp : 0 ≤ p.1) : 1 ≤ p.1 := by
  have hs : 0 ≤ sip p.2 p.2 := sip_self_nonneg p.2
  have hsq : p.1 ^ 2 = 1 + sip p.2 p.2 := by
    have := h; simp only [NS] at this; linarith
  nlinarith

theorem NS_paraSqrt {p : LorentzCarrier} (h : NS p = 1) (hp : 0 ≤ p.1) : NS (paraSqrt p) = 1 := by
  have h1 : (1 : ℝ) ≤ p.1 := one_le_fst h hp
  have hpos : (0 : ℝ) < 2 * (1 + p.1) := by linarith
  have hsq : Real.sqrt (2 * (1 + p.1)) ^ 2 = 2 * (1 + p.1) := Real.sq_sqrt hpos.le
  set c : ℝ := (Real.sqrt (2 * (1 + p.1)))⁻¹ with hc
  have hc2 : c ^ 2 * (2 * (1 + p.1)) = 1 := by
    rw [hc, inv_pow, hsq]
    have hne : Real.sqrt (2 * (1 + p.1)) ≠ 0 := by positivity
    field_simp
  have hNS : NS (paraSqrt p) = c ^ 2 * ((1 + p.1) ^ 2 - sip p.2 p.2) := by
    show (c * (1 + p.1)) ^ 2 - sip (c • (0 + p.2)) (c • (0 + p.2)) = _
    rw [sip_smul_left, sip_smul_right]
    simp only [zero_add]
    ring
  rw [hNS]
  have hval : (1 + p.1) ^ 2 - sip p.2 p.2 = 2 * (1 + p.1) := by
    have := h; simp only [NS] at this; nlinarith
  rw [hval, hc2]

theorem paraSqrt_fst_nonneg {p : LorentzCarrier} (h : NS p = 1) (hp : 0 ≤ p.1) :
    0 ≤ (paraSqrt p).1 := by
  have h1 : (1 : ℝ) ≤ p.1 := one_le_fst h hp
  show 0 ≤ (Real.sqrt (2 * (1 + p.1)))⁻¹ * (1 + p.1)
  have hcn : (0 : ℝ) ≤ (Real.sqrt (2 * (1 + p.1)))⁻¹ := by positivity
  nlinarith

/-- **Paravector square root.**  `A(√p)² = A(p)`. -/
theorem paraSqrt_sq {p : LorentzCarrier} (h : NS p = 1) (hp : 0 ≤ p.1) :
    spinToCl (paraSqrt p) * spinToCl (paraSqrt p) = spinToCl p := by
  have h1 : (1 : ℝ) ≤ p.1 := one_le_fst h hp
  have hpos : (0 : ℝ) < 2 * (1 + p.1) := by linarith
  have hsq : Real.sqrt (2 * (1 + p.1)) ^ 2 = 2 * (1 + p.1) := Real.sq_sqrt hpos.le
  set c : ℝ := (Real.sqrt (2 * (1 + p.1)))⁻¹ with hc
  have hc2 : c ^ 2 * (2 * (1 + p.1)) = 1 := by
    rw [hc, inv_pow, hsq]
    have hne : Real.sqrt (2 * (1 + p.1)) ≠ 0 := by positivity
    field_simp
  have hfst : (paraSqrt p).1 = c * (1 + p.1) := rfl
  have hNS := NS_paraSqrt h hp
  have hCH := spinToCl_sq (paraSqrt p)
  rw [hNS, hfst, map_one] at hCH
  have hval : spinToCl (paraSqrt p) = c • (1 + spinToCl p) := by
    rw [paraSqrt, spinToCl_smul, spinToCl_add, spinToCl_sOne]
  rw [hCH, hval]
  have h2 : (2 * (c * (1 + p.1))) • (c • (1 + spinToCl p)) - 1
      = (c ^ 2 * (2 * (1 + p.1))) • (1 + spinToCl p) - 1 := by
    rw [smul_smul]; ring_nf
  rw [h2, hc2, one_smul]
  abel

/-! ## The even part -/

/-- The paravector decomposition `z = A(p) + ω A(q)` is unique. -/
theorem para_split_zero {p q : LorentzCarrier} (hz : spinToCl p + omega * spinToCl q = 0) :
    p = 0 ∧ q = 0 := by
  have hrevz : spinToCl p - omega * spinToCl q = 0 := by
    have hh := congrArg (reverse (Q := q3)) hz
    rw [map_add, reverse_spinToCl, reverse_omega_mul, reverse_spinToCl, map_zero,
      ← sub_eq_add_neg] at hh
    exact hh
  have hp2 : (2 : ℝ) • spinToCl p = 0 := by
    calc (2 : ℝ) • spinToCl p
        = (spinToCl p + omega * spinToCl q) + (spinToCl p - omega * spinToCl q) := by module
      _ = 0 := by rw [hz, hrevz, add_zero]
  have hp0 : spinToCl p = 0 := by
    rcases smul_eq_zero.mp hp2 with hh | hh
    · norm_num at hh
    · exact hh
  have hq0 : spinToCl q = 0 := by
    have hw : omega * spinToCl q = 0 := by
      calc omega * spinToCl q = spinToCl p + omega * spinToCl q := by rw [hp0, zero_add]
        _ = 0 := hz
    have h3 : omega * (omega * spinToCl q) = 0 := by rw [hw, mul_zero]
    rw [← mul_assoc, omega_sq, neg_mul, one_mul, neg_eq_zero] at h3
    exact h3
  exact ⟨spinToCl_eq_zero hp0, spinToCl_eq_zero hq0⟩

/-- An element fixed by the grade involution is of the form `a + ω ι(v)`. -/
theorem even_decomp {y : Cl3} (h : involute (Q := q3) y = y) :
    ∃ (a : ℝ) (v : Fin 3 → ℝ), y = algebraMap ℝ Cl3 a + omega * ι q3 v := by
  obtain ⟨p, q, rfl⟩ := exists_para_decomp y
  have hinv : involute (Q := q3) (spinToCl p + omega * spinToCl q)
      = spinToCl (sconj p) - omega * spinToCl (sconj q) := by
    rw [map_add, map_mul, involute_spinToCl, involute_spinToCl, involute_omega,
      spinToClBar_eq, spinToClBar_eq, neg_mul]
    abel
  rw [hinv] at h
  have key : spinToCl (sconj p - p) + omega * spinToCl (-sconj q - q) = 0 := by
    rw [spinToCl_sub, spinToCl_sub, spinToCl_neg, mul_sub, mul_neg]
    calc spinToCl (sconj p) - spinToCl p
          + (-(omega * spinToCl (sconj q)) - omega * spinToCl q)
        = (spinToCl (sconj p) - omega * spinToCl (sconj q))
          - (spinToCl p + omega * spinToCl q) := by abel
      _ = 0 := by rw [h, sub_self]
  obtain ⟨h1, h2⟩ := para_split_zero key
  have hp2 : p.2 = 0 := by
    have hs := congrArg Prod.snd h1
    simp only [Prod.snd_sub, sconj_snd, Prod.snd_zero] at hs
    funext i
    have hi := congrFun hs i
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.zero_apply] at hi
    simp only [Pi.zero_apply]
    linarith
  have hq1 : q.1 = 0 := by
    have hs := congrArg Prod.fst h2
    simp only [Prod.fst_sub, Prod.fst_neg, sconj_fst, Prod.fst_zero] at hs
    linarith
  refine ⟨p.1, q.2, ?_⟩
  have hpe : spinToCl p = algebraMap ℝ Cl3 p.1 := by
    rw [spinToCl_apply, hp2, map_zero, add_zero]
  have hqe : spinToCl q = ι q3 q.2 := by
    rw [spinToCl_apply, hq1, map_zero, zero_add]
  rw [hpe, hqe]

/-! ## Rotors are squares -/

theorem omega_ι_sq (w : Fin 3 → ℝ) :
    omega * ι q3 w * (omega * ι q3 w) = -algebraMap ℝ Cl3 (sip w w) := by
  have hcomm : omega * ι q3 w * (omega * ι q3 w) = omega * omega * (ι q3 w * ι q3 w) := by
    rw [mul_assoc, ← mul_assoc (ι q3 w), ← omega_central, mul_assoc, ← mul_assoc]
  rw [hcomm, omega_sq, clifford_square_convention, neg_mul, one_mul]

theorem rotor_sq_expand (al : ℝ) (w : Fin 3 → ℝ) :
    (algebraMap ℝ Cl3 al + omega * ι q3 w) * (algebraMap ℝ Cl3 al + omega * ι q3 w)
      = algebraMap ℝ Cl3 (al * al - sip w w) + omega * ι q3 ((2 * al) • w) := by
  have hA : algebraMap ℝ Cl3 al * (omega * ι q3 w) = al • (omega * ι q3 w) :=
    (Algebra.smul_def al _).symm
  have hA' : omega * ι q3 w * algebraMap ℝ Cl3 al = al • (omega * ι q3 w) := by
    rw [← Algebra.commutes, Algebra.smul_def]
  have hsq : algebraMap ℝ Cl3 al * algebraMap ℝ Cl3 al = algebraMap ℝ Cl3 (al * al) := by
    rw [← map_mul]
  have hsmul : omega * ι q3 ((2 * al) • w) = (2 * al) • (omega * ι q3 w) := by
    rw [map_smul, mul_smul_comm]
  rw [mul_add, add_mul, add_mul, hsq, hA, hA', omega_ι_sq, hsmul, map_sub]
  module

/-- A rotor `a + ω ι(v)` with `a² + ⟪v,v⟫ = 1` is a square. -/
theorem rotor_is_square {a : ℝ} {v : Fin 3 → ℝ} (h : a ^ 2 + sip v v = 1) :
    ∃ s : Cl3, s * s = algebraMap ℝ Cl3 a + omega * ι q3 v := by
  by_cases ha : a = -1
  · -- degenerate case: `v = 0` and the rotor is `−1 = (ω e₀)²`
    have hv : sip v v = 0 := by rw [ha] at h; nlinarith
    have hv0 : v = 0 := sip_self_eq_zero hv
    refine ⟨omega * cle 0, ?_⟩
    rw [hv0, map_zero, mul_zero, add_zero, ha]
    have hcomm : omega * cle 0 * (omega * cle 0) = omega * omega * (cle 0 * cle 0) := by
      rw [mul_assoc, ← mul_assoc (cle 0), ← omega_central, mul_assoc, ← mul_assoc]
    rw [hcomm, omega_sq, cle_sq, mul_one, map_neg, map_one]
  · have hle : -1 ≤ a := by nlinarith [sip_self_nonneg v]
    have ha1 : -1 < a := lt_of_le_of_ne hle (fun hh => ha hh.symm)
    have hpos : (0 : ℝ) < (1 + a) / 2 := by linarith
    set al : ℝ := Real.sqrt ((1 + a) / 2) with hal
    have halpos : 0 < al := Real.sqrt_pos.mpr hpos
    have halsq : al ^ 2 = (1 + a) / 2 := Real.sq_sqrt hpos.le
    have hne : (2 * al) ≠ 0 := by positivity
    refine ⟨algebraMap ℝ Cl3 al + omega * ι q3 ((2 * al)⁻¹ • v), ?_⟩
    rw [rotor_sq_expand]
    have hw : sip ((2 * al)⁻¹ • v) ((2 * al)⁻¹ • v) = (2 * al)⁻¹ ^ 2 * sip v v := by
      rw [sip_smul_left, sip_smul_right]; ring
    have h1 : al * al - sip ((2 * al)⁻¹ • v) ((2 * al)⁻¹ • v) = a := by
      rw [hw]
      have hvv : sip v v = 1 - a ^ 2 := by linarith
      have hal2 : al * al = (1 + a) / 2 := by
        rw [← pow_two]; exact halsq
      rw [hvv, hal2]
      field_simp
      nlinarith [halsq]
    have h2 : (2 * al) • ((2 * al)⁻¹ • v) = v := by
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    rw [h1, h2]

/-! ## Polar decomposition of a spin element -/

/-- **Phase V.**  Every spin element is a product of two squares. -/
theorem spin_eq_product_of_squares {g : Cl3} (hg : IsSpinElem g) :
    ∃ b s : Cl3, g = b * b * (s * s) := by
  -- the positive paravector `h = g · reverse g`
  have hrev : reverse (Q := q3) (g * reverse (Q := q3) g) = g * reverse (Q := q3) g := by
    rw [reverse.map_mul, reverse_reverse]
  obtain ⟨p, hp⟩ := (reverse_fixed_iff_para _).1 hrev
  have hcc : cconj (g * reverse (Q := q3) g) = involute (Q := q3) g * cconj g := by
    rw [cconj_mul, cconj, reverse_reverse]
  have h2 : (g * reverse (Q := q3) g) * cconj (g * reverse (Q := q3) g) = 1 := by
    rw [hcc]
    calc g * reverse (Q := q3) g * (involute (Q := q3) g * cconj g)
        = g * (reverse (Q := q3) g * involute (Q := q3) g) * cconj g := by noncomm_ring
      _ = g * cconj g := by rw [reverse_mul_involute hg, mul_one]
      _ = 1 := hg.1
  rw [hp, spinToCl_norm p] at h2
  have hNSp : NS p = 1 :=
    algebraMap_Cl3_injective (show algebraMap ℝ Cl3 (NS p) = algebraMap ℝ Cl3 1 by
      rw [h2, map_one])
  have hp0 : 0 ≤ p.1 := fst_nonneg_of_mul_reverse hp.symm
  -- the boost factor
  set bp : LorentzCarrier := paraSqrt p with hbp
  have hNSbp : NS bp = 1 := NS_paraSqrt hNSp hp0
  have hbp0 : 0 ≤ bp.1 := paraSqrt_fst_nonneg hNSp hp0
  set beta : Cl3 := spinToCl bp with hbeta
  have hbeta_sq : beta * beta = g * reverse (Q := q3) g := by
    rw [hbeta, hbp, paraSqrt_sq hNSp hp0, ← hp]
  have hbetaSpin : IsSpinElem beta := isSpinElem_spinToCl hNSbp
  -- `β` is itself a square
  obtain ⟨b, hb⟩ : ∃ b : Cl3, b * b = beta :=
    ⟨spinToCl (paraSqrt bp), paraSqrt_sq hNSbp hbp0⟩
  -- the rotor factor
  set r : Cl3 := cconj beta * g with hr
  have hgr : g = beta * r := by
    rw [hr, ← mul_assoc, hbetaSpin.1, one_mul]
  have hcconj_para : cconj beta = spinToCl (sconj bp) := by
    rw [hbeta, cconj_spinToCl, spinToClBar_eq]
  have hrevr : r * reverse (Q := q3) r = 1 := by
    have hrc : reverse (Q := q3) (cconj beta) = cconj beta := by
      rw [hcconj_para, reverse_spinToCl]
    rw [hr, reverse.map_mul, hrc]
    calc cconj beta * g * (reverse (Q := q3) g * cconj beta)
        = cconj beta * (g * reverse (Q := q3) g) * cconj beta := by noncomm_ring
      _ = cconj beta * (beta * beta) * cconj beta := by rw [hbeta_sq]
      _ = (cconj beta * beta) * (beta * cconj beta) := by noncomm_ring
      _ = 1 := by rw [hbetaSpin.1, hbetaSpin.2, one_mul]
  have hrSpin : IsSpinElem r := isSpinElem_mul (isSpinElem_cconj hbetaSpin) hg
  -- reversion and Clifford conjugation agree on `r`, hence `reverse r` is even
  have hrev_eq : reverse (Q := q3) r = cconj r := by
    calc reverse (Q := q3) r = 1 * reverse (Q := q3) r := (one_mul _).symm
      _ = cconj r * r * reverse (Q := q3) r := by rw [hrSpin.2]
      _ = cconj r * (r * reverse (Q := q3) r) := by rw [mul_assoc]
      _ = cconj r := by rw [hrevr, mul_one]
  have heven : involute (Q := q3) (reverse (Q := q3) r) = reverse (Q := q3) r := by
    rw [← cconj, hrev_eq]
  obtain ⟨a, v, hav⟩ := even_decomp heven
  -- transport the decomposition back to `r`
  have hrform : r = algebraMap ℝ Cl3 a + omega * ι q3 (-v) := by
    have hh := congrArg (reverse (Q := q3)) hav
    rw [reverse_reverse, map_add, reverse.commutes, reverse_omega_mul, reverse_ι] at hh
    rw [hh, map_neg, mul_neg]
  have hunit : a ^ 2 + sip (-v) (-v) = 1 := by
    have hrr : (algebraMap ℝ Cl3 a + omega * ι q3 (-v))
        * reverse (Q := q3) (algebraMap ℝ Cl3 a + omega * ι q3 (-v)) = 1 := by
      rw [← hrform]; exact hrevr
    rw [map_add, reverse.commutes, reverse_omega_mul, reverse_ι] at hrr
    have hcalc : (algebraMap ℝ Cl3 a + omega * ι q3 (-v))
        * (algebraMap ℝ Cl3 a + -(omega * ι q3 (-v)))
        = algebraMap ℝ Cl3 (a * a + sip (-v) (-v)) := by
      have hA : algebraMap ℝ Cl3 a * (omega * ι q3 (-v)) = a • (omega * ι q3 (-v)) :=
        (Algebra.smul_def a _).symm
      have hA' : omega * ι q3 (-v) * algebraMap ℝ Cl3 a = a • (omega * ι q3 (-v)) := by
        rw [← Algebra.commutes, Algebra.smul_def]
      have hsq : algebraMap ℝ Cl3 a * algebraMap ℝ Cl3 a = algebraMap ℝ Cl3 (a * a) := by
        rw [← map_mul]
      rw [mul_add, add_mul, add_mul, hsq, mul_neg, mul_neg, hA, hA', omega_ι_sq, map_add]
      abel
    rw [hcalc] at hrr
    have := algebraMap_Cl3_injective
      (show algebraMap ℝ Cl3 (a * a + sip (-v) (-v)) = algebraMap ℝ Cl3 1 by
        rw [hrr, map_one])
    nlinarith [this]
  obtain ⟨s, hs⟩ := rotor_is_square hunit
  exact ⟨b, s, by rw [hb, hgr, hrform, hs]⟩

/-! ## The determinant of the induced map -/

theorem spinLorLin_mul (g h : Cl3) :
    spinLorLin (g * h) = (spinLorLin g).comp (spinLorLin h) :=
  LinearMap.ext fun x => by simpa using spinLor_mul g h x

theorem det_spinLorLin_mul (g h : Cl3) :
    LinearMap.det (spinLorLin (g * h))
      = LinearMap.det (spinLorLin g) * LinearMap.det (spinLorLin h) := by
  rw [spinLorLin_mul, LinearMap.det_comp]

/-- The determinant of the induced map of a spin element is nonnegative. -/
theorem det_spinLorLin_nonneg {g : Cl3} (hg : IsSpinElem g) :
    0 ≤ LinearMap.det (spinLorLin g) := by
  obtain ⟨b, s, rfl⟩ := spin_eq_product_of_squares hg
  rw [det_spinLorLin_mul, det_spinLorLin_mul, det_spinLorLin_mul]
  have h1 : LinearMap.det (spinLorLin b) * LinearMap.det (spinLorLin b)
      * (LinearMap.det (spinLorLin s) * LinearMap.det (spinLorLin s))
      = (LinearMap.det (spinLorLin b) * LinearMap.det (spinLorLin s)) ^ 2 := by ring
  rw [h1]
  positivity

theorem spinLorEquiv_coe {g : Cl3} (hg : IsSpinElem g) :
    ((spinLorEquiv hg : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : LorentzCarrier →ₗ[ℝ] LorentzCarrier) = spinLorLin g := rfl

/-- **Phase V (completion).**  The induced map of a spin element has determinant `1`. -/
theorem spinLorEquiv_det {g : Cl3} (hg : IsSpinElem g) :
    LinearMap.det ((spinLorEquiv hg : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : LorentzCarrier →ₗ[ℝ] LorentzCarrier) = 1 := by
  rw [spinLorEquiv_coe hg]
  have hsq : LinearMap.det (spinLorLin g) ^ 2 = 1 := by
    have hd := det_sq_of_NS_preserving (F := spinLorEquiv hg) (fun x => NS_spinLor hg x)
    rwa [spinLorEquiv_coe hg] at hd
  have hnn := det_spinLorLin_nonneg hg
  nlinarith [hsq, hnn]

/-- **Phase V (completion).**  A spin element induces an element of the intrinsic Lorentz
group `G_L` of the carrier: it preserves `N`, the square cone, and the orientation. -/
theorem spinLorEquiv_mem_GLor {g : Cl3} (hg : IsSpinElem g) : spinLorEquiv hg ∈ GLor :=
  ⟨spinLorEquiv_mem_GLorWide hg, spinLorEquiv_det hg⟩

end SpinCore
