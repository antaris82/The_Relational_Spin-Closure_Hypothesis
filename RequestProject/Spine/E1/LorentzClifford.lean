import Mathlib
import RequestProject.Spine.E1.Clifford
import RequestProject.Spine.E1.Hodge

/-!
# Task 11, Phase IV, obligations E1 and E2 : the Lorentz Clifford branch and the bivector map

## E1 — the conventions, verified rather than remembered (falsification test K8)

Mathlib's Clifford convention is

`ι Q v * ι Q v = algebraMap R _ (Q v)`  (`CliffordAlgebra.ι_sq_scalar`),

i.e. *the square of a vector is `+Q(v)`*, with no minus sign.  Under this convention the
Task-9 algebra `Cl₃(ℝ) = CliffordAlgebra q3`, with `q3 v = ⟪v,v⟫ > 0`, has generators
squaring to `+1` (`SpinCore.cle_sq`); it is the Euclidean algebra usually written
`Cl_{3,0}(ℝ)`.  This is recorded as `SpinCore.clifford_square_convention`.

The intrinsic Lorentz quadratic form of the carrier is `SpinCore.qN`, with
`qN x = N(x) = t² - |v|²` (`SpinCore.qN_apply`) — signature `(1,3)` in the same convention
(`SpinCore.lorentz_square_convention`: the intrinsic unit squares to `+1`, a spatial vector
squares to `-1`).

The textbook statement `Cl⁰_{1,3}(ℝ) ≅ Cl_{3,0}(ℝ)` is therefore **not** assumed.  What is
constructed here, from project data only, is the canonical algebra map

`SpinCore.evenToCl3 : Cl⁰(q_N) →ₐ[ℝ] Cl₃(ℝ)`,

obtained from the *universal property of the even Clifford algebra*
(`CliffordAlgebra.even.lift`) applied to the intrinsic bilinear datum

`bilin x y = (t_x + c(u_x)) · (t_y - c(u_y))`,

where `c = ι q3` is the Task-9 Clifford embedding of `V`.  Concretely this implements the
classical identification `γ_i γ_0 ↦ e_i`, `γ_i γ_j ↦ -e_i e_j`, but it is *derived* from
the universal property, not posited.  `SpinCore.evenToCl3_surjective` shows that the map is
onto, so `Cl₃(ℝ)` is a quotient of the even Lorentz Clifford algebra; injectivity (hence
the full isomorphism) is **not** claimed here — see the Phase-IV checkpoint.

## E2 — the bivector map

`SpinCore.iota : Λ²𝒮 →ₗ[ℝ] Cl₃(ℝ)` is defined by the alternating map

`x ∧ y ↦ ½ (bilin x y - bilin y x)`,

so it is the antisymmetric part of exactly the same universal datum
(`SpinCore.iota_wedge_eq_even`, which exhibits the factorisation through `Cl⁰(q_N)`).  No
Pauli matrix and no `M₂(ℂ)` occurs in the construction.

Injectivity of `iota` and the pseudoscalar identity are in
`RequestProject/Task11CliffordHodgeBridge.lean`.
-/

noncomputable section

open CliffordAlgebra

namespace SpinCore

open SpinCore

/-! ## E1 : the two quadratic forms and the Lean sign convention -/

/-- **K8.**  Mathlib's convention, verified in the project's own algebra: the square of a
vector is `+q(v)`, so the Task-9 generators square to `+1`. -/
theorem clifford_square_convention (v : Fin 3 → ℝ) :
    ι q3 v * ι q3 v = algebraMap ℝ Cl3 (sip v v) :=
  ι_sq_scalar q3 v

/-- The intrinsic Lorentz bilinear form as a bilinear map. -/
def bilN : LinearMap.BilinMap ℝ LorentzCarrier ℝ :=
  LinearMap.mk₂ ℝ (fun x y => BS x y)
    (by intros; simp only [BS_eq, sip, Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring)
    (by intros; simp only [BS_eq, sip, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
          smul_eq_mul]; ring)
    (by intros; simp only [BS_eq, sip, Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring)
    (by intros; simp only [BS_eq, sip, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
          smul_eq_mul]; ring)

@[simp] theorem bilN_apply (x y : LorentzCarrier) : bilN x y = BS x y := rfl

/-- The intrinsic Lorentz quadratic form `N` of the carrier, as a `QuadraticForm`. -/
def qN : QuadraticForm ℝ LorentzCarrier := LinearMap.BilinMap.toQuadraticMap bilN

@[simp] theorem qN_apply (x : LorentzCarrier) : qN x = NS x := by
  show BS x x = NS x
  rw [BS_eq]
  simp [NS, sip]
  ring

/-- **K8 (Lorentz side).**  In the same Lean convention the intrinsic unit squares to `+1`
and a spatial direction squares to `-1`: the signature is `(1,3)`. -/
theorem lorentz_square_convention :
    qN sOne = 1 ∧ ∀ i : Fin 3, qN (bvec i) = -1 := by
  refine ⟨by simp [sOne, NS, sip], fun i => ?_⟩
  fin_cases i <;> simp [bvec, evec, NS, sip]

/-! ## The intrinsic bilinear datum -/

/-- The Task-9 embedding `𝒮 → Cl₃(ℝ)` with the spatial part negated. -/
def spinToClBar (x : LorentzCarrier) : Cl3 := algebraMap ℝ Cl3 x.1 - ι q3 x.2

@[simp] theorem spinToClBar_apply (x : LorentzCarrier) :
    spinToClBar x = algebraMap ℝ Cl3 x.1 - ι q3 x.2 := rfl

theorem spinToCl_add (x y : LorentzCarrier) : spinToCl (x + y) = spinToCl x + spinToCl y := by
  simp only [spinToCl_apply, Prod.fst_add, Prod.snd_add, map_add]
  abel

theorem spinToCl_smul (r : ℝ) (x : LorentzCarrier) : spinToCl (r • x) = r • spinToCl x := by
  simp only [spinToCl_apply, Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul,
    Algebra.algebraMap_eq_smul_one, smul_add, smul_smul]

theorem spinToClBar_add (x y : LorentzCarrier) :
    spinToClBar (x + y) = spinToClBar x + spinToClBar y := by
  simp only [spinToClBar_apply, Prod.fst_add, Prod.snd_add, map_add]
  abel

theorem spinToClBar_smul (r : ℝ) (x : LorentzCarrier) :
    spinToClBar (r • x) = r • spinToClBar x := by
  simp only [spinToClBar_apply, Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul,
    Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul]

/-- `A(x) · Ā(x) = N(x)`. -/
theorem spinToCl_mul_bar (x : LorentzCarrier) :
    spinToCl x * spinToClBar x = algebraMap ℝ Cl3 (NS x) := by
  obtain ⟨a, u⟩ := x
  simp only [spinToCl_apply, spinToClBar_apply]
  have h : ι q3 u * ι q3 u = algebraMap ℝ Cl3 (sip u u) := clifford_square_convention u
  have hc : algebraMap ℝ Cl3 a * ι q3 u = ι q3 u * algebraMap ℝ Cl3 a :=
    Algebra.commutes a _
  show (algebraMap ℝ Cl3 a + ι q3 u) * (algebraMap ℝ Cl3 a - ι q3 u)
      = algebraMap ℝ Cl3 (a ^ 2 - sip u u)
  rw [mul_sub, add_mul, add_mul, ← hc, h, map_sub, ← map_mul, ← pow_two]
  abel

/-- `Ā(x) · A(x) = N(x)`. -/
theorem bar_mul_spinToCl (x : LorentzCarrier) :
    spinToClBar x * spinToCl x = algebraMap ℝ Cl3 (NS x) := by
  obtain ⟨a, u⟩ := x
  simp only [spinToCl_apply, spinToClBar_apply]
  have h : ι q3 u * ι q3 u = algebraMap ℝ Cl3 (sip u u) := clifford_square_convention u
  have hc : algebraMap ℝ Cl3 a * ι q3 u = ι q3 u * algebraMap ℝ Cl3 a :=
    Algebra.commutes a _
  show (algebraMap ℝ Cl3 a - ι q3 u) * (algebraMap ℝ Cl3 a + ι q3 u)
      = algebraMap ℝ Cl3 (a ^ 2 - sip u u)
  rw [mul_add, sub_mul, sub_mul, ← hc, h, map_sub, ← map_mul, ← pow_two]
  abel

/-- The intrinsic bilinear datum `bilin x y = A(x) Ā(y)`. -/
def clBil : LorentzCarrier →ₗ[ℝ] LorentzCarrier →ₗ[ℝ] Cl3 :=
  LinearMap.mk₂ ℝ (fun x y => spinToCl x * spinToClBar y)
    (by intro x x' y; dsimp only; rw [spinToCl_add, add_mul])
    (by intro r x y; dsimp only; rw [spinToCl_smul, smul_mul_assoc])
    (by intro x y y'; dsimp only; rw [spinToClBar_add, mul_add])
    (by intro r x y; dsimp only; rw [spinToClBar_smul, mul_smul_comm])

@[simp] theorem clBil_apply (x y : LorentzCarrier) : clBil x y = spinToCl x * spinToClBar y := rfl

/-- The even Clifford datum: a bilinear map satisfying the two `EvenHom` identities. -/
def evenHomSpin : EvenHom qN Cl3 where
  bilin := clBil
  contract m := by
    rw [clBil_apply, spinToCl_mul_bar, qN_apply]
  contract_mid m₁ m₂ m₃ := by
    rw [clBil_apply, clBil_apply, clBil_apply, qN_apply, mul_assoc, ← mul_assoc (spinToClBar m₂),
      bar_mul_spinToCl, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      mul_smul_comm]

/-- **E1 (main construction).**  The canonical algebra map from the even part of the
intrinsic Lorentz Clifford algebra to the Task-9 Euclidean Clifford algebra, obtained from
the universal property of the even subalgebra. -/
def evenToCl3 : (CliffordAlgebra.even qN) →ₐ[ℝ] Cl3 := CliffordAlgebra.even.lift qN evenHomSpin

@[simp] theorem evenToCl3_ι (x y : LorentzCarrier) :
    evenToCl3 ((CliffordAlgebra.even.ι qN).bilin x y) = spinToCl x * spinToClBar y :=
  CliffordAlgebra.even.lift_ι qN evenHomSpin x y

/-- The classical dictionary, *derived*: `γ_i γ_0 ↦ e_i`. -/
theorem evenToCl3_bvec_one (i : Fin 3) :
    evenToCl3 ((CliffordAlgebra.even.ι qN).bilin (bvec i) sOne) = cle i := by
  rw [evenToCl3_ι]
  show (algebraMap ℝ Cl3 (0:ℝ) + ι q3 (evec i)) * (algebraMap ℝ Cl3 (1:ℝ) - ι q3 0) = cle i
  simp [cle]

/-- The classical dictionary, *derived*: `γ_i γ_j ↦ -e_i e_j`. -/
theorem evenToCl3_bvec_bvec (i j : Fin 3) :
    evenToCl3 ((CliffordAlgebra.even.ι qN).bilin (bvec i) (bvec j)) = -(cle i * cle j) := by
  rw [evenToCl3_ι]
  show (algebraMap ℝ Cl3 (0:ℝ) + ι q3 (evec i)) * (algebraMap ℝ Cl3 (0:ℝ) - ι q3 (evec j))
      = -(cle i * cle j)
  simp [cle]

/-- **E1.**  `evenToCl3` is surjective: `Cl₃(ℝ)` is a quotient of `Cl⁰(q_N)`. -/
theorem evenToCl3_surjective : Function.Surjective evenToCl3 := by
  have hrange : evenToCl3.range = ⊤ := by
    have hgen : Algebra.adjoin ℝ (Set.range (ι q3)) = ⊤ := adjoin_range_ι
    refine top_le_iff.mp ?_
    rw [← hgen]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, rfl⟩
    refine ⟨(CliffordAlgebra.even.ι qN).bilin ((0:ℝ), v) sOne, ?_⟩
    show evenToCl3 ((CliffordAlgebra.even.ι qN).bilin ((0:ℝ), v) sOne) = ι q3 v
    rw [evenToCl3_ι]
    show (algebraMap ℝ Cl3 (0:ℝ) + ι q3 v) * (algebraMap ℝ Cl3 (1:ℝ) - ι q3 0) = ι q3 v
    simp
  intro y
  have : y ∈ evenToCl3.range := by rw [hrange]; trivial
  exact this

/-! ## E2 : the bivector map -/

/-- The value of `ι` on a decomposable bivector: the antisymmetric part of the even datum. -/
def iotaFun (x y : LorentzCarrier) : Cl3 :=
  (2:ℝ)⁻¹ • (spinToCl x * spinToClBar y - spinToCl y * spinToClBar x)

theorem iotaFun_add_left (x x' y : LorentzCarrier) :
    iotaFun (x + x') y = iotaFun x y + iotaFun x' y := by
  simp only [iotaFun, spinToCl_add, spinToClBar_add, add_mul, mul_add]
  module

theorem iotaFun_add_right (x y y' : LorentzCarrier) :
    iotaFun x (y + y') = iotaFun x y + iotaFun x y' := by
  simp only [iotaFun, spinToCl_add, spinToClBar_add, add_mul, mul_add]
  module

theorem iotaFun_smul_left (r : ℝ) (x y : LorentzCarrier) :
    iotaFun (r • x) y = r • iotaFun x y := by
  simp only [iotaFun, spinToCl_smul, spinToClBar_smul, smul_mul_assoc, mul_smul_comm]
  module

theorem iotaFun_smul_right (r : ℝ) (x y : LorentzCarrier) :
    iotaFun x (r • y) = r • iotaFun x y := by
  simp only [iotaFun, spinToCl_smul, spinToClBar_smul, smul_mul_assoc, mul_smul_comm]
  module

theorem iotaFun_self (x : LorentzCarrier) : iotaFun x x = 0 := by
  simp [iotaFun]

/-- The alternating map underlying `ι`. -/
def iotaAlt : LorentzCarrier [⋀^Fin 2]→ₗ[ℝ] Cl3 where
  toFun m := iotaFun (m 0) (m 1)
  map_update_add' := by
    intro _ m i x y
    fin_cases i <;> simp [Function.update, iotaFun_add_left, iotaFun_add_right]
  map_update_smul' := by
    intro _ m i r x
    fin_cases i <;> simp [Function.update, iotaFun_smul_left, iotaFun_smul_right]
  map_eq_zero_of_eq' := by
    intro m i j hij hne
    fin_cases i <;> fin_cases j <;> simp_all [iotaFun_self]

/-- **E2 (definition).**  The canonical map `ι : Λ²𝒮 → Cl₃(ℝ)`. -/
def iota : (⋀[ℝ]^2 LorentzCarrier) →ₗ[ℝ] Cl3 :=
  exteriorPower.alternatingMapLinearEquiv iotaAlt

@[simp] theorem iota_wedge (x y : LorentzCarrier) : iota (wedge x y) = iotaFun x y := by
  rw [iota, wedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- **E2.**  `ι` factors through the even Lorentz Clifford algebra: on decomposables it is
the antisymmetric part of the universal even datum. -/
theorem iota_wedge_eq_even (x y : LorentzCarrier) :
    iota (wedge x y)
      = (2:ℝ)⁻¹ • (evenToCl3 ((CliffordAlgebra.even.ι qN).bilin x y)
          - evenToCl3 ((CliffordAlgebra.even.ι qN).bilin y x)) := by
  rw [iota_wedge, evenToCl3_ι, evenToCl3_ι, iotaFun]

end SpinCore
