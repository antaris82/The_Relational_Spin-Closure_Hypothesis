import Mathlib
import RequestProject.Spine.E1.LorentzGroup

/-!
# Task 10, Branch 4 (part 1) : the exterior square and the intrinsic skew algebra

**Consumed Task 1–9 data.**  The real carrier `𝒮 = SpinCore.LorentzCarrier` and the polarized form
`B_𝒮 = SpinCore.BS` only.  No orientation, no cone, no topology, no differentiability, no
standard Lie-algebra target: `𝔤_B` is defined by the intrinsic skewness condition

`𝔤_B = {A ∈ End_ℝ(𝒮) : B(Ax,y) + B(x,Ay) = 0}`,

and `Λ²𝒮` is the exterior square of the carrier (`CANONICAL_CONSTRUCTION` from the module
structure alone).  `so(1,3)` is not mentioned anywhere in this file.
-/

noncomputable section

namespace SpinCore

open SpinCore

/-! ## E1 : the exterior square -/

theorem finrank_spin : Module.finrank ℝ LorentzCarrier = 4 := by
  rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]

/-- **E1.**  The exterior square of the four-dimensional real carrier has dimension `6`. -/
theorem finrank_extPow2 : Module.finrank ℝ (⋀[ℝ]^2 LorentzCarrier) = 6 := by
  rw [exteriorPower.finrank_eq, finrank_spin]
  decide

/-- Notation for the decomposable bivector `u ∧ v`. -/
def wedge (u v : LorentzCarrier) : ⋀[ℝ]^2 LorentzCarrier := exteriorPower.ιMulti ℝ 2 ![u, v]

/-! ## E2 : the canonical skew endomorphism of a decomposable bivector -/

/-- **E2 (definition).**  `K_{u,v}(x) = B(v,x) u - B(u,x) v`. -/
def Kend (u v : LorentzCarrier) : Module.End ℝ LorentzCarrier where
  toFun x := BS v x • u - BS u x • v
  map_add' x y := by
    rw [BS_add_right, BS_add_right, add_smul, add_smul]
    abel
  map_smul' r x := by
    rw [BS_smul_right, BS_smul_right, mul_smul, mul_smul, smul_sub]
    rfl

@[simp] theorem Kend_apply (u v x : LorentzCarrier) : Kend u v x = BS v x • u - BS u x • v := rfl

/-- **E2 (skewness).** -/
theorem Kend_skew (u v x y : LorentzCarrier) :
    BS (Kend u v x) y + BS x (Kend u v y) = 0 := by
  rw [Kend_apply, Kend_apply, BS_sub_left, BS_smul_left, BS_smul_left,
    BS_sub_right, BS_smul_right, BS_smul_right]
  have h1 : BS u y = BS y u := BS_symm u y
  have h2 : BS v y = BS y v := BS_symm v y
  have h3 : BS x u = BS u x := BS_symm x u
  have h4 : BS x v = BS v x := BS_symm x v
  rw [h3, h4]
  ring

theorem Kend_self (u : LorentzCarrier) : Kend u u = 0 := by
  apply LinearMap.ext
  intro x
  rw [Kend_apply]
  simp

theorem Kend_add_left (u u' v : LorentzCarrier) : Kend (u + u') v = Kend u v + Kend u' v := by
  apply LinearMap.ext
  intro x
  rw [Kend_apply, LinearMap.add_apply, Kend_apply, Kend_apply, BS_add_left, add_smul, smul_add]
  abel

theorem Kend_add_right (u v v' : LorentzCarrier) : Kend u (v + v') = Kend u v + Kend u v' := by
  apply LinearMap.ext
  intro x
  rw [Kend_apply, LinearMap.add_apply, Kend_apply, Kend_apply, BS_add_left, add_smul, smul_add]
  abel

theorem Kend_smul_left (r : ℝ) (u v : LorentzCarrier) : Kend (r • u) v = r • Kend u v := by
  apply LinearMap.ext
  intro x
  rw [Kend_apply, LinearMap.smul_apply, Kend_apply, BS_smul_left, smul_sub, smul_smul,
    smul_smul, smul_smul]
  ring_nf

theorem Kend_smul_right (r : ℝ) (u v : LorentzCarrier) : Kend u (r • v) = r • Kend u v := by
  apply LinearMap.ext
  intro x
  rw [Kend_apply, LinearMap.smul_apply, Kend_apply, BS_smul_left, smul_sub, smul_smul,
    smul_smul, smul_smul]
  ring_nf

/-- The alternating map `(u,v) ↦ K_{u,v}`. -/
def Kalt : LorentzCarrier [⋀^Fin 2]→ₗ[ℝ] (Module.End ℝ LorentzCarrier) where
  toFun m := Kend (m 0) (m 1)
  map_update_add' := by
    intro _ m i x y
    fin_cases i <;>
      simp [Function.update, Kend_add_left, Kend_add_right]
  map_update_smul' := by
    intro _ m i r x
    fin_cases i <;>
      simp [Function.update, Kend_smul_left, Kend_smul_right]
  map_eq_zero_of_eq' := by
    intro v i j hij hne
    fin_cases i <;> fin_cases j <;> simp_all [Kend_self]

/-! ## E2 : the intrinsic skew algebra -/

/-- **E2 (definition).**  The intrinsic `B_𝒮`-skew endomorphisms. -/
def gB : Submodule ℝ (Module.End ℝ LorentzCarrier) where
  carrier := {A : Module.End ℝ LorentzCarrier | ∀ x y : LorentzCarrier, BS (A x) y + BS x (A y) = 0}
  add_mem' := by
    intro A B hA hB x y
    have h1 := hA x y
    have h2 := hB x y
    show BS (A x + B x) y + BS x (A y + B y) = 0
    rw [BS_add_left, BS_add_right]
    linarith
  zero_mem' := by
    intro x y
    show BS 0 y + BS x 0 = 0
    rw [BS_zero_left, BS_zero_right]
    ring
  smul_mem' := by
    intro r A hA x y
    have h := hA x y
    show BS (r • A x) y + BS x (r • A y) = 0
    rw [BS_smul_left, BS_smul_right]
    linear_combination r * h

theorem mem_gB {A : Module.End ℝ LorentzCarrier} :
    A ∈ gB ↔ ∀ x y : LorentzCarrier, BS (A x) y + BS x (A y) = 0 := Iff.rfl

theorem Kend_mem_gB (u v : LorentzCarrier) : Kend u v ∈ gB := fun x y => Kend_skew u v x y

/-- **E3 (bracket closure).**  `𝔤_B` is closed under the commutator. -/
theorem gB_bracket_mem {A B : Module.End ℝ LorentzCarrier} (hA : A ∈ gB) (hB : B ∈ gB) :
    A * B - B * A ∈ gB := by
  intro x y
  have h1 : BS (A (B x)) y = -BS (B x) (A y) := by linarith [hA (B x) y]
  have h2 : BS (B x) (A y) = -BS x (B (A y)) := by linarith [hB x (A y)]
  have h3 : BS (B (A x)) y = -BS (A x) (B y) := by linarith [hB (A x) y]
  have h4 : BS (A x) (B y) = -BS x (A (B y)) := by linarith [hA x (B y)]
  show BS ((A * B - B * A) x) y + BS x ((A * B - B * A) y) = 0
  have e1 : (A * B - B * A) x = A (B x) - B (A x) := rfl
  have e2 : (A * B - B * A) y = A (B y) - B (A y) := rfl
  rw [e1, e2, BS_sub_left, BS_sub_right, h1, h2, h3, h4]
  ring

/-- **E3.**  `𝔤_B` as a Lie subalgebra of `End_ℝ(𝒮)` with the commutator bracket. -/
def gBLie : LieSubalgebra ℝ (Module.End ℝ LorentzCarrier) where
  __ := gB
  lie_mem' := by
    intro A B hA hB
    exact gB_bracket_mem hA hB

/-! ## E2 : the intrinsic map `Λ²𝒮 → 𝔤_B` -/

/-- The linear map `Λ²𝒮 → End_ℝ(𝒮)` induced by `K`. -/
def Phi0 : (⋀[ℝ]^2 LorentzCarrier) →ₗ[ℝ] Module.End ℝ LorentzCarrier :=
  exteriorPower.alternatingMapLinearEquiv Kalt

@[simp] theorem Phi0_wedge (u v : LorentzCarrier) : Phi0 (wedge u v) = Kend u v := by
  rw [Phi0, wedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem Phi0_range_le : LinearMap.range Phi0 ≤ gB := by
  rw [LinearMap.range_eq_map, ← exteriorPower.ιMulti_span (R := ℝ) (n := 2) (M := LorentzCarrier),
    Submodule.map_span, Submodule.span_le]
  rintro A ⟨m, ⟨w, rfl⟩, rfl⟩
  have h : Phi0 (exteriorPower.ιMulti ℝ 2 w) = Kend (w 0) (w 1) := by
    rw [Phi0, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rfl
  rw [h]
  exact Kend_mem_gB _ _

/-- **E2 (main map).**  The intrinsic map `Φ : Λ²𝒮 → 𝔤_B`. -/
def Phi : (⋀[ℝ]^2 LorentzCarrier) →ₗ[ℝ] gB :=
  LinearMap.codRestrict gB Phi0 (fun z => Phi0_range_le ⟨z, rfl⟩)

@[simp] theorem Phi_coe (z : ⋀[ℝ]^2 LorentzCarrier) : ((Phi z : gB) : Module.End ℝ LorentzCarrier) = Phi0 z := rfl

end SpinCore
