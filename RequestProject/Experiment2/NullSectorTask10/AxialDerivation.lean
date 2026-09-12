import RequestProject.Experiment2.NullSectorTask10.HalfAngleSectors

/-!
# Task 10, Layer 8: the axial derivation probe (§25, §26, §27)

No physical time is introduced.  The object of study is purely algebraic: the
real-linear maps `D : W →ₗ[ℝ] W` satisfying

* the Leibniz rule `D (x y) = D x · y + x · D y`,
* `D 1 = 0`,
* `D A = 0` (the distinguished axis is annihilated),
* `D (Trans) ⊆ Trans`,
* skewness of `D` on `Trans` with respect to the inherited old Euclidean
  rest-space form.

The solution space is determined exactly: it is one-dimensional, spanned by a
normalized generator fixed by the orientation convention `D B = C`.  Its action
on the remaining derived basis elements is *computed*, not prescribed, and an
intrinsic commutator formula is derived afterwards.
-/

namespace NullSectorTask10

open NullSectorTask01 NullSectorTask04 NullSectorTask07 NullSectorTask08
open NullSectorTask09

/-- The inherited old Euclidean rest-space form, read off the transverse
coordinates of the carrier.  It is the pullback along `ι₃` of the ordinary
Euclidean form of the transverse old spatial plane. -/
def transForm (x y : W) : ℝ := x 2 * y 2 + x 3 * y 3

theorem transForm_iota3 (X Y : Vec4) :
    transForm (iota3 X) (iota3 Y) = X.2.2.1 * Y.2.2.1 + X.2.2.2 * Y.2.2.2 := by
  simp [transForm]

/-! ## §25 — the structural conditions -/

/-- **THE AXIAL DERIVATION PROBLEM (§25).**  Purely structural; no evolution
parameter, no time, no dynamics. -/
structure IsAxialDerivation (D : W →ₗ[ℝ] W) : Prop where
  /-- Leibniz rule for the inherited product. -/
  leibniz : ∀ x y : W, D (x ⋆ y) = D x ⋆ y + x ⋆ D y
  /-- The unit is annihilated. -/
  unit : D w1 = 0
  /-- The distinguished axis is annihilated. -/
  axis : D wA = 0
  /-- The transverse plane is preserved. -/
  trans : ∀ x ∈ TransW, D x ∈ TransW
  /-- Skewness on the transverse plane for the inherited old Euclidean form. -/
  skew : ∀ x ∈ TransW, ∀ y ∈ TransW, transForm (D x) y + transForm x (D y) = 0

/-! ## §26 — solving the conditions -/

theorem wB_mem_TransW : wB ∈ TransW := Submodule.subset_span (by simp)
theorem wC_mem_TransW : wC ∈ TransW := Submodule.subset_span (by simp)

section Forced

variable {D : W →ₗ[ℝ] W} (hD : IsAxialDerivation D)

include hD in
/-- On the transverse plane the derivation is a rotation generator: a single
real parameter survives. -/
theorem forced_transverse :
    ∃ l : ℝ, D wB = l • wC ∧ D wC = (-l) • wB := by
  obtain ⟨b1, c1, hB⟩ := (mem_TransW_iff _).1 (hD.trans wB wB_mem_TransW)
  obtain ⟨b2, c2, hC⟩ := (mem_TransW_iff _).1 (hD.trans wC wC_mem_TransW)
  have hBB := hD.skew wB wB_mem_TransW wB wB_mem_TransW
  have hCC := hD.skew wC wC_mem_TransW wC wC_mem_TransW
  have hBC := hD.skew wB wB_mem_TransW wC wC_mem_TransW
  rw [hB] at hBB hBC
  rw [hC] at hCC hBC
  simp [transForm, wB, wC] at hBB hCC hBC
  refine ⟨c1, ?_, ?_⟩
  · rw [hB, hBB, zero_smul, zero_add]
  · rw [hC, hCC, zero_smul, add_zero]
    congr 1
    linarith

include hD in
theorem deriv_forced_wP {l : ℝ} (hB : D wB = l • wC) : D wP = l • wQ := by
  have h : D (wA ⋆ wB) = D wA ⋆ wB + wA ⋆ D wB := hD.leibniz wA wB
  rw [wit8_wA_wB, hD.axis, zero_mul_W, zero_add, hB, mul_smul_W, wit8_wA_wC] at h
  exact h

include hD in
theorem deriv_forced_wQ {l : ℝ} (hC : D wC = (-l) • wB) : D wQ = (-l) • wP := by
  have h : D (wA ⋆ wC) = D wA ⋆ wC + wA ⋆ D wC := hD.leibniz wA wC
  rw [wit8_wA_wC, hD.axis, zero_mul_W, zero_add, hC, mul_smul_W, wit8_wA_wB] at h
  exact h

include hD in
theorem deriv_forced_wR {l : ℝ} (hB : D wB = l • wC) (hC : D wC = (-l) • wB) :
    D wR = 0 := by
  have h : D (wB ⋆ wC) = D wB ⋆ wC + wB ⋆ D wC := hD.leibniz wB wC
  rw [wit8_wB_wC, hB, hC, smul_mul_W, mul_smul_W, wit8_wC_wC, wit8_wB_wB] at h
  rw [h]
  module

include hD in
theorem deriv_forced_wS {l : ℝ} (hB : D wB = l • wC) (hC : D wC = (-l) • wB) :
    D wS = 0 := by
  have h : D (wA ⋆ wR) = D wA ⋆ wR + wA ⋆ D wR := hD.leibniz wA wR
  rw [wit8_wA_wR, hD.axis, zero_mul_W, zero_add, deriv_forced_wR hD hB hC,
    mul_zero_W] at h
  exact h

end Forced

/-! ## The explicit generator -/

/-- Coordinate description of the normalized axial derivation. -/
def DgenFun (x : W) : W := ![0, 0, -x 3, x 2, -x 5, x 4, 0, 0]

/-- **THE NORMALIZED AXIAL DERIVATION**, as a real-linear map. -/
def Dgen : W →ₗ[ℝ] W where
  toFun := DgenFun
  map_add' := by intro x y; funext i; fin_cases i <;> simp [DgenFun] <;> ring
  map_smul' := by intro c x; funext i; fin_cases i <;> simp [DgenFun]

@[simp] theorem Dgen_coord_0 (x : W) : Dgen x 0 = 0 := by simp [Dgen, DgenFun]
@[simp] theorem Dgen_coord_1 (x : W) : Dgen x 1 = 0 := by simp [Dgen, DgenFun]
@[simp] theorem Dgen_coord_2 (x : W) : Dgen x 2 = -x 3 := by simp [Dgen, DgenFun]
@[simp] theorem Dgen_coord_3 (x : W) : Dgen x 3 = x 2 := by simp [Dgen, DgenFun]
@[simp] theorem Dgen_coord_4 (x : W) : Dgen x 4 = -x 5 := by simp [Dgen, DgenFun]
@[simp] theorem Dgen_coord_5 (x : W) : Dgen x 5 = x 4 := by simp [Dgen, DgenFun]
@[simp] theorem Dgen_coord_6 (x : W) : Dgen x 6 = 0 := by simp [Dgen, DgenFun]
@[simp] theorem Dgen_coord_7 (x : W) : Dgen x 7 = 0 := by simp [Dgen, DgenFun]

@[simp] theorem Dgen_w1 : Dgen w1 = 0 := by
  funext i; fin_cases i <;> simp [w1]
@[simp] theorem Dgen_wA : Dgen wA = 0 := by
  funext i; fin_cases i <;> simp [wA]
@[simp] theorem Dgen_wB : Dgen wB = wC := by
  funext i; fin_cases i <;> simp [wB, wC]
@[simp] theorem Dgen_wC : Dgen wC = -wB := by
  funext i; fin_cases i <;> simp [wB, wC]
@[simp] theorem Dgen_wP : Dgen wP = wQ := by
  funext i; fin_cases i <;> simp [wP, wQ]
@[simp] theorem Dgen_wQ : Dgen wQ = -wP := by
  funext i; fin_cases i <;> simp [wP, wQ]
@[simp] theorem Dgen_wR : Dgen wR = 0 := by
  funext i; fin_cases i <;> simp [wR]
@[simp] theorem Dgen_wS : Dgen wS = 0 := by
  funext i; fin_cases i <;> simp [wS]

theorem Dgen_leibniz (x y : W) : Dgen (x ⋆ y) = Dgen x ⋆ y + x ⋆ Dgen y := by
  have h0 : Dgen (x ⋆ y) 0 = (Dgen x ⋆ y + x ⋆ Dgen y) 0 := by
    simp only [Dgen_coord_0, Dgen_coord_1, Dgen_coord_2, Dgen_coord_3,
      Dgen_coord_4, Dgen_coord_5, Dgen_coord_6, Dgen_coord_7,
      wit8Mul_coord_0, Pi.add_apply]; ring
  have h1 : Dgen (x ⋆ y) 1 = (Dgen x ⋆ y + x ⋆ Dgen y) 1 := by
    simp only [Dgen_coord_0, Dgen_coord_1, Dgen_coord_2, Dgen_coord_3,
      Dgen_coord_4, Dgen_coord_5, Dgen_coord_6, Dgen_coord_7,
      wit8Mul_coord_1, Pi.add_apply]; ring
  have h2 : Dgen (x ⋆ y) 2 = (Dgen x ⋆ y + x ⋆ Dgen y) 2 := by
    simp only [Dgen_coord_0, Dgen_coord_1, Dgen_coord_2, Dgen_coord_3,
      Dgen_coord_4, Dgen_coord_5, Dgen_coord_6, Dgen_coord_7,
      wit8Mul_coord_2, wit8Mul_coord_3, Pi.add_apply]; ring
  have h3 : Dgen (x ⋆ y) 3 = (Dgen x ⋆ y + x ⋆ Dgen y) 3 := by
    simp only [Dgen_coord_0, Dgen_coord_1, Dgen_coord_2, Dgen_coord_3,
      Dgen_coord_4, Dgen_coord_5, Dgen_coord_6, Dgen_coord_7,
      wit8Mul_coord_2, wit8Mul_coord_3, Pi.add_apply]; ring
  have h4 : Dgen (x ⋆ y) 4 = (Dgen x ⋆ y + x ⋆ Dgen y) 4 := by
    simp only [Dgen_coord_0, Dgen_coord_1, Dgen_coord_2, Dgen_coord_3,
      Dgen_coord_4, Dgen_coord_5, Dgen_coord_6, Dgen_coord_7,
      wit8Mul_coord_4, wit8Mul_coord_5, Pi.add_apply]; ring
  have h5 : Dgen (x ⋆ y) 5 = (Dgen x ⋆ y + x ⋆ Dgen y) 5 := by
    simp only [Dgen_coord_0, Dgen_coord_1, Dgen_coord_2, Dgen_coord_3,
      Dgen_coord_4, Dgen_coord_5, Dgen_coord_6, Dgen_coord_7,
      wit8Mul_coord_4, wit8Mul_coord_5, Pi.add_apply]; ring
  have h6 : Dgen (x ⋆ y) 6 = (Dgen x ⋆ y + x ⋆ Dgen y) 6 := by
    simp only [Dgen_coord_0, Dgen_coord_1, Dgen_coord_2, Dgen_coord_3,
      Dgen_coord_4, Dgen_coord_5, Dgen_coord_6, Dgen_coord_7,
      wit8Mul_coord_6, Pi.add_apply]; ring
  have h7 : Dgen (x ⋆ y) 7 = (Dgen x ⋆ y + x ⋆ Dgen y) 7 := by
    simp only [Dgen_coord_0, Dgen_coord_1, Dgen_coord_2, Dgen_coord_3,
      Dgen_coord_4, Dgen_coord_5, Dgen_coord_6, Dgen_coord_7,
      wit8Mul_coord_7, Pi.add_apply]; ring
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

theorem Dgen_mem_TransW {x : W} (hx : x ∈ TransW) : Dgen x ∈ TransW := by
  obtain ⟨b, c, rfl⟩ := (mem_TransW_iff x).1 hx
  rw [map_add, map_smul, map_smul, Dgen_wB, Dgen_wC, mem_TransW_iff]
  exact ⟨-c, b, by module⟩

/-- **EXISTENCE.**  The normalized generator satisfies all structural
conditions. -/
theorem Dgen_isAxialDerivation : IsAxialDerivation Dgen where
  leibniz := Dgen_leibniz
  unit := Dgen_w1
  axis := Dgen_wA
  trans _ hx := Dgen_mem_TransW hx
  skew := by
    intro x hx y hy
    obtain ⟨b, c, rfl⟩ := (mem_TransW_iff x).1 hx
    obtain ⟨b', c', rfl⟩ := (mem_TransW_iff y).1 hy
    rw [map_add, map_add, map_smul, map_smul, map_smul, map_smul,
      Dgen_wB, Dgen_wC]
    simp [transForm, wB, wC]
    ring

/-! ## §26 — the exact solution space -/

/-- **THE CLASSIFICATION (§26).**  The space of axial derivations is exactly the
real line through the normalized generator: the structure fixes the generator
**direction**, and nothing more. -/
theorem axialDerivation_classification (D : W →ₗ[ℝ] W) :
    IsAxialDerivation D ↔ ∃ l : ℝ, D = l • Dgen := by
  constructor
  · intro hD
    obtain ⟨l, hB, hC⟩ := forced_transverse hD
    refine ⟨l, linMap_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
      simp only [LinearMap.smul_apply, Dgen_w1, Dgen_wA, Dgen_wB, Dgen_wC,
        Dgen_wP, Dgen_wQ, Dgen_wR, Dgen_wS, hD.unit, hD.axis, hB, hC,
        deriv_forced_wP hD hB, deriv_forced_wQ hD hC,
        deriv_forced_wR hD hB hC, deriv_forced_wS hD hB hC] <;>
      module
  · rintro ⟨l, rfl⟩
    exact
      { leibniz := by
          intro x y
          simp only [LinearMap.smul_apply, Dgen_leibniz, smul_add, smul_mul_W,
            mul_smul_W]
        unit := by simp
        axis := by simp
        trans := by
          intro x hx
          simp only [LinearMap.smul_apply]
          exact Submodule.smul_mem _ _ (Dgen_mem_TransW hx)
        skew := by
          intro x hx y hy
          have h := Dgen_isAxialDerivation.skew x hx y hy
          simp only [LinearMap.smul_apply, transForm, Pi.smul_apply, smul_eq_mul]
          simp only [transForm] at h
          linear_combination l * h }

/-- **UNIQUENESS AFTER THE ORIENTATION CONVENTION.**  Fixing `D B = C` singles
out exactly one axial derivation. -/
theorem axialDerivation_unique_of_orientation {D : W →ₗ[ℝ] W}
    (hD : IsAxialDerivation D) (hor : D wB = wC) : D = Dgen := by
  obtain ⟨l, rfl⟩ := (axialDerivation_classification D).1 hD
  simp only [LinearMap.smul_apply, Dgen_wB] at hor
  have hl : l = 1 := by
    have h := congrFun hor 3
    simpa [wC] using h
  rw [hl, one_smul]

theorem Dgen_ne_zero : Dgen ≠ 0 := by
  intro h
  have h2 := congrArg (fun f : W →ₗ[ℝ] W => f wB) h
  simp only [LinearMap.zero_apply, Dgen_wB] at h2
  have h3 := congrFun h2 3
  simp [wC] at h3

/-- **THE SOLUTION SPACE IS EXACTLY ONE-DIMENSIONAL.** -/
theorem finrank_axialDerivations :
    Module.finrank ℝ (Submodule.span ℝ {Dgen}) = 1 :=
  finrank_span_singleton Dgen_ne_zero

/-! ## §27 — an intrinsic formula -/

/-- One half of the commutator with the derived transverse channel `R`, as a
real-linear map. -/
noncomputable def Ccom : W →ₗ[ℝ] W where
  toFun x := (2⁻¹ : ℝ) • (x ⋆ wR - wR ⋆ x)
  map_add' := by
    intro x y
    simp only [add_mul_W, mul_add_W]
    module
  map_smul' := by
    intro c x
    simp only [smul_mul_W, mul_smul_W, RingHom.id_apply]
    module

/-- **THE INTRINSIC FORMULA (§27).**  The normalized axial derivation is one
half of the commutator with the derived transverse channel `R`.  The formula was
not prescribed; it is verified on the derived basis after the classification. -/
theorem Dgen_eq_Ccom : Dgen = Ccom := by
  refine linMap_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [Dgen_w1, Ccom, LinearMap.coe_mk, AddHom.coe_mk, mul_one_W, one_mul_W]
    module
  · simp only [Dgen_wA, Ccom, LinearMap.coe_mk, AddHom.coe_mk, wit8_wA_wR, wit8_wR_wA]
    module
  · simp only [Dgen_wB, Ccom, LinearMap.coe_mk, AddHom.coe_mk, wit8_wB_wR, wit8_wR_wB]
    module
  · simp only [Dgen_wC, Ccom, LinearMap.coe_mk, AddHom.coe_mk, wit8_wC_wR, wit8_wR_wC]
    module
  · simp only [Dgen_wP, Ccom, LinearMap.coe_mk, AddHom.coe_mk, wit8_wP_wR, wit8_wR_wP]
    module
  · simp only [Dgen_wQ, Ccom, LinearMap.coe_mk, AddHom.coe_mk, wit8_wQ_wR, wit8_wR_wQ]
    module
  · simp only [Dgen_wR, Ccom, LinearMap.coe_mk, AddHom.coe_mk]
    module
  · simp only [Dgen_wS, Ccom, LinearMap.coe_mk, AddHom.coe_mk, wit8_wS_wR, wit8_wR_wS]
    module

theorem Dgen_eq_half_commutator (x : W) :
    Dgen x = (2⁻¹ : ℝ) • (x ⋆ wR - wR ⋆ x) := by
  rw [Dgen_eq_Ccom]; rfl

/-! ### Comparison with the infinitesimal generator of the algebra family -/

/-- **THE ALGEBRA FAMILY IS DIFFERENTIABLE AT ZERO WITH THIS GENERATOR.**  The
derivative of `θ ↦ Φθ x` at `θ = 0` is exactly `Dgen x`; the normalized
derivation is therefore the infinitesimal generator of the axial automorphism
family. -/
theorem hasDerivAt_Phi_zero (x : W) :
    HasDerivAt (fun θ => Phi θ x) (Dgen x) 0 := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa using hasDerivAt_const (0 : ℝ) (x 0)
  · simpa using hasDerivAt_const (0 : ℝ) (x 1)
  · simpa using
      ((Real.hasDerivAt_cos 0).mul_const (x 2)).sub ((Real.hasDerivAt_sin 0).mul_const (x 3))
  · simpa using
      ((Real.hasDerivAt_sin 0).mul_const (x 2)).add ((Real.hasDerivAt_cos 0).mul_const (x 3))
  · simpa using
      ((Real.hasDerivAt_cos 0).mul_const (x 4)).sub ((Real.hasDerivAt_sin 0).mul_const (x 5))
  · simpa using
      ((Real.hasDerivAt_sin 0).mul_const (x 4)).add ((Real.hasDerivAt_cos 0).mul_const (x 5))
  · simpa using hasDerivAt_const (0 : ℝ) (x 6)
  · simpa using hasDerivAt_const (0 : ℝ) (x 7)

end NullSectorTask10
