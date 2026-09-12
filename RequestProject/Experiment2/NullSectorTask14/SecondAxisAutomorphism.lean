import RequestProject.Experiment2.NullSectorTask14.SecondAxisOldStructure

/-!
# Task 14, Layer 2 (§10, §11): the independent second-axis transformation and its
algebra extension

**INDEPENDENT SECOND-AXIS DERIVATION.**  The one-parameter family `rotB` is constructed
directly from the inherited old-space requirements of §10:

* the old temporal unit is fixed;
* the second axis `B` is fixed;
* the inherited rest space is preserved;
* the inherited spatial form (and the inherited `Q4`) is preserved;
* the family acts nontrivially on the second transverse plane;
* it is the identity at `0` and additive in the parameter.

It is **not** obtained by conjugating the inherited A-axis family with any spatial
transformation.

*Orientation audit (§10).*  The requirement list above does not select a sign: the
reversed family `φ ↦ rotB (-φ)` satisfies exactly the same list, and the two families
differ.  Both branches are recorded in `second_axis_orientation_branches`; the branch used
below is a **documented convention** (the one for which `C` turns towards `A`), never a
derived fact.

For §11 the extension problem for an *unknown* real-linear map is posed, its values on all
eight derived basis elements are **forced**, uniqueness is proved, and only afterwards is
an explicit witness exhibited and verified.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask12 NullSectorTask13

/-! ## §10 — the second-axis old transformation -/

/-- **INDEPENDENT SECOND-AXIS DERIVATION (§10).**  The chosen branch of the second-axis
old transformation: the temporal coordinate and the second spatial coordinate are fixed,
and the remaining two spatial coordinates are mixed. -/
noncomputable def rotB (φ : ℝ) : Vec4 →ₗ[ℝ] Vec4 where
  toFun X := (X.1,
    Real.cos φ * X.2.1 + Real.sin φ * X.2.2.2,
    X.2.2.1,
    -(Real.sin φ) * X.2.1 + Real.cos φ * X.2.2.2)
  map_add' := by intro X Y; simp [Prod.ext_iff]; constructor <;> ring
  map_smul' := by intro c X; simp [Prod.ext_iff]; constructor <;> ring

@[simp] theorem rotB_apply (φ : ℝ) (X : Vec4) :
    rotB φ X = (X.1,
      Real.cos φ * X.2.1 + Real.sin φ * X.2.2.2,
      X.2.2.1,
      -(Real.sin φ) * X.2.1 + Real.cos φ * X.2.2.2) := rfl

@[simp] theorem rotB_e₀ (φ : ℝ) : rotB φ e₀ = e₀ := by simp [e₀]

/-- **DERIVED (§10).**  The second axis is fixed. -/
@[simp] theorem rotB_dirB (φ : ℝ) : rotB φ dirB = dirB := by simp [dirB, sp, s₂]

/-- **DERIVED (§10).**  The action on the two inherited transverse directions. -/
@[simp] theorem rotB_dirA (φ : ℝ) :
    rotB φ dirA = Real.cos φ • dirA + (-Real.sin φ) • dirC := by
  simp [dirA, dirC, sp, s₁, s₃, Prod.ext_iff]

@[simp] theorem rotB_dirC (φ : ℝ) :
    rotB φ dirC = Real.sin φ • dirA + Real.cos φ • dirC := by
  simp [dirA, dirC, sp, s₁, s₃, Prod.ext_iff]

/-- **DERIVED (§10).**  Identity at the zero parameter. -/
theorem rotB_zero : rotB 0 = LinearMap.id := by
  refine LinearMap.ext fun X => ?_
  simp

/-- **DERIVED (§10).**  Additive composition. -/
theorem rotB_add (φ χ : ℝ) : rotB (φ + χ) = (rotB φ).comp (rotB χ) := by
  refine LinearMap.ext fun X => ?_
  simp only [rotB_apply, LinearMap.comp_apply, Real.cos_add, Real.sin_add, Prod.mk.injEq]
  exact ⟨trivial, by ring, trivial, by ring⟩

theorem rotB_add_apply (φ χ : ℝ) (X : Vec4) : rotB (φ + χ) X = rotB φ (rotB χ X) := by
  rw [rotB_add]; rfl

/-- **DERIVED (§10).**  The inherited `3+1` form is preserved. -/
theorem Q4_rotB (φ : ℝ) (X : Vec4) : Q4 (rotB φ X) = Q4 X := by
  simp only [Q4, rotB_apply]
  linear_combination (- X.2.1 ^ 2 - X.2.2.2 ^ 2) * Real.sin_sq_add_cos_sq φ

/-- **DERIVED (§10).**  The inherited spatial form is preserved. -/
theorem dot3_rotB (φ : ℝ) (X Y : Vec4) :
    dot3 (rotB φ X).2 (rotB φ Y).2 = dot3 X.2 Y.2 := by
  simp only [rotB_apply, dot3_apply]
  linear_combination (X.2.1 * Y.2.1 + X.2.2.2 * Y.2.2.2) * Real.sin_sq_add_cos_sq φ

theorem rotB_mem_Rest {X : Vec4} (φ : ℝ) (hX : X ∈ Rest) : rotB φ X ∈ Rest := by
  rw [mem_Rest] at hX ⊢
  simpa using hX

theorem rotB_mem_TransB {X : Vec4} (φ : ℝ) (hX : X ∈ TransB) : rotB φ X ∈ TransB := by
  rw [TransB_coords] at hX ⊢
  have h0 : X.1 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.1) hX; simpa using this
  have hy : X.2.2.1 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.2.2.1) hX; simpa using this
  simp [h0, hy]

theorem rotB_mem_LongB {X : Vec4} (φ : ℝ) (hX : X ∈ LongB) : rotB φ X ∈ LongB := by
  rw [LongB_coords] at hX ⊢
  have h0 : X.1 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.1) hX; simpa using this
  have hx : X.2.1 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.2.1) hX; simpa using this
  have hz : X.2.2.2 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.2.2.2) hX; simpa using this
  simp [h0, hx, hz]

/-- **DERIVED (§10).**  The family acts nontrivially on the second transverse plane
whenever `sin φ ≠ 0`. -/
theorem rotB_nontrivial_on_TransB {φ : ℝ} (hφ : Real.sin φ ≠ 0) :
    rotB φ dirA ≠ dirA := by
  intro hcon
  have h := congrArg (fun Y : Vec4 => Y.2.2.2) hcon
  simp [dirA, sp, s₁] at h
  exact hφ h

/-! ### §10 — the orientation/sign branch audit -/

/-- **NEUTRAL DEFINITION (§10).**  The complete list of inherited old-space requirements a
second-axis family must satisfy.  No orientation and no sign convention is part of it. -/
structure IsSecondAxisOldFamily (T : ℝ → (Vec4 →ₗ[ℝ] Vec4)) : Prop where
  /-- The old temporal unit is fixed. -/
  fix_time : ∀ φ, T φ e₀ = e₀
  /-- The second axis is fixed. -/
  fix_axis : ∀ φ, T φ dirB = dirB
  /-- The inherited rest space is preserved. -/
  rest : ∀ φ, ∀ X ∈ Rest, T φ X ∈ Rest
  /-- The inherited spatial form is preserved. -/
  form : ∀ φ X Y, dot3 (T φ X).2 (T φ Y).2 = dot3 X.2 Y.2
  /-- The transverse plane is preserved and moved. -/
  trans_stable : ∀ φ, ∀ X ∈ TransB, T φ X ∈ TransB
  /-- Nontriviality on the transverse plane. -/
  nontrivial : ∃ φ, T φ dirA ≠ dirA
  /-- Identity at the zero parameter. -/
  id_zero : T 0 = LinearMap.id
  /-- Additive composition. -/
  add : ∀ φ χ, T (φ + χ) = (T φ).comp (T χ)

theorem rotB_isSecondAxisOldFamily : IsSecondAxisOldFamily rotB where
  fix_time := rotB_e₀
  fix_axis := rotB_dirB
  rest := fun φ _ hX => rotB_mem_Rest φ hX
  form := dot3_rotB
  trans_stable := fun φ _ hX => rotB_mem_TransB φ hX
  nontrivial := ⟨Real.pi / 2, rotB_nontrivial_on_TransB (by
    rw [Real.sin_pi_div_two]; norm_num)⟩
  id_zero := rotB_zero
  add := rotB_add

/-- **ORIENTATION AUDIT (§10): `second_axis_orientation_branches`.**  The inherited
requirement list of §10 does **not** select a sign: the reversed family satisfies exactly
the same requirements, and the two branches are genuinely different families.  The branch
`rotB` used from here on is therefore a documented convention, not a derived choice. -/
theorem second_axis_orientation_branches :
    IsSecondAxisOldFamily rotB ∧
    IsSecondAxisOldFamily (fun φ => rotB (-φ)) ∧
    rotB (Real.pi / 2) ≠ rotB (-(Real.pi / 2)) := by
  refine ⟨rotB_isSecondAxisOldFamily, ?_, ?_⟩
  · exact
    { fix_time := fun φ => rotB_e₀ (-φ)
      fix_axis := fun φ => rotB_dirB (-φ)
      rest := fun φ _ hX => rotB_mem_Rest (-φ) hX
      form := fun φ => dot3_rotB (-φ)
      trans_stable := fun φ _ hX => rotB_mem_TransB (-φ) hX
      nontrivial := ⟨Real.pi / 2, by
        simpa using rotB_nontrivial_on_TransB (φ := -(Real.pi / 2))
          (by rw [Real.sin_neg, Real.sin_pi_div_two]; norm_num)⟩
      id_zero := by simpa using rotB_zero
      add := fun φ χ => by
        have : -(φ + χ) = -φ + -χ := by ring
        rw [this, rotB_add] }
  · intro hcon
    have h := congrArg (fun T : Vec4 →ₗ[ℝ] Vec4 => (T dirA).2.2.2) hcon
    simp [dirA, sp, s₁] at h
    exact absurd h (by norm_num)

/-! ## §11 — the second-axis algebra extension problem -/

/-- **THE SECOND-AXIS EXTENSION PROBLEM (§11).**  A unital multiplicative real-linear map
of the carrier restricting to the second-axis old transformation.  No value on
`P, Q, R, S` is prescribed. -/
structure IsSecondAxisExtension (φ : ℝ) (Ψ : W →ₗ[ℝ] W) : Prop where
  /-- The unit is preserved. -/
  unital : Ψ w1 = w1
  /-- Multiplicativity for the inherited product. -/
  mul : ∀ x y : W, Ψ (x ⋆ y) = Ψ x ⋆ Ψ y
  /-- On embedded old vectors the map is the second-axis old transformation. -/
  old : ∀ X : Vec4, Ψ (iota3 X) = iota3 (rotB φ X)

namespace ForcedB

variable {φ : ℝ} {Ψ : W →ₗ[ℝ] W} (hΨ : IsSecondAxisExtension φ Ψ)
include hΨ

/-- **FORCED (§11).** -/
theorem forcedB_wA : Ψ wA = Real.cos φ • wA + (-Real.sin φ) • wC := by
  have hold := hΨ.old dirA
  rw [iota3_dirA, rotB_dirA, map_add, map_smul, map_smul, iota3_dirA, iota3_dirC] at hold
  exact hold

/-- **FORCED (§11).** -/
theorem forcedB_wB : Ψ wB = wB := by
  have hold := hΨ.old dirB
  rwa [iota3_dirB, rotB_dirB, iota3_dirB] at hold

/-- **FORCED (§11).** -/
theorem forcedB_wC : Ψ wC = Real.sin φ • wA + Real.cos φ • wC := by
  have hold := hΨ.old dirC
  rw [iota3_dirC, rotB_dirC, map_add, map_smul, map_smul, iota3_dirA, iota3_dirC] at hold
  exact hold

/-- **FORCED (§11).**  `P = A ⋆ B`. -/
theorem forcedB_wP : Ψ wP = Real.cos φ • wP + Real.sin φ • wR := by
  have hP : wP = wA ⋆ wB := (wit8_wA_wB).symm
  rw [hP, hΨ.mul, forcedB_wA hΨ, forcedB_wB hΨ]
  simp only [add_mul_W, smul_mul_W, wit8_wA_wB, wit8_wC_wB]
  module

/-- **FORCED (§11).**  `Q = A ⋆ C`; the Pythagorean identity is the only analytic
input. -/
theorem forcedB_wQ : Ψ wQ = wQ := by
  have hpy := Real.sin_sq_add_cos_sq φ
  have hQ : wQ = wA ⋆ wC := (wit8_wA_wC).symm
  rw [hQ, hΨ.mul, forcedB_wA hΨ, forcedB_wC hΨ]
  simp only [add_mul_W, mul_add_W, smul_mul_W, mul_smul_W, wit8_wA_wA, wit8_wA_wC,
    wit8_wC_wA, wit8_wC_wC]
  match_scalars <;>
    first
      | linear_combination (0 : ℝ) * hpy
      | linear_combination hpy
      | linear_combination -hpy

/-- **FORCED (§11).**  `R = B ⋆ C`. -/
theorem forcedB_wR : Ψ wR = (-Real.sin φ) • wP + Real.cos φ • wR := by
  have hR : wR = wB ⋆ wC := (wit8_wB_wC).symm
  rw [hR, hΨ.mul, forcedB_wB hΨ, forcedB_wC hΨ]
  simp only [mul_add_W, mul_smul_W, wit8_wB_wA, wit8_wB_wC]
  module

/-- **FORCED (§11).**  `S = A ⋆ R`. -/
theorem forcedB_wS : Ψ wS = wS := by
  have hpy := Real.sin_sq_add_cos_sq φ
  have hS : wS = wA ⋆ wR := (wit8_wA_wR).symm
  rw [hS, hΨ.mul, forcedB_wA hΨ, forcedB_wR hΨ]
  simp only [add_mul_W, mul_add_W, smul_mul_W, mul_smul_W, wit8_wA_wP, wit8_wA_wR,
    wit8_wC_wP, wit8_wC_wR]
  match_scalars <;>
    first
      | linear_combination (0 : ℝ) * hpy
      | linear_combination hpy
      | linear_combination -hpy

end ForcedB

open ForcedB

/-- **PRINCIPAL THEOREM (§11): `second_axis_automorphism_unique_or_classified`.**  Any two
extensions of the second-axis old transformation coincide: the extension is unique if it
exists. -/
theorem secondAxisExtension_unique {φ : ℝ} {Ψ Ψ' : W →ₗ[ℝ] W}
    (h : IsSecondAxisExtension φ Ψ) (h' : IsSecondAxisExtension φ Ψ') : Ψ = Ψ' :=
  linMap_ext
    (by rw [h.unital, h'.unital])
    (by rw [forcedB_wA h, forcedB_wA h'])
    (by rw [forcedB_wB h, forcedB_wB h'])
    (by rw [forcedB_wC h, forcedB_wC h'])
    (by rw [forcedB_wP h, forcedB_wP h'])
    (by rw [forcedB_wQ h, forcedB_wQ h'])
    (by rw [forcedB_wR h, forcedB_wR h'])
    (by rw [forcedB_wS h, forcedB_wS h'])

/-! ### The explicit witness, written from the forced values -/

/-- The coordinate description of the candidate second-axis extension.  Its coordinates
are exactly the values forced above. -/
noncomputable def PhiBFun (φ : ℝ) (x : W) : W :=
  ![x 0,
    Real.cos φ * x 1 + Real.sin φ * x 3,
    x 2,
    -(Real.sin φ) * x 1 + Real.cos φ * x 3,
    Real.cos φ * x 4 - Real.sin φ * x 6,
    x 5,
    Real.sin φ * x 4 + Real.cos φ * x 6,
    x 7]

/-- **THE SECOND-AXIS CANDIDATE EXTENSION**, as a real-linear map. -/
noncomputable def PhiB (φ : ℝ) : W →ₗ[ℝ] W where
  toFun := PhiBFun φ
  map_add' := by intro x y; funext i; fin_cases i <;> simp [PhiBFun] <;> ring
  map_smul' := by intro c x; funext i; fin_cases i <;> simp [PhiBFun] <;> ring

theorem PhiB_apply (φ : ℝ) (x : W) : PhiB φ x = PhiBFun φ x := rfl

@[simp] theorem PhiB_coord_0 (φ : ℝ) (x : W) : PhiB φ x 0 = x 0 := by simp [PhiB, PhiBFun]
@[simp] theorem PhiB_coord_1 (φ : ℝ) (x : W) :
    PhiB φ x 1 = Real.cos φ * x 1 + Real.sin φ * x 3 := by simp [PhiB, PhiBFun]
@[simp] theorem PhiB_coord_2 (φ : ℝ) (x : W) : PhiB φ x 2 = x 2 := by simp [PhiB, PhiBFun]
@[simp] theorem PhiB_coord_3 (φ : ℝ) (x : W) :
    PhiB φ x 3 = -(Real.sin φ) * x 1 + Real.cos φ * x 3 := by simp [PhiB, PhiBFun]
@[simp] theorem PhiB_coord_4 (φ : ℝ) (x : W) :
    PhiB φ x 4 = Real.cos φ * x 4 - Real.sin φ * x 6 := by simp [PhiB, PhiBFun]
@[simp] theorem PhiB_coord_5 (φ : ℝ) (x : W) : PhiB φ x 5 = x 5 := by simp [PhiB, PhiBFun]
@[simp] theorem PhiB_coord_6 (φ : ℝ) (x : W) :
    PhiB φ x 6 = Real.sin φ * x 4 + Real.cos φ * x 6 := by simp [PhiB, PhiBFun]
@[simp] theorem PhiB_coord_7 (φ : ℝ) (x : W) : PhiB φ x 7 = x 7 := by simp [PhiB, PhiBFun]

/-- **DERIVED (§11).**  The candidate is multiplicative.  The Pythagorean identity is the
only analytic input. -/
theorem PhiB_mul (φ : ℝ) (x y : W) : PhiB φ (x ⋆ y) = PhiB φ x ⋆ PhiB φ y := by
  have hc2 : Real.cos φ ^ 2 = 1 - Real.sin φ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq φ]
  funext i
  fin_cases i <;>
    simp [PhiB, PhiBFun, wit8MulFun] <;> ring_nf <;> (try simp only [hc2]) <;> (try ring)

@[simp] theorem PhiB_w1 (φ : ℝ) : PhiB φ w1 = w1 := by
  funext i; fin_cases i <;> simp [w1]

theorem PhiB_old (φ : ℝ) (X : Vec4) : PhiB φ (iota3 X) = iota3 (rotB φ X) := by
  funext i; fin_cases i <;> simp

/-- **PRINCIPAL THEOREM (§11): `second_axis_automorphism_exists`.**  The independently
constructed second-axis old transformation extends to the whole carrier, and by
`secondAxisExtension_unique` the extension is unique. -/
theorem PhiB_isSecondAxisExtension (φ : ℝ) : IsSecondAxisExtension φ (PhiB φ) where
  unital := PhiB_w1 φ
  mul := PhiB_mul φ
  old := PhiB_old φ

/-- **PRINCIPAL THEOREM (§11).**  Existence and uniqueness, packaged. -/
theorem second_axis_extension_exists_unique (φ : ℝ) :
    ∃! Ψ : W →ₗ[ℝ] W, IsSecondAxisExtension φ Ψ :=
  ⟨PhiB φ, PhiB_isSecondAxisExtension φ,
    fun _ h => secondAxisExtension_unique h (PhiB_isSecondAxisExtension φ)⟩

/-! ### The one-parameter group law and the complete basis table -/

/-- **PRINCIPAL THEOREM (§11).**  Identity at zero. -/
theorem PhiB_zero : PhiB 0 = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  funext i; fin_cases i <;> simp

/-- **PRINCIPAL THEOREM (§11).**  Additive composition.  Derived from the *uniqueness*
theorem: the composite is again an extension, of the composite old transformation. -/
theorem PhiB_add (φ χ : ℝ) : PhiB (φ + χ) = (PhiB φ).comp (PhiB χ) := by
  refine secondAxisExtension_unique (PhiB_isSecondAxisExtension (φ + χ)) ?_
  refine ⟨?_, ?_, ?_⟩
  · simp [LinearMap.comp_apply]
  · intro x y
    simp only [LinearMap.comp_apply, PhiB_mul]
  · intro X
    simp only [LinearMap.comp_apply, PhiB_old, rotB_add_apply]

theorem PhiB_add_apply (φ χ : ℝ) (x : W) : PhiB (φ + χ) x = PhiB φ (PhiB χ x) := by
  rw [PhiB_add]; rfl

/-- **DERIVED (§11).**  The complete action on the eight derived basis elements, obtained
from the forced values (never copied from the A-axis table). -/
@[simp] theorem PhiB_wA (φ : ℝ) : PhiB φ wA = Real.cos φ • wA + (-Real.sin φ) • wC := by
  funext i; fin_cases i <;> simp [wA, wC]

@[simp] theorem PhiB_wB (φ : ℝ) : PhiB φ wB = wB := by
  funext i; fin_cases i <;> simp [wB]

@[simp] theorem PhiB_wC (φ : ℝ) : PhiB φ wC = Real.sin φ • wA + Real.cos φ • wC := by
  funext i; fin_cases i <;> simp [wA, wC]

@[simp] theorem PhiB_wP (φ : ℝ) : PhiB φ wP = Real.cos φ • wP + Real.sin φ • wR := by
  funext i; fin_cases i <;> simp [wP, wR]

@[simp] theorem PhiB_wQ (φ : ℝ) : PhiB φ wQ = wQ := by
  funext i; fin_cases i <;> simp [wQ]

@[simp] theorem PhiB_wR (φ : ℝ) : PhiB φ wR = (-Real.sin φ) • wP + Real.cos φ • wR := by
  funext i; fin_cases i <;> simp [wP, wR]

@[simp] theorem PhiB_wS (φ : ℝ) : PhiB φ wS = wS := by
  funext i; fin_cases i <;> simp [wS]

/-- **PRINCIPAL THEOREM (§11): the exact second-axis basis table.**  Compare with the
inherited A-axis table only *after* this derivation: the fixed noncentral direction is `Q`
here, not `R`, and the moved pairs are `(A,C)` and `(P,R)`. -/
theorem second_axis_basis_table (φ : ℝ) :
    PhiB φ w1 = w1 ∧
    PhiB φ wA = Real.cos φ • wA + (-Real.sin φ) • wC ∧
    PhiB φ wB = wB ∧
    PhiB φ wC = Real.sin φ • wA + Real.cos φ • wC ∧
    PhiB φ wP = Real.cos φ • wP + Real.sin φ • wR ∧
    PhiB φ wQ = wQ ∧
    PhiB φ wR = (-Real.sin φ) • wP + Real.cos φ • wR ∧
    PhiB φ wS = wS :=
  ⟨PhiB_w1 φ, PhiB_wA φ, PhiB_wB φ, PhiB_wC φ, PhiB_wP φ, PhiB_wQ φ, PhiB_wR φ, PhiB_wS φ⟩

/-- **DERIVED (§11).**  The second-axis family returns to the identity after a full
turn. -/
theorem PhiB_two_pi : PhiB (2 * Real.pi) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  funext i
  fin_cases i <;> simp [Real.cos_two_pi, Real.sin_two_pi]

end NullSectorTask14
