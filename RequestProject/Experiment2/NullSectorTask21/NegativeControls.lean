import RequestProject.Experiment2.NullSectorTask21.TorsorPlacement

/-!
# Task 21, Package N: negative controls against overidentification

Each control below is a *formal* statement which would have to be false if the corresponding
overclaim were made.  The controls which cannot be stated as theorems — because they are
statements about objects that were deliberately **not** constructed — are recorded as
explicit non-constructions in `TASK21_AUDIT.md` and are listed at the end of this docstring.

Formalized here:

1. (item 125) Unit quaternions alone do not give the visible group: the core projection is
   not injective, so the core carrier and the visible group are not the same object; the
   target identification had to be proved separately (Packages C–D).
2. (item 126) A two-element kernel does not determine a covering map: there is a second
   group homomorphism from the core carrier onto the visible group with exactly the same
   kernel, which is not equal to the intrinsic projection.
3. (item 127) The core kernel is strictly smaller than the kernel on the full carrier.
4. (item 128) The continuous centre is not quotiented away anywhere: it is a continuous
   injective one-parameter family inside the kernel of the full projection.
5. (item 129) `S² = -1` alone does not determine the identification of the centre with the
   complex numbers: a second, different multiplicative equivalence exists, so the
   coefficient map had to be constructed explicitly.
6. (item 131) The core sign and the direction reversal remain distinct two-valued
   structures.

Not formalized because deliberately not constructed (items 130, 132, 133, 134): no
topological-group equivalence is claimed for the central-product quotient; no spin structure
on any manifold or bundle; no `Spinᶜ` structure; no physical spin degree of freedom.  No
object of any of these kinds occurs anywhere in this project.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask21

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20

/-- **CONTROL 1 (item 125).**  The core projection is not injective. -/
theorem projCore_not_injective : ¬ Function.Injective projCore := by
  intro hinj
  have h : projCore lNegOne = projCore 1 := by
    have := projCore_sign 1
    simpa using this
  exact core_sign_free 1 (by simpa using hinj h)

/-! ### Two non-commuting visible transformations

The second control needs a *non-central* visible transformation.  Two quarter-turn
reference implementers about two distinct inherited coordinate directions are exhibited and
their visible transformations are proved not to commute, by evaluating both composites on a
single inherited spatial vector. -/

theorem axis_e1 : IsUnitAxis ((1, 0, 0) : Vec3) := by simp [IsUnitAxis, h3, dot3]
theorem axis_e2 : IsUnitAxis ((0, 1, 0) : Vec3) := by simp [IsUnitAxis, h3, dot3]

/-- A quarter-turn reference implementer about the first inherited direction. -/
noncomputable def coreQuarterOne : LiftG :=
  ⟨UnG axis_e1 (Real.pi / 2), UnG_mem_LiftG axis_e1 _⟩

/-- A quarter-turn reference implementer about the second inherited direction. -/
noncomputable def coreQuarterTwo : LiftG :=
  ⟨UnG axis_e2 (Real.pi / 2), UnG_mem_LiftG axis_e2 _⟩

/-- **DERIVED.**  The visible group is not commutative. -/
theorem visible_noncommuting :
    projCore coreQuarterOne * projCore coreQuarterTwo
      ≠ projCore coreQuarterTwo * projCore coreQuarterOne := by
  intro h
  have h' := congrArg (fun U : GvisG => ((U : (Module.End ℝ W)ˣ) : Module.End ℝ W)
      (spat ((1 : ℝ), (0 : ℝ), (0 : ℝ)))) h
  simp only [Subgroup.coe_mul, Units.val_mul, projCore_coe,
    show ∀ (F G : W →ₗ[ℝ] W) (x : W), (F * G) x = F (G x) from fun _ _ _ => rfl] at h'
  rw [show ((coreQuarterOne : WG)).val = Un ((1, 0, 0) : Vec3) (Real.pi / 2) from rfl,
    show ((coreQuarterTwo : WG)).val = Un ((0, 1, 0) : Vec3) (Real.pi / 2) from rfl] at h'
  rw [proj_Un axis_e1, proj_Un axis_e2] at h'
  rw [PhiGen_spat axis_e2, PhiGen_spat axis_e1, PhiGen_spat axis_e1, PhiGen_spat axis_e2] at h'
  have h2 := spat_injective h'
  simp [rotv, spCross, h3, dot3, Prod.ext_iff] at h2

/-- **CONTROL 2 (item 126).**  A second homomorphism onto the visible group with the same
kernel, different from the intrinsic projection: a two-element kernel does not identify a
covering map. -/
theorem kernel_does_not_determine_map :
    ∃ φ : LiftG →* GvisG, φ.ker = projCore.ker ∧ φ ≠ projCore := by
  set A : GvisG := projCore coreQuarterOne with hA_def
  refine ⟨(MulAut.conj A).toMonoidHom.comp projCore, ?_, ?_⟩
  · ext g
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro h
      refine mul_left_cancel (a := A) ?_
      rw [mul_one]
      calc A * projCore g = (A * projCore g * A⁻¹) * A := by group
        _ = 1 * A := by rw [h]
        _ = A := by group
    · intro h; rw [h]; group
  · intro hcontra
    have h1 := DFunLike.congr_fun hcontra coreQuarterTwo
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply] at h1
    refine visible_noncommuting ?_
    calc A * projCore coreQuarterTwo
        = (A * projCore coreQuarterTwo * A⁻¹) * A := by group
      _ = projCore coreQuarterTwo * A := by rw [h1]

/-- **CONTROL 5 (item 129).**  The identification of the centre with the complex numbers is
not unique, so it cannot be inferred from `S² = -1`: the coefficient map itself carries
information. -/
theorem central_identification_not_unique :
    ∃ e : CUnitG ≃* ℂˣ, e ≠ cUnitComplexEquiv := by
  have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
  refine ⟨cUnitComplexEquiv.trans (Units.mapEquiv (starRingAut (R := ℂ)).toMulEquiv), ?_⟩
  intro h
  have h1 := DFunLike.congr_fun h (cUnitComplexEquiv.symm (Units.mk0 Complex.I hI))
  simp only [MulEquiv.coe_trans, Function.comp_apply] at h1
  rw [MulEquiv.apply_symm_apply] at h1
  have h2 : ((Units.mapEquiv (starRingAut (R := ℂ)).toMulEquiv (Units.mk0 Complex.I hI) : ℂˣ) : ℂ)
      = ((Units.mk0 Complex.I hI : ℂˣ) : ℂ) := congrArg Units.val h1
  simp [Units.mapEquiv] at h2
  exact Complex.I_ne_zero (by linear_combination -h2 / 2)

/-- **PACKAGE N, principal.**  The formalizable anti-overidentification controls,
collected. -/
theorem task21_negative_controls :
    (¬ Function.Injective projCore) ∧
      (∃ φ : LiftG →* GvisG, φ.ker = projCore.ker ∧ φ ≠ projCore) ∧
      (({w1, -w1} : Set W) ⊂ CentreOf LiftZ) ∧
      (Continuous (fun t : ℝ => zexp 1 0 t) ∧ Function.Injective (fun t : ℝ => zexp 1 0 t) ∧
        ∀ t : ℝ, zexp 1 0 t ∈ CUnit ∧ proj (zexp 1 0 t) = LinearMap.id) ∧
      (∃ e : CUnitG ≃* ℂˣ, e ≠ cUnitComplexEquiv) ∧
      (∀ g : LiftG, lNegOne * g ≠ g) ∧
      (∀ (n : Vec3) (θ : ℝ), Un (-n) (-θ) = Un n θ) := by
  refine ⟨projCore_not_injective, kernel_does_not_determine_map, ?_, kernel_full_continuum,
    central_identification_not_unique, core_sign_free, Un_neg_axis_neg_param⟩
  rw [centre_LiftZ]
  exact kernel_core_ssubset_kernel_full

end NullSectorTask21
