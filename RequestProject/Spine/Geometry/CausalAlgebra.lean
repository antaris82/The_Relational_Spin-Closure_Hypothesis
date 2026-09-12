import Mathlib
import RequestProject.Spine.E1.Coords
import RequestProject.Spine.E1.ShellTransitivity

/-!
# Task 4, WP2/WP9 : the causal algebra of the intrinsic carrier

This module proves, on the intrinsic carrier `𝒮 = LorentzCarrier = ℝ × (Fin 3 → ℝ)` alone,
the Lorentzian linear algebra that the frame layer of Task 4 needs:

* the *signature audit* of the intrinsic quadratic form `N_𝒮` — it is `(1,3)`
  (`NS_sOne`, `NS_spatial_unit`);
* the two causal sign lemmas
  (`fst_pos_of_BS_pos_of_timelike`, `fst_nonneg_of_BS_nonneg_of_causal`);
* the **reduction criterion** `isGLor_of_isometry_of_future_of_det_pos`: a linear
  automorphism of the carrier which

  1. preserves the polarized form `B_𝒮` (metric condition),
  2. maps the intrinsic unit to a future-pointing vector (time-orientation condition),
  3. has positive determinant (orientation condition),

  lies in the native intrinsic Lorentz target `SpinCore.GLor`.  This is the exact algebraic
  content of "orientation *and* time orientation reduce the orthonormal frame group to the
  proper orthochronous component", and it is *derived*, not assumed.

* the negative controls showing that neither hypothesis may be dropped:
  `spatialReflI_notMem_GLor` (a `B_𝒮`- and cone-preserving reflection of determinant `-1`,
  excluded only by the orientation hypothesis) and `timeReflI_not_isGLorWide` (a
  `B_𝒮`-preserving map of determinant `-1` excluded only by the time-orientation
  hypothesis).  Orientation and time orientation are therefore **independent**.

Nothing in this module mentions a manifold, a bundle, a cover or a Spin group.
-/

noncomputable section

namespace SpinCore

/-! ## Elementary identities -/

/-- Pairing with the intrinsic unit reads off the time component. -/
@[simp] theorem BS_sOne (x : LorentzCarrier) : BS x sOne = x.1 := by
  rw [BS_eq]
  simp [sOne, sip_zero_right]

/-- **WP9 (signature audit).**  The intrinsic unit is timelike of norm `+1`. -/
@[simp] theorem NS_sOne : NS (sOne : LorentzCarrier) = 1 := by
  rw [NS_def]
  simp [sOne, sip_zero_left]

/-- **WP9 (signature audit).**  A purely spatial vector has norm `-|v|²`. -/
theorem NS_spatial (v : Fin 3 → ℝ) : NS ((0, v) : LorentzCarrier) = -sip v v := by
  rw [NS_def]; ring

/-- **WP9 (signature audit).**  The three spatial coordinate directions have norm `-1`:
together with `NS_sOne` this pins the signature to `(1,3)` — one plus, three minuses. -/
theorem NS_spatial_unit (k : Fin 3) :
    NS ((0, Pi.single k 1) : LorentzCarrier) = -1 := by
  rw [NS_spatial]
  fin_cases k <;> simp [sip]

/-! ## The two causal sign lemmas -/

/-- **DERIVED_NATIVE (WP2).**  If `t` is future timelike and `u` is timelike with
`B_𝒮 t u > 0`, then `u` is future pointing. -/
theorem fst_pos_of_BS_pos_of_timelike {t u : LorentzCarrier} (ht : 0 < NS t) (ht1 : 0 < t.1)
    (hu : 0 < NS u) (h : 0 < BS t u) : 0 < u.1 := by
  by_contra hcon
  push_neg at hcon
  rw [NS_def] at ht hu
  rw [BS_eq] at h
  have hst := sip_self_nonneg t.2
  have hsu := sip_self_nonneg u.2
  have hc := sip_cauchy t.2 u.2
  have hb2 : 0 < u.1 ^ 2 := lt_of_le_of_lt hsu (by linarith)
  have hpq : sip t.2 t.2 * sip u.2 u.2 < t.1 ^ 2 * u.1 ^ 2 := by nlinarith
  have hr2 : (sip t.2 u.2) ^ 2 < (t.1 * u.1) ^ 2 := by nlinarith
  have hab : t.1 * u.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht1) hcon
  nlinarith

/-- **DERIVED_NATIVE (WP2).**  If `u` is future timelike and `y` is causal with
`B_𝒮 y u ≥ 0`, then `y` is future pointing (weakly). -/
theorem fst_nonneg_of_BS_nonneg_of_causal {u y : LorentzCarrier} (hu : 0 < NS u)
    (hu1 : 0 < u.1) (hy : 0 ≤ NS y) (h : 0 ≤ BS y u) : 0 ≤ y.1 := by
  by_contra hcon
  push_neg at hcon
  rw [NS_def] at hu hy
  rw [BS_eq] at h
  have hsy := sip_self_nonneg y.2
  have hsu := sip_self_nonneg u.2
  have hc := sip_cauchy y.2 u.2
  have hy2 : 0 < y.1 ^ 2 := by nlinarith
  have hpq : sip y.2 y.2 * sip u.2 u.2 < y.1 ^ 2 * u.1 ^ 2 := by nlinarith
  have hr2 : (sip y.2 u.2) ^ 2 < (y.1 * u.1) ^ 2 := by nlinarith
  have hab : y.1 * u.1 < 0 := mul_neg_of_neg_of_pos hcon hu1
  nlinarith

/-! ## The reduction criterion -/

variable {F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier}

theorem apply_inv_apply_self (F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) (z : LorentzCarrier) :
    F (F⁻¹ z) = z := by
  show (F * F⁻¹) z = z
  rw [mul_inv_cancel]; rfl

theorem inv_apply_apply_self (F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) (z : LorentzCarrier) :
    F⁻¹ (F z) = z := by
  show (F⁻¹ * F) z = z
  rw [inv_mul_cancel]; rfl

/-- A `B_𝒮`-isometry preserves `N_𝒮`. -/
theorem NS_of_BS_isometry (hiso : ∀ x y, BS (F x) (F y) = BS x y) (x : LorentzCarrier) :
    NS (F x) = NS x := by
  rw [← BS_self, ← BS_self, hiso]

/-- The inverse of a `B_𝒮`-isometry is a `B_𝒮`-isometry. -/
theorem BS_isometry_inv (hiso : ∀ x y, BS (F x) (F y) = BS x y) (x y : LorentzCarrier) :
    BS (F⁻¹ x) (F⁻¹ y) = BS x y := by
  have := hiso (F⁻¹ x) (F⁻¹ y)
  rw [apply_inv_apply_self, apply_inv_apply_self] at this
  exact this.symm

/-- **DERIVED_NATIVE (WP2), the cone half of the reduction criterion.**  A `B_𝒮`-isometry
which maps the intrinsic unit to a future-pointing vector preserves the intrinsic causal
cone, i.e. lies in the *wide* intrinsic group `GLorWide`. -/
theorem isGLorWide_of_isometry_of_future (hiso : ∀ x y, BS (F x) (F y) = BS x y)
    (hfut : 0 < (F sOne).1) : IsGLorWide F := by
  have key : ∀ G : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier,
      (∀ x y, BS (G x) (G y) = BS x y) → 0 < (G sOne).1 →
      ∀ x : LorentzCarrier, x ∈ ConeS → G x ∈ ConeS := by
    intro G hG hG1 x hx
    rw [mem_coneS_iff] at hx ⊢
    have hNS : NS (G x) = NS x := NS_of_BS_isometry hG x
    refine ⟨?_, by rw [hNS]; exact hx.2⟩
    have hu : 0 < NS (G sOne) := by rw [NS_of_BS_isometry hG, NS_sOne]; norm_num
    have hpair : 0 ≤ BS (G x) (G sOne) := by rw [hG, BS_sOne]; exact hx.1
    exact fst_nonneg_of_BS_nonneg_of_causal hu hG1 (by rw [hNS]; exact hx.2) hpair
  have hinv1 : 0 < (F⁻¹ sOne).1 := by
    have h := hiso (F⁻¹ sOne) sOne
    rw [apply_inv_apply_self] at h
    have heq : (F⁻¹ sOne).1 = (F sOne).1 := by
      rw [← BS_sOne (F⁻¹ sOne), ← h, BS_symm, BS_sOne]
    rw [heq]; exact hfut
  refine ⟨NS_of_BS_isometry hiso, fun x => ⟨key F hiso hfut x, fun hFx => ?_⟩⟩
  have hb := key F⁻¹ (BS_isometry_inv hiso) hinv1 (F x) hFx
  rwa [inv_apply_apply_self] at hb

/-- **DERIVED_NATIVE (WP2).**  A `B_𝒮`-isometry has determinant `±1` (inherited from the
intrinsic determinant dichotomy `SpinCore.det_sq_of_BS_preserving`); if its determinant is
positive it is exactly `1`. -/
theorem det_eq_one_of_isometry_of_det_pos (hiso : ∀ x y, BS (F x) (F y) = BS x y)
    (hdet : 0 < LinearMap.det (F : LorentzCarrier →ₗ[ℝ] LorentzCarrier)) :
    LinearMap.det (F : LorentzCarrier →ₗ[ℝ] LorentzCarrier) = 1 := by
  have h2 := det_sq_of_BS_preserving (F := (F : LorentzCarrier →ₗ[ℝ] LorentzCarrier)) hiso
  nlinarith [h2, hdet]

/-- **DERIVED_NATIVE (WP2), principal — the frame-group reduction criterion.**

A real-linear automorphism of the intrinsic carrier lies in the native proper orthochronous
target `GLor` as soon as it

* preserves the polarized intrinsic form `B_𝒮` (*metric* condition),
* sends the intrinsic unit to a future-pointing vector (*time-orientation* condition),
* has positive determinant (*orientation* condition).

Each of the three hypotheses is used, and none is redundant: see
`spatialReflI_notMem_GLor` and `timeReflI_not_isGLorWide`. -/
theorem isGLor_of_isometry_of_future_of_det_pos (hiso : ∀ x y, BS (F x) (F y) = BS x y)
    (hfut : 0 < (F sOne).1)
    (hdet : 0 < LinearMap.det (F : LorentzCarrier →ₗ[ℝ] LorentzCarrier)) : F ∈ GLor :=
  ⟨isGLorWide_of_isometry_of_future hiso hfut, det_eq_one_of_isometry_of_det_pos hiso hdet⟩

/-! ## Negative controls: orientation and time orientation are independent -/

/-- The intrinsic spatial reflection is a `B_𝒮`-isometry. -/
theorem spatialReflI_BS (x y : LorentzCarrier) :
    BS (spatialReflI x) (spatialReflI y) = BS x y := by
  rw [BS_eq, BS_eq, sip_spatialReflI]
  rfl

/-- **NEGATIVE CONTROL (WP2/WP9).**  The spatial reflection preserves the intrinsic norm
*and* the intrinsic causal cone — it is orthochronous — but it is **not** in `GLor`: its
determinant is `-1`.  Hence the *orientation* hypothesis is not implied by the metric and
time-orientation hypotheses. -/
theorem spatialReflI_notMem_GLor : spatialReflI ∉ GLor := by
  intro h
  have := h.2
  rw [spatialReflI_det] at this
  norm_num at this

theorem spatialReflI_mem_GLorWide : spatialReflI ∈ GLorWide := spatialReflI_wide

/-- The intrinsic time reflection `(t, v) ↦ (-t, v)`. -/
def timeReflI : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier where
  toFun x := (-x.1, x.2)
  map_add' x y := by
    apply Prod.ext
    · show -(x.1 + y.1) = -x.1 + -y.1; ring
    · rfl
  map_smul' r x := by
    apply Prod.ext
    · show -(r * x.1) = r * -x.1; ring
    · rfl
  invFun x := (-x.1, x.2)
  left_inv x := by
    apply Prod.ext
    · show - -x.1 = x.1; ring
    · rfl
  right_inv x := by
    apply Prod.ext
    · show - -x.1 = x.1; ring
    · rfl

@[simp] theorem timeReflI_apply (x : LorentzCarrier) : timeReflI x = (-x.1, x.2) := rfl

theorem timeReflI_BS (x y : LorentzCarrier) : BS (timeReflI x) (timeReflI y) = BS x y := by
  rw [BS_eq, BS_eq]
  show -x.1 * -y.1 - sip x.2 y.2 = x.1 * y.1 - sip x.2 y.2
  ring

/-- **NEGATIVE CONTROL (WP2/WP9).**  The time reflection preserves the intrinsic norm and
the polarized form, but reverses the causal cone: it is not even in the *wide* intrinsic
group.  Hence the *time-orientation* hypothesis is genuinely separate from the metric
hypothesis, and is not implied by orientation either (the composite of the time reflection
with a spatial reflection has determinant `+1` and is still not orthochronous). -/
theorem timeReflI_not_isGLorWide : ¬ IsGLorWide timeReflI := by
  intro h
  have h1 : (sOne : LorentzCarrier) ∈ ConeS := one_mem_coneS
  have h2 := (h.2 sOne).1 h1
  rw [mem_coneS_iff] at h2
  have : ((timeReflI sOne).1 : ℝ) = -1 := by
    show -(sOne : LorentzCarrier).1 = -1
    simp [sOne]
  rw [this] at h2
  norm_num at h2

/-- **NEGATIVE CONTROL (WP2).**  Orientation does not imply time orientation: the composite
`timeReflI ∘ spatialReflI` is a `B_𝒮`-isometry of determinant `+1` which is nevertheless not
orthochronous, hence not in `GLor`. -/
theorem timeRefl_comp_spatialRefl_notMem_GLor :
    (timeReflI * spatialReflI) ∉ GLor := by
  intro h
  have hcone := (h.1.2 sOne).1 one_mem_coneS
  rw [mem_coneS_iff] at hcone
  have hval : ((timeReflI * spatialReflI : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) sOne).1
      = -1 := by
    show (timeReflI (spatialReflI sOne)).1 = -1
    rw [spatialReflI_one]
    show -(sOne : LorentzCarrier).1 = -1
    simp [sOne]
  rw [hval] at hcone
  norm_num at hcone

end SpinCore
