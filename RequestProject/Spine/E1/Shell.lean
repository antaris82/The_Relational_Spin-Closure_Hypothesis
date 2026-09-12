import Mathlib
import RequestProject.Spine.E1.ShellTransitivity

/-!
# Task 10, Branch 3 (part 2) : homogeneity of the unit future shell, its tangent form,
and the recovery of the Task-1/Task-3 rapidity

The intrinsic boosts of `Task10Hyperbolic` preserve the norm and the cone but their real
orientation is not fixed by that data alone (Task 9 already proved that orientation is an
independent *discrete* datum).  Section E1 supplies the single discrete correction needed:
an explicit spatial reflection of the carrier, whose determinant `-1` is imported from the
frozen Task-8 computation `Task8.reflY_det` (`DISCRETE_COMPONENT_SELECTION`, not a new
continuous input).

With it:

* `shell_transitive` : `G_L` acts transitively on `𝓗`;
* `shell_eq_orbit` : `𝓗` is exactly the `G_L`-orbit of `1_𝒮`;
* `stabOne_mulEquiv_rot` : the stabilizer of `1_𝒮` is the intrinsic rotation group of
  `(V, ⟨·,·⟩)`;
* `tangent_neg_definite` : `-B_𝒮` is positive definite on the `B`-orthogonal complement of a
  shell point (the algebraic tangent-space statement; no manifold structure is used);
* `rapidity_*` : the Task-1/Task-3 reciprocal boost parameter reappears inside the shell.
-/

noncomputable section

namespace SpinCore

open SpinCore

/-! ## D3 : the stabilizer of the unit -/

/-- The stabilizer of the canonical unit inside the intrinsic group. -/
def StabOne : Subgroup GLor where
  carrier := {F | (F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) sOne = sOne}
  one_mem' := rfl
  mul_mem' := by
    intro F G hF hG
    show (F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) ((G : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) sOne) = sOne
    rw [show (G : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) sOne = sOne from hG, show (F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) sOne = sOne
      from hF]
  inv_mem' := by
    intro F hF
    show ((F⁻¹ : GLor) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) sOne = sOne
    have h : (F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) sOne = sOne := hF
    have : ((F⁻¹ : GLor) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) ((F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) sOne) = sOne := by
      show ((F⁻¹ * F : GLor) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) sOne = sOne
      rw [inv_mul_cancel]; rfl
    rwa [h] at this

/-- The intrinsic rotation group of the primitive Euclidean space `(V, ⟨·,·⟩)`: linear
automorphisms preserving `sip`, with real orientation `+1`.  `SO(3)` is *not* mentioned. -/
def RotV : Subgroup ((Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) where
  carrier := {R | (∀ u v, sip (R u) (R v) = sip u v) ∧
    LinearMap.det (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) = 1}
  one_mem' := ⟨fun _ _ => rfl, by simp⟩
  mul_mem' := by
    rintro R S ⟨hR1, hR2⟩ ⟨hS1, hS2⟩
    refine ⟨fun u v => ?_, ?_⟩
    · show sip (R (S u)) (R (S v)) = sip u v
      rw [hR1, hS1]
    · have hcomp : ((R * S : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) :
          (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
          = (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) ∘ₗ (S : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) := rfl
      rw [hcomp, LinearMap.det_comp, hR2, hS2, one_mul]
  inv_mem' := by
    rintro R ⟨h1, h2⟩
    have hRR : ∀ u, R (R⁻¹ u) = u := by
      intro u
      show (R * R⁻¹) u = u
      rw [mul_inv_cancel]; rfl
    refine ⟨fun u v => ?_, ?_⟩
    · have := h1 (R⁻¹ u) (R⁻¹ v)
      rw [hRR, hRR] at this
      exact this.symm
    · have hcomp : ((R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
          ∘ₗ ((R⁻¹ : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)))
          = LinearMap.id := by
        apply LinearMap.ext; intro u; exact hRR u
      have := congrArg LinearMap.det hcomp
      rw [LinearMap.det_comp, h2, one_mul] at this
      simpa using this

/-- The carrier automorphism attached to a rotation of `V`. -/
def rotToSpin (R : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier :=
  LinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ) R

@[simp] theorem rotToSpin_apply (R : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) (x : LorentzCarrier) :
    rotToSpin R x = (x.1, R x.2) := rfl

theorem rotToSpin_det (R : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) :
    LinearMap.det ((rotToSpin R : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : LorentzCarrier →ₗ[ℝ] LorentzCarrier)
      = LinearMap.det (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) := by
  have h : ((rotToSpin R : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : LorentzCarrier →ₗ[ℝ] LorentzCarrier)
      = LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
        (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) := by
    apply LinearMap.ext; intro x; rfl
  rw [h, LinearMap.det_prodMap, LinearMap.det_id, one_mul]

theorem rotToSpin_mem {R : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)} (hR : R ∈ RotV) :
    rotToSpin R ∈ GLor := by
  obtain ⟨h1, h2⟩ := hR
  have hNS : ∀ x : LorentzCarrier, NS (rotToSpin R x) = NS x := by
    intro x
    show x.1 ^ 2 - sip (R x.2) (R x.2) = x.1 ^ 2 - sip x.2 x.2
    rw [h1]
  refine ⟨⟨hNS, fun x => ?_⟩, ?_⟩
  · rw [mem_coneS_iff, mem_coneS_iff, hNS]
    exact Iff.rfl
  · rw [rotToSpin_det, h2]

theorem rotToSpin_one (R : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) : rotToSpin R sOne = sOne := by
  apply Prod.ext
  · rfl
  · show R 0 = 0
    simp

/-- The `V`-restriction of a carrier automorphism fixing the unit. -/
def spinToRot (F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun u := (F (0, u)).2
  map_add' u v := by
    have h : ((0 : ℝ), u + v) = ((0 : ℝ), u) + ((0 : ℝ), v) := by
      apply Prod.ext <;> simp
    rw [h, map_add]
    rfl
  map_smul' r u := by
    have h : ((0 : ℝ), r • u) = r • ((0 : ℝ), u) := by
      apply Prod.ext <;> simp
    rw [h, map_smul]
    rfl

theorem BS_one_left (y : LorentzCarrier) : BS sOne y = y.1 := by
  rw [BS_eq]
  show 1 * y.1 - sip 0 y.2 = y.1
  rw [sip_zero_left]; ring

/-- A unit-fixing member of `G_L` maps the `B`-orthogonal complement of the unit (i.e. `V`)
to itself. -/
theorem stab_fst_zero {F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier} (hF : F ∈ GLor) (hone : F sOne = sOne)
    (u : Fin 3 → ℝ) : (F ((0 : ℝ), u)).1 = 0 := by
  have h := GLor_BS hF sOne ((0 : ℝ), u)
  rw [hone, BS_one_left, BS_one_left] at h
  exact h

/-- **D3 (decomposition).**  A unit-fixing member of `G_L` is `id ⊕ R`. -/
theorem stab_eq_rot {F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier} (hF : F ∈ GLor) (hone : F sOne = sOne) (x : LorentzCarrier) :
    F x = (x.1, spinToRot F x.2) := by
  have hsplit : x = x.1 • sOne + ((0 : ℝ), x.2) := by
    apply Prod.ext
    · show x.1 = x.1 * 1 + 0
      ring
    · show x.2 = x.1 • (0 : Fin 3 → ℝ) + x.2
      simp
  have hFx : F x = x.1 • sOne + F ((0 : ℝ), x.2) := by
    conv_lhs => rw [hsplit]
    rw [map_add, map_smul, hone]
  rw [hFx]
  apply Prod.ext
  · show x.1 * 1 + (F ((0:ℝ), x.2)).1 = x.1
    rw [stab_fst_zero hF hone]
    ring
  · show x.1 • (0 : Fin 3 → ℝ) + (F ((0:ℝ), x.2)).2 = spinToRot F x.2
    rw [smul_zero, zero_add]
    rfl


theorem GLor_inv_one {F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier} (hone : F sOne = sOne) : F⁻¹ sOne = sOne := by
  have : F⁻¹ (F sOne) = sOne := by
    show (F⁻¹ * F) sOne = sOne
    rw [inv_mul_cancel]; rfl
  rwa [hone] at this

/-- The `V`-restriction of a unit-fixing member of `G_L`, as a linear automorphism. -/
def stabRot {F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier} (hF : F ∈ GLor) (hone : F sOne = sOne) :
    (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  LinearEquiv.ofLinear (spinToRot F) (spinToRot F⁻¹)
    (by
      apply LinearMap.ext
      intro u
      show (F ((0 : ℝ), (F⁻¹ ((0 : ℝ), u)).2)).2 = u
      have h0 : (F⁻¹ ((0 : ℝ), u)).1 = 0 :=
        stab_fst_zero (GLor.inv_mem hF) (GLor_inv_one hone) u
      have hpair : ((0 : ℝ), (F⁻¹ ((0 : ℝ), u)).2) = F⁻¹ ((0 : ℝ), u) := by
        apply Prod.ext
        · exact h0.symm
        · rfl
      rw [hpair]
      show (F (F⁻¹ ((0 : ℝ), u))).2 = u
      show ((F * F⁻¹) ((0 : ℝ), u)).2 = u
      rw [mul_inv_cancel]; rfl)
    (by
      apply LinearMap.ext
      intro u
      show (F⁻¹ ((0 : ℝ), (F ((0 : ℝ), u)).2)).2 = u
      have h0 : (F ((0 : ℝ), u)).1 = 0 := stab_fst_zero hF hone u
      have hpair : ((0 : ℝ), (F ((0 : ℝ), u)).2) = F ((0 : ℝ), u) := by
        apply Prod.ext
        · exact h0.symm
        · rfl
      rw [hpair]
      show ((F⁻¹ * F) ((0 : ℝ), u)).2 = u
      rw [inv_mul_cancel]; rfl)

@[simp] theorem stabRot_apply {F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier} (hF : F ∈ GLor) (hone : F sOne = sOne)
    (u : Fin 3 → ℝ) : stabRot hF hone u = (F ((0 : ℝ), u)).2 := rfl

theorem BS_vec (u v : Fin 3 → ℝ) : BS ((0 : ℝ), u) ((0 : ℝ), v) = -sip u v := by
  rw [BS_eq]; simp

/-- **D3 (main).**  The stabilizer of the canonical unit inside `G_L` consists exactly of the
maps `id ⊕ R` with `R` an orientation-preserving isometry of the primitive Euclidean space
`(V, ⟨·,·⟩)`.  `SO(3)` is nowhere used: `RotV` is defined from `sip` alone. -/
theorem stabOne_iff (F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) :
    (F ∈ GLor ∧ F sOne = sOne)
      ↔ ∃ R : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ), R ∈ RotV ∧ F = rotToSpin R := by
  constructor
  · rintro ⟨hF, hone⟩
    refine ⟨stabRot hF hone, ⟨fun u v => ?_, ?_⟩, ?_⟩
    · have h := GLor_BS hF ((0 : ℝ), u) ((0 : ℝ), v)
      rw [BS_vec] at h
      have hu : F ((0 : ℝ), u) = ((0 : ℝ), stabRot hF hone u) := by
        apply Prod.ext
        · exact stab_fst_zero hF hone u
        · rfl
      have hv : F ((0 : ℝ), v) = ((0 : ℝ), stabRot hF hone v) := by
        apply Prod.ext
        · exact stab_fst_zero hF hone v
        · rfl
      rw [hu, hv, BS_vec] at h
      linarith
    · have hdec : (F : LorentzCarrier →ₗ[ℝ] LorentzCarrier)
          = LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
            ((stabRot hF hone : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) :
              (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) := by
        apply LinearMap.ext
        intro x
        exact stab_eq_rot hF hone x
      have := hF.2
      rw [hdec, LinearMap.det_prodMap, LinearMap.det_id, one_mul] at this
      exact this
    · apply LinearEquiv.ext
      intro x
      rw [rotToSpin_apply]
      exact stab_eq_rot hF hone x
  · rintro ⟨R, hR, rfl⟩
    exact ⟨rotToSpin_mem hR, rotToSpin_one R⟩

/-! ## D4 : the tangent form -/

/-- **D4.**  On the `B`-orthogonal complement of a shell point, `-B_𝒮` is positive definite.
This is the algebraic tangent-space statement; no differentiable structure is used. -/
theorem tangent_neg_definite {x : LorentzCarrier} (hx : x ∈ Shell) {y : LorentzCarrier} (hy : BS x y = 0)
    (hy0 : y ≠ 0) : 0 < -NS y := by
  rw [mem_shell_iff] at hx
  obtain ⟨hpos, hnorm⟩ := hx
  rw [BS_eq] at hy
  have hcs : (sip x.2 y.2) ^ 2 ≤ sip x.2 x.2 * sip y.2 y.2 := sip_cauchy _ _
  have hv : sip y.2 y.2 ≠ 0 := by
    intro h
    have hy2 : y.2 = 0 := sip_self_eq_zero h
    have hy1 : y.1 = 0 := by
      rw [hy2] at hy
      rw [sip_zero_right] at hy
      have : x.1 * y.1 = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (ne_of_gt hpos)
      · exact h'
    exact hy0 (Prod.ext hy1 hy2)
  have hvpos : 0 < sip y.2 y.2 := lt_of_le_of_ne (sip_self_nonneg y.2) (Ne.symm hv)
  have hxx : sip x.2 x.2 = x.1 ^ 2 - 1 := by linarith
  have hs : x.1 * y.1 = sip x.2 y.2 := by linarith
  rw [hxx] at hcs
  show 0 < -(y.1 ^ 2 - sip y.2 y.2)
  by_contra hcon
  push_neg at hcon
  have h1 : (x.1 * y.1) ^ 2 ≤ (x.1 ^ 2 - 1) * sip y.2 y.2 := by rw [hs]; exact hcs
  have h2 : 0 ≤ x.1 ^ 2 * (y.1 ^ 2 - sip y.2 y.2) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith [h1, h2, hvpos]

/-! ## D5 : the Task-1/Task-3 rapidity inside the shell -/

/-- The one-parameter family of shell points spanned by the unit and the first `V`-axis. -/
def rapidityPoint (eta : ℝ) : LorentzCarrier := (Real.cosh eta, ![Real.sinh eta, 0, 0])

theorem rapidityPoint_mem_shell (eta : ℝ) : rapidityPoint eta ∈ Shell := by
  rw [mem_shell_iff]
  refine ⟨Real.cosh_pos eta, ?_⟩
  show Real.cosh eta ^ 2 - sip ![Real.sinh eta, 0, 0] ![Real.sinh eta, 0, 0] = 1
  simp [sip]
  have := Real.cosh_sq_sub_sinh_sq eta
  nlinarith [this]

@[simp] theorem rapidityPoint_zero : rapidityPoint 0 = sOne := by
  apply Prod.ext
  · show Real.cosh 0 = 1
    simp
  · funext i
    fin_cases i <;> simp [sOne, rapidityPoint]

/-- **D5.1.**  The intrinsic form of two shell points of the rapidity family is the hyperbolic
cosine of the difference of the parameters: the invariant from which the standard rapidity is
read off. -/
theorem BS_rapidityPoint (eta1 eta2 : ℝ) :
    BS (rapidityPoint eta1) (rapidityPoint eta2) = Real.cosh (eta1 - eta2) := by
  rw [BS_eq, Real.cosh_sub]
  show Real.cosh eta1 * Real.cosh eta2
      - sip ![Real.sinh eta1, 0, 0] ![Real.sinh eta2, 0, 0] = _
  simp [sip]

/-- **D5.2 (one-parameter group).**  The intrinsic boosts of the rapidity family compose by
addition of the parameter, exactly as the Task-1/Task-3 boost family does. -/
theorem boost_rapidityPoint (eta1 eta2 : ℝ) :
    boostFun (rapidityPoint eta1) (rapidityPoint eta2) = rapidityPoint (eta1 + eta2) := by
  have hk : Real.cosh eta1 + 1 ≠ 0 := by positivity
  have hid : Real.cosh eta1 ^ 2 - Real.sinh eta1 ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq eta1
  apply Prod.ext
  · show Real.cosh eta1 * Real.cosh eta2
        + sip ![Real.sinh eta1, 0, 0] ![Real.sinh eta2, 0, 0] = Real.cosh (eta1 + eta2)
    rw [Real.cosh_add]
    simp [sip]
  · show ![Real.sinh eta2, 0, 0]
        + (Real.cosh eta2 + sip ![Real.sinh eta1, 0, 0] ![Real.sinh eta2, 0, 0]
            / (Real.cosh eta1 + 1)) • ![Real.sinh eta1, 0, 0]
      = ![Real.sinh (eta1 + eta2), 0, 0]
    rw [Real.sinh_add]
    funext i
    fin_cases i <;> simp [sip]
    field_simp
    linear_combination (-Real.sinh eta2) * hid

/-- **D5.3 (closure with Task 1 and Task 3).**  In the two-dimensional restriction spanned by
the unit and the first `V`-axis, the intrinsic shell boost acts on the null coordinates
`u = y₀ + y₁`, `v = y₀ - y₁` exactly by the reciprocal Task-1 rule `u ↦ e^η u`,
`v ↦ e^{-η} v`. -/
theorem boost_null_coords (eta b w : ℝ) :
    (boostFun (rapidityPoint eta) (b, ![w, 0, 0])).1
        + (boostFun (rapidityPoint eta) (b, ![w, 0, 0])).2 0
      = Real.exp eta * (b + w) ∧
    (boostFun (rapidityPoint eta) (b, ![w, 0, 0])).1
        - (boostFun (rapidityPoint eta) (b, ![w, 0, 0])).2 0
      = Real.exp (-eta) * (b - w) := by
  have hk : Real.cosh eta + 1 ≠ 0 := by positivity
  have hid : Real.cosh eta ^ 2 - Real.sinh eta ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq eta
  have he : Real.exp eta = Real.cosh eta + Real.sinh eta := (Real.cosh_add_sinh eta).symm
  have he' : Real.exp (-eta) = Real.cosh eta - Real.sinh eta := by
    have := Real.cosh_add_sinh (-eta)
    rw [Real.cosh_neg, Real.sinh_neg] at this
    linarith [this]
  have h1 : (boostFun (rapidityPoint eta) (b, ![w, 0, 0])).1
      = Real.cosh eta * b + Real.sinh eta * w := by
    show Real.cosh eta * b + sip ![Real.sinh eta, 0, 0] ![w, 0, 0] = _
    simp [sip]
  have h2 : (boostFun (rapidityPoint eta) (b, ![w, 0, 0])).2 0
      = w + (b + Real.sinh eta * w / (Real.cosh eta + 1)) * Real.sinh eta := by
    show (![w, 0, 0] + (b + sip ![Real.sinh eta, 0, 0] ![w, 0, 0] / (Real.cosh eta + 1))
      • ![Real.sinh eta, 0, 0]) 0 = _
    simp [sip]
  rw [h1, h2, he, he']
  constructor
  · field_simp
    linear_combination (-w) * hid
  · field_simp
    linear_combination w * hid

end SpinCore
