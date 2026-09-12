import Mathlib
import RequestProject.Spine.E1.LorentzGroup

/-!
# Task 10, Branch 3 (part 1) : the unit future shell and its intrinsic boosts

**Consumed Task 1–9 data.**  Only `NS` and `ConeS` (hence `IntFuture`), the additive/linear
structure of `𝒮`, and the intrinsic group `GLor`.  No new bilinear form, no topology, no
manifold structure, no independently chosen time orientation: the future condition is the
Task-9 square cone itself.

The shell is

`𝓗 = {x : N(x) = 1 ∧ x ∈ 𝒞}`,

and for every `x ∈ 𝓗` an explicit norm- and cone-preserving automorphism `boostEquiv x`
sending `1_𝒮` to `x` is constructed from `x` alone (it is the composite of the two
`B`-reflections in `1_𝒮` and in `x + 1_𝒮`, written out in closed form).
-/

noncomputable section

namespace SpinCore

open SpinCore

/-! ## D1 : the unit future shell -/

/-- **D1 (definition).**  The unit future shell: intrinsic norm `1`, inside the intrinsic
square cone. -/
def Shell : Set LorentzCarrier := {x : LorentzCarrier | NS x = 1 ∧ x ∈ ConeS}

theorem shell_subset_intFuture : Shell ⊆ IntFuture := by
  rintro x ⟨h1, h2⟩
  exact ⟨h2, by rw [h1]; norm_num⟩

theorem shell_fst_pos {x : LorentzCarrier} (hx : x ∈ Shell) : 0 < x.1 :=
  intFuture_fst_pos (shell_subset_intFuture hx)

theorem shell_norm {x : LorentzCarrier} (hx : x ∈ Shell) : x.1 ^ 2 - sip x.2 x.2 = 1 := hx.1

theorem one_mem_shell : sOne ∈ Shell := by
  refine ⟨?_, one_mem_coneS⟩
  rw [NS_def]
  simp [sOne, sip]

/-- Membership in the shell is decided by the two intrinsic scalars. -/
theorem mem_shell_iff (x : LorentzCarrier) : x ∈ Shell ↔ (0 < x.1 ∧ x.1 ^ 2 - sip x.2 x.2 = 1) := by
  constructor
  · intro hx
    exact ⟨shell_fst_pos hx, hx.1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rw [mem_coneS_iff]
    exact ⟨h1.le, by rw [NS_def, h2]; norm_num⟩

/-- **D1.1.**  `G_L` preserves the unit future shell. -/
theorem GLor_shell {F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier} (hF : F ∈ GLor) (x : LorentzCarrier) :
    x ∈ Shell ↔ F x ∈ Shell := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [GLor_NS hF]; exact h1, (GLor_cone hF x).1 h2⟩
  · rintro ⟨h1, h2⟩
    rw [GLor_NS hF] at h1
    exact ⟨h1, (GLor_cone hF x).2 h2⟩

/-! ## D2 : the intrinsic boost attached to a shell element -/

/-- The closed form of the composite of the `B`-reflections in `1_𝒮` and in `x + 1_𝒮`.  For
`x ∈ 𝓗` this is the unique boost carrying `1_𝒮` to `x` in the plane they span. -/
def boostFun (x y : LorentzCarrier) : LorentzCarrier :=
  (x.1 * y.1 + sip x.2 y.2, y.2 + (y.1 + sip x.2 y.2 / (x.1 + 1)) • x.2)

/-- The `𝒮`-conjugate `(a, u) ↦ (a, -u)`; for `x ∈ 𝓗` it is again in `𝓗` and its boost is
the inverse boost. -/
def spinConj (x : LorentzCarrier) : LorentzCarrier := (x.1, -x.2)

theorem spinConj_mem_shell {x : LorentzCarrier} (hx : x ∈ Shell) : spinConj x ∈ Shell := by
  rw [mem_shell_iff] at hx ⊢
  refine ⟨hx.1, ?_⟩
  have h : sip (-x.2) (-x.2) = sip x.2 x.2 := by
    have := sip_smul_self (-1 : ℝ) x.2
    simpa using this
  show x.1 ^ 2 - sip (-x.2) (-x.2) = 1
  rw [h]; exact hx.2

@[simp] theorem boostFun_fst (x y : LorentzCarrier) : (boostFun x y).1 = x.1 * y.1 + sip x.2 y.2 := rfl

@[simp] theorem boostFun_snd (x y : LorentzCarrier) :
    (boostFun x y).2 = y.2 + (y.1 + sip x.2 y.2 / (x.1 + 1)) • x.2 := rfl

/-- The boost, as a linear map. -/
def boostLin (x : LorentzCarrier) : LorentzCarrier →ₗ[ℝ] LorentzCarrier where
  toFun := boostFun x
  map_add' y z := by
    apply Prod.ext
    · show x.1 * (y.1 + z.1) + sip x.2 (y.2 + z.2) = _
      rw [sip_add_right]
      show _ = (x.1 * y.1 + sip x.2 y.2) + (x.1 * z.1 + sip x.2 z.2)
      ring
    · show (y.2 + z.2) + ((y.1 + z.1) + sip x.2 (y.2 + z.2) / (x.1 + 1)) • x.2
        = (y.2 + (y.1 + sip x.2 y.2 / (x.1 + 1)) • x.2)
          + (z.2 + (z.1 + sip x.2 z.2 / (x.1 + 1)) • x.2)
      rw [sip_add_right]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  map_smul' r y := by
    apply Prod.ext
    · show x.1 * (r * y.1) + sip x.2 (r • y.2) = r * (x.1 * y.1 + sip x.2 y.2)
      rw [sip_smul_right]; ring
    · show (r • y.2) + ((r * y.1) + sip x.2 (r • y.2) / (x.1 + 1)) • x.2
        = r • (y.2 + (y.1 + sip x.2 y.2 / (x.1 + 1)) • x.2)
      rw [sip_smul_right]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

@[simp] theorem boostLin_apply (x y : LorentzCarrier) : boostLin x y = boostFun x y := rfl

/-- **D2.1.**  The inverse boost undoes the boost.  Consumes only `x ∈ 𝓗`. -/
theorem boostFun_conj_left {x : LorentzCarrier} (hx : x ∈ Shell) (y : LorentzCarrier) :
    boostFun (spinConj x) (boostFun x y) = y := by
  rw [mem_shell_iff] at hx
  obtain ⟨hpos, hnorm⟩ := hx
  have hk : x.1 + 1 ≠ 0 := by positivity
  have hW : sip x.2 x.2 = x.1 ^ 2 - 1 := by linarith
  apply Prod.ext
  · show x.1 * (x.1 * y.1 + sip x.2 y.2)
      + sip (-x.2) (y.2 + (y.1 + sip x.2 y.2 / (x.1 + 1)) • x.2) = y.1
    rw [sip_add_right, sip_smul_right]
    have h1 : sip (-x.2) y.2 = -sip x.2 y.2 := by
      have := sip_smul_left (-1 : ℝ) x.2 y.2
      simpa using this
    have h2 : sip (-x.2) x.2 = -sip x.2 x.2 := by
      have := sip_smul_left (-1 : ℝ) x.2 x.2
      simpa using this
    rw [h1, h2, hW]
    field_simp
    ring
  · show (y.2 + (y.1 + sip x.2 y.2 / (x.1 + 1)) • x.2)
      + ((x.1 * y.1 + sip x.2 y.2)
        + sip (-x.2) (y.2 + (y.1 + sip x.2 y.2 / (x.1 + 1)) • x.2) / ((x.1, -x.2).1 + 1))
          • (-x.2) = y.2
    rw [sip_add_right, sip_smul_right]
    have h1 : sip (-x.2) y.2 = -sip x.2 y.2 := by
      have := sip_smul_left (-1 : ℝ) x.2 y.2
      simpa using this
    have h2 : sip (-x.2) x.2 = -sip x.2 x.2 := by
      have := sip_smul_left (-1 : ℝ) x.2 x.2
      simpa using this
    rw [h1, h2, hW]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    field_simp
    ring

/-- The boost attached to a shell element, as a linear automorphism. -/
def boostEquiv {x : LorentzCarrier} (hx : x ∈ Shell) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier :=
  LinearEquiv.ofLinear (boostLin x) (boostLin (spinConj x))
    (by
      apply LinearMap.ext
      intro y
      show boostFun x (boostFun (spinConj x) y) = y
      have h := boostFun_conj_left (spinConj_mem_shell hx) y
      have hc : spinConj (spinConj x) = x := by
        apply Prod.ext
        · rfl
        · show -(-x.2) = x.2
          simp
      rwa [hc] at h)
    (by
      apply LinearMap.ext
      intro y
      exact boostFun_conj_left hx y)

@[simp] theorem boostEquiv_apply {x : LorentzCarrier} (hx : x ∈ Shell) (y : LorentzCarrier) :
    boostEquiv hx y = boostFun x y := rfl

/-- **D2.2.**  The boost carries the unit to `x`. -/
theorem boostEquiv_one {x : LorentzCarrier} (hx : x ∈ Shell) : boostEquiv hx sOne = x := by
  rw [boostEquiv_apply]
  apply Prod.ext
  · show x.1 * 1 + sip x.2 0 = x.1
    rw [sip_zero_right]; ring
  · show (0 : Fin 3 → ℝ) + (1 + sip x.2 0 / (x.1 + 1)) • x.2 = x.2
    rw [sip_zero_right]
    funext i
    simp

/-- **D2.3 (norm preservation).** -/
theorem boostFun_NS {x : LorentzCarrier} (hx : x ∈ Shell) (y : LorentzCarrier) : NS (boostFun x y) = NS y := by
  rw [mem_shell_iff] at hx
  obtain ⟨hpos, hnorm⟩ := hx
  have hk : x.1 + 1 ≠ 0 := by positivity
  have hW : sip x.2 x.2 = x.1 ^ 2 - 1 := by linarith
  show (x.1 * y.1 + sip x.2 y.2) ^ 2
      - sip (y.2 + (y.1 + sip x.2 y.2 / (x.1 + 1)) • x.2)
          (y.2 + (y.1 + sip x.2 y.2 / (x.1 + 1)) • x.2) = _
  rw [sip_add_left, sip_add_right, sip_add_right, sip_smul_left, sip_smul_right,
    sip_smul_right, sip_smul_left, sip_comm x.2 y.2, hW]
  show _ = y.1 ^ 2 - sip y.2 y.2
  field_simp
  ring

/-- **D2.4 (cone preservation, one direction).** -/
theorem boostFun_mem_cone {x : LorentzCarrier} (hx : x ∈ Shell) {y : LorentzCarrier} (hy : y ∈ ConeS) :
    boostFun x y ∈ ConeS := by
  have hxs := hx
  rw [mem_shell_iff] at hxs
  obtain ⟨hpos, hnorm⟩ := hxs
  rw [mem_coneS_iff] at hy ⊢
  obtain ⟨hy1, hy2⟩ := hy
  rw [NS_def] at hy2
  refine ⟨?_, ?_⟩
  · show 0 ≤ x.1 * y.1 + sip x.2 y.2
    have hcs : (sip x.2 y.2) ^ 2 ≤ sip x.2 x.2 * sip y.2 y.2 := sip_cauchy _ _
    nlinarith [sip_self_nonneg x.2, sip_self_nonneg y.2, mul_nonneg hpos.le hy1]
  · rw [boostFun_NS hx, NS_def]; linarith

/-- **D2.5 (the boost is in the wide intrinsic group).** -/
theorem boostEquiv_wide {x : LorentzCarrier} (hx : x ∈ Shell) : IsGLorWide (boostEquiv hx) := by
  refine ⟨fun y => boostFun_NS hx y, fun y => ?_⟩
  constructor
  · intro hy
    exact boostFun_mem_cone hx hy
  · intro hy
    have h := boostFun_mem_cone (spinConj_mem_shell hx) hy
    rwa [boostEquiv_apply, boostFun_conj_left hx] at h

end SpinCore
