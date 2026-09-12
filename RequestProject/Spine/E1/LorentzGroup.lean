import Mathlib
import RequestProject.Spine.E1.Carrier

/-!
# Task 10, Part A : freezing the Task-9 endpoint

This file freezes the exact dependency endpoint of Task 9 that Task 10 consumes, and adds
**no new primitive data**.  The inherited objects are

* the carrier `𝒮 = SpinCore.LorentzCarrier = ℝ ⊕ ℝ³` with its additive/real-linear structure;
* the Euclidean form `SpinCore.sip` on `V = ℝ³` (the only primitive bilinear datum of the
  project);
* the Jordan product `SpinCore.sJ` and unit `SpinCore.sOne`;
* the trace `SpinCore.strS`, the quadratic norm `SpinCore.NS`, its polarization `SpinCore.BS`, and
  the square cone `SpinCore.ConeS`.

Part A of Task 10 records the elementary structural facts about `NS`, `BS` and `ConeS`
which the four branches consume (bilinearity, symmetry, nondegeneracy, the intrinsic
characterization of the cone, convexity, pointedness), and defines the intrinsic group

`G_L = Aut⁺_{N,𝒞}(𝒮) = {F : 𝒮 ≃ₗ[ℝ] 𝒮 | N∘F = N, F⁻¹𝒞 = 𝒞, det_ℝ F = 1}`

directly on the spin factor.  Only *afterwards* is `G_L` compared with the Task-8 group
`Task8.JordanConeAut` and hence with `SO⁺(1,3)`.

**Audit note.**  Every definition in sections A1–A3 mentions only `ℝ`, `Fin 3`, `sip`,
`sJ`, `NS`, `BS`, `ConeS` and real-linear algebra.  The Hermitian carrier appears for the
first time in section A4, and only inside comparison theorems.
-/

noncomputable section

namespace SpinCore

open SpinCore

/-! ## A1 : the inherited quadratic and bilinear data -/

theorem NS_def (x : LorentzCarrier) : NS x = x.1 ^ 2 - sip x.2 x.2 := rfl

theorem sip_smul_right (r : ℝ) (u v : Fin 3 → ℝ) : sip u (r • v) = r * sip u v := by
  rw [sip_comm, sip_smul_left, sip_comm]

theorem sip_add_right (u v w : Fin 3 → ℝ) : sip u (v + w) = sip u v + sip u w := by
  rw [sip_comm, sip_add_left, sip_comm, sip_comm w u]

theorem sip_smul_self (r : ℝ) (u : Fin 3 → ℝ) : sip (r • u) (r • u) = r ^ 2 * sip u u := by
  rw [sip_smul_left, sip_smul_right]; ring

theorem sip_zero_left (u : Fin 3 → ℝ) : sip 0 u = 0 := by simp [sip]

theorem sip_zero_right (u : Fin 3 → ℝ) : sip u 0 = 0 := by simp [sip]

/-- Cauchy–Schwarz for the primitive Euclidean form on `V = ℝ³`. -/
theorem sip_cauchy (u v : Fin 3 → ℝ) : (sip u v) ^ 2 ≤ sip u u * sip v v := by
  simp only [sip]
  nlinarith [sq_nonneg (u 0 * v 1 - u 1 * v 0), sq_nonneg (u 0 * v 2 - u 2 * v 0),
    sq_nonneg (u 1 * v 2 - u 2 * v 1)]

/-- `B_𝒮` is symmetric. -/
theorem BS_symm (x y : LorentzCarrier) : BS x y = BS y x := by
  rw [BS_eq, BS_eq, sip_comm]; ring

/-- `B_𝒮` polarizes `N_𝒮`. -/
theorem BS_self (x : LorentzCarrier) : BS x x = NS x := by
  rw [BS_eq, NS_def]; ring

theorem BS_add_left (x y z : LorentzCarrier) : BS (x + y) z = BS x z + BS y z := by
  simp only [BS_eq, Prod.fst_add, Prod.snd_add, sip_add_left]; ring

theorem BS_add_right (x y z : LorentzCarrier) : BS x (y + z) = BS x y + BS x z := by
  rw [BS_symm, BS_add_left, BS_symm, BS_symm z x]

theorem BS_smul_left (r : ℝ) (x y : LorentzCarrier) : BS (r • x) y = r * BS x y := by
  simp only [BS_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, sip_smul_left]; ring

theorem BS_smul_right (r : ℝ) (x y : LorentzCarrier) : BS x (r • y) = r * BS x y := by
  rw [BS_symm, BS_smul_left, BS_symm]

theorem BS_zero_left (x : LorentzCarrier) : BS 0 x = 0 := by
  simp [BS_eq, sip_zero_left]

theorem BS_zero_right (x : LorentzCarrier) : BS x 0 = 0 := by
  rw [BS_symm, BS_zero_left]

theorem BS_neg_left (x y : LorentzCarrier) : BS (-x) y = -BS x y := by
  have := BS_smul_left (-1 : ℝ) x y
  simpa using this

theorem BS_sub_left (x y z : LorentzCarrier) : BS (x - y) z = BS x z - BS y z := by
  rw [sub_eq_add_neg, BS_add_left, BS_neg_left, sub_eq_add_neg]

theorem BS_sub_right (x y z : LorentzCarrier) : BS x (y - z) = BS x y - BS x z := by
  rw [BS_symm, BS_sub_left, BS_symm, BS_symm z x]

/-- **A1 (nondegeneracy).**  `B_𝒮` is a nondegenerate symmetric bilinear form.  This is the
prerequisite of the bivector branch (E) and is proved here, once. -/
theorem BS_nondegenerate {x : LorentzCarrier} (h : ∀ y : LorentzCarrier, BS x y = 0) : x = 0 := by
  have hx := h (x.1, -x.2)
  rw [BS_eq] at hx
  have hs : sip x.2 (-x.2) = -sip x.2 x.2 := by
    have := sip_smul_right (-1 : ℝ) x.2 x.2
    simpa using this
  rw [hs] at hx
  have h1 : x.1 = 0 := by nlinarith [sip_self_nonneg x.2, sq_nonneg x.1]
  have h2 : sip x.2 x.2 = 0 := by nlinarith [sip_self_nonneg x.2]
  have := sip_self_eq_zero h2
  exact Prod.ext h1 this

/-! ## A2 : the inherited cone -/

/-- **A2 (intrinsic characterization of the square cone).**  `x` is a Jordan square iff its
trace and its norm are nonnegative.  Proved directly on the spin factor: no Hermitian
matrices, no positive semidefiniteness, no coordinates other than the intrinsic
decomposition `𝒮 = ℝ ⊕ V`. -/
theorem mem_coneS_iff (x : LorentzCarrier) : x ∈ ConeS ↔ 0 ≤ x.1 ∧ 0 ≤ NS x := by
  constructor
  · rintro ⟨y, rfl⟩
    have hfst : (sJ y y).1 = y.1 ^ 2 + sip y.2 y.2 := by rw [sJ_fst]; ring
    have hsnd : (sJ y y).2 = (2 * y.1) • y.2 := by
      rw [sJ_snd]; funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    constructor
    · rw [hfst]; nlinarith [sip_self_nonneg y.2, sq_nonneg y.1]
    · rw [NS_def, hfst, hsnd, sip_smul_self]
      nlinarith [sq_nonneg (y.1 ^ 2 - sip y.2 y.2)]
  · rintro ⟨ha, hN⟩
    set a : ℝ := x.1 with hadef
    set u : Fin 3 → ℝ := x.2 with hudef
    set q : ℝ := sip u u with hqdef
    have hq0 : 0 ≤ q := sip_self_nonneg u
    have hNq : 0 ≤ a ^ 2 - q := by rw [NS_def] at hN; exact hN
    set d : ℝ := Real.sqrt (a ^ 2 - q) with hddef
    have hd0 : 0 ≤ d := Real.sqrt_nonneg _
    have hdsq : d ^ 2 = a ^ 2 - q := Real.sq_sqrt hNq
    set s : ℝ := (a + d) / 2 with hsdef
    have hs0 : 0 ≤ s := by positivity
    rcases eq_or_lt_of_le hs0 with hs | hs
    · -- degenerate case: `s = 0` forces `x = 0`
      have hae : a = 0 := by linarith [hs.symm ▸ (by linarith : a + d = 2 * s)]
      have hde : d = 0 := by linarith [hs.symm ▸ (by linarith : a + d = 2 * s)]
      have hqe : q = 0 := by
        have : (0:ℝ) ^ 2 = a ^ 2 - q := by rw [← hde, hdsq]
        rw [hae] at this; linarith [this]
      have hu : u = 0 := sip_self_eq_zero hqe
      refine ⟨0, ?_⟩
      apply Prod.ext
      · show a = _
        rw [sJ_fst]; simp [sip_zero_left, hae]
      · show u = _
        rw [sJ_snd, hu]; simp
    · -- generic case
      set b : ℝ := Real.sqrt s with hbdef
      have hb0 : 0 < b := Real.sqrt_pos.2 hs
      have hbsq : b ^ 2 = s := Real.sq_sqrt hs0
      refine ⟨(b, (1 / (2 * b)) • u), ?_⟩
      have h2b : (2 : ℝ) * b ≠ 0 := by positivity
      have hqs : q = (a - d) * (2 * s) := by
        have : q = a ^ 2 - d ^ 2 := by rw [hdsq]; ring
        rw [this, hsdef]; ring
      apply Prod.ext
      · show a = b * b + sip ((1 / (2 * b)) • u) ((1 / (2 * b)) • u)
        rw [sip_smul_self, ← hqdef]
        have hbb : b * b = s := by rw [← hbsq]; ring
        rw [hbb, hqs]
        field_simp
        rw [hbsq, hsdef]
        ring
      · show u = b • (1 / (2 * b)) • u + b • (1 / (2 * b)) • u
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring

theorem zero_mem_coneS : (0 : LorentzCarrier) ∈ ConeS := by
  rw [mem_coneS_iff]
  refine ⟨le_refl _, ?_⟩
  rw [NS_def]
  simp [sip_zero_left]

theorem one_mem_coneS : sOne ∈ ConeS := by
  rw [mem_coneS_iff]
  refine ⟨by norm_num [sOne], ?_⟩
  rw [NS_def]
  simp [sOne, sip_zero_left]

/-- **A2 (convexity).** The cone is closed under addition. -/
theorem add_mem_coneS {x y : LorentzCarrier} (hx : x ∈ ConeS) (hy : y ∈ ConeS) : x + y ∈ ConeS := by
  rw [mem_coneS_iff] at hx hy ⊢
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  rw [NS_def] at hx2 hy2
  refine ⟨by simpa using add_nonneg hx1 hy1, ?_⟩
  rw [NS_def]
  have hsum : sip (x + y).2 (x + y).2
      = sip x.2 x.2 + 2 * sip x.2 y.2 + sip y.2 y.2 := by
    show sip (x.2 + y.2) (x.2 + y.2) = _
    rw [sip_add_left, sip_add_right, sip_add_right, sip_comm y.2 x.2]; ring
  rw [hsum]
  have hcs : (sip x.2 y.2) ^ 2 ≤ sip x.2 x.2 * sip y.2 y.2 := sip_cauchy _ _
  have hxy : sip x.2 y.2 ≤ x.1 * y.1 := by
    nlinarith [sip_self_nonneg x.2, sip_self_nonneg y.2, mul_nonneg hx1 hy1]
  show 0 ≤ (x.1 + y.1) ^ 2 - _
  nlinarith

theorem smul_mem_coneS {x : LorentzCarrier} (hx : x ∈ ConeS) {r : ℝ} (hr : 0 ≤ r) : r • x ∈ ConeS := by
  rw [mem_coneS_iff] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  rw [NS_def] at h2
  refine ⟨by simpa using mul_nonneg hr h1, ?_⟩
  rw [NS_def]
  show 0 ≤ (r * x.1) ^ 2 - sip (r • x.2) (r • x.2)
  rw [sip_smul_self]
  nlinarith

/-- **A2 (pointedness).**  `𝒞 ∩ (-𝒞) = {0}`.  This is the fact that makes causal
antisymmetry work in Branch 2. -/
theorem coneS_pointed {x : LorentzCarrier} (h₁ : x ∈ ConeS) (h₂ : -x ∈ ConeS) : x = 0 := by
  rw [mem_coneS_iff] at h₁ h₂
  obtain ⟨ha, hN⟩ := h₁
  obtain ⟨ha', -⟩ := h₂
  have hx1 : x.1 = 0 := by
    have : (0:ℝ) ≤ -x.1 := by simpa using ha'
    linarith
  rw [NS_def, hx1] at hN
  have : sip x.2 x.2 = 0 := le_antisymm (by linarith) (sip_self_nonneg x.2)
  exact Prod.ext hx1 (sip_self_eq_zero this)

theorem coneS_fst_nonneg {x : LorentzCarrier} (hx : x ∈ ConeS) : 0 ≤ x.1 := ((mem_coneS_iff x).1 hx).1

theorem coneS_NS_nonneg {x : LorentzCarrier} (hx : x ∈ ConeS) : 0 ≤ NS x := ((mem_coneS_iff x).1 hx).2

/-- The intrinsic **interior future** predicate: an element of the square cone with strictly
positive norm.  Only `NS` and `ConeS` are used. -/
def IntFuture : Set LorentzCarrier := {x : LorentzCarrier | x ∈ ConeS ∧ 0 < NS x}

/-- On the interior future the trace component is strictly positive. -/
theorem intFuture_fst_pos {x : LorentzCarrier} (hx : x ∈ IntFuture) : 0 < x.1 := by
  obtain ⟨hc, hN⟩ := hx
  have h1 : 0 ≤ x.1 := coneS_fst_nonneg hc
  rcases eq_or_lt_of_le h1 with h | h
  · exfalso
    rw [NS_def, ← h] at hN
    nlinarith [sip_self_nonneg x.2]
  · exact h

theorem one_mem_intFuture : sOne ∈ IntFuture := by
  refine ⟨one_mem_coneS, ?_⟩
  rw [NS_def]
  simp [sOne, sip_zero_left]

/-! ## A3 : the intrinsic norm/cone automorphism group `G_L` -/

/-- The two intrinsic conditions: preservation of `N_𝒮` and of the square cone. -/
def IsGLorWide (F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : Prop :=
  (∀ x : LorentzCarrier, NS (F x) = NS x) ∧ (∀ x : LorentzCarrier, x ∈ ConeS ↔ F x ∈ ConeS)

/-- **A3 (main intrinsic definition).**  `G_L = Aut⁺_{N,𝒞}(𝒮)`: real-linear
automorphisms of the carrier preserving the intrinsic norm and the intrinsic square cone,
with intrinsic orientation `det_ℝ F = 1`. -/
def IsGLor (F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : Prop :=
  IsGLorWide F ∧ LinearMap.det (F : LorentzCarrier →ₗ[ℝ] LorentzCarrier) = 1

theorem isGLorWide_inv {F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier} (h : IsGLorWide F) : IsGLorWide F⁻¹ := by
  obtain ⟨h1, h2⟩ := h
  have hFF : ∀ x : LorentzCarrier, F (F⁻¹ x) = x := by
    intro x
    show (F * F⁻¹) x = x
    rw [mul_inv_cancel]; rfl
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have := h1 (F⁻¹ x); rw [hFF] at this; exact this.symm
  · have := h2 (F⁻¹ x); rw [hFF] at this; exact this.symm

/-- The wide intrinsic group (no orientation condition). -/
def GLorWide : Subgroup (LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) where
  carrier := {F | IsGLorWide F}
  one_mem' := ⟨fun _ => rfl, fun _ => Iff.rfl⟩
  mul_mem' := by
    rintro F G ⟨hF1, hF2⟩ ⟨hG1, hG2⟩
    exact ⟨fun x => (hF1 (G x)).trans (hG1 x), fun x => (hG2 x).trans (hF2 (G x))⟩
  inv_mem' h := isGLorWide_inv h

/-- **A3.** The intrinsic proper norm/cone automorphism group of the spin factor. -/
def GLor : Subgroup (LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) where
  carrier := {F | IsGLor F}
  one_mem' := by
    refine ⟨GLorWide.one_mem, ?_⟩
    show LinearMap.det (LinearMap.id : LorentzCarrier →ₗ[ℝ] LorentzCarrier) = 1
    simp
  mul_mem' := by
    rintro F G ⟨hF1, hF2⟩ ⟨hG1, hG2⟩
    refine ⟨GLorWide.mul_mem hF1 hG1, ?_⟩
    have h : ((F * G : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : LorentzCarrier →ₗ[ℝ] LorentzCarrier)
        = (F : LorentzCarrier →ₗ[ℝ] LorentzCarrier) ∘ₗ (G : LorentzCarrier →ₗ[ℝ] LorentzCarrier) := rfl
    rw [h, LinearMap.det_comp, hF2, hG2, one_mul]
  inv_mem' := by
    rintro F ⟨h1, h2⟩
    refine ⟨isGLorWide_inv h1, ?_⟩
    have hcomp : ((F : LorentzCarrier →ₗ[ℝ] LorentzCarrier) ∘ₗ ((F⁻¹ : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : LorentzCarrier →ₗ[ℝ] LorentzCarrier))
        = (LinearMap.id : LorentzCarrier →ₗ[ℝ] LorentzCarrier) := by
      apply LinearMap.ext
      intro x
      show F (F⁻¹ x) = x
      show (F * F⁻¹) x = x
      rw [mul_inv_cancel]; rfl
    have := congrArg LinearMap.det hcomp
    rw [LinearMap.det_comp, h2, one_mul] at this
    simpa using this

theorem mem_GLor {F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier} : F ∈ GLor ↔ IsGLor F := Iff.rfl

theorem GLor_le_GLorWide : GLor ≤ GLorWide := fun _ h => h.1

/-- Members of `G_L` preserve `N_𝒮`. -/
theorem GLor_NS {F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier} (hF : F ∈ GLor) (x : LorentzCarrier) : NS (F x) = NS x := hF.1.1 x

/-- **A3.** Members of `G_L` preserve the polarized form `B_𝒮`: an immediate consequence of
norm preservation and linearity. -/
theorem GLor_BS {F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier} (hF : F ∈ GLor) (x y : LorentzCarrier) : BS (F x) (F y) = BS x y := by
  unfold BS
  rw [← map_add, hF.1.1, hF.1.1, hF.1.1]

/-- Members of `G_L` preserve the square cone. -/
theorem GLor_cone {F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier} (hF : F ∈ GLor) (x : LorentzCarrier) : x ∈ ConeS ↔ F x ∈ ConeS :=
  hF.1.2 x

/-- Members of `G_L` preserve the intrinsic interior future. -/
theorem GLor_intFuture {F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier} (hF : F ∈ GLor) (x : LorentzCarrier) :
    x ∈ IntFuture ↔ F x ∈ IntFuture := by
  constructor
  · rintro ⟨hc, hN⟩
    exact ⟨(GLor_cone hF x).1 hc, by rw [GLor_NS hF]; exact hN⟩
  · rintro ⟨hc, hN⟩
    rw [GLor_NS hF] at hN
    exact ⟨(GLor_cone hF x).2 hc, hN⟩

end SpinCore
