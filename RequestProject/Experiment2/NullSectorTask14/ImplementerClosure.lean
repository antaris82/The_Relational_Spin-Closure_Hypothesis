import RequestProject.Experiment2.NullSectorTask14.MixedInfinitesimalComposition

/-!
# Task 14, Layer 10 (§26): the minimal product-closed implementer algebra

No dimension is prescribed.  The smallest real subspace of the inherited carrier which

* contains every value of the inherited A-axis reference implementation,
* contains every value of the independently derived B-axis reference implementation,
* and is closed under the inherited product,

is determined exactly: it is the four-dimensional subspace spanned by the unit and the
three derived directions `P, Q, R`, its multiplication table is computed, and its own
centre is found to be only the real multiples of the unit — strictly smaller than the exact
centre `Z` of the whole carrier.

This is a principal Task-14 theorem.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## The candidate subspace -/

/-- **NEUTRAL DEFINITION (§26).**  Closure of a subspace under the inherited product. -/
def IsProductClosed (M : Submodule ℝ W) : Prop := ∀ x ∈ M, ∀ y ∈ M, x ⋆ y ∈ M

/-- **NEUTRAL DEFINITION (§26).**  The subspace singled out below, described by
coordinates. -/
def ImplAlg : Submodule ℝ W where
  carrier := {x | x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 7 = 0}
  add_mem' := by
    rintro x y ⟨h1, h2, h3, h7⟩ ⟨k1, k2, k3, k7⟩
    exact ⟨by simp [h1, k1], by simp [h2, k2], by simp [h3, k3], by simp [h7, k7]⟩
  zero_mem' := ⟨rfl, rfl, rfl, rfl⟩
  smul_mem' := by
    rintro c x ⟨h1, h2, h3, h7⟩
    exact ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h7]⟩

/-- **NEUTRAL NOTATION.**  A general element of the subspace. -/
noncomputable def qelt (a b c d : ℝ) : W := a • w1 + b • wP + c • wQ + d • wR

@[simp] theorem qelt_coord_0 (a b c d : ℝ) : qelt a b c d 0 = a := by
  simp [qelt, w1, wP, wQ, wR]
@[simp] theorem qelt_coord_4 (a b c d : ℝ) : qelt a b c d 4 = b := by
  simp [qelt, w1, wP, wQ, wR]
@[simp] theorem qelt_coord_5 (a b c d : ℝ) : qelt a b c d 5 = c := by
  simp [qelt, w1, wP, wQ, wR]
@[simp] theorem qelt_coord_6 (a b c d : ℝ) : qelt a b c d 6 = d := by
  simp [qelt, w1, wP, wQ, wR]

theorem mem_ImplAlg_iff (x : W) : x ∈ ImplAlg ↔ ∃ a b c d : ℝ, x = qelt a b c d := by
  constructor
  · rintro ⟨h1, h2, h3, h7⟩
    refine ⟨x 0, x 4, x 5, x 6, ?_⟩
    funext i
    fin_cases i <;> simp [qelt, w1, wP, wQ, wR, h1, h2, h3, h7]
  · rintro ⟨a, b, c, d, rfl⟩
    exact ⟨by simp [qelt, w1, wP, wQ, wR], by simp [qelt, w1, wP, wQ, wR],
      by simp [qelt, w1, wP, wQ, wR], by simp [qelt, w1, wP, wQ, wR]⟩

/-- **DERIVED (§26): the exact multiplication table of the subspace.** -/
theorem qelt_mul (a b c d a' b' c' d' : ℝ) :
    qelt a b c d ⋆ qelt a' b' c' d'
      = qelt (a * a' - b * b' - c * c' - d * d')
          (a * b' + b * a' - c * d' + d * c')
          (a * c' + c * a' + b * d' - d * b')
          (a * d' + d * a' - b * c' + c * b') := by
  funext i
  fin_cases i <;> simp [qelt, w1, wP, wQ, wR, wit8MulFun] <;> ring

/-- **PRINCIPAL THEOREM (§26), closure.** -/
theorem ImplAlg_productClosed : IsProductClosed ImplAlg := by
  intro x hx y hy
  obtain ⟨a, b, c, d, rfl⟩ := (mem_ImplAlg_iff x).1 hx
  obtain ⟨a', b', c', d', rfl⟩ := (mem_ImplAlg_iff y).1 hy
  rw [qelt_mul]
  exact (mem_ImplAlg_iff _).2 ⟨_, _, _, _, rfl⟩

theorem qelt_eq_zero_iff (a b c d : ℝ) :
    qelt a b c d = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 4,
      by simpa using congrFun h 5, by simpa using congrFun h 6⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    funext i; fin_cases i <;> simp [qelt, w1, wP, wQ, wR]

/-- **PRINCIPAL THEOREM (§26), exact real dimension.** -/
theorem finrank_ImplAlg : Module.finrank ℝ (ImplAlg : Submodule ℝ W) = 4 := by
  have hspan : ImplAlg = Submodule.span ℝ (Set.range ![w1, wP, wQ, wR]) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨a, b, c, d, rfl⟩ := (mem_ImplAlg_iff x).1 hx
      have hq : qelt a b c d = a • w1 + b • wP + c • wQ + d • wR := rfl
      rw [hq]
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
        refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
      · exact ⟨3, by simp⟩
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      fin_cases i
      · exact (mem_ImplAlg_iff _).2 ⟨1, 0, 0, 0, by funext j; fin_cases j <;> simp [qelt, w1, wP, wQ, wR]⟩
      · exact (mem_ImplAlg_iff _).2 ⟨0, 1, 0, 0, by funext j; fin_cases j <;> simp [qelt, w1, wP, wQ, wR]⟩
      · exact (mem_ImplAlg_iff _).2 ⟨0, 0, 1, 0, by funext j; fin_cases j <;> simp [qelt, w1, wP, wQ, wR]⟩
      · exact (mem_ImplAlg_iff _).2 ⟨0, 0, 0, 1, by funext j; fin_cases j <;> simp [qelt, w1, wP, wQ, wR]⟩
  have hli : LinearIndependent ℝ ![w1, wP, wQ, wR] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hsum : qelt (g 0) (g 1) (g 2) (g 3) = 0 := by
      rw [qelt]
      simpa [Fin.sum_univ_four] using hg
    obtain ⟨h0, h1, h2, h3⟩ := (qelt_eq_zero_iff _ _ _ _).1 hsum
    fin_cases i <;> assumption
  rw [hspan, finrank_span_eq_card hli]
  simp

/-! ## The two reference families lie in the subspace -/

theorem Uref_mem_ImplAlg (θ : ℝ) : Uref θ ∈ ImplAlg := by
  rw [Uref_apply, ksc]
  exact ⟨by simp [w1, wR], by simp [w1, wR], by simp [w1, wR], by simp [w1, wR]⟩

theorem UBref_mem_ImplAlg (φ : ℝ) : UBref φ ∈ ImplAlg := by
  rw [UBref_apply]
  exact ⟨by simp [w1, wQ], by simp [w1, wQ], by simp [w1, wQ], by simp [w1, wQ]⟩

/-! ## Minimality -/

/-- **PRINCIPAL THEOREM (§26): `minimal_implementer_subalgebra`.**  Every product-closed
subspace containing the two independently derived reference families contains the whole
four-dimensional subspace: no smaller product-closed carrier suffices, and no extra
noncentral direction is needed. -/
theorem ImplAlg_minimal {M : Submodule ℝ W} (hM : IsProductClosed M)
    (hA : ∀ θ, Uref θ ∈ M) (hB : ∀ φ, UBref φ ∈ M) : ImplAlg ≤ M := by
  have h1 : w1 ∈ M := by
    have := hA 0
    rwa [show Uref 0 = w1 from Uref_isFullLift.unit] at this
  have hR : wR ∈ M := by
    have hpi := hA Real.pi
    have hval : Uref Real.pi = -wR := by
      rw [Uref_apply, ksc, Real.cos_pi_div_two, Real.sin_pi_div_two]
      module
    rw [hval] at hpi
    simpa using Submodule.neg_mem M hpi
  have hQ : wQ ∈ M := by
    have hpi := hB Real.pi
    have hval : UBref Real.pi = wQ := by
      rw [UBref_apply, Real.cos_pi_div_two, Real.sin_pi_div_two]
      module
    rwa [hval] at hpi
  have hP : wP ∈ M := by
    have := hM wR hR wQ hQ
    rwa [wit8_wR_wQ] at this
  intro x hx
  obtain ⟨a, b, c, d, rfl⟩ := (mem_ImplAlg_iff x).1 hx
  have hq : qelt a b c d = a • w1 + b • wP + c • wQ + d • wR := rfl
  rw [hq]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ hP))
    (Submodule.smul_mem _ _ hQ)) (Submodule.smul_mem _ _ hR)

/-! ## The centre inside the subalgebra -/

/-- **PRINCIPAL THEOREM (§26): the centre of the minimal implementer algebra.**  Inside the
four-dimensional product-closed subspace the elements commuting with everything are exactly
the real multiples of the unit.  In particular the exact centre `Z` of the whole carrier is
**not** contained in it: the central element `S` lies outside. -/
theorem ImplAlg_center :
    (∀ x ∈ ImplAlg, (∀ y ∈ ImplAlg, x ⋆ y = y ⋆ x) ↔ ∃ a : ℝ, x = a • w1) ∧
    wS ∉ ImplAlg := by
  constructor
  · intro x hx
    obtain ⟨a, b, c, d, rfl⟩ := (mem_ImplAlg_iff x).1 hx
    constructor
    · intro hcomm
      have hP := hcomm wP ((mem_ImplAlg_iff _).2 ⟨0, 1, 0, 0, by
        funext j; fin_cases j <;> simp [qelt, w1, wP, wQ, wR]⟩)
      have hQ := hcomm wQ ((mem_ImplAlg_iff _).2 ⟨0, 0, 1, 0, by
        funext j; fin_cases j <;> simp [qelt, w1, wP, wQ, wR]⟩)
      have h5 := congrFun hP 5
      have h6 := congrFun hP 6
      have h4 := congrFun hQ 4
      have h6' := congrFun hQ 6
      simp [qelt, w1, wP, wQ, wR] at h5 h6 h4 h6'
      refine ⟨a, ?_⟩
      funext i
      fin_cases i <;> simp [qelt, w1, wP, wQ, wR] <;> linarith
    · rintro ⟨a', ha'⟩ y hy
      rw [ha']
      rw [smul_mul_W, mul_smul_W, one_mul_W, mul_one_W]
  · rintro ⟨-, -, -, h7⟩
    simp [wS] at h7

end NullSectorTask14
