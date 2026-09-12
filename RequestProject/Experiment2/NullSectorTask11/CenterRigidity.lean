import RequestProject.Experiment2.NullSectorTask11.SafeBase

/-!
# Task 11, Layer 1: the exact center of the carrier (§9, §10)

Task 09 proved that the derived two-plane `Z = spanℝ{1, S}` is *contained* in
the center.  Nothing so far excluded a larger center.  This module settles the
question intrinsically, using only the independently derived basis and
multiplication table: **the center is exactly `Z`**, and the smallest subset of
the derived generating data that already forces this is the pair `{A, B}`.

The negative control of §10 is included: the centralizer of the single generator
`A` is strictly larger (it contains `A` itself, and `A ∉ Z`), so no single
generator suffices; and the centralizer of the old generating *triple*
`{A, B, C}` coincides with the full center.

No conventional identification, no matrix, no complex scalar is used.
-/

namespace NullSectorTask11

open NullSectorTask08 NullSectorTask09 NullSectorTask10

/-! ## The intrinsic definitions -/

/-- **DERIVED (intrinsic).**  The center of the carrier. -/
def CenterW : Set W := {z : W | ∀ x : W, z ⋆ x = x ⋆ z}

/-- **DERIVED (intrinsic).**  The centralizer of a set of elements. -/
def CentralizerOf (T : Set W) : Set W := {z : W | ∀ x ∈ T, z ⋆ x = x ⋆ z}

theorem mem_CenterW {z : W} : z ∈ CenterW ↔ ∀ x : W, z ⋆ x = x ⋆ z := Iff.rfl

/-! ## Step 1 — commutation with `A` -/

/-- Commuting with the distinguished axis `A` kills the four coordinates
`B, C, P, Q`. -/
theorem coords_of_comm_wA {z : W} (h : z ⋆ wA = wA ⋆ z) :
    z 2 = 0 ∧ z 3 = 0 ∧ z 4 = 0 ∧ z 5 = 0 := by
  have h2 := congrFun h 4
  have h3 := congrFun h 5
  have h4 := congrFun h 2
  have h5 := congrFun h 3
  simp [wA] at h2 h3 h4 h5
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## Step 2 — commutation with `B` -/

/-- Commuting with the second generator `B` kills the two coordinates `A, R`,
once the four coordinates of Step 1 are already known to vanish. -/
theorem coords_of_comm_wB {z : W} (h : z ⋆ wB = wB ⋆ z)
    (h2 : z 2 = 0) (h4 : z 4 = 0) (h5 : z 5 = 0) :
    z 1 = 0 ∧ z 6 = 0 := by
  have e4 := congrFun h 4
  have e3 := congrFun h 3
  simp [wB, h2, h4, h5] at e4 e3
  exact ⟨by linarith, by linarith⟩

/-! ## Step 3 — the exact center -/

/-- **THE EXACT CENTER THEOREM (§9).**  The center of the reconstructed carrier
is exactly the derived central two-plane `Z = spanℝ{1, S}`.  Only commutation
with the two derived generators `A` and `B` is used in the forward direction. -/
theorem center_eq_Z : CenterW = (Z : Set W) := by
  ext z
  constructor
  · intro hz
    obtain ⟨h2, h3, h4, h5⟩ := coords_of_comm_wA (hz wA)
    obtain ⟨h1, h6⟩ := coords_of_comm_wB (hz wB) h2 h4 h5
    have : z = zc (z 0) (z 7) := by
      funext i
      fin_cases i <;> simp [zc, w1, wS, h1, h2, h3, h4, h5, h6]
    rw [this]
    exact zc_mem_Z _ _
  · intro hz x
    exact Z_central hz x

/-- **THE EXACT CENTER, IN NORMAL FORM.** -/
theorem mem_center_iff (z : W) : z ∈ CenterW ↔ ∃ a b : ℝ, z = zc a b := by
  rw [show z ∈ CenterW ↔ z ∈ (Z : Set W) from by rw [center_eq_Z]]
  constructor
  · intro hz; exact ⟨z 0, z 7, eq_zc_of_mem_Z hz⟩
  · rintro ⟨a, b, rfl⟩; exact zc_mem_Z a b

/-- **THE SMALLEST GENERATING SUBSET ACTUALLY NEEDED (§9).**  Commutation with
the two elements `A` and `B` alone already forces membership in `Z`. -/
theorem centralizer_pair_eq_Z : CentralizerOf {wA, wB} = (Z : Set W) := by
  ext z
  constructor
  · intro hz
    have hA : z ⋆ wA = wA ⋆ z := hz wA (by simp)
    have hB : z ⋆ wB = wB ⋆ z := hz wB (by simp)
    obtain ⟨h2, h3, h4, h5⟩ := coords_of_comm_wA hA
    obtain ⟨h1, h6⟩ := coords_of_comm_wB hB h2 h4 h5
    have : z = zc (z 0) (z 7) := by
      funext i
      fin_cases i <;> simp [zc, w1, wS, h1, h2, h3, h4, h5, h6]
    rw [this]
    exact zc_mem_Z _ _
  · intro hz x _
    exact Z_central hz x

/-- **THE CENTRALIZER OF THE OLD GENERATING TRIPLE (§10).**  It is *already* the
full center: adjoining `C` to `{A, B}` adds no constraint. -/
theorem centralizer_triple_eq_center : CentralizerOf {wA, wB, wC} = CenterW := by
  rw [center_eq_Z]
  ext z
  constructor
  · intro hz
    have hz' : z ∈ CentralizerOf {wA, wB} := by
      intro x hx
      rcases hx with hx | hx <;> subst hx
      · exact hz wA (by simp)
      · exact hz wB (by simp)
    rwa [centralizer_pair_eq_Z] at hz'
  · intro hz x _
    exact Z_central hz x

/-! ## Negative control: one generator is not enough -/

/-- **NEGATIVE CONTROL (§10).**  The centralizer of the single distinguished
generator `A` is strictly larger than the center: it contains `A`, which is not
central. -/
theorem centralizer_single_ne_center : CentralizerOf {wA} ≠ CenterW := by
  intro h
  have hmem : wA ∈ CentralizerOf {wA} := by
    intro x hx
    rcases hx with hx
    subst hx
    rfl
  rw [h, center_eq_Z] at hmem
  have := eq_zc_of_mem_Z hmem
  have h1 := congrFun this 1
  simp [wA] at h1

/-- The two remaining derived channels `P, Q, R` are *not* central; the
two-plane really is the whole center. -/
theorem wR_not_mem_center : wR ∉ CenterW := by
  intro h
  rw [center_eq_Z] at h
  have := eq_zc_of_mem_Z h
  have h6 := congrFun this 6
  simp [wR] at h6

end NullSectorTask11
