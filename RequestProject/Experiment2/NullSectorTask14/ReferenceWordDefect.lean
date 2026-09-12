import RequestProject.Experiment2.NullSectorTask14.GenericTwoAxisComposition

/-!
# Task 14, Layer 14 (§44–§46): words of axis implementations and their central defect

This module treats *words* — finite ordered products of the independently derived axis
reference implementations — and answers two separate questions:

* **§44** conjugation by a word induces exactly the composition of the corresponding
  inherited algebra automorphisms;
* **§45** if two internal elements implement the *same* algebra automorphism, their
  relative factor is forced to lie in the exact center `Z` (the Task-11 theorem
  `center_eq_Z` is the only external input);
* **§46** for words built from the *reference* axis implementations the defect set is
  computed exactly: it is `{1, -1}`, and both values occur.

No defect is normalized away and no quotient is taken.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## §44 — internal implementations of an algebra automorphism -/

/-- **NEUTRAL DEFINITION (§44).**  `u` implements the linear map `F` by conjugation, with
`ui` a two-sided inverse.  No normalization, no subspace, no continuity. -/
structure Implements (u ui : W) (F : W →ₗ[ℝ] W) : Prop where
  /-- Right inverse relation. -/
  inv_right : u ⋆ ui = w1
  /-- Left inverse relation. -/
  inv_left : ui ⋆ u = w1
  /-- The conjugation action. -/
  conj : ∀ x : W, (u ⋆ x) ⋆ ui = F x

/-- **DERIVED (§44).**  An implementer intertwines left multiplication. -/
theorem Implements.intertwine {u ui : W} {F : W →ₗ[ℝ] W} (h : Implements u ui F) (y : W) :
    u ⋆ y = F y ⋆ u := by
  calc u ⋆ y = ((u ⋆ y) ⋆ ui) ⋆ u := by
        rw [mul_assoc_W (u ⋆ y) ui u, h.inv_left, mul_one_W]
    _ = F y ⋆ u := by rw [h.conj]

/-- **DERIVED (§44).**  The inverse intertwines in the opposite direction. -/
theorem Implements.intertwine_inv {u ui : W} {F : W →ₗ[ℝ] W} (h : Implements u ui F) (y : W) :
    ui ⋆ F y = y ⋆ ui := by
  calc ui ⋆ F y = ui ⋆ ((u ⋆ y) ⋆ ui) := by rw [h.conj]
    _ = ((ui ⋆ u) ⋆ y) ⋆ ui := by simp only [mul_assoc_W]
    _ = y ⋆ ui := by rw [h.inv_left, one_mul_W]

/-- **DERIVED (§44).**  Every element of the carrier is in the image of an implemented
map. -/
theorem Implements.surjective {u ui : W} {F : W →ₗ[ℝ] W} (h : Implements u ui F) (x : W) :
    F (ui ⋆ (x ⋆ u)) = x := by
  rw [← h.conj]
  calc (u ⋆ (ui ⋆ (x ⋆ u))) ⋆ ui = (((u ⋆ ui) ⋆ x) ⋆ u) ⋆ ui := by simp only [mul_assoc_W]
    _ = x := by rw [h.inv_right, one_mul_W, mul_assoc_W, h.inv_right, mul_one_W]

/-- **PRINCIPAL THEOREM (§44).**  Conjugation by a product of implementations is the
composition of the implemented maps: internal words map onto automorphism words. -/
theorem Implements.mul {u ui v vi : W} {F G : W →ₗ[ℝ] W}
    (hu : Implements u ui F) (hv : Implements v vi G) :
    Implements (u ⋆ v) (vi ⋆ ui) (F.comp G) where
  inv_right := by
    calc (u ⋆ v) ⋆ (vi ⋆ ui) = (u ⋆ (v ⋆ vi)) ⋆ ui := by simp only [mul_assoc_W]
      _ = w1 := by rw [hv.inv_right, mul_one_W, hu.inv_right]
  inv_left := by
    calc (vi ⋆ ui) ⋆ (u ⋆ v) = (vi ⋆ (ui ⋆ u)) ⋆ v := by simp only [mul_assoc_W]
      _ = w1 := by rw [hu.inv_left, mul_one_W, hv.inv_left]
  conj := by
    intro x
    calc ((u ⋆ v) ⋆ x) ⋆ (vi ⋆ ui) = (u ⋆ ((v ⋆ x) ⋆ vi)) ⋆ ui :=
          conj_assoc_helper u v x vi ui
      _ = F.comp G x := by rw [hv.conj, hu.conj]; rfl

/-! ## §45 — the central word-defect theorem -/

/-- **PRINCIPAL THEOREM (§45): `reference_word_relative_central`.**  Two internal
implementations of the *same* algebra automorphism differ by a factor lying in the **exact
center** `Z`.  The Task-11 exact-center theorem is used explicitly here; nothing else is
assumed, in particular no normalization of `u` or `v`. -/
theorem implements_defect_mem_Z {u ui v vi : W} {F : W →ₗ[ℝ] W}
    (hu : Implements u ui F) (hv : Implements v vi F) : u ⋆ vi ∈ Z := by
  refine mem_Z_of_comm_all (fun x => ?_)
  obtain ⟨y, rfl⟩ : ∃ y : W, F y = x := ⟨ui ⋆ (x ⋆ u), hu.surjective x⟩
  calc (u ⋆ vi) ⋆ F y = u ⋆ (vi ⋆ F y) := mul_assoc_W _ _ _
    _ = u ⋆ (y ⋆ vi) := by rw [hv.intertwine_inv]
    _ = (u ⋆ y) ⋆ vi := (mul_assoc_W _ _ _).symm
    _ = (F y ⋆ u) ⋆ vi := by rw [hu.intertwine]
    _ = F y ⋆ (u ⋆ vi) := mul_assoc_W _ _ _

/-- **PRINCIPAL THEOREM (§45), explicit factorized form.**  `u = z ⋆ v` with `z ∈ Z`; the
central element is *not* normalized and need not be `±1` at this level of generality. -/
theorem implements_defect_factor {u ui v vi : W} {F : W →ₗ[ℝ] W}
    (hu : Implements u ui F) (hv : Implements v vi F) : ∃ z ∈ Z, u = z ⋆ v := by
  refine ⟨u ⋆ vi, implements_defect_mem_Z hu hv, ?_⟩
  rw [mul_assoc_W, hv.inv_left, mul_one_W]

/-! ## §46 — words of reference axis implementations -/

/-- **NEUTRAL DEFINITION (§46).**  A word is a finite list of (axis, parameter) pairs. -/
abbrev AxisWord : Type := List (Vec3 × ℝ)

/-- All axes occurring in a word are unit axes. -/
def IsUnitWord (l : AxisWord) : Prop := ∀ p ∈ l, IsUnitAxis p.1

/-- **NEUTRAL DEFINITION.**  The internal element of a reference word. -/
noncomputable def wordVal : AxisWord → W
  | [] => w1
  | p :: t => Un p.1 p.2 ⋆ wordVal t

/-- **NEUTRAL DEFINITION.**  The internal element of the reversed inverse word. -/
noncomputable def wordInv : AxisWord → W
  | [] => w1
  | p :: t => wordInv t ⋆ Un p.1 (-p.2)

/-- **NEUTRAL DEFINITION.**  The induced composition of inherited algebra
automorphisms. -/
noncomputable def wordAut : AxisWord → (W →ₗ[ℝ] W)
  | [] => LinearMap.id
  | p :: t => (PhiGen p.1 p.2).comp (wordAut t)

@[simp] theorem wordVal_nil : wordVal [] = w1 := rfl
@[simp] theorem wordInv_nil : wordInv [] = w1 := rfl
@[simp] theorem wordAut_nil : wordAut [] = LinearMap.id := rfl

/-- **DERIVED.**  A single reference implementation implements its automorphism. -/
theorem Un_implements {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    Implements (Un n θ) (Un n (-θ)) (PhiGen n θ) where
  inv_right := Un_mul_neg hn θ
  inv_left := Un_neg_mul hn θ
  conj := fun _ => rfl

/-- **PRINCIPAL THEOREM (§44) for reference words.**  Conjugation by a reference word is
exactly the corresponding composition of inherited algebra automorphisms. -/
theorem word_implements {l : AxisWord} (hl : IsUnitWord l) :
    Implements (wordVal l) (wordInv l) (wordAut l) := by
  induction l with
  | nil =>
      refine ⟨mul_one_W w1, mul_one_W w1, fun x => ?_⟩
      show (w1 ⋆ x) ⋆ w1 = x
      rw [one_mul_W, mul_one_W]
  | cons p t ih =>
      exact Implements.mul (Un_implements (hl p (by simp)) p.2)
        (ih (fun q hq => hl q (by simp [hq])))

theorem wordVal_mem_ImplAlg (l : AxisWord) : wordVal l ∈ ImplAlg := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons p t ih => exact ImplAlg_productClosed _ (Un_mem_ImplAlg p.1 p.2) _ ih

theorem wordInv_mem_ImplAlg (l : AxisWord) : wordInv l ∈ ImplAlg := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons p t ih => exact ImplAlg_productClosed _ ih _ (Un_mem_ImplAlg p.1 (-p.2))

theorem qnrm_w1 : qnrm w1 = 1 := by simp [qnrm, w1]

theorem qnrm_wordVal {l : AxisWord} (hl : IsUnitWord l) : qnrm (wordVal l) = 1 := by
  induction l with
  | nil => exact qnrm_w1
  | cons p t ih =>
      rw [wordVal, qnrm_mul (Un_mem_ImplAlg p.1 p.2) (wordVal_mem_ImplAlg t),
        qnrm_Un (hl p (by simp)), ih (fun q hq => hl q (by simp [hq])), one_mul]

theorem qnrm_wordInv {l : AxisWord} (hl : IsUnitWord l) : qnrm (wordInv l) = 1 := by
  induction l with
  | nil => exact qnrm_w1
  | cons p t ih =>
      rw [wordInv, qnrm_mul (wordInv_mem_ImplAlg t) (Un_mem_ImplAlg p.1 (-p.2)),
        qnrm_Un (hl p (by simp)), ih (fun q hq => hl q (by simp [hq])), one_mul]

/-! ### The exact intersection of the center with the implementer algebra -/

/-- **DERIVED.**  The exact center meets the minimal implementer algebra in the real line
through the unit only. -/
theorem Z_inter_ImplAlg {z : W} (hZ : z ∈ Z) (hI : z ∈ ImplAlg) : ∃ a : ℝ, z = a • w1 := by
  obtain ⟨a, b, hz⟩ := (mem_Z_iff z).1 hZ
  have hb : b = 0 := by
    have h7 : z 7 = 0 := hI.2.2.2
    rw [hz] at h7
    simpa [w1, wS] using h7
  exact ⟨a, by rw [hz, hb]; module⟩

/-- **PRINCIPAL THEOREM (§46): `reference_word_defect_classification`.**  If two reference
words induce the *same* algebra automorphism, their internal defect is exactly `+1` or
`-1`.  Nothing is normalized: the two values are the complete list of possibilities. -/
theorem reference_word_defect {l l' : AxisWord} (hl : IsUnitWord l) (hl' : IsUnitWord l')
    (h : wordAut l = wordAut l') :
    wordVal l ⋆ wordInv l' = w1 ∨ wordVal l ⋆ wordInv l' = -w1 := by
  have hu := word_implements hl
  have hv := word_implements hl'
  rw [h] at hu
  have hZ : wordVal l ⋆ wordInv l' ∈ Z := implements_defect_mem_Z hu hv
  have hI : wordVal l ⋆ wordInv l' ∈ ImplAlg :=
    ImplAlg_productClosed _ (wordVal_mem_ImplAlg l) _ (wordInv_mem_ImplAlg l')
  obtain ⟨a, ha⟩ := Z_inter_ImplAlg hZ hI
  have hn : qnrm (wordVal l ⋆ wordInv l') = 1 := by
    rw [qnrm_mul (wordVal_mem_ImplAlg l) (wordInv_mem_ImplAlg l'), qnrm_wordVal hl,
      qnrm_wordInv hl', one_mul]
  rw [ha] at hn
  have ha2 : a ^ 2 = 1 := by
    have : qnrm (a • w1) = a ^ 2 := by simp [qnrm, w1]
    rw [this] at hn; exact hn
  have hfac : (a - 1) * (a + 1) = 0 := by nlinarith [ha2]
  rcases mul_eq_zero.1 hfac with h1 | h1
  · left
    have : a = 1 := by linarith
    rw [ha, this, one_smul]
  · right
    have : a = -1 := by linarith
    rw [ha, this]; module

/-- **DERIVED.**  Both defect values are realized.  The `+1` case is trivial; the `-1`
case is realized by the full-parameter word on a single axis, whose induced automorphism
is the identity while its internal element is `-1`. -/
theorem full_turn_val {n : Vec3} : Un n (2 * Real.pi) = -w1 := by
  rw [Un, show 2 * Real.pi / 2 = Real.pi by ring, Real.cos_pi, Real.sin_pi]
  module

theorem full_turn_inv {n : Vec3} : Un n (-(2 * Real.pi)) = -w1 := by
  rw [Un_neg, show 2 * Real.pi / 2 = Real.pi by ring, Real.cos_pi, Real.sin_pi]
  module

theorem full_turn_aut (n : Vec3) : PhiGen n (2 * Real.pi) = LinearMap.id := by
  refine LinearMap.ext (fun x => ?_)
  show (Un n (2 * Real.pi) ⋆ x) ⋆ Un n (-(2 * Real.pi)) = x
  rw [full_turn_val, full_turn_inv, neg_mul_W, neg_mul_W, mul_neg_W, neg_neg,
    one_mul_W, mul_one_W]

/-- **PRINCIPAL THEOREM (§46), realization.**  There are two reference words inducing the
identical algebra automorphism whose internal defect is `-1`. -/
theorem reference_word_defect_minus_one_realized {n : Vec3} (hn : IsUnitAxis n) :
    IsUnitWord [(n, 2 * Real.pi)] ∧ IsUnitWord ([] : AxisWord) ∧
      wordAut [(n, 2 * Real.pi)] = wordAut ([] : AxisWord) ∧
      wordVal [(n, 2 * Real.pi)] ⋆ wordInv ([] : AxisWord) = -w1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact hn
  · intro p hp; simp at hp
  · show (PhiGen n (2 * Real.pi)).comp (wordAut []) = LinearMap.id
    rw [wordAut_nil, LinearMap.comp_id, full_turn_aut]
  · show (Un n (2 * Real.pi) ⋆ wordVal []) ⋆ wordInv [] = -w1
    rw [wordVal_nil, wordInv_nil, mul_one_W, mul_one_W, full_turn_val]

/-- **PRINCIPAL THEOREM (§46), the exact defect set.**  The reference-word defect set is
exactly `{1, -1}` — no smaller and no larger. -/
theorem reference_word_defect_set_exact :
    (∀ (l l' : AxisWord), IsUnitWord l → IsUnitWord l' → wordAut l = wordAut l' →
        wordVal l ⋆ wordInv l' = w1 ∨ wordVal l ⋆ wordInv l' = -w1) ∧
      (∃ l l' : AxisWord, IsUnitWord l ∧ IsUnitWord l' ∧ wordAut l = wordAut l' ∧
        wordVal l ⋆ wordInv l' = w1) ∧
      (∃ l l' : AxisWord, IsUnitWord l ∧ IsUnitWord l' ∧ wordAut l = wordAut l' ∧
        wordVal l ⋆ wordInv l' = -w1) := by
  have hunit : IsUnitAxis ((1 : ℝ), (0 : ℝ), (0 : ℝ)) := by
    simp [IsUnitAxis, h3]
  refine ⟨fun l l' hl hl' h => reference_word_defect hl hl' h, ⟨[], [], ?_, ?_, rfl, ?_⟩, ?_⟩
  · intro p hp; simp at hp
  · intro p hp; simp at hp
  · show w1 ⋆ w1 = w1
    rw [one_mul_W]
  · obtain ⟨h1, h2, h3, h4⟩ := reference_word_defect_minus_one_realized hunit
    exact ⟨_, _, h1, h2, h3, h4⟩

end NullSectorTask14
