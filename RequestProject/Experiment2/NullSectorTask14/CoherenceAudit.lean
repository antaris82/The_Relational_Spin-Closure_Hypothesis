import RequestProject.Experiment2.NullSectorTask14.FullLiftDefect

/-!
# Task 14, Layer 16 (§49–§54): coherence, composition defect, closed paths, path dependence

This module settles the central coherence question:

* **§49** is there an internal implementer assigned to *every* implementable algebra
  automorphism which is exactly multiplicative?  **No** — `coherent_lift_obstructed`;
* **§50** the exact composition defect of the reference section is a *central* element,
  and for reference words it is confined to `{1, -1}` (§46), so the obstruction is a sign,
  computed algebraically from finite compositions only;
* **§52** an explicit closed mixed path whose induced algebra automorphism is the identity
  while its internal implementation is `-1`;
* **§53** two explicitly different paths to the same automorphism whose reference
  implementations differ by `-1`: verdict **PATH DEPENDENT**;
* **§54** the three notions of closure are kept apart and each is given its own theorem.

The obstruction is derived here from the two independently reconstructed axis systems and
their finite compositions.  No topology, covering space or extension theory is used.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## The two half-parameter basis-axis implementations -/

/-- **NEUTRAL DEFINITION.**  The first inherited old spatial basis direction as a unit
axis. -/
def axA : Vec3 := (1, 0, 0)

/-- **NEUTRAL DEFINITION.**  The second inherited old spatial basis direction. -/
def axB : Vec3 := (0, 1, 0)

theorem axA_unit : IsUnitAxis axA := by simp [IsUnitAxis, h3, axA]

theorem axB_unit : IsUnitAxis axB := by simp [IsUnitAxis, h3, axB]

theorem axA_axB_orthogonal : h3 axA axB = 0 := by simp [h3, axA, axB]

/-- **DERIVED.**  At the half-turn parameter the reference implementation is exactly minus
the derived generator direction. -/
theorem Un_pi (n : Vec3) : Un n Real.pi = -Jmap n := by
  rw [Un, show Real.pi / 2 = Real.pi / 2 from rfl, Real.cos_pi_div_two, Real.sin_pi_div_two]
  module

theorem Un_neg_pi (n : Vec3) : Un n (-Real.pi) = Jmap n := by
  rw [Un_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  module

/-- **DERIVED.**  Generator directions of orthogonal axes anticommute. -/
theorem Jmap_anticomm {n m : Vec3} (h : h3 n m = 0) :
    Jmap n ⋆ Jmap m = -(Jmap m ⋆ Jmap n) := by
  have := Jmap_symmetric_product n m
  rw [h] at this
  have h0 : ((-(2 * (0 : ℝ))) • w1 : W) = 0 := by module
  rw [h0] at this
  linear_combination (norm := module) this

/-- **PRINCIPAL THEOREM (§52), algebraic core.**  Any two implementers of the two
orthogonal half-turn automorphisms **anticommute** — whatever central residuals they
carry.  This uses only the exact-center theorem and the derived generator relations. -/
theorem half_turn_implementers_anticommute {u ui v vi : W}
    (hu : Implements u ui (PhiGen axA Real.pi)) (hv : Implements v vi (PhiGen axB Real.pi)) :
    u ⋆ v = -(v ⋆ u) := by
  obtain ⟨z, zi, hz, _, _, rfl⟩ := (axis_lift_iff axA_unit Real.pi u).1 ⟨ui, hu⟩
  obtain ⟨z', zi', hz', _, _, rfl⟩ := (axis_lift_iff axB_unit Real.pi v).1 ⟨vi, hv⟩
  have hbase : Un axA Real.pi ⋆ Un axB Real.pi = -(Un axB Real.pi ⋆ Un axA Real.pi) := by
    rw [Un_pi, Un_pi, neg_mul_W, mul_neg_W, neg_mul_W, mul_neg_W, neg_neg, neg_neg,
      Jmap_anticomm axA_axB_orthogonal]
  have hzz : ∀ x y : W, (z ⋆ x) ⋆ (z' ⋆ y) = (z ⋆ z') ⋆ (x ⋆ y) := by
    intro x y
    calc (z ⋆ x) ⋆ (z' ⋆ y) = z ⋆ ((x ⋆ z') ⋆ y) := by simp only [mul_assoc_W]
      _ = z ⋆ ((z' ⋆ x) ⋆ y) := by rw [Z_central hz' x]
      _ = (z ⋆ z') ⋆ (x ⋆ y) := by simp only [mul_assoc_W]
  have hzz' : ∀ x y : W, (z' ⋆ x) ⋆ (z ⋆ y) = (z ⋆ z') ⋆ (x ⋆ y) := by
    intro x y
    calc (z' ⋆ x) ⋆ (z ⋆ y) = z' ⋆ ((x ⋆ z) ⋆ y) := by simp only [mul_assoc_W]
      _ = z' ⋆ ((z ⋆ x) ⋆ y) := by rw [Z_central hz x]
      _ = (z' ⋆ z) ⋆ (x ⋆ y) := by simp only [mul_assoc_W]
      _ = (z ⋆ z') ⋆ (x ⋆ y) := by rw [Z_central hz z']
  rw [hzz, hzz', hbase, mul_neg_W]

/-- **DERIVED (§24, algebraically).**  The two orthogonal half-turn *automorphisms* do
commute — the internal anticommutation is invisible at the automorphism level because the
sign is central. -/
theorem half_turn_automorphisms_commute :
    (PhiGen axA Real.pi).comp (PhiGen axB Real.pi)
      = (PhiGen axB Real.pi).comp (PhiGen axA Real.pi) := by
  refine LinearMap.ext (fun x => ?_)
  have ha : Un axA Real.pi = -Jmap axA := Un_pi axA
  have hb : Un axB Real.pi = -Jmap axB := Un_pi axB
  have ha' : Un axA (-Real.pi) = Jmap axA := Un_neg_pi axA
  have hb' : Un axB (-Real.pi) = Jmap axB := Un_neg_pi axB
  have hanti : Jmap axA ⋆ Jmap axB = -(Jmap axB ⋆ Jmap axA) := Jmap_anticomm axA_axB_orthogonal
  show ((Un axA Real.pi ⋆ ((Un axB Real.pi ⋆ x) ⋆ Un axB (-Real.pi))) ⋆ Un axA (-Real.pi))
      = ((Un axB Real.pi ⋆ ((Un axA Real.pi ⋆ x) ⋆ Un axA (-Real.pi))) ⋆ Un axB (-Real.pi))
  rw [ha, hb, ha', hb']
  have expand : ∀ p q : W,
      ((-p) ⋆ (((-q) ⋆ x) ⋆ q)) ⋆ p = ((p ⋆ q) ⋆ x) ⋆ (q ⋆ p) := by
    intro p q
    simp only [neg_mul_W, mul_neg_W, neg_neg]
    simp only [mul_assoc_W]
  rw [expand (Jmap axA) (Jmap axB), expand (Jmap axB) (Jmap axA), hanti]
  simp only [neg_mul_W, mul_neg_W, neg_neg]

/-! ## §49 — the coherent-lift question -/

/-- **NEUTRAL DEFINITION (§49).**  The algebra automorphisms admitting an internal
implementation.  The family is closed under composition (`Implements.mul`). -/
def IsImplementable (g : W →ₗ[ℝ] W) : Prop := ∃ u ui : W, Implements u ui g

theorem isImplementable_comp {g h : W →ₗ[ℝ] W} (hg : IsImplementable g)
    (hh : IsImplementable h) : IsImplementable (g.comp h) := by
  obtain ⟨u, ui, hu⟩ := hg
  obtain ⟨v, vi, hv⟩ := hh
  exact ⟨u ⋆ v, vi ⋆ ui, Implements.mul hu hv⟩

theorem isImplementable_PhiGen {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    IsImplementable (PhiGen n θ) := ⟨_, _, Un_implements hn θ⟩

theorem w1_ne_zero : (w1 : W) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [w1] at this

/-- **DERIVED.**  An implemented element is never zero. -/
theorem implements_ne_zero {u ui : W} {F : W →ₗ[ℝ] W} (h : Implements u ui F) : u ≠ 0 := by
  intro hu
  have : (w1 : W) = 0 := by
    rw [← h.inv_right, hu]
    exact zero_mul_W ui
  exact w1_ne_zero this

/-- **PRINCIPAL THEOREM (§49): `coherent_lift_exists_or_obstructed`, verdict
**OBSTRUCTED**.**  There is *no* assignment of internal implementers to implementable
algebra automorphisms which is exactly multiplicative.  The obstruction is derived from
the two independently reconstructed axis systems: their half-turn automorphisms commute
while *all* of their internal implementations anticommute. -/
theorem coherent_lift_obstructed :
    ¬ ∃ U Ui : (W →ₗ[ℝ] W) → W,
        (∀ g : W →ₗ[ℝ] W, IsImplementable g → Implements (U g) (Ui g) g) ∧
        (∀ g h : W →ₗ[ℝ] W, IsImplementable g → IsImplementable h →
          U (g.comp h) = U g ⋆ U h) := by
  rintro ⟨U, Ui, himpl, hmul⟩
  set gA := PhiGen axA Real.pi with hgA
  set gB := PhiGen axB Real.pi with hgB
  have hAi : IsImplementable gA := isImplementable_PhiGen axA_unit Real.pi
  have hBi : IsImplementable gB := isImplementable_PhiGen axB_unit Real.pi
  have hcomm : U gA ⋆ U gB = U gB ⋆ U gA := by
    rw [← hmul gA gB hAi hBi, ← hmul gB gA hBi hAi, half_turn_automorphisms_commute]
  have hanti : U gA ⋆ U gB = -(U gB ⋆ U gA) :=
    half_turn_implementers_anticommute (himpl gA hAi) (himpl gB hBi)
  have hzero : U gA ⋆ U gB = 0 := by
    have : (2 : ℝ) • (U gA ⋆ U gB) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hcomm]
      rw [hanti]
      module
    have h2 := congrArg (fun y : W => (2⁻¹ : ℝ) • y) this
    simpa using h2
  -- but the product of two implementers is itself an implementer, hence nonzero
  have himplAB : Implements (U gA ⋆ U gB) (Ui gB ⋆ Ui gA) (gA.comp gB) :=
    Implements.mul (himpl gA hAi) (himpl gB hBi)
  exact implements_ne_zero himplAB hzero

/-! ## §50 — the exact composition defect of the reference section -/

/-- **PRINCIPAL THEOREM (§50).**  For the reference section, words compose *strictly*
along concatenation, so the composition defect can only appear between two different words
inducing the *same* automorphism — where §46 already computed it to be `±1`. -/
theorem wordVal_append (l l' : AxisWord) :
    wordVal (l ++ l') = wordVal l ⋆ wordVal l' := by
  induction l with
  | nil => rw [List.nil_append, wordVal_nil, one_mul_W]
  | cons p t ih =>
      show Un p.1 p.2 ⋆ wordVal (t ++ l') = (Un p.1 p.2 ⋆ wordVal t) ⋆ wordVal l'
      rw [ih, mul_assoc_W]

theorem wordAut_append (l l' : AxisWord) :
    wordAut (l ++ l') = (wordAut l).comp (wordAut l') := by
  induction l with
  | nil => rw [List.nil_append, wordAut_nil, LinearMap.id_comp]
  | cons p t ih =>
      show (PhiGen p.1 p.2).comp (wordAut (t ++ l'))
        = ((PhiGen p.1 p.2).comp (wordAut t)).comp (wordAut l')
      rw [ih, LinearMap.comp_assoc]

/-! ## §52 — an explicit closed mixed path -/

/-- **NEUTRAL DEFINITION (§52).**  The explicit closed mixed path: two orthogonal
half-turns, twice. -/
noncomputable def closedPath : AxisWord :=
  [(axA, Real.pi), (axB, Real.pi), (axA, Real.pi), (axB, Real.pi)]

theorem closedPath_unit : IsUnitWord closedPath := by
  intro p hp
  simp only [closedPath, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact axA_unit
  · exact axB_unit
  · exact axA_unit
  · exact axB_unit

theorem closedPath_val : wordVal closedPath = -w1 := by
  show Un axA Real.pi ⋆ (Un axB Real.pi ⋆ (Un axA Real.pi ⋆ (Un axB Real.pi ⋆ wordVal []))) = -w1
  rw [wordVal_nil, Un_pi, Un_pi, mul_one_W]
  funext i
  fin_cases i <;> simp [Jmap, axA, axB, w1, wP, wQ, wR, wit8MulFun] <;> ring

theorem closedPath_inv : wordInv closedPath = -w1 := by
  show ((((wordInv []) ⋆ Un axB (-Real.pi)) ⋆ Un axA (-Real.pi)) ⋆ Un axB (-Real.pi))
      ⋆ Un axA (-Real.pi) = -w1
  rw [wordInv_nil, Un_neg_pi, Un_neg_pi, one_mul_W]
  funext i
  fin_cases i <;> simp [Jmap, axA, axB, w1, wP, wQ, wR, wit8MulFun] <;> ring

/-- **PRINCIPAL THEOREM (§52).**  The closed mixed path induces the *identity* algebra
automorphism while its internal reference implementation is `-1`.  The central residual of
a closed path is therefore genuinely nontrivial and is not quotiented away. -/
theorem closed_path_internal_residual :
    wordAut closedPath = LinearMap.id ∧ wordVal closedPath = -w1 := by
  refine ⟨?_, closedPath_val⟩
  have h := word_implements closedPath_unit
  refine LinearMap.ext (fun x => ?_)
  rw [← h.conj x, closedPath_val, closedPath_inv, neg_mul_W, neg_mul_W, mul_neg_W,
    neg_neg, one_mul_W, mul_one_W]
  rfl

/-! ## §53 — path independence -/

/-- **PRINCIPAL THEOREM (§53): verdict **PATH DEPENDENT** (with defect exactly `-1`).**
Two explicitly different reference paths induce the same algebra automorphism — the
identity — while their internal implementations differ by `-1`. -/
theorem path_dependence_explicit :
    wordAut closedPath = wordAut ([] : AxisWord) ∧
      wordVal closedPath = -w1 ∧ wordVal ([] : AxisWord) = w1 ∧
      wordVal closedPath ⋆ wordInv ([] : AxisWord) = -w1 := by
  refine ⟨(closed_path_internal_residual).1, closedPath_val, wordVal_nil, ?_⟩
  rw [wordInv_nil, mul_one_W, closedPath_val]

/-! ## §54 — the three notions of closure, kept separate -/

/-- **PRINCIPAL THEOREM (§54).**  The three closure statements, each with its own content:

* **A** the implementable algebra automorphisms are closed under composition;
* **B** the reference internal implementations are closed: a product of two of them *is*
  a reference implementation of a single derived axis;
* **C** arbitrary full implementations close only up to a central factor, which is exactly
  the residual freedom classified in §47.

A positive answer for one is *not* used to obtain another. -/
theorem three_closure_notions :
    (∀ g h : W →ₗ[ℝ] W, IsImplementable g → IsImplementable h →
        IsImplementable (g.comp h)) ∧
      (∀ (n m : Vec3), IsUnitAxis n → IsUnitAxis m → ∀ θ φ : ℝ,
        ∃ (k : Vec3) (ψ : ℝ), IsUnitAxis k ∧ Un n θ ⋆ Un m φ = Un k ψ) ∧
      (∀ (a b c d : ℝ) (n m : Vec3) (θ φ : ℝ),
        (zz a b ⋆ Un n θ) ⋆ (zz c d ⋆ Un m φ)
          = (zz a b ⋆ zz c d) ⋆ (Un n θ ⋆ Un m φ)) :=
  ⟨fun _ _ hg hh => isImplementable_comp hg hh,
    fun _ _ hn hm θ φ => generic_reference_composition_closes hn hm θ φ,
    fun a b c d n m θ φ => mixed_full_lift_product a b c d n m θ φ⟩

end NullSectorTask14
