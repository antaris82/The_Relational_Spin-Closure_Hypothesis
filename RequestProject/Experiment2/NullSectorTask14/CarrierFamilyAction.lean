import RequestProject.Experiment2.NullSectorTask14.CarrierIntertwiners

/-!
# Task 14, Layer 18 (§57–§58): the induced action on the carrier family

The Task-13 sphere parametrization of the minimal-carrier family is used here only as an
already proved coordinate theorem.  The action of the *independently reconstructed*
second-axis automorphism — and of every generic axis automorphism — on those coordinates
is **derived**, not assumed to be a sphere transformation:

* `conj_spat_raw` is a constraint-free algebraic identity inside the carrier;
* `PhiGen_spat` specializes it to a unit axis and yields the exact coordinate action
  `rotv`;
* `rotv_preserves_form` shows the derived coordinate action preserves the inherited
  spatial form, so it maps the sphere family to itself;
* `generic_carrier_family_action` transports this to the carriers themselves;
* `secondAxis_carrier_family_action` is the explicit second-axis case;
* `mixed_carrier_family_action` composes the two independently reconstructed actions.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## The constraint-free conjugation identity -/

/-- **DERIVED.**  The conjugate of an old spatial element by an arbitrary element of the
derived two-plane `span {1, J(n)}`, with *no* normalization assumed on either the
coefficients or the axis. -/
theorem conj_spat_raw (c s : ℝ) (n p : Vec3) :
    ((c • w1 - s • Jmap n) ⋆ spat p) ⋆ (c • w1 + s • Jmap n)
      = spat ((c ^ 2 - s ^ 2 * h3 n n) • p + (2 * c * s) • spCross n p
          + (2 * s ^ 2 * h3 n p) • n) := by
  funext i
  fin_cases i <;>
    simp [Jmap, spCross, h3, w1, wP, wQ, wR, wit8MulFun, Prod.smul_def] <;> ring

/-- **NEUTRAL DEFINITION (§57).**  The derived coordinate action of an axis automorphism on
old spatial directions.  It is *read off* from `conj_spat_raw`, not imported. -/
noncomputable def rotv (n : Vec3) (θ : ℝ) (p : Vec3) : Vec3 :=
  (Real.cos θ) • p + (Real.sin θ) • spCross n p + ((1 - Real.cos θ) * h3 n p) • n

/-- **PRINCIPAL THEOREM (§57).**  The exact action of a generic axis automorphism on the
inherited old spatial subspace.  The half-angle coefficients of the internal implementer
combine into the whole-parameter coefficients of `rotv`; the two hyperbolic-free identities
used are the standard double-parameter identities for `Real.sin` and `Real.cos`. -/
theorem PhiGen_spat {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) (p : Vec3) :
    PhiGen n θ (spat p) = spat (rotv n θ p) := by
  have hpy := Real.sin_sq_add_cos_sq (θ / 2)
  have hcos : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_two_mul' (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    linarith
  have hsin : Real.sin θ = 2 * Real.cos (θ / 2) * Real.sin (θ / 2) := by
    have h := Real.sin_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    linarith
  have hone : 1 - (Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2)
      = 2 * Real.sin (θ / 2) ^ 2 := by linarith
  rw [PhiGen_apply, Un, Un_neg, conj_spat_raw, hn, rotv, hcos, hsin, hone]
  congr 1
  module

/-- **DERIVED (§57).**  The derived coordinate action preserves the inherited spatial
form; the proof uses only multiplicativity of the automorphism and the inherited square
relation of old spatial elements. -/
theorem rotv_preserves_form {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) (p : Vec3) :
    h3 (rotv n θ p) (rotv n θ p) = h3 p p := by
  have h1 : spat (rotv n θ p) ⋆ spat (rotv n θ p) = (h3 p p) • w1 := by
    rw [← PhiGen_spat hn, ← PhiGen_mul hn, spat_sq, map_smul, PhiGen_unital hn]
  rw [spat_sq] at h1
  have h0 := congrFun h1 0
  simpa [w1] using h0

/-- **DERIVED.**  The derived coordinate action fixes its own axis, in both signs. -/
theorem rotv_axis {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) : rotv n θ n = n := by
  have hc : spCross n n = 0 := spCross_basis.2.2.2 n
  rw [rotv, hc, hn]
  module

theorem rotv_neg_axis {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) : rotv n θ (-n) = -n := by
  have hc : spCross n (-n) = 0 := by
    simp only [spCross]
    have := spCross_basis.2.2.2 n
    simp only [spCross] at this
    have h1 := congrArg (fun v : Vec3 => v.1) this
    have h2 := congrArg (fun v : Vec3 => v.2.1) this
    have h3' := congrArg (fun v : Vec3 => v.2.2) this
    simp at h1 h2 h3'
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> linarith
  have hh : h3 n (-n) = -1 := by
    have : h3 n (-n) = -h3 n n := by simp [h3]; ring
    rw [this, hn]
  rw [rotv, hc, hh]
  module

/-! ## The sphere parametrization in vector notation -/

/-- **NEUTRAL NOTATION.**  The Task-13 sphere point written with a spatial vector. -/
noncomputable def esphv (p : Vec3) : W := esph p.1 p.2.1 p.2.2

theorem esphv_eq (p : Vec3) : esphv p = (2⁻¹ : ℝ) • (w1 + spat p) := by
  funext i
  fin_cases i <;>
    simp [esphv, esph, w1, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- **DERIVED (§57).**  The generic axis automorphism acts on sphere points exactly by the
derived coordinate action. -/
theorem PhiGen_esphv {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) (p : Vec3) :
    PhiGen n θ (esphv p) = esphv (rotv n θ p) := by
  rw [esphv_eq, esphv_eq, map_smul, map_add, PhiGen_unital hn, PhiGen_spat hn]

/-! ## Transport to the carrier family -/

theorem PhiGen_zero (n : Vec3) (x : W) : PhiGen n 0 x = x := by
  rw [PhiGen_apply, Un_zero, neg_zero, Un_zero, one_mul_W, mul_one_W]

theorem PhiGen_surjective {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    Function.Surjective (PhiGen n θ) := by
  intro x
  refine ⟨PhiGen n (-θ) x, ?_⟩
  have := PhiGen_group hn θ (-θ) x
  rw [add_neg_cancel, PhiGen_zero] at this
  exact this.symm

/-- **DERIVED (§57).**  The image of a generated carrier is the carrier generated by the
image. -/
theorem PhiGen_map_Lgen {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) (ψ : W) :
    Submodule.map (PhiGen n θ) (Lgen ψ) = Lgen (PhiGen n θ ψ) := by
  ext y
  simp only [Submodule.mem_map, mem_Lgen_iff]
  constructor
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    exact ⟨PhiGen n θ x, (PhiGen_mul hn θ x ψ).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨x', rfl⟩ := PhiGen_surjective hn θ x
    exact ⟨x' ⋆ ψ, ⟨x', rfl⟩, PhiGen_mul hn θ x' ψ⟩

/-- **PRINCIPAL THEOREM (§57): `second_axis_carrier_family_action`, generic form.**  On the
Task-13 sphere parametrization of the minimal-carrier family, every independently
reconstructed axis automorphism acts by the derived coordinate action `rotv`.  This is
*derived*; it was not assumed that the action is a sphere transformation. -/
theorem generic_carrier_family_action {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) (p : Vec3) :
    Submodule.map (PhiGen n θ) (Lgen (esphv p)) = Lgen (esphv (rotv n θ p)) := by
  rw [PhiGen_map_Lgen hn, PhiGen_esphv hn]

/-- **PRINCIPAL THEOREM (§57), the explicit second-axis case.**  The independently
reconstructed second-axis automorphism acts on the sphere coordinates by

`(p₁,p₂,p₃) ↦ (cos φ · p₁ + sin φ · p₃, p₂, cos φ · p₃ − sin φ · p₁)`. -/
theorem secondAxis_carrier_family_action (φ : ℝ) (p : Vec3) :
    Submodule.map (PhiGen axB φ) (Lgen (esphv p))
      = Lgen (esphv (Real.cos φ * p.1 + Real.sin φ * p.2.2, p.2.1,
          Real.cos φ * p.2.2 - Real.sin φ * p.1)) := by
  have hv : rotv axB φ p = (Real.cos φ * p.1 + Real.sin φ * p.2.2, p.2.1,
      Real.cos φ * p.2.2 - Real.sin φ * p.1) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp [rotv, axB, spCross, h3] <;> ring
  rw [generic_carrier_family_action axB_unit, hv]

/-- **PRINCIPAL THEOREM (§58).**  The two independently reconstructed axis actions compose
on the carrier family exactly by composing their derived coordinate actions. -/
theorem mixed_carrier_family_action {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m)
    (θ φ : ℝ) (p : Vec3) :
    Submodule.map (PhiGen n θ) (Submodule.map (PhiGen m φ) (Lgen (esphv p)))
      = Lgen (esphv (rotv n θ (rotv m φ p))) := by
  rw [generic_carrier_family_action hm, generic_carrier_family_action hn]

end NullSectorTask14
