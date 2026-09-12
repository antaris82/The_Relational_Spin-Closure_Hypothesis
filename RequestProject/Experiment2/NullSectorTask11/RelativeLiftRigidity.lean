import RequestProject.Experiment2.NullSectorTask11.FullLift

/-!
# Task 11, Layer 3: comparison of two arbitrary full lifts (§11, §12, §13, §14)

Two *arbitrary* full-carrier lifts `U, V` of the **same** inherited algebra
action `Phi` are compared.  Nothing is prescribed about the relative element: it
is simply defined as

```
rel U V θ := U θ ⋆ V (-θ),
```

and the commutation relations that follow from the two conjugation hypotheses
are computed.  Only then is the exact center theorem of Layer 1 invoked to
classify it.

The explicit Task-10 representative is **not** used anywhere in this module; the
whole layer is the "upper classification" demanded by §14, valid before any
existence witness is available.
-/

namespace NullSectorTask11

open NullSectorTask08 NullSectorTask09 NullSectorTask10

/-- Moving a central factor across a product. -/
theorem central_mul_move {c : W} (hc : ∀ x : W, c ⋆ x = x ⋆ c) (u v : W) :
    u ⋆ (c ⋆ v) = c ⋆ (u ⋆ v) := by
  rw [← mul_assoc_W, ← hc, mul_assoc_W]

/-! ## §11 — the neutral relative element -/

/-- **NEUTRAL RELATIVE ELEMENT (§11).**  No centrality, reality, positivity or
dimension is prescribed. -/
noncomputable def rel (U V : ℝ → W) (θ : ℝ) : W := U θ ⋆ V (-θ)

section Compare

variable {U V : ℝ → W} (hU : IsFullLift U) (hV : IsFullLift V)
include hU hV

/-- **DERIVED (§11).**  The relative element commutes with every element in the
image of `Phi θ` — this is exactly what the two conjugation hypotheses give,
before any classification. -/
theorem rel_comm_image (θ : ℝ) (x : W) :
    rel U V θ ⋆ Phi θ x = Phi θ x ⋆ rel U V θ := by
  have hl : rel U V θ ⋆ Phi θ x = U θ ⋆ (x ⋆ V (-θ)) := by
    rw [rel, ← hV.conj θ x]
    simp only [mul_assoc_W, hV.inv_cancel_left]
  have hr : Phi θ x ⋆ rel U V θ = U θ ⋆ (x ⋆ V (-θ)) := by
    rw [rel, ← hU.conj θ x]
    simp only [mul_assoc_W, hU.inv_cancel_left]
  rw [hl, hr]

/-- **DERIVED (§11–§12).**  Since `Phi θ` is surjective, the relative element
commutes with *everything*: it lies in the intrinsically defined center. -/
theorem rel_mem_center (θ : ℝ) : rel U V θ ∈ CenterW := by
  intro y
  obtain ⟨x, rfl⟩ := (Phi_bijective θ).2 y
  exact rel_comm_image hU hV θ x

/-- **EXACT POINTWISE RESIDUAL FREEDOM (§12).**  Any two full internal lifts of
the same algebra action differ pointwise by an element of the exactly classified
center, i.e. of the derived central two-plane — a two-dimensional real
subalgebra.  It is *not* assumed to be real, one-dimensional or positive; this
is what the proof yields. -/
theorem exists_central_factor (θ : ℝ) :
    ∃ a b : ℝ, U θ = zc a b ⋆ V θ := by
  obtain ⟨a, b, hab⟩ := (mem_center_iff (rel U V θ)).1 (rel_mem_center hU hV θ)
  refine ⟨a, b, ?_⟩
  rw [← hab, rel, mul_assoc_W, hV.neg_mul, mul_one_W]

/-! ## §13 — the functional equation inherited by the relative factor -/

/-- **DERIVED (§13).**  The relative map is normalized at zero. -/
theorem rel_zero : rel U V 0 = w1 := by
  rw [rel, neg_zero, hU.unit, hV.unit, one_mul_W]

/-- **DERIVED (§13).**  The relative map inherits the multiplicative group law.
The proof *uses* the centrality established above; it is not assumed. -/
theorem rel_add (θ φ : ℝ) : rel U V (θ + φ) = rel U V θ ⋆ rel U V φ := by
  have hcentral : ∀ x : W, (U φ ⋆ V (-φ)) ⋆ x = x ⋆ (U φ ⋆ V (-φ)) :=
    rel_mem_center hU hV φ
  have hneg : -(θ + φ) = -φ + -θ := by ring
  calc rel U V (θ + φ) = (U θ ⋆ U φ) ⋆ (V (-φ) ⋆ V (-θ)) := by
        rw [rel, hU.group, hneg, hV.group]
    _ = U θ ⋆ ((U φ ⋆ V (-φ)) ⋆ V (-θ)) := by simp only [mul_assoc_W]
    _ = U θ ⋆ (V (-θ) ⋆ (U φ ⋆ V (-φ))) := by rw [hcentral (V (-θ))]
    _ = rel U V θ ⋆ rel U V φ := by rw [rel, rel, mul_assoc_W]

/-- **DERIVED (§13).**  The value at `-θ` is the inverse of the value at `θ`. -/
theorem rel_neg (θ : ℝ) : rel U V θ ⋆ rel U V (-θ) = w1 := by
  have h := rel_add hU hV θ (-θ)
  rw [add_neg_cancel, rel_zero hU hV] at h
  exact h.symm

end Compare

/-! ## The residual-map interface (§13, §14) -/

/-- **RESIDUAL MAP (§13).**  A one-parameter family of *central* elements
satisfying the multiplicative law.  Invertibility is derived, not assumed. -/
structure IsCentralHom (z : ℝ → W) : Prop where
  /-- Values in the exactly classified center. -/
  mem : ∀ θ : ℝ, z θ ∈ CenterW
  /-- Normalization at zero. -/
  unit : z 0 = w1
  /-- Multiplicative law. -/
  mul : ∀ θ φ : ℝ, z (θ + φ) = z θ ⋆ z φ

namespace IsCentralHom

variable {z : ℝ → W} (hz : IsCentralHom z)
include hz

theorem mul_neg (θ : ℝ) : z θ ⋆ z (-θ) = w1 := by
  have h := hz.mul θ (-θ)
  rw [add_neg_cancel, hz.unit] at h
  exact h.symm

theorem central (θ : ℝ) (x : W) : z θ ⋆ x = x ⋆ z θ := hz.mem θ x

end IsCentralHom

/-- **DERIVED (§13).**  The relative map of two full lifts is a residual map in
exactly the above sense. -/
theorem rel_isCentralHom {U V : ℝ → W} (hU : IsFullLift U) (hV : IsFullLift V) :
    IsCentralHom (rel U V) where
  mem := rel_mem_center hU hV
  unit := rel_zero hU hV
  mul := rel_add hU hV

/-! ## §14 — the upper classification, before any explicit witness -/

/-- **UPPER RESIDUAL-FREEDOM THEOREM (§14).**  Relative to an *arbitrary* fixed
reference lift `V`, every full lift `U` of the same algebra action is
`θ ↦ z θ ⋆ V θ` for a residual map `z` taking values in the exact center and
satisfying the multiplicative law; and conversely every such residual map
produces a full lift of the *same* algebra action.  No explicit reference
formula is used. -/
theorem fullLift_relative_classification {V : ℝ → W} (hV : IsFullLift V)
    (U : ℝ → W) :
    IsFullLift U ↔ ∃ z : ℝ → W, IsCentralHom z ∧ ∀ θ, U θ = z θ ⋆ V θ := by
  constructor
  · intro hU
    exact ⟨rel U V, rel_isCentralHom hU hV, fun θ => by
      rw [rel, mul_assoc_W, hV.neg_mul, mul_one_W]⟩
  · rintro ⟨z, hz, hU⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hU, hz.unit, hV.unit, one_mul_W]
    · intro θ φ
      rw [hU, hU, hU, hz.mul, hV.group]
      simp only [mul_assoc_W]
      rw [central_mul_move (hz.mem φ) (V θ) (V φ)]
    · intro θ x
      rw [hU, hU]
      simp only [mul_assoc_W]
      rw [central_mul_move (hz.mem (-θ)) x (V (-θ)),
        central_mul_move (hz.mem (-θ)) (V θ) (x ⋆ V (-θ)),
        ← mul_assoc_W (z θ) (z (-θ)), hz.mul_neg, one_mul_W, ← mul_assoc_W,
        hV.conj]

/-- **EVERY RESIDUAL MAP PRESERVES THE IMPLEMENTED ACTION (§14).**  Explicitly:
modifying a full lift by a residual map changes no value of the conjugation
action. -/
theorem residual_preserves_action {V z : ℝ → W} (hV : IsFullLift V)
    (hz : IsCentralHom z) (θ : ℝ) (x : W) :
    (((z θ ⋆ V θ) ⋆ x) ⋆ (z (-θ) ⋆ V (-θ))) = (V θ ⋆ x) ⋆ V (-θ) := by
  have h := ((fullLift_relative_classification hV (fun t => z t ⋆ V t)).2
    ⟨z, hz, fun _ => rfl⟩).conj θ x
  rw [h, hV.conj]

end NullSectorTask11
