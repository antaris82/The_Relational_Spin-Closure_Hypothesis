import RequestProject.Experiment2.NullSectorTask11.InfinitesimalLift
import RequestProject.Experiment2.NullSectorTask10.AxialDerivation

/-!
# Task 11, Layer 10: generator separation (§29, §30, §31)

Three logically distinct objects are separated here.

* the **left generator** `G` of a differentiable full lift — an element of the
  carrier, acting on the carrier by left multiplication;
* the **derivation** it induces by the commutator, which is exactly the
  inherited infinitesimal generator `Dgen` of the algebra automorphism family;
* the **rate freedom** `λ • Dgen` of the Task-10 derivation classification.

The commutator formula is *derived*, not prescribed, and the exact kernel of the
map `G ↦ (x ↦ G ⋆ x - x ⋆ G)` is identified with the exact center of §9.
-/

namespace NullSectorTask11

open NullSectorTask08 NullSectorTask09 NullSectorTask10

/-! ## Two missing distributivity lemmas -/

theorem sub_mul_W (x y z : W) : (x - y) ⋆ z = x ⋆ z - y ⋆ z := by
  rw [sub_eq_add_neg, add_mul_W, neg_mul_W, ← sub_eq_add_neg]

theorem mul_sub_W (x y z : W) : x ⋆ (y - z) = x ⋆ y - x ⋆ z := by
  rw [sub_eq_add_neg, mul_add_W, mul_neg_W, ← sub_eq_add_neg]

/-! ## §29 — the derivation induced by a carrier element -/

/-- **DERIVED NOTION.**  The derivation induced by a carrier element through the
commutator.  Neutral name; no dynamical reading. -/
def inducedDer (G : W) : W → W := fun x => G ⋆ x - x ⋆ G

theorem inducedDer_apply (G x : W) : inducedDer G x = G ⋆ x - x ⋆ G := rfl

/-- Central summands of a generator drop out of the induced derivation. -/
theorem inducedDer_zc_add (a b : ℝ) (G : W) :
    inducedDer (zc a b + G) = inducedDer G := by
  funext x
  simp only [inducedDer, add_mul_W, mul_add_W, zc_central a b x]
  abel

/-- **THE INDUCED DERIVATION OF THE EXACT GENERATOR (§29).**  For the exact
generator of §28 the commutator is precisely the inherited infinitesimal algebra
generator `Dgen` — the visible part is the fixed `-(1/2)·R` component, and the
central part contributes nothing. -/
theorem inducedDer_generator (a b : ℝ) :
    inducedDer (zc a b - (2⁻¹ : ℝ) • wR) = Dgen := by
  have h : zc a b - (2⁻¹ : ℝ) • wR = zc a b + (-((2⁻¹ : ℝ) • wR)) := by abel
  rw [h, inducedDer_zc_add]
  funext x
  rw [inducedDer_apply, neg_mul_W, mul_neg_W, smul_mul_W, mul_smul_W,
    Dgen_eq_half_commutator]
  module

/-- **THE INFINITESIMAL GENERATOR THEOREM (§29).**  Every differentiable full
lift induces, through the commutator of its left generator, exactly the
inherited infinitesimal algebra generator; and the derivative of the algebra
action is that same object.  The two roles are kept apart: `G` acts by *left
multiplication*, `inducedDer G` is the *derivation*. -/
theorem differentiableFullLift_inducedDer {U : ℝ → W} (hU : IsDifferentiableFullLift U) :
    inducedDer (leftGen U) = Dgen ∧
      ∀ x : W, HasDerivAt (fun θ => Phi θ x) (inducedDer (leftGen U) x) 0 := by
  obtain ⟨α, β, -, hG⟩ := differentiableFullLift_generator hU
  have h : inducedDer (leftGen U) = Dgen := by rw [hG, inducedDer_generator]
  exact ⟨h, fun x => by rw [h]; exact hasDerivAt_Phi_zero x⟩

/-- **LEFT MULTIPLICATION IS NOT THE DERIVATION (§29).**  The generator of a
differentiable full lift never acts as a derivation by left multiplication:
the Leibniz rule fails already on the unit.  Only the *commutator* of `G` is a
derivation. -/
theorem leftMul_generator_not_derivation {U : ℝ → W} (hU : IsDifferentiableFullLift U) :
    ¬ (∀ x y : W, leftGen U ⋆ (x ⋆ y) = (leftGen U ⋆ x) ⋆ y + x ⋆ (leftGen U ⋆ y)) := by
  intro h
  have h1 := h w1 w1
  simp only [one_mul_W, mul_one_W] at h1
  have hG0 : leftGen U = 0 := left_eq_add.mp h1
  obtain ⟨α, β, -, hG⟩ := differentiableFullLift_generator hU
  have h6 : (leftGen U) 6 = -(2⁻¹ : ℝ) := by
    rw [hG]
    simp [zc, w1, wS, wR]
  rw [hG0] at h6
  norm_num at h6

/-! ## §30 — the invisible part of the generator -/

/-- **EXACT INVISIBLE FREEDOM (§30).**  Two carrier elements induce the same
derivation **iff** their difference lies in the exact center of `W` classified
in §9 — equivalently, in the inherited central plane `Z`.  Nothing was assumed
about the difference beforehand. -/
theorem inducedDer_eq_iff_sub_mem_center (G G' : W) :
    inducedDer G = inducedDer G' ↔ G - G' ∈ CenterW := by
  constructor
  · intro h x
    have hx := congrFun h x
    rw [inducedDer_apply, inducedDer_apply] at hx
    rw [sub_mul_W, mul_sub_W]
    have h3 : (G ⋆ x - G' ⋆ x) - (x ⋆ G - x ⋆ G')
        = (G ⋆ x - x ⋆ G) - (G' ⋆ x - x ⋆ G') := by abel
    rw [hx, sub_self] at h3
    exact sub_eq_zero.mp h3
  · intro h
    funext x
    have hx : (G - G') ⋆ x = x ⋆ (G - G') := h x
    rw [sub_mul_W, mul_sub_W] at hx
    rw [inducedDer_apply, inducedDer_apply]
    have h3 : (G ⋆ x - x ⋆ G) - (G' ⋆ x - x ⋆ G')
        = (G ⋆ x - G' ⋆ x) - (x ⋆ G - x ⋆ G') := by abel
    rw [hx, sub_self] at h3
    exact sub_eq_zero.mp h3

/-- **INVISIBLE FREEDOM, EXPLICIT FORM (§30).**  The invisible freedom is exactly
the inherited central plane: adding any `zc a b` to a generator changes nothing
in the induced derivation, and no other change is invisible. -/
theorem invisible_generator_freedom (G G' : W) :
    inducedDer G = inducedDer G' ↔ ∃ a b : ℝ, G - G' = zc a b := by
  rw [inducedDer_eq_iff_sub_mem_center]
  exact mem_center_iff _

/-! ## §31 — comparison with the Task-10 derivation-rate freedom -/

/-- **THE RATE IS NOT FREE FOR A LIFT (§31).**  Task 10 classified the admissible
axial derivations as the whole real line `λ • Dgen`.  For an internal lift of the
*fixed* automorphism family that freedom collapses: the induced derivation is
`Dgen` itself, i.e. `λ = 1`, whatever the residual lift freedom.  The two
freedoms are therefore logically independent, not two names for one freedom. -/
theorem rate_freedom_collapses {U : ℝ → W} (hU : IsDifferentiableFullLift U) (l : ℝ) :
    (∀ x : W, inducedDer (leftGen U) x = l • Dgen x) ↔ l = 1 := by
  have hD : inducedDer (leftGen U) = Dgen := (differentiableFullLift_inducedDer hU).1
  constructor
  · intro h
    have h2 := h wB
    rw [hD] at h2
    simp only [Dgen_wB] at h2
    have h3 := congrFun h2 3
    simp [wC] at h3
    linarith
  · intro h x
    rw [hD, h, one_smul]

/-- **THE RESIDUAL LIFT FREEDOM IS INVISIBLE TO THE ALGEBRA (§31).**  All
differentiable full lifts — the whole two-parameter residual family — induce one
and the same derivation.  The residual freedom is thus *not* a rate freedom: it
does not rescale the algebra flow, it is completely invisible to it. -/
theorem residual_freedom_invisible {U V : ℝ → W}
    (hU : IsDifferentiableFullLift U) (hV : IsDifferentiableFullLift V) :
    inducedDer (leftGen U) = inducedDer (leftGen V) ∧ leftGen U - leftGen V ∈ CenterW := by
  have h1 := (differentiableFullLift_inducedDer hU).1
  have h2 := (differentiableFullLift_inducedDer hV).1
  have h : inducedDer (leftGen U) = inducedDer (leftGen V) := by rw [h1, h2]
  exact ⟨h, (inducedDer_eq_iff_sub_mem_center _ _).1 h⟩

/-- **SEPARATION SUMMARY (§31).**  The visible component of the generator is the
fixed axis term; the invisible component is an arbitrary element of the exact
center.  Both statements are proved, not assumed. -/
theorem generator_visible_invisible_split {U : ℝ → W} (hU : IsDifferentiableFullLift U) :
    ∃ z : W, z ∈ CenterW ∧ leftGen U = z - (2⁻¹ : ℝ) • wR ∧
      inducedDer (leftGen U) = Dgen ∧ inducedDer ((-(2⁻¹) : ℝ) • wR) = Dgen := by
  obtain ⟨α, β, -, hG⟩ := differentiableFullLift_generator hU
  refine ⟨zc α β, (mem_center_iff _).2 ⟨α, β, rfl⟩, hG, ?_, ?_⟩
  · rw [hG, inducedDer_generator]
  · have h : ((-(2⁻¹) : ℝ)) • wR = zc 0 0 - (2⁻¹ : ℝ) • wR := by
      rw [zc]; module
    rw [h, inducedDer_generator]

end NullSectorTask11
