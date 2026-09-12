import RequestProject.Spine.Task36.SpinObstruction
import RequestProject.Spine.Task36.TrivialControl
import RequestProject.Spine.Task36.SmoothBundlePackaging
import RequestProject.Spine.Task36.OrientationReversing
import RequestProject.Spine.Task36.SpinNotLorentz
import RequestProject.Spine.Task36.LoopSpinFreedom

/-!
# Task 36 / Adversarial : the bundled certificate (§20)

**Ninth module of the Task-36 battery.**

This module states, as a single theorem, exactly those adversarial tests of Task 36 that were
actually proved.  Nothing that is blocked, external or merely documented appears as a field.

In particular the following §12–§16 source-derived cases are **absent** from the certificate,
because they are *not* formalized in this project; they are recorded as external robustness
cases with their exact blockers in `TASK36_COUNTERTEST_MATRIX.md`:

* §12 the concrete `S⁴` separation (`spin_does_not_imply_lorentz`);
* §13 the `E8`-type topological/smooth separation;
* §14 the spin-foam category separation;
* §16 the globally-hyperbolic `ℝ × Σ` positive class.

## Fields of `adversarial_global_topology_certificate`

For an arbitrary smooth base gluing `B` and native Spin transition datum `S`:

1. **reconvergence** (§11) — a regular solder implies orientation compatibility of the
   emergent atlas *and* triviality of the project-native Spin-lifting obstruction;
2. **orientation contrapositive** (§20 `orientation_obstruction_nonzero_implies_no_solder`);
3. **Spin contrapositive** (§20 `spin_obstruction_nonzero_implies_no_solder`);
4. **smooth packaging** (§1) — the regular solder is equivalent to the six-item smooth
   bundle-equivalence certificate;
5. **time orientation** (§3) — a regular solder yields a coherent future-cone reduction.

For the concrete adversarial models:

6. **trivial control** (§6) — the one-chart base: solder exists, no overlap obstruction, no
   artificial sign family;
7. **one-loop control** (§7) — the loop base: a regular solder exists and there are two
   gauge-inequivalent native Spin data over the *same* projected Lorentz transition system;
8. **fixed-cover multiplicity** (§8) — `N` independent loops give `2^N` classes, instantiated
   at `N = 2`;
9. **orientation-reversing control** (§9) — the Möbius-type gluing admits no regular solder,
   for *any* native Spin datum, and the failure is at the orientation gate;
10. **Spin-type data do not imply a Lorentz solder** (§12, project-native form) — over the
    same Möbius-type gluing native Spin transition data *do* exist while no regular solder
    does.  This is **not** the `S⁴` theorem; see `Task36.spin_does_not_imply_lorentz_moebius`
    and `TASK36_COUNTERTEST_MATRIX.md`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task36

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase
open EmergentBase.BaseGluingData

universe t

/-- **NEWLY DEFINED (Task 36), PRINCIPAL — `adversarial_global_topology_certificate` (§20).**

The bundled Task-36 result: every field is a test that was actually proved at the exact
project-native regularity level.  Blocked and external cases are deliberately not fields.

The scientific content is the pair of independent *gates*.  A regular solder — built bottom-up
from the primitive Euclidean root with no orientation datum, no characteristic class and no
`SO`-first lift anywhere in its construction — nevertheless forces the orientation
compatibility of the emergent atlas and the vanishing of the project-native Spin-lifting
obstruction; and the two gates reject the two adversarial controls independently: the
orientation-reversing gluing is rejected by the determinant gate alone (field 9), while a
nontrivial lifting obstruction is rejected by the triple-overlap gate alone (field 3).  At the
same time the residual `ℤ/2` loop freedom is *not* destroyed by the construction (fields 7, 8),
so the bottom-up route has not accidentally canonized the Spin structure. -/
theorem adversarial_global_topology_certificate
    {ι : Type t} {B : BaseGluingData LocalModel ι} (h : B.SmoothGluing)
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) :
    -- 1. §11 classical reconvergence
    (∀ E : SmoothTangentSolderData B S,
      (∃ a : ι → LocalModel → ℝ,
        (∀ i, ContinuousOn (a i) (B.D i)) ∧
        (∀ i y, a i y ≠ 0) ∧
        (∀ i j, ∀ y ∈ B.W i j,
          LinearMap.det ((B.tangentTransitionMap i j y : LocalModel →ₗ[ℝ] LocalModel))
            * a i y = a j (B.φ i j y))) ∧
      (∀ (i j : ι) (y : LocalModel) (hy : y ∈ B.W i j) (v : LocalModel),
        E.solderLorentzRep i j y v
          = projectedLorentzTransition S i j (B.chart i ⟨y, B.W_subset i j hy⟩) v) ∧
      (∀ D : SpinLiftFamily internalSpinProjection (project internalSpinProjection S),
        D.obstruction = trivialClass internalSpinProjection (emergentCover B))) ∧
    -- 2. §20 orientation contrapositive
    ((¬ ∃ a : ι → LocalModel → ℝ,
        (∀ i, ContinuousOn (a i) (B.D i)) ∧
        (∀ i y, a i y ≠ 0) ∧
        (∀ i j, ∀ y ∈ B.W i j,
          LinearMap.det ((B.tangentTransitionMap i j y : LocalModel →ₗ[ℝ] LocalModel))
            * a i y = a j (B.φ i j y))) →
      ∀ S' : NativeSpinTransitionData ↥SpinGroup (emergentCover B),
        IsEmpty (SmoothTangentSolderData B S')) ∧
    -- 3. §20 Spin-lifting contrapositive
    (∀ {T : VisibleCocycle ↥GLor (emergentCover B)}
        (D : SpinLiftFamily internalSpinProjection T),
      D.obstruction ≠ trivialClass internalSpinProjection (emergentCover B) →
      ¬ ∃ S' : NativeSpinTransitionData ↥SpinGroup (emergentCover B),
          Nonempty (SmoothTangentSolderData B S') ∧
          ∀ i j, ∀ x ∈ (emergentCover B).overlap₂ i j,
            (project internalSpinProjection S').g i j x = T.g i j x) ∧
    -- 4. §1 smooth bundle packaging
    (Nonempty (SmoothTangentSolderData B S) ↔ Nonempty (RegularBundleCertificate h S)) ∧
    -- 5. §3 time-orientation reduction
    (∀ _E : SmoothTangentSolderData B S, Nonempty (TimeOrientationReduction B)) ∧
    -- 6. §6 trivial positive control
    (oneChartGluing.SmoothGluing ∧
      IsManifold localModelI (⊤ : ℕ∞) (Space oneChartGluing) ∧
      Nonempty (SmoothTangentSolderData oneChartGluing oneChartSpin) ∧
      (∀ ε : KerCocycle internalSpinProjection (emergentCover oneChartGluing),
        ε.IsPointwiseTrivial)) ∧
    -- 7. §7 one-loop kernel-sign freedom
    (∃ S₁ S₂ : NativeSpinTransitionData ↥SpinGroup
        (emergentCover (loopGluingOf Unit LoopTwist.id')),
      Nonempty (SmoothTangentSolderData (loopGluingOf Unit LoopTwist.id') S₁) ∧
      Nonempty (SmoothTangentSolderData (loopGluingOf Unit LoopTwist.id') S₂) ∧
      (∀ (p q : Unit × Bool) (x : Space (loopGluingOf Unit LoopTwist.id')),
        x ∈ (emergentCover (loopGluingOf Unit LoopTwist.id')).overlap₂ p q →
          (project internalSpinProjection S₂).g p q x
            = (project internalSpinProjection S₁).g p q x) ∧
      ¬ GaugeEquiv internalSpinProjection S₁ S₂) ∧
    -- 8. §8 fixed-cover multiplicity, instantiated at N = 2
    (Fintype.card (Fin 2 → Bool) = 4 ∧
      (∀ σ τ : Fin 2 → Bool,
        Nonempty (SmoothTangentSolderData (loopGluingOf (Fin 2) LoopTwist.id')
          (twistedSpin σ)) ∧
        (GaugeEquiv internalSpinProjection (twistedSpin σ) (twistedSpin τ) → σ = τ))) ∧
    -- 9. §9 orientation-reversing negative control
    (∀ S' : NativeSpinTransitionData ↥SpinGroup (emergentCover moebiusGluing),
      IsEmpty (SmoothTangentSolderData moebiusGluing S')) ∧
    -- 10. §12 project-native Spin/Lorentz separation (NOT the S⁴ theorem)
    (moebiusGluing.SmoothGluing ∧
      IsManifold localModelI (⊤ : ℕ∞) (Space moebiusGluing) ∧
      Nonempty (NativeSpinTransitionData ↥SpinGroup (emergentCover moebiusGluing)) ∧
      (∀ S' : NativeSpinTransitionData ↥SpinGroup (emergentCover moebiusGluing),
        IsEmpty (SmoothTangentSolderData moebiusGluing S'))) := by
  refine ⟨fun E => classical_reconvergence h E,
    fun hobstr S' => orientation_obstruction_nonzero_implies_no_solder hobstr S',
    fun D hD => spin_obstruction_nonzero_implies_no_solder D hD,
    nonempty_regularBundleCertificate_iff h,
    fun E => nonempty_timeOrientationReduction_of_solder E,
    ⟨oneChartGluing_smoothGluing, oneChartGluing_isManifold, ⟨oneChartSolder⟩,
      fun ε => kerCocycle_pointwiseTrivial_of_subsingleton ε⟩,
    one_loop_has_kernel_sign_freedom,
    two_loop_spin_choice_family,
    orientation_reversing_gluing_no_solder,
    spin_does_not_imply_lorentz_moebius⟩

end Task36

end

/-! ## Axiom audit -/

#print axioms Task36.adversarial_global_topology_certificate
