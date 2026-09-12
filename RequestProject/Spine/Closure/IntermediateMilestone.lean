import RequestProject.Spine.E1.Core
import RequestProject.Spine.Solder.SmoothMetric
import RequestProject.Spine.Task36.Certificate
import RequestProject.Spine.Deformation.SolderTransport

/-!
# Task 39 / Part III §7 : the intermediate-milestone certificate

**Closure module of the present project phase.**  It introduces no new mathematics: every
conjunct below is discharged by a theorem that was already certified in Tasks 30–38 or in the
two Task-39 strengthening modules `Spine.Deformation.SmoothProjectedGauge` and
`Spine.Deformation.SolderTransport`.

The purpose of the module is to make the frozen intermediate state checkable in one place:
if any of the aggregated endpoints is weakened or removed, this module stops compiling.

## What is aggregated

```text
 LOCAL   L1  the intrinsic Lorentz quadratic structure of the carrier
         L2  Clifford / Jordan compatibility of the paravector embedding
         L3  the intrinsic Spin double cover of the intrinsic Lorentz group
 GLOBAL  G1  a smooth base gluing produces a smooth four-dimensional emergent manifold
         G2  a regular solder is exactly a regular bundle equivalence
                internal Lorentz bundle ≃ TM
         G3  a regular solder produces a smooth tangent Lorentz metric of signature (1,3)
         G4  a regular solder forces orientation compatibility of the emergent atlas
         G5  a regular solder forces triviality of the project-native Spin obstruction
         G6  a regular solder yields a coherent future-cone (time-orientation) reduction
         G7  the discrete fixed-cover Spin-lift freedom survives the construction
 SMOKE   S1  the Task-37 native one-parameter transition deformation is globally admissible
                on the frozen periodic control, for every finite parameter value
         S2  the tested family lies in one full-Spin Čech gauge orbit, and so does its
                projection
         S3  the projected Lorentz gauge is C^∞ on every chart domain (Task 39 §4)
         S4  the regular solder solution spaces at two parameter values correspond, and
                corresponding solutions induce the same tangent Lorentz metric (Task 39 §5)
```

## What is deliberately **not** aggregated

* nothing about a Spin connection, parallel transport, holonomy, curvature, a field strength,
  Einstein dynamics or a cosmological statement — no such object exists in this project;
* no identification of the project-native Spin obstruction with the standard `w₂(TM)`, and no
  identification of the orientation gate with `w₁(TM)`;
* no claim that a regular solder exists for an arbitrary base gluing: G2–G6 are all
  *conditional* on a regular solder being given, and the Möbius-type control of Task 36 shows
  that the condition can fail;
* no generality beyond the frozen periodic control for S1–S4.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Closure

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase Task36 Task37.Deformation
open EmergentBase.BaseGluingData

universe t

/-! ## The local core -/

/-- **Task 39 §7, LOCAL.**  The certified intrinsic local core: the quadratic structure of the
carrier is the Minkowski form of signature `(1,3)` in the intrinsic frame, the paravector
embedding into the intrinsic Clifford algebra turns the symmetrized Clifford product into the
spin-factor Jordan product, and the intrinsic Spin group covers the intrinsic Lorentz group
twice, with central kernel. -/
theorem local_core_certificate :
    (∀ x : LorentzCarrier, NS x = x.1 ^ 2 - (x.2 0 ^ 2 + x.2 1 ^ 2 + x.2 2 ^ 2)) ∧
    (∀ x y : LorentzCarrier,
      (2 : ℝ)⁻¹ • (spinToCl x * spinToCl y + spinToCl y * spinToCl x) = spinToCl (sJ x y)) ∧
    Function.Surjective (⇑spinCover : ↥SpinGroup → ↥GLor) ∧
    (∀ z ∈ spinCover.ker, ∀ u : ↥SpinGroup, z * u = u * z) ∧
    Nat.card (spinCover.ker : Subgroup ↥SpinGroup) = 2 ∧
    Continuous (⇑spinCover : ↥SpinGroup → ↥GLor) ∧
    (∀ k : GLor, ∃ V : Set GLor, IsOpen V ∧ k ∈ V ∧ ∃ s : GLor → SpinGroup,
      ContinuousOn s V ∧ ∀ y ∈ V, spinCover (s y) = y) :=
  ⟨lorentz_quadratic_form, clifford_jordan, spinCover_surjective,
   fun z hz u => spinCover_ker_central z hz u, spinCover_ker_card,
   spin_double_cover_topological_endpoint.2.2.2.2.1,
   spin_double_cover_local_section_endpoint⟩

/-! ## The global layer -/

section Global

variable {ι : Type t} {B : BaseGluingData LocalModel ι}

/-- **Task 39 §7, GLOBAL.**  The certified global layer, for an arbitrary smooth base gluing
`B` and an arbitrary native Spin transition datum `S` over its emergent cover.

Every solder-dependent item is stated **conditionally**: `∀ E : SmoothTangentSolderData B S`.
Nothing here asserts that such an `E` exists for a given `B`; the Möbius-type control
`Task36.orientation_reversing_gluing_no_solder` shows that it need not. -/
theorem global_layer_certificate [Countable ι] (hclosed : B.ClosedGluingGraph)
    (h : B.SmoothGluing) (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) :
    -- G1 the emergent smooth four-manifold
    (T2Space (Space B) ∧ SecondCountableTopology (Space B) ∧
      IsManifold (modelWithCornersSelf ℝ LocalModel) (⊤ : ℕ∞) (Space B) ∧
      Module.finrank ℝ LocalModel = 4) ∧
    -- G2 regular solder = regular bundle equivalence with TM
    (Nonempty (SmoothTangentSolderData B S) ↔ Nonempty (RegularBundleCertificate h S)) ∧
    -- G3 the smooth tangent Lorentz metric of the regular-solder sector
    (∀ E : SmoothTangentSolderData B S,
      (∀ i u v, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => E.metricCoeff i y u v) (B.D i)) ∧
      (∀ i y u v, E.metricCoeff i y u v = E.metricCoeff i y v u) ∧
      (∀ i j, ∀ y ∈ B.W i j, ∀ u v,
        E.metricCoeff j (B.φ i j y) (B.tangentTransitionMap i j y u)
            (B.tangentTransitionMap i j y v)
          = E.metricCoeff i y u v) ∧
      (∀ i y, E.metricCoeff i y (E.A i y sOne) (E.A i y sOne) = 1 ∧
        (∀ w : Fin 3 → ℝ, E.metricCoeff i y (E.A i y (0, w)) (E.A i y (0, w)) ≤ 0) ∧
        (∀ w : Fin 3 → ℝ, E.metricCoeff i y (E.A i y (0, w)) (E.A i y (0, w)) = 0 → w = 0))) ∧
    -- G4/G5 the two reconvergence gates
    (Nonempty (SmoothTangentSolderData B S) →
      (∃ a : ι → LocalModel → ℝ,
        (∀ i, ContinuousOn (a i) (B.D i)) ∧
        (∀ i y, a i y ≠ 0) ∧
        (∀ i j, ∀ y ∈ B.W i j,
          LinearMap.det ((B.tangentTransitionMap i j y : LocalModel →ₗ[ℝ] LocalModel))
            * a i y = a j (B.φ i j y))) ∧
      (∀ D : SpinLiftFamily internalSpinProjection (project internalSpinProjection S),
        D.obstruction = trivialClass internalSpinProjection (emergentCover B))) ∧
    -- G6 the future-cone reduction
    (Nonempty (SmoothTangentSolderData B S) → Nonempty (TimeOrientationReduction B)) := by
  refine ⟨?_, nonempty_regularBundleCertificate_iff h, fun E => ?_, fun hE => ?_,
    fun hE => ?_⟩
  · obtain ⟨h1, h2, h3, h4, -, -⟩ := B.smoothEmergentManifoldCertificate hclosed h
    exact ⟨h1, h2, h3, h4⟩
  · obtain ⟨hsmooth, hsymm, -, htensor, hsig, -⟩ := E.smooth_tangent_lorentz_metric h
    exact ⟨hsmooth, hsymm, htensor, hsig⟩
  · obtain ⟨E⟩ := hE
    obtain ⟨hor, -, hspin⟩ := classical_reconvergence h E
    exact ⟨hor, hspin⟩
  · obtain ⟨E⟩ := hE
    exact nonempty_timeOrientationReduction_of_solder E

end Global

/-- **Task 39 §7, GLOBAL — the discrete fixed-cover Spin-lift freedom is not removed.**
Over the one-loop control there are two native Spin transition data with the *same* projected
Lorentz transition system, both admitting a regular solder, which are not related by the
project's kernel-valued fixed-cover gauge equivalence.  The bottom-up construction therefore
has not accidentally canonized the Spin lift. -/
theorem fixed_cover_lift_freedom_certificate :
    ∃ S S' : NativeSpinTransitionData ↥SpinGroup
        (emergentCover (loopGluingOf Unit LoopTwist.id')),
      Nonempty (SmoothTangentSolderData (loopGluingOf Unit LoopTwist.id') S) ∧
      Nonempty (SmoothTangentSolderData (loopGluingOf Unit LoopTwist.id') S') ∧
      (∀ (p q : Unit × Bool) (x : Space (loopGluingOf Unit LoopTwist.id')),
        x ∈ (emergentCover (loopGluingOf Unit LoopTwist.id')).overlap₂ p q →
          (project internalSpinProjection S').g p q x
            = (project internalSpinProjection S).g p q x) ∧
      ¬ GaugeEquiv internalSpinProjection S S' :=
  one_loop_has_kernel_sign_freedom

/-! ## The deformation smoke test, at exactly its proved scope -/

/-- **Task 39 §7, SMOKE TEST.**  The exact strength of the Task-37/38 experiment on the frozen
periodic control base, together with the two Task-39 strengthenings.

Read the scope literally: every statement is about the *fixed* control base
`Task36.loopGluingOf κ LoopTwist.id'` and the *specific* native one-parameter Spin
transition family `Task37.Deformation.loopSharedSpin`.  Nothing is claimed for other base
gluings, for co-varying bases, or for transition deformations in general. -/
theorem smoketest_certificate (κ : Type) [DecidableEq κ] :
    -- S1 universal admissibility of the tested family on the fixed control
    (∀ l : ℝ, ControlAAdmissible κ l) ∧
    regularRegion (loopTransportFamily κ) = Set.univ ∧
    -- S2 one full-Spin Čech gauge orbit, and the projected orbit
    (∀ l₁ l₂ : ℝ, CocycleGaugeEquiv (loopSharedSpin (κ := κ) l₁) (loopSharedSpin l₂)) ∧
    (∀ l₁ l₂ : ℝ,
      CocycleGaugeEquiv (project internalSpinProjection (loopSharedSpin (κ := κ) l₁))
        (project internalSpinProjection (loopSharedSpin l₂))) ∧
    -- S3 the projected Lorentz gauge is smooth on every chart domain
    (∀ (l : ℝ) (p : κ × Bool),
      ContDiffOn ℝ (⊤ : ℕ∞) (loopProjectedGauge l p)
        ((loopGluingOf κ LoopTwist.id').D p)) ∧
    -- S4 the regular solution spaces correspond, with equal induced tangent metrics
    (∀ l₁ l₂ : ℝ,
      ∃ F : SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₁)
          ≃ SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₂),
        ∀ (E : SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₁))
          (x : Space (loopGluingOf κ LoopTwist.id')) (u v : TangentSpace localModelI x),
          ((F E).toTangentSolderData loopSmoothGluing).tangentMetric x u v
            = (E.toTangentSolderData loopSmoothGluing).tangentMetric x u v) ∧
    -- and the original Task-38 statement about the explicit branch, unchanged
    (∀ (l₁ l₂ : ℝ) (x : Space (loopGluingOf κ LoopTwist.id'))
        (u v : TangentSpace localModelI x),
      ((loopParaSolder l₁).toTangentSolderData loopSmoothGluing).tangentMetric x u v
        = ((loopParaSolder l₂).toTangentSolderData loopSmoothGluing).tangentMetric x u v) :=
  ⟨fun l => controlAAdmissible_all l,
   regularRegion_loopTransportFamily,
   fun l₁ l₂ => spinCocycle_gaugeEquiv l₁ l₂,
   fun l₁ l₂ => projectedCocycle_gaugeEquiv l₁ l₂,
   fun l p => contDiffOn_loopProjectedGauge l p,
   fun l₁ l₂ => loopSolderSolutionSpace_correspondence l₁ l₂,
   fun l₁ l₂ x u v => tangentMetric_loopParaSolder_eq l₁ l₂ x u v⟩

/-- **Task 39 §7, PRINCIPAL — the intermediate-milestone certificate.**

The single aggregate statement of the frozen intermediate release: the local intrinsic core,
the global layer for an arbitrary smooth base gluing and native Spin datum, the surviving
discrete lift freedom, and the deformation smoke test at exactly its proved scope.

This theorem is an aggregation only.  It contains no conjunct that is not proved elsewhere in
the project, and in particular no conjunct about a connection, a parallel transport, a
holonomy, a curvature or a field equation. -/
theorem intermediate_milestone_certificate
    {ι : Type t} [Countable ι] {B : BaseGluingData LocalModel ι}
    (hclosed : B.ClosedGluingGraph) (h : B.SmoothGluing)
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B))
    (κ : Type) [DecidableEq κ] :
    (∀ x : LorentzCarrier, NS x = x.1 ^ 2 - (x.2 0 ^ 2 + x.2 1 ^ 2 + x.2 2 ^ 2)) ∧
    Function.Surjective (⇑spinCover : ↥SpinGroup → ↥GLor) ∧
    Nat.card (spinCover.ker : Subgroup ↥SpinGroup) = 2 ∧
    IsManifold (modelWithCornersSelf ℝ LocalModel) (⊤ : ℕ∞) (Space B) ∧
    (Nonempty (SmoothTangentSolderData B S) ↔ Nonempty (RegularBundleCertificate h S)) ∧
    (∀ E : SmoothTangentSolderData B S,
      (∀ i u v, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => E.metricCoeff i y u v) (B.D i)) ∧
      (∀ i y, E.metricCoeff i y (E.A i y sOne) (E.A i y sOne) = 1)) ∧
    (Nonempty (SmoothTangentSolderData B S) →
      (∃ a : ι → LocalModel → ℝ,
        (∀ i, ContinuousOn (a i) (B.D i)) ∧
        (∀ i y, a i y ≠ 0) ∧
        (∀ i j, ∀ y ∈ B.W i j,
          LinearMap.det ((B.tangentTransitionMap i j y : LocalModel →ₗ[ℝ] LocalModel))
            * a i y = a j (B.φ i j y))) ∧
      (∀ D : SpinLiftFamily internalSpinProjection (project internalSpinProjection S),
        D.obstruction = trivialClass internalSpinProjection (emergentCover B)) ∧
      Nonempty (TimeOrientationReduction B)) ∧
    (∃ S₁ S₂ : NativeSpinTransitionData ↥SpinGroup
        (emergentCover (loopGluingOf Unit LoopTwist.id')),
      Nonempty (SmoothTangentSolderData (loopGluingOf Unit LoopTwist.id') S₁) ∧
      Nonempty (SmoothTangentSolderData (loopGluingOf Unit LoopTwist.id') S₂) ∧
      ¬ GaugeEquiv internalSpinProjection S₁ S₂) ∧
    (∀ l : ℝ, ControlAAdmissible κ l) ∧
    (∀ l₁ l₂ : ℝ, CocycleGaugeEquiv (loopSharedSpin (κ := κ) l₁) (loopSharedSpin l₂)) ∧
    (∀ (l : ℝ) (p : κ × Bool),
      ContDiffOn ℝ (⊤ : ℕ∞) (loopProjectedGauge l p)
        ((loopGluingOf κ LoopTwist.id').D p)) ∧
    (∀ l₁ l₂ : ℝ,
      ∃ F : SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₁)
          ≃ SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₂),
        ∀ (E : SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₁))
          (x : Space (loopGluingOf κ LoopTwist.id')) (u v : TangentSpace localModelI x),
          ((F E).toTangentSolderData loopSmoothGluing).tangentMetric x u v
            = (E.toTangentSolderData loopSmoothGluing).tangentMetric x u v) := by
  obtain ⟨hL1, -, hL3, -, hL5, -, -⟩ := local_core_certificate
  obtain ⟨hG1, hG2, hG3, hG45, hG6⟩ := global_layer_certificate hclosed h S
  obtain ⟨hS1, -, hS2, -, hS3, hS4, -⟩ := smoketest_certificate κ
  obtain ⟨S₁, S₂, hs₁, hs₂, -, hne⟩ := fixed_cover_lift_freedom_certificate
  exact ⟨hL1, hL3, hL5, hG1.2.2.1, hG2,
    fun E => ⟨(hG3 E).1, fun i y => ((hG3 E).2.2.2 i y).1⟩,
    fun hE => ⟨(hG45 hE).1, (hG45 hE).2, hG6 hE⟩,
    ⟨S₁, S₂, hs₁, hs₂, hne⟩, hS1, hS2, hS3, hS4⟩

end Closure

end

/-! ## Axiom audit -/

#print axioms Closure.local_core_certificate
#print axioms Closure.global_layer_certificate
#print axioms Closure.fixed_cover_lift_freedom_certificate
#print axioms Closure.smoketest_certificate
#print axioms Closure.intermediate_milestone_certificate
