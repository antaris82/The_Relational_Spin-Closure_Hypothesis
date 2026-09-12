import RequestProject.Spine.Comparison.SpinNativeVsSO
import RequestProject.Spine.Comparison.KernelTwistCohomology

/-!
# Spine / Comparison : the canonical Spin seed

The packaged output of Task 31, and the intended *input* of the next stage.  A
`SpinNative.CanonicalSpinSeed` contains **only** what has been certified so far:

| field / theorem | content | status |
|---|---|---|
| `cover` | a Čech cover `𝓤` of an already given base `X` | **external input, still required** |
| `proj` | the central double cover `ρ : L → G` (frozen interface) | given |
| `native` | coherent Spin-native gluing data `g̃_ij` on `𝓤` | primitive datum |
| `projected` | the `SO`/Lorentz-valued cocycle `ρ ∘ g̃` | derived, no choice |
| `canonical` | the distinguished Spin structure over `projected` | derived, no lift choice |
| `obstruction_trivial` | the *existing standard* Spin-lift obstruction of `projected` is trivial, for **every** family of local lifts | theorem (Task 30) |
| `residual_freedom` | every competing Spin structure over `projected` is a kernel twist | theorem (Task 31) |
| `unique_up_to_gauge_of_gate` | under the explicit fixed-cover `H¹`-type gate the Spin structure is unique up to gauge equivalence | theorem (Task 31) |

## What is deliberately **not** in the package

No manifold constructed from the data, no connection, no transport, no holonomy, no
curvature, no torsion, no metric beyond the frame data already used in the Lorentz
instantiation, and no dynamics.  Nothing of the sort exists anywhere in the Task-30/31
layers.

## The external inputs that remain — visible in the type

The parameters `X`, `[TopologicalSpace X]`, `ι` and the field `cover` are exactly the inputs
that the next stage is meant to eliminate: the base set, its topology, the index type of the
cover and the cover itself.  They are *syntactically* part of `CanonicalSpinSeed`, which is
the point of the package: the remaining unwanted inputs cannot be overlooked.  `L`, `G` and
`proj` are not in that list — they are the frozen algebraic interface of the Spin core.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace SpinNative

open CechSpinLift CechZ2 CechSpinZ2 NullSectorTask28

universe u v w t

/-- **NEWLY DEFINED (Task 31), the packaged handoff object.**  A canonical Spin seed: a
central double cover, a Čech cover of an already given base, and coherent Spin-native gluing
data on it.  Everything else — the projected visible cocycle, the canonical Spin structure,
the triviality of the standard obstruction and the uniqueness statements — is *derived* from
these three fields by the theorems below, so the package adds no unproved content. -/
structure CanonicalSpinSeed (L : Type u) (G : Type v) [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] [Group G] [TopologicalSpace G] (X : Type w) [TopologicalSpace X]
    (ι : Type t) where
  /-- **EXTERNAL INPUT, still required.**  The Čech cover of the already given base `X`. -/
  cover : CechCover X ι
  /-- The frozen central double-cover interface `ρ : L → G`. -/
  proj : InternalProjection L G
  /-- The primitive datum: coherent Spin-native gluing data. -/
  native : NativeSpinTransitionData L cover

namespace CanonicalSpinSeed

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}
  (s : CanonicalSpinSeed L G X ι)

/-- The visible (`SO`/Lorentz-valued) transition cocycle obtained by projecting the primitive
Spin datum through `ρ`.  Derived; no choice. -/
def projected : VisibleCocycle G s.cover := project s.proj s.native

/-- **U1.**  The distinguished Spin structure of the seed, over its own projection. -/
def canonical : SpinStructureOver s.proj s.projected :=
  canonicalSpinStructure s.proj s.native

@[simp] theorem canonical_data : s.canonical.data = s.native := rfl

/-- **Task 30, re-exported.**  The *existing standard* Spin-lift obstruction of the projected
data is trivial, for every family of local Spin lifts. -/
theorem obstruction_trivial (D : SpinLiftFamily s.proj s.projected) :
    D.obstruction = trivialClass s.proj s.cover :=
  projected_obstruction_trivial_of_lifts s.proj s.native D

/-- **U2.**  The primitive datum is recovered from the canonical Spin structure, and the
canonical structure is the unique Spin structure over `projected` carrying it. -/
theorem canonical_unique (C : SpinStructureOver s.proj s.projected) (h : C.data = s.native) :
    C = s.canonical :=
  canonicalSpinStructure_unique s.proj s.native C h

/-- **Task 31, the residual freedom.**  Every Spin structure over the projected data is a
kernel twist of the canonical one. -/
theorem residual_freedom (C : SpinStructureOver s.proj s.projected) :
    ∃ ε : KerCocycle s.proj s.cover, twist s.native ε = C.data :=
  s.canonical.exists_twist C

/-- **U3–U4.**  Under the explicit fixed-cover `H¹`-type gate, the Spin structure of the seed
is unique up to gauge equivalence. -/
theorem unique_up_to_gauge_of_gate (hgate : KernelTwistsGaugeTrivial s.proj s.cover)
    (C : SpinStructureOver s.proj s.projected) : GaugeEquiv s.proj s.native C.data :=
  gaugeEquiv_canonical_of_kernelTwistsGaugeTrivial hgate s.native C

/-- **U3–U4, cohomological form.**  On a cover with preconnected double overlaps whose Čech
`Ȟ¹(𝓤;ℤ₂)` vanishes (with respect to a kernel dictionary `ker ρ ≅ ℤ₂`), the Spin structure of
the seed is unique up to gauge equivalence.  `H1 s.cover.U` is the cohomology of the nerve of
the *given* cover; it is not identified here with `H¹(X;ℤ₂)`. -/
theorem unique_up_to_gauge_of_cover_H1_trivial (S : KernelSign s.proj)
    (hpre : ∀ i j, IsPreconnected (s.cover.overlap₂ i j)) (hH1 : ∀ h : H1 s.cover.U, h = 0)
    (C : SpinStructureOver s.proj s.projected) : GaugeEquiv s.proj s.native C.data :=
  s.unique_up_to_gauge_of_gate (kernelTwistsGaugeTrivial_of_cover_H1_trivial S hpre hH1) C

/-- **The packaged Task-31 endpoint.**  For a canonical Spin seed:

1. the canonical Spin structure carries exactly the primitive datum (U1, U2);
2. the standard obstruction of the projected data is trivial for every choice of local Spin
   lifts (Task 30);
3. every competitor over the same projected data is a kernel twist (residual freedom);
4. under the explicit gate every competitor is gauge equivalent to it, and the gauge quotient
   is a subsingleton (U3, U4). -/
theorem seed_certificate :
    s.canonical.data = s.native ∧
    (∀ D : SpinLiftFamily s.proj s.projected, D.obstruction = trivialClass s.proj s.cover) ∧
    (∀ C : SpinStructureOver s.proj s.projected,
        ∃ ε : KerCocycle s.proj s.cover, twist s.native ε = C.data) ∧
    (KernelTwistsGaugeTrivial s.proj s.cover →
        (∀ C : SpinStructureOver s.proj s.projected, GaugeEquiv s.proj s.native C.data) ∧
        Subsingleton (GaugeClass s.proj s.projected)) :=
  ⟨rfl, fun D => s.obstruction_trivial D, fun C => s.residual_freedom C,
   fun hgate => ⟨fun C => s.unique_up_to_gauge_of_gate hgate C,
     subsingleton_gaugeClass hgate s.projected⟩⟩

end CanonicalSpinSeed

end SpinNative

/-! ## Axiom audit of the Task-31 endpoints -/

#print axioms SpinNative.KerCocycle
#print axioms SpinNative.twist
#print axioms SpinNative.project_twist
#print axioms SpinNative.ratio
#print axioms SpinNative.exists_kerCocycle_twist_eq
#print axioms SpinNative.native_kernel_torsor
#print axioms SpinNative.GaugeEquiv
#print axioms SpinNative.gaugeEquiv_iff_twist_isGaugeTrivial
#print axioms SpinNative.canonicalSpinStructure
#print axioms SpinNative.subsingleton_native_output
#print axioms SpinNative.NoNontrivialKernelTwist
#print axioms SpinNative.KernelTwistsGaugeTrivial
#print axioms SpinNative.data_eq_on_overlaps_of_noNontrivialKernelTwist
#print axioms SpinNative.gaugeEquiv_of_kernelTwistsGaugeTrivial
#print axioms SpinNative.subsingleton_gaugeClass
#print axioms SpinNative.native_uniqueness_summary
#print axioms SpinNative.d_kerCocycleCochain
#print axioms SpinNative.kernelTwistsGaugeTrivial_of_cover_H1_trivial
#print axioms SpinNative.spinStructure_unique_up_to_gauge_of_cover_H1_trivial
#print axioms SpinNative.CanonicalSpinSeed.seed_certificate
