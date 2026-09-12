import RequestProject.Spine.Comparison.SpinNativeVsSO
import RequestProject.Spine.Comparison.KernelTwistCohomology
import RequestProject.Spine.Cech.SpinKernelSign

/-!
# Spine / Comparison : the Task-31 uniqueness gate on the Lorentz-frame Spin structures

This comparison module connects the generic Spin-native uniqueness layer
(`RequestProject.Spine.SpinNative.KernelTwist`, `…GaugeEquivalence`, `…Canonical`,
`…Rigidity`) with the pre-existing, unmodified Lorentz-frame presentation of a Spin structure
(`LorentzFrames.SpinFrameStructure` of `RequestProject.Spine.Geometry.SpinStructure`).

## No duplicated cocycle theory

`LorentzFrames.KerCocycle₁ Φ` (Task 4, WP8) and `SpinNative.KerCocycle P 𝓤` (Task 31) are the
*same* structure, the former being the latter at the intrinsic Spin projection and the frame
cover: `LorentzFrames.KerCocycle₁.toNative` and `LorentzFrames.KerCocycle₁.ofNative` are
mutually inverse and preserve the twist (`LorentzFrames.toNative_twist`).  The Task-31
uniqueness statements therefore *apply to* the Task-4 Spin structures rather than replacing
them.

## What is proved here

* `LorentzFrames.SpinFrameStructure.toSpinStructureOver` — a Spin structure on Lorentz frame
  data is a Spin structure over the frame transition cocycle in the Spin-native sense;
* `LorentzFrames.spinFrameStructure_eq_on_overlaps_of_rigid` — under strict rigidity two Spin
  structures on the same frame data agree on every double overlap;
* `LorentzFrames.spinFrameStructure_gaugeEquiv_of_gate` — under the fixed-cover `H¹`-type
  gate they are gauge equivalent;
* `LorentzFrames.spinFrameStructure_gaugeEquiv_of_cover_H1_trivial` — the same conclusion
  from the vanishing of the project's own Čech `Ȟ¹(𝓤;ℤ₂)` of the frame cover, on a cover
  with preconnected double overlaps, using the frozen kernel dictionary
  `CechSpinZ2.spinKernelSign`.

Nothing here claims uniqueness unconditionally: the negative control
`LorentzFrames.Control.two_distinct_spinFrameStructures` (Task 4) and
`SpinNativeControl.two_distinct_native_spin_structures` (Task 31) exhibit two distinct Spin
structures over the same projected data on a two-patch cover.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace LorentzFrames

open SpinCore CechSpinLift CechZ2 CechSpinZ2 SpinNative NullSectorTask28

universe u v t

variable {M : Type u} [TopologicalSpace M] {Fib : M → Type v}
  [∀ x, AddCommGroup (Fib x)] [∀ x, Module ℝ (Fib x)] {ι : Type t}
  {Φ : LorentzFrameData M Fib ι}

/-! ## The Task-4 kernel cocycles are the Task-31 kernel cocycles -/

/-- **AUDIT (Task 31), no new mathematics.**  A Lorentz-frame `{±1}`-valued Čech 1-cocycle is
a Spin-native kernel 1-cocycle for the intrinsic projection on the frame cover. -/
def KerCocycle₁.toNative (ε : KerCocycle₁ Φ) :
    SpinNative.KerCocycle internalSpinProjection Φ.cover where
  e := ε.e
  isKer := ε.isKer
  cocycle := ε.cocycle

/-- The inverse passage. -/
def KerCocycle₁.ofNative (ε : SpinNative.KerCocycle internalSpinProjection Φ.cover) :
    KerCocycle₁ Φ where
  e := ε.e
  isKer := ε.isKer
  cocycle := ε.cocycle

@[simp] theorem KerCocycle₁.toNative_e (ε : KerCocycle₁ Φ) (i j : ι) :
    ε.toNative.e i j = ε.e i j := rfl

theorem KerCocycle₁.ofNative_toNative (ε : KerCocycle₁ Φ) :
    KerCocycle₁.ofNative ε.toNative = ε := rfl

theorem KerCocycle₁.toNative_ofNative
    (ε : SpinNative.KerCocycle internalSpinProjection Φ.cover) :
    (KerCocycle₁.ofNative (Φ := Φ) ε).toNative = ε := rfl

/-- **AUDIT (Task 31).**  The Task-4 twist of a Spin structure and the Task-31 twist of its
Spin-native data are the same operation. -/
theorem toNative_twist (S : SpinFrameStructure Φ) (ε : KerCocycle₁ Φ) :
    (S.twist ε).toNative = SpinNative.twist S.toNative ε.toNative := rfl

/-! ## Lorentz-frame Spin structures as Spin structures over the frame cocycle -/

/-- **NEWLY DEFINED (Task 31).**  A Spin structure on Lorentz frame data, read as a Spin
structure over the frame transition cocycle in the Spin-native presentation. -/
def SpinFrameStructure.toSpinStructureOver (S : SpinFrameStructure Φ) :
    SpinStructureOver internalSpinProjection Φ.frameCocycle where
  data := S.toNative
  projects i j x hx := S.projects i j x hx

@[simp] theorem SpinFrameStructure.toSpinStructureOver_data (S : SpinFrameStructure Φ) :
    S.toSpinStructureOver.data = S.toNative := rfl

/-! ## The uniqueness gate, transported -/

/-- **DERIVED_NATIVE (Task 31), Lorentz-frame instance of endpoint U3 (strict form).**  Under
the strict rigidity condition on the frame cover, two Spin structures on the same Lorentz
frame data have the same Spin transition maps on every double overlap. -/
theorem spinFrameStructure_eq_on_overlaps_of_rigid
    (hrig : NoNontrivialKernelTwist internalSpinProjection Φ.cover)
    (S S' : SpinFrameStructure Φ) (i j : ι) {x : M} (hx : x ∈ Φ.cover.overlap₂ i j) :
    S'.s i j x = S.s i j x :=
  data_eq_on_overlaps_of_noNontrivialKernelTwist hrig S.toSpinStructureOver
    S'.toSpinStructureOver i j hx

/-- **DERIVED_NATIVE (Task 31), Lorentz-frame instance of endpoint U3 (gauge form).**  Under
the fixed-cover `H¹`-type gate, any two Spin structures on the same Lorentz frame data are
gauge equivalent. -/
theorem spinFrameStructure_gaugeEquiv_of_gate
    (hgate : KernelTwistsGaugeTrivial internalSpinProjection Φ.cover)
    (S S' : SpinFrameStructure Φ) :
    GaugeEquiv internalSpinProjection S.toNative S'.toNative :=
  gaugeEquiv_of_kernelTwistsGaugeTrivial hgate S.toSpinStructureOver S'.toSpinStructureOver

/-- **DERIVED_NATIVE (Task 31), PRINCIPAL Lorentz-frame endpoint — the cohomological gate.**
On a frame cover with preconnected double overlaps whose first Čech `ℤ₂`-cohomology vanishes,
any two Spin structures on the same Lorentz frame data are gauge equivalent.

`CechZ2.H1 Φ.cover.U` is the Čech cohomology of the **nerve of the chosen cover**; it is not
identified in this project with `H¹(M;ℤ₂)`. -/
theorem spinFrameStructure_gaugeEquiv_of_cover_H1_trivial
    (hpre : ∀ i j, IsPreconnected (Φ.cover.overlap₂ i j))
    (hH1 : ∀ h : H1 Φ.cover.U, h = 0) (S S' : SpinFrameStructure Φ) :
    GaugeEquiv internalSpinProjection S.toNative S'.toNative :=
  spinFrameStructure_gaugeEquiv_of_gate
    (kernelTwistsGaugeTrivial_of_cover_H1_trivial spinKernelSign hpre hH1) S S'

end LorentzFrames

/-! ## Axiom audit of the Lorentz-frame endpoints -/

#print axioms LorentzFrames.KerCocycle₁.toNative
#print axioms LorentzFrames.toNative_twist
#print axioms LorentzFrames.SpinFrameStructure.toSpinStructureOver
#print axioms LorentzFrames.spinFrameStructure_eq_on_overlaps_of_rigid
#print axioms LorentzFrames.spinFrameStructure_gaugeEquiv_of_gate
#print axioms LorentzFrames.spinFrameStructure_gaugeEquiv_of_cover_H1_trivial
