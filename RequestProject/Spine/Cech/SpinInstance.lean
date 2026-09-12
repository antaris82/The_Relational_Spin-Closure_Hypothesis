import RequestProject.Spine.Cech.Comparison
import RequestProject.Spine.Cech.SpinKernelSign

/-!
# Task 6 : the intrinsic Spin instance and the Lorentz-frame instance

Everything in `SpinCocycle.lean` and `Comparison.lean` is stated for an arbitrary internal
projection `P` with a kernel dictionary `KernelSign P`.  This module instantiates it twice:

* with the **native intrinsic Spin projection** `SpinCore.internalSpinProjection`, whose kernel
  is the exact `{±1} = {1, negOneSpin}` of the Task-1/Task-2 spin cover, giving
  `CechSpinZ2.spinLiftCechClass : Ȟ²(𝓤;ℤ₂)`;
* with the **Lorentz frame data** of Task 4, giving `CechSpinZ2.frameCechClass` and the
  Task-4 vanishing theorem in standard Čech language:
  `[z]_frame = 0 ↔ the frame data admits a Spin structure`.

No new mathematics is introduced here; these are the instantiations of the generic theorems.

**Interpretation boundary (unchanged).**  `[z]_frame` is a fixed-cover topological Spin-lift
obstruction.  It is *not* asserted to be `w₂(TM)`, and it is not curvature, torsion, holonomy,
a synchronization mismatch or any dynamical quantity.
-/

noncomputable section

namespace CechSpinZ2

open SpinCore CechSpinLift CechZ2 LorentzFrames NullSectorTask28

universe w t u v

/-! ## The intrinsic Spin instance -/

variable {X : Type w} [TopologicalSpace X] {ι : Type t} {𝓤 : CechCover X ι}
  {T : VisibleCocycle (↥GLor) 𝓤}

/-- **Task-6 principal endpoint, Spin case.**  The Spin-lift obstruction of Task 3 as a genuine
class in fixed-cover Čech cohomology, `[z] ∈ Ȟ²(𝓤;ℤ₂)`. -/
def spinLiftCechClass {D : SpinLiftFamily internalSpinProjection T}
    (V : ConstOn₃ 𝓤 D.defect) : H2 𝓤.U :=
  spinCechClass spinKernelSign V

/-- The value of the class' representative is the Task-4 sign of the Task-3 defect: this is the
translation `{±1} → ℤ₂` applied to `c_ijk`, nothing else. -/
theorem spinLiftCechCochain_apply {D : SpinLiftFamily internalSpinProjection T}
    (V : ConstOn₃ 𝓤 D.defect) (σ : Nerve 𝓤.U 2) {x : X}
    (hx : x ∈ 𝓤.overlap₃ (σ.idx 0) (σ.idx 1) (σ.idx 2)) :
    zCochain spinKernelSign V σ = spinSign (D.defect (σ.idx 0) (σ.idx 1) (σ.idx 2) x) :=
  zCochain_apply spinKernelSign V σ hx

/-- `δ_Č z = 0` for the intrinsic Spin defect. -/
theorem d_spinLiftCechCochain {D : SpinLiftFamily internalSpinProjection T}
    (V : ConstOn₃ 𝓤 D.defect) : d 𝓤.U 2 (zCochain spinKernelSign V) = 0 :=
  d_zCochain spinKernelSign V

/-- The Spin class does not depend on the chosen local lifts. -/
theorem spinLiftCechClass_lift_independent
    (hpre : ∀ i j, IsPreconnected (𝓤.overlap₂ i j))
    (D D' : SpinLiftFamily internalSpinProjection T) (V : ConstOn₃ 𝓤 D.defect)
    (V' : ConstOn₃ 𝓤 D'.defect) : spinLiftCechClass V' = spinLiftCechClass V :=
  spinCechClass_lift_independent_of_preconnected spinKernelSign hpre D D' V V'

/-- Vanishing iff coherent Spin transition data exist. -/
theorem spinLiftCechClass_eq_zero_iff_exists_coherent
    (hpre : ∀ i j, IsPreconnected (𝓤.overlap₂ i j))
    {D : SpinLiftFamily internalSpinProjection T} (V : ConstOn₃ 𝓤 D.defect) :
    spinLiftCechClass V = 0 ↔ ∃ D' : SpinLiftFamily internalSpinProjection T, D'.IsCoherent :=
  spinCechClass_eq_zero_iff_exists_coherent spinKernelSign hpre V

/-- The canonical comparison with the Task-3 class, in the Spin case. -/
theorem toObstruction_spinLiftCechClass {D : SpinLiftFamily internalSpinProjection T}
    (V : ConstOn₃ 𝓤 D.defect) :
    toObstruction spinKernelSign 𝓤 (spinLiftCechClass V) = D.obstruction :=
  toObstruction_spinCechClass spinKernelSign V

/-! ## The Lorentz-frame instance (Task-4 data) -/

variable {M : Type u} [TopologicalSpace M] {Fib : M → Type v}
  [∀ x, AddCommGroup (Fib x)] [∀ x, Module ℝ (Fib x)] {Φ : LorentzFrameData M Fib ι}

/-- **Task-6 endpoint for the Task-4 frame data.**  The Lorentz-frame Spin-lift obstruction as a
genuine class in `Ȟ²(𝓤;ℤ₂)` for the frame cover. -/
def frameCechClass {D : FrameSpinLifts Φ} (V : ConstOn₃ Φ.cover D.defect) :
    H2 Φ.cover.U :=
  spinCechClass spinKernelSign V

/-- **Task-6 endpoint.**  On a frame cover with preconnected double overlaps, the genuine Čech
class of the frame data vanishes **iff** the frame data admits a Spin structure.  This is the
Task-4 criterion, now consuming the standard Čech quotient. -/
theorem frameCechClass_eq_zero_iff_spinStructure
    (hpre : ∀ i j, IsPreconnected (Φ.cover.overlap₂ i j)) {D : FrameSpinLifts Φ}
    (V : ConstOn₃ Φ.cover D.defect) :
    frameCechClass V = 0 ↔ Nonempty (SpinFrameStructure Φ) := by
  rw [frameCechClass, spinCechClass_eq_zero_iff_exists_coherent spinKernelSign hpre V,
    ← LorentzFrameData.nonempty_spinFrameStructure_iff_exists_coherent]

/-- The frame Čech class maps onto the Task-4 frame obstruction class under the canonical
comparison map of WP9. -/
theorem toObstruction_frameCechClass {D : FrameSpinLifts Φ}
    (V : ConstOn₃ Φ.cover D.defect) :
    toObstruction spinKernelSign Φ.cover (frameCechClass V) = LorentzFrameData.frameObstruction D :=
  toObstruction_spinCechClass spinKernelSign V

end CechSpinZ2
