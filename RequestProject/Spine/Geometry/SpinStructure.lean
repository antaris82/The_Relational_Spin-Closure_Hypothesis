import RequestProject.Spine.Geometry.FrameField
import RequestProject.Spine.E2.Cech.SpinInstance

/-!
# Task 4, WP4–WP5 and WP8 : the Lorentz-frame Spin-lift obstruction and Spin structures

This module feeds the Lorentz frame transition cocycle of
`RequestProject.Spine.Geometry.FrameField` into the abstract Task-3 obstruction machinery,
defines the conventional (Čech-presented) notion of a Spin structure on that frame data, and
proves the equivalence

`[c]_frame = 0  ↔  a Spin structure on the Lorentz frame data exists`.

## Naming discipline (mandatory)

The class constructed here is called the **Lorentz-frame Spin-lift obstruction**.  It is
*not* called `w₂(TM)`; see `RequestProject.Spine.Geometry.Core` and `TASK04_AUDIT.md` for the
exact status of that identification.

## The three levels of nonuniqueness (WP10)

* a **choice of local frames** — the field `frame` of `LorentzFrameData`;
* a **choice of local Spin representatives** — a `FrameSpinLifts Φ`, i.e. a `SpinLiftFamily`;
  the defect depends on it, the class does not (`frameObstruction_choice_independent`);
* a **Spin structure** — a `SpinFrameStructure Φ`, i.e. a coherent Spin-valued transition
  cocycle;
* **existence** of a Spin structure — `Nonempty (SpinFrameStructure Φ)`, the only thing the
  vanishing of the obstruction is equivalent to.

WP8 is the torsor statement, proved here at the level of Čech cocycles on the fixed cover:
the difference of two Spin structures is a continuous `{±1}`-valued Čech 1-cocycle, and
twisting by such a cocycle produces a Spin structure again; the two operations are mutually
inverse (`ratio_twist`, `twist_ratio`).
-/

noncomputable section

namespace LorentzFrames

open SpinCore CechSpinLift NullSectorTask28

universe u v t

variable {M : Type u} [TopologicalSpace M] {Fib : M → Type v}
  [∀ x, AddCommGroup (Fib x)] [∀ x, Module ℝ (Fib x)] {ι : Type t}

/-! ## WP4 — the Task-3 obstruction on the Lorentz frame cocycle -/

/-- **NEWLY DEFINED (WP4).**  A family of continuous local Spin representatives of the
Lorentz frame transition cocycle: the Task-3 `SpinLiftFamily` for the native intrinsic Spin
projection and the frame cocycle. -/
abbrev FrameSpinLifts (Φ : LorentzFrameData M Fib ι) : Type _ :=
  SpinLiftFamily internalSpinProjection Φ.frameCocycle

namespace LorentzFrameData

variable {Φ : LorentzFrameData M Fib ι}

/-- **DERIVED_NATIVE (WP4).**  The triple-overlap defect of the Lorentz frame data is
`{±1}`-valued: it lies in the exact intrinsic kernel of the native Spin projection. -/
theorem frame_defect_eq_pm_one (D : FrameSpinLifts Φ) (i j k : ι) {x : M}
    (hx : x ∈ Φ.cover.overlap₃ i j k) :
    D.defect i j k x = 1 ∨ D.defect i j k x = negOneSpin :=
  cech_defect_eq_pm_one D i j k hx

/-- **NEWLY DEFINED (WP4), principal — the Lorentz-frame Spin-lift obstruction.**  The
Task-3 fixed-cover obstruction class of the Lorentz frame transition cocycle. -/
def frameObstruction (D : FrameSpinLifts Φ) :
    ObstructionClass internalSpinProjection Φ.cover :=
  D.obstruction

/-- **DERIVED_NATIVE (WP4).**  The Lorentz-frame Spin-lift obstruction does not depend on
the chosen family of local Spin representatives. -/
theorem frameObstruction_choice_independent (D D' : FrameSpinLifts Φ) :
    frameObstruction D = frameObstruction D' :=
  D.obstruction_lift_independent D'

end LorentzFrameData

/-! ## WP5 — Spin structures on the Lorentz frame data -/

/-- **NEWLY DEFINED (WP5), principal.**  A *Spin structure on the Lorentz frame data*, in
the Čech presentation attached to the chosen cover: a continuous `Spin`-valued transition
cocycle lifting the `GLor`-valued Lorentz frame transition cocycle along the native
projection `SpinGroup → GLor`.

This is the cocycle description of a lift of the oriented, time-oriented orthonormal frame
bundle along `Spin⁺(1,3) → SO⁺(1,3)`; the total-space (principal-bundle) description is not
available in the pinned library and is classified in `TASK04_AUDIT.md`. -/
structure SpinFrameStructure (Φ : LorentzFrameData M Fib ι) where
  /-- The Spin-valued transition functions. -/
  s : ι → ι → (M → ↥SpinGroup)
  /-- They are continuous on the double overlaps. -/
  continuousOn_s : ∀ i j, ContinuousOn (s i j) (Φ.cover.overlap₂ i j)
  /-- They lift the Lorentz frame transition functions. -/
  projects : ∀ i j, ∀ x ∈ Φ.cover.overlap₂ i j, spinCover (s i j x) = Φ.transition i j x
  /-- They satisfy the exact Čech 1-cocycle law. -/
  cocycle : ∀ i j k, ∀ x ∈ Φ.cover.overlap₃ i j k, s i j x * s j k x = s i k x

namespace SpinFrameStructure

variable {Φ : LorentzFrameData M Fib ι}

/-- A Spin structure is in particular a coherent family of local Spin representatives. -/
def toSpinLifts (S : SpinFrameStructure Φ) : FrameSpinLifts Φ where
  lift := S.s
  isRep i j := ⟨S.continuousOn_s i j, fun x hx => S.projects i j x hx⟩

theorem toSpinLifts_isCoherent (S : SpinFrameStructure Φ) : S.toSpinLifts.IsCoherent :=
  S.cocycle

/-- Conversely, a coherent family of local Spin representatives is a Spin structure. -/
def ofCoherent {D : FrameSpinLifts Φ} (h : D.IsCoherent) : SpinFrameStructure Φ where
  s := D.lift
  continuousOn_s i j := (D.isRep i j).1
  projects i j x hx := (D.isRep i j).2 x hx
  cocycle := h

end SpinFrameStructure

namespace LorentzFrameData

variable {Φ : LorentzFrameData M Fib ι}

/-- **DERIVED_NATIVE (WP5), principal.**  Coherent Spin-valued frame transition data and
Spin structures on the Lorentz frame data are the same thing. -/
theorem nonempty_spinFrameStructure_iff_exists_coherent :
    Nonempty (SpinFrameStructure Φ) ↔ ∃ D : FrameSpinLifts Φ, D.IsCoherent :=
  ⟨fun ⟨S⟩ => ⟨S.toSpinLifts, S.toSpinLifts_isCoherent⟩,
   fun ⟨_, h⟩ => ⟨SpinFrameStructure.ofCoherent h⟩⟩

/-- **DERIVED_NATIVE (WP4+WP5), principal endpoint of Task 4.**  The Lorentz-frame Spin-lift
obstruction of an oriented, time-oriented Lorentzian frame datum vanishes **iff** the frame
data admits a Spin structure.

The statement quantifies over an arbitrary family `D` of local Spin representatives; by
`frameObstruction_choice_independent` the class is the same for all of them, so the
criterion is a property of the frame data (and the chosen cover) alone. -/
theorem frameObstruction_eq_trivial_iff_spinStructure (D : FrameSpinLifts Φ) :
    frameObstruction D = trivialClass internalSpinProjection Φ.cover ↔
      Nonempty (SpinFrameStructure Φ) := by
  rw [nonempty_spinFrameStructure_iff_exists_coherent]
  exact D.obstruction_eq_trivialClass_iff_exists_coherent

end LorentzFrameData

/-! ## WP8 — the `{±1}`-valued Čech 1-cocycles and the torsor statement -/

/-- **NEWLY DEFINED (WP8).**  A continuous `{±1}`-valued Čech 1-cocycle on the cover of the
frame data: the group through which Spin structures on a fixed cover differ. -/
structure KerCocycle₁ (Φ : LorentzFrameData M Fib ι) where
  /-- The kernel-valued functions. -/
  e : ι → ι → (M → ↥SpinGroup)
  /-- Continuity and kernel-valuedness on the double overlaps. -/
  isKer : ∀ i j, internalSpinProjection.IsKerFunOn (Φ.cover.overlap₂ i j) (e i j)
  /-- The exact Čech 1-cocycle law. -/
  cocycle : ∀ i j k, ∀ x ∈ Φ.cover.overlap₃ i j k, e i j x * e j k x = e i k x

namespace KerCocycle₁

variable {Φ : LorentzFrameData M Fib ι}

/-- **DERIVED_NATIVE (WP8).**  The values of such a cocycle really are `±1`. -/
theorem eq_pm_one (ε : KerCocycle₁ Φ) (i j : ι) {x : M} (hx : x ∈ Φ.cover.overlap₂ i j) :
    ε.e i j x = 1 ∨ ε.e i j x = negOneSpin :=
  (mem_ker_spinCover_iff _).1 ((ε.isKer i j).2 x hx)

end KerCocycle₁

namespace SpinFrameStructure

variable {Φ : LorentzFrameData M Fib ι}

/-- **NEWLY DEFINED (WP8).**  The ratio of two Spin structures on the same frame data. -/
def ratioFun (S S' : SpinFrameStructure Φ) : ι → ι → (M → ↥SpinGroup) :=
  fun i j x => S'.s i j x * (S.s i j x)⁻¹

/-- **DERIVED_NATIVE (WP8).**  The ratio of two Spin structures is a continuous
`{±1}`-valued Čech 1-cocycle. -/
def ratio (S S' : SpinFrameStructure Φ) : KerCocycle₁ Φ where
  e := ratioFun S S'
  isKer i j := by
    refine ⟨((S'.continuousOn_s i j).mul ((S.continuousOn_s i j).inv)), fun x hx => ?_⟩
    rw [InternalProjection.mem_Ker_iff]
    show spinCover (S'.s i j x * (S.s i j x)⁻¹) = 1
    rw [map_mul, map_inv, S.projects i j x hx, S'.projects i j x hx, mul_inv_cancel]
  cocycle i j k x hx := by
    have hjk : x ∈ Φ.cover.overlap₂ j k := Φ.cover.overlap₃_subset_jk i j k hx
    have hkerjk : S'.s j k x * (S.s j k x)⁻¹ ∈ internalSpinProjection.Ker := by
      rw [InternalProjection.mem_Ker_iff]
      show spinCover (S'.s j k x * (S.s j k x)⁻¹) = 1
      rw [map_mul, map_inv, S.projects j k x hjk, S'.projects j k x hjk, mul_inv_cancel]
    have hcomm := internalSpinProjection.ker_central _ hkerjk (S.s i j x)⁻¹
    show S'.s i j x * (S.s i j x)⁻¹ * (S'.s j k x * (S.s j k x)⁻¹)
        = S'.s i k x * (S.s i k x)⁻¹
    calc S'.s i j x * (S.s i j x)⁻¹ * (S'.s j k x * (S.s j k x)⁻¹)
        = S'.s i j x * ((S.s i j x)⁻¹ * (S'.s j k x * (S.s j k x)⁻¹)) := by
          rw [mul_assoc]
      _ = S'.s i j x * ((S'.s j k x * (S.s j k x)⁻¹) * (S.s i j x)⁻¹) := by rw [← hcomm]
      _ = (S'.s i j x * S'.s j k x) * ((S.s i j x * S.s j k x)⁻¹) := by
          rw [mul_inv_rev]; group
      _ = S'.s i k x * (S.s i k x)⁻¹ := by
          rw [S.cocycle i j k x hx, S'.cocycle i j k x hx]

/-- **NEWLY DEFINED (WP8).**  Twisting a Spin structure by a `{±1}`-valued Čech 1-cocycle. -/
def twist (S : SpinFrameStructure Φ) (ε : KerCocycle₁ Φ) : SpinFrameStructure Φ where
  s i j x := ε.e i j x * S.s i j x
  continuousOn_s i j := (ε.isKer i j).1.mul (S.continuousOn_s i j)
  projects i j x hx := by
    have hker : spinCover (ε.e i j x) = 1 := (ε.isKer i j).2 x hx
    rw [map_mul, hker, one_mul, S.projects i j x hx]
  cocycle i j k x hx := by
    have hjk : x ∈ Φ.cover.overlap₂ j k := Φ.cover.overlap₃_subset_jk i j k hx
    have hcomm := internalSpinProjection.ker_central _ ((ε.isKer j k).2 x hjk) (S.s i j x)
    show ε.e i j x * S.s i j x * (ε.e j k x * S.s j k x) = ε.e i k x * S.s i k x
    calc ε.e i j x * S.s i j x * (ε.e j k x * S.s j k x)
        = ε.e i j x * (S.s i j x * ε.e j k x) * S.s j k x := by group
      _ = ε.e i j x * (ε.e j k x * S.s i j x) * S.s j k x := by rw [← hcomm]
      _ = (ε.e i j x * ε.e j k x) * (S.s i j x * S.s j k x) := by group
      _ = ε.e i k x * S.s i k x := by
          rw [ε.cocycle i j k x hx, S.cocycle i j k x hx]

/-- **DERIVED_NATIVE (WP8).**  Twisting by the ratio recovers the second Spin structure. -/
theorem twist_ratio (S S' : SpinFrameStructure Φ) (i j : ι) (x : M) :
    (S.twist (S.ratio S')).s i j x = S'.s i j x := by
  show (S'.s i j x * (S.s i j x)⁻¹) * S.s i j x = S'.s i j x
  group

/-- **DERIVED_NATIVE (WP8).**  The ratio of a twist is the twisting cocycle. -/
theorem ratio_twist (S : SpinFrameStructure Φ) (ε : KerCocycle₁ Φ) (i j : ι) (x : M) :
    (S.ratio (S.twist ε)).e i j x = ε.e i j x := by
  show (ε.e i j x * S.s i j x) * (S.s i j x)⁻¹ = ε.e i j x
  group

/-- **WP8, packaged endpoint (fixed cover, cocycle level).**  When a Spin structure exists,
the Spin structures on the fixed cover form a *torsor* under the group of continuous
`{±1}`-valued Čech 1-cocycles: the difference of two of them is such a cocycle, twisting by
a cocycle gives a Spin structure, and the two constructions are mutually inverse.

In particular the vanishing of the Lorentz-frame Spin-lift obstruction does **not** single
out a Spin structure. -/
theorem spinStructure_torsor (S : SpinFrameStructure Φ) :
    (∀ S' : SpinFrameStructure Φ, ∀ i j, ∀ x, (S.twist (S.ratio S')).s i j x = S'.s i j x) ∧
    (∀ ε : KerCocycle₁ Φ, ∀ i j, ∀ x, (S.ratio (S.twist ε)).e i j x = ε.e i j x) :=
  ⟨fun S' i j x => twist_ratio S S' i j x, fun ε i j x => ratio_twist S ε i j x⟩

end SpinFrameStructure

end LorentzFrames
