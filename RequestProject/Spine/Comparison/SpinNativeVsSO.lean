import RequestProject.Spine.SpinNative.Projection
import RequestProject.Spine.E2.Cech.Obstruction
import RequestProject.Spine.Geometry.SpinStructure

/-!
# Spine / Comparison : the Spin-native branch against the standard `SO`-lift branch

This is the **only** module in which the two branches of the Stage-1.3 architecture meet.

```
   Branch A (standard control path, unchanged)      Branch B (Spin-native, Task 30)
   ------------------------------------------      -------------------------------
   visible SO-valued transition data                Spin-native transition data g̃_ij
            ↓  local Spin lifts (choice)                     ↓  ρ = P.proj
   triple-overlap defect c_ijk ∈ ker ρ              visible SO-valued transition data
            ↓                                                ↓  g̃ used as its own lift
   Čech class [c]                                   defect ≡ 1, hence [c] = 1
            ↓
   coherent Spin lift iff [c] = 1
```

Neither branch is a prerequisite of the other: `RequestProject.Spine.SpinNative.*` imports
no defect, coboundary or obstruction module, and the standard branch imports nothing from
`SpinNative`.  This module imports both, and no production module imports this module.

## What is proved

* `SpinNative.nativeLiftFamily` — Spin-native data are, tautologically, a family of local
  Spin lifts of their own projection: the standard branch can be *run* on the projected data
  with `g̃_ij` itself as the chosen lift.  No `SO → Spin` reconstruction step, no local
  section of `ρ` and no lift-admissibility hypothesis is needed.
* `SpinNative.nativeLiftFamily_defect_eq_one`, `SpinNative.nativeLiftFamily_isCoherent` —
  the standard triple-overlap defect of that family is identically `1`.
* `SpinNative.projected_obstruction_trivial` and
  `SpinNative.projected_obstruction_trivial_of_lifts` — the **existing standard obstruction**
  (`CechSpinLift.SpinLiftFamily.obstruction`, unmodified) of the projected data is the
  trivial class, for the tautological family and hence, by the frozen choice-independence
  theorem, for *every* family of local lifts of the projected data.
* `SpinCore.spin_projected_obstruction_trivial` — the same statement for the native
  intrinsic Spin/Lorentz projection.
* `LorentzFrames.SpinFrameStructure.toNative` and `LorentzFrames.project_twist` — the
  Lorentz-frame instantiation, together with the information-loss statement: twisting a Spin
  structure by a `{±1}`-valued Čech 1-cocycle does not change its projection on the
  overlaps.

## What is **not** proved

Nothing here classifies Spin structures, and nothing here says that a vanishing standard
obstruction recovers Spin-native provenance: the standard branch gives *existence* of a
coherent lift, not the statement that it came from Spin-native data.  No identification with
`w₂(TM)` is made or attempted.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace SpinNative

open CechSpinLift NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}
  {𝓤 : CechCover X ι}

/-! ## The comparison: Spin-native data as a family of local lifts of their projection -/

/-- **NEWLY DEFINED (Task 30), principal — the comparison arrow.**  Spin-native transition
data are a family of local Spin lifts of their own projection, with no choice made: the
projection condition `ρ (g̃_ij x) = g_ij x` holds by definition of `project`. -/
def nativeLiftFamily (P : InternalProjection L G) (S : NativeSpinTransitionData L 𝓤) :
    SpinLiftFamily P (project P S) where
  lift := S.g
  isRep i j := ⟨S.continuousOn_g i j, fun _ _ => rfl⟩

@[simp] theorem nativeLiftFamily_lift (P : InternalProjection L G)
    (S : NativeSpinTransitionData L 𝓤) (i j : ι) : (nativeLiftFamily P S).lift i j = S.g i j :=
  rfl

/-- **DERIVED_NATIVE (Task 30).**  The standard triple-overlap defect of that family is the
unit on every triple overlap: the Spin-side cocycle law is exactly the vanishing of the
standard defect. -/
theorem nativeLiftFamily_defect_eq_one (P : InternalProjection L G)
    (S : NativeSpinTransitionData L 𝓤) (i j k : ι) {x : X} (hx : x ∈ 𝓤.overlap₃ i j k) :
    (nativeLiftFamily P S).defect i j k x = 1 := by
  rw [SpinLiftFamily.defect_apply, nativeLiftFamily_lift, nativeLiftFamily_lift,
    nativeLiftFamily_lift, S.cocycle i j k x hx, mul_inv_cancel]

/-- **DERIVED_NATIVE (Task 30).**  The family is coherent in the sense of the standard
branch. -/
theorem nativeLiftFamily_isCoherent (P : InternalProjection L G)
    (S : NativeSpinTransitionData L 𝓤) : (nativeLiftFamily P S).IsCoherent :=
  fun i j k x hx => S.cocycle i j k x hx

/-- **DERIVED_NATIVE (Task 30), PRINCIPAL TARGET.**  The **existing** standard Spin-lift
obstruction class of the data obtained by projecting coherent Spin-native transition data
through `ρ` is the trivial class. -/
theorem projected_obstruction_trivial (P : InternalProjection L G)
    (S : NativeSpinTransitionData L 𝓤) :
    (nativeLiftFamily P S).obstruction = trivialClass P 𝓤 :=
  SpinLiftFamily.obstruction_eq_trivialClass_of_isCoherent (nativeLiftFamily_isCoherent P S)

/-- **DERIVED_NATIVE (Task 30), PRINCIPAL TARGET (choice-free form).**  The standard
obstruction of the projected data computed from *any* family of local Spin lifts — not only
from the tautological one — is trivial.  This uses the frozen choice-independence theorem of
the standard branch. -/
theorem projected_obstruction_trivial_of_lifts (P : InternalProjection L G)
    (S : NativeSpinTransitionData L 𝓤) (D : SpinLiftFamily P (project P S)) :
    D.obstruction = trivialClass P 𝓤 := by
  rw [D.obstruction_lift_independent (nativeLiftFamily P S)]
  exact projected_obstruction_trivial P S

/-- **DERIVED_NATIVE (Task 30), packaged endpoint — the Task-30 square.**  For coherent
Spin-native transition data `S`:

1. its projection is exact visible transition data on the same cover;
2. `S` is itself a family of local Spin lifts of that projection, so the standard branch is
   applicable without any `SO → Spin` reconstruction;
3. the standard triple-overlap defect of that family vanishes identically;
4. the standard obstruction class of the projected data is trivial, for every choice of local
   lifts;
5. consequently coherent Spin-valued transition data over the projection exist. -/
theorem native_projection_square (P : InternalProjection L G)
    (S : NativeSpinTransitionData L 𝓤) :
    (∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k,
        (project P S).g i j x * (project P S).g j k x = (project P S).g i k x) ∧
    (∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, P.proj ((nativeLiftFamily P S).lift i j x)
        = (project P S).g i j x) ∧
    (∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k, (nativeLiftFamily P S).defect i j k x = 1) ∧
    (∀ D : SpinLiftFamily P (project P S), D.obstruction = trivialClass P 𝓤) ∧
    (∃ D : SpinLiftFamily P (project P S), D.IsCoherent) :=
  ⟨(project P S).cocycle, fun _ _ _ _ => rfl,
   fun i j k _ hx => nativeLiftFamily_defect_eq_one P S i j k hx,
   fun D => projected_obstruction_trivial_of_lifts P S D,
   ⟨nativeLiftFamily P S, nativeLiftFamily_isCoherent P S⟩⟩

end SpinNative

/-! ## The native intrinsic Spin/Lorentz instance -/

namespace SpinCore

open CechSpinLift SpinNative

universe w t

variable {X : Type w} [TopologicalSpace X] {ι : Type t} {𝓤 : CechCover X ι}

/-- **DERIVED_NATIVE (Task 30), principal target for the intrinsic cover.**  Coherent
`Spin⁺(1,3)`-valued transition data project, through the native intrinsic double cover
`ρ : Spin → GLor`, to `GLor`-valued transition data whose standard `ℤ₂`-valued Spin-lift
obstruction is trivial. -/
theorem spin_projected_obstruction_trivial
    (S : NativeSpinTransitionData (↥SpinGroup) 𝓤)
    (D : SpinLiftFamily internalSpinProjection (project internalSpinProjection S)) :
    D.obstruction = trivialClass internalSpinProjection 𝓤 :=
  projected_obstruction_trivial_of_lifts internalSpinProjection S D

/-- **AUDIT (Task 30), no new mathematics.**  The pointwise information-loss statement
`ρ(-u) = ρ(u)` is *not* reproved here: it is the inherited
`SpinCore.spinCover_negOneSpin_mul` of `RequestProject.Spine.E1.Topology.LocalSection`.  This
restatement only records that the generic `SpinNative.proj_ker_mul` specializes to it. -/
theorem proj_ker_mul_eq_spinCover_negOneSpin_mul (u : ↥SpinGroup) :
    internalSpinProjection.proj (negOneSpin * u) = internalSpinProjection.proj u ∧
      spinCover (negOneSpin * u) = spinCover u :=
  ⟨proj_ker_mul internalSpinProjection ((mem_ker_spinCover_iff negOneSpin).2 (Or.inr rfl)),
    spinCover_negOneSpin_mul u⟩

end SpinCore

/-! ## The Lorentz-frame instantiation and the twist/projection compatibility -/

namespace LorentzFrames

open SpinCore CechSpinLift SpinNative NullSectorTask28

universe u v t

variable {M : Type u} [TopologicalSpace M] {Fib : M → Type v}
  [∀ x, AddCommGroup (Fib x)] [∀ x, Module ℝ (Fib x)] {ι : Type t}
  {Φ : LorentzFrameData M Fib ι}

/-- **NEWLY DEFINED (Task 30).**  The Spin-native content of a Spin structure on Lorentz
frame data: its Spin-valued transition maps, with the `projects` field *forgotten*.  This is
the arrow from the standard presentation into the Spin-native branch; it makes explicit that
`SpinFrameStructure` is Spin-valued gluing data **plus** a compatibility with previously
given `SO`-data, the latter being exactly what the Spin-native branch does not need. -/
def SpinFrameStructure.toNative (S : SpinFrameStructure Φ) :
    NativeSpinTransitionData (↥SpinGroup) Φ.cover where
  g := S.s
  continuousOn_g := S.continuousOn_s
  cocycle := S.cocycle

@[simp] theorem SpinFrameStructure.toNative_g (S : SpinFrameStructure Φ) (i j : ι) :
    S.toNative.g i j = S.s i j := rfl

/-- **DERIVED_NATIVE (Task 30).**  On the double overlaps the projection of the Spin-native
data of a Spin structure is the Lorentz frame transition map it was a lift of.  (Off the
overlaps nothing is claimed: the `projects` field asserts nothing there.) -/
theorem project_toNative_eq_transition (S : SpinFrameStructure Φ) (i j : ι) {x : M}
    (hx : x ∈ Φ.cover.overlap₂ i j) :
    (project internalSpinProjection S.toNative).g i j x = Φ.transition i j x :=
  S.projects i j x hx

/-- **DERIVED_NATIVE (Task 30), principal — projection forgets the kernel twist.**  Twisting
a Spin structure by a continuous `{±1}`-valued Čech 1-cocycle changes the Spin-side data but
not its projection: on every double overlap

`project (twist S ε) = project S`.

This is the exact separation of Spin data from their `SO` projection.  The equality is stated
pointwise on the overlaps because that is where the kernel-valuedness of `ε` is available;
off the overlaps neither side is constrained. -/
theorem project_twist (S : SpinFrameStructure Φ) (ε : KerCocycle₁ Φ) (i j : ι) {x : M}
    (hx : x ∈ Φ.cover.overlap₂ i j) :
    (project internalSpinProjection (S.twist ε).toNative).g i j x
      = (project internalSpinProjection S.toNative).g i j x :=
  project_eq_of_ker_factor internalSpinProjection
    (S := S.toNative) (S' := (S.twist ε).toNative) (e := ε.e)
    (fun i j x hx => (ε.isKer i j).2 x hx) (fun _ _ _ _ => rfl) i j hx

/-- **DERIVED_NATIVE (Task 30), packaged Lorentz-frame endpoint.**  For a Spin structure `S`
on Lorentz frame data and any `{±1}`-valued Čech 1-cocycle `ε`:

1. the Spin-native data underlying `S` project, on the overlaps, onto the given frame
   transition cocycle;
2. `S` and its twist `ε · S` have the same projection there — the kernel sign is lost;
3. the standard Lorentz-frame Spin-lift obstruction of the projected data is trivial. -/
theorem native_spin_structure_projection (S : SpinFrameStructure Φ) (ε : KerCocycle₁ Φ) :
    (∀ i j, ∀ x ∈ Φ.cover.overlap₂ i j,
        (project internalSpinProjection S.toNative).g i j x = Φ.transition i j x) ∧
    (∀ i j, ∀ x ∈ Φ.cover.overlap₂ i j,
        (project internalSpinProjection (S.twist ε).toNative).g i j x
          = (project internalSpinProjection S.toNative).g i j x) ∧
    (∀ D : SpinLiftFamily internalSpinProjection (project internalSpinProjection S.toNative),
        D.obstruction = trivialClass internalSpinProjection Φ.cover) :=
  ⟨fun i j _ hx => project_toNative_eq_transition S i j hx,
   fun i j _ hx => project_twist S ε i j hx,
   fun D => spin_projected_obstruction_trivial S.toNative D⟩

end LorentzFrames

/-! ## Axiom audit of the Task-30 endpoints -/

#print axioms SpinNative.project
#print axioms SpinNative.nativeLiftFamily
#print axioms SpinNative.nativeLiftFamily_isCoherent
#print axioms SpinNative.projected_obstruction_trivial
#print axioms SpinNative.projected_obstruction_trivial_of_lifts
#print axioms SpinNative.native_projection_square
#print axioms SpinNative.project_eq_of_ker_factor
#print axioms SpinCore.spin_projected_obstruction_trivial
#print axioms SpinCore.proj_ker_mul_eq_spinCover_negOneSpin_mul
#print axioms LorentzFrames.SpinFrameStructure.toNative
#print axioms LorentzFrames.project_toNative_eq_transition
#print axioms LorentzFrames.project_twist
#print axioms LorentzFrames.native_spin_structure_projection
