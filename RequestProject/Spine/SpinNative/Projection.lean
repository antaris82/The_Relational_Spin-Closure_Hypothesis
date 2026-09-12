import RequestProject.Spine.SpinNative.TransitionData

/-!
# Spine / SpinNative : projecting Spin-native gluing data down to the visible geometry

Second module of the Spin-native branch.  Given Spin-native transition data `g̃_ij` and the
frozen internal projection `ρ = P.proj` (the Spin/Lorentz double cover interface of
`RequestProject.Spine.E2.CentralDoubleCover`), the *projected* transition data is

`g_ij := ρ ∘ g̃_ij`.

Two facts are proved:

* `SpinNative.project` — the projected data is again continuous transition data satisfying
  the **exact** Čech 1-cocycle law.  Continuity is continuity of `ρ`; the cocycle law is the
  homomorphism property of `ρ` applied to the Spin-side cocycle law.  Nothing is chosen, no
  lift is made, and no local section of `ρ` is used: the direction is `Spin → SO`.
* `SpinNative.project_eq_of_ker_factor` — the projection **forgets the central sign**:
  Spin-native data differing on the overlaps by kernel-valued factors have the same
  projection there.  For the intrinsic Spin cover the kernel is `{±1}`, so this is exactly
  `ρ(u) = ρ(-u)` transported to families.

The kernel theory itself is not reproved here; only `P.mem_Ker_iff` (i.e. the definition of
the kernel) is used.  No defect, coboundary or obstruction module is imported.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace SpinNative

open CechSpinLift NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}
  {𝓤 : CechCover X ι}

/-- **NEWLY DEFINED (Task 30), principal — the downward arrow of the Spin-native branch.**
The image of Spin-native transition data under the internal projection: `g_ij = ρ ∘ g̃_ij`.
It is again exact transition data on the same cover, now valued in the visible group. -/
def project (P : InternalProjection L G) (S : NativeSpinTransitionData L 𝓤) :
    VisibleCocycle G 𝓤 where
  g i j x := P.proj (S.g i j x)
  continuousOn_g i j := P.continuous_proj.comp_continuousOn (S.continuousOn_g i j)
  cocycle i j k x hx := by
    rw [← map_mul, S.cocycle i j k x hx]

@[simp] theorem project_g (P : InternalProjection L G) (S : NativeSpinTransitionData L 𝓤)
    (i j : ι) (x : X) : (project P S).g i j x = P.proj (S.g i j x) := rfl

/-- **DERIVED_NATIVE (Task 30).**  A kernel factor is invisible after projection:
`ρ (z * u) = ρ u` for `z ∈ ker ρ`.  For the intrinsic Spin cover, `z = -1`. -/
theorem proj_ker_mul (P : InternalProjection L G) {z u : L} (hz : z ∈ P.Ker) :
    P.proj (z * u) = P.proj u := by
  rw [map_mul, (P.mem_Ker_iff).1 hz, one_mul]

/-- **DERIVED_NATIVE (Task 30), principal — the information-loss statement.**  If two
Spin-native transition data differ on the double overlaps by kernel-valued factors, their
projections agree there.  The central sign carried by the Spin-side data is *not* recorded
by the projected visible data. -/
theorem project_eq_of_ker_factor (P : InternalProjection L G)
    {S S' : NativeSpinTransitionData L 𝓤} {e : ι → ι → (X → L)}
    (hker : ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, e i j x ∈ P.Ker)
    (hfac : ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, S'.g i j x = e i j x * S.g i j x) (i j : ι)
    {x : X} (hx : x ∈ 𝓤.overlap₂ i j) : (project P S').g i j x = (project P S).g i j x := by
  rw [project_g, project_g, hfac i j x hx, proj_ker_mul P (hker i j x hx)]

end SpinNative
