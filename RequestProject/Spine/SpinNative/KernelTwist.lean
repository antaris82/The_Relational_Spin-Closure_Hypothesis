import RequestProject.Spine.SpinNative.Projection

/-!
# Spine / SpinNative : the residual kernel freedom of Spin-native gluing data

Third module of the Spin-native branch.  It answers, at the level of the *gluing data*
themselves, the question

> two Spin-native transition data with the **same** projection through `ρ` — by how much can
> they differ?

and nothing else.  No manifold, no connection, no holonomy, no curvature and no obstruction
class occurs here; the import closure of this module is that of
`RequestProject.Spine.SpinNative.Projection` (cover, cocycle, projection, kernel predicate),
and in particular contains none of `E2.Cech.Defect`, `E2.Cech.Coboundary`,
`E2.Cech.Obstruction`, `E2.Cech.SpinInstance`, `Geometry.SpinStructure` or `Spine.Cech`.

## Contents

* `SpinNative.KerCocycle P 𝓤` — a continuous `ker ρ`-valued Čech 1-cocycle on the fixed
  cover.  This is the *generic* form of the Lorentz-frame object
  `LorentzFrames.KerCocycle₁` of `RequestProject.Spine.Geometry.SpinStructure`; the two are
  identified in the comparison layer (`LorentzFrames.KerCocycle₁.toNative`), so no cocycle
  theory is duplicated: the group-agnostic statement is proved once, here, and the
  Lorentz-frame statement is an instance of it.
* `SpinNative.KerCochain₀ P 𝓤` and `KerCocycle.IsGaugeTrivial` — kernel-valued Čech
  0-cochains and the *gauge* (coboundary) notion of triviality of a kernel 1-cocycle.  This
  is the fixed-cover, `H¹`-type notion; see the discussion of the remaining gap in
  `TASK31_PROVENANCE.md`.
* `SpinNative.twist S ε` — the twist of Spin-native gluing data by such a cocycle, and
  `SpinNative.project_twist`: **the projection does not see the twist**.  This is the
  negative control in its abstract form.
* `SpinNative.ratio S S' hproj` — the kernel 1-cocycle comparing two Spin-native data with
  the same projection, and `SpinNative.exists_kerCocycle_twist_eq`: *every* competitor of a
  given Spin-native datum over the same projected data is a twist of it.

Centrality of `ker ρ` (a field of the frozen `InternalProjection` interface) is used exactly
twice: for the cocycle law of `ratio` and for the cocycle law of `twist`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace SpinNative

open CechSpinLift NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}
  {𝓤 : CechCover X ι}

/-! ## Kernel-valued Čech 1-cocycles on the fixed cover -/

/-- **NEWLY DEFINED (Task 31), principal.**  A continuous `ker ρ`-valued Čech 1-cocycle on
the cover: the object through which two Spin-native gluing data with the same projection
differ.  Only the cocycle law on triple overlaps is assumed; the unit and inverse laws are
derived below. -/
structure KerCocycle (P : InternalProjection L G) (𝓤 : CechCover X ι) where
  /-- The kernel-valued comparison functions. -/
  e : ι → ι → (X → L)
  /-- Continuity and kernel-valuedness on the double overlaps. -/
  isKer : ∀ i j, P.IsKerFunOn (𝓤.overlap₂ i j) (e i j)
  /-- The exact Čech 1-cocycle law on the triple overlaps. -/
  cocycle : ∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k, e i j x * e j k x = e i k x

namespace KerCocycle

variable {P : InternalProjection L G}

/-- The trivial kernel 1-cocycle. -/
def one (P : InternalProjection L G) (𝓤 : CechCover X ι) : KerCocycle P 𝓤 where
  e _ _ _ := 1
  isKer _ _ := P.isKerFunOn_one _
  cocycle _ _ _ _ _ := one_mul 1

@[simp] theorem one_e (P : InternalProjection L G) (𝓤 : CechCover X ι) (i j : ι) (x : X) :
    (one P 𝓤).e i j x = 1 := rfl

/-- **DERIVED (Task 31).**  The diagonal value is the unit. -/
theorem e_self (ε : KerCocycle P 𝓤) (i : ι) {x : X} (hx : x ∈ 𝓤.U i) : ε.e i i x = 1 := by
  have h := ε.cocycle i i i x ⟨⟨hx, hx⟩, hx⟩
  have h2 : ε.e i i x * ε.e i i x = 1 * ε.e i i x := by rw [one_mul]; exact h
  exact mul_right_cancel h2

/-- **DERIVED (Task 31).**  The transposed value is the inverse. -/
theorem e_symm (ε : KerCocycle P 𝓤) (i j : ι) {x : X} (hx : x ∈ 𝓤.overlap₂ i j) :
    ε.e j i x = (ε.e i j x)⁻¹ := by
  have h := ε.cocycle i j i x ⟨⟨hx.1, hx.2⟩, hx.1⟩
  rw [ε.e_self i hx.1] at h
  exact eq_inv_of_mul_eq_one_right h

/-- **NEWLY DEFINED (Task 31).**  *Pointwise* triviality: the cocycle is the unit at every
point of every double overlap.  This is the strictest possible notion of "no residual
freedom". -/
def IsPointwiseTrivial (ε : KerCocycle P 𝓤) : Prop :=
  ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, ε.e i j x = 1

theorem one_isPointwiseTrivial (P : InternalProjection L G) (𝓤 : CechCover X ι) :
    (one P 𝓤).IsPointwiseTrivial := fun _ _ _ _ => rfl

end KerCocycle

/-! ## Kernel-valued Čech 0-cochains and gauge triviality -/

/-- **NEWLY DEFINED (Task 31).**  A continuous `ker ρ`-valued Čech 0-cochain: one
kernel-valued function per patch.  These are exactly the reparametrisations of Spin-native
data that are invisible after projection *and* patchwise. -/
structure KerCochain₀ (P : InternalProjection L G) (𝓤 : CechCover X ι) where
  /-- The kernel-valued function on each patch. -/
  l : ι → (X → L)
  /-- Continuity and kernel-valuedness on the patch. -/
  isKer : ∀ i, P.IsKerFunOn (𝓤.U i) (l i)

namespace KerCochain₀

variable {P : InternalProjection L G}

/-- **NEWLY DEFINED (Task 31).**  The Čech coboundary of a kernel 0-cochain,
`(δλ)_ij = λ_i λ_j⁻¹`, as a kernel 1-cocycle. -/
def delta (lam : KerCochain₀ P 𝓤) : KerCocycle P 𝓤 where
  e i j x := lam.l i x * (lam.l j x)⁻¹
  isKer i j :=
    ((lam.isKer i).mono P fun _ hx => hx.1).mul P (((lam.isKer j).mono P fun _ hx => hx.2).inv P)
  cocycle i j k _ _ := by group

@[simp] theorem delta_e (lam : KerCochain₀ P 𝓤) (i j : ι) (x : X) :
    lam.delta.e i j x = lam.l i x * (lam.l j x)⁻¹ := rfl

/-- The trivial 0-cochain. -/
def one (P : InternalProjection L G) (𝓤 : CechCover X ι) : KerCochain₀ P 𝓤 where
  l _ _ := 1
  isKer _ := P.isKerFunOn_one _

end KerCochain₀

namespace KerCocycle

variable {P : InternalProjection L G}

/-- **NEWLY DEFINED (Task 31), principal — the `H¹`-type notion.**  A kernel 1-cocycle is
*gauge trivial* when it is the coboundary of a kernel 0-cochain on the same cover.  Two
Spin-native data differing by a gauge-trivial cocycle are the same datum read through
patchwise central relabellings; see `RequestProject.Spine.SpinNative.GaugeEquivalence`.

This is a statement about the **fixed cover** only: it is the vanishing of the
fixed-cover kernel-twist quotient, not of a global cohomology group. -/
def IsGaugeTrivial (ε : KerCocycle P 𝓤) : Prop :=
  ∃ lam : KerCochain₀ P 𝓤, ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, ε.e i j x = lam.l i x * (lam.l j x)⁻¹

/-- **DERIVED (Task 31).**  Pointwise triviality is strictly stronger than gauge
triviality. -/
theorem isGaugeTrivial_of_isPointwiseTrivial {ε : KerCocycle P 𝓤}
    (h : ε.IsPointwiseTrivial) : ε.IsGaugeTrivial :=
  ⟨KerCochain₀.one P 𝓤, fun i j x hx => by rw [h i j x hx]; simp [KerCochain₀.one]⟩

theorem delta_isGaugeTrivial (lam : KerCochain₀ P 𝓤) : lam.delta.IsGaugeTrivial :=
  ⟨lam, fun _ _ _ _ => rfl⟩

end KerCocycle

/-! ## Twisting Spin-native gluing data -/

/-- **NEWLY DEFINED (Task 31), principal.**  The twist of Spin-native transition data by a
kernel 1-cocycle: `(ε · S)_ij = ε_ij · g̃_ij`.  It is again Spin-native transition data —
centrality of the kernel is what makes the twisted family satisfy the exact cocycle law. -/
def twist {P : InternalProjection L G} (S : NativeSpinTransitionData L 𝓤)
    (ε : KerCocycle P 𝓤) : NativeSpinTransitionData L 𝓤 where
  g i j x := ε.e i j x * S.g i j x
  continuousOn_g i j := (ε.isKer i j).1.mul (S.continuousOn_g i j)
  cocycle i j k x hx := by
    have hjk : x ∈ 𝓤.overlap₂ j k := 𝓤.overlap₃_subset_jk i j k hx
    have hcomm := P.ker_central _ ((ε.isKer j k).2 x hjk) (S.g i j x)
    show ε.e i j x * S.g i j x * (ε.e j k x * S.g j k x) = ε.e i k x * S.g i k x
    calc ε.e i j x * S.g i j x * (ε.e j k x * S.g j k x)
        = ε.e i j x * (S.g i j x * ε.e j k x) * S.g j k x := by group
      _ = ε.e i j x * (ε.e j k x * S.g i j x) * S.g j k x := by rw [← hcomm]
      _ = (ε.e i j x * ε.e j k x) * (S.g i j x * S.g j k x) := by group
      _ = ε.e i k x * S.g i k x := by
          rw [ε.cocycle i j k x hx, S.cocycle i j k x hx]

@[simp] theorem twist_g {P : InternalProjection L G} (S : NativeSpinTransitionData L 𝓤)
    (ε : KerCocycle P 𝓤) (i j : ι) (x : X) : (twist S ε).g i j x = ε.e i j x * S.g i j x :=
  rfl

/-- **DERIVED_NATIVE (Task 31).**  Twisting by the trivial cocycle changes nothing. -/
theorem twist_one (P : InternalProjection L G) (S : NativeSpinTransitionData L 𝓤) :
    twist S (KerCocycle.one P 𝓤) = S :=
  transitionData_ext (by funext i j x; simp)

/-- **DERIVED_NATIVE (Task 31), PRINCIPAL — the abstract negative control.**  The projection
through `ρ` does not see a kernel twist: on every double overlap the projected data of
`ε · S` and of `S` coincide.

Off the overlaps nothing is claimed, because that is exactly where kernel-valuedness of `ε`
is available. -/
theorem project_twist (P : InternalProjection L G) (S : NativeSpinTransitionData L 𝓤)
    (ε : KerCocycle P 𝓤) (i j : ι) {x : X} (hx : x ∈ 𝓤.overlap₂ i j) :
    (project P (twist S ε)).g i j x = (project P S).g i j x :=
  project_eq_of_ker_factor P (S := S) (S' := twist S ε) (e := ε.e)
    (fun i j x hx => (ε.isKer i j).2 x hx) (fun _ _ _ _ => rfl) i j hx

/-! ## The ratio of two Spin-native data with the same projection -/

/-- **NEWLY DEFINED (Task 31), principal.**  The comparison cocycle `ε_ij = g̃'_ij (g̃_ij)⁻¹`
of two Spin-native data whose projections agree on the double overlaps.  It really is a
continuous kernel-valued Čech 1-cocycle. -/
def ratio (P : InternalProjection L G) {S S' : NativeSpinTransitionData L 𝓤}
    (hproj : ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, P.proj (S'.g i j x) = P.proj (S.g i j x)) :
    KerCocycle P 𝓤 where
  e i j x := S'.g i j x * (S.g i j x)⁻¹
  isKer i j := by
    refine ⟨(S'.continuousOn_g i j).mul ((S.continuousOn_g i j).inv), fun x hx => ?_⟩
    rw [InternalProjection.mem_Ker_iff, map_mul, map_inv, hproj i j x hx, mul_inv_cancel]
  cocycle i j k x hx := by
    have hjk : x ∈ 𝓤.overlap₂ j k := 𝓤.overlap₃_subset_jk i j k hx
    have hkerjk : S'.g j k x * (S.g j k x)⁻¹ ∈ P.Ker := by
      rw [InternalProjection.mem_Ker_iff, map_mul, map_inv, hproj j k x hjk, mul_inv_cancel]
    have hcomm := P.ker_central _ hkerjk (S.g i j x)⁻¹
    show S'.g i j x * (S.g i j x)⁻¹ * (S'.g j k x * (S.g j k x)⁻¹)
        = S'.g i k x * (S.g i k x)⁻¹
    calc S'.g i j x * (S.g i j x)⁻¹ * (S'.g j k x * (S.g j k x)⁻¹)
        = S'.g i j x * ((S.g i j x)⁻¹ * (S'.g j k x * (S.g j k x)⁻¹)) := by rw [mul_assoc]
      _ = S'.g i j x * ((S'.g j k x * (S.g j k x)⁻¹) * (S.g i j x)⁻¹) := by rw [← hcomm]
      _ = (S'.g i j x * S'.g j k x) * ((S.g i j x * S.g j k x)⁻¹) := by
          rw [mul_inv_rev]; group
      _ = S'.g i k x * (S.g i k x)⁻¹ := by
          rw [S.cocycle i j k x hx, S'.cocycle i j k x hx]

@[simp] theorem ratio_e (P : InternalProjection L G) {S S' : NativeSpinTransitionData L 𝓤}
    (hproj : ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, P.proj (S'.g i j x) = P.proj (S.g i j x))
    (i j : ι) (x : X) : (ratio P hproj).e i j x = S'.g i j x * (S.g i j x)⁻¹ := rfl

/-- **DERIVED_NATIVE (Task 31).**  Twisting by the ratio recovers the second datum, on the
nose and everywhere. -/
theorem twist_ratio (P : InternalProjection L G) {S S' : NativeSpinTransitionData L 𝓤}
    (hproj : ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, P.proj (S'.g i j x) = P.proj (S.g i j x)) :
    twist S (ratio P hproj) = S' :=
  transitionData_ext (by funext i j x; show S'.g i j x * (S.g i j x)⁻¹ * S.g i j x = _; group)

/-- **DERIVED_NATIVE (Task 31).**  The ratio of a twist is the twisting cocycle. -/
theorem ratio_twist (P : InternalProjection L G) (S : NativeSpinTransitionData L 𝓤)
    (ε : KerCocycle P 𝓤)
    (hproj : ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j,
      P.proj ((twist S ε).g i j x) = P.proj (S.g i j x)) (i j : ι) (x : X) :
    (ratio P hproj).e i j x = ε.e i j x := by
  show ε.e i j x * S.g i j x * (S.g i j x)⁻¹ = ε.e i j x
  group

/-- **DERIVED_NATIVE (Task 31), PRINCIPAL — every competitor is a twist.**  If `S'` projects
through `ρ` to the same visible data as `S` on the double overlaps, then `S'` is the twist of
`S` by a (uniquely determined) kernel-valued Čech 1-cocycle.

Together with `project_twist` this says: over a fixed projected datum, the Spin-native data
form a torsor under the group of kernel 1-cocycles of the cover — exactly the classical
`Z¹(𝓤; ker ρ)`-torsor statement, obtained here without any `SO`-first lift. -/
theorem exists_kerCocycle_twist_eq (P : InternalProjection L G)
    (S S' : NativeSpinTransitionData L 𝓤)
    (hproj : ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, P.proj (S'.g i j x) = P.proj (S.g i j x)) :
    ∃ ε : KerCocycle P 𝓤, twist S ε = S' :=
  ⟨ratio P hproj, twist_ratio P hproj⟩

/-- **DERIVED_NATIVE (Task 31), packaged — the fixed-cover torsor statement.**  For
Spin-native data over a fixed projection: every competitor is a twist, every twist is a
competitor, and the two constructions are mutually inverse. -/
theorem native_kernel_torsor (P : InternalProjection L G)
    (S : NativeSpinTransitionData L 𝓤) :
    (∀ S' : NativeSpinTransitionData L 𝓤,
        (∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, P.proj (S'.g i j x) = P.proj (S.g i j x)) →
        ∃ ε : KerCocycle P 𝓤, twist S ε = S') ∧
    (∀ ε : KerCocycle P 𝓤, ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j,
        (project P (twist S ε)).g i j x = (project P S).g i j x) :=
  ⟨fun S' hproj => exists_kerCocycle_twist_eq P S S' hproj,
   fun ε i j _ hx => project_twist P S ε i j hx⟩

end SpinNative
