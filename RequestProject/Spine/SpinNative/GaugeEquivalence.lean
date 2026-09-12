import RequestProject.Spine.SpinNative.KernelTwist

/-!
# Spine / SpinNative : gauge equivalence of Spin-native gluing data

Fourth module of the Spin-native branch.  It fixes **the** equivalence relation under which
"uniqueness of the Spin structure" can honestly be asserted at the level of Čech gluing data
on a fixed cover:

`S ≈ S'  ⟺  ∃ λ_i : U_i → ker ρ continuous,  g̃'_ij = λ_i · g̃_ij · λ_j⁻¹  on U_ij`.

This is the cocycle form of an isomorphism of the two glued objects: `λ` is a patchwise
central relabelling of the Spin-side fibres.  Because `ker ρ` is central, `λ_i g̃ λ_j⁻¹`
equals `(δλ)_ij · g̃`, so gauge equivalence is exactly *twisting by a gauge-trivial kernel
1-cocycle* (`gaugeEquiv_iff_twist_isGaugeTrivial`).

Nothing here uses a manifold, a bundle, a connection, or the `SO`-first lift machinery; the
import closure is that of `RequestProject.Spine.SpinNative.KernelTwist`.

**Boundary.**  A gauge equivalence of Čech data is not proved here to be an isomorphism of
principal bundles: the project has no total-space presentation of the glued object at this
stage (see `TASK04_AUDIT.md`).  `GaugeEquiv` is exactly the cocycle-level notion and is used
as such throughout Task 31.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace SpinNative

open CechSpinLift NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}
  {𝓤 : CechCover X ι} {P : InternalProjection L G}

namespace KerCochain₀

/-- Pointwise product of kernel 0-cochains. -/
def mul (lam lam' : KerCochain₀ P 𝓤) : KerCochain₀ P 𝓤 where
  l i x := lam.l i x * lam'.l i x
  isKer i := (lam.isKer i).mul P (lam'.isKer i)

@[simp] theorem mul_l (lam lam' : KerCochain₀ P 𝓤) (i : ι) (x : X) :
    (lam.mul lam').l i x = lam.l i x * lam'.l i x := rfl

/-- Pointwise inverse of a kernel 0-cochain. -/
def inv (lam : KerCochain₀ P 𝓤) : KerCochain₀ P 𝓤 where
  l i x := (lam.l i x)⁻¹
  isKer i := (lam.isKer i).inv P

@[simp] theorem inv_l (lam : KerCochain₀ P 𝓤) (i : ι) (x : X) :
    lam.inv.l i x = (lam.l i x)⁻¹ := rfl

end KerCochain₀

/-! ## The equivalence relation -/

/-- **NEWLY DEFINED (Task 31), principal.**  Gauge equivalence of Spin-native gluing data on
a fixed cover: the two data differ by a continuous patchwise kernel-valued relabelling.  Only
the values on the double overlaps are constrained, because that is the only place where the
gluing data carry information. -/
def GaugeEquiv (P : InternalProjection L G) (S S' : NativeSpinTransitionData L 𝓤) : Prop :=
  ∃ lam : KerCochain₀ P 𝓤, ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j,
    S'.g i j x = lam.l i x * S.g i j x * (lam.l j x)⁻¹

namespace GaugeEquiv

theorem refl (P : InternalProjection L G) (S : NativeSpinTransitionData L 𝓤) :
    GaugeEquiv P S S :=
  ⟨KerCochain₀.one P 𝓤, fun _ _ _ _ => by simp [KerCochain₀.one]⟩

theorem symm {S S' : NativeSpinTransitionData L 𝓤} (h : GaugeEquiv P S S') :
    GaugeEquiv P S' S := by
  obtain ⟨lam, hlam⟩ := h
  refine ⟨lam.inv, fun i j x hx => ?_⟩
  rw [hlam i j x hx]
  simp only [KerCochain₀.inv_l]
  group

theorem trans {S S' S'' : NativeSpinTransitionData L 𝓤} (h : GaugeEquiv P S S')
    (h' : GaugeEquiv P S' S'') : GaugeEquiv P S S'' := by
  obtain ⟨lam, hlam⟩ := h
  obtain ⟨lam', hlam'⟩ := h'
  refine ⟨lam'.mul lam, fun i j x hx => ?_⟩
  rw [hlam' i j x hx, hlam i j x hx]
  simp only [KerCochain₀.mul_l]
  group

end GaugeEquiv

theorem gaugeEquiv_equivalence (P : InternalProjection L G) (𝓤 : CechCover X ι) :
    Equivalence (GaugeEquiv (𝓤 := 𝓤) P) :=
  ⟨GaugeEquiv.refl P, GaugeEquiv.symm, GaugeEquiv.trans⟩

/-! ## Gauge equivalence versus kernel twisting -/

/-- **DERIVED_NATIVE (Task 31), principal.**  Because the kernel is central, gauge
equivalence is exactly twisting by a *gauge-trivial* kernel 1-cocycle. -/
theorem gaugeEquiv_iff_twist_isGaugeTrivial (S S' : NativeSpinTransitionData L 𝓤) :
    GaugeEquiv P S S' ↔ ∃ ε : KerCocycle P 𝓤, ε.IsGaugeTrivial ∧
      ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, S'.g i j x = (twist S ε).g i j x := by
  constructor
  · rintro ⟨lam, hlam⟩
    refine ⟨lam.delta, KerCocycle.delta_isGaugeTrivial lam, fun i j x hx => ?_⟩
    have hcomm := P.ker_central _ ((lam.isKer j).2 x hx.2) (S.g i j x)
    rw [hlam i j x hx, twist_g, KerCochain₀.delta_e]
    calc lam.l i x * S.g i j x * (lam.l j x)⁻¹
        = lam.l i x * (S.g i j x * (lam.l j x)⁻¹) := by rw [mul_assoc]
      _ = lam.l i x * ((lam.l j x)⁻¹ * S.g i j x) := by
          rw [(P.ker_central _ (Subgroup.inv_mem _ ((lam.isKer j).2 x hx.2)) (S.g i j x)).symm]
      _ = lam.l i x * (lam.l j x)⁻¹ * S.g i j x := by rw [mul_assoc]
  · rintro ⟨ε, ⟨lam, hlam⟩, htw⟩
    refine ⟨lam, fun i j x hx => ?_⟩
    rw [htw i j x hx, twist_g, hlam i j x hx]
    have := P.ker_central _ (Subgroup.inv_mem _ ((lam.isKer j).2 x hx.2)) (S.g i j x)
    calc lam.l i x * (lam.l j x)⁻¹ * S.g i j x
        = lam.l i x * ((lam.l j x)⁻¹ * S.g i j x) := by rw [mul_assoc]
      _ = lam.l i x * (S.g i j x * (lam.l j x)⁻¹) := by rw [this]
      _ = lam.l i x * S.g i j x * (lam.l j x)⁻¹ := by rw [mul_assoc]

/-- **DERIVED_NATIVE (Task 31).**  Gauge-equivalent Spin-native data have the same projection
on the double overlaps: the visible geometry cannot distinguish them. -/
theorem project_eq_of_gaugeEquiv {S S' : NativeSpinTransitionData L 𝓤}
    (h : GaugeEquiv P S S') (i j : ι) {x : X} (hx : x ∈ 𝓤.overlap₂ i j) :
    (project P S').g i j x = (project P S).g i j x := by
  obtain ⟨lam, hlam⟩ := h
  have hi : P.proj (lam.l i x) = 1 := (P.mem_Ker_iff).1 ((lam.isKer i).2 x hx.1)
  have hj : P.proj (lam.l j x) = 1 := (P.mem_Ker_iff).1 ((lam.isKer j).2 x hx.2)
  show P.proj (S'.g i j x) = P.proj (S.g i j x)
  rw [hlam i j x hx, map_mul, map_mul, map_inv, hi, hj, one_mul, inv_one, mul_one]

/-- **DERIVED_NATIVE (Task 31).**  Twisting by a gauge-trivial cocycle produces a
gauge-equivalent datum. -/
theorem gaugeEquiv_twist_of_isGaugeTrivial (S : NativeSpinTransitionData L 𝓤)
    {ε : KerCocycle P 𝓤} (hε : ε.IsGaugeTrivial) : GaugeEquiv P S (twist S ε) :=
  (gaugeEquiv_iff_twist_isGaugeTrivial S (twist S ε)).2 ⟨ε, hε, fun _ _ _ _ => rfl⟩

end SpinNative
