import RequestProject.Spine.Cech.SpinInstance
import RequestProject.Spine.GoodCover.AcyclicCover

/-!
# Task 7, WP3 (endpoint) : a good cover makes the Task-6 constancy conditions automatic

Task 6 had to carry two explicit hypotheses when transporting the Spin-lift defect into the
nerve-valued Čech complex, because a nerve cochain stores **one** `ℤ₂` per nonempty overlap
while the Task-3 defect is a *function* on the overlap:

* `CechSpinZ2.ConstOn₃ 𝓤 D.defect` — the triple-overlap defect is constant;
* `CechSpinZ2.ConstOn₂ 𝓤 e` — a kernel-valued comparison 1-cochain is constant,

and it constructed both from *preconnectedness* of the corresponding overlaps.

This module closes WP3: for a **good cover** (`GoodCoverZ2.IsGoodCover`), every finite overlap
is contractible, hence path connected, hence preconnected, so both constancy data exist with
no further hypothesis:

```
    IsGoodCover 𝓤.U  ⟹  ConstOn₃ 𝓤 D.defect   and   ConstOn₂ 𝓤 e     (automatic)
```

Consequently the whole Task-6 Spin package — the class `[z] ∈ Ȟ²(𝓤;ℤ₂)`, its independence of
the local Spin lifts, and the vanishing criterion — becomes unconditional on a good cover.

Nothing here assumes that good covers *exist*: existence is the separate question of WP4, see
`RequestProject.Spine.GoodCover.ManifoldCovers`.
-/

noncomputable section

namespace GoodCoverZ2

open CechSpinLift CechZ2 CechSpinZ2 SpinCore LorentzFrames NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}
  {𝓤 : CechCover X ι} {P : InternalProjection L G} {T : VisibleCocycle G 𝓤}

/-! ## WP3 : the constancy data on a good cover -/

/-- On a good cover the double overlaps are preconnected. -/
theorem isPreconnected_overlap₂ (h : IsGoodCover 𝓤.U) (i j : ι) :
    IsPreconnected (𝓤.overlap₂ i j) :=
  h.isPreconnected_pair i j

/-- On a good cover the triple overlaps are preconnected. -/
theorem isPreconnected_overlap₃ (h : IsGoodCover 𝓤.U) (i j k : ι) :
    IsPreconnected (𝓤.overlap₃ i j k) :=
  h.isPreconnected_triple i j k

/-- **WP3, principal (pair form).**  On a good cover, a continuous kernel-valued Čech
1-cochain is automatically constant on each double overlap. -/
def constOn₂_ofGoodCover (h : IsGoodCover 𝓤.U) (P : InternalProjection L G)
    {e : ι → ι → (X → L)} (he : IsKerCochain₁ P 𝓤 e) : ConstOn₂ 𝓤 e :=
  ConstOn₂.ofPreconnected P he (fun i j => isPreconnected_overlap₂ h i j)

/-- **WP3, principal (triple form).**  On a good cover, the Task-3 triple-overlap Spin defect
is automatically constant on each triple overlap. -/
def constOn₃_ofGoodCover (h : IsGoodCover 𝓤.U) (D : SpinLiftFamily P T) :
    ConstOn₃ 𝓤 D.defect :=
  ConstOn₃.ofPreconnectedDefect D (fun i j k => isPreconnected_overlap₃ h i j k)

/-- **WP3, boxed implication.**  A good cover supplies both Task-6 constancy conditions. -/
theorem goodCover_constOn (h : IsGoodCover 𝓤.U) (D : SpinLiftFamily P T)
    {e : ι → ι → (X → L)} (he : IsKerCochain₁ P 𝓤 e) :
    Nonempty (ConstOn₃ 𝓤 D.defect) ∧ Nonempty (ConstOn₂ 𝓤 e) :=
  ⟨⟨constOn₃_ofGoodCover h D⟩, ⟨constOn₂_ofGoodCover h P he⟩⟩

/-! ## The same, for an acyclic cover -/

/-- On an acyclic cover (whose overlaps are preconnected by definition) the Task-3 defect is
likewise automatically constant. -/
def constOn₃_ofAcyclicCover (h : IsAcyclicCover 𝓤.U) (D : SpinLiftFamily P T) :
    ConstOn₃ 𝓤 D.defect :=
  ConstOn₃.ofPreconnectedDefect D (fun i j k => h.isPreconnected_triple i j k)

/-- On an acyclic cover a continuous kernel-valued Čech 1-cochain is automatically constant. -/
def constOn₂_ofAcyclicCover (h : IsAcyclicCover 𝓤.U) (P : InternalProjection L G)
    {e : ι → ι → (X → L)} (he : IsKerCochain₁ P 𝓤 e) : ConstOn₂ 𝓤 e :=
  ConstOn₂.ofPreconnected P he (fun i j => h.isPreconnected_pair i j)

/-! ## The Task-6 Spin package, unconditional on a good cover -/

variable {T' : VisibleCocycle (↥GLor) 𝓤}

/-- **The Spin-lift Čech class on a good cover.**  No constancy hypothesis is required: it is
supplied by the cover. -/
def spinLiftCechClassGood (h : IsGoodCover 𝓤.U)
    (D : SpinLiftFamily internalSpinProjection T') : H2 𝓤.U :=
  spinLiftCechClass (constOn₃_ofGoodCover h D)

/-- On a good cover the class does not depend on the choice of local Spin lifts. -/
theorem spinLiftCechClassGood_lift_independent (h : IsGoodCover 𝓤.U)
    (D D' : SpinLiftFamily internalSpinProjection T') :
    spinLiftCechClassGood h D = spinLiftCechClassGood h D' :=
  spinLiftCechClass_lift_independent (fun i j => isPreconnected_overlap₂ h i j) D' D
    (constOn₃_ofGoodCover h D') (constOn₃_ofGoodCover h D)

/-- **Vanishing criterion on a good cover.**  `[z] = 0` iff coherent Spin transition data
exist. -/
theorem spinLiftCechClassGood_eq_zero_iff (h : IsGoodCover 𝓤.U)
    (D : SpinLiftFamily internalSpinProjection T') :
    spinLiftCechClassGood h D = 0 ↔
      ∃ D' : SpinLiftFamily internalSpinProjection T', D'.IsCoherent :=
  spinLiftCechClass_eq_zero_iff_exists_coherent
    (fun i j => isPreconnected_overlap₂ h i j) (constOn₃_ofGoodCover h D)

/-! ## WP13 : the old Task-3 carrier, seen from a good cover -/

/-- **WP13.**  On a good cover the canonical map from genuine Čech `Ȟ²(𝓤;ℤ₂)` into the older,
broader Task-3 `ObstructionClass` carrier is **injective**: no information is lost, and the
Čech class determines the Task-3 class.  (The map is still not surjective in general — the old
carrier admits arbitrary group-valued cochains — so the extra Task-3 representatives are
artefacts of the broader carrier, not additional Spin-lift defects.) -/
theorem toObstruction_injective_of_goodCover (S : KernelSign P) (h : IsGoodCover 𝓤.U) :
    Function.Injective (toObstruction S 𝓤) :=
  toObstruction_injective S (fun i j => isPreconnected_overlap₂ h i j)

/-! ## The Lorentz-frame instance of Task 4 on a good cover -/

variable {M : Type u} [TopologicalSpace M] {Fib : M → Type v}
  [∀ x, AddCommGroup (Fib x)] [∀ x, Module ℝ (Fib x)] {Φ : LorentzFrameData M Fib ι}

/-- **The Lorentz-frame Spin-lift class on a good frame cover**, with no constancy
hypothesis. -/
def frameCechClassGood (h : IsGoodCover Φ.cover.U) (D : FrameSpinLifts Φ) : H2 Φ.cover.U :=
  frameCechClass (constOn₃_ofGoodCover h D)

/-- **Task-7 form of the Task-4/Task-6 endpoint.**  On a good cover of the frame data, the
Čech class vanishes **iff** the Lorentz frame data admits a Spin structure. -/
theorem frameCechClassGood_eq_zero_iff_spinStructure (h : IsGoodCover Φ.cover.U)
    (D : FrameSpinLifts Φ) :
    frameCechClassGood h D = 0 ↔ Nonempty (SpinFrameStructure Φ) :=
  frameCechClass_eq_zero_iff_spinStructure
    (fun i j => isPreconnected_overlap₂ h i j) (constOn₃_ofGoodCover h D)

end GoodCoverZ2
