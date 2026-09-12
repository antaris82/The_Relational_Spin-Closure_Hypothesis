import RequestProject.Experiment2.NullSectorTask23.Cover

/-!
# Task 23, Package C: continuous local representatives on each domain

**RECONSTRUCTION LAYER.**

On the domain `Vset i` the local representative is *normalized by the inherited coordinate
itself*: it is the unique core element over a given visible element whose `i`-th inherited
coordinate is positive (item 28 — the formula is inherited from the axis/parameter
implementation, not chosen by a global selection).  Its continuity is **proved**, not
asserted (item 27): the restricted projection is shown to be a continuous open bijection
from the positivity locus onto the domain, and the local representative is its inverse.

Item 29/30 are settled at the end: the two normalizations (positive or negative `i`-th
coordinate) are exactly related by the kernel sign, and every representative over `Vset i`
differs from the normalized one by a unique sign function.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask23

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21

open Quaternion Topology

/-! ## The projection is an open map -/

theorem sact_negOne_involutive (u : LiftT) : sact Sgn.negOne (sact Sgn.negOne u) = u := by
  rw [← sact_mul, Sgn.mul_self, sact_one]

/-- **DERIVED.**  The core-carrier preimage of the image of a set is the union of that set
and of its sign reflection. -/
theorem preimage_image_pr (O : Set LiftT) :
    pr ⁻¹' (pr '' O) = O ∪ (sact Sgn.negOne) ⁻¹' O := by
  ext u
  constructor
  · rintro ⟨v, hv, hvu⟩
    obtain ⟨e, he⟩ := (pr_eq_iff v u).1 hvu
    rcases Sgn.eq_one_or_negOne e with rfl | rfl
    · rw [sact_one] at he; exact Or.inl (he ▸ hv)
    · right
      show sact Sgn.negOne u ∈ O
      rw [he, sact_negOne_involutive]
      exact hv
  · rintro (h | h)
    · exact ⟨u, h, rfl⟩
    · exact ⟨sact Sgn.negOne u, h, pr_sact _ u⟩

/-- **PACKAGE C.**  The certified projection is an open map. -/
theorem isOpenMap_pr : IsOpenMap pr := by
  intro O hO
  refine (isQuotientMap_pr.isOpen_preimage).1 ?_
  rw [preimage_image_pr]
  exact hO.union (hO.preimage (continuous_sact Sgn.negOne))

/-- **DERIVED.**  A general restriction principle: an open map between open subsets stays an
open map. -/
theorem isOpenMap_restrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsOpenMap f) {A : Set X} (hA : IsOpen A) {B : Set Y}
    (hmap : ∀ a ∈ A, f a ∈ B) :
    IsOpenMap (fun a : ↥A => (⟨f (a : X), hmap (a : X) a.2⟩ : ↥B)) := by
  intro S hS
  have hval : IsOpen (Subtype.val '' S) := hA.isOpenMap_subtype_val S hS
  have himg : IsOpen (f '' (Subtype.val '' S)) := hf _ hval
  have hset : (fun a : ↥A => (⟨f (a : X), hmap (a : X) a.2⟩ : ↥B)) '' S
      = Subtype.val ⁻¹' (f '' (Subtype.val '' S)) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(a : X), ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨a, ha, rfl⟩, hy⟩
      exact ⟨a, ha, Subtype.ext hy⟩
  rw [hset]
  exact himg.preimage continuous_subtype_val

/-! ## The positivity locus and the restricted projection -/

/-- **NEUTRAL DEFINITION.**  The locus where the `i`-th inherited coordinate is positive. -/
def Upos (i : Fin 4) : Set LiftT := {u : LiftT | 0 < qco i (u : W)}

theorem isOpen_Upos (i : Fin 4) : IsOpen (Upos i) := by
  have hcont : Continuous fun u : LiftT => qco i (u : W) :=
    (continuous_qco i).comp continuous_subtype_val
  exact isOpen_lt continuous_const hcont

theorem Upos_subset_Uset (i : Fin 4) : Upos i ⊆ Uset i := fun _ hu => ne_of_gt hu

theorem pr_mem_Vset_of_Upos {i : Fin 4} {u : LiftT} (hu : u ∈ Upos i) : pr u ∈ Vset i :=
  mem_Vset_of (ne_of_gt hu)

/-- The restricted projection. -/
noncomputable def prPos (i : Fin 4) (u : ↥(Upos i)) : ↥(Vset i) :=
  ⟨pr (u : LiftT), pr_mem_Vset_of_Upos u.2⟩

theorem continuous_prPos (i : Fin 4) : Continuous (prPos i) :=
  Continuous.subtype_mk (continuous_pr.comp continuous_subtype_val) _

theorem prPos_injective (i : Fin 4) : Function.Injective (prPos i) := by
  intro u v h
  have hpr : pr (u : LiftT) = pr (v : LiftT) := congrArg Subtype.val h
  obtain ⟨e, he⟩ := (pr_eq_iff (u : LiftT) (v : LiftT)).1 hpr
  rcases Sgn.eq_one_or_negOne e with rfl | rfl
  · rw [sact_one] at he
    exact Subtype.ext he.symm
  · exfalso
    have hv : qco i ((v : LiftT) : W) = -qco i ((u : LiftT) : W) := by
      rw [he, sact_val, Sgn.negOne_val, qco_smul]
      ring
    have h1 : 0 < qco i ((u : LiftT) : W) := u.2
    have h2 : 0 < qco i ((v : LiftT) : W) := v.2
    rw [hv] at h2
    linarith

theorem prPos_surjective (i : Fin 4) : Function.Surjective (prPos i) := by
  rintro ⟨g, hg⟩
  obtain ⟨u, rfl⟩ := pr_surjective g
  have hne : qco i (u : W) ≠ 0 := mem_Vset_iff.1 hg u rfl
  refine ⟨⟨sact (sgnOf hne) u, ?_⟩, ?_⟩
  · show 0 < qco i ((sact (sgnOf hne) u : LiftT) : W)
    rw [sact_val, qco_smul]
    exact sgnOf_pos hne
  · exact Subtype.ext (pr_sact _ u)

theorem prPos_bijective (i : Fin 4) : Function.Bijective (prPos i) :=
  ⟨prPos_injective i, prPos_surjective i⟩

theorem isOpenMap_prPos (i : Fin 4) : IsOpenMap (prPos i) :=
  isOpenMap_restrict isOpenMap_pr (isOpen_Upos i) (fun _ hu => pr_mem_Vset_of_Upos hu)

/-- **PACKAGE C.**  The restricted projection is a homeomorphism of the positivity locus onto
the visible domain. -/
noncomputable def prPosHomeo (i : Fin 4) : ↥(Upos i) ≃ₜ ↥(Vset i) :=
  (Equiv.ofBijective _ (prPos_bijective i)).toHomeomorphOfContinuousOpen
    (continuous_prPos i) (isOpenMap_prPos i)

theorem prPosHomeo_apply (i : Fin 4) (u : ↥(Upos i)) : prPosHomeo i u = prPos i u := rfl

/-! ## The local representative -/

/-- **PACKAGE C (item 24), principal definition.**  The local representative on the domain
`Vset i`: the unique core element over the given visible element whose `i`-th inherited
coordinate is positive. -/
noncomputable def sec (i : Fin 4) (g : ↥(Vset i)) : LiftT := (((prPosHomeo i).symm g : ↥(Upos i)) : LiftT)

/-- **PACKAGE C (item 25).**  The local representative is a representative. -/
@[simp] theorem pr_sec (i : Fin 4) (g : ↥(Vset i)) : pr (sec i g) = (g : GvisT) := by
  have h : prPos i ((prPosHomeo i).symm g) = g := by
    rw [← prPosHomeo_apply]
    exact (prPosHomeo i).apply_symm_apply g
  exact congrArg (fun x : ↥(Vset i) => (x : GvisT)) h

/-- **PACKAGE C.**  The local representative is normalized. -/
theorem sec_pos (i : Fin 4) (g : ↥(Vset i)) : 0 < qco i ((sec i g : LiftT) : W) :=
  ((prPosHomeo i).symm g).2

/-- **PACKAGE C (item 26), principal.**  The local representative is continuous. -/
theorem continuous_sec (i : Fin 4) : Continuous (sec i) :=
  continuous_subtype_val.comp (prPosHomeo i).continuous_invFun

/-- **PACKAGE C.**  The normalization determines the local representative uniquely. -/
theorem sec_unique {i : Fin 4} {g : ↥(Vset i)} {u : LiftT} (hpr : pr u = (g : GvisT))
    (hpos : 0 < qco i (u : W)) : u = sec i g := by
  have h : prPos i ⟨u, hpos⟩ = prPos i ((prPosHomeo i).symm g) := by
    refine Subtype.ext ?_
    show pr u = pr (sec i g)
    rw [hpr, pr_sec]
  have h2 := prPos_injective i h
  exact congrArg (fun x : ↥(Upos i) => (x : LiftT)) h2

/-! ## Normalizations (items 29, 30) -/

/-- The opposite normalization on the same domain. -/
noncomputable def secNeg (i : Fin 4) (g : ↥(Vset i)) : LiftT := sact Sgn.negOne (sec i g)

/-- **PACKAGE C (item 30).**  The two natural normalizations on a domain are related exactly
by the kernel sign; no silent choice is made. -/
theorem secNeg_spec (i : Fin 4) (g : ↥(Vset i)) :
    pr (secNeg i g) = (g : GvisT) ∧ qco i ((secNeg i g : LiftT) : W) < 0 ∧
      secNeg i g = sact Sgn.negOne (sec i g) := by
  refine ⟨by rw [secNeg, pr_sact, pr_sec], ?_, rfl⟩
  have h := sec_pos i g
  rw [secNeg, sact_val, Sgn.negOne_val, qco_smul]
  linarith

/-- **PACKAGE C (items 29, 30), principal.**  Every representative over a domain differs from
the normalized local representative by a unique sign function. -/
theorem section_sign_unique {i : Fin 4} (t : ↥(Vset i) → LiftT)
    (ht : ∀ g, pr (t g) = (g : GvisT)) :
    ∃! e : ↥(Vset i) → Sgn, ∀ g, t g = sact (e g) (sec i g) := by
  have hex : ∀ g : ↥(Vset i), ∃ e : Sgn, t g = sact e (sec i g) := by
    intro g
    exact (pr_eq_iff (sec i g) (t g)).1 (by rw [pr_sec, ht])
  classical
  refine ⟨fun g => Classical.choose (hex g), fun g => Classical.choose_spec (hex g), ?_⟩
  intro e' he'
  funext g
  refine sact_injective_sign (sec i g) ?_
  rw [← he' g, ← Classical.choose_spec (hex g)]

end NullSectorTask23
