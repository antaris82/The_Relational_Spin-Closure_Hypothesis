import RequestProject.Experiment2.NullSectorTask23.SafeBase

/-!
# Task 23, Package B: an explicit open family in the visible carrier

**RECONSTRUCTION LAYER.**

The family is obtained *intrinsically* from the axis/parameter reconstruction already
present in the inherited development: an element of the core carrier is exactly
`a • 1 - J v` with `a² + ⟨v,v⟩ = 1`, i.e. it has four inherited coordinates

`qco 0 u = a`, `qco 1 u, qco 2 u, qco 3 u = v`,

whose squares sum to one.  The four visible domains are obtained by excluding, one
coordinate at a time, the locus where that coordinate vanishes; this is exactly the
degeneracy locus of the axis/parameter description (`qco 0` vanishes at parameter `π`, the
three others vanish where the corresponding axis component or the parameter degenerates).
No standard atlas is imported (item 18).

Proved here: each domain is open (item 20), the four of them cover the visible carrier
(item 21), and no three of them do (item 23) — so the family is minimal among its own
subfamilies.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask23

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21

open Quaternion Topology

/-! ## The four inherited coordinates of a core element -/

/-- **NEUTRAL DEFINITION.**  The four inherited coordinates of an element of the carrier:
the unit coefficient and the three generator coefficients. -/
def qco (i : Fin 4) (u : W) : ℝ := ![u 0, -(u 6), u 5, -(u 4)] i

@[simp] theorem qco_zero (u : W) : qco 0 u = u 0 := rfl
@[simp] theorem qco_one (u : W) : qco 1 u = -(u 6) := rfl
@[simp] theorem qco_two (u : W) : qco 2 u = u 5 := rfl
@[simp] theorem qco_three (u : W) : qco 3 u = -(u 4) := rfl

theorem continuous_qco (i : Fin 4) : Continuous (qco i) := by
  have h0 : Continuous fun u : W => u 0 := continuous_apply 0
  have h4 : Continuous fun u : W => -(u 4) := (continuous_apply 4).neg
  have h5 : Continuous fun u : W => u 5 := continuous_apply 5
  have h6 : Continuous fun u : W => -(u 6) := (continuous_apply 6).neg
  fin_cases i
  · exact h0
  · exact h6
  · exact h5
  · exact h4

theorem qco_smul (i : Fin 4) (c : ℝ) (u : W) : qco i (c • u) = c * qco i u := by
  fin_cases i <;> simp [qco]

/-- **DERIVED.**  On the core carrier the four coordinates are normalized. -/
theorem qco_sq_sum {u : W} (hu : u ∈ Lift) :
    qco 0 u ^ 2 + qco 1 u ^ 2 + qco 2 u ^ 2 + qco 3 u ^ 2 = 1 := by
  have h := quatOf_normSq hu
  rw [normSq_def'] at h
  simp only [quatOf_re, quatOf_imI, quatOf_imJ, quatOf_imK] at h
  simp only [qco_zero, qco_one, qco_two, qco_three]
  linarith [h]

/-- **DERIVED.**  No element of the core carrier has all four coordinates zero. -/
theorem exists_qco_ne_zero {u : W} (hu : u ∈ Lift) : ∃ i : Fin 4, qco i u ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have h := qco_sq_sum hu
  rw [hcon 0, hcon 1, hcon 2, hcon 3] at h
  norm_num at h

/-! ## The four domains -/

/-- **NEUTRAL DEFINITION.**  The core-carrier locus on which the `i`-th coordinate does not
vanish. -/
def Uset (i : Fin 4) : Set LiftT := {u : LiftT | qco i (u : W) ≠ 0}

theorem isOpen_Uset (i : Fin 4) : IsOpen (Uset i) := by
  have hcont : Continuous fun u : LiftT => qco i (u : W) :=
    (continuous_qco i).comp continuous_subtype_val
  exact isOpen_ne.preimage hcont

/-- **NEUTRAL DEFINITION (item 17).**  The visible domain attached to the `i`-th
coordinate. -/
def Vset (i : Fin 4) : Set GvisT := pr '' (Uset i)

/-- **PACKAGE B.**  Membership in a visible domain is a property of the whole fibre: it does
not depend on the chosen core representative. -/
theorem mem_Vset_iff {i : Fin 4} {g : GvisT} :
    g ∈ Vset i ↔ ∀ u : LiftT, pr u = g → qco i (u : W) ≠ 0 := by
  constructor
  · rintro ⟨u₀, hu₀, rfl⟩ u hu
    obtain ⟨e, rfl⟩ := (pr_eq_iff u₀ u).1 hu.symm
    rw [sact_val, qco_smul]
    refine mul_ne_zero ?_ hu₀
    rcases e.2 with h | h <;> rw [h] <;> norm_num
  · intro h
    obtain ⟨u, rfl⟩ := pr_surjective g
    exact ⟨u, h u rfl, rfl⟩

theorem mem_Vset_of {i : Fin 4} {u : LiftT} (hu : qco i (u : W) ≠ 0) : pr u ∈ Vset i :=
  ⟨u, hu, rfl⟩

/-- **PACKAGE B.**  The core-carrier preimage of a visible domain is exactly the
corresponding coordinate locus. -/
theorem preimage_Vset (i : Fin 4) : pr ⁻¹' (Vset i) = Uset i := by
  ext u
  constructor
  · intro h
    exact mem_Vset_iff.1 h u rfl
  · intro h
    exact mem_Vset_of h

/-- **PACKAGE B (item 20).**  Every visible domain is open. -/
theorem isOpen_Vset (i : Fin 4) : IsOpen (Vset i) := by
  refine (isQuotientMap_pr.isOpen_preimage).1 ?_
  rw [preimage_Vset]
  exact isOpen_Uset i

/-- **PACKAGE B (item 21), principal.**  The four visible domains cover the visible
carrier. -/
theorem Vset_covers : (⋃ i : Fin 4, Vset i) = (Set.univ : Set GvisT) := by
  refine Set.eq_univ_of_forall fun g => ?_
  obtain ⟨u, rfl⟩ := pr_surjective g
  obtain ⟨i, hi⟩ := exists_qco_ne_zero u.2
  exact Set.mem_iUnion.2 ⟨i, mem_Vset_of hi⟩

theorem exists_mem_Vset (g : GvisT) : ∃ i : Fin 4, g ∈ Vset i := by
  have h : g ∈ (⋃ i : Fin 4, Vset i) := by rw [Vset_covers]; trivial
  exact Set.mem_iUnion.1 h

/-! ## Minimality of the family (item 23) -/

/-- The core element whose only nonvanishing coordinate is the `i`-th one. -/
noncomputable def basisElt (i : Fin 4) : W :=
  fromQuat (![(1 : ℍ), ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] i)

theorem basisElt_mem_Lift (i : Fin 4) : basisElt i ∈ Lift := by
  refine fromQuat_mem_Lift ?_
  fin_cases i <;> simp [normSq_def']

theorem qco_basisElt (i j : Fin 4) : qco j (basisElt i) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [basisElt, qco, fromQuat, w1, Jmap, wP, wQ, wR]

/-- **PACKAGE B (item 23).**  No three of the four domains cover: for every index the
element whose only nonvanishing coordinate is that one lies in that domain and in no
other.  Hence the four-element family is minimal among its subfamilies. -/
theorem Vset_minimal (i : Fin 4) :
    ∃ g : GvisT, g ∈ Vset i ∧ ∀ j : Fin 4, j ≠ i → g ∉ Vset j := by
  refine ⟨pr ⟨basisElt i, basisElt_mem_Lift i⟩, mem_Vset_of ?_, ?_⟩
  · rw [show ((⟨basisElt i, basisElt_mem_Lift i⟩ : LiftT) : W) = basisElt i from rfl,
      qco_basisElt i i, if_pos rfl]
    norm_num
  · intro j hj hmem
    have h := mem_Vset_iff.1 hmem ⟨basisElt i, basisElt_mem_Lift i⟩ rfl
    rw [show ((⟨basisElt i, basisElt_mem_Lift i⟩ : LiftT) : W) = basisElt i from rfl,
      qco_basisElt i j, if_neg (Ne.symm hj)] at h
    exact h rfl

end NullSectorTask23
