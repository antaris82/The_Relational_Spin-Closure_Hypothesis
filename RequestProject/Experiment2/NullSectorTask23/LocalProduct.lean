import RequestProject.Experiment2.NullSectorTask23.Transitions

/-!
# Task 23, Package F: the local product decomposition

**RECONSTRUCTION LAYER.**

For each domain of the chosen family the candidate local product map

`(g, ε) ↦ ε • s_i(g)`

is constructed (item 45), its explicit inverse is written down (item 47), bijectivity is
proved (item 46) and both directions are proved continuous (item 48).  The verdict of item
49 is therefore the strongest one: the preimage of a domain is **homeomorphic** to the
product of the domain with the two-element sign carrier.

No conventional name is attached to this fact here (item 50); the comparison is made in the
final comparison module.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask23

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21

open Quaternion Topology

/-! ## Two sign computations -/

theorem sgnOf_smul_of_pos {e : Sgn} {a : ℝ} (ha : 0 < a) (h : (e : ℝ) * a ≠ 0) :
    sgnOf h = e := by
  rcases Sgn.eq_one_or_negOne e with rfl | rfl
  · refine sgnOf_eq_one h ?_
    rw [Sgn.one_val]; linarith
  · refine sgnOf_eq_negOne h ?_
    rw [Sgn.negOne_val]; linarith

theorem sec_eq_sact_of_rep {i : Fin 4} {g : GvisT} (hi : g ∈ Vset i) {u : LiftT}
    (hu : pr u = g) (hui : qco i (u : W) ≠ 0) :
    sec i ⟨g, hi⟩ = sact (sgnOf hui) u := by
  refine (sec_unique ?_ ?_).symm
  · rw [pr_sact, hu]
  · exact sgnOf_smul_pos hui rfl

/-! ## The candidate local product map -/

theorem sact_sec_mem_Uset (i : Fin 4) (p : ↥(Vset i) × Sgn) :
    sact p.2 (sec i p.1) ∈ Uset i := by
  have hpos : 0 < qco i ((sec i p.1 : LiftT) : W) := sec_pos i p.1
  show qco i ((sact p.2 (sec i p.1) : LiftT) : W) ≠ 0
  rw [sact_val, qco_smul]
  rcases Sgn.eq_one_or_negOne p.2 with h | h <;> rw [h] <;> simp <;> linarith

/-- **PACKAGE F (item 45).**  The candidate local product map. -/
noncomputable def locProd (i : Fin 4) (p : ↥(Vset i) × Sgn) : ↥(Uset i) :=
  ⟨sact p.2 (sec i p.1), sact_sec_mem_Uset i p⟩

/-- **PACKAGE F (item 47).**  The explicit inverse. -/
noncomputable def locProdInv (i : Fin 4) (u : ↥(Uset i)) : ↥(Vset i) × Sgn :=
  (⟨pr (u : LiftT), mem_Vset_of u.2⟩, sgnOf u.2)

theorem locProdInv_locProd (i : Fin 4) (p : ↥(Vset i) × Sgn) :
    locProdInv i (locProd i p) = p := by
  obtain ⟨g, e⟩ := p
  have hpos : 0 < qco i ((sec i g : LiftT) : W) := sec_pos i g
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    show pr (sact e (sec i g)) = (g : GvisT)
    rw [pr_sact, pr_sec]
  · show sgnOf (sact_sec_mem_Uset i (g, e)) = e
    have hval : qco i ((sact e (sec i g) : LiftT) : W)
        = (e : ℝ) * qco i ((sec i g : LiftT) : W) := by
      rw [sact_val, qco_smul]
    refine Subtype.ext ?_
    rw [sgnOf_val, hval]
    have h : sgnOf (show (e : ℝ) * qco i ((sec i g : LiftT) : W) ≠ 0 from by
        rw [← hval]; exact sact_sec_mem_Uset i (g, e)) = e := sgnOf_smul_of_pos hpos _
    exact congrArg Subtype.val h

theorem locProd_locProdInv (i : Fin 4) (u : ↥(Uset i)) : locProd i (locProdInv i u) = u := by
  refine Subtype.ext ?_
  show sact (sgnOf u.2) (sec i ⟨pr (u : LiftT), mem_Vset_of u.2⟩) = (u : LiftT)
  rw [sec_eq_sact_of_rep (mem_Vset_of u.2) rfl u.2, ← sact_mul, Sgn.mul_self, sact_one]

/-- **PACKAGE F (item 46).**  The candidate local product map is bijective. -/
noncomputable def locProdEquiv (i : Fin 4) : (↥(Vset i) × Sgn) ≃ ↥(Uset i) where
  toFun := locProd i
  invFun := locProdInv i
  left_inv := locProdInv_locProd i
  right_inv := locProd_locProdInv i

theorem continuous_locProd (i : Fin 4) : Continuous (locProd i) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  have h1 : Continuous fun p : ↥(Vset i) × Sgn => ((p.2 : Sgn) : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have h2 : Continuous fun p : ↥(Vset i) × Sgn => ((sec i p.1 : LiftT) : W) :=
    continuous_subtype_val.comp ((continuous_sec i).comp continuous_fst)
  exact h1.smul h2

theorem continuous_locProdInv (i : Fin 4) : Continuous (locProdInv i) := by
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) ?_
  · exact continuous_pr.comp continuous_subtype_val
  · refine Continuous.subtype_mk ?_ _
    have hr : Continuous fun u : ↥(Uset i) => qco i ((u : LiftT) : W) :=
      (continuous_qco i).comp (continuous_subtype_val.comp continuous_subtype_val)
    exact hr.div hr.abs fun u => abs_ne_zero.2 u.2

/-- **PACKAGE F (items 48, 49), principal.**  The local product decomposition holds in the
strongest form: the preimage of a domain is homeomorphic to the product of the domain with
the two-element sign carrier. -/
noncomputable def locProdHomeo (i : Fin 4) : (↥(Vset i) × Sgn) ≃ₜ ↥(Uset i) where
  toEquiv := locProdEquiv i
  continuous_toFun := continuous_locProd i
  continuous_invFun := continuous_locProdInv i

/-- **PACKAGE F (item 49), principal endpoint.**  The same statement written directly for the
preimage of the domain under the certified projection. -/
noncomputable def preimageProdHomeo (i : Fin 4) :
    ↥(pr ⁻¹' (Vset i)) ≃ₜ (↥(Vset i) × Sgn) :=
  (Homeomorph.setCongr (preimage_Vset i)).trans (locProdHomeo i).symm

theorem preimageProdHomeo_fst (i : Fin 4) (u : ↥(pr ⁻¹' (Vset i))) :
    ((preimageProdHomeo i u).1 : GvisT) = pr (u : LiftT) := rfl

end NullSectorTask23
