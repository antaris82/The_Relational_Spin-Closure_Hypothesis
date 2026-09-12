import RequestProject.Experiment2.NullSectorTask23.Reconstruction

/-!
# Task 23, Package L: the global-section obstruction, read locally

**RECONSTRUCTION LAYER.**

The certified statement "no global continuous section exists" is restated purely in terms of
the local data of Packages C–E (item 85), and the following equivalence is proved in both
directions **from the local data**, not imported (items 86–88):

> a global continuous representative exists **iff** the local representatives can be
> modified by continuous kernel signs so that all overlap transitions become `+1`.

Two negative controls are separated carefully: without the continuity requirement such a
sign modification always exists (so local representatives alone never obstruct anything —
item 98), while with continuity it never does (item 89).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask23

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21

open Quaternion Topology

/-! ## Global representatives -/

/-- **NEUTRAL DEFINITION.**  A global representative of the certified projection. -/
def IsGlobalRep (σ : GvisT → LiftT) : Prop := ∀ g : GvisT, pr (σ g) = g

/-- **PACKAGE L (item 85).**  The certified no-section theorem, restated for the frozen
carriers of Task 23. -/
theorem no_continuous_global_rep : ¬ ∃ σ : GvisT → LiftT, Continuous σ ∧ IsGlobalRep σ := by
  rintro ⟨σ, hcont, hrep⟩
  refine no_continuous_core_section ⟨fun F => ((σ F : LiftT) : W), ⟨?_, ?_⟩, ?_⟩
  · intro F; exact (σ F).2
  · intro F
    have h := hrep F
    exact congrArg Subtype.val h
  · exact continuous_subtype_val.comp hcont

/-- **DERIVED.**  A global representative exists set-theoretically. -/
theorem exists_global_rep : ∃ σ : GvisT → LiftT, IsGlobalRep σ := by
  classical
  refine ⟨fun g => sec (Classical.choose (exists_mem_Vset g))
    ⟨g, Classical.choose_spec (exists_mem_Vset g)⟩, fun g => ?_⟩
  exact pr_sec _ _

/-! ## Sign modifications of the local representatives -/

/-- **NEUTRAL DEFINITION.**  A family of kernel signs, one on each domain. -/
abbrev SignFamily : Type := ∀ i : Fin 4, ↥(Vset i) → Sgn

/-- **NEUTRAL DEFINITION.**  The modified local representative. -/
noncomputable def secMod (c : SignFamily) (i : Fin 4) (g : ↥(Vset i)) : LiftT :=
  sact (c i g) (sec i g)

theorem pr_secMod (c : SignFamily) (i : Fin 4) (g : ↥(Vset i)) :
    pr (secMod c i g) = (g : GvisT) := by
  rw [secMod, pr_sact, pr_sec]

/-- **NEUTRAL DEFINITION (item 86).**  A sign family trivializes the overlap data when the
modified local representatives agree on every overlap. -/
def Trivializes (c : SignFamily) : Prop :=
  ∀ (i j : Fin 4) (g : GvisT) (hi : g ∈ Vset i) (hj : g ∈ Vset j),
    secMod c j ⟨g, hj⟩ = secMod c i ⟨g, hi⟩

/-- **PACKAGE L.**  Trivialization is exactly the statement that the modified transitions are
all `+1`, i.e. that the transition sign is the product of the two modifying signs. -/
theorem trivializes_iff_tau_eq (c : SignFamily) :
    Trivializes c ↔ ∀ (i j : Fin 4) (g : GvisT) (hi : g ∈ Vset i) (hj : g ∈ Vset j),
      tauAt i j g hi hj = c i ⟨g, hi⟩ * c j ⟨g, hj⟩ := by
  constructor
  · intro h i j g hi hj
    have h' := h i j g hi hj
    rw [secMod, secMod, sec_eq_tau_smul hi hj, ← sact_mul] at h'
    have hsign := sact_injective_sign (sec i ⟨g, hi⟩) h'
    rw [Sgn.eq_mul_of_mul_eq hsign, mul_comm]
  · intro h i j g hi hj
    rw [secMod, secMod, sec_eq_tau_smul hi hj, ← sact_mul, h i j g hi hj]
    congr 1
    exact Sgn.mul_left_self _ _

/-! ## From a global representative to a trivializing sign family -/

theorem qco_globalRep_ne_zero {σ : GvisT → LiftT} (hσ : IsGlobalRep σ) {i : Fin 4}
    (g : ↥(Vset i)) : qco i ((σ (g : GvisT) : LiftT) : W) ≠ 0 :=
  mem_Vset_iff.1 g.2 (σ (g : GvisT)) (hσ (g : GvisT))

/-- **NEUTRAL DEFINITION.**  The sign relating a global representative to the normalized
local representative. -/
noncomputable def repSign {σ : GvisT → LiftT} (hσ : IsGlobalRep σ) (i : Fin 4)
    (g : ↥(Vset i)) : Sgn := sgnOf (qco_globalRep_ne_zero hσ g)

theorem secMod_repSign {σ : GvisT → LiftT} (hσ : IsGlobalRep σ) (i : Fin 4) (g : ↥(Vset i)) :
    secMod (repSign hσ) i g = σ (g : GvisT) := by
  have hsec : sec i g = sact (repSign hσ i g) (σ (g : GvisT)) := by
    have h := sec_eq_sact_of_rep g.2 (hσ (g : GvisT)) (qco_globalRep_ne_zero hσ g)
    simpa [repSign] using h
  rw [secMod, hsec, ← sact_mul, Sgn.mul_self, sact_one]

/-- **PACKAGE L, first direction (set-theoretic part).**  Every global representative gives a
trivializing sign family. -/
theorem trivializes_repSign {σ : GvisT → LiftT} (hσ : IsGlobalRep σ) :
    Trivializes (repSign hσ) := by
  intro i j g hi hj
  rw [secMod_repSign hσ j ⟨g, hj⟩, secMod_repSign hσ i ⟨g, hi⟩]

theorem continuous_repSign {σ : GvisT → LiftT} (hσ : IsGlobalRep σ) (hcont : Continuous σ)
    (i : Fin 4) : Continuous (repSign hσ i) := by
  refine Continuous.subtype_mk ?_ _
  have hr : Continuous fun g : ↥(Vset i) => qco i ((σ (g : GvisT) : LiftT) : W) :=
    ((continuous_qco i).comp continuous_subtype_val).comp (hcont.comp continuous_subtype_val)
  exact hr.div hr.abs fun g => abs_ne_zero.2 (qco_globalRep_ne_zero hσ g)

/-! ## From a trivializing sign family to a global representative -/

/-- The global representative assembled from a trivializing sign family. -/
noncomputable def globalOfTrivialization (c : SignFamily) (g : GvisT) : LiftT :=
  secMod c (Classical.choose (exists_mem_Vset g))
    ⟨g, Classical.choose_spec (exists_mem_Vset g)⟩

theorem globalOfTrivialization_eq {c : SignFamily} (hc : Trivializes c) {i : Fin 4} {g : GvisT}
    (hi : g ∈ Vset i) : globalOfTrivialization c g = secMod c i ⟨g, hi⟩ :=
  hc i _ g hi (Classical.choose_spec (exists_mem_Vset g))

theorem isGlobalRep_globalOfTrivialization {c : SignFamily} (hc : Trivializes c) :
    IsGlobalRep (globalOfTrivialization c) := by
  intro g
  obtain ⟨i, hi⟩ := exists_mem_Vset g
  rw [globalOfTrivialization_eq hc hi, pr_secMod]

theorem continuous_globalOfTrivialization {c : SignFamily} (hc : Trivializes c)
    (hcont : ∀ i, Continuous (c i)) : Continuous (globalOfTrivialization c) := by
  have hloc : ∀ i : Fin 4, ContinuousOn (globalOfTrivialization c) (Vset i) := by
    intro i
    rw [continuousOn_iff_continuous_restrict]
    have hrestr : (Vset i).restrict (globalOfTrivialization c) = secMod c i := by
      funext g
      exact globalOfTrivialization_eq hc g.2
    rw [hrestr]
    exact Continuous.subtype_mk
      ((continuous_subtype_val.comp ((hcont i).comp continuous_id)).smul
        (continuous_subtype_val.comp (continuous_sec i))) _
  rw [continuous_iff_continuousAt]
  intro g
  obtain ⟨i, hi⟩ := exists_mem_Vset g
  exact (hloc i).continuousAt ((isOpen_Vset i).mem_nhds hi)

/-! ## The equivalence and the obstruction -/

/-- **PACKAGE L (items 86, 87), principal.**  A global continuous representative exists
exactly when the local representatives can be modified by continuous kernel signs making all
overlap transitions trivial.  Both directions are proved from the local data. -/
theorem globalRep_iff_trivializable :
    (∃ σ : GvisT → LiftT, Continuous σ ∧ IsGlobalRep σ) ↔
      (∃ c : SignFamily, (∀ i, Continuous (c i)) ∧ Trivializes c) := by
  constructor
  · rintro ⟨σ, hcont, hσ⟩
    exact ⟨repSign hσ, continuous_repSign hσ hcont, trivializes_repSign hσ⟩
  · rintro ⟨c, hcont, hc⟩
    exact ⟨globalOfTrivialization c, continuous_globalOfTrivialization hc hcont,
      isGlobalRep_globalOfTrivialization hc⟩

/-- **PACKAGE L (item 89), principal.**  Consequently no continuous sign modification can
trivialize the overlap data: every admissible continuous modification leaves at least one
nontrivial overlap sign. -/
theorem no_continuous_trivialization :
    ¬ ∃ c : SignFamily, (∀ i, Continuous (c i)) ∧ Trivializes c := by
  intro h
  exact no_continuous_global_rep (globalRep_iff_trivializable.2 h)

/-- **PACKAGE L (item 90), strongest precise form for the chosen cover.**  For every
continuous sign family there are two domains and a point of their overlap at which the
transition sign is *not* the product of the two modifying signs. -/
theorem exists_nontrivial_overlap_sign (c : SignFamily) (hcont : ∀ i, Continuous (c i)) :
    ∃ (i j : Fin 4) (g : GvisT) (hi : g ∈ Vset i) (hj : g ∈ Vset j),
      tauAt i j g hi hj ≠ c i ⟨g, hi⟩ * c j ⟨g, hj⟩ := by
  by_contra hcon
  push_neg at hcon
  exact no_continuous_trivialization ⟨c, hcont, (trivializes_iff_tau_eq c).2 hcon⟩

/-- **PACKAGE L (item 98), negative control.**  Without the continuity requirement a
trivializing sign family always exists: the obstruction is not the existence of local
representatives, and local representatives never imply a global continuous one. -/
theorem exists_settheoretic_trivialization : ∃ c : SignFamily, Trivializes c := by
  obtain ⟨σ, hσ⟩ := exists_global_rep
  exact ⟨repSign hσ, trivializes_repSign hσ⟩

end NullSectorTask23
