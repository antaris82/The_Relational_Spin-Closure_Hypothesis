import RequestProject.Experiment2.NullSectorTask21.CoreProjection

/-!
# Task 21, Package G: the continuity obstruction as a section theorem

**IDENTIFICATION / COMPARISON MODULE** (it uses only intrinsic objects, but it is placed in
the identification layer because it is read together with Packages D and E).

Task 20 proved, intrinsically:

* a quotient-compatible internal choice **exists** (set-theoretically);
* no quotient-compatible internal choice is **continuous**.

Here those two statements are transported, through the Task-20 homeomorphism between the
visible quotient and the visible image, into statements about **sections of the intrinsic
core projection**, and the two formulations are proved equivalent in both directions.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask21

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20

/-! ## Sections at the group level -/

/-- **PACKAGE G (items 66–68).**  A set-theoretic section of the packaged core projection
exists.  Nothing but a choice of representative is used. -/
theorem exists_group_section : ∃ s : GvisG → LiftG, ∀ U : GvisG, projCore (s U) = U := by
  classical
  exact ⟨fun U => Classical.choose (projCore_surjective U),
    fun U => Classical.choose_spec (projCore_surjective U)⟩

/-! ## Sections at the carrier level, where the inherited topology lives -/

/-- The visible transformation attached to a parameter, read inside the inherited space of
maps of the carrier (where the Task-20 topology comparison is available). -/
noncomputable def visFun (p : VisParam) : visImageFun := ⟨⇑(visMap p), ⟨p, rfl⟩⟩

theorem continuous_visFun : Continuous visFun :=
  continuous_visMapFun.subtype_mk _

/-- **NEUTRAL DEFINITION.**  A section of the intrinsic core projection: a choice, for every
visible transformation, of an internal core element projecting to it. -/
def IsCoreSection (s : visImageFun → W) : Prop :=
  (∀ F : visImageFun, s F ∈ Lift) ∧ (∀ F : visImageFun, ⇑(proj (s F)) = (F : W → W))

/-- **NEUTRAL DEFINITION.**  A quotient-compatible internal choice, in the Task-20 sense. -/
def IsQuotientChoice (σ : VisParam → W) : Prop :=
  (∀ p : VisParam, σ p ∈ Lift) ∧ (∀ p : VisParam, proj (σ p) = visMap p) ∧
    (∀ p q : VisParam, visRel p q → σ p = σ q)

/-- **PACKAGE G (item 68).**  A set-theoretic section of the intrinsic core projection
exists. -/
theorem exists_core_section : ∃ s : visImageFun → W, IsCoreSection s := by
  classical
  refine ⟨fun F => Un ((Classical.choose F.2).1 : Vec3) (Classical.choose F.2).2, ?_, ?_⟩
  · intro F
    exact Un_mem_Lift (Classical.choose F.2).1.2 _
  · intro F
    rw [proj_Un (Classical.choose F.2).1.2]
    exact Classical.choose_spec F.2

/-- Visibly equal parameters give the same point of the visible image. -/
theorem visFun_eq_of_visRel {p q : VisParam} (h : visRel p q) : visFun p = visFun q :=
  Subtype.ext (congrArg (fun G : W →ₗ[ℝ] W => (G : W → W)) h)

theorem visFun_surjective (F : visImageFun) : ∃ p, visFun p = F := by
  obtain ⟨F, p, rfl⟩ := F
  exact ⟨p, rfl⟩

/-- **PACKAGE G (item 70), first direction.**  A section gives a quotient-compatible
choice, continuously. -/
theorem quotientChoice_of_section {s : visImageFun → W} (hs : IsCoreSection s) :
    IsQuotientChoice (fun p => s (visFun p)) := by
  refine ⟨fun p => hs.1 _, fun p => ?_, fun p q hpq => ?_⟩
  · exact DFunLike.coe_injective (hs.2 (visFun p))
  · show s (visFun p) = s (visFun q)
    rw [visFun_eq_of_visRel hpq]

/-- **PACKAGE G (item 70), second direction.**  A quotient-compatible choice gives a
section, continuously. -/
theorem exists_section_of_quotientChoice {σ : VisParam → W} (hσ : IsQuotientChoice σ)
    (hcont : Continuous σ) :
    ∃ s : visImageFun → W, IsCoreSection s ∧ Continuous s ∧ ∀ p, s (visFun p) = σ p := by
  set s' : visImageFun → W :=
    fun F => Quotient.lift σ (fun a b h => hσ.2.2 a b h) (visHomeo.symm F) with hs'
  have key : ∀ p, s' (visFun p) = σ p := by
    intro p
    show Quotient.lift σ _ (visHomeo.symm (visFun p)) = σ p
    rw [show visHomeo.symm (visFun p) = visClass p from visHomeo.symm_apply_apply (visClass p)]
    rfl
  refine ⟨s', ⟨?_, ?_⟩, ?_, key⟩
  · intro F
    obtain ⟨p, rfl⟩ := visFun_surjective F
    rw [key]
    exact hσ.1 p
  · intro F
    obtain ⟨p, rfl⟩ := visFun_surjective F
    rw [key, hσ.2.1 p]
    rfl
  · exact (continuous_quot_lift _ hcont).comp visHomeo.symm.continuous

/-- **PACKAGE G (item 70).**  The two formulations are equivalent. -/
theorem continuous_section_iff_continuous_choice :
    (∃ s : visImageFun → W, IsCoreSection s ∧ Continuous s) ↔
      (∃ σ : VisParam → W, IsQuotientChoice σ ∧ Continuous σ) := by
  constructor
  · rintro ⟨s, hs, hcont⟩
    exact ⟨fun p => s (visFun p), quotientChoice_of_section hs, hcont.comp continuous_visFun⟩
  · rintro ⟨σ, hσ, hcont⟩
    obtain ⟨s, hs, hscont, -⟩ := exists_section_of_quotientChoice hσ hcont
    exact ⟨s, hs, hscont⟩

/-- **PACKAGE G (item 69), principal.**  No global continuous section of the intrinsic core
projection exists. -/
theorem no_continuous_core_section :
    ¬ ∃ s : visImageFun → W, IsCoreSection s ∧ Continuous s := by
  intro h
  obtain ⟨σ, hσ, hcont⟩ := continuous_section_iff_continuous_choice.1 h
  exact no_continuous_quotient_compatible_lift ⟨σ, hcont, hσ.1, hσ.2.1, hσ.2.2⟩

/-- **PACKAGE G (item 73).**  The Task-19/20 relation-completeness obstruction and the
section obstruction are the two faces of one statement: no relation-complete locally exact
system exists, and no continuous section of the core projection exists, while a
set-theoretic section does exist. -/
theorem section_and_relation_completeness :
    (∃ s : visImageFun → W, IsCoreSection s) ∧
      (¬ ∃ s : visImageFun → W, IsCoreSection s ∧ Continuous s) ∧
      (¬ ∃ (ι : Type) (D : ι → Set Vec3) (U : ι → Vec3 → ℝ → W),
        IsLocalSystem D U ∧ SystemRelationComplete D U) :=
  ⟨exists_core_section, no_continuous_core_section, relation_completeness_package.2.1⟩

end NullSectorTask21
