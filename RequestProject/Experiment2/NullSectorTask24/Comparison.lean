import RequestProject.Experiment2.NullSectorTask24.LiftedFrames

/-!
# Task 24, Package J and the negative controls

**Package J is intentionally small (items 65–69).**  The Task-XXIII four-chart atlas is *not*
rebuilt and is *not* used anywhere in the definition of the frame carrier; the only thing
proved here is one clean compatibility theorem: after choosing a frame coordinate
presentation, the Task-XXIII local representatives induce local choices of lifted frames, and
the sign by which two such choices differ over a point of an overlap is exactly the
Task-XXIII overlap sign.  The statement holds for *every* reference frame, so the comparison
does not depend on that choice (item 68).

The bridging maps between the packaged group carriers of Task 21 and the set-level carriers
of Task 23 are recorded first; they are pure repackaging (both sides are the same inherited
data).

The negative controls (items 74–80) close the file.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask24

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21 NullSectorTask23

/-! ## Bridging the two packagings of the certified projection -/

/-- **PACKAGING.**  The set-level internal element, read in the packaged internal group. -/
noncomputable def ofLiftT (u : LiftT) : LiftGrp :=
  ⟨WG.ofInvertible (isInvertible_of_mem_Lift u.2), u.2⟩

@[simp] theorem ofLiftT_val (u : LiftT) : ((ofLiftT u : LiftGrp) : WG).val = (u : W) := rfl

/-- **PACKAGING.**  The packaged visible element, read in the set-level visible carrier. -/
def toGvisT (g : Gvis) : GvisT :=
  ⟨⇑((g : (Module.End ℝ W)ˣ) : Module.End ℝ W), by
    obtain ⟨p, hp⟩ := g.2
    exact ⟨p, congrArg (fun F : W →ₗ[ℝ] W => (F : W → W)) hp⟩⟩

theorem toGvisT_injective : Function.Injective toGvisT := by
  intro g g' h
  have h1 : ⇑((g : (Module.End ℝ W)ˣ) : Module.End ℝ W)
      = ⇑((g' : (Module.End ℝ W)ˣ) : Module.End ℝ W) := congrArg Subtype.val h
  exact Subtype.ext (Units.ext (DFunLike.coe_injective h1))

/-- **PACKAGING.**  The two packagings of the certified projection agree. -/
theorem toGvisT_projCore (u : LiftT) : toGvisT (projCore (ofLiftT u)) = pr u := rfl

/-! ## The kernel sign attached to a Task-XXIII sign -/

open scoped Classical in
/-- **NEUTRAL DEFINITION.**  The kernel element attached to a Task-XXIII sign. -/
noncomputable def kerOf (e : Sgn) : LiftGrp := if (e : ℝ) = 1 then 1 else lNegOne

theorem kerOf_mem (e : Sgn) : kerOf e ∈ KerSign := by
  rw [kerOf]
  split
  · exact Subgroup.one_mem _
  · exact lNegOne_mem_KerSign

theorem kerOf_one : kerOf 1 = 1 := by rw [kerOf, if_pos Sgn.one_val]

theorem kerOf_negOne : kerOf Sgn.negOne = lNegOne := by
  rw [kerOf, if_neg (by norm_num)]

/-- **DERIVED.**  The Task-XXIII sign action corresponds exactly to multiplication by the
kernel element in the packaged internal group. -/
theorem ofLiftT_sact (e : Sgn) (u : LiftT) : ofLiftT (sact e u) = kerOf e * ofLiftT u := by
  rcases Sgn.eq_one_or_negOne e with rfl | rfl
  · rw [kerOf_one, one_mul, sact_one]
  · rw [kerOf_negOne]
    refine Subtype.ext (WG.ext ?_)
    show ((-1 : ℝ) • (u : W)) = (-w1) ⋆ (u : W)
    rw [neg_mul_W, one_mul_W]
    module

/-! ## Package J — the single compatibility theorem (items 66–68) -/

section LocalComparison

variable (F₀ : FramePlus)

/-- The lifted frame induced by a Task-XXIII local representative, after a frame coordinate
presentation has been chosen. -/
noncomputable def localLiftedFrame {i : Fin 4} (g : ↥(Vset i)) : LiftedFrame F₀ :=
  LiftedFrame.mk F₀ (ofLiftT (sec i g))

/-- **PACKAGE J (items 66, 67), principal.**  Over a point of an overlap, the two local
choices of lifted frames differ exactly by the kernel sign attached to the Task-XXIII overlap
sign.  The statement is uniform in the reference frame `F₀`, so the comparison does not depend
on the frame coordinate presentation (item 68). -/
theorem localLiftedFrame_overlap {i j : Fin 4} {g : GvisT} (hi : g ∈ Vset i) (hj : g ∈ Vset j) :
    localLiftedFrame F₀ (⟨g, hj⟩ : ↥(Vset j))
      = (⟨kerOf (tauAt i j g hi hj), kerOf_mem _⟩ : KerSign) •
          localLiftedFrame F₀ (⟨g, hi⟩ : ↥(Vset i)) := by
  refine LiftedFrame.ext ?_
  show ofLiftT (sec j ⟨g, hj⟩) = kerOf (tauAt i j g hi hj) * ofLiftT (sec i ⟨g, hi⟩)
  rw [sec_eq_tau_smul hi hj, ofLiftT_sact]

/-- **PACKAGE J.**  In particular the two local choices lie over the same frame. -/
theorem localLiftedFrame_same_frame {i j : Fin 4} {g : GvisT} (hi : g ∈ Vset i)
    (hj : g ∈ Vset j) :
    liftedFrameProj F₀ (localLiftedFrame F₀ (⟨g, hj⟩ : ↥(Vset j)))
      = liftedFrameProj F₀ (localLiftedFrame F₀ (⟨g, hi⟩ : ↥(Vset i))) := by
  rw [localLiftedFrame_overlap F₀ hi hj]
  rfl

end LocalComparison

/-! ## Negative controls -/

/-- An auxiliary frame, obtained from the coordinate frame by reversing two of its vectors.
It is used only to exhibit a nontrivial visible transformation. -/
def altFrame : FramePlus := by
  refine ⟨![be 0, -be 1, -be 2], ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [be, h3, dot3]
  · show 0 < triple (be 0) (-be 1) (-be 2)
    norm_num [triple_apply, be, Matrix.cons_val_two, Matrix.tail_cons]

theorem altFrame_ne_coordFrame : altFrame ≠ coordFrame := by
  intro h
  have h1 : altFrame.vec 1 = coordFrame.vec 1 := congrArg (fun F : FramePlus => F.vec 1) h
  have h2 : -be 1 = be 1 := h1
  have h3' : (be 1).2.1 = 0 := by
    have := congrArg (fun p : E => p.2.1) h2
    simp only [Prod.snd_neg, Prod.fst_neg] at this
    linarith
  simp [be] at h3'

/-- **NEGATIVE CONTROL.**  The visible carrier is nontrivial. -/
theorem exists_nontrivial_gvis : ∃ g : Gvis, g ≠ 1 := by
  refine ⟨frameHom coordFrame altFrame, ?_⟩
  intro h
  refine altFrame_ne_coordFrame ?_
  have := frameHom_smul coordFrame altFrame
  rw [h, one_smul] at this
  exact this.symm

/-- **NEGATIVE CONTROL (item 74).**  No frame is fixed by the whole visible carrier: the
frame carrier has no distinguished element, unlike the visible carrier, which has its unit.
The frame carrier is therefore not identified with the visible carrier by its definition. -/
theorem no_gvis_fixed_frame (F : FramePlus) : ∃ g : Gvis, g ≠ 1 ∧ g • F ≠ F := by
  obtain ⟨g, hg⟩ := exists_nontrivial_gvis
  refine ⟨g, hg, fun h => hg (frameAction_free h)⟩

/-- **NEGATIVE CONTROL (item 76/77).**  The lifted frame projection is not injective: the
lifted frame carrier is a two-valued object over the frame carrier, and nothing more is
claimed of it. -/
theorem liftedFrameProj_not_injective (F₀ : FramePlus) :
    ¬ Function.Injective (liftedFrameProj F₀) := by
  intro hinj
  obtain ⟨x, y, hxy, hz⟩ := two_lifts F₀ coordFrame
  exact hxy (hinj (((hz x).2 (Or.inl rfl)).trans (((hz y).2 (Or.inr rfl))).symm))

end NullSectorTask24
