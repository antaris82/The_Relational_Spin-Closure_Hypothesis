import RequestProject.Experiment2.NullSectorTask24.Task24

/-!
# Task 25, Packages A–D: the full internal action on the lifted frame carrier

**Hard target A.**

Package A re-exposes the inherited Task-24 objects under stable Task-25 names.  *No new
mathematics occurs there*: every declaration in that section is an alias or a one-line
packaging statement.

Packages B, C, D then close the precise gap left by Task 24: Task 24 formalized only the
*induced* action of the internal carrier on the ordinary frame carrier `FramePlus` (which is
transitive but **not** free, with stabilizer `KerSign`), and the *kernel-sign* action on the
lifted carrier.  Here the full internal group `LiftGrp` is made to act on `LiftedFrame F₀`
directly, and the action is proved free and transitive.

Naming note: the inherited packaged internal group is called `LiftGrp` (a Task-24 alias for
`NullSectorTask21.LiftG`), and the inherited certified projection is `projCore : LiftGrp →*
Gvis`.  The informal names `Lift` and `proj` of the task statement refer to exactly these two
inherited objects; the inherited names are used verbatim, and nothing is redefined.  (The
identifier `Lift` is *not* introduced, because it already denotes an inherited *set* in an
opened namespace.)
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask25

open NullSectorTask20 NullSectorTask21 NullSectorTask23 NullSectorTask24

/-! ## Package A — the inherited objects, re-exposed

Every declaration in this section is **INHERITED** or pure **ALIASING/PACKAGING**. -/

/-- **INHERITED (aliasing).**  The intrinsic positively oriented orthonormal frame carrier. -/
abbrev FramePlus := NullSectorTask24.FramePlus

/-- **INHERITED (aliasing).**  The visible carrier acting on `FramePlus`. -/
abbrev Gvis := NullSectorTask24.Gvis

/-- **INHERITED (aliasing).**  The packaged internal carrier (`Lift` of the task statement). -/
abbrev LiftGrp := NullSectorTask24.LiftGrp

/-- **INHERITED (aliasing).**  The lifted frame carrier over a temporary reference frame. -/
abbrev LiftedFrame (F₀ : FramePlus) := NullSectorTask24.LiftedFrame F₀

/-- **INHERITED (packaging).**  The free and transitive visible action downstairs. -/
theorem inherited_framePlus_free_transitive :
    Nonempty FramePlus ∧ (∀ (g : Gvis) (F : FramePlus), g • F = F → g = 1) ∧
      (∀ F G : FramePlus, ∃! g : Gvis, g • F = G) :=
  framePlus_free_transitive

/-- **INHERITED (packaging).**  The lifted frame projection. -/
theorem inherited_liftedFrameProj (F₀ : FramePlus) (x : LiftedFrame F₀) :
    liftedFrameProj F₀ x = x.frame := rfl

/-- **INHERITED (packaging).**  The certified projection is surjective. -/
theorem inherited_projCore_surjective : Function.Surjective projCore := projCore_surjective

/-- **INHERITED (packaging).**  The kernel of the certified projection has exactly the two
elements `1` and the sign element. -/
theorem inherited_kerSign_elements {e : LiftGrp} : e ∈ KerSign ↔ (e = 1 ∨ e = lNegOne) :=
  mem_KerSign_iff'

/-- **INHERITED (packaging).**  The kernel-sign action on the lifted carrier. -/
theorem inherited_signSmul (F₀ : FramePlus) (e : KerSign) (x : LiftedFrame F₀) :
    (signSmul F₀ e x).elt = (e : LiftGrp) * x.elt := rfl

/-- **INHERITED (packaging).**  The unique visible reference change downstairs. -/
theorem inherited_reference_change_unique (F₀ F₁ : FramePlus) : ∃! g : Gvis, g • F₀ = F₁ :=
  existsUnique_gvis_map_frame F₀ F₁

/-! ## Package B — the full internal action upstairs (items 19–24)

The action is constructed directly on the internal representative, *not* transported through
the Task-24 carrier equivalence `LiftedFrame F₀ ≃ LiftGrp`: the ordinary-frame component is
moved by the projection of the acting element, which is exactly the geometry required by
item 24. -/

/-- **NEWLY DEFINED (item 19), principal.**  The natural action of the internal carrier on the
lifted frame carrier: the internal component is multiplied on the left, and the ordinary-frame
component is moved by the visible image of the acting element.

Item 20 (the defining lifted-frame compatibility condition) is discharged inside the
definition: `projCore (a * x.elt) • F₀ = projCore a • (projCore x.elt • F₀) = projCore a •
x.frame`. -/
noncomputable def liftSmul (F₀ : FramePlus) (a : LiftGrp) (x : LiftedFrame F₀) :
    LiftedFrame F₀ :=
  ⟨(a * x.elt, projCore a • x.frame), by
    show projCore (a * x.elt) • F₀ = projCore a • x.frame
    rw [map_mul, mul_smul, x.spec]⟩

noncomputable instance instSMulLiftGrpLiftedFrame (F₀ : FramePlus) :
    SMul LiftGrp (LiftedFrame F₀) := ⟨liftSmul F₀⟩

@[simp] theorem liftSmul_elt (F₀ : FramePlus) (a : LiftGrp) (x : LiftedFrame F₀) :
    (a • x).elt = a * x.elt := rfl

@[simp] theorem liftSmul_frame (F₀ : FramePlus) (a : LiftGrp) (x : LiftedFrame F₀) :
    (a • x).frame = projCore a • x.frame := rfl

/-- **DERIVED (item 20).**  The result of the action satisfies the defining lifted-frame
compatibility condition (restated explicitly, although it is already part of the subtype). -/
theorem liftSmul_spec (F₀ : FramePlus) (a : LiftGrp) (x : LiftedFrame F₀) :
    projCore ((a • x).elt) • F₀ = (a • x).frame := (a • x).spec

/-- **DERIVED (item 21), principal endpoint.**  The identity acts trivially. -/
theorem liftSmul_one (F₀ : FramePlus) (x : LiftedFrame F₀) : (1 : LiftGrp) • x = x :=
  NullSectorTask24.LiftedFrame.ext (by simp)

/-- **DERIVED (item 22), principal endpoint.**  Action compatibility with multiplication. -/
theorem liftSmul_mul (F₀ : FramePlus) (a b : LiftGrp) (x : LiftedFrame F₀) :
    (a * b) • x = a • (b • x) :=
  NullSectorTask24.LiftedFrame.ext (by simp [mul_assoc])

/-- **PACKAGE B (item 23), principal endpoint.**  The genuine group action `LiftGrp ↷
LiftedFrame F₀`. -/
noncomputable instance instMulActionLiftGrpLiftedFrame (F₀ : FramePlus) :
    MulAction LiftGrp (LiftedFrame F₀) where
  one_smul := liftSmul_one F₀
  mul_smul := liftSmul_mul F₀

/-! ## Package C — freeness upstairs (items 25–28) -/

/-- **PACKAGE C (item 26), principal endpoint.**  The internal action on the *lifted* frame
carrier is free.  The proof is the preferred one: equality of lifted frames forces equality of
the internal components, and the internal component is then cancelled in the group. -/
theorem liftedFrameAction_free (F₀ : FramePlus) {a : LiftGrp} {x : LiftedFrame F₀}
    (h : a • x = x) : a = 1 := by
  have hval : a * x.elt = x.elt := congrArg NullSectorTask24.LiftedFrame.elt h
  have h2 := congrArg (fun u : LiftGrp => u * x.elt⁻¹) hval
  simpa [mul_assoc] using h2

theorem liftedFrameAction_free_iff (F₀ : FramePlus) (a : LiftGrp) (x : LiftedFrame F₀) :
    a • x = x ↔ a = 1 := by
  refine ⟨fun h => liftedFrameAction_free F₀ h, ?_⟩
  rintro rfl
  exact liftSmul_one F₀ x

/-- **PACKAGE C.**  Cancellation form of freeness. -/
theorem liftedFrameAction_cancel (F₀ : FramePlus) {a b : LiftGrp} {x : LiftedFrame F₀}
    (h : a • x = b • x) : a = b := by
  have h1 : (b⁻¹ * a) • x = x := by
    rw [liftSmul_mul, h, ← liftSmul_mul, inv_mul_cancel, liftSmul_one]
  exact (inv_mul_eq_one.1 (liftedFrameAction_free F₀ h1)).symm

/-- **PACKAGE C.**  Freeness in stabilizer form. -/
theorem stabilizer_liftedFrame_eq_bot (F₀ : FramePlus) (x : LiftedFrame F₀) :
    MulAction.stabilizer LiftGrp x = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun _ hg =>
    liftedFrameAction_free F₀ (MulAction.mem_stabilizer_iff.1 hg)

/-- **PACKAGE C (item 27), negative comparison, stated side by side with the previous
theorem (item 28).**  On the *ordinary* frame carrier the same group does **not** act freely:
its stabilizer at every frame is exactly `KerSign`, and the nontrivial kernel sign acts
trivially.  The two carriers are kept strictly apart: `liftedFrameAction_free` speaks about
`LiftedFrame F₀`, the statement below about `FramePlus`. -/
theorem liftedFrameAction_free_versus_framePlus (F₀ : FramePlus) :
    (∀ (a : LiftGrp) (x : LiftedFrame F₀), a • x = x → a = 1) ∧
      (∀ F : FramePlus, MulAction.stabilizer LiftGrp F = KerSign) ∧
      (∃ a : LiftGrp, a ≠ 1 ∧ ∀ F : FramePlus, a • F = F) :=
  ⟨fun _ _ h => liftedFrameAction_free F₀ h, lact_stabilizer, lact_not_free⟩

/-! ## Package D — transitivity upstairs (items 29–35) -/

/-- **DERIVED (item 30).**  The internal component of the explicit transporter. -/
theorem liftedFrame_transporter_elt (F₀ : FramePlus) (x y : LiftedFrame F₀) :
    ((y.elt * x.elt⁻¹) • x).elt = y.elt := by
  simp [mul_assoc]

/-- **DERIVED (item 31).**  The ordinary-frame component of the explicit transporter. -/
theorem liftedFrame_transporter_frame (F₀ : FramePlus) (x y : LiftedFrame F₀) :
    ((y.elt * x.elt⁻¹) • x).frame = y.frame := by
  rw [← ((y.elt * x.elt⁻¹) • x).spec, ← y.spec, liftedFrame_transporter_elt]

/-- **PACKAGE D (item 32), principal endpoint.**  The internal action on the lifted frame
carrier is transitive, with the explicit transporter `y.elt * x.elt⁻¹`. -/
theorem liftedFrameAction_transitive (F₀ : FramePlus) (x y : LiftedFrame F₀) :
    ∃ a : LiftGrp, a • x = y :=
  ⟨y.elt * x.elt⁻¹, NullSectorTask24.LiftedFrame.ext (liftedFrame_transporter_elt F₀ x y)⟩

noncomputable instance (F₀ : FramePlus) :
    MulAction.IsPretransitive LiftGrp (LiftedFrame F₀) :=
  ⟨fun x y => liftedFrameAction_transitive F₀ x y⟩

/-- **PACKAGE D (item 34), principal endpoint.**  Combining transitivity with freeness:
exactly one internal element carries a given lifted frame to another. -/
theorem existsUnique_lift_map_liftedFrame (F₀ : FramePlus) (x y : LiftedFrame F₀) :
    ∃! a : LiftGrp, a • x = y := by
  obtain ⟨a, ha⟩ := liftedFrameAction_transitive F₀ x y
  exact ⟨a, ha, fun b hb => liftedFrameAction_cancel F₀ (hb.trans ha.symm)⟩

/-- **PACKAGE D (item 35), principal endpoint.**  The packaged statement: for each temporary
reference frame the lifted frame carrier is a nonempty, free and transitive `LiftGrp`-set.
Only elementary `Free` + `Transitive` + `ExistsUnique` statements are used; no general torsor
API is adapted (item 35, second clause). -/
theorem liftedFrame_free_transitive (F₀ : FramePlus) :
    Nonempty (LiftedFrame F₀) ∧
      (∀ (a : LiftGrp) (x : LiftedFrame F₀), a • x = x → a = 1) ∧
      (∀ x y : LiftedFrame F₀, ∃! a : LiftGrp, a • x = y) :=
  ⟨⟨NullSectorTask24.LiftedFrame.mk F₀ 1⟩, fun _ _ h => liftedFrameAction_free F₀ h,
    existsUnique_lift_map_liftedFrame F₀⟩

end NullSectorTask25
