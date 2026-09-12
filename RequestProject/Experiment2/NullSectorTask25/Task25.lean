import RequestProject.Experiment2.NullSectorTask25.OneFiberInterface

/-!
# Task 25 — principal endpoints

This module imports the complete Task-25 development and exposes the principal theorems under
stable names, followed by an axiom report (`#print axioms`) on each of them.

Inherited naming: the informal `Lift` and `proj` of the task statement are the inherited
Task-21/24 objects `LiftGrp` (`= NullSectorTask21.LiftG`) and `projCore : LiftGrp →* Gvis`.
No Task-24 declaration was modified; the only change to inherited files is none at all —
Task 25 is a pure extension.

| Question | Verdict |
| --- | --- |
| Natural `Lift` action on `LiftedFrame` defined? | `PROVED` (`liftSmul`) |
| Action laws? | `PROVED` (`liftSmul_one`, `liftSmul_mul`) |
| Action free? | `PROVED` (`liftedFrameAction_free`) |
| Action transitive? | `PROVED` (`liftedFrameAction_transitive`) |
| Unique `Lift` element between lifted frames? | `PROVED` (`existsUnique_lift_map_liftedFrame`) |
| Projection to ordinary frames equivariant? | `PROVED` (`liftedFrameProj_equivariant`) |
| Kernel restriction equals existing sign action? | `PROVED` (`liftSmul_restrict_kerSign_eq_signSmul`) |
| Kernel signs act trivially downstairs? | `PROVED` (`kerSign_trivial_downstairs`) |
| Kernel signs act freely upstairs? | `PROVED` (`kerSign_free_upstairs`) |
| `liftedEltEquiv` action-equivariant? | `PROVED` (`liftedEltEquiv_equivariant`) |
| Downstairs reference change unique? | `INHERITED` (`existsUnique_gvis_map_frame`) |
| Exactly two lifted reference changes? | `PROVED` (`liftsOf_reference_change_ncard`) |
| Difference of lifted reference changes exactly one kernel sign? | `PROVED` (`lifts_differ_unique_kerSign`) |
| Lifted transfer equivariant? | `PROVED` (`liftedTransfer_equivariant`, unconjugated convention) |
| Two transfer maps differ by unique kernel sign? | `PROVED` (`liftedTransfer_difference_unique_kerSign`) |
| One-fibre interface reference-independent? | `PROVED` (`oneFiberInterface_reference_independent`) |
| Nontrivial varying base introduced? | `NO` |
| Frame bundle constructed? | `NO` |
| Principal bundle constructed? | `NO` |
| Spin structure constructed? | `NO` |
| Physical spin derived? | `NO` |
-/

set_option maxHeartbeats 1000000

namespace NullSectorTask25

open NullSectorTask20 NullSectorTask21 NullSectorTask23 NullSectorTask24

/-! ## Priority 1 — the action upstairs -/

/-- Principal endpoint 1: the natural internal action on the lifted frame carrier. -/
noncomputable def task25_liftSmul (F₀ : FramePlus) : LiftGrp → LiftedFrame F₀ → LiftedFrame F₀ :=
  liftSmul F₀

alias task25_action_one := liftSmul_one
alias task25_action_mul := liftSmul_mul
alias task25_action_free := liftedFrameAction_free
alias task25_action_transitive := liftedFrameAction_transitive
alias task25_existsUnique_lift_map_liftedFrame := existsUnique_lift_map_liftedFrame
alias task25_free_transitive := liftedFrame_free_transitive
alias task25_free_upstairs_not_free_downstairs := liftedFrameAction_free_versus_framePlus

/-! ## Priority 1 — equivariance and the kernel restriction -/

alias task25_liftedFrameProj_equivariant := liftedFrameProj_equivariant
alias task25_commuting_square := liftedFrame_commuting_square
alias task25_liftSmul_restrict_kerSign_eq_signSmul := liftSmul_restrict_kerSign_eq_signSmul
alias task25_kerSign_trivial_downstairs := kerSign_trivial_downstairs
alias task25_kerSign_free_upstairs := kerSign_free_upstairs
alias task25_fibre_free_transitive_kerSign := fibre_free_transitive_kerSign

/-! ## Priority 2 — reference-change closure -/

alias task25_liftedEltEquiv_equivariant := liftedEltEquiv_equivariant
alias task25_liftedEltEquiv_equivariant_pair := liftedEltEquiv_equivariant_pair
alias task25_two_lifts_of_reference_change := two_lifts_of_reference_change
alias task25_liftsOf_reference_change_ncard := liftsOf_reference_change_ncard
alias task25_lifts_differ_unique_kerSign := lifts_differ_unique_kerSign
alias task25_liftsOf_eq_kerSign_orbit := liftsOf_eq_kerSign_orbit
alias task25_liftedTransfer_equivariant := liftedTransfer_equivariant
alias task25_liftedTransfer_kerSign := liftedTransfer_kerSign
alias task25_liftedTransfer_difference_unique_kerSign :=
  liftedTransfer_difference_unique_kerSign
alias task25_liftedTransfer_sign_shift := liftedTransfer_sign_shift
alias task25_reference_change_downstairs_unique_upstairs_two :=
  reference_change_downstairs_unique_upstairs_two

/-! ## Priority 3 — the frozen one-fibre interface -/

/-- Principal endpoint: the one-fibre interface attached to a temporary reference frame. -/
noncomputable def task25_oneFiberInterface : FramePlus → OneFiberLiftInterface :=
  oneFiberInterface

alias task25_oneFiberInterface_kerSign_eq_signSmul := oneFiberInterface_kerSign_eq_signSmul
alias task25_oneFiberInterface_reference_independent :=
  oneFiberInterface_reference_independent
alias task25_oneFiberInterfaceEquiv_ambiguity := oneFiberInterfaceEquiv_ambiguity
alias task25_one_fibre_only := one_fibre_only

/-! ## Negative controls -/

alias task25_nonequivariant_carrier_equiv := exists_nonequivariant_carrier_equiv
alias task25_liftSmul_changes_fibre := exists_liftSmul_changes_fibre
alias task25_reference_change_not_unique_upstairs := reference_change_not_unique_upstairs

/-! ## The Task-25 success criterion, in one theorem -/

/-- **TASK-25 FINAL ENDPOINT.**  For every temporary reference frame:

* the lifted frame carrier is a free and transitive `LiftGrp`-space;
* its projection to the ordinary frame carrier is equivariant along `projCore`;
* the restriction of the action to the kernel is exactly the inherited Task-24 sign action;
* the reference change downstairs is unique, while upstairs the possible lifted reference
  changes form exactly one free transitive two-element `KerSign`-family, so that all temporary
  reference choices are classified up to the same unique `Z₂` ambiguity. -/
theorem task25_final (F₀ F₁ : FramePlus) :
    (∀ (a : LiftGrp) (x : LiftedFrame F₀), a • x = x → a = 1) ∧
      (∀ x y : LiftedFrame F₀, ∃! a : LiftGrp, a • x = y) ∧
      (∀ (a : LiftGrp) (x : LiftedFrame F₀),
        liftedFrameProj F₀ (a • x) = projCore a • liftedFrameProj F₀ x) ∧
      (∀ (e : KerSign) (x : LiftedFrame F₀), (e : LiftGrp) • x = signSmul F₀ e x) ∧
      (∃! g : Gvis, g • F₀ = F₁) ∧
      (liftsOf (frameHom F₀ F₁)).ncard = 2 ∧
      (∀ u v : LiftGrp, ∀ hu : projCore u = frameHom F₀ F₁,
        ∀ hv : projCore v = frameHom F₀ F₁,
          ∃! e : KerSign, ∀ x : LiftedFrame F₀,
            liftedTransfer F₀ F₁ v hv x = (e : LiftGrp) • liftedTransfer F₀ F₁ u hu x) ∧
      Nonempty (InterfaceEquiv (oneFiberInterface F₀) (oneFiberInterface F₁)) := by
  obtain ⟨hd, hn, ht⟩ := reference_change_downstairs_unique_upstairs_two F₀ F₁
  exact ⟨fun _ _ h => liftedFrameAction_free F₀ h, existsUnique_lift_map_liftedFrame F₀,
    liftedFrameProj_equivariant F₀, liftSmul_restrict_kerSign_eq_signSmul F₀, hd, hn, ht,
    oneFiberInterface_reference_independent F₀ F₁⟩

/-! ## Axiom report -/

#print axioms task25_liftSmul
#print axioms task25_action_one
#print axioms task25_action_mul
#print axioms task25_action_free
#print axioms task25_action_transitive
#print axioms task25_existsUnique_lift_map_liftedFrame
#print axioms task25_free_transitive
#print axioms task25_free_upstairs_not_free_downstairs
#print axioms task25_liftedFrameProj_equivariant
#print axioms task25_commuting_square
#print axioms task25_liftSmul_restrict_kerSign_eq_signSmul
#print axioms task25_kerSign_trivial_downstairs
#print axioms task25_kerSign_free_upstairs
#print axioms task25_fibre_free_transitive_kerSign
#print axioms task25_liftedEltEquiv_equivariant
#print axioms task25_liftedEltEquiv_equivariant_pair
#print axioms task25_two_lifts_of_reference_change
#print axioms task25_liftsOf_reference_change_ncard
#print axioms task25_lifts_differ_unique_kerSign
#print axioms task25_liftsOf_eq_kerSign_orbit
#print axioms task25_liftedTransfer_equivariant
#print axioms task25_liftedTransfer_kerSign
#print axioms task25_liftedTransfer_difference_unique_kerSign
#print axioms task25_liftedTransfer_sign_shift
#print axioms task25_reference_change_downstairs_unique_upstairs_two
#print axioms task25_oneFiberInterface
#print axioms task25_oneFiberInterface_kerSign_eq_signSmul
#print axioms task25_oneFiberInterface_reference_independent
#print axioms task25_oneFiberInterfaceEquiv_ambiguity
#print axioms task25_one_fibre_only
#print axioms task25_nonequivariant_carrier_equiv
#print axioms task25_liftSmul_changes_fibre
#print axioms task25_reference_change_not_unique_upstairs
#print axioms task25_final

end NullSectorTask25
