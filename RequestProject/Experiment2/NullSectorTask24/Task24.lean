import RequestProject.Experiment2.NullSectorTask24.Comparison

/-!
# Task 24 — principal endpoints

This module imports the complete Task-24 development and exposes the principal theorems
under stable names, followed by an axiom report (`#print axioms`) on each of them.

| Question | Verdict |
| --- | --- |
| Intrinsic oriented orthonormal frame carrier constructed? | `PROVED` (`FramePlus`) |
| Definition independent of `Gvis`? | `PROVED` (by inspection of the definition; the visible carrier occurs nowhere in it) |
| Definition independent of reference frame? | `PROVED` (a coordinate frame is used only for nonemptiness) |
| `Gvis` acts on frames? | `PROVED` |
| Action free? | `PROVED` |
| Action transitive? | `PROVED` |
| Unique `Gvis` element between any two frames? | `PROVED` |
| Reference frame yields coordinate equivalence `Gvis ≃ FramePlus`? | `PROVED` (set/group level; no topology) |
| Change of reference explicitly classified? | `PROVED` |
| Lifted-frame carrier constructed? | `PROVED` |
| Exactly two lifted representatives per frame? | `PROVED` |
| Difference exactly `{±1}`? | `PROVED` |
| Lifted construction reference-independent? | `PROVED` (explicit equivalence, canonical up to a kernel sign, which is itself classified) |
| Stabilizer of `Lift` action exactly `{±1}`? | `PROVED` |
| Task-XXIII local signs compatible with lifted-frame signs? | `PROVED` (one compatibility theorem) |
| Frame bundle over nontrivial base constructed? | `NO` |
| Spin structure constructed? | `NO` |
| Physical spin derived? | `NO` |
-/

set_option maxHeartbeats 1000000

namespace NullSectorTask24

open NullSectorTask20 NullSectorTask21 NullSectorTask23

/-! ## Package B — the intrinsic frame carrier -/

alias task24_framePlus_nonempty := framePlus_nonempty
alias task24_frame_ext := FramePlus.ext_iff_three
alias task24_frame_span := frame_span
alias task24_frame_linearIndependent := frame_linearIndependent
alias task24_frame_expand := frame_expand

/-- Principal endpoint: every intrinsic frame is a basis of the carrier. -/
noncomputable def task24_frameBasis : FramePlus → Module.Basis (Fin 3) ℝ E := frameBasis

/-! ## Package C — the visible action on frames -/

alias task24_frames_orthonormal_preserved := gact_orthonormalTriple
alias task24_frames_orientation_preserved := gact_positivelyOriented
alias task24_frame_action_one := frame_one_smul
alias task24_frame_action_mul := frame_mul_smul

/-! ## Packages D and E — free and transitive -/

alias task24_frameAction_free := frameAction_free
alias task24_frameAction_transitive := frameAction_transitive
alias task24_existsUnique_gvis_map_frame := existsUnique_gvis_map_frame
alias task24_framePlus_free_transitive := framePlus_free_transitive
alias task24_stabilizer_frame_eq_bot := stabilizer_frame_eq_bot

/-! ## Package F — reference frames coordinatize -/

/-- Principal endpoint: the coordinate equivalence attached to a reference frame. -/
noncomputable def task24_coordEquiv : FramePlus → (Gvis ≃ FramePlus) := coordEquiv

alias task24_coord_bijective := coord_bijective
alias task24_change_of_reference := coord_change
alias task24_change_of_reference_equiv := coordEquiv_change
alias task24_reference_independence := reference_independence
alias task24_reference_not_intrinsic := coord_ne_of_ne

/-! ## Package G — the lifted frame carrier -/

alias task24_liftedFrameProj_surjective := liftedFrameProj_surjective
alias task24_two_lifts := two_lifts
alias task24_lifted_fibre_ncard := lifted_fibre_ncard
alias task24_lifts_differ_by_unique_sign := liftedFrame_eq_iff_sign
alias task24_sign_action_free := signSmul_free

/-- Principal endpoint: the quotient of the lifted frame carrier by the kernel sign is the
ordinary frame carrier. -/
noncomputable def task24_liftedQuotientEquiv (F₀ : FramePlus) :
    Quotient (liftedSetoid F₀) ≃ FramePlus := liftedQuotientEquiv F₀

/-! ## Package H — reference independence of the lifted construction -/

/-- Principal endpoint: the explicit equivalence of the two lifted carriers. -/
noncomputable def task24_liftedTransfer (F₀ F₁ : FramePlus) (u₀ : LiftGrp)
    (h₀ : projCore u₀ = frameHom F₀ F₁) : LiftedFrame F₀ ≃ LiftedFrame F₁ :=
  liftedTransfer F₀ F₁ u₀ h₀

alias task24_liftedTransfer_proj := liftedTransfer_proj
alias task24_liftedTransfer_sign := liftedTransfer_sign
alias task24_liftedTransfer_choice := liftedTransfer_choice

/-! ## Package I — the internal carrier acting on frames -/

alias task24_lact_transitive := lact_transitive
alias task24_lact_stabilizer := lact_stabilizer
alias task24_lact_eq_iff := lact_eq_iff
alias task24_lact_not_free := lact_not_free

/-! ## Package J and the negative controls -/

alias task24_local_cover_compatibility := localLiftedFrame_overlap
alias task24_no_gvis_fixed_frame := no_gvis_fixed_frame
alias task24_liftedFrameProj_not_injective := liftedFrameProj_not_injective

/-! ## Axiom report -/

#print axioms task24_framePlus_nonempty
#print axioms task24_frame_ext
#print axioms task24_frame_span
#print axioms task24_frame_linearIndependent
#print axioms task24_frame_expand
#print axioms task24_frameBasis
#print axioms task24_frames_orthonormal_preserved
#print axioms task24_frames_orientation_preserved
#print axioms task24_frame_action_one
#print axioms task24_frame_action_mul
#print axioms task24_frameAction_free
#print axioms task24_frameAction_transitive
#print axioms task24_existsUnique_gvis_map_frame
#print axioms task24_framePlus_free_transitive
#print axioms task24_stabilizer_frame_eq_bot
#print axioms task24_coordEquiv
#print axioms task24_coord_bijective
#print axioms task24_change_of_reference
#print axioms task24_change_of_reference_equiv
#print axioms task24_reference_independence
#print axioms task24_reference_not_intrinsic
#print axioms task24_liftedFrameProj_surjective
#print axioms task24_two_lifts
#print axioms task24_lifted_fibre_ncard
#print axioms task24_lifts_differ_by_unique_sign
#print axioms task24_sign_action_free
#print axioms task24_liftedQuotientEquiv
#print axioms task24_liftedTransfer
#print axioms task24_liftedTransfer_proj
#print axioms task24_liftedTransfer_sign
#print axioms task24_liftedTransfer_choice
#print axioms task24_lact_transitive
#print axioms task24_lact_stabilizer
#print axioms task24_lact_eq_iff
#print axioms task24_lact_not_free
#print axioms task24_local_cover_compatibility
#print axioms task24_no_gvis_fixed_frame
#print axioms task24_liftedFrameProj_not_injective

end NullSectorTask24
