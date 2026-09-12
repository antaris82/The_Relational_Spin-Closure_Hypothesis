import RequestProject.Experiment2.NullSectorTask21.NegativeControls

/-!
# Task 21 — Intrinsic/standard identification audit: principal endpoints

This module imports the complete Task-21 development and exposes the principal final
declarations.  **It contains no new mathematics**: every `task21_*` name below is an `alias`
of a theorem proved in a source module, the single composite equivalence
`liftZU2Split` is a composition of two equivalences already proved, and the remainder of the
file consists of `#print axioms` commands.

## Source order

`SafeBase → GroupPackaging → CoreQuaternionEquiv → SU2Model → VisibleRotationCandidate
→ CoreProjection → SectionObstruction → CentralComplex → CentralProduct
→ NormalizedCentralCarrier → SignStructures → TorsorPlacement → NegativeControls → Task21`

`SafeBase` and `GroupPackaging` are the two reconstruction modules; every later module is an
explicitly labelled identification / comparison module.

## Status table

| claim | Lean declaration | status |
| --- | --- | --- |
| `Lift ≃` unit quaternions | `liftQuatEquiv` | `PROVED` |
| the same maps are a homeomorphism | `liftQuatHomeo` | `PROVED` |
| `Lift ≃ SU(2)` | `liftSUEquiv`, `quatSUEquiv` | `PROVED` (abstract group equivalence) |
| `Gvis ≃ SO(3)` | `visibleRotationEquiv` | `PROVED` (abstract group equivalence) |
| intrinsic projection = quaternionic rotation map | `task21_projection_diagram` | `PROVED` |
| core kernel `= {±1}` | `task21_core_kernel`, `task21_quat_rotation_kernel` | `PROVED` |
| set-theoretic section exists | `task21_section_exists`, `task21_group_section_exists` | `PROVED` |
| quotient-compatible choice ↔ section | `task21_section_iff_choice` | `PROVED` |
| no continuous global section | `task21_no_continuous_section` | `PROVED` |
| `CUnit ≃ ℂˣ` | `cUnitComplexEquiv` | `PROVED` |
| `CUnit ∩ Lift = {±1}` | `task21_centre_core_intersection` | `PROVED` |
| product map surjective, diagonal-sign kernel | `task21_mu_surjective`, `task21_mu_kernel` | `PROVED` |
| `LiftZ` central-product quotient | `centralProductEquiv`, `liftZStandardEquiv` | `PROVED` |
| `ℂˣ ≃ ℝ₊ × U(1)` | `polarEquiv` | `PROVED` |
| positive modulus splits from `LiftZ` | `liftZSplit` | `PROVED` |
| normalized quotient `(U(1) × UQ)/Δℤ₂` | `normalizedQuotientEquiv`, `task21_normalized_kernel` | `PROVED` |
| normalized carrier `≃ U(2)` | `normalizedU2Equiv` | `PROVED` (abstract group equivalence) |
| full carrier `≃ ℝ₊ × U(2)` | `liftZU2Split` | `PROVED` (composition of the two above) |
| core sign distinct from direction reversal | `task21_sign_structures_distinct` | `PROVED` |
| half-odd labels are central phase weights | `task21_phase_weight` | `PROVED` |
| full turn ↔ integer difference | `task21_full_turn_integer` | `PROVED` |
| mod-2 information loss | `task21_full_turn_parity_only` | `PROVED` |
| negative controls | `task21_controls` | `PROVED` |

Every equivalence recorded above is an equivalence of **abstract multiplicative groups**,
except `liftQuatHomeo`, which is the only statement of this development in which topology is
part of the conclusion.  No Lie-group or smooth-structure claim is made anywhere.
-/

namespace NullSectorTask21

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20

open Quaternion Matrix

/-! ## Core carrier -/

alias task21_core_quaternion_one := liftQuatEquiv_one
alias task21_core_quaternion_mul := liftQuatEquiv_mul
alias task21_core_quaternion_inv := liftQuatEquiv_inv
alias task21_core_quaternion_inverse_identities := liftQuatEquiv_inverse_identities
alias task21_core_homeomorphism_same_map := liftQuatHomeo_coe

/-! ## Standard special unitary model -/

alias task21_su2_injective := toSU_injective
alias task21_su2_surjective := toSU_surjective

/-! ## Visible group -/

alias task21_visible_injective := toRot_injective
alias task21_visible_surjective := toRot_surjective

/-! ## Core projection -/

alias task21_projection_diagram := coreProjection_diagram
alias task21_quat_rotation_kernel := quatRot_kernel
alias task21_core_kernel := ker_projCore
alias task21_projection_surjective := projCore_surjective

/-! ## Section obstruction -/

alias task21_group_section_exists := exists_group_section
alias task21_section_exists := exists_core_section
alias task21_section_iff_choice := continuous_section_iff_continuous_choice
alias task21_no_continuous_section := no_continuous_core_section
alias task21_section_and_relations := section_and_relation_completeness

/-! ## Continuous centre -/

alias task21_centre_coefficient := cUnitComplexEquiv_apply
alias task21_centre_continuous := continuous_toComplex
alias task21_centre_continuous_inverse := continuous_ofComplex

/-! ## Full central product -/

alias task21_centre_core_intersection := CUnit_inter_Lift
alias task21_centre_core_intersection_packaged := inter_CUnitG_LiftG
alias task21_mu_surjective := mu_surjective
alias task21_mu_kernel := ker_mu
alias task21_mu_std_surjective := muStd_surjective
alias task21_mu_std_kernel := ker_muStd

/-! ## Normalization -/

alias task21_polar_modulus := polarEquiv_fst
alias task21_polar_phase := polarEquiv_snd
alias task21_split_injective := splitMap_injective
alias task21_split_surjective := splitMap_surjective
alias task21_normalized_surjective := muNorm_surjective
alias task21_normalized_kernel := ker_muNorm
alias task21_u2_surjective := nuU2_surjective
alias task21_u2_kernel := ker_nuU2

/-- **TASK-21 ENDPOINT (packaging only).**  The composition of the proved modulus split
`LiftZG ≃* Rpos × LiftZ1G` with the proved normalized identification
`LiftZ1G ≃* U(2)`.  No new mathematical content: both factors are already proved. -/
noncomputable def liftZU2Split : LiftZG ≃* Rpos × Matrix.unitaryGroup (Fin 2) ℂ :=
  liftZSplit.trans ((MulEquiv.refl Rpos).prodCongr normalizedU2Equiv)

/-! ## Sign structures and the torsor placement -/

alias task21_core_sign_invisible := projCore_sign
alias task21_core_sign_free := core_sign_free
alias task21_sign_structures_distinct := two_sign_structures_distinct
alias task21_reversal_quotient_not_two_element := revQuot_not_two_element
alias task21_phase_weight := toComplex_labelBridge_circle
alias task21_full_turn_integer := full_turn_eq_iff_int_difference
alias task21_label_differences_integers := halfOdd_differences_are_integers
alias task21_full_turn_parity_only := full_turn_remembers_only_parity

/-! ## Negative controls -/

alias task21_projection_not_injective := projCore_not_injective
alias task21_visible_noncommuting := visible_noncommuting
alias task21_kernel_does_not_determine := kernel_does_not_determine_map
alias task21_central_identification_not_unique := central_identification_not_unique
alias task21_controls := task21_negative_controls

/-! ## Axiom audit -/

#print axioms liftQuatEquiv
#print axioms liftQuatHomeo
#print axioms quatSUEquiv
#print axioms liftSUEquiv
#print axioms visibleRotationEquiv
#print axioms projCore
#print axioms projZ
#print axioms cUnitComplexEquiv
#print axioms mu
#print axioms centralProductEquiv
#print axioms muStd
#print axioms liftZStandardEquiv
#print axioms polarEquiv
#print axioms posCentral
#print axioms splitMap
#print axioms liftZSplit
#print axioms muNorm
#print axioms normalizedQuotientEquiv
#print axioms nuU2
#print axioms normalizedU2Equiv
#print axioms liftZU2Split

#print axioms task21_core_quaternion_one
#print axioms task21_core_quaternion_mul
#print axioms task21_core_quaternion_inv
#print axioms task21_core_quaternion_inverse_identities
#print axioms task21_core_homeomorphism_same_map
#print axioms task21_su2_injective
#print axioms task21_su2_surjective
#print axioms task21_visible_injective
#print axioms task21_visible_surjective
#print axioms task21_projection_diagram
#print axioms task21_quat_rotation_kernel
#print axioms task21_core_kernel
#print axioms task21_projection_surjective
#print axioms task21_group_section_exists
#print axioms task21_section_exists
#print axioms task21_section_iff_choice
#print axioms task21_no_continuous_section
#print axioms task21_section_and_relations
#print axioms task21_centre_coefficient
#print axioms task21_centre_continuous
#print axioms task21_centre_continuous_inverse
#print axioms task21_centre_core_intersection
#print axioms task21_centre_core_intersection_packaged
#print axioms task21_mu_surjective
#print axioms task21_mu_kernel
#print axioms task21_mu_std_surjective
#print axioms task21_mu_std_kernel
#print axioms task21_polar_modulus
#print axioms task21_polar_phase
#print axioms task21_split_injective
#print axioms task21_split_surjective
#print axioms task21_normalized_surjective
#print axioms task21_normalized_kernel
#print axioms task21_u2_surjective
#print axioms task21_u2_kernel
#print axioms task21_core_sign_invisible
#print axioms task21_core_sign_free
#print axioms task21_sign_structures_distinct
#print axioms task21_reversal_quotient_not_two_element
#print axioms task21_phase_weight
#print axioms task21_full_turn_integer
#print axioms task21_label_differences_integers
#print axioms task21_full_turn_parity_only
#print axioms task21_projection_not_injective
#print axioms task21_visible_noncommuting
#print axioms task21_kernel_does_not_determine
#print axioms task21_central_identification_not_unique
#print axioms task21_controls

end NullSectorTask21
