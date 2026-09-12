import RequestProject.Experiment2.NullSectorTask23.Comparison

/-!
# Task 23 — Local decomposition and reconstruction of the certified double cover:
principal endpoints

This module imports the complete Task-23 development and exposes the principal final
declarations.  **It contains no new mathematics**: every `task23_*` name below is an `alias`
of a theorem proved in a source module, and the remainder of the file consists of
`#print axioms` commands.

## Source order

`SafeBase → Cover → Sections → Transitions → LocalProduct → Reconstruction → GlobalSection
→ OldDomains → OldBridges → Hierarchy → Comparison → Task23`

`Comparison` is the only identification module; every other module is intrinsic.

## Status table

| question | Lean declaration | verdict |
| --- | --- | --- |
| explicit open cover of the visible carrier | `task23_cover_open`, `task23_cover_covers` | `PROVED` |
| the cover is minimal among its subfamilies | `task23_cover_minimal` | `PROVED` |
| continuous local representatives | `task23_local_section`, `task23_local_section_continuous` | `PROVED` |
| unique `{+1,-1}` relative factor | `task23_transition`, `task23_transition_unique` | `PROVED` |
| transition factors continuous / locally constant | `task23_transition_continuous`, `task23_transition_locally_constant` | `PROVED` |
| overlaps connected? | `task23_overlap_not_preconnected` | `REFUTED` (componentwise data kept) |
| identity / inverse / triple-overlap laws | `task23_transition_id`, `task23_transition_inv`, `task23_transition_triple` | `PROVED` |
| local product decomposition | `task23_local_product` | `PROVED` (homeomorphism) |
| global carrier reconstructed from local pieces | `task23_reconstruction`, `task23_reconstruction_proj` | `PROVED` |
| old `Dom v` correspond exactly to the new domains | `task23_old_domain_map`, `task23_old_domain_fails` | `PARTIAL` / `REFUTED` |
| old core bridges reduce to transition signs | `task23_core_bridge_sign`, `task23_extended_bridge_not_sign` | `PROVED` / `REFUTED` for the extended case |
| integer label differences reduce by parity | `task23_parity`, `task23_full_turn_integer_trivial` | `PARTIAL` |
| sign data sufficient for the core carrier | `task23_level3` | `PROVED` |
| sign data sufficient for the extended carrier | `task23_extended_needs_more` | `REFUTED` |
| global section iff transitions trivializable | `task23_global_iff_trivializable` | `PROVED` |
| standard local two-sheeted structure identified | `task23_covering_map` | `PROVED` (comparison module only) |
| any frame bundle constructed | — | `NO` |
| any spin structure constructed | — | `NO` |
| any physical spin degree of freedom derived | — | `NO` |
-/

namespace NullSectorTask23

/-! ## Package A — the frozen projection -/

alias task23_projection_continuous := continuous_pr
alias task23_projection_surjective := pr_surjective
alias task23_fibre := pr_eq_iff
alias task23_fibre_sign_unique := sact_injective_sign
alias task23_kernel_sign_subgroup := KerSign_eq

/-! ## Package B — the explicit open cover -/

alias task23_cover_open := isOpen_Vset
alias task23_cover_covers := Vset_covers
alias task23_cover_minimal := Vset_minimal

/-! ## Package C — continuous local representatives -/

alias task23_local_section := pr_sec
alias task23_local_section_continuous := continuous_sec
alias task23_local_section_unique := sec_unique
alias task23_local_section_normalizations := secNeg_spec
alias task23_local_section_sign_unique := section_sign_unique

/-! ## Packages D and E — the transition data and their laws -/

alias task23_transition := sec_eq_tau_smul
alias task23_transition_unique := tauAt_unique
alias task23_transition_continuous := continuous_tau
alias task23_transition_locally_constant := isLocallyConstant_tau
alias task23_transition_const_on_preconnected := tau_const_of_isPreconnected
alias task23_overlap_not_preconnected := ovl_not_preconnected
alias task23_transition_id := tauAt_self
alias task23_transition_inv := tauAt_symm
alias task23_transition_inv_order_two := tauAt_symm'
alias task23_transition_triple := tauAt_trans

/-! ## Package F — the local product decomposition -/

alias task23_local_product := preimageProdHomeo
alias task23_local_product_over_base := preimageProdHomeo_fst

/-! ## Package G — the reconstruction (principal endpoint) -/

alias task23_reconstruction := liftLocalHomeo
alias task23_reconstruction_proj := pr_toLift
alias task23_reconstruction_injective := toLift_injective
alias task23_reconstruction_surjective := toLift_surjective

/-! ## Package H — comparison with the old direction domains -/

alias task23_old_domain_map := visOf_mem_Vset_one_iff_Dom
alias task23_old_domain_induces_section := sec_one_eq_Un
alias task23_old_domain_fails := Vset_zero_not_from_Dom
alias task23_local_section_is_signed_reference := sec_eq_sign_Un

/-! ## Package I — comparison with the old bridges -/

alias task23_core_bridge_sign := core_relative_factor
alias task23_extended_bridge_not_sign := extended_relative_factor_not_sign
alias task23_old_family_not_core := locFam_notMem_Lift
alias task23_extended_kernel_continuum := extended_kernel_continuum

/-! ## Package J — the integer labels -/

alias task23_parity := parityMap_eq_one_iff
alias task23_parity_surjective := parityMap_surjective
alias task23_parity_shift := Un_shift
alias task23_full_turn_integer_trivial := full_turn_integer_label_trivial
alias task23_label_invisible := label_invisible_to_core
alias task23_labels_same_sign := distinct_labels_same_sign

/-! ## Package K — the reconstruction hierarchy -/

alias task23_level1 := level1_insufficient
alias task23_level2 := level2_insufficient
alias task23_level3 := level3_sufficient
alias task23_extended_needs_more := core_two_extended_infinite

/-! ## Package L — the global-section obstruction, read locally -/

alias task23_no_global_section := no_continuous_global_rep
alias task23_global_iff_trivializable := globalRep_iff_trivializable
alias task23_no_trivialization := no_continuous_trivialization
alias task23_unavoidable_sign := exists_nontrivial_overlap_sign

/-! ## Package M — comparison-only identification -/

alias task23_ingredient_list := task23_ingredients
alias task23_covering_map := isCoveringMap_pr
alias task23_controls := task23_negative_controls

/-! ## Axiom audit -/

#print axioms task23_projection_continuous
#print axioms task23_projection_surjective
#print axioms task23_fibre
#print axioms task23_fibre_sign_unique
#print axioms task23_kernel_sign_subgroup
#print axioms task23_cover_open
#print axioms task23_cover_covers
#print axioms task23_cover_minimal
#print axioms task23_local_section
#print axioms task23_local_section_continuous
#print axioms task23_local_section_unique
#print axioms task23_local_section_normalizations
#print axioms task23_local_section_sign_unique
#print axioms task23_transition
#print axioms task23_transition_unique
#print axioms task23_transition_continuous
#print axioms task23_transition_locally_constant
#print axioms task23_transition_const_on_preconnected
#print axioms task23_overlap_not_preconnected
#print axioms task23_transition_id
#print axioms task23_transition_inv
#print axioms task23_transition_inv_order_two
#print axioms task23_transition_triple
#print axioms task23_local_product
#print axioms task23_local_product_over_base
#print axioms task23_reconstruction
#print axioms task23_reconstruction_proj
#print axioms task23_reconstruction_injective
#print axioms task23_reconstruction_surjective
#print axioms task23_old_domain_map
#print axioms task23_old_domain_induces_section
#print axioms task23_old_domain_fails
#print axioms task23_local_section_is_signed_reference
#print axioms task23_core_bridge_sign
#print axioms task23_extended_bridge_not_sign
#print axioms task23_old_family_not_core
#print axioms task23_extended_kernel_continuum
#print axioms task23_parity
#print axioms task23_parity_surjective
#print axioms task23_parity_shift
#print axioms task23_full_turn_integer_trivial
#print axioms task23_label_invisible
#print axioms task23_labels_same_sign
#print axioms task23_level1
#print axioms task23_level2
#print axioms task23_level3
#print axioms task23_extended_needs_more
#print axioms task23_no_global_section
#print axioms task23_global_iff_trivializable
#print axioms task23_no_trivialization
#print axioms task23_unavoidable_sign
#print axioms task23_ingredient_list
#print axioms task23_covering_map
#print axioms task23_controls

end NullSectorTask23
