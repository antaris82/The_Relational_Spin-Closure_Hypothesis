import RequestProject.Spine.AlgebraicTopology.Excision
import RequestProject.Spine.AlgebraicTopology.MayerVietoris
import RequestProject.Spine.AlgebraicTopology.SphereCover
import RequestProject.Spine.AlgebraicTopology.RelativeAcyclicity
import RequestProject.Spine.Nerve.Basic.CanonicalMap
import RequestProject.Spine.Nerve.CellFamily.TargetDecomposition
import RequestProject.Spine.Nerve.Comparison.BaseCase
import RequestProject.Spine.Nerve.Comparison.Blockers
import RequestProject.Spine.Nerve.Comparison.RelJ
import RequestProject.Spine.Nerve.Comparison.GlobalCohomology
import RequestProject.Spine.Nerve.Comparison.SkeletalInduction
import RequestProject.Spine.Nerve.Controls.ComparisonControls
import RequestProject.Spine.Nerve.Geometry.BoundarySphere
import RequestProject.Spine.Nerve.Geometry.CellSeparation
import RequestProject.Spine.Nerve.Geometry.PushoutRetraction
import RequestProject.Spine.Nerve.Geometry.RelativeHomotopy
import RequestProject.Spine.Nerve.Skeleton.RealizationMono
import RequestProject.Spine.Nerve.StandardCell.BoundaryTwoSetCover
import RequestProject.Spine.Nerve.StandardCell.CanonicalGenerator
import RequestProject.Spine.Nerve.StandardCell.Excision
import RequestProject.Spine.Nerve.StandardCell.RealizedSimplexHomology
import RequestProject.Spine.Nerve.StandardCell.RelativeComparison

/-!
# Stage 1.3 — the consolidated axiom audit

`#print axioms` on every principal declaration of the Stage-1.3 development: the relative
chain complexes and the pair long exact sequence, the skeletal attachment/pushout layer, the
point model and the geometry of the realized standard cell, subdivision and singular excision,
the singular-homology toolbox, the standard-cell homology, fundamental class and canonical
generator, the single-cell relative comparison, the source decomposition and the family
compatibility of the frozen `J`, the geometric cell separation, the direct-sum chain complexes and
their homology over an arbitrary index type, the relative cell-sum isomorphisms and the target
decomposition, and `RelJIsIso`.

Each must report exactly `[propext, Classical.choice, Quot.sound]`; in particular **no**
`sorryAx`, no `native_decide` axiom and no project-local `axiom`.

This module replaces the ten per-task audit modules of the historical layout.  It is a leaf:
no production module imports it.
-/

/-! ### relative chain complexes, the pair LES and the canonical relative comparison -/

namespace SpineTask14

-- WP3 : skeletal cell attachment
#print axioms SpineTask14.skelPiece_bijective
#print axioms SpineTask14.attachExtend
#print axioms SpineTask14.attachExtend_comp_skInc
#print axioms SpineTask14.attachExtend_cell
#print axioms SpineTask14.attachExtend_unique
#print axioms SpineTask14.mem_skeleton_of_not_epi
#print axioms SpineTask14.notMem_skeleton_of_epi

-- WP4 : realization
#print axioms SpineTask14.toTop_isPushout

-- WP7 : relative chains
#print axioms SpineTask14.relChainCx
#print axioms SpineTask14.relProj
#print axioms SpineTask14.relSC_shortExact
#print axioms SpineTask14.relSingSC_shortExact
#print axioms SpineTask14.relSimpSC_shortExact
#print axioms SpineTask14.relChainCxMap
#print axioms SpineTask14.relChainCxMap_relProj

-- WP8 : pair long exact sequence
#print axioms SpineTask14.pairDelta
#print axioms SpineTask14.pair_exact₁
#print axioms SpineTask14.pair_exact₂
#print axioms SpineTask14.pair_exact₃
#print axioms SpineTask14.pairDelta_naturality

-- WP13 : the τ₂ five lemma
#print axioms SpineTask14.mono_homologyMap_τ₂
#print axioms SpineTask14.epi_homologyMap_τ₂
#print axioms SpineTask14.isIso_homologyMap_τ₂
#print axioms SpineTask14.quasiIso_τ₂

-- WP12 : the canonical relative comparison
#print axioms SpineTask14.relJ
#print axioms SpineTask14.relJ_tau₂
#print axioms SpineTask14.relJ_generator
#print axioms SpineTask14.unit_skeletal_square

-- WP13 : the one-skeleton step
#print axioms SpineTask14.oneSkeletonStep
#print axioms SpineTask14.oneSkeletonStep_of_blockers

-- WP17 : controls
#print axioms SpineTask14.nakahara_filled_triangle
#print axioms SpineTask14.nakahara_circle_nontrivial
#print axioms SpineTask14.relChain_self_subsingleton
#print axioms SpineTask14.cellIndexTopEquiv

end SpineTask14

/-! ### the point model of geometric realization and the realized boundary -/

namespace SpineTask16

-- barycentric coordinate combinatorics
#print axioms SpineTask16.supp_nonempty
#print axioms SpineTask16.supp_map
#print axioms SpineTask16.map_restrict

-- WP1/WP3, Level A : representative existence
#print axioms SpineTask16.exists_representative

-- WP4 : barycentric coordinates on the realization of a representable
#print axioms SpineTask16.coord
#print axioms SpineTask16.coord_naturality

-- faces of the standard simplex
#print axioms SpineTask16.faceMap
#print axioms SpineTask16.subFaceMap_comp_ι
#print axioms SpineTask16.faceMap_comp_ι
#print axioms SpineTask16.bdCoord_faceMap

-- WP2/WP3, Level C : the point normal form
#print axioms SpineTask16.subNormalForm
#print axioms SpineTask16.normalForm

-- WP6/WP7 : the standard-cell monomorphism, and its subcomplex generalisation
#print axioms SpineTask16.subcomplexMono
#print axioms SpineTask16.standardCellMono

-- WP5/WP10 : the realized boundary
#print axioms SpineTask16.range_bdCoord
#print axioms SpineTask16.realized_boundary_eq_iUnion_faces
#print axioms SpineTask16.compl_range_bdCoord
#print axioms SpineTask16.range_realization_boundary

-- WP8 : the Task-15 reduction, consumed
#print axioms SpineTask16.realization_skInc_injective
#print axioms SpineTask16.realizationInjective
#print axioms SpineTask16.oneSkeletonStep
#print axioms SpineTask16.skeletalInduction
#print axioms SpineTask16.finiteDimensional_homologyIso

-- WP11 : smoke tests
#print axioms SpineTask16.boundaryZero_realization_isEmpty
#print axioms SpineTask16.boundaryOne_eq_vertex

end SpineTask16

/-! ### the topology of the realized standard cell and the boundary sphere -/

namespace SpineTask17

-- WP3 : the realized standard simplex as the geometric standard simplex
#print axioms SpineTask17.simplexHomeo
#print axioms SpineTask17.coe_simplexHomeo
#print axioms SpineTask17.simplexHomeo_naturality
#print axioms SpineTask17.simplexHomeo_vertex

-- WP5 : contractibility
#print axioms SpineTask17.contractibleSpace_realized_simplex

-- WP2 : compactness of realized subcomplexes, and the closed embeddings
#print axioms SpineTask17.subCover_surjective
#print axioms SpineTask17.compactSpace_realized_subcomplex
#print axioms SpineTask17.isClosedEmbedding_subCoord
#print axioms SpineTask17.isClosedEmbedding_realization_subcomplex
#print axioms SpineTask17.isClosedEmbedding_bdCoord
#print axioms SpineTask17.isClosedEmbedding_realization_boundary
#print axioms SpineTask17.isOpen_compl_realized_boundary

-- WP2, the boxed target : the realized boundary as the barycentric boundary locus
#print axioms SpineTask17.boundaryHomeo
#print axioms SpineTask17.coe_boundaryHomeo

-- low dimensions
#print axioms SpineTask17.boundaryZero_isEmpty
#print axioms SpineTask17.boundaryOneHomeo

-- WP6 : the sphere
#print axioms SpineTask17.finrank_hyper
#print axioms SpineTask17.simplexGauge_sub_bary
#print axioms SpineTask17.simplexPoint_sphereMap
#print axioms SpineTask17.sphereMap_simplexPoint
#print axioms SpineTask17.bdLocusSphereHomeo
#print axioms SpineTask17.boundaryRealizationSphereHomeo

end SpineTask17

/-! ### subdivision, small simplices, singular excision and contractibility -/

namespace SpineTask18

-- WP2 : the chain prism
#print axioms SpineTask18.cobd_cobd
#print axioms SpineTask18.lbd_prismChain
#print axioms SpineTask18.realizeP_lbd
#print axioms SpineTask18.singBd_prismSimp_succ
#print axioms SpineTask18.singBd_prismSimp_zero
#print axioms SpineTask18.prism_identity_succ
#print axioms SpineTask18.prism_identity_zero
#print axioms SpineTask18.prismHomotopy
#print axioms SpineTask18.homologyMap_eq_of_prism

-- WP3 : contractibility smoke test
#print axioms SpineTask18.exists_boundary_of_cycle
#print axioms SpineTask18.exactAt_singCx_of_contractible
#print axioms SpineTask18.isZero_homology_of_contractible
#print axioms SpineTask18.isZero_homology_realized_simplex

-- WP4 : barycentric subdivision on singular chains
#print axioms SpineTask18.sdS_chain_map
#print axioms SpineTask18.sdS_natural
#print axioms SpineTask18.carrier_sdS
#print axioms SpineTask18.carrier_sdTS

-- WP5 : `sd ~ id` and its iterates
#print axioms SpineTask18.sdTS_homotopy
#print axioms SpineTask18.homN_homotopy
#print axioms SpineTask18.homN_smallChains

-- WP6 : the small-simplices subcomplex
#print axioms SpineTask18.smallSSet
#print axioms SpineTask18.range_smallInc_chainMap
#print axioms SpineTask18.sdS_smallChains
#print axioms SpineTask18.sdTS_smallChains

-- WP7 : eventual smallness
#print axioms SpineTask18.sd_support_mesh
#print axioms SpineTask18.chainMesh_sdIter
#print axioms SpineTask18.exists_iterate_small
#print axioms SpineTask18.exists_iterate_small_chain

-- WP8 : the small-simplices quasi-isomorphism
#print axioms SpineTask18.relSmall_exactAt
#print axioms SpineTask18.isZero_relSmall_homology
#print axioms SpineTask18.isIso_homologyMap_smallInc
#print axioms SpineTask18.quasiIso_smallInc

-- WP9 : excision
#print axioms SpineTask18.excPsi_isIso
#print axioms SpineTask18.excSC_shortExact
#print axioms SpineTask18.excisionMap_factor
#print axioms SpineTask18.isIso_homologyMap_excAlpha
#print axioms SpineTask18.isIso_homologyMap_excisionMap
#print axioms SpineTask18.excisionIso

end SpineTask18

/-! ### singular homology, spheres, the fundamental class and the cell generator -/

namespace SpineTask19

/-! ## WP2 : degree-zero control -/

#print axioms SpineTask19.h0Equiv
#print axioms SpineTask19.ptCls_ne_zero
#print axioms SpineTask19.augH
#print axioms SpineTask19.isZero_homology_td
#print axioms SpineTask19.h0_two_spanning
#print axioms SpineTask19.h0_two_indep
#print axioms SpineTask19.h0TwoEquiv
#print axioms SpineTask19.twoPointMap_bijective
#print axioms SpineTask19.augH_natural
#print axioms SpineTask19.Hred0
#print axioms SpineTask19.Hred0_eq_bot
#print axioms SpineTask19.hred0TwoEquiv
#print axioms SpineTask19.ker_homologyMap_zero_eq_Hred0

/-! ## WP1/WP3 : pair sequence and Mayer–Vietoris -/

#print axioms SpineTask19.isIso_pProj
#print axioms SpineTask19.isIso_pProj_one
#print axioms SpineTask19.isIso_pairDelta
#print axioms SpineTask19.range_pairDelta
#print axioms SpineTask19.mvIsoSucc
#print axioms SpineTask19.mvIsoOne
#print axioms SpineTask19.mv_mono_delta_one
#print axioms SpineTask19.mv_range_delta_one
#print axioms SpineTask19.mvOneEquiv

/-! ## WP4 : sphere cover geometry -/

#print axioms SpineTask19.contractibleSpace_Uset
#print axioms SpineTask19.contractibleSpace_Vset
#print axioms SpineTask19.Uset_union_Vset
#print axioms SpineTask19.interSphereHomotopyEquiv
#print axioms SpineTask19.bdU_union_bdV
#print axioms SpineTask19.bdInterHomotopyEquiv

/-! ## WP5/WP7 : sphere and boundary homology -/

#print axioms SpineTask19.isZero_homology_of_isEmpty
#print axioms SpineTask19.isLine_Hred0_Bd_one
#print axioms SpineTask19.bdIsoSucc
#print axioms SpineTask19.bdEquivOne
#print axioms SpineTask19.sphere_homology
#print axioms SpineTask19.bd_isZero
#print axioms SpineTask19.bd_isLine_top
#print axioms SpineTask19.bd_isLine_zero

/-! ## WP6 : the canonical mod-2 fundamental classes -/

#print axioms SpineTask19.lineGen
#print axioms SpineTask19.eq_lineGen_of_ne_zero
#print axioms SpineTask19.bdFundClass
#print axioms SpineTask19.bdFundClass_ne_zero
#print axioms SpineTask19.bdIsoSucc_bdFundClass
#print axioms SpineTask19.bdEquivOne_bdFundClass

/-! ## WP8/WP9 : relative standard-cell homology and blocker B1 -/

#print axioms SpineTask19.relIsoBd
#print axioms SpineTask19.relEquivOneBd
#print axioms SpineTask19.isZero_rel_zero
#print axioms SpineTask19.standardCellPairAcyclic
#print axioms SpineTask19.isLine_relHomology_top
#print axioms SpineTask19.standardCellPairTop

/-! ## WP10 : the canonical relative generator -/

#print axioms SpineTask19.stdCellTopClass
#print axioms SpineTask19.stdCellTopClass_ne_zero
#print axioms SpineTask19.eq_zero_or_eq_stdCellTopClass
#print axioms SpineTask19.stdCellTopEquiv
#print axioms SpineTask19.stdCellTopEquiv_stdCellTopClass
#print axioms SpineTask19.pairDelta_stdCellTopClass_succ
#print axioms SpineTask19.pairDelta_stdCellTopClass_one
#print axioms SpineTask19.charSimp
#print axioms SpineTask19.charChain_boundary
#print axioms SpineTask19.relCharChain_mem_Zc
#print axioms SpineTask19.stdCellGenerator
#print axioms SpineTask19.stdCellGenerator_zero_ne_zero
#print axioms SpineTask19.stdCellGenerator_zero_eq

end SpineTask19

/-! ### the canonical standard-cell generator -/

namespace SpineTask20

/-! ## Coordinate geometry of the boundary locus -/

#print axioms SpineTask20.barPt
#print axioms SpineTask20.vtx0
#print axioms SpineTask20.barPt_ne_vtx0
#print axioms SpineTask20.eq_vtx0_of_apply_zero_eq_one
#print axioms SpineTask20.coordRetr
#print axioms SpineTask20.continuous_coordRetr
#print axioms SpineTask20.coordRetr_mem_bdLocus
#print axioms SpineTask20.coordRetr_of_face

/-! ## Face maps and the explicit face-sum cycle -/

#print axioms SpineTask20.faceHom
#print axioms SpineTask20.bdFaceSimp_eq
#print axioms SpineTask20.bdFaceTop
#print axioms SpineTask20.bdCoord_bdFaceTop_zero
#print axioms SpineTask20.bdCoord_bdFaceTop_succ
#print axioms SpineTask20.sSetChainMap_injective
#print axioms SpineTask20.bdFaceChain_mem_Zc
#print axioms SpineTask20.boundary_single_bdFaceSimp_zero

/-! ## The two-set cover and the retraction of the `0`-th face inclusion -/

#print axioms SpineTask20.Uset
#print axioms SpineTask20.Vset
#print axioms SpineTask20.Uset_union_Vset
#print axioms SpineTask20.carrier_bdFaceSimp_subset_Uset
#print axioms SpineTask20.carrier_bdFaceSimp_subset_Vset
#print axioms SpineTask20.gIn
#print axioms SpineTask20.retr
#print axioms SpineTask20.gIn_comp_retr

/-! ## Detection of the face-sum homology class -/

#print axioms SpineTask20.interChain
#print axioms SpineTask20.interChain_mem_Zc
#print axioms SpineTask20.homologyMap_retr_gIn
#print axioms SpineTask20.hcls_interChain_ne_zero
#print axioms SpineTask20.hcls_bdFaceChain_zero
#print axioms SpineTask20.hcls_bdFaceChain_step
#print axioms SpineTask20.hcls_bdFaceChain_ne_zero

/-! ## The principal compatibility theorem and the required endpoints -/

#print axioms SpineTask20.hcls_bdFaceChain_eq_bdFundClass
#print axioms SpineTask20.pairDelta_stdCellGenerator
#print axioms SpineTask20.stdCellGenerator_ne_zero
#print axioms SpineTask20.stdCellGenerator_eq_stdCellTopClass

/-! ## Optional single-cell corollary -/

#print axioms SpineTask20.cellRelJ
#print axioms SpineTask20.cellRelJ_topSimp
#print axioms SpineTask20.simplicialTop_mem_Zc
#print axioms SpineTask20.homologyMap_cellRelJ_top

end SpineTask20

/-! ### the single standard-cell relative comparison `cellRelJ` -/

section

open SpineTask21

-- The new source-side input (naturality of the normalization homotopy).
#print axioms SpineTask21.homotopyPToId_hom_naturality
#print axioms SpineTask21.homotopyPInftyToId_hom_naturality
#print axioms SpineTask21.normHtpy_natural

-- The source-side relative homology of the simplicial standard cell pair.
#print axioms SpineTask21.single_mem_range_of_not_surjective
#print axioms SpineTask21.single_mem_degen_of_surjective
#print axioms SpineTask21.proj_natural
#print axioms SpineTask21.proj_mem_range
#print axioms SpineTask21.isZero_simpRel_homology
#print axioms SpineTask21.exists_smul_relTop
#print axioms SpineTask21.exists_smul_simpTopClass

-- The comparison in the top degree.
#print axioms SpineTask21.homologyMap_cellRelJ_simpTopClass
#print axioms SpineTask21.bijective_homologyMap_cellRelJ_top

-- The principal endpoint, and its packaging.
#print axioms SpineTask21.isIso_homologyMap_cellRelJ
#print axioms SpineTask21.homologyIso_cellRelJ
#print axioms SpineTask21.isLine_simpRel_homology_top
#print axioms SpineTask21.simpTopClass_ne_zero
#print axioms SpineTask21.quasiIso_cellRelJ

end

/-! ### the cell separation, the source decomposition and the family compatibility of `J` -/

section

open SpineTask22

-- WP1 : the finite direct sum used.
#print axioms SpineTask22.finiteBiproduct_of_fintype

-- General relative-chain lemmas.
#print axioms SpineTask22.hcls_rel_eq_zero_of_proj_mem_range
#print axioms SpineTask22.proj_mem_range_of_normMap_surj
#print axioms SpineTask22.clsAll

-- WP2 : the skeletal relative simplicial homology.
#print axioms SpineTask22.normChain_mem_range_of_ne
#print axioms SpineTask22.proj_skel_mem_range
#print axioms SpineTask22.isZero_skelRel_homology
#print axioms SpineTask22.subsingleton_relChain_of_lt
#print axioms SpineTask22.mem_Zc_top
#print axioms SpineTask22.topCls_eq_of_normProj_eq
#print axioms SpineTask22.phi_injective
#print axioms SpineTask22.phi_surjective
#print axioms SpineTask22.bijective_phi

-- WP2 : the canonical cell components and the source finite-family decomposition.
#print axioms SpineTask22.cellPairMap
#print axioms SpineTask22.cellPairMap_relTop
#print axioms SpineTask22.homologyMap_cellPairMap_simpTopClass
#print axioms SpineTask22.lineEquiv
#print axioms SpineTask22.srcDecomp
#print axioms SpineTask22.bijective_srcDecomp_top
#print axioms SpineTask22.isIso_srcDecomp
#print axioms SpineTask22.srcDecompIso

-- WP3/WP4 : the realized cell family and the comparison square.
#print axioms SpineTask22.topCellPairMap
#print axioms SpineTask22.cellPairMap_relJ
#print axioms SpineTask22.tgtDecomp
#print axioms SpineTask22.sumCellRelJ
#print axioms SpineTask22.isIso_sumCellRelJ
#print axioms SpineTask22.relJ_decomposition_square
#print axioms SpineTask22.homologyMap_relJ_eq

-- Generator-level form.
#print axioms SpineTask22.relJ_f_cellSimplex
#print axioms SpineTask22.relJ_topCls
#print axioms SpineTask22.relJ_generator_component

-- Section 7 : the geometric separation statement for the realized cell family.
#print axioms SpineTask22.realIsPushout
#print axioms SpineTask22.real_bdryMap_injective
#print axioms SpineTask22.cellPushoutIso
#print axioms SpineTask22.range_skInc_union_range_cellMap
#print axioms SpineTask22.real_cellMap_eq_skInc_iff
#print axioms SpineTask22.real_cellMap_eq_cellMap_iff
#print axioms SpineTask22.real_cellMap_injOn_compl_bdry
#print axioms SpineTask22.real_cellMap_notMem_range_skInc
#print axioms SpineTask22.compl_range_skInc

-- The remaining (unproved, unassumed) singular cell-family statement, and the conditional
-- finite-cell-family corollary.
#print axioms SpineTask22.SingularCellFamilyAdditivity
#print axioms SpineTask22.relJIsIso_of_singularCellFamilyAdditivity

end

/-! ### the punctured cell, the excision isomorphisms and the finite criterion -/

-- WP2 : the radial deformation retraction of the punctured standard cell
#print axioms SpineTask23.radialRetract
#print axioms SpineTask23.radialHomotopy
#print axioms SpineTask23.radialHomotopy_zero
#print axioms SpineTask23.radialHomotopy_of_bdLocus
#print axioms SpineTask23.radialHomotopy_one_mem_bdLocus
#print axioms SpineTask23.cellRetract
#print axioms SpineTask23.cellHomotopy
#print axioms SpineTask23.cellHomotopy_zero
#print axioms SpineTask23.cellHomotopy_one
#print axioms SpineTask23.cellHomotopy_bdry
#print axioms SpineTask23.cellRetract_bdryToPunctured

-- WP1 : open/closed control in the realized pushout
#print axioms SpineTask23.isClosed_iff_of_isPushout
#print axioms SpineTask23.isOpen_iff_of_isPushout
#print axioms SpineTask23.isClosed_coprod_iff
#print axioms SpineTask23.isClosed_range_skInc
#print axioms SpineTask23.baryPoint_notMem_range_skInc
#print axioms SpineTask23.isClosed_barySet
#print axioms SpineTask23.isOpen_puncturedNbhd
#print axioms SpineTask23.isOpen_openCells
#print axioms SpineTask23.openCells_union_puncturedNbhd

-- WP3 : descent through the realized pushout
#print axioms SpineTask23.isQuotientMap_totMap
#print axioms SpineTask23.descend
#print axioms SpineTask23.descendHomotopy
#print axioms SpineTask23.vRetract
#print axioms SpineTask23.vHomotopy
#print axioms SpineTask23.vRetract_skToV
#print axioms SpineTask23.vHomotopy_zero
#print axioms SpineTask23.vHomotopy_one
#print axioms SpineTask23.vHomotopy_fix

-- WP4 : the relative homotopy consequence
#print axioms SpineTask23.vHomotopyEquiv
#print axioms SpineTask23.isZero_relHomology_of_quasiIso
#print axioms SpineTask23.isZero_relHomology_skToV

-- WP5 : excision for the attached family
#print axioms SpineTask23.isIso_homologyMap_relChainCxMap
#print axioms SpineTask23.isIso_homologyMap_pairAV
#print axioms SpineTask23.excisionIsoCells
#print axioms SpineTask23.cellPairIso

-- the single standard cell
#print axioms SpineTask23.bdryHomotopyEquiv
#print axioms SpineTask23.isIso_homologyMap_stdPair
#print axioms SpineTask23.stdExcisionIso
#print axioms SpineTask23.stdCellIso

-- WP7/WP8 : the (open) finite target decomposition and its conditional relJ corollary
#print axioms SpineTask23.finiteSingularCellFamilyAdditivity_of_singularCellFamilyAdditivity
#print axioms SpineTask23.relJIsIso_of_finite

/-! ### the relative cell-sum isomorphisms, the finite target decomposition and finite `RelJIsIso` -/

-- inherited Task-23 input : the geometric decomposition of the singular simplices of `U`
#print axioms SpineTask23.bijective_cellSingMap
#print axioms SpineTask23.cellSingMap_mem_range_incInterU_iff
#print axioms SpineTask23.cellIncl
#print axioms SpineTask23.isOpenMap_cellIncl
#print axioms SpineTask23.exists_cellIncl_lift

-- the direct-sum chain complex and its homology, over an arbitrary index type
#print axioms SpineTask23.finsuppCx
#print axioms SpineTask23.finsuppCxι
#print axioms SpineTask23.finsuppCxπ
#print axioms SpineTask23.finsuppCx_sum_support_single
#print axioms SpineTask23.homologyMap_finset_idem
#print axioms SpineTask23.isIso_sumHomologyMap_of_splitting
#print axioms SpineTask23.isIso_sumHomologyMap_finsuppCxι
#print axioms SpineTask23.isIso_sumHomologyMap
#print axioms SpineTask23.isIso_sumHomologyMap_of_iso

-- inherited Task-23 input : the two excision isomorphisms
#print axioms SpineTask23.stdCellIso
#print axioms SpineTask23.cellPairIso

-- WP1/WP2 : the absolute cell-sum chain isomorphism Θ_abs
#print axioms SpineTask24.finsuppCxDesc
#print axioms SpineTask24.finsuppCxι_desc
#print axioms SpineTask24.famChainMap
#print axioms SpineTask24.famChainMapDeg_apply
#print axioms SpineTask24.bijective_famChainMapDeg
#print axioms SpineTask24.isIso_famChainMap
#print axioms SpineTask24.thetaAbs
#print axioms SpineTask24.isIso_thetaAbs

-- WP3 : the relative cell-sum chain isomorphism Θ_rel
#print axioms SpineTask24.famRelChainMap
#print axioms SpineTask24.famRelChainMapDeg_mapRangeMk
#print axioms SpineTask24.isIso_famRelChainMap
#print axioms SpineTask24.cellRelPairMap
#print axioms SpineTask24.thetaRel
#print axioms SpineTask24.isIso_thetaRel

-- the relative homology decomposition
#print axioms SpineTask24.sumCellHomology
#print axioms SpineTask24.sumCellHomology_single
#print axioms SpineTask24.isIso_sumCellHomology

-- WP5 : transport along the Task-23 excision isomorphisms
#print axioms SpineTask24.excision_cell_square
#print axioms SpineTask24.stdPair_cell_square
#print axioms SpineTask24.cell_decomposition_square

-- WP6/WP7 : identification with the frozen `tgtDecomp`, and its invertibility
#print axioms SpineTask24.mapRangeStd
#print axioms SpineTask24.isIso_mapRangeStd
#print axioms SpineTask24.mapRangeStd_tgtDecomp
#print axioms SpineTask24.isIso_tgtDecomp
#print axioms SpineTask24.isIso_tgtDecomp_finite

-- blocker B3 : `RelJIsIso` for an arbitrary cell family, and its finite forms
#print axioms SpineTask24.singularCellFamilyAdditivity
#print axioms SpineTask24.relJIsIso
#print axioms SpineTask24.singularCellFamilyAdditivity_finite
#print axioms SpineTask24.finiteSingularCellFamilyAdditivity_finite
#print axioms SpineTask24.relJIsIso_finite

-- the global canonical simplicial–singular comparison and its cohomological dual
#print axioms NerveTopology.isClosedMap_realization_subcomplex
#print axioms NerveTopology.exists_skeletal_factorization
#print axioms NerveSkeleton.skeletalSupport
#print axioms SpineExhaustion.isIso_homologyMap_of_exhaustive
#print axioms NerveComparison.globalHomologyIso_of_skeletalSupport
#print axioms NerveComparison.globalHomologyIso
#print axioms NerveComparison.homologyIso_of_hasDimensionLT
#print axioms SpineNaiveHomology.bijective_homologyMap_of_isIso
#print axioms SpineDualCohomology.mem_coboundaries_iff
#print axioms SpineDualCohomology.exists_cocycle_of_functional
#print axioms SpineDualCohomology.bijective_Hmap
#print axioms NerveGeom.bijective_naive_homologyMap
#print axioms NerveGeom.geometricHmap_bijective
#print axioms NerveGeom.geometricComparison
