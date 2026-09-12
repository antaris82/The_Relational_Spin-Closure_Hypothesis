import RequestProject.Spine.E2.Topology.TopologicalFrameFamily

/-!
# Task 27 — principal endpoints

This module imports the complete Task-XXVII development and exposes its principal endpoints
under stable names, followed by an axiom report (`#print axioms`) on each of them.

The Task-XXVI endpoint is imported **unchanged**: no declaration of Task XXVI (or of any
earlier layer) was modified.  Nowhere in this layer does a lifted/double-cover frame family,
a spin structure, a principal bundle, a pre-existing vector- or frame-bundle object, a
characteristic class, cohomology, a connection, or any smooth structure occur.  The work is
entirely in the topological category, over an arbitrary topological base: the base is not
assumed to be a manifold, connected, Hausdorff, paracompact, second countable or locally
compact.

## Required decision table

| Question | Verdict |
| --- | --- |
| Base topology included explicitly? | `PROVED` (`TopologicalSpace B` is an explicit hypothesis throughout; `task27_frame_family`) |
| Correct total fibre topology formalized? | `PROVED` (`task27_fibre_topology`, `task27_fibre_topology_isOpen_iff`) |
| Automatic sigma topology rejected as sufficient? | `PROVED` (`task27_sigma_fibre_open`, `task27_atlasTop_no_open_fibre`, `task27_atlasTop_ne_sigmaTop`) |
| Base projection continuous? | `PROVED` (`task27_continuous_fibreBase`, `task27_continuous_frameBase`) |
| Genuine local product trivialization defined? | `PROVED` (`task27_TopologicalFibreTriv`, `task27_fibreTriv_homeo`, `task27_fibreTriv_of_homeo`) |
| Atlas induces total-space topology? | `PROVED` (`task27_atlas_topology_admissible`, `task27_atlas_topTriv`) |
| Atlas-induced topology unique? | `PROVED` (`task27_atlas_topology_unique`, `task27_frame_topology_unique`) |
| Frame-total topology constructed? | `PROVED` (`task27_frame_topology`, `task27_frame_topology_admissible`) |
| Fibre trivialization induces frame homeomorphism? | `PROVED` (`task27_fibreTriv_induces_frameTriv`, `task27_frameTriv_homeo`) |
| Ordinary transition maps continuous? | `PROVED` (`task27_continuous_transition`, `task27_continuous_transitionOn`) |
| Identity/inverse/triple laws preserved? | `PROVED` (`task27_transition_self`, `task27_transition_symm`, `task27_transition_trans`) |
| Compatible frame trivialization defined equivariantly? | `PROVED` (`task27_CompatibleFrameTriv`) |
| Frame→fibre reconstruction? | `PROVED` (`task27_reconstruct_fibreTriv`, `task27_reconstruction_unique`) |
| Fibre/frame topological trivializations equivalent? | `PROVED` (`task27_fibreTriv_equiv_frameTriv`) |
| Continuous local frame sections obtained? | `PROVED` (`task27_continuous_frameSection`) |
| Continuous global frame guaranteed? | `NO` (only the conditional `task27_conditional_global_frameSection`) |
| Principal bundle formalized? | `NO` |
| Internal lifted family constructed? | `NO` |
| Spin structure constructed? | `NO` |

## Exact frontier handed on (Package N)

The frozen output is `task27_OrdinaryTransitionSystem`, obtained from any ordinary
topological frame family by `task27_frozen_transition_system`.  The only question left open
for a future task — and deliberately *not* answered here — is:

> Given a continuous ordinary transition system valued in the reconstructed visible group,
> what additional compatibility data would be required to reconstruct a coherent two-valued
> internal system over the same base?
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask27

open NullSectorTask26 Topology Module

universe u v t

section Endpoints

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : MetricOrientedRankThreeFamily B E} {ι : Type t}

/-! ## Package B — the total fibre carrier and its admissible topologies -/

/-- Principal endpoint 1: the total fibre carrier, with the *default* dependent-sum topology
deliberately blocked; a topology is always supplied as an explicit extra datum. -/
abbrev task27_FiberTotal (E : B → Type v) : Type _ := Total E

alias task27_fiberTotal_def := fiberTotal_def
alias task27_fiber_exact := fiberBase_preimage_singleton

/-- Principal endpoint 2: the admissibility predicate for a candidate total-space topology
(base projection continuous and every chart of the atlas a homeomorphism). -/
abbrev task27_IsAdmissible {C : B → Type v} {M : Type v} [TopologicalSpace M]
    (atlas : ChartAtlas C M ι) [TopologicalSpace (Total C)] : Prop :=
  atlas.IsAdmissible

/-- Principal endpoint 3: the atlas-generated topology on the total fibre carrier. -/
noncomputable abbrev task27_fibre_topology (A : MetricOrientedFibreAtlas F ι) :
    TopologicalSpace (Total E) := A.top

alias task27_fibre_topology_isOpen_iff := MetricOrientedFibreAtlas.isOpen_top_iff
alias task27_continuous_fibreBase := MetricOrientedFibreAtlas.continuous_top_fiberBase
alias task27_continuous_fibreInclusion :=
  MetricOrientedFibreAtlas.continuous_top_fibreInclusion

/-! ## Package C — genuine topological local fibre trivializations -/

/-- Principal endpoint 4: a topological metric-oriented local fibre trivialization. -/
abbrev task27_TopologicalFibreTriv [TopologicalSpace (Total E)]
    (F : MetricOrientedRankThreeFamily B E) (U : Set B) : Type _ :=
  TopologicalFibreTriv F U

alias task27_fibreTriv_homeo := TopologicalFibreTriv.homeo
alias task27_fibreTriv_proj := TopologicalFibreTriv.homeo_fst
alias task27_fibreTriv_linear := TopologicalFibreTriv.fibrewise_linear
alias task27_fibreTriv_isometry := TopologicalFibreTriv.fibrewise_isometry
alias task27_fibreTriv_orientation := TopologicalFibreTriv.fibrewise_orientation
alias task27_fibreTriv_of_homeo := topologicalFibreTriv_of_homeo

/-! ## Package D — the atlas and the topology it induces -/

/-- Principal endpoint 5: a metric-oriented local trivialization atlas. -/
abbrev task27_MetricOrientedFibreAtlas (F : MetricOrientedRankThreeFamily B E) (ι : Type t) :
    Type _ := MetricOrientedFibreAtlas F ι

alias task27_atlas_topTriv := MetricOrientedFibreAtlas.topTriv
alias task27_atlas_topology_admissible := MetricOrientedFibreAtlas.top_isAdmissible
alias task27_atlas_topology_unique := MetricOrientedFibreAtlas.eq_top_of_isAdmissible

/-! ## Package E — negative control against the automatic sigma topology -/

alias task27_sigma_fibre_open := isOpen_sigmaTop_fibre
alias task27_atlasTop_no_open_fibre := Example27.not_isOpen_fibre_in_atlasTop
alias task27_atlasTop_ne_sigmaTop := Example27.atlasTop_ne_sigmaTop

/-! ## Package F — the ordinary-frame total space and its topology -/

/-- Principal endpoint 6: the topology of the total ordinary-frame carrier. -/
noncomputable abbrev task27_frame_topology (A : MetricOrientedFibreAtlas F ι) :
    TopologicalSpace (Total F.FramePlusAt) := A.frameTop

alias task27_frame_topology_admissible := MetricOrientedFibreAtlas.frameTop_isAdmissible
alias task27_frame_topology_unique := MetricOrientedFibreAtlas.frame_eq_top_of_isAdmissible

/-- Principal endpoint 7: a topological local frame trivialization. -/
abbrev task27_TopologicalFrameTriv (G : MetricOrientedRankThreeFamily B E)
    [TopologicalSpace (Total G.FramePlusAt)] (U : Set B) : Type _ :=
  TopologicalFrameTriv G U

alias task27_frameTriv_homeo := TopologicalFrameTriv.homeo
alias task27_frameTriv_proj := TopologicalFrameTriv.homeo_fst
alias task27_fibreTriv_induces_frameTriv :=
  topologicalFibreTriv_induces_topologicalFrameTriv
alias task27_fibreTriv_induces_frameEquiv := topologicalFibreTriv_induces_frameEquiv

/-! ## Package G and H — continuous transition data -/

alias task27_transitionOn := transitionOn
alias task27_continuous_transitionOn := continuous_transitionOn
alias task27_continuous_fibre_transition := continuousOn_fibre_transition
alias task27_continuous_frame_transition_map := continuousOn_frame_transition
alias task27_frame_transition_law := frameTrivAt_transitionOn
alias task27_continuous_frame_transition := continuous_frame_transition

alias task27_transition := MetricOrientedFibreAtlas.transitionFun
alias task27_continuous_transition := MetricOrientedFibreAtlas.continuous_transitionFun
alias task27_transition_self := MetricOrientedFibreAtlas.transitionFun_self
alias task27_transition_symm := MetricOrientedFibreAtlas.transitionFun_symm
alias task27_transition_trans := MetricOrientedFibreAtlas.transitionFun_trans
alias task27_frameTriv_transition := MetricOrientedFibreAtlas.frameTrivAt_transitionFun
alias task27_continuous_frameTransition :=
  MetricOrientedFibreAtlas.continuous_frameTransitionFun

/-! ## Package I and J — reverse reconstruction and the exact equivalence -/

/-- Principal endpoint 8: a *compatible* (equivariant) topological frame trivialization. -/
abbrev task27_CompatibleFrameTriv (G : MetricOrientedRankThreeFamily B E)
    [TopologicalSpace (Total G.FramePlusAt)] (U : Set B) : Type _ :=
  CompatibleFrameTriv G U

alias task27_frameRAct_free_transitive := existsUnique_frameRAct
alias task27_equivariance_necessary := exists_nonequivariant_frame_bijection
alias task27_reconstruct_iso := reconIso
alias task27_reconstruct_orientation := reconIso_orientation
alias task27_reconstruct_induces_frameEquiv := frameEquivOfIsom_reconIso
alias task27_reconstruction_unique := reconIso_unique
alias task27_reconstruct_fibreTriv := fibreTrivOfCompatibleFrameTriv
alias task27_fibreTriv_equiv_frameTriv := fibreTrivEquivCompatibleFrameTriv
alias task27_frameTriv_atlas := compatibleFrameTrivOfFibreTriv_atlas

/-! ## Package L — local sections and the conditional global statement -/

alias task27_frameSection := MetricOrientedFibreAtlas.frameSection
alias task27_continuous_frameSection := MetricOrientedFibreAtlas.continuous_frameSection
alias task27_conditional_global_frameSection := exists_continuous_global_frameSection

/-! ## Package K and N — the compact interface and the frozen frontier -/

/-- Principal endpoint 9: the ordinary topological frame family.  **Not** a principal
bundle: no principal-bundle axiom is formulated in this development. -/
abbrev task27_frame_family (B : Type u) [TopologicalSpace B] (E : B → Type v)
    [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] (ι : Type t) : Type _ :=
  TopologicalFrameFamily B E ι

/-- Principal endpoint 10: the frozen continuous ordinary transition system. -/
abbrev task27_OrdinaryTransitionSystem (B : Type u) [TopologicalSpace B] (ι : Type t) :
    Type _ := OrdinaryTransitionSystem B ι

alias task27_frozen_transition_system := TopologicalFrameFamily.toOrdinaryTransitionSystem
alias task27_family_free_transitive := TopologicalFrameFamily.frameAction_free_transitive

end Endpoints

/-! ## Axiom report (item 135) -/

#print axioms NullSectorTask27.Total
#print axioms NullSectorTask27.fiberTotal_def
#print axioms NullSectorTask27.fiberBase_preimage_singleton
#print axioms NullSectorTask27.ChartAtlas
#print axioms NullSectorTask27.ChartAtlas.IsAdmissible
#print axioms NullSectorTask27.ChartAtlas.top
#print axioms NullSectorTask27.ChartAtlas.top_isAdmissible
#print axioms NullSectorTask27.ChartAtlas.IsAdmissible.eq_top
#print axioms NullSectorTask27.MetricOrientedFibreAtlas
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.top
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.isOpen_top_iff
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.continuous_top_fiberBase
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.continuous_top_fibreInclusion
#print axioms NullSectorTask27.TopologicalFibreTriv
#print axioms NullSectorTask27.TopologicalFibreTriv.homeo
#print axioms NullSectorTask27.TopologicalFibreTriv.homeo_fst
#print axioms NullSectorTask27.TopologicalFibreTriv.fibrewise_linear
#print axioms NullSectorTask27.TopologicalFibreTriv.fibrewise_isometry
#print axioms NullSectorTask27.TopologicalFibreTriv.fibrewise_orientation
#print axioms NullSectorTask27.topologicalFibreTriv_of_homeo
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.topTriv
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.top_isAdmissible
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.eq_top_of_isAdmissible
#print axioms NullSectorTask27.isOpen_sigmaTop_fibre
#print axioms NullSectorTask27.Example27.not_isOpen_fibre_in_atlasTop
#print axioms NullSectorTask27.Example27.atlasTop_ne_sigmaTop
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.frameTop
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.frameTop_isAdmissible
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.frame_eq_top_of_isAdmissible
#print axioms NullSectorTask27.TopologicalFrameTriv
#print axioms NullSectorTask27.TopologicalFrameTriv.homeo
#print axioms NullSectorTask27.TopologicalFrameTriv.homeo_fst
#print axioms NullSectorTask27.topologicalFibreTriv_induces_topologicalFrameTriv
#print axioms NullSectorTask27.topologicalFibreTriv_induces_frameEquiv
#print axioms NullSectorTask27.transitionOn
#print axioms NullSectorTask27.continuous_transitionOn
#print axioms NullSectorTask27.continuousOn_fibre_transition
#print axioms NullSectorTask27.continuousOn_frame_transition
#print axioms NullSectorTask27.frameTrivAt_transitionOn
#print axioms NullSectorTask27.continuous_frame_transition
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.transitionFun
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.continuous_transitionFun
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.transitionFun_self
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.transitionFun_symm
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.transitionFun_trans
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.frameTrivAt_transitionFun
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.continuous_frameTransitionFun
#print axioms NullSectorTask27.CompatibleFrameTriv
#print axioms NullSectorTask27.frameRAct
#print axioms NullSectorTask27.existsUnique_frameRAct
#print axioms NullSectorTask27.exists_nonequivariant_frame_bijection
#print axioms NullSectorTask27.reconIso
#print axioms NullSectorTask27.reconIso_orientation
#print axioms NullSectorTask27.frameEquivOfIsom_reconIso
#print axioms NullSectorTask27.reconIso_unique
#print axioms NullSectorTask27.fibreTrivOfCompatibleFrameTriv
#print axioms NullSectorTask27.fibreTrivEquivCompatibleFrameTriv
#print axioms NullSectorTask27.compatibleFrameTrivOfFibreTriv_atlas
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.frameSection
#print axioms NullSectorTask27.MetricOrientedFibreAtlas.continuous_frameSection
#print axioms NullSectorTask27.exists_continuous_global_frameSection
#print axioms NullSectorTask27.TopologicalFrameFamily
#print axioms NullSectorTask27.TopologicalFrameFamily.continuous_fibreBase
#print axioms NullSectorTask27.TopologicalFrameFamily.continuous_frameBase
#print axioms NullSectorTask27.TopologicalFrameFamily.frameAction_free_transitive
#print axioms NullSectorTask27.OrdinaryTransitionSystem
#print axioms NullSectorTask27.TopologicalFrameFamily.toOrdinaryTransitionSystem

end NullSectorTask27
