import RequestProject.Spine.E2.Defect.GlobalCoveringHardening

/-!
# Task 31, Package F (item 50, strongest form): the negative example realized as an inherited
ordinary topological frame family

The negative test system of `UniversalExistenceAudit` was exhibited at the frozen Task-XXVII
output interface (`OrdinaryTransitionSystem`).  This module strengthens the result: the very
same transition data is realized by an actual **ordinary metric-oriented rank-three
topological frame family** in the inherited sense of Task XXVI/XXVII.

The family is the constant rank-three metric-oriented family over the visible model group,
with the two-element trivializing atlas

* chart `0`: the identity identification of every fibre with the model carrier;
* chart `1`: the identification given by the base point itself, read as a rotation of the
  model carrier.

Both charts are metric and orientation preserving, and their overlap maps are continuous, so
the atlas is an inherited `MetricOrientedFibreAtlas`.  Its transition system is computed
explicitly (`badFamily_transition_ft`): the transition from chart `0` to chart `1` at the base
point `b` is `b` itself.

Consequently a compatible continuous internal transition system for this frame family would
again be a continuous global internal representative of the identity map of the visible
group, which the certified layers refute.  Hence

`badFamily_not_internalLiftable` and
`exists_inherited_frame_family_not_internalLiftable`:

**an ordinary topological frame family of the inherited class whose local internal
representatives admit no simultaneous continuous global compatibility.**
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask31

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask29 NullSectorTask30

namespace Examples

/-! ## The constant metric-oriented rank-three family over the visible group -/

/-- The constant rank-three metric-oriented family over the visible model group. -/
noncomputable def badFamilyBase :
    MetricOrientedRankThreeFamily (↥GvisModel) (fun _ : ↥GvisModel => Model) where
  rank_three := fun _ => model_rank_three
  orient := fun _ => modelOrient

/-- Chart `0`: the identity identification of every fibre with the model carrier. -/
noncomputable def badTriv₀ : badFamilyBase.LocalFibreTriv (Set.univ : Set ↥GvisModel) where
  iso := fun _ => LinearIsometryEquiv.refl ℝ Model
  orientation_preserving := fun _ => isOrientationPreserving_refl modelOrient

/-- Chart `1`: the identification given by the base point itself, read as a rotation of the
model carrier. -/
noncomputable def badTriv₁ : badFamilyBase.LocalFibreTriv (Set.univ : Set ↥GvisModel) where
  iso := fun b => ((b : ↥GvisModel) : Model ≃ₗᵢ[ℝ] Model)
  orientation_preserving := fun b => (b : ↥GvisModel).2

/-- The two-chart atlas of the negative example. -/
noncomputable def badTriv : Bool → badFamilyBase.LocalFibreTriv (Set.univ : Set ↥GvisModel)
  | false => badTriv₀
  | true => badTriv₁

/-- Continuity of the overlap maps of the two-chart atlas.  The four cases are the identity,
the base point acting on a model vector, its inverse acting on a model vector, and the
identity again. -/
theorem continuousOn_badOverlap (i j : Bool) :
    ContinuousOn (ovMap (C := fun _ : ↥GvisModel => Model) (M := Model)
        (fun _ : Bool => (Set.univ : Set ↥GvisModel))
        (fun i b => fibreChart (badTriv i) b) i j)
      {p : ↥(Set.univ : Set ↥GvisModel) × Model | (p.1 : ↥GvisModel) ∈ Set.univ} := by
  have hrw : ovMap (C := fun _ : ↥GvisModel => Model) (M := Model)
      (fun _ : Bool => (Set.univ : Set ↥GvisModel))
      (fun i b => fibreChart (badTriv i) b) i j
      = fun p : ↥(Set.univ : Set ↥GvisModel) × Model =>
        (badTriv j).iso ⟨(p.1 : ↥GvisModel), Set.mem_univ _⟩
          (((badTriv i).iso p.1).symm p.2) := by
    funext p
    exact ovMap_apply (C := fun _ : ↥GvisModel => Model) (M := Model)
      (U := fun _ : Bool => (Set.univ : Set ↥GvisModel))
      (chart := fun i b => fibreChart (badTriv i) b) (i := i) (j := j) p (Set.mem_univ _)
  rw [hrw]
  refine Continuous.continuousOn ?_
  have hbase : Continuous fun p : ↥(Set.univ : Set ↥GvisModel) × Model =>
      ((p.1 : ↥GvisModel) : Model ≃ₗᵢ[ℝ] Model) :=
    continuous_induced_dom.comp (continuous_subtype_val.comp continuous_fst)
  cases i <;> cases j
  · exact continuous_snd
  · exact continuous_gvisModel_eval (continuous_subtype_val.comp continuous_fst) continuous_snd
  · exact continuous_modelIsom_symm_eval hbase continuous_snd
  · exact (continuous_gvisModel_eval (continuous_subtype_val.comp continuous_fst)
      (continuous_modelIsom_symm_eval hbase continuous_snd))

/-- **PACKAGE F (item 50), the inherited frame family of the negative example.** -/
noncomputable def badFamily :
    TopologicalFrameFamily (↥GvisModel) (fun _ : ↥GvisModel => Model) Bool where
  family := badFamilyBase
  atlas :=
    { U := fun _ => Set.univ
      isOpen_U := fun _ => isOpen_univ
      cover := fun b => ⟨false, Set.mem_univ b⟩
      triv := badTriv
      continuousOn_overlap := continuousOn_badOverlap }

/-- **PACKAGE F.**  The transition of the frame family from chart `0` to chart `1` at a base
point is that base point itself. -/
theorem badFamily_transition_ft (b : ↥(badFamily.cover false ∩ badFamily.cover true)) :
    badFamily.transition false true b = (b : ↥GvisModel) := by
  refine Subtype.ext (LinearIsometryEquiv.ext fun m => ?_)
  show ((b : ↥GvisModel) : Model ≃ₗᵢ[ℝ] Model)
      ((LinearIsometryEquiv.refl ℝ Model).symm m)
    = ((b : ↥GvisModel) : Model ≃ₗᵢ[ℝ] Model) m
  rfl

/-- **PACKAGE F (item 50), REQUIRED ENDPOINT, strongest form.**  Through every internal
projection without a whole-domain internal representative of the identity, the ordinary
topological frame family above admits **no** compatible continuous internal transitions: its
internally derived kernel equations have no solution.

The argument is internal and elementary: such a system would provide a continuous global
internal representative of the identity map of the visible group. -/
theorem badFamily_not_internalLiftable {L : Type} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] (P : InternalProjection L GvisModel)
    (hP : ¬ P.HasContinuousInternalRep (id : GvisModel → _) Set.univ) :
    ¬ OrdinaryInternalLiftable P badFamily.toOrdinaryTransitionSystem := by
  rintro ⟨T⟩
  refine hP ⟨fun b => T.v false true ⟨b, Set.mem_univ _, Set.mem_univ _⟩, ?_, ?_⟩
  · exact continuousOn_univ.2 ((T.continuous_v false true).comp
      (Continuous.subtype_mk continuous_id _))
  · intro b _
    exact (T.proj_v false true ⟨b, Set.mem_univ _, Set.mem_univ _⟩).trans
      (badFamily_transition_ft ⟨b, Set.mem_univ _, Set.mem_univ _⟩)

end Examples

/-- **PACKAGE F (item 50), REQUIRED ENDPOINT in the strongest ordinary form.**  For every
internal projection without a whole-domain representative of the identity there is an
ordinary metric-oriented rank-three topological frame family — the Task-XXVII object, not
merely an abstract transition system — whose internal lifting problem is unsolvable. -/
theorem exists_frame_family_not_internalLiftable {L : Type} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] (P : InternalProjection L GvisModel)
    (hP : ¬ P.HasContinuousInternalRep (id : GvisModel → _) Set.univ) :
    ∃ (B : Type) (_ : TopologicalSpace B) (E : B → Type) (_ : ∀ b, NormedAddCommGroup (E b))
      (_ : ∀ b, InnerProductSpace ℝ (E b)) (ι : Type) (Tf : TopologicalFrameFamily B E ι),
      ¬ OrdinaryInternalLiftable P Tf.toOrdinaryTransitionSystem :=
  ⟨↥GvisModel, inferInstance, fun _ => Model, inferInstance, inferInstance, Bool,
    Examples.badFamily, Examples.badFamily_not_internalLiftable P hP⟩

/-- **PACKAGE K, strongest form.**  The intrinsic global kernel-defect state of the frame
family above is **non-neutral**. -/
theorem badFamily_not_isNeutralGlobalKernelDefect {L : Type} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] (P : InternalProjection L GvisModel)
    (hP : ¬ P.HasContinuousInternalRep (id : GvisModel → _) Set.univ) :
    ¬ IsNeutralGlobalKernelDefect P
      (ofOrdinary Examples.badFamily.toOrdinaryTransitionSystem) :=
  fun h => Examples.badFamily_not_internalLiftable P hP
    (internalLiftable_iff_globalKernelDefect_neutral.2 h)

end NullSectorTask31
