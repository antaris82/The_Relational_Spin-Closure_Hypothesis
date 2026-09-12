import RequestProject.Spine.E2.Topology.ReverseReconstruction

/-!
# Task 27, Packages K and N: the compact ordinary topological frame-family interface

**Package K (items 94–97).**  The strongest completed structure of Task XXVII is packaged in a
single neutral object `TopologicalFrameFamily`, consisting of

* a topological base;
* the inherited algebraic metric-oriented rank-three fibre family;
* a metric-oriented local trivialization atlas (the *extra topological datum* of Task XXVII).

Everything else — the total fibre topology, the total ordinary-frame topology, continuity of
the two base projections, the local product charts, the continuous visible-group-valued
transition system with its identity/inverse/triple-overlap laws, and the free and transitive
fibrewise action on frames — is *derived* from this datum and re-exposed here.

**Comparison note only (items 96–97).**  This object is deliberately *not* called a principal
bundle: the principal-bundle axioms are not formulated anywhere in this development, and no
pre-existing bundle category is imported or identified with it.

**Package N (items 107–112).**  The frozen output interface is `OrdinaryTransitionSystem`: a
continuous `GvisModel`-valued transition system over an open cover satisfying the identity,
inverse and triple-overlap laws.  Nothing above this system is constructed.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask27

open NullSectorTask26 Topology Module

universe u v t

/-! ## Package K — the compact interface -/

/-- **NEWLY DEFINED (items 94–96), principal.**  The *ordinary topological frame family*: a
topological base, the inherited algebraic metric-oriented rank-three fibre family, and a
metric-oriented local trivialization atlas.  Neutral name on purpose — it is **not** claimed
to be a principal bundle (item 96). -/
structure TopologicalFrameFamily (B : Type u) [TopologicalSpace B] (E : B → Type v)
    [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] (ι : Type t) where
  /-- The inherited Task-XXVI algebraic family. -/
  family : MetricOrientedRankThreeFamily B E
  /-- The extra topological datum: a metric-oriented local trivialization atlas. -/
  atlas : MetricOrientedFibreAtlas family ι

namespace TopologicalFrameFamily

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {ι : Type t} (T : TopologicalFrameFamily B E ι)

/-- The total fibre topology of the family. -/
noncomputable def fibreTopology : TopologicalSpace (Total E) := T.atlas.top

/-- The total ordinary-frame topology of the family. -/
noncomputable def frameTopology : TopologicalSpace (Total T.family.FramePlusAt) :=
  T.atlas.frameTop

/-- **DERIVED, principal.**  The fibre base projection is continuous. -/
theorem continuous_fibreBase : @Continuous _ _ T.fibreTopology _ (totalBase E) :=
  T.atlas.continuous_top_fiberBase

/-- **DERIVED, principal.**  The frame base projection is continuous. -/
theorem continuous_frameBase :
    @Continuous _ _ T.frameTopology _ (totalBase T.family.FramePlusAt) :=
  T.atlas.toFrameAtlas.continuous_top_base

/-- The trivializing cover of the family. -/
def cover (i : ι) : Set B := T.atlas.U i

theorem isOpen_cover (i : ι) : IsOpen (T.cover i) := T.atlas.isOpen_U i

theorem cover_covers (b : B) : ∃ i, b ∈ T.cover i := T.atlas.cover b

/-- **DERIVED, principal.**  Every chart of the family is a genuine topological
metric-oriented local fibre trivialization for the fibre topology. -/
noncomputable def fibreTriv (i : ι) :
    TopologicalFibreTriv (τtot := T.fibreTopology) T.family (T.cover i) :=
  T.atlas.topTriv i

/-- **DERIVED, principal.**  Every chart of the family induces a *compatible* (equivariant)
topological frame trivialization for the frame topology. -/
noncomputable def frameTriv (i : ι) :
    CompatibleFrameTriv (τfrm := T.frameTopology) T.family (T.cover i) :=
  compatibleFrameTrivOfFibreTriv T.atlas (T.atlas.topTriv i)

/-- The continuous visible-group-valued transition system of the family. -/
noncomputable def transition (i j : ι) (b : ↥(T.cover i ∩ T.cover j)) : GvisModel :=
  T.atlas.transitionFun i j b

/-- **DERIVED, principal.**  Continuity of the transition system. -/
theorem continuous_transition (i j : ι) : Continuous (T.transition i j) :=
  T.atlas.continuous_transitionFun i j

/-- **DERIVED.**  Identity law. -/
theorem transition_self (i : ι) (b : ↥(T.cover i ∩ T.cover i)) : T.transition i i b = 1 :=
  T.atlas.transitionFun_self i b

/-- **DERIVED.**  Inverse law. -/
theorem transition_symm (i j : ι) (b : B) (h : b ∈ T.cover i ∩ T.cover j)
    (h' : b ∈ T.cover j ∩ T.cover i) :
    T.transition j i ⟨b, h'⟩ = (T.transition i j ⟨b, h⟩)⁻¹ :=
  T.atlas.transitionFun_symm i j b h h'

/-- **DERIVED.**  Triple-overlap law. -/
theorem transition_trans (i j k : ι) (b : B) (h₁ : b ∈ T.cover i ∩ T.cover k)
    (h₂ : b ∈ T.cover j ∩ T.cover k) (h₃ : b ∈ T.cover i ∩ T.cover j) :
    T.transition i k ⟨b, h₁⟩ = T.transition j k ⟨b, h₂⟩ * T.transition i j ⟨b, h₃⟩ :=
  T.atlas.transitionFun_trans i j k b h₁ h₂ h₃

/-- **DERIVED, principal.**  The frame charts transform by the same transition system. -/
theorem frameTriv_transition (i j : ι) (b : B) (h : b ∈ T.cover i ∩ T.cover j)
    (v : T.family.FramePlusAt b) :
    MetricOrientedRankThreeFamily.frameTrivAt (T.atlas.triv j) ⟨b, h.2⟩ v
      = T.transition i j ⟨b, h⟩ •
        MetricOrientedRankThreeFamily.frameTrivAt (T.atlas.triv i) ⟨b, h.1⟩ v :=
  T.atlas.frameTrivAt_transitionFun i j b h v

/-- **DERIVED, principal.**  The transition action on the model frame space is continuous. -/
theorem continuous_frameTransition (i j : ι) :
    Continuous fun p : ↥(T.cover i ∩ T.cover j) × FramePlusModel =>
      T.transition i j p.1 • p.2 :=
  T.atlas.continuous_frameTransitionFun i j

/-- **DERIVED (item 95), principal.**  The fibrewise action of the fixed visible model group
on the frame space over each base point is free and transitive. -/
theorem frameAction_free_transitive (b : B) (v w : T.family.FramePlusAt b) :
    ∃! k : GvisModel, frameRAct v k = w :=
  existsUnique_frameRAct v w

/-- **DERIVED (item 98), principal.**  Each chart gives a continuous local frame section. -/
theorem continuous_frameSection (i : ι) :
    @Continuous _ _ _ T.frameTopology
      (fun b : T.cover i => (⟨(b : B), T.atlas.frameSection i b⟩ :
        Total T.family.FramePlusAt)) :=
  T.atlas.continuous_frameSection i

end TopologicalFrameFamily

/-! ## Package N — the frozen ordinary transition system -/

/-- **NEWLY DEFINED (item 107), principal.**  The frozen Task-XXVII output: a continuous
transition system valued in the fixed visible model group, over an open cover of the base,
satisfying the identity, inverse and triple-overlap laws.  Nothing above this object is
constructed in Task XXVII (items 108–112). -/
structure OrdinaryTransitionSystem (B : Type u) [TopologicalSpace B] (ι : Type t) where
  /-- The trivializing cover. -/
  U : ι → Set B
  /-- Each domain is open. -/
  isOpen_U : ∀ i, IsOpen (U i)
  /-- The domains cover the base. -/
  cover : ∀ b : B, ∃ i, b ∈ U i
  /-- The transition transformations. -/
  g : ∀ i j : ι, ↥(U i ∩ U j) → GvisModel
  /-- Continuity of every transition transformation. -/
  continuous_g : ∀ i j, Continuous (g i j)
  /-- Identity law. -/
  g_self : ∀ (i : ι) (b : ↥(U i ∩ U i)), g i i b = 1
  /-- Inverse law. -/
  g_symm : ∀ (i j : ι) (b : B) (h : b ∈ U i ∩ U j) (h' : b ∈ U j ∩ U i),
    g j i ⟨b, h'⟩ = (g i j ⟨b, h⟩)⁻¹
  /-- Triple-overlap law. -/
  g_trans : ∀ (i j k : ι) (b : B) (h₁ : b ∈ U i ∩ U k) (h₂ : b ∈ U j ∩ U k)
    (h₃ : b ∈ U i ∩ U j), g i k ⟨b, h₁⟩ = g j k ⟨b, h₂⟩ * g i j ⟨b, h₃⟩

namespace TopologicalFrameFamily

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {ι : Type t} (T : TopologicalFrameFamily B E ι)

/-- **DERIVED (item 107), principal — the exact frontier handed on by Task XXVII.**  Every
ordinary topological frame family produces a continuous ordinary transition system. -/
noncomputable def toOrdinaryTransitionSystem : OrdinaryTransitionSystem B ι where
  U := T.cover
  isOpen_U := T.isOpen_cover
  cover := T.cover_covers
  g := T.transition
  continuous_g := T.continuous_transition
  g_self := T.transition_self
  g_symm := T.transition_symm
  g_trans := T.transition_trans

end TopologicalFrameFamily

end NullSectorTask27
