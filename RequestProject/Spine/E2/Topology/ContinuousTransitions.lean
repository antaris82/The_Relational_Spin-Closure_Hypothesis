import RequestProject.Spine.E2.Topology.FrameTopology

/-!
# Task 27, Packages G and H: continuous transition data

**Hard target B, second half (items 64–78).**

The inherited algebraic transition transformation `g_ij(b) = Ψ_b ∘ Φ_b⁻¹ ∈ GvisModel` of
Task XXVI is here proved to be a **continuous** function of the base point on the overlap of
the domains, for the fixed model group topology of `ModelTopology`.  The proof uses the
continuity of the two total-space product charts (item 69), not merely pointwise membership
in the group (item 68).

The three algebraic laws (identity, inverse, triple overlap) are re-exposed unchanged from
Task XXVI (item 70), the frame charts are proved to have exactly the same transition
functions (item 74), acting on the model frame space by the inherited action (item 75), and
the action itself is continuous (items 76–78).  No Čech language and no lifted transition
map appears (items 72–73).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask27

open NullSectorTask26 Topology Module

universe u v t

section Transitions

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : MetricOrientedRankThreeFamily B E} {U W X : Set B}

/-- **NEWLY DEFINED (items 64–65), principal.**  The inherited transition transformation of
two local fibre trivializations, as a function on the overlap of their domains. -/
noncomputable def transitionOn (Φ : F.LocalFibreTriv U) (Ψ : F.LocalFibreTriv W)
    (b : ↥(U ∩ W)) : GvisModel :=
  MetricOrientedRankThreeFamily.transition Φ Ψ b.2.1 b.2.2

omit [TopologicalSpace B] in
@[simp] theorem transitionOn_apply (Φ : F.LocalFibreTriv U) (Ψ : F.LocalFibreTriv W)
    (b : ↥(U ∩ W)) (m : Model) :
    (transitionOn Φ Ψ b : Model ≃ₗᵢ[ℝ] Model) m
      = Ψ.iso ⟨(b : B), b.2.2⟩ ((Φ.iso ⟨(b : B), b.2.1⟩).symm m) := rfl

/-! ### The three algebraic laws, re-exposed from Task XXVI (item 70) -/

omit [TopologicalSpace B] in
/-- **DERIVED (item 70), principal.**  Identity law `g_ii = 1`. -/
theorem transitionOn_self (Φ : F.LocalFibreTriv U) (b : ↥(U ∩ U)) :
    transitionOn Φ Φ b = 1 :=
  MetricOrientedRankThreeFamily.transition_self Φ b.2.1 b.2.2

omit [TopologicalSpace B] in
/-- **DERIVED (item 70), principal.**  Inverse law `g_ji = g_ij⁻¹`. -/
theorem transitionOn_symm (Φ : F.LocalFibreTriv U) (Ψ : F.LocalFibreTriv W) (b : B)
    (h : b ∈ U ∩ W) (h' : b ∈ W ∩ U) :
    transitionOn Ψ Φ ⟨b, h'⟩ = (transitionOn Φ Ψ ⟨b, h⟩)⁻¹ :=
  MetricOrientedRankThreeFamily.transition_symm Φ Ψ h.1 h.2

omit [TopologicalSpace B] in
/-- **DERIVED (item 70), principal.**  Triple-overlap law `g_ik = g_jk * g_ij`. -/
theorem transitionOn_trans (Φ : F.LocalFibreTriv U) (Ψ : F.LocalFibreTriv W)
    (Χ : F.LocalFibreTriv X) (b : B) (h₁ : b ∈ U ∩ X) (h₂ : b ∈ W ∩ X) (h₃ : b ∈ U ∩ W) :
    transitionOn Φ Χ ⟨b, h₁⟩ = transitionOn Ψ Χ ⟨b, h₂⟩ * transitionOn Φ Ψ ⟨b, h₃⟩ :=
  MetricOrientedRankThreeFamily.transition_trans Φ Ψ Χ h₁.1 h₂.1 h₁.2

omit [TopologicalSpace B] in
/-- **DERIVED (items 74–75), principal.**  On an overlap the two induced frame coordinates
differ exactly by the action of the transition transformation on the model frame space,
`frameCoord_j = g_ij • frameCoord_i`.  This is the inherited Task-XXVI identity, restated
with the transition function of this module. -/
theorem frameTrivAt_transitionOn (Φ : F.LocalFibreTriv U) (Ψ : F.LocalFibreTriv W) (b : B)
    (h : b ∈ U ∩ W) (v : F.FramePlusAt b) :
    MetricOrientedRankThreeFamily.frameTrivAt Ψ ⟨b, h.2⟩ v
      = transitionOn Φ Ψ ⟨b, h⟩ • MetricOrientedRankThreeFamily.frameTrivAt Φ ⟨b, h.1⟩ v :=
  MetricOrientedRankThreeFamily.frameTrivAt_transition Φ Ψ h.1 h.2 v

/-! ### Continuity of the transition transformations (item 67) -/

variable [τtot : TopologicalSpace (Total E)]

/-- **DERIVED (items 67–69), principal.**  The transition transformation of two *topological*
fibre trivializations is a continuous function of the base point on the overlap, valued in
the visible model group with its inherited topology.  The proof goes through the continuity
of the two local product charts. -/
theorem continuous_transitionOn (Φ : TopologicalFibreTriv F U) (Ψ : TopologicalFibreTriv F W) :
    Continuous fun b : ↥(U ∩ W) => transitionOn Φ.alg Ψ.alg b := by
  classical
  rw [continuous_gvisModel_iff]
  intro m
  have hcont : Continuous fun b : ↥(U ∩ W) =>
      ((⟨(b : B), b.2.1⟩ : ↥U), m) :=
    (continuous_subtype_val.subtype_mk _).prodMk continuous_const
  have hmem : ∀ b : ↥(U ∩ W),
      ((⟨(b : B), b.2.1⟩ : ↥U), m) ∈ {p : ↥U × Model | (p.1 : B) ∈ W} :=
    fun b => b.2.2
  have hbase := (continuousOn_fibre_transition Φ Ψ).comp_continuous hcont hmem
  refine hbase.congr fun b => ?_
  have hb : (((⟨(b : B), b.2.1⟩ : ↥U) : B)) ∈ W := b.2.2
  simp only [Function.comp_apply, dif_pos hb]
  rfl

/-! ### Package H: the frame charts have the same transition data -/

/-- **DERIVED (items 76–78), principal.**  `continuous_frame_transition`: the transition
action on the model frame space is continuous in the base point and in the frame
simultaneously.  Together with `frameTrivAt_transitionOn` this is the continuous local
product structure of the ordinary frame total space. -/
theorem continuous_frame_transition (Φ : TopologicalFibreTriv F U)
    (Ψ : TopologicalFibreTriv F W) :
    Continuous fun p : ↥(U ∩ W) × FramePlusModel =>
      transitionOn Φ.alg Ψ.alg p.1 • p.2 :=
  continuous_gvisModel_smul ((continuous_transitionOn Φ Ψ).comp continuous_fst) continuous_snd

end Transitions

/-! ## The transition data of a metric-oriented atlas -/

section AtlasTransitions

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : MetricOrientedRankThreeFamily B E} {ι : Type t}

namespace MetricOrientedFibreAtlas

variable (A : MetricOrientedFibreAtlas F ι)

/-- **NEWLY DEFINED (items 65, 71), principal.**  The transition system of the atlas. -/
noncomputable def transitionFun (i j : ι) (b : ↥(A.U i ∩ A.U j)) : GvisModel :=
  transitionOn (A.triv i) (A.triv j) b

/-- **DERIVED (item 67), principal.**  Every transition function of the atlas is continuous.
No topology on the total carrier appears in the statement; the proof uses the atlas
topology. -/
theorem continuous_transitionFun (i j : ι) : Continuous (A.transitionFun i j) := by
  letI := A.top
  exact continuous_transitionOn (A.topTriv i) (A.topTriv j)

/-- **DERIVED (item 70).**  Identity law of the atlas transition system. -/
theorem transitionFun_self (i : ι) (b : ↥(A.U i ∩ A.U i)) :
    A.transitionFun i i b = 1 :=
  transitionOn_self (A.triv i) b

/-- **DERIVED (item 70).**  Inverse law of the atlas transition system. -/
theorem transitionFun_symm (i j : ι) (b : B) (h : b ∈ A.U i ∩ A.U j)
    (h' : b ∈ A.U j ∩ A.U i) : A.transitionFun j i ⟨b, h'⟩ = (A.transitionFun i j ⟨b, h⟩)⁻¹ :=
  transitionOn_symm (A.triv i) (A.triv j) b h h'

/-- **DERIVED (item 70).**  Triple-overlap law of the atlas transition system. -/
theorem transitionFun_trans (i j k : ι) (b : B) (h₁ : b ∈ A.U i ∩ A.U k)
    (h₂ : b ∈ A.U j ∩ A.U k) (h₃ : b ∈ A.U i ∩ A.U j) :
    A.transitionFun i k ⟨b, h₁⟩ = A.transitionFun j k ⟨b, h₂⟩ * A.transitionFun i j ⟨b, h₃⟩ :=
  transitionOn_trans (A.triv i) (A.triv j) (A.triv k) b h₁ h₂ h₃

/-- **DERIVED (items 74–75).**  The induced frame charts of the atlas have exactly the same
transition system, acting on the model frame space. -/
theorem frameTrivAt_transitionFun (i j : ι) (b : B) (h : b ∈ A.U i ∩ A.U j)
    (v : F.FramePlusAt b) :
    MetricOrientedRankThreeFamily.frameTrivAt (A.triv j) ⟨b, h.2⟩ v
      = A.transitionFun i j ⟨b, h⟩ •
        MetricOrientedRankThreeFamily.frameTrivAt (A.triv i) ⟨b, h.1⟩ v :=
  frameTrivAt_transitionOn (A.triv i) (A.triv j) b h v

/-- **DERIVED (items 76–78), principal.**  The frame transition action of the atlas is
continuous. -/
theorem continuous_frameTransitionFun (i j : ι) :
    Continuous fun p : ↥(A.U i ∩ A.U j) × FramePlusModel =>
      A.transitionFun i j p.1 • p.2 :=
  continuous_gvisModel_smul ((A.continuous_transitionFun i j).comp continuous_fst)
    continuous_snd

end MetricOrientedFibreAtlas

end AtlasTransitions

end NullSectorTask27
