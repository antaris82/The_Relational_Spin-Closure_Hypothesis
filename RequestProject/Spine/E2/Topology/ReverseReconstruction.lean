import RequestProject.Spine.E2.Topology.FrameRightAction

/-!
# Task 27, Packages I, J, L: reverse reconstruction, atlas equivalence, local sections

**Hard target C (items 79–92, 98–102).**

A *compatible topological frame trivialization* over an open set `U` is a topological frame
trivialization whose fibrewise part is **equivariant** for the right action of the fixed
visible model group (item 79–80; without equivariance the reconstruction fails, see
`exists_nonequivariant_frame_bijection`).

The main result is that the forward construction of Package F is a **bijection**:

`TopologicalFibreTriv U ≃ CompatibleFrameTriv U`   (`fibreTrivEquivCompatibleFrameTriv`)

for the atlas topologies on the two total spaces.  In particular the reconstruction of the
metric-oriented fibre trivialization from an equivariant frame trivialization exists, is
fibrewise linear, metric- and orientation-preserving, is continuous in both directions on
the total space (item 86), and is unique (item 87).

Package L adds the local-section diagnostic: every chart of the atlas gives a *continuous*
local frame section, and a global topological trivialization gives a continuous global frame
section; no continuous global frame is asserted (items 98–101).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask27

open NullSectorTask26 Topology Module

universe u v t

section Recon

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : MetricOrientedRankThreeFamily B E} {ι : Type t}

/-! ## Local frame sections attached to an atlas chart (Package L) -/

namespace MetricOrientedFibreAtlas

variable (A : MetricOrientedFibreAtlas F ι)

/-- **NEWLY DEFINED (item 98).**  The local frame section determined by a chart of the
atlas: the frame whose associated isometry is the inverse of the chart. -/
noncomputable def frameSection (i : ι) (b : A.U i) : F.FramePlusAt (b : B) :=
  (MetricOrientedRankThreeFamily.frameTrivAt (A.triv i) b).symm modelFrame

theorem frameSection_vec (i : ι) (b : A.U i) (k : Fin 3) :
    FramePlusOf.vec (A.frameSection i b) k = ((A.triv i).iso b).symm (modelBasis k) := by
  show ((A.triv i).iso b).symm (FramePlusOf.vec modelFrame k) = _
  rw [modelBasis_eq_modelFrame_vec]

theorem frameIsom_frameSection (i : ι) (b : A.U i) :
    frameIsom (A.frameSection i b) = ((A.triv i).iso b).symm := by
  refine isom_ext_of_frame modelFrame fun k => ?_
  rw [← modelBasis_eq_modelFrame_vec, frameIsom_modelBasis, frameSection_vec]

/-- **DERIVED (item 98), principal.**  The local frame section of a chart is continuous into
the frame total space with its atlas topology. -/
theorem continuous_frameSection (i : ι) :
    @Continuous _ _ _ A.frameTop
      (fun b : A.U i => (⟨(b : B), A.frameSection i b⟩ : Total F.FramePlusAt)) := by
  letI := A.frameTop
  have hfac : (fun b : A.U i => (⟨(b : B), A.frameSection i b⟩ : Total F.FramePlusAt))
      = fun b : A.U i => A.toFrameAtlas.psi i (b, modelFrame) := rfl
  rw [hfac]
  exact (A.toFrameAtlas.continuous_psi_top i).comp (continuous_id.prodMk continuous_const)

end MetricOrientedFibreAtlas

/-! ## Compatible (equivariant) topological frame trivializations (items 79–80) -/

/-- **NEWLY DEFINED (items 79–80), principal.**  A *compatible topological frame
trivialization*: a topological frame trivialization over `U` whose fibrewise identifications
are equivariant for the right action of the fixed visible model group. -/
structure CompatibleFrameTriv (F : MetricOrientedRankThreeFamily B E)
    [τfrm : TopologicalSpace (Total F.FramePlusAt)] (U : Set B)
    extends TopologicalFrameTriv F U where
  /-- Equivariance for the model-group action on frames. -/
  equivariant : ∀ (b : U) (v : F.FramePlusAt (b : B)) (k : GvisModel),
    frameEquiv b (frameRAct v k) = frameRAct (frameEquiv b v) k

/-! ## The pointwise reconstruction of the fibre identifications -/

section Pointwise

variable [τfrm : TopologicalSpace (Total F.FramePlusAt)] {U : Set B}

/-- **NEWLY DEFINED (items 82–85), principal.**  The reconstructed metric-oriented fibre
identification at a point: the unique orientation-preserving linear isometry onto the model
inducing the given equivariant frame identification. -/
noncomputable def reconIso (Θ : CompatibleFrameTriv F U) (b : U) : E (b : B) ≃ₗᵢ[ℝ] Model :=
  isomOfFramePair (Classical.arbitrary (F.FramePlusAt (b : B)))
    (Θ.frameEquiv b (Classical.arbitrary (F.FramePlusAt (b : B))))

/-- **DERIVED (item 85).**  The reconstruction preserves the orientation datum (and, being a
`LinearIsometryEquiv`, it is real-linear and metric preserving — items 83–84). -/
theorem reconIso_orientation (Θ : CompatibleFrameTriv F U) (b : U) :
    IsOrientationPreserving (F.orient (b : B)) modelOrient (reconIso Θ b) :=
  isomOfFramePair_orientation _ _

/-- **DERIVED (items 82–85), principal.**  The reconstruction induces exactly the given
frame identification. -/
theorem frameEquivOfIsom_reconIso (Θ : CompatibleFrameTriv F U) (b : U)
    (v : F.FramePlusAt (b : B)) :
    frameEquivOfIsom (reconIso_orientation Θ b) v = Θ.frameEquiv b v := by
  have h := eq_of_equivariant
    (α := fun w => frameEquivOfIsom (reconIso_orientation Θ b) w)
    (β := fun w => Θ.frameEquiv b w)
    (fun w k => frameEquivOfIsom_frameRAct _ w k)
    (fun w k => Θ.equivariant b w k)
    (v₀ := Classical.arbitrary (F.FramePlusAt (b : B)))
    (frameEquivOfIsom_isomOfFramePair _ _)
  exact congrFun h v

/-- The algebraic local fibre trivialization reconstructed from a compatible frame
trivialization. -/
noncomputable def reconAlg (Θ : CompatibleFrameTriv F U) : F.LocalFibreTriv U where
  iso := reconIso Θ
  orientation_preserving := reconIso_orientation Θ

/-- **DERIVED (item 87), principal.**  Uniqueness of the reconstruction: an
orientation-preserving fibrewise identification inducing the given frame identification is
unique, hence equal to `reconIso`. -/
theorem reconIso_unique (Θ : CompatibleFrameTriv F U) (b : U) (f : E (b : B) ≃ₗᵢ[ℝ] Model)
    (hf : IsOrientationPreserving (F.orient (b : B)) modelOrient f)
    (hfΘ : ∀ v, frameEquivOfIsom hf v = Θ.frameEquiv b v) : f = reconIso Θ b := by
  obtain ⟨g, -, huniq⟩ := existsUnique_isom_of_equivariant
    (Θ := fun v => Θ.frameEquiv b v) (fun v k => Θ.equivariant b v k)
    (Classical.arbitrary (F.FramePlusAt (b : B)))
  have h1 : (⟨f, hf⟩ : {f : E (b : B) ≃ₗᵢ[ℝ] Model //
      IsOrientationPreserving (F.orient (b : B)) modelOrient f}) = g := huniq _ hfΘ
  have h2 : (⟨reconIso Θ b, reconIso_orientation Θ b⟩ : {f : E (b : B) ≃ₗᵢ[ℝ] Model //
      IsOrientationPreserving (F.orient (b : B)) modelOrient f}) = g :=
    huniq _ (frameEquivOfIsom_reconIso Θ b)
  exact congrArg Subtype.val (h1.trans h2.symm)

/-- The frame identification of a compatible frame trivialization, expressed through the
reconstructed isometry. -/
theorem frameIsom_frameEquiv (Θ : CompatibleFrameTriv F U) (b : U)
    (v : F.FramePlusAt (b : B)) :
    frameIsom (Θ.frameEquiv b v) = (frameIsom v).trans (reconIso Θ b) := by
  rw [← frameEquivOfIsom_reconIso Θ b v, frameIsom_frameEquivOfIsom]

end Pointwise

/-! ## Continuity of the reconstruction (item 86) -/

section Continuity

variable (A : MetricOrientedFibreAtlas F ι) {U : Set B}

/-- Continuity of a family of model isometries attached to a continuous family of model
frames. -/
theorem continuous_frameIsom_model {X : Type*} [TopologicalSpace X] {v : X → FramePlusModel}
    (hv : Continuous v) : Continuous fun x => (frameIsom (v x) : Model ≃ₗᵢ[ℝ] Model) := by
  rw [continuous_modelIsom_iff]
  intro m
  exact continuous_frameIsom_eval hv continuous_const

/-- The continuous family of model frames obtained by reading the local frame section of the
`i`-th chart in a compatible frame trivialization. -/
theorem continuous_reconFrame (Θ : CompatibleFrameTriv (τfrm := A.frameTop) F U) (i : ι) :
    Continuous fun b : ↥(U ∩ A.U i) =>
      TopologicalFrameTriv.frameEquiv (τfrm := A.frameTop) (CompatibleFrameTriv.toTopologicalFrameTriv (τfrm := A.frameTop) Θ)
        ⟨(b : B), b.2.1⟩ (A.frameSection i ⟨(b : B), b.2.2⟩) := by
  letI := A.frameTop
  have hsec : @Continuous _ (Total F.FramePlusAt) _ A.frameTop
      (fun b : ↥(U ∩ A.U i) =>
        (⟨(b : B), A.frameSection i ⟨(b : B), b.2.2⟩⟩ : Total F.FramePlusAt)) :=
    (A.continuous_frameSection i).comp (continuous_subtype_val.subtype_mk _)
  have hk : Continuous fun b : ↥(U ∩ A.U i) =>
      (⟨(⟨(b : B), A.frameSection i ⟨(b : B), b.2.2⟩⟩ : Total F.FramePlusAt), b.2.1⟩ :
        framePart F U) := hsec.subtype_mk _
  exact continuous_snd.comp (Θ.continuous_chart.comp hk)

/-- **DERIVED (item 86), principal.**  The reconstruction is continuous on the total space:
a compatible topological frame trivialization over `U` yields a *topological* metric-oriented
fibre trivialization over `U`. -/
noncomputable def fibreTrivOfCompatibleFrameTriv
    (Θ : CompatibleFrameTriv (τfrm := A.frameTop) F U) :
    TopologicalFibreTriv (τtot := A.top) F U := by
  classical
  letI := A.top
  letI := A.frameTop
  set χ : ∀ b : U, E (b : B) ≃ Model := fun b => fibreChart (reconAlg Θ) b with hχ
  -- the model-isometry family attached to the reconstruction, read in the `i`-th chart
  have key : ∀ (i : ι) (b : B) (hU : b ∈ U) (hi : b ∈ A.U i) (m : Model),
      frameIsom (TopologicalFrameTriv.frameEquiv (τfrm := A.frameTop) (CompatibleFrameTriv.toTopologicalFrameTriv (τfrm := A.frameTop) Θ)
        ⟨b, hU⟩ (A.frameSection i ⟨b, hi⟩)) m
        = reconIso Θ ⟨b, hU⟩ (((A.triv i).iso ⟨b, hi⟩).symm m) := by
    intro i b hU hi m
    rw [frameIsom_frameEquiv, A.frameIsom_frameSection]
    rfl
  have h1 : ∀ i, ContinuousOn
      (ovMap (A.toChartAtlas.optU U) (A.toChartAtlas.optChart U χ) none (some i))
      {p : (A.toChartAtlas.optU U none) × Model |
        (p.1 : B) ∈ A.toChartAtlas.optU U (some i)} := by
    intro i
    have hw : Continuous fun x : {p : ↥U × Model | (p.1 : B) ∈ A.U i} =>
        (frameIsom (TopologicalFrameTriv.frameEquiv (τfrm := A.frameTop)
          (CompatibleFrameTriv.toTopologicalFrameTriv (τfrm := A.frameTop) Θ) ⟨(x.1.1 : B), x.1.1.2⟩
            (A.frameSection i ⟨(x.1.1 : B), x.2⟩)) : Model ≃ₗᵢ[ℝ] Model) := by
      refine continuous_frameIsom_model ?_
      have hmap : Continuous fun x : {p : ↥U × Model | (p.1 : B) ∈ A.U i} =>
          (⟨((x.1.1 : B)), ⟨x.1.1.2, x.2⟩⟩ : ↥(U ∩ A.U i)) :=
        (((continuous_subtype_val.comp continuous_fst).comp
          continuous_subtype_val)).subtype_mk _
      exact (continuous_reconFrame A Θ i).comp hmap
    have hcont : Continuous fun x : {p : ↥U × Model | (p.1 : B) ∈ A.U i} =>
        (frameIsom (TopologicalFrameTriv.frameEquiv (τfrm := A.frameTop)
          (CompatibleFrameTriv.toTopologicalFrameTriv (τfrm := A.frameTop) Θ) ⟨(x.1.1 : B), x.1.1.2⟩
            (A.frameSection i ⟨(x.1.1 : B), x.2⟩)) : Model ≃ₗᵢ[ℝ] Model).symm x.1.2 :=
      continuous_modelIsom_symm_eval hw (continuous_snd.comp continuous_subtype_val)
    rw [continuousOn_iff_continuous_restrict]
    refine hcont.congr fun x => ?_
    have hp : ((x.1.1 : B)) ∈ A.U i := x.2
    rw [Set.restrict_apply,
      ovMap_apply (U := A.toChartAtlas.optU U) (chart := A.toChartAtlas.optChart U χ)
        (i := none) (j := some i) x.1 hp]
    show _ = (A.triv i).iso ⟨(x.1.1 : B), hp⟩ ((reconIso Θ x.1.1).symm x.1.2)
    have hfun : reconIso Θ x.1.1 (((A.triv i).iso ⟨(x.1.1 : B), hp⟩).symm
        ((frameIsom (TopologicalFrameTriv.frameEquiv (τfrm := A.frameTop)
          (CompatibleFrameTriv.toTopologicalFrameTriv (τfrm := A.frameTop) Θ) ⟨(x.1.1 : B), x.1.1.2⟩
            (A.frameSection i ⟨(x.1.1 : B), hp⟩))).symm x.1.2)) = x.1.2 := by
      rw [← key i (x.1.1 : B) x.1.1.2 hp]
      exact LinearIsometryEquiv.apply_symm_apply _ x.1.2
    have := congrArg (fun m : Model => (A.triv i).iso ⟨(x.1.1 : B), hp⟩
      ((reconIso Θ x.1.1).symm m)) hfun
    simpa using this
  have h2 : ∀ i, ContinuousOn
      (ovMap (A.toChartAtlas.optU U) (A.toChartAtlas.optChart U χ) (some i) none)
      {p : (A.toChartAtlas.optU U (some i)) × Model |
        (p.1 : B) ∈ A.toChartAtlas.optU U none} := by
    intro i
    have hw : Continuous fun x : {p : ↥(A.U i) × Model | (p.1 : B) ∈ U} =>
        TopologicalFrameTriv.frameEquiv (τfrm := A.frameTop) (CompatibleFrameTriv.toTopologicalFrameTriv (τfrm := A.frameTop) Θ)
          ⟨(x.1.1 : B), x.2⟩ (A.frameSection i ⟨(x.1.1 : B), x.1.1.2⟩) :=
      (continuous_reconFrame A Θ i).comp
        ((((continuous_subtype_val.comp continuous_fst).comp
          continuous_subtype_val)).subtype_mk
            (fun x => ⟨x.2, x.1.1.2⟩))
    have hcont : Continuous fun x : {p : ↥(A.U i) × Model | (p.1 : B) ∈ U} =>
        frameIsom (TopologicalFrameTriv.frameEquiv (τfrm := A.frameTop)
          (CompatibleFrameTriv.toTopologicalFrameTriv (τfrm := A.frameTop) Θ) ⟨(x.1.1 : B), x.2⟩
            (A.frameSection i ⟨(x.1.1 : B), x.1.1.2⟩)) x.1.2 :=
      continuous_frameIsom_eval hw (continuous_snd.comp continuous_subtype_val)
    rw [continuousOn_iff_continuous_restrict]
    refine hcont.congr fun x => ?_
    have hp : ((x.1.1 : B)) ∈ U := x.2
    rw [Set.restrict_apply,
      ovMap_apply (U := A.toChartAtlas.optU U) (chart := A.toChartAtlas.optChart U χ)
        (i := some i) (j := none) x.1 hp]
    exact key i (x.1.1 : B) hp x.1.1.2 x.1.2
  exact
    { alg := reconAlg Θ
      isOpen_dom := Θ.isOpen_dom
      continuous_chart := A.toChartAtlas.continuous_addChart U χ Θ.isOpen_dom h1 h2
      continuous_chartSymm := A.toChartAtlas.continuous_addChart_symm U χ Θ.isOpen_dom h1 h2 }

end Continuity

/-! ## Package J — the exact fibre/frame equivalence (items 88, 91–92) -/

section AtlasEquivalence

variable (A : MetricOrientedFibreAtlas F ι) {U : Set B}

/-- **DERIVED.**  Extensionality for topological fibre trivializations: they are determined
by their fibrewise identifications. -/
theorem topologicalFibreTriv_ext {τ : TopologicalSpace (Total E)}
    {Φ Ψ : TopologicalFibreTriv (τtot := τ) F U}
    (h : ∀ b : U, (TopologicalFibreTriv.alg (τtot := τ) Φ).iso b
      = (TopologicalFibreTriv.alg (τtot := τ) Ψ).iso b) : Φ = Ψ := by
  obtain ⟨⟨fi, fo⟩, h1, h2, h3⟩ := Φ
  obtain ⟨⟨gi, go⟩, k1, k2, k3⟩ := Ψ
  have hfi : fi = gi := funext h
  subst hfi
  rfl

/-- **DERIVED.**  Extensionality for compatible topological frame trivializations. -/
theorem compatibleFrameTriv_ext {τ : TopologicalSpace (Total F.FramePlusAt)}
    {Θ Ξ : CompatibleFrameTriv (τfrm := τ) F U}
    (h : ∀ (b : U) (v : F.FramePlusAt (b : B)),
      TopologicalFrameTriv.frameEquiv (τfrm := τ)
          (CompatibleFrameTriv.toTopologicalFrameTriv (τfrm := τ) Θ) b v
        = TopologicalFrameTriv.frameEquiv (τfrm := τ)
          (CompatibleFrameTriv.toTopologicalFrameTriv (τfrm := τ) Ξ) b v) : Θ = Ξ := by
  obtain ⟨⟨fe, h1, h2, h3⟩, he⟩ := Θ
  obtain ⟨⟨ge, k1, k2, k3⟩, ke⟩ := Ξ
  have hfe : fe = ge := funext fun b => Equiv.ext (h b)
  subst hfe
  rfl

/-- **DERIVED (items 91–92), principal.**  The frame trivialization induced by a topological
metric-oriented fibre trivialization is *equivariant*, hence a compatible topological frame
trivialization. -/
noncomputable def compatibleFrameTrivOfFibreTriv
    (Φ : TopologicalFibreTriv (τtot := A.top) F U) :
    CompatibleFrameTriv (τfrm := A.frameTop) F U :=
  letI := A.frameTop
  { toTopologicalFrameTriv := topologicalFibreTriv_induces_topologicalFrameTriv A Φ
    equivariant := fun b v k =>
      frameEquivOfIsom_frameRAct
        ((TopologicalFibreTriv.alg (τtot := A.top) Φ).orientation_preserving b) v k }

theorem compatibleFrameTrivOfFibreTriv_frameEquiv
    (Φ : TopologicalFibreTriv (τtot := A.top) F U) (b : U) :
    TopologicalFrameTriv.frameEquiv (τfrm := A.frameTop)
        (CompatibleFrameTriv.toTopologicalFrameTriv (τfrm := A.frameTop)
          (compatibleFrameTrivOfFibreTriv A Φ)) b
      = MetricOrientedRankThreeFamily.frameTrivAt
          (TopologicalFibreTriv.alg (τtot := A.top) Φ) b := by
  rfl

theorem fibreTrivOfCompatibleFrameTriv_alg
    (Θ : CompatibleFrameTriv (τfrm := A.frameTop) F U) :
    TopologicalFibreTriv.alg (τtot := A.top) (fibreTrivOfCompatibleFrameTriv A Θ)
      = reconAlg (τfrm := A.frameTop) Θ := rfl

/-- **DERIVED (item 88).**  Reconstructing the fibre trivialization from the induced frame
trivialization returns the original fibre trivialization. -/
theorem fibreTriv_roundtrip (Φ : TopologicalFibreTriv (τtot := A.top) F U) :
    fibreTrivOfCompatibleFrameTriv A (compatibleFrameTrivOfFibreTriv A Φ) = Φ := by
  refine topologicalFibreTriv_ext fun b => ?_
  rw [fibreTrivOfCompatibleFrameTriv_alg]
  refine (reconIso_unique (τfrm := A.frameTop) (compatibleFrameTrivOfFibreTriv A Φ) b
    ((TopologicalFibreTriv.alg (τtot := A.top) Φ).iso b)
    ((TopologicalFibreTriv.alg (τtot := A.top) Φ).orientation_preserving b) fun v => ?_).symm
  rw [compatibleFrameTrivOfFibreTriv_frameEquiv]
  rfl

/-- **DERIVED (item 88).**  Inducing the frame trivialization from the reconstructed fibre
trivialization returns the original compatible frame trivialization. -/
theorem frameTriv_roundtrip (Θ : CompatibleFrameTriv (τfrm := A.frameTop) F U) :
    compatibleFrameTrivOfFibreTriv A (fibreTrivOfCompatibleFrameTriv A Θ) = Θ := by
  refine compatibleFrameTriv_ext (τ := A.frameTop) fun b v => ?_
  rw [compatibleFrameTrivOfFibreTriv_frameEquiv, fibreTrivOfCompatibleFrameTriv_alg]
  exact frameEquivOfIsom_reconIso (τfrm := A.frameTop) Θ b v

/-- **DERIVED (item 88), principal — the strongest endpoint of hard target C.**  Over any
open set, topological metric-oriented fibre trivializations and equivariant topological frame
trivializations are the same data. -/
noncomputable def fibreTrivEquivCompatibleFrameTriv :
    TopologicalFibreTriv (τtot := A.top) F U ≃ CompatibleFrameTriv (τfrm := A.frameTop) F U where
  toFun := compatibleFrameTrivOfFibreTriv A
  invFun := fibreTrivOfCompatibleFrameTriv A
  left_inv := fibreTriv_roundtrip A
  right_inv := frameTriv_roundtrip A

/-- **DERIVED (item 91).**  Atlas level: every chart of a metric-oriented fibre atlas gives a
compatible topological frame trivialization over the same domain, whose fibrewise part is the
inherited algebraic frame chart. -/
theorem compatibleFrameTrivOfFibreTriv_atlas (i : ι) (b : A.U i) :
    TopologicalFrameTriv.frameEquiv (τfrm := A.frameTop)
        (CompatibleFrameTriv.toTopologicalFrameTriv (τfrm := A.frameTop)
          (compatibleFrameTrivOfFibreTriv A (A.topTriv i))) b
      = A.frameChartOf i b :=
  compatibleFrameTrivOfFibreTriv_frameEquiv A (A.topTriv i) b

end AtlasEquivalence

/-! ## Package L — the conditional global-section statement (items 99–101) -/

section GlobalSection

variable (A : MetricOrientedFibreAtlas F ι)

/-- **DERIVED (item 100), principal.**  *Conditional* statement only: if a **global**
topological metric-oriented fibre trivialization exists, then there is a continuous global
frame section.  No continuous global frame is asserted unconditionally (item 99). -/
theorem exists_continuous_global_frameSection
    (Φ : TopologicalFibreTriv (τtot := A.top) F Set.univ) :
    ∃ s : B → Total F.FramePlusAt,
      (∀ b, (s b).1 = b) ∧ @Continuous _ _ _ A.frameTop s := by
  letI := A.frameTop
  set Θ := topologicalFibreTriv_induces_topologicalFrameTriv A Φ with hΘ
  refine ⟨fun b => ((frameChartSymm
    (TopologicalFrameTriv.frameEquiv (τfrm := A.frameTop) Θ)
      (⟨b, Set.mem_univ b⟩, modelFrame)) : Total F.FramePlusAt), fun b => rfl, ?_⟩
  exact continuous_subtype_val.comp
    ((TopologicalFrameTriv.continuous_chartSymm (τfrm := A.frameTop) Θ).comp
      ((continuous_id.subtype_mk _).prodMk continuous_const))

end GlobalSection

end Recon

end NullSectorTask27
