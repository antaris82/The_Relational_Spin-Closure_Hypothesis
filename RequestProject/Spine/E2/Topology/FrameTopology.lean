import RequestProject.Spine.E2.Topology.AtlasExtension
import RequestProject.Spine.E2.Topology.FiberTopology

/-!
# Task 27, Package F: the topological ordinary-frame total space

**Hard target B.**

The inherited total ordinary-frame carrier `FrameTotal F = Σ b, FramePlusAt b` (Task XXVI,
unchanged) is topologized *from the fibre atlas*, never by the automatic sigma topology
(item 58).  Concretely:

* every metric-oriented fibre atlas induces a **frame atlas** whose charts are exactly the
  inherited algebraic frame trivializations `frameTrivAt`, and whose overlap maps are
  continuous because the fibre overlap maps are (the frame overlap map is the fibre overlap
  map applied to each of the three frame vectors);
* the frame total space therefore carries the atlas topology `frameTop`, admissible and
  unique in the same sense as on the fibre side;
* `TopologicalFrameTriv` is the frame analogue of `TopologicalFibreTriv`;
* **item 63**: a topological metric-oriented fibre trivialization over *any* open `U` — not
  merely a member of the atlas — induces a topological frame trivialization over `U`, i.e. a
  homeomorphism `frameBase⁻¹ U ≃ₜ U × FramePlusModel` over the base whose fibrewise part is
  exactly the inherited algebraic frame equivalence.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask27

open NullSectorTask26 Topology Module

universe u v t

section FrameCarrier

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : MetricOrientedRankThreeFamily B E}

omit [TopologicalSpace B] in
/-- **DERIVED (item 56).**  The Task-XXVII frame carrier is the inherited Task-XXVI one. -/
theorem frameTotal_def : F.FrameTotal = Total F.FramePlusAt := rfl

omit [TopologicalSpace B] in
/-- **DERIVED (item 56).**  The inherited frame projection is the generic base projection. -/
theorem frameBase_def : F.frameBase = totalBase F.FramePlusAt := rfl

/-- The part of the total frame carrier lying over a subset of the base. -/
def framePart (F : MetricOrientedRankThreeFamily B E) (U : Set B) :
    Set (Total F.FramePlusAt) := {x | totalBase F.FramePlusAt x ∈ U}

/-- The chart map attached to a family of fibrewise frame identifications. -/
def frameChartFun {U : Set B} (θ : ∀ b : U, F.FramePlusAt (b : B) ≃ FramePlusModel) :
    framePart F U → U × FramePlusModel :=
  fun x => (⟨totalBase F.FramePlusAt x.1, x.2⟩, θ ⟨totalBase F.FramePlusAt x.1, x.2⟩ x.1.2)

/-- The inverse chart map attached to a family of fibrewise frame identifications. -/
def frameChartSymm {U : Set B} (θ : ∀ b : U, F.FramePlusAt (b : B) ≃ FramePlusModel) :
    U × FramePlusModel → framePart F U :=
  fun p => ⟨⟨(p.1 : B), (θ p.1).symm p.2⟩, p.1.2⟩

/-- **DERIVED.**  The two frame chart maps are mutually inverse. -/
noncomputable def frameChartEquiv {U : Set B} (θ : ∀ b : U, F.FramePlusAt (b : B) ≃ FramePlusModel) :
    framePart F U ≃ U × FramePlusModel where
  toFun := frameChartFun θ
  invFun := frameChartSymm θ
  left_inv := by
    rintro ⟨⟨b, v⟩, hb⟩
    apply Subtype.ext
    show (⟨b, (θ ⟨b, hb⟩).symm (θ ⟨b, hb⟩ v)⟩ : Total F.FramePlusAt) = ⟨b, v⟩
    rw [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨b, hb⟩, w⟩
    refine Prod.ext rfl ?_
    show θ ⟨b, hb⟩ ((θ ⟨b, hb⟩).symm w) = w
    rw [Equiv.apply_symm_apply]

/-- **NEWLY DEFINED (items 59–62), principal.**  A *topological local frame trivialization*
over the open set `U`: a fibrewise identification of the frame spaces with the model frame
space whose induced total-space chart is a homeomorphism over the base. -/
structure TopologicalFrameTriv (F : MetricOrientedRankThreeFamily B E)
    [τfrm : TopologicalSpace (Total F.FramePlusAt)] (U : Set B) where
  /-- The fibrewise frame identification. -/
  frameEquiv : ∀ b : U, F.FramePlusAt (b : B) ≃ FramePlusModel
  /-- The domain is open. -/
  isOpen_dom : IsOpen U
  /-- The chart map is continuous. -/
  continuous_chart : Continuous (frameChartFun frameEquiv)
  /-- The inverse chart map is continuous. -/
  continuous_chartSymm : Continuous (frameChartSymm frameEquiv)

namespace TopologicalFrameTriv

variable [TopologicalSpace (Total F.FramePlusAt)] {U : Set B} (Θ : TopologicalFrameTriv F U)

/-- **DERIVED (item 60), principal.**  The frame chart is a homeomorphism onto the local
product. -/
noncomputable def homeo : framePart F U ≃ₜ U × FramePlusModel where
  toEquiv := frameChartEquiv Θ.frameEquiv
  continuous_toFun := Θ.continuous_chart
  continuous_invFun := Θ.continuous_chartSymm

/-- **DERIVED (item 61).**  Projection compatibility. -/
theorem homeo_fst (x : framePart F U) :
    ((Θ.homeo x).1 : B) = totalBase F.FramePlusAt x.1 := rfl

end TopologicalFrameTriv

end FrameCarrier

/-! ## The frame atlas induced by a metric-oriented fibre atlas -/

section FrameAtlas

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : MetricOrientedRankThreeFamily B E} {ι : Type t}

namespace MetricOrientedFibreAtlas

variable (A : MetricOrientedFibreAtlas F ι)

/-- The frame charts of the atlas: the inherited algebraic frame trivializations. -/
noncomputable def frameChartOf (i : ι) (b : A.U i) :
    F.FramePlusAt (b : B) ≃ FramePlusModel :=
  MetricOrientedRankThreeFamily.frameTrivAt (A.triv i) b

/-- **DERIVED, principal.**  The frame overlap map is the fibre overlap map applied to each
of the three frame vectors.  This is the algebraic identity behind the continuity of the
frame transition data. -/
theorem ovMap_frame_vec (i j : ι) (p : (A.U i) × FramePlusModel)
    (h : (p.1 : B) ∈ A.U j) (k : Fin 3) :
    FramePlusOf.vec (ovMap A.U A.frameChartOf i j p) k
      = ovMap A.U (fun i b => fibreChart (A.triv i) b) i j (p.1, FramePlusOf.vec p.2 k) := by
  rw [ovMap_apply (chart := A.frameChartOf) p h,
    ovMap_apply (chart := fun i b => fibreChart (A.triv i) b) (p.1, FramePlusOf.vec p.2 k) h]
  rfl

/-- **DERIVED, principal.**  The frame atlas induced by the fibre atlas: same domains, the
inherited algebraic frame trivializations as charts, and continuous overlap maps. -/
noncomputable def toFrameAtlas : ChartAtlas F.FramePlusAt FramePlusModel ι where
  U := A.U
  isOpen_U := A.isOpen_U
  cover := A.cover
  chart := A.frameChartOf
  continuousOn_overlap := by
    intro i j
    rw [continuousOn_iff_continuous_restrict, continuous_framePlus_iff]
    intro k
    have hmap : ∀ x : {p : (A.U i) × FramePlusModel | (p.1 : B) ∈ A.U j},
        FramePlusOf.vec (ovMap A.U A.frameChartOf i j x.1) k
          = ovMap A.U (fun i b => fibreChart (A.triv i) b) i j
            (x.1.1, FramePlusOf.vec x.1.2 k) := fun x => A.ovMap_frame_vec i j x.1 x.2 k
    have hcont : Continuous fun x : {p : (A.U i) × FramePlusModel | (p.1 : B) ∈ A.U j} =>
        ((x.1.1, FramePlusOf.vec x.1.2 k) : (A.U i) × Model) :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_framePlus_vec k).comp (continuous_snd.comp continuous_subtype_val))
    have hmem : ∀ x : {p : (A.U i) × FramePlusModel | (p.1 : B) ∈ A.U j},
        ((x.1.1, FramePlusOf.vec x.1.2 k) : (A.U i) × Model)
          ∈ {p : (A.U i) × Model | (p.1 : B) ∈ A.U j} := fun x => x.2
    have hres := (A.continuousOn_overlap i j).comp_continuous hcont hmem
    exact hres.congr fun x => (hmap x).symm

@[simp] theorem toFrameAtlas_U (i : ι) : A.toFrameAtlas.U i = A.U i := rfl

theorem toFrameAtlas_dom (i : ι) : A.toFrameAtlas.dom i = framePart F (A.U i) := rfl

/-- **NEWLY DEFINED (items 57–58), principal.**  The topology of the total ordinary-frame
carrier: the atlas topology of the induced frame atlas.  It is **not** the automatic sigma
topology. -/
noncomputable def frameTop : TopologicalSpace (Total F.FramePlusAt) := A.toFrameAtlas.top

/-- **DERIVED, principal.**  The frame topology is admissible: the frame projection is
continuous and every induced frame chart is a homeomorphism. -/
theorem frameTop_isAdmissible : letI := A.frameTop; A.toFrameAtlas.IsAdmissible :=
  A.toFrameAtlas.top_isAdmissible

/-- **DERIVED, principal.**  Uniqueness of the frame topology. -/
theorem frame_eq_top_of_isAdmissible {τ : TopologicalSpace (Total F.FramePlusAt)}
    (h : @ChartAtlas.IsAdmissible _ _ _ _ _ _ A.toFrameAtlas τ) : τ = A.frameTop :=
  ChartAtlas.IsAdmissible.eq_top A.toFrameAtlas h

end MetricOrientedFibreAtlas

/-! ## Continuity of transition data between arbitrary topological trivializations -/

section Transitions

variable [τtot : TopologicalSpace (Total E)] {U W : Set B}

open Classical in
/-- **DERIVED, principal.**  The fibre transition map between two topological fibre
trivializations is continuous on the overlap.  The proof uses the continuity of the two
total-space charts, not merely pointwise membership in the model group. -/
theorem continuousOn_fibre_transition (Φ : TopologicalFibreTriv F U)
    (Ψ : TopologicalFibreTriv F W) :
    ContinuousOn (fun p : ↥U × Model =>
        if h : (p.1 : B) ∈ W then Ψ.alg.iso ⟨(p.1 : B), h⟩ ((Φ.alg.iso p.1).symm p.2)
        else p.2)
      {p : ↥U × Model | (p.1 : B) ∈ W} := by
  rw [continuousOn_iff_continuous_restrict]
  have hk : Continuous fun x : {p : ↥U × Model | (p.1 : B) ∈ W} =>
      ((fibreChartSymm Φ.alg x.1 : Total E)) :=
    continuous_subtype_val.comp (Φ.continuous_chartSymm.comp continuous_subtype_val)
  have hk2 : Continuous fun x : {p : ↥U × Model | (p.1 : B) ∈ W} =>
      (⟨(fibreChartSymm Φ.alg x.1 : Total E), x.2⟩ : fibrePart E W) :=
    hk.subtype_mk _
  have hcomp := (continuous_snd.comp (Ψ.continuous_chart.comp hk2))
  refine hcomp.congr fun x => ?_
  have hx : ((x.1.1 : B)) ∈ W := x.2
  rw [Set.restrict_apply, dif_pos hx]
  rfl

open Classical in
/-- **DERIVED, principal.**  The frame transition map between the induced frame
trivializations is continuous on the overlap. -/
theorem continuousOn_frame_transition (Φ : TopologicalFibreTriv F U)
    (Ψ : TopologicalFibreTriv F W) :
    ContinuousOn (fun p : ↥U × FramePlusModel =>
        if h : (p.1 : B) ∈ W then
          MetricOrientedRankThreeFamily.frameTrivAt Ψ.alg ⟨(p.1 : B), h⟩
            ((MetricOrientedRankThreeFamily.frameTrivAt Φ.alg p.1).symm p.2)
        else p.2)
      {p : ↥U × FramePlusModel | (p.1 : B) ∈ W} := by
  rw [continuousOn_iff_continuous_restrict, continuous_framePlus_iff]
  intro k
  have hcont : Continuous fun x : {p : ↥U × FramePlusModel | (p.1 : B) ∈ W} =>
      ((x.1.1, FramePlusOf.vec x.1.2 k) : ↥U × Model) :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_framePlus_vec k).comp (continuous_snd.comp continuous_subtype_val))
  have hmem : ∀ x : {p : ↥U × FramePlusModel | (p.1 : B) ∈ W},
      ((x.1.1, FramePlusOf.vec x.1.2 k) : ↥U × Model)
        ∈ {p : ↥U × Model | (p.1 : B) ∈ W} := fun x => x.2
  have hbase := (continuousOn_fibre_transition Φ Ψ).comp_continuous hcont hmem
  refine hbase.congr fun x => ?_
  have hx : ((x.1.1 : B)) ∈ W := x.2
  simp only [Function.comp_apply, Set.restrict_apply, dif_pos hx]
  rfl

end Transitions

/-! ## Item 63: a topological fibre trivialization induces a topological frame
trivialization -/

section Induced

variable (A : MetricOrientedFibreAtlas F ι) {U : Set B}

/-- **DERIVED (item 63), principal.**  Given the atlas topologies on the total fibre carrier
and on the total frame carrier, every topological metric-oriented fibre trivialization over
an open set `U` induces a topological frame trivialization over `U`; its fibrewise part is
exactly the inherited algebraic frame equivalence `frameTrivAt`. -/
noncomputable def topologicalFibreTriv_induces_topologicalFrameTriv
    (Φ : TopologicalFibreTriv (τtot := A.top) F U) :
    TopologicalFrameTriv (τfrm := A.frameTop) F U := by
  letI := A.top
  letI := A.frameTop
  classical
  -- the extra frame chart over `U`
  set χ : ∀ b : U, F.FramePlusAt (b : B) ≃ FramePlusModel := fun b =>
    MetricOrientedRankThreeFamily.frameTrivAt Φ.alg b with hχ
  have h1 : ∀ i, ContinuousOn
      (ovMap (A.toFrameAtlas.optU U) (A.toFrameAtlas.optChart U χ) none (some i))
      {p : (A.toFrameAtlas.optU U none) × FramePlusModel |
        (p.1 : B) ∈ A.toFrameAtlas.optU U (some i)} := by
    intro idx
    refine (continuousOn_frame_transition (τtot := A.top) Φ (A.topTriv idx)).congr
      fun p hp => ?_
    rw [ovMap_apply (U := A.toFrameAtlas.optU U) (chart := A.toFrameAtlas.optChart U χ)
      (i := none) (j := some idx) p hp]
    have hp' : (p.1 : B) ∈ A.U idx := hp
    rw [dif_pos hp']
    rfl
  have h2 : ∀ i, ContinuousOn
      (ovMap (A.toFrameAtlas.optU U) (A.toFrameAtlas.optChart U χ) (some i) none)
      {p : (A.toFrameAtlas.optU U (some i)) × FramePlusModel |
        (p.1 : B) ∈ A.toFrameAtlas.optU U none} := by
    intro idx
    refine (continuousOn_frame_transition (τtot := A.top) (A.topTriv idx) Φ).congr
      fun p hp => ?_
    rw [ovMap_apply (U := A.toFrameAtlas.optU U) (chart := A.toFrameAtlas.optChart U χ)
      (i := some idx) (j := none) p hp]
    have hp' : (p.1 : B) ∈ U := hp
    rw [dif_pos hp']
    rfl
  exact
    { frameEquiv := χ
      isOpen_dom := Φ.isOpen_dom
      continuous_chart :=
        A.toFrameAtlas.continuous_addChart U χ Φ.isOpen_dom h1 h2
      continuous_chartSymm :=
        A.toFrameAtlas.continuous_addChart_symm U χ Φ.isOpen_dom h1 h2 }

/-- **DERIVED (item 62).**  The fibrewise part of the induced frame trivialization is
exactly the inherited algebraic frame equivalence. -/
theorem topologicalFibreTriv_induces_frameEquiv
    (Φ : TopologicalFibreTriv (τtot := A.top) F U) (b : U) :
    TopologicalFrameTriv.frameEquiv (τfrm := A.frameTop)
        (topologicalFibreTriv_induces_topologicalFrameTriv A Φ) b
      = MetricOrientedRankThreeFamily.frameTrivAt
          (TopologicalFibreTriv.alg (τtot := A.top) Φ) b := rfl

end Induced

end FrameAtlas

end NullSectorTask27
