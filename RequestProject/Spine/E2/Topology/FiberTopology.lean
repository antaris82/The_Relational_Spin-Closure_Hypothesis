import RequestProject.Spine.E2.Topology.AtlasTopology

/-!
# Task 27, Packages B, C, D, E: the topological fibre carrier

**Hard target A, applied to the varying metric-oriented fibres.**

* **Package B (items 24–33).**  The total fibre carrier `Total E = Σ b, E b` of the inherited
  family, its base projection, admissible topologies as an *explicit extra datum*, the exact
  description of the fibres, and the negative control that individual fibres need **not** be
  open.
* **Package C (items 34–42).**  `TopologicalFibreTriv`: a genuine *topological* local
  metric-oriented fibre trivialization — a homeomorphism `fiberBase⁻¹ U ≃ₜ U × Model` whose
  fibrewise restrictions are exactly the inherited real-linear, metric- and
  orientation-preserving identifications.  Both formulations of item 39/40 (pointwise family
  + total-space continuity, and total-space homeomorphism) are given and proved equivalent.
* **Package D (items 43–50).**  A metric-oriented *atlas* and the atlas-generated topology,
  obtained by specializing the generic `ChartAtlas` machinery: existence and uniqueness.
* **Package E (items 51–55).**  The comparison with the inherited sigma topology, with a
  minimal explicit example over a non-discrete base.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask27

open NullSectorTask26 Topology Module

universe u v t

section Carrier

variable {B : Type u} {E : B → Type v}

/-- **DERIVED (item 25).**  The total fibre carrier of Task XXVII is literally the dependent
sum of the inherited fibres. -/
theorem fiberTotal_def : Total E = Σ b : B, E b := rfl

/-- **DERIVED (items 30–31).**  The fibre of the base projection over `b` is exactly the set
of points of the total carrier whose first coordinate is `b`. -/
theorem fiberBase_preimage_singleton (b : B) :
    totalBase E ⁻¹' {b} = {x : Total E | x.1 = b} := rfl

/-- The part of the total fibre carrier lying over a subset of the base. -/
def fibrePart (E : B → Type v) (U : Set B) : Set (Total E) := {x | totalBase E x ∈ U}

theorem mem_fibrePart {U : Set B} {x : Total E} : x ∈ fibrePart E U ↔ totalBase E x ∈ U :=
  Iff.rfl

end Carrier

section Fibres

variable {B : Type u} {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : MetricOrientedRankThreeFamily B E}

/-- The plain bijection underlying an inherited algebraic fibre chart. -/
noncomputable def fibreChart {U : Set B} (Φ : F.LocalFibreTriv U) (b : U) : E (b : B) ≃ Model :=
  (Φ.iso b).toLinearEquiv.toEquiv

@[simp] theorem fibreChart_apply {U : Set B} (Φ : F.LocalFibreTriv U) (b : U) (e : E (b : B)) :
    fibreChart Φ b e = Φ.iso b e := rfl

@[simp] theorem fibreChart_symm_apply {U : Set B} (Φ : F.LocalFibreTriv U) (b : U)
    (m : Model) : (fibreChart Φ b).symm m = (Φ.iso b).symm m := rfl

/-- The chart map of an algebraic local fibre trivialization, on the total carrier. -/
noncomputable def fibreChartFun {U : Set B} (Φ : F.LocalFibreTriv U) :
    fibrePart E U → U × Model :=
  fun x => (⟨totalBase E x.1, x.2⟩, Φ.iso ⟨totalBase E x.1, x.2⟩ x.1.2)

/-- The inverse chart map of an algebraic local fibre trivialization. -/
noncomputable def fibreChartSymm {U : Set B} (Φ : F.LocalFibreTriv U) :
    U × Model → fibrePart E U :=
  fun p => ⟨⟨(p.1 : B), (Φ.iso p.1).symm p.2⟩, p.1.2⟩

/-- **DERIVED, principal.**  The two maps are mutually inverse bijections. -/
noncomputable def fibreChartEquiv {U : Set B} (Φ : F.LocalFibreTriv U) :
    fibrePart E U ≃ U × Model where
  toFun := fibreChartFun Φ
  invFun := fibreChartSymm Φ
  left_inv := by
    rintro ⟨⟨b, e⟩, hb⟩
    apply Subtype.ext
    show (⟨b, (Φ.iso ⟨b, hb⟩).symm (Φ.iso ⟨b, hb⟩ e)⟩ : Total E) = ⟨b, e⟩
    rw [LinearIsometryEquiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨b, hb⟩, m⟩
    refine Prod.ext rfl ?_
    show Φ.iso ⟨b, hb⟩ ((Φ.iso ⟨b, hb⟩).symm m) = m
    rw [LinearIsometryEquiv.apply_symm_apply]

/-- **DERIVED (item 36).**  Projection compatibility: the first coordinate of the chart is
the base point. -/
theorem fibreChartFun_fst {U : Set B} (Φ : F.LocalFibreTriv U) (x : fibrePart E U) :
    ((fibreChartFun Φ x).1 : B) = totalBase E x.1 := rfl

/-! ## Topological local fibre trivializations (Package C) -/

variable [TopologicalSpace B]

/-- **NEWLY DEFINED (items 34–42), principal.**  A *topological metric-oriented local fibre
trivialization* over the open set `U`: the inherited algebraic trivialization `alg` (whose
fibrewise restrictions are real-linear isometries preserving the orientation datum) together
with continuity of the induced total-space chart in both directions.  By
`TopologicalFibreTriv.homeo` this is exactly a homeomorphism
`fiberBase⁻¹ U ≃ₜ U × Model` over the base whose fibrewise parts are the algebraic data
(items 39–40), and it is *not* called a vector-bundle trivialization (item 42). -/
structure TopologicalFibreTriv [τtot : TopologicalSpace (Total E)]
    (F : MetricOrientedRankThreeFamily B E) (U : Set B) where
  /-- The inherited algebraic trivialization. -/
  alg : F.LocalFibreTriv U
  /-- The domain is open. -/
  isOpen_dom : IsOpen U
  /-- The chart map is continuous. -/
  continuous_chart : Continuous (fibreChartFun alg)
  /-- The inverse chart map is continuous. -/
  continuous_chartSymm : Continuous (fibreChartSymm alg)

namespace TopologicalFibreTriv

variable [TopologicalSpace (Total E)] {U : Set B} (Φ : TopologicalFibreTriv F U)

/-- **DERIVED (items 35, 40), principal.**  The chart of a topological fibre trivialization
is a homeomorphism onto the local product. -/
noncomputable def homeo : fibrePart E U ≃ₜ U × Model where
  toEquiv := fibreChartEquiv Φ.alg
  continuous_toFun := Φ.continuous_chart
  continuous_invFun := Φ.continuous_chartSymm

/-- **DERIVED (item 36).**  Projection compatibility. -/
theorem homeo_fst (x : fibrePart E U) : ((Φ.homeo x).1 : B) = totalBase E x.1 := rfl

/-- **DERIVED (item 37).**  Each fibre restriction is real-linear. -/
theorem fibrewise_linear (b : U) (r : ℝ) (e f : E (b : B)) :
    Φ.alg.iso b (r • e + f) = r • Φ.alg.iso b e + Φ.alg.iso b f := by
  rw [map_add, map_smul]

/-- **DERIVED (item 37).**  Each fibre restriction is an isometry. -/
theorem fibrewise_isometry (b : U) (e f : E (b : B)) :
    inner ℝ (Φ.alg.iso b e) (Φ.alg.iso b f) = inner ℝ e f :=
  LinearIsometryEquiv.inner_map_map _ e f

/-- **DERIVED (item 37).**  Each fibre restriction preserves the orientation datum. -/
theorem fibrewise_orientation (b : U) :
    IsOrientationPreserving (F.orient (b : B)) modelOrient (Φ.alg.iso b) :=
  Φ.alg.orientation_preserving b

end TopologicalFibreTriv

/-- **DERIVED (items 39–40), principal.**  The converse of the packaging: a homeomorphism of
the total-space chart *is* a topological fibre trivialization.  The pointwise formulation
plus total-space continuity and the total-space homeomorphism formulation are therefore
equivalent notions. -/
def topologicalFibreTriv_of_homeo [TopologicalSpace (Total E)] {U : Set B}
    (alg : F.LocalFibreTriv U) (hU : IsOpen U) (h : fibrePart E U ≃ₜ U × Model)
    (hh : ∀ x, h x = fibreChartFun alg x) : TopologicalFibreTriv F U where
  alg := alg
  isOpen_dom := hU
  continuous_chart := by
    have heq : fibreChartFun alg = fun x => h x := funext fun x => (hh x).symm
    rw [heq]
    exact h.continuous
  continuous_chartSymm := by
    have hsymm : ∀ p, h.symm p = fibreChartSymm alg p := by
      intro p
      have hp := hh (h.symm p)
      rw [Homeomorph.apply_symm_apply] at hp
      have h2 : (fibreChartEquiv alg) (h.symm p) = p := hp.symm
      calc h.symm p = (fibreChartEquiv alg).symm ((fibreChartEquiv alg) (h.symm p)) :=
            ((fibreChartEquiv alg).symm_apply_apply _).symm
        _ = fibreChartSymm alg p := by rw [h2]; rfl
    have heq : fibreChartSymm alg = fun p => h.symm p := funext fun p => (hsymm p).symm
    rw [heq]
    exact h.continuous_symm

/-! ## Metric-oriented atlases and the atlas-generated topology (Package D) -/

/-- **NEWLY DEFINED (items 43–44), principal.**  A *metric-oriented fibre atlas*: an open
cover of the base, an inherited algebraic local fibre trivialization over each domain, and
continuity of the overlap maps.  This is exactly the extra datum that Task XXVI identified as
missing. -/
structure MetricOrientedFibreAtlas (F : MetricOrientedRankThreeFamily B E) (ι : Type t) where
  /-- The trivializing domains. -/
  U : ι → Set B
  /-- Each domain is open. -/
  isOpen_U : ∀ i, IsOpen (U i)
  /-- The domains cover the base. -/
  cover : ∀ b : B, ∃ i, b ∈ U i
  /-- The inherited algebraic trivialization over each domain. -/
  triv : ∀ i, F.LocalFibreTriv (U i)
  /-- Continuity of the overlap maps. -/
  continuousOn_overlap : ∀ i j : ι,
    ContinuousOn (ovMap U (fun i b => fibreChart (triv i) b) i j)
      {p : (U i) × Model | (p.1 : B) ∈ U j}

namespace MetricOrientedFibreAtlas

variable {ι : Type t} (A : MetricOrientedFibreAtlas F ι)

/-- The underlying generic chart atlas. -/
noncomputable def toChartAtlas : ChartAtlas E Model ι where
  U := A.U
  isOpen_U := A.isOpen_U
  cover := A.cover
  chart := fun i b => fibreChart (A.triv i) b
  continuousOn_overlap := A.continuousOn_overlap

@[simp] theorem toChartAtlas_U (i : ι) : A.toChartAtlas.U i = A.U i := rfl

theorem toChartAtlas_dom (i : ι) : A.toChartAtlas.dom i = fibrePart E (A.U i) := rfl

theorem toChartAtlas_chartFun (i : ι) :
    A.toChartAtlas.chartFun i = fibreChartFun (A.triv i) := rfl

theorem toChartAtlas_chartSymm (i : ι) :
    A.toChartAtlas.chartSymm i = fibreChartSymm (A.triv i) := rfl

/-- **NEWLY DEFINED (items 45–47), principal.**  The topology on the total fibre carrier
generated by a metric-oriented atlas: open means "open in every local product chart". -/
noncomputable def top : TopologicalSpace (Total E) := A.toChartAtlas.top

theorem isOpen_top_iff (S : Set (Total E)) :
    IsOpen[A.top] S ↔ ∀ i, IsOpen (A.toChartAtlas.psi i ⁻¹' S) :=
  A.toChartAtlas.isOpen_top_iff S

/-- **DERIVED (item 30), principal.**  For the atlas topology the base projection is
continuous. -/
theorem continuous_top_fiberBase : letI := A.top; Continuous (totalBase E) :=
  A.toChartAtlas.continuous_top_base

/-- **DERIVED (items 45–47), principal.**  Existence: the atlas topology makes every chart of
the atlas a genuine topological metric-oriented local fibre trivialization. -/
noncomputable def topTriv (i : ι) :
    letI := A.top; TopologicalFibreTriv F (A.U i) :=
  letI := A.top
  { alg := A.triv i
    isOpen_dom := A.isOpen_U i
    continuous_chart := A.toChartAtlas.continuous_top_chartFun i
    continuous_chartSymm := A.toChartAtlas.continuous_top_chartSymm i }

/-- **DERIVED (items 45–48), principal.**  A topology on the total fibre carrier for which
the base projection is continuous and all atlas charts are homeomorphisms is *unique*, and
equals the atlas topology. -/
theorem eq_top_of_isAdmissible {τ : TopologicalSpace (Total E)}
    (h : @ChartAtlas.IsAdmissible _ _ _ _ _ _ A.toChartAtlas τ) : τ = A.top :=
  ChartAtlas.IsAdmissible.eq_top A.toChartAtlas h

/-- **DERIVED (item 47).**  The atlas topology is itself admissible, so existence and
uniqueness together characterize it. -/
theorem top_isAdmissible : letI := A.top; A.toChartAtlas.IsAdmissible :=
  A.toChartAtlas.top_isAdmissible

/-- **DERIVED.**  Each fibre embeds continuously into the total carrier. -/
theorem continuous_top_fibreInclusion (b : B) :
    @Continuous (E b) (Total E) _ A.top (fun e => (⟨b, e⟩ : Total E)) := by
  letI := A.top
  obtain ⟨i, hi⟩ := A.cover b
  have hfac : (fun e : E b => (⟨b, e⟩ : Total E))
      = fun e : E b => A.toChartAtlas.psi i (⟨b, hi⟩, A.triv i |>.iso ⟨b, hi⟩ e) := by
    funext e
    show (⟨b, e⟩ : Total E) = ⟨b, (A.triv i).iso ⟨b, hi⟩ |>.symm ((A.triv i).iso ⟨b, hi⟩ e)⟩
    rw [LinearIsometryEquiv.symm_apply_apply]
  rw [hfac]
  exact (A.toChartAtlas.continuous_psi_top i).comp
    (continuous_const.prodMk ((A.triv i).iso ⟨b, hi⟩).continuous)

end MetricOrientedFibreAtlas

/-! ## Package E — comparison with the inherited sigma topology -/

/-- The topology that the dependent sum carries automatically.  It is named here only in
order to be *rejected*: it is never used as the total-space topology (item 19). -/
def sigmaTop (E : B → Type v) [∀ b, TopologicalSpace (E b)] : TopologicalSpace (Total E) :=
  inferInstanceAs (TopologicalSpace (Σ b : B, E b))

omit [∀ b, InnerProductSpace ℝ (E b)] [TopologicalSpace B] in
/-- **NEGATIVE CONTROL (item 51), inherited from Task XXVI.**  In the sigma topology every
fibre is open. -/
theorem isOpen_sigmaTop_fibre (b : B) :
    IsOpen[sigmaTop E] {x : Total E | x.1 = b} :=
  isOpen_sigmaFiber b

end Fibres

/-! ### A minimal example over a non-discrete base (items 52–55)

The base is `ℝ`, the fibre is constantly the model carrier, and the atlas has a single
global chart.  In the resulting atlas topology no fibre is open, whereas in the sigma
topology every fibre is open. -/

namespace Example27

/-- The constant metric-oriented rank-three family over the real line. -/
noncomputable def constFamily : MetricOrientedRankThreeFamily ℝ (fun _ : ℝ => Model) where
  rank_three := fun _ => model_rank_three
  orient := fun _ => modelOrient

/-- The global algebraic trivialization of the constant family. -/
noncomputable def constTriv (U : Set ℝ) : constFamily.LocalFibreTriv U where
  iso := fun _ => LinearIsometryEquiv.refl ℝ Model
  orientation_preserving := fun _ => isOrientationPreserving_refl _

/-- The one-chart atlas of the constant family over the real line. -/
noncomputable def constAtlas : MetricOrientedFibreAtlas constFamily Unit where
  U := fun _ => Set.univ
  isOpen_U := fun _ => isOpen_univ
  cover := fun b => ⟨(), Set.mem_univ b⟩
  triv := fun _ => constTriv Set.univ
  continuousOn_overlap := by
    intro i j
    have h : ovMap (C := fun _ : ℝ => Model) (fun _ : Unit => (Set.univ : Set ℝ))
        (fun i b => fibreChart (constTriv Set.univ) b) i j
        = fun p : ↑(Set.univ : Set ℝ) × Model => p.2 := by
      funext p
      rw [ovMap_apply (C := fun _ : ℝ => Model)
        (chart := fun i b => fibreChart (constTriv Set.univ) b) p (Set.mem_univ _)]
      rfl
    rw [h]
    exact continuous_snd.continuousOn

theorem not_isOpen_singleton_real : ¬ IsOpen ({(0 : ℝ)} : Set ℝ) := by
  intro h
  obtain ⟨x, hx1, hx2⟩ := (dense_compl_singleton (0:ℝ)).inter_open_nonempty _ h ⟨0, rfl⟩
  exact hx2 hx1

/-- **NEGATIVE CONTROL (items 32–33, 52–54), principal.**  In the atlas-generated topology of
this local product structure the individual fibre over `0` is **not** open.  Hence "every
fibre is open" is not part of, and not implied by, the local-product axioms. -/
theorem not_isOpen_fibre_in_atlasTop :
    ¬ IsOpen[constAtlas.top] {x : Total (fun _ : ℝ => Model) | x.1 = 0} := by
  intro h
  rw [MetricOrientedFibreAtlas.isOpen_top_iff] at h
  have h0 := h ()
  have hk : Continuous fun t : ℝ => ((⟨t, Set.mem_univ t⟩ : (Set.univ : Set ℝ)), (0 : Model)) :=
    (continuous_id.subtype_mk _).prodMk continuous_const
  have hpre : (fun t : ℝ => ((⟨t, Set.mem_univ t⟩ : (Set.univ : Set ℝ)), (0 : Model)))
      ⁻¹' (constAtlas.toChartAtlas.psi () ⁻¹' {x : Total (fun _ : ℝ => Model) | x.1 = 0})
      = {(0 : ℝ)} := by
    ext t
    simp [ChartAtlas.psi]
  exact not_isOpen_singleton_real (hpre ▸ (h0.preimage hk))

/-- **NEGATIVE CONTROL (item 53), principal.**  Consequently the sigma topology is *not*
forced by the local-product axioms: here it differs from the admissible atlas topology. -/
theorem atlasTop_ne_sigmaTop :
    constAtlas.top ≠ sigmaTop (fun _ : ℝ => Model) := by
  intro h
  exact not_isOpen_fibre_in_atlasTop (h ▸ isOpen_sigmaTop_fibre (E := fun _ : ℝ => Model) 0)

end Example27

end NullSectorTask27
