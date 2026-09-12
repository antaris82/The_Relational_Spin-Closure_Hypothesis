import RequestProject.Spine.E2.Topology.ModelTopology

/-!
# Task 27, Packages B–D (generic core): total-space topology from a chart atlas

**Hard target A.**

This module contains the purely topological heart of Task XXVII, stated once for an
arbitrary *varying carrier* `C : B → Type v` over a topological base `B` and a fixed model
`M`.  It is applied twice later: to the varying fibres `E b` with model `Model`, and to the
varying frame spaces `FramePlusAt b` with model `FramePlusModel`.  Nothing here knows about
metrics, orientations, frames or groups.

## Contents

* `Total C := Σ b, C b`, `totalBase`.  **The automatically inherited sigma topology is not
  used** (items 26, 28): `Total` is a plain (non-reducible) definition, so no
  `TopologicalSpace (Total C)` instance is ever synthesized for it; a topology is always an
  explicit extra datum, either an instance variable or the constructed `ChartAtlas.top`.
* `ChartAtlas C M ι`: an open cover `U i` of the base, a bijection `C b ≃ M` for every
  `b ∈ U i`, and the *continuity of the overlap maps* — the only analytic hypothesis.
* `ChartAtlas.top`: the atlas-generated topology; a set is open iff its preimage in every
  local product chart is open (item 46).
* `ChartAtlas.IsAdmissible`: a topology on `Total C` is admissible for the atlas when the
  base projection is continuous and every chart is a homeomorphism onto `U i × M`.
* `ChartAtlas.top_isAdmissible` (existence, item 47) and `ChartAtlas.IsAdmissible.eq_top`
  (uniqueness, item 48).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask27

open Topology

universe u v w t

/-! ## The total carrier of a varying family -/

section Total

variable {B : Type u}

/-- **NEWLY DEFINED (item 25).**  The total carrier of a varying family.  It is the dependent
sum; being a plain definition, it does **not** inherit the sigma topology as an instance
(items 26, 28). -/
def Total (C : B → Type v) : Type max u v := Σ b : B, C b

/-- **NEWLY DEFINED (item 29).**  The base projection of the total carrier. -/
def totalBase (C : B → Type v) : Total C → B := fun x => x.1

@[simp] theorem totalBase_mk {C : B → Type v} (b : B) (c : C b) :
    totalBase C (⟨b, c⟩ : Total C) = b := rfl

/-- **DERIVED (item 31).**  The fibre of the projection over `b` is exactly the set of points
with first coordinate `b`. -/
theorem totalBase_preimage {C : B → Type v} (b : B) :
    totalBase C ⁻¹' {b} = {x : Total C | x.1 = b} := rfl

end Total

/-! ## Chart atlases -/

variable {B : Type u} [TopologicalSpace B] {C : B → Type v} {M : Type w} [TopologicalSpace M]
  {ι : Type t}

open Classical in
/-- The overlap map of two charts, made total by a `dite`: on the overlap it is the chart
change `chart j ∘ (chart i)⁻¹`, elsewhere it is irrelevant. -/
noncomputable def ovMap (U : ι → Set B) (chart : ∀ (i : ι) (b : U i), C (b : B) ≃ M) (i j : ι) :
    (U i) × M → M :=
  fun p => if h : (p.1 : B) ∈ U j then chart j ⟨(p.1 : B), h⟩ ((chart i p.1).symm p.2)
    else p.2

omit [TopologicalSpace B] [TopologicalSpace M] in
theorem ovMap_apply {U : ι → Set B} {chart : ∀ (i : ι) (b : U i), C (b : B) ≃ M} {i j : ι}
    (p : (U i) × M) (h : (p.1 : B) ∈ U j) :
    ovMap U chart i j p = chart j ⟨(p.1 : B), h⟩ ((chart i p.1).symm p.2) := by
  unfold ovMap
  exact dif_pos h

/-- **NEWLY DEFINED (items 43–44), principal.**  A *chart atlas* for the varying carrier `C`
with model `M`: an open cover of the base together with a bijection of every fibre over
`U i` with `M`, subject to continuity of the overlap maps.  This is the exact input from
which an admissible total-space topology is constructed. -/
structure ChartAtlas (C : B → Type v) (M : Type w) [TopologicalSpace M] (ι : Type t) where
  /-- The trivializing domains. -/
  U : ι → Set B
  /-- Each domain is open. -/
  isOpen_U : ∀ i, IsOpen (U i)
  /-- The domains cover the base. -/
  cover : ∀ b : B, ∃ i, b ∈ U i
  /-- The fibrewise identification of the carrier with the model over each domain. -/
  chart : ∀ (i : ι) (b : U i), C (b : B) ≃ M
  /-- The only analytic hypothesis: the overlap maps are continuous. -/
  continuousOn_overlap : ∀ i j : ι,
    ContinuousOn (ovMap U chart i j) {p : (U i) × M | (p.1 : B) ∈ U j}

namespace ChartAtlas

variable (A : ChartAtlas C M ι)

/-- The part of the total carrier lying over the `i`-th domain. -/
def dom (i : ι) : Set (Total C) := {x : Total C | totalBase C x ∈ A.U i}

theorem mem_dom {i : ι} {x : Total C} : x ∈ A.dom i ↔ totalBase C x ∈ A.U i := Iff.rfl

theorem iUnion_dom : (⋃ i, A.dom i) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true, mem_dom]
  exact A.cover (totalBase C x)

/-- The local product parametrization attached to the `i`-th chart. -/
def psi (i : ι) : (A.U i) × M → Total C := fun p => ⟨(p.1 : B), (A.chart i p.1).symm p.2⟩

@[simp] theorem totalBase_psi (i : ι) (p : (A.U i) × M) :
    totalBase C (A.psi i p) = (p.1 : B) := rfl

theorem psi_mem_dom (i : ι) (p : (A.U i) × M) : A.psi i p ∈ A.dom i := p.1.2

/-- The chart map on the part of the total carrier lying over `U i`. -/
def chartFun (i : ι) : A.dom i → (A.U i) × M :=
  fun x => (⟨totalBase C x.1, x.2⟩, A.chart i ⟨totalBase C x.1, x.2⟩ x.1.2)

/-- The inverse chart map. -/
def chartSymm (i : ι) : (A.U i) × M → A.dom i := fun p => ⟨A.psi i p, A.psi_mem_dom i p⟩

/-- **DERIVED, principal.**  The chart map is a bijection: the two constructions above are
mutually inverse. -/
def chartEquiv (i : ι) : A.dom i ≃ (A.U i) × M where
  toFun := A.chartFun i
  invFun := A.chartSymm i
  left_inv := by
    rintro ⟨⟨b, c⟩, hb⟩
    apply Subtype.ext
    show (⟨b, (A.chart i ⟨b, hb⟩).symm (A.chart i ⟨b, hb⟩ c)⟩ : Total C) = ⟨b, c⟩
    rw [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨b, hb⟩, m⟩
    refine Prod.ext rfl ?_
    show A.chart i ⟨b, hb⟩ ((A.chart i ⟨b, hb⟩).symm m) = m
    rw [Equiv.apply_symm_apply]

@[simp] theorem chartEquiv_apply (i : ι) (x : A.dom i) : A.chartEquiv i x = A.chartFun i x :=
  rfl

@[simp] theorem chartEquiv_symm_apply (i : ι) (p : (A.U i) × M) :
    (A.chartEquiv i).symm p = A.chartSymm i p := rfl

/-- **DERIVED (item 36).**  Projection compatibility: the first coordinate of the chart is
the base point. -/
theorem chartFun_fst (i : ι) (x : A.dom i) : ((A.chartFun i x).1 : B) = totalBase C x.1 := rfl

/-! ### Admissible topologies -/

/-- **NEWLY DEFINED (items 30, 35, 47), principal.**  A topology on the total carrier is
*admissible* for the atlas when the base projection is continuous and each chart is a
homeomorphism onto the local product.  This is the exact notion of "correct total-space
topology" used in Task XXVII. -/
structure IsAdmissible [TopologicalSpace (Total C)] : Prop where
  /-- The base projection is continuous. -/
  continuous_base : Continuous (totalBase C)
  /-- Each chart map is continuous. -/
  continuous_chart : ∀ i, Continuous (A.chartFun i)
  /-- Each inverse chart map is continuous. -/
  continuous_chartSymm : ∀ i, Continuous (A.chartSymm i)

variable {A}

/-- **DERIVED, principal.**  For an admissible topology each chart is a genuine
homeomorphism onto the local product. -/
def IsAdmissible.chartHomeo [TopologicalSpace (Total C)] (h : A.IsAdmissible) (i : ι) :
    A.dom i ≃ₜ (A.U i) × M where
  toEquiv := A.chartEquiv i
  continuous_toFun := h.continuous_chart i
  continuous_invFun := h.continuous_chartSymm i

theorem IsAdmissible.isOpen_dom [TopologicalSpace (Total C)] (h : A.IsAdmissible) (i : ι) :
    IsOpen (A.dom i) :=
  h.continuous_base.isOpen_preimage _ (A.isOpen_U i)

theorem IsAdmissible.continuous_psi [TopologicalSpace (Total C)] (h : A.IsAdmissible)
    (i : ι) : Continuous (A.psi i) :=
  continuous_subtype_val.comp (h.continuous_chartSymm i)

variable (A)

/-! ### The atlas-generated topology (item 46) -/

/-- **NEWLY DEFINED (item 46), principal.**  The topology generated by the atlas: a subset of
the total carrier is open exactly when its preimage in every local product chart is open.
This is *not* the sigma topology (item 19); see the negative controls. -/
def top : TopologicalSpace (Total C) :=
  ⨆ i : ι, TopologicalSpace.coinduced (A.psi i) inferInstance

theorem isOpen_top_iff (S : Set (Total C)) :
    IsOpen[A.top] S ↔ ∀ i, IsOpen (A.psi i ⁻¹' S) := by
  rw [top, isOpen_iSup_iff]
  rfl

theorem continuous_psi_top (i : ι) : letI := A.top; Continuous (A.psi i) := by
  letI := A.top
  rw [continuous_iff_coinduced_le]
  exact le_iSup (fun i => TopologicalSpace.coinduced (A.psi i) inferInstance) i

theorem isOpen_top_dom (i : ι) : IsOpen[A.top] (A.dom i) := by
  rw [isOpen_top_iff]
  intro j
  have h : A.psi j ⁻¹' A.dom i = (fun p : (A.U j) × M => (p.1 : B)) ⁻¹' A.U i := rfl
  rw [h]
  exact (A.isOpen_U i).preimage (continuous_subtype_val.comp continuous_fst)

theorem continuous_top_base : letI := A.top; Continuous (totalBase C) := by
  letI := A.top
  rw [continuous_def]
  intro W hW
  rw [isOpen_top_iff]
  intro i
  exact hW.preimage (continuous_subtype_val.comp continuous_fst)

/-- Continuity into a product with a subtype factor is tested in the ambient product. -/
theorem continuous_into_subtype_prod {X : Type*} [TopologicalSpace X] {S : Set B}
    (f : X → S × M) (hf : Continuous fun x => (((f x).1 : B), (f x).2)) : Continuous f :=
  Continuous.prodMk (hf.fst.subtype_mk fun x => (f x).1.2) hf.snd

theorem continuous_top_chartFun (i : ι) : letI := A.top; Continuous (A.chartFun i) := by
  letI := A.top
  refine continuous_into_subtype_prod _ ?_
  rw [continuous_def]
  intro W₀ hW₀
  set T : Set (Total C) :=
    {x : Total C | ∃ h : totalBase C x ∈ A.U i,
      (totalBase C x, A.chart i ⟨totalBase C x, h⟩ x.2) ∈ W₀} with hT
  have hpre : (fun x : A.dom i => ((totalBase C x.1 : B),
      A.chart i ⟨totalBase C x.1, x.2⟩ x.1.2)) ⁻¹' W₀ = Subtype.val ⁻¹' T := by
    ext x
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  have hgoal : (fun x : A.dom i => (((A.chartFun i x).1 : B), (A.chartFun i x).2)) ⁻¹' W₀
      = Subtype.val ⁻¹' T := hpre
  rw [hgoal]
  refine IsOpen.preimage continuous_subtype_val ?_
  rw [isOpen_top_iff]
  intro j
  have hset : A.psi j ⁻¹' T
      = {p : (A.U j) × M | (p.1 : B) ∈ A.U i}
        ∩ (fun p : (A.U j) × M => ((p.1 : B), ovMap A.U A.chart j i p)) ⁻¹' W₀ := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h, hx⟩
      exact ⟨h, by rwa [ovMap_apply (chart := A.chart) p h]⟩
    · rintro ⟨h, hx⟩
      refine ⟨h, ?_⟩
      rwa [ovMap_apply (chart := A.chart) p h] at hx
  rw [hset]
  refine ContinuousOn.isOpen_inter_preimage ?_ ?_ hW₀
  · exact ContinuousOn.prodMk (continuous_subtype_val.comp continuous_fst).continuousOn
      (A.continuousOn_overlap j i)
  · exact (A.isOpen_U i).preimage (continuous_subtype_val.comp continuous_fst)

theorem continuous_top_chartSymm (i : ι) : letI := A.top; Continuous (A.chartSymm i) := by
  letI := A.top
  exact Continuous.subtype_mk (A.continuous_psi_top i) _

/-- **DERIVED (item 47), principal.**  Existence: the atlas-generated topology is admissible.
The base projection is continuous, and every chart of the atlas is a homeomorphism onto its
local product by construction. -/
theorem top_isAdmissible : letI := A.top; A.IsAdmissible := by
  letI := A.top
  exact
    { continuous_base := A.continuous_top_base
      continuous_chart := A.continuous_top_chartFun
      continuous_chartSymm := A.continuous_top_chartSymm }

/-- **DERIVED (item 48), principal.**  Uniqueness: *any* topology on the total carrier for
which the base projection is continuous and all atlas charts are homeomorphisms equals the
atlas-generated topology. -/
theorem IsAdmissible.eq_top {τ : TopologicalSpace (Total C)}
    (h : @IsAdmissible _ _ _ _ _ _ A τ) : τ = A.top := by
  letI := τ
  refine TopologicalSpace.ext_iff.2 fun S => ⟨fun hS => ?_, fun hS => ?_⟩
  · rw [isOpen_top_iff]
    exact fun i => hS.preimage (h.continuous_psi i)
  · rw [isOpen_top_iff] at hS
    have hcover : S = ⋃ i, S ∩ A.dom i := by
      rw [← Set.inter_iUnion, A.iUnion_dom, Set.inter_univ]
    rw [hcover]
    refine isOpen_iUnion fun i => ?_
    have h0 : A.chartSymm i ⁻¹' ((Subtype.val : A.dom i → Total C) ⁻¹' S)
        = A.psi i ⁻¹' S := rfl
    have hsub : IsOpen ((Subtype.val : A.dom i → Total C) ⁻¹' S) := by
      refine ((h.chartHomeo i).symm.isOpen_preimage).1 ?_
      rw [show ((h.chartHomeo i).symm ⁻¹' ((Subtype.val : A.dom i → Total C) ⁻¹' S))
        = A.psi i ⁻¹' S from h0]
      exact hS i
    have himg := (h.isOpen_dom i).isOpenMap_subtype_val _ hsub
    rwa [Subtype.image_preimage_coe, Set.inter_comm] at himg

/-- **DERIVED (item 48).**  Consequently an admissible topology is unique. -/
theorem admissible_unique {τ₁ τ₂ : TopologicalSpace (Total C)}
    (h₁ : @IsAdmissible _ _ _ _ _ _ A τ₁) (h₂ : @IsAdmissible _ _ _ _ _ _ A τ₂) : τ₁ = τ₂ :=
  Eq.trans (IsAdmissible.eq_top A h₁) (IsAdmissible.eq_top A h₂).symm

end ChartAtlas

end NullSectorTask27
