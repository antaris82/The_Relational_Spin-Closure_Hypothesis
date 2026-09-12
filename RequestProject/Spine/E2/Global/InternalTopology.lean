import RequestProject.Spine.E2.Global.InternalQuotient

/-!
# Task 30, Packages F and G: the topology of the glued carrier and the chart changes

**Hard target B.**

**Route Q and Route A coincide (items 50–53).**  Only *one* topology is introduced: the
quotient topology carried by `InternalTotal T = Quotient (InternalGlueSetoid T)`, coinduced
from the disjoint union of the local products (Route Q).  It is then *proved* to be the
atlas-generated topology of Route A, i.e. the supremum of the topologies coinduced by the
local parametrizations `ipsi i` (`internalTotal_topology_eq_iSup`,
`isOpen_internalTotal_iff`).  No second topology is maintained (item 53).

**Package G (items 60–65).**  The change-of-coordinate map on an overlap,

`(b, a) ↦ (b, u_ij(b) * a)`,

is continuous (`internal_chart_change_continuous`); its inverse is the coordinate change for
the reversed transition, and the composition of two chart changes is the chart change of the
composed transition (the triple-overlap law).  This is exactly what makes the local
parametrizations *open* maps, and hence the local charts homeomorphisms (item 65).

**Package F output (items 55–58).**  Every chart

`internalBase⁻¹(U i) ≃ₜ U i × Lift`

is a homeomorphism, the base projection is continuous, the preimage of every chart domain is
open, and the topology is the unique one with these chart properties.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask30

open NullSectorTask28 NullSectorTask29 Topology

universe u v w t

section Topology

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {P : InternalProjection L G} {S : TransitionSystem B ι G}
  (T : CompatibleContinuousInternalTransitions P S)

/-! ## Route Q: the quotient topology, and its Route A characterization -/

/-- **PACKAGE F (Route Q).**  The quotient map is continuous. -/
theorem continuous_iq : Continuous (iq T) := continuous_quot_mk

/-- **PACKAGE F (Route Q).**  The quotient map is a quotient map. -/
theorem isQuotientMap_iq : IsQuotientMap (iq T) := ⟨iq_surjective T, rfl⟩

/-- **PACKAGE F.**  A name for the topology carried by the glued carrier: the quotient
topology coinduced from the disjoint union of the local products (Route Q). -/
abbrev internalTop : TopologicalSpace (InternalTotal T) := inferInstance

/-- **PACKAGE F.**  The local parametrizations are continuous. -/
theorem continuous_ipsi (i : ι) : Continuous (ipsi T i) :=
  (continuous_iq T).comp continuous_sigmaMk

/-- **PACKAGE F (items 50–52), principal — Route Q = Route A, opens version.**  A subset of
the glued carrier is open exactly when its preimage in every local product is open. -/
theorem isOpen_internalTotal_iff (V : Set (InternalTotal T)) :
    IsOpen V ↔ ∀ i, IsOpen (ipsi T i ⁻¹' V) := by
  rw [← (isQuotientMap_iq T).isOpen_preimage, isOpen_sigma_iff]
  rfl

/-- **PACKAGE F (items 50–52), principal — Route Q = Route A, topologies version.**  The
quotient topology *is* the atlas-generated topology of the local parametrizations. -/
theorem internalTotal_topology_eq_iSup :
    (inferInstance : TopologicalSpace (InternalTotal T))
      = ⨆ i : ι, TopologicalSpace.coinduced (ipsi T i) inferInstance := by
  ext V
  rw [isOpen_internalTotal_iff, isOpen_iSup_iff]
  rfl

/-- **PACKAGE F.**  Mapping out of the glued carrier: continuity is chartwise. -/
theorem continuous_internalTotal_iff {X : Type*} [TopologicalSpace X]
    (f : InternalTotal T → X) : Continuous f ↔ ∀ i, Continuous (f ∘ ipsi T i) := by
  rw [(isQuotientMap_iq T).continuous_iff, continuous_sigma_iff]
  rfl

/-! ## Package G — the chart changes -/

/-- **PACKAGE G (item 60).**  The domain of the `i → j` change of coordinates. -/
def chgDom (S : TransitionSystem B ι G) (L : Type w) (i j : ι) : Set (↥(S.U i) × L) :=
  {p | (p.1 : B) ∈ S.U j}

omit [Group L] [IsTopologicalGroup L] in
theorem isOpen_chgDom (i j : ι) : IsOpen (chgDom S L i j) :=
  (S.isOpen_U j).preimage (continuous_subtype_val.comp continuous_fst)

omit [Group L] [TopologicalSpace L] [IsTopologicalGroup L] in
theorem mem_chgDom {i j : ι} {p : ↥(S.U i) × L} : p ∈ chgDom S L i j ↔ (p.1 : B) ∈ S.U j :=
  Iff.rfl

/-- **PACKAGE G (item 60), principal definition.**  The change of coordinates between two
charts, in the derived convention: `(b, a) ↦ (b, u_ij(b) * a)`. -/
def chgMap (i j : ι) (p : ↥(chgDom S L i j)) : ↥(S.U j) × L :=
  (⟨(p.1.1 : B), p.2⟩, uu T i j (p.1.1 : B) p.1.1.2 p.2 * p.1.2)

/-- **PACKAGE G (items 61, 64), REQUIRED ENDPOINT `internal_chart_change_continuous`.**  The
change-of-coordinate map on an overlap is continuous. -/
theorem internal_chart_change_continuous (i j : ι) : Continuous (chgMap T i j) := by
  have hval : Continuous fun p : ↥(chgDom S L i j) => ((p.1.1 : B)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
  have hpair : Continuous fun p : ↥(chgDom S L i j) =>
      (⟨(p.1.1 : B), p.1.1.2, p.2⟩ : ↥(S.U i ∩ S.U j)) := hval.subtype_mk _
  have huu : Continuous fun p : ↥(chgDom S L i j) =>
      uu T i j (p.1.1 : B) p.1.1.2 p.2 := (T.continuous_v i j).comp hpair
  have hlast : Continuous fun p : ↥(chgDom S L i j) => (p.1.2 : L) :=
    continuous_snd.comp continuous_subtype_val
  exact (hval.subtype_mk _).prodMk (huu.mul hlast)

/-- **PACKAGE G.**  The change of coordinates is compatible with the gluing: it describes the
same point of the glued carrier. -/
theorem ipsi_chgMap (i j : ι) (p : ↥(chgDom S L i j)) :
    ipsi T j (chgMap T i j p) = ipsi T i p.1 :=
  ipsi_trans T i j (p.1.1 : B) p.1.1.2 p.2 p.1.2

/-- **PACKAGE G (item 62), principal.**  The inverse of a chart change is the chart change of
the reversed transition. -/
theorem chgMap_chgMap (i j : ι) (p : ↥(chgDom S L i j))
    (h : chgMap T i j p ∈ chgDom S L j i) :
    chgMap T j i ⟨chgMap T i j p, h⟩ = p.1 := by
  refine Prod.ext (Subtype.ext rfl) ?_
  show uu T j i (p.1.1 : B) p.2 p.1.1.2 * (uu T i j (p.1.1 : B) p.1.1.2 p.2 * p.1.2) = p.1.2
  rw [uu_symm T i j (p.1.1 : B) p.1.1.2 p.2, inv_mul_cancel_left]

/-- **PACKAGE G (item 63), principal.**  The composition of two chart changes agrees with the
chart change given by the triple-overlap law. -/
theorem chgMap_comp (i j k : ι) (p : ↥(chgDom S L i j)) (hk : (p.1.1 : B) ∈ S.U k)
    (h : chgMap T i j p ∈ chgDom S L j k) (h' : p.1 ∈ chgDom S L i k) :
    chgMap T j k ⟨chgMap T i j p, h⟩ = chgMap T i k ⟨p.1, h'⟩ := by
  refine Prod.ext (Subtype.ext rfl) ?_
  show uu T j k (p.1.1 : B) p.2 hk * (uu T i j (p.1.1 : B) p.1.1.2 p.2 * p.1.2)
      = uu T i k (p.1.1 : B) p.1.1.2 hk * p.1.2
  rw [← mul_assoc, uu_trans T i j k (p.1.1 : B) p.1.1.2 p.2 hk]

/-! ## Openness of the local parametrizations, and the chart homeomorphisms -/

theorem ipsi_preimage_image (i j : ι) (W : Set (↥(S.U j) × L)) :
    ipsi T i ⁻¹' (ipsi T j '' W) = Subtype.val '' (chgMap T i j ⁻¹' W) := by
  ext p
  constructor
  · rintro ⟨w, hwW, hw⟩
    have hrel : InternalGlueRel T (⟨j, w⟩ : InternalPre S L) ⟨i, p⟩ := (iq_eq_iff T).1 hw
    have hb : (p.1 : B) = (w.1 : B) := glueRel_pt_eq T hrel
    have hmem : p ∈ chgDom S L i j := by
      show (p.1 : B) ∈ S.U j
      rw [hb]; exact w.1.2
    have hval : chgMap T i j ⟨p, hmem⟩ = w :=
      ipsi_injective T j ((ipsi_chgMap T i j ⟨p, hmem⟩).trans hw.symm)
    exact ⟨⟨p, hmem⟩, by rw [Set.mem_preimage, hval]; exact hwW, rfl⟩
  · rintro ⟨⟨w, hmem⟩, hwW, rfl⟩
    exact ⟨chgMap T i j ⟨w, hmem⟩, hwW, ipsi_chgMap T i j ⟨w, hmem⟩⟩

/-- **PACKAGE F/G, principal.**  The local parametrizations are open maps.  This is the
topological heart of the gluing: it holds *because* the chart changes are continuous. -/
theorem isOpenMap_ipsi (j : ι) : IsOpenMap (ipsi T j) := by
  intro W hW
  rw [isOpen_internalTotal_iff]
  intro i
  rw [ipsi_preimage_image]
  exact (isOpen_chgDom (S := S) (L := L) i j).isOpenMap_subtype_val _
    (hW.preimage (internal_chart_change_continuous T i j))

/-- **PACKAGE F.**  The quotient map is an open map. -/
theorem isOpenMap_iq : IsOpenMap (iq T) := by
  intro V hV
  have hunion : iq T '' V
      = ⋃ j : ι, ipsi T j '' ((fun p : ↥(S.U j) × L => (⟨j, p⟩ : InternalPre S L)) ⁻¹' V) := by
    ext x
    constructor
    · rintro ⟨⟨j, p⟩, hp, rfl⟩
      exact Set.mem_iUnion.2 ⟨j, ⟨p, hp, rfl⟩⟩
    · rintro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
      obtain ⟨p, hp, rfl⟩ := hj
      exact ⟨⟨j, p⟩, hp, rfl⟩
  rw [hunion]
  exact isOpen_iUnion fun j =>
    isOpenMap_ipsi T j _ (hV.preimage (continuous_sigmaMk (i := j)))

/-- **PACKAGE F (items 55, 56, 57).**  The base projection is continuous. -/
theorem continuous_internalBase : Continuous (internalBase T) := by
  rw [continuous_internalTotal_iff]
  intro i
  exact continuous_subtype_val.comp continuous_fst

/-- **PACKAGE F (item 57), principal.**  The preimage of every chart domain is open. -/
theorem isOpen_internalDom (i : ι) :
    IsOpen {x : InternalTotal T | internalBase T x ∈ S.U i} :=
  (S.isOpen_U i).preimage (continuous_internalBase T)

/-- **PACKAGE F (item 55), REQUIRED ENDPOINT — the local charts are homeomorphisms.**  Over
every chart domain the glued carrier is homeomorphic to the local product `U i × Lift`. -/
noncomputable def internalChartHomeo (i : ι) :
    ↥(S.U i) × L ≃ₜ {x : InternalTotal T // internalBase T x ∈ S.U i} :=
  Equiv.toHomeomorphOfContinuousOpen (internalLocalEquiv T i).symm
    ((continuous_ipsi T i).subtype_mk _)
    (by
      intro W hW
      have himg : (internalLocalEquiv T i).symm '' W
          = Subtype.val ⁻¹' (ipsi T i '' W) := by
        ext x
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact ⟨w, hw, rfl⟩
        · rintro ⟨w, hw, hx⟩
          exact ⟨w, hw, Subtype.ext hx⟩
      rw [himg]
      exact (isOpenMap_ipsi T i W hW).preimage continuous_subtype_val)

@[simp] theorem internalChartHomeo_apply (i : ι) (p : ↥(S.U i) × L) :
    (internalChartHomeo T i p : InternalTotal T) = ipsi T i p := rfl

/-- **PACKAGE F, principal.**  The chart in the direction demanded by item 55. -/
noncomputable def internalChart (i : ι) :
    {x : InternalTotal T // internalBase T x ∈ S.U i} ≃ₜ ↥(S.U i) × L where
  toEquiv := internalLocalEquiv T i
  continuous_toFun := (internalChartHomeo T i).symm.continuous
  continuous_invFun := (continuous_ipsi T i).subtype_mk _

@[simp] theorem internalChart_apply (i : ι)
    (x : {x : InternalTotal T // internalBase T x ∈ S.U i}) :
    internalChart T i x = (⟨internalBase T x.1, x.2⟩, icoord T i x.1) := rfl

theorem continuous_icoord_on_dom (i : ι) :
    Continuous fun x : {x : InternalTotal T // internalBase T x ∈ S.U i} => icoord T i x.1 :=
  continuous_snd.comp (internalChart T i).continuous

/-- **PACKAGE F (item 58) — uniqueness relative to the charts.**  Any topology on the glued
carrier for which every local parametrization is continuous and open is the one constructed
here. -/
theorem internalTotal_topology_unique {τ : TopologicalSpace (InternalTotal T)}
    (hcont : ∀ i : ι, @Continuous (↥(S.U i) × L) (InternalTotal T) inferInstance τ (ipsi T i))
    (hopen : ∀ i : ι, @IsOpenMap (↥(S.U i) × L) (InternalTotal T) inferInstance τ (ipsi T i)) :
    τ = internalTop T := by
  have hunion : ∀ V : Set (InternalTotal T), V = ⋃ i : ι, ipsi T i '' (ipsi T i ⁻¹' V) := by
    intro V
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := iq_surjective T x
      exact ⟨y.1, y.2, hx, rfl⟩
    · rintro ⟨i, p, hp, rfl⟩
      exact hp
  refine TopologicalSpace.ext_iff.2 fun V => ⟨fun hV => ?_, fun hV => ?_⟩
  · exact (isOpen_internalTotal_iff T V).2 fun i => (hcont i).isOpen_preimage V hV
  · have hV' : ∀ i, IsOpen (ipsi T i ⁻¹' V) := (isOpen_internalTotal_iff T V).1 hV
    rw [hunion V]
    exact isOpen_iUnion fun i => hopen i _ (hV' i)

end Topology

end NullSectorTask30
