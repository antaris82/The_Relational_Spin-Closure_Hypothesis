import RequestProject.Spine.Emergent.BaseGluing

/-!
# Spine / Emergent : reconstruction of the base from the gluing primitive

**Third module of the manifold-emergence layer (Task 32, §§8–9).**

Given a base-gluing datum `B : BaseGluingData V ι` — the explicit base-gluing primitive
isolated in `RequestProject.Spine.Emergent.BaseGluing` — this module constructs the candidate base

`X₀ = ⨿ i, D i`,  `Space B = X₀ / ∼`

with the quotient topology, and proves, in this order:

* `BaseGluingData.isOpenMap_mk` — the quotient map is **open** (this is where the openness of
  the incidence domains and the continuity of the identification maps are used);
* `BaseGluingData.isOpenEmbedding_chart` — every local piece embeds as an **open** subset;
* `BaseGluingData.chartHomeomorph`, `BaseGluingData.chartedSpace` — the emergent base is
  locally homeomorphic to open subsets of the local model, packaged as a genuine
  `ChartedSpace V (Space B)`;
* `BaseGluingData.t2Space_of_closedGluingGraph` — Hausdorffness, under the explicit and
  necessary extra condition that the gluing graph is closed (it does **not** follow from the
  gluing laws: non-Hausdorff quotients such as the line with two origins satisfy all of
  them);
* `BaseGluingData.secondCountableTopology_space` — second countability, for a countable
  index type over a second-countable local model;
* `BaseGluingData.emergentManifoldCertificate` — the packaged statement.

Nothing here mentions a Spin structure, an obstruction class, a connection, transport,
holonomy or curvature, and the import closure of this module contains no Čech, obstruction
or frame-geometry module.
-/

noncomputable section

namespace EmergentBase

universe u t

namespace BaseGluingData

variable {V : Type u} [TopologicalSpace V] {ι : Type t} (B : BaseGluingData V ι)

/-! ## The emergent base -/

/-- **NEWLY DEFINED (Task 32), principal.**  The emergent base: the tagged disjoint union of
the local pieces modulo the gluing relation, with the quotient topology. -/
def Space (B : BaseGluingData V ι) : Type _ := Quotient B.setoid

instance : TopologicalSpace (Space B) :=
  inferInstanceAs (TopologicalSpace (Quotient B.setoid))

/-- The quotient map onto the emergent base. -/
def quotMk (B : BaseGluingData V ι) (p : Total B) : Space B := Quotient.mk B.setoid p

theorem mk_eq_mk_iff {p q : Total B} : B.quotMk p = B.quotMk q ↔ B.Rel p q :=
  Quotient.eq (r := B.setoid)

theorem mk_surjective : Function.Surjective B.quotMk := Quotient.mk_surjective

theorem continuous_mk : Continuous B.quotMk := continuous_quot_mk

theorem isOpen_space_iff {S : Set (Space B)} : IsOpen S ↔ IsOpen (B.quotMk ⁻¹' S) := Iff.rfl

/-- **DERIVED (Task 32), principal.**  The quotient map onto the emergent base is an **open**
map.  The proof uses exactly the two topological fields of the primitive: the incidence
domains are open and the identification maps are continuous. -/
theorem isOpenMap_mk : IsOpenMap B.quotMk := by
  intro T hT
  rw [isOpen_space_iff, isOpen_sigma_iff]
  intro j
  have hslice : (Sigma.mk j ⁻¹' (B.quotMk ⁻¹' (B.quotMk '' T)))
      = ⋃ i : ι, (Subtype.val ⁻¹'
          (B.W j i ∩ B.φ j i ⁻¹' (Classical.choose (isOpen_induced_iff.1
            (hT.preimage (continuous_sigmaMk (i := i))))))) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨p, hpT, hp⟩
      refine ⟨p.1, ?_, ?_⟩
      · exact (B.rel_symm ((B.mk_eq_mk_iff).1 hp)).1
      · have hspec := (Classical.choose_spec (isOpen_induced_iff.1
          (hT.preimage (continuous_sigmaMk (i := p.1))))).2
        have hx : p.2 ∈ Sigma.mk p.1 ⁻¹' T := by
          simpa using (by simpa using hpT : (⟨p.1, p.2⟩ : Total B) ∈ T)
        have := hspec ▸ hx
        have hφ : B.φ j p.1 (y : V) = (p.2 : V) := (B.rel_symm ((B.mk_eq_mk_iff).1 hp)).2
        rw [hφ]
        exact this
    · rintro ⟨i, hyW, hyS⟩
      have hspec := (Classical.choose_spec (isOpen_induced_iff.1
        (hT.preimage (continuous_sigmaMk (i := i))))).2
      have hmem : B.φ j i (y : V) ∈ B.W i j := B.φ_mapsTo j i hyW
      refine ⟨⟨i, ⟨B.φ j i (y : V), B.W_subset i j hmem⟩⟩, ?_, ?_⟩
      · have : (⟨B.φ j i (y : V), B.W_subset i j hmem⟩ : (B.D i : Set V))
            ∈ Sigma.mk i ⁻¹' T := by
          rw [← hspec]
          exact hyS
        simpa using this
      · refine (B.mk_eq_mk_iff).2 ?_
        exact ⟨hmem, B.φ_inv j i (y : V) hyW⟩
  rw [hslice]
  refine isOpen_iUnion fun i => ?_
  exact IsOpen.preimage continuous_subtype_val
    ((B.continuousOn_φ j i).isOpen_inter_preimage (B.isOpen_W j i)
      (Classical.choose_spec (isOpen_induced_iff.1
        (hT.preimage (continuous_sigmaMk (i := i))))).1)

theorem isQuotientMap_mk : Topology.IsQuotientMap B.quotMk :=
  B.isOpenMap_mk.isQuotientMap B.continuous_mk B.mk_surjective

/-! ## The emergent charts -/

/-- The chart map of the piece `i`: the local domain `D i` mapped into the emergent base. -/
def chart (B : BaseGluingData V ι) (i : ι) (x : (B.D i : Set V)) : Space B := B.quotMk ⟨i, x⟩

theorem continuous_chart (i : ι) : Continuous (B.chart i) :=
  B.continuous_mk.comp continuous_sigmaMk

theorem injective_chart (i : ι) : Function.Injective (B.chart i) := fun _ _ h =>
  B.rel_same_index ((B.mk_eq_mk_iff).1 h)

theorem isOpenMap_chart (i : ι) : IsOpenMap (B.chart i) :=
  B.isOpenMap_mk.comp isOpenMap_sigmaMk

theorem isOpenEmbedding_chart (i : ι) : Topology.IsOpenEmbedding (B.chart i) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap (B.continuous_chart i)
    (B.injective_chart i) (B.isOpenMap_chart i)

/-- The image of the piece `i` in the emergent base. -/
def chartRange (B : BaseGluingData V ι) (i : ι) : Set (Space B) := Set.range (B.chart i)

theorem isOpen_chartRange (i : ι) : IsOpen (B.chartRange i) :=
  (B.isOpenEmbedding_chart i).isOpen_range

/-- **DERIVED (Task 32).**  The chart images cover the emergent base. -/
theorem iUnion_chartRange : (⋃ i, B.chartRange i) = Set.univ := by
  ext p
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  obtain ⟨q, rfl⟩ := B.mk_surjective p
  exact Set.mem_iUnion.2 ⟨q.1, ⟨q.2, rfl⟩⟩

/-- **DERIVED (Task 32), principal.**  Every local piece is homeomorphic to its (open) image
in the emergent base: the base is locally a copy of an open subset of the local model. -/
def chartHomeomorph (B : BaseGluingData V ι) (i : ι) :
    (B.D i : Set V) ≃ₜ (B.chartRange i : Set (Space B)) :=
  (B.isOpenEmbedding_chart i).isEmbedding.toHomeomorph

/-! ## The charted-space packaging -/

/-- The chart of the emergent base attached to a point, as an `OpenPartialHomeomorph` into
the local model: its source is the (open) image of the piece containing a chosen
representative of the point, and its target is that piece. -/
def chartOfPoint (B : BaseGluingData V ι) (p : Space B) : OpenPartialHomeomorph (Space B) V :=
  haveI : Nonempty ((B.D (Quotient.out (s := B.setoid) p).1 : Set V)) :=
    ⟨(Quotient.out (s := B.setoid) p).2⟩
  ((B.isOpenEmbedding_chart (Quotient.out (s := B.setoid) p).1).toOpenPartialHomeomorph
      _).symm.trans
    (((B.isOpen_D (Quotient.out (s := B.setoid) p).1).isOpenEmbedding_subtypeVal
      ).toOpenPartialHomeomorph _)

theorem mem_source_chartOfPoint (p : Space B) : p ∈ (B.chartOfPoint p).source := by
  have hp : B.quotMk (Quotient.out (s := B.setoid) p) = p := Quotient.out_eq (s := B.setoid) p
  have hrange : p ∈ Set.range (B.chart (Quotient.out (s := B.setoid) p).1) :=
    ⟨(Quotient.out (s := B.setoid) p).2, hp⟩
  simpa [chartOfPoint, Topology.IsOpenEmbedding.toOpenPartialHomeomorph,
    OpenPartialHomeomorph.trans] using hrange

/-- **DERIVED (Task 32), PRINCIPAL — the emergent base is a charted space over the local
model.**  The charts are the local pieces of the primitive; nothing is supplied from
outside. -/
def chartedSpace (B : BaseGluingData V ι) : ChartedSpace V (Space B) where
  atlas := Set.range B.chartOfPoint
  chartAt := B.chartOfPoint
  mem_chart_source := B.mem_source_chartOfPoint
  chart_mem_atlas p := ⟨p, rfl⟩

/-! ## Hausdorffness -/

/-- **NEWLY DEFINED (Task 32), the explicit separation condition.**  The gluing graph is
closed in `X₀ × X₀`.  This condition is *not* implied by the gluing laws — the line with two
origins is a counterexample — and it is exactly what Hausdorffness of the quotient needs. -/
def ClosedGluingGraph (B : BaseGluingData V ι) : Prop :=
  IsClosed {p : Total B × Total B | B.Rel p.1 p.2}

/-- **DERIVED (Task 32).**  With the closed-graph condition the emergent base is Hausdorff.
The proof uses that the quotient map is open. -/
theorem t2Space_of_closedGluingGraph (h : B.ClosedGluingGraph) : T2Space (Space B) := by
  rw [t2_iff_isClosed_diagonal]
  have hq : Topology.IsQuotientMap (Prod.map B.quotMk B.quotMk) :=
    (B.isOpenMap_mk.prodMap B.isOpenMap_mk).isQuotientMap
      (B.continuous_mk.prodMap B.continuous_mk)
      (B.mk_surjective.prodMap B.mk_surjective)
  rw [← hq.isClosed_preimage]
  have hpre : Prod.map B.quotMk B.quotMk ⁻¹' Set.diagonal (Space B)
      = {p : Total B × Total B | B.Rel p.1 p.2} := by
    ext p
    exact B.mk_eq_mk_iff
  rw [hpre]
  exact h

/-! ## Second countability -/

/-- **DERIVED (Task 32).**  A countable family of pieces of a second-countable local model
glues to a second-countable base. -/
theorem secondCountableTopology_space [Countable ι] [SecondCountableTopology V] :
    SecondCountableTopology (Space B) := by
  haveI : SecondCountableTopology (Total B) :=
    inferInstanceAs (SecondCountableTopology (Σ i, (B.D i : Set V)))
  exact B.isQuotientMap_mk.secondCountableTopology B.isOpenMap_mk

/-! ## The packaged reconstruction endpoint -/

/-- **NEWLY DEFINED (Task 32), the endpoint object.**  An emergent manifold: a base-gluing
datum together with the *derived* topological-manifold structure of its quotient.  The base
is not an external parameter — it is `Space gluing`, constructed from the datum. -/
structure EmergentManifold (V : Type u) [TopologicalSpace V] (ι : Type t) where
  /-- The primitive base-gluing datum. -/
  gluing : BaseGluingData V ι
  /-- The emergent base is Hausdorff. -/
  t2 : T2Space (Space gluing)
  /-- The emergent base is second countable. -/
  secondCountable : SecondCountableTopology (Space gluing)
  /-- The emergent base is locally modelled on the local model `V`. -/
  charted : ChartedSpace V (Space gluing)

/-- **DERIVED (Task 32), PRINCIPAL — manifold reconstruction.**  From a base-gluing datum
with a closed gluing graph, over a countable index type and a second-countable local model,
the quotient is a Hausdorff, second-countable space locally homeomorphic to open subsets of
the local model: an emergent (topological) manifold. -/
def emergentManifold [Countable ι] [SecondCountableTopology V]
    (h : B.ClosedGluingGraph) : EmergentManifold V ι where
  gluing := B
  t2 := B.t2Space_of_closedGluingGraph h
  secondCountable := B.secondCountableTopology_space
  charted := B.chartedSpace

/-- **DERIVED (Task 32), the reconstruction certificate in one statement.** -/
theorem emergentManifoldCertificate [Countable ι]
    [SecondCountableTopology V] (h : B.ClosedGluingGraph) :
    T2Space (Space B) ∧ SecondCountableTopology (Space B) ∧
      Nonempty (ChartedSpace V (Space B)) ∧
      (∀ i, IsOpen (B.chartRange i)) ∧ (⋃ i, B.chartRange i) = Set.univ :=
  ⟨B.t2Space_of_closedGluingGraph h, B.secondCountableTopology_space, ⟨B.chartedSpace⟩,
    B.isOpen_chartRange, B.iUnion_chartRange⟩

end BaseGluingData

end EmergentBase

end
