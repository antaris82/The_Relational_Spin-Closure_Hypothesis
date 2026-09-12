import RequestProject.Spine.GoodCover.GoodCover
import RequestProject.Spine.Geometry.TangentInstance

/-!
# Task 7, WP2/WP4 : what the Task-4 manifold class really supplies

WP2 asks which topological properties the manifolds of Task 4 have, and WP4 asks whether such
manifolds admit *suitable* (good) covers.  Task 4 assumes exactly

```
  [TopologicalSpace M] [ChartedSpace LorentzCarrier M]        (+ [IsManifold carrierModel ⊤ M])
```

with `LorentzCarrier = ℝ × (Fin 3 → ℝ)`, a four-dimensional real normed space.  **No**
Hausdorff, second-countability, paracompactness, metrisability or Riemannian-metric
hypothesis is present, and this module does not add any.

What *is* derivable from the charted structure alone is proved here:

* `SpineTop.stronglyLocallyContractibleSpace_of_normed` — a real normed space has a
  neighbourhood basis of contractible sets (open balls are convex, hence contractible);
* `SpineTop.stronglyLocallyContractibleSpace_of_openCover` — strong local contractibility is a
  local property;
* `SpineTop.exists_contractible_open_nhds` — **arbitrarily fine contractible open
  neighbourhoods**: in a space charted on a normed space, every neighbourhood of every point
  contains a contractible *open* neighbourhood (the chart preimage of a small ball);
* `SpineTop.stronglyLocallyContractibleSpace_of_chartedSpace` — such a space is strongly
  locally contractible;
* `SpineTop.exists_contractible_refinement` — every open cover of such a space is refined by a
  cover consisting of contractible open sets;
* `LorentzFrames.contractibleCover` — the resulting `CechCover M M` for a Task-4 manifold, and
  `LorentzFrames.contractibleCover_contractible`, that each of its members is contractible.

## What is *not* proved (WP4, honest classification)

`GoodCoverZ2.IsGoodCover` requires **every nonempty finite intersection** to be contractible.
A cover by contractible chart-balls does *not* satisfy this: intersections of chart balls need
not even be connected.  The classical route to genuine good covers is Riemannian — a complete
metric, geodesically convex balls (Whitehead), and the fact that intersections of geodesically
convex sets are geodesically convex.  In pinned Mathlib there is no Riemannian metric on a
manifold, no exponential map, no injectivity radius and no convexity radius, so that route is
unavailable, and no other construction of good covers exists in the library.

Consequently Task 7 follows **Outcome C** of WP4: the downstream theory is developed
*parametrically* under the hypothesis `IsGoodCover 𝓤.U` (see
`RequestProject.Spine.GoodCover.Constancy`), the existence question is recorded as the
predicate `SpineTop.HasGoodCover`, and it is left unproved rather than assumed.  The
predicate is not vacuous: `SpineTop.hasGoodCover_of_contractible` exhibits good covers of
contractible spaces (in particular of the model space `LorentzCarrier` itself).
-/

noncomputable section

namespace SpineTop

open Metric Set Topology Filter GoodCoverZ2 CechZ2

universe w t

/-! ## Strong local contractibility -/

/-- A real normed space has a neighbourhood basis of contractible sets: the open balls, which
are convex. -/
theorem stronglyLocallyContractibleSpace_of_normed (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : StronglyLocallyContractibleSpace E :=
  .of_bases (fun x => Metric.nhds_basis_ball (x := x))
    (fun _ _ hr => Metric.contractibleSpace_ball hr)

/-- Strong local contractibility is a **local** property: a space covered by open subspaces
that are strongly locally contractible is itself strongly locally contractible. -/
theorem stronglyLocallyContractibleSpace_of_openCover {X : Type w} [TopologicalSpace X]
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ StronglyLocallyContractibleSpace U) :
    StronglyLocallyContractibleSpace X where
  contractible_basis x := by
    obtain ⟨U, hU, hxU, hSLC⟩ := h x
    haveI := hSLC
    rw [Filter.hasBasis_self]
    intro t ht
    have hemb : Topology.IsOpenEmbedding ((↑) : U → X) := hU.isOpenEmbedding_subtypeVal
    have hx' : (Subtype.val ⁻¹' t : Set U) ∈ 𝓝 (⟨x, hxU⟩ : U) :=
      continuousAt_subtype_val.preimage_mem_nhds ht
    obtain ⟨s', hs'mem, hs'c, hs'sub⟩ :=
      (Filter.hasBasis_self.1 (contractible_basis (⟨x, hxU⟩ : U))) _ hx'
    refine ⟨Subtype.val '' s', ?_, ?_, ?_⟩
    · have hmap := hemb.map_nhds_eq (⟨x, hxU⟩ : U)
      simp only at hmap
      rw [← hmap]
      exact Filter.image_mem_map hs'mem
    · haveI := hs'c
      exact ((hemb.toIsEmbedding.homeomorphImage s').symm).contractibleSpace
    · rintro _ ⟨y, hy, rfl⟩
      exact hs'sub hy

/-! ## Arbitrarily fine contractible open neighbourhoods on a charted space -/

/-- **WP2, principal.**  On a space charted on a real normed space, every point of every open
set has a **contractible open** neighbourhood inside that set: the chart preimage of a small
ball.  No metric, paracompactness or separation hypothesis on `M` is used. -/
theorem exists_contractible_open_nhds (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M] {V : Set M} (hV : IsOpen V) {x : M}
    (hx : x ∈ V) : ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ ContractibleSpace W := by
  set e := chartAt E x with he
  have hxs : x ∈ e.source := mem_chart_source E x
  have hO : IsOpen (e '' (e.source ∩ V)) := e.isOpen_image_source_inter hV
  have hmem : e x ∈ e '' (e.source ∩ V) := ⟨x, ⟨hxs, hx⟩, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO _ hmem
  refine ⟨e.source ∩ e ⁻¹' (ball (e x) r), ?_, ?_, ?_, ?_⟩
  · exact e.isOpen_inter_preimage Metric.isOpen_ball
  · exact ⟨hxs, by simpa using hr⟩
  · rintro y ⟨hys, hyb⟩
    obtain ⟨z, ⟨hzs, hzV⟩, hz⟩ := hball hyb
    have hyz : y = z := e.injOn hys hzs hz.symm
    exact hyz ▸ hzV
  · have hsub : e.source ∩ e ⁻¹' (ball (e x) r) ⊆ e.source := inter_subset_left
    have himg : e '' (e.source ∩ e ⁻¹' (ball (e x) r)) = ball (e x) r := by
      apply Subset.antisymm
      · rintro _ ⟨y, ⟨_, hyb⟩, rfl⟩; exact hyb
      · intro b hb
        obtain ⟨z, ⟨hzs, _⟩, hz⟩ := hball hb
        refine ⟨z, ⟨hzs, ?_⟩, hz⟩
        show e z ∈ ball (e x) r
        rw [hz]; exact hb
    haveI := Metric.contractibleSpace_ball (x := e x) hr
    exact (e.homeomorphOfImageSubsetSource hsub himg).contractibleSpace

/-- A space charted on a real normed space is strongly locally contractible. -/
theorem stronglyLocallyContractibleSpace_of_chartedSpace (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] {M : Type w} [TopologicalSpace M] [ChartedSpace E M] :
    StronglyLocallyContractibleSpace M := by
  haveI := stronglyLocallyContractibleSpace_of_normed E
  refine stronglyLocallyContractibleSpace_of_openCover fun x => ?_
  exact ⟨(chartAt E x).source, (chartAt E x).open_source, mem_chart_source E x,
    (chartAt E x).isOpenEmbedding_restrict.stronglyLocallyContractibleSpace⟩

/-- **WP2/WP4.**  Every open cover of a space charted on a real normed space is refined by a
cover consisting of *contractible open* sets, indexed by the points of the space.  This is the
strongest cover statement the Task-4 hypotheses support. -/
theorem exists_contractible_refinement (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M] {ι : Type t} (V : ι → Set M)
    (hVo : ∀ i, IsOpen (V i)) (hVc : ∀ x : M, ∃ i, x ∈ V i) :
    ∃ W : M → Set M, (∀ x, IsOpen (W x)) ∧ (∀ x, x ∈ W x) ∧
      (∀ x, ContractibleSpace (W x)) ∧ (∀ x, ∃ i, W x ⊆ V i) := by
  classical
  choose i hi using hVc
  choose W hWo hxW hWsub hWc using fun x : M =>
    exists_contractible_open_nhds E (hVo (i x)) (hi x)
  exact ⟨W, hWo, hxW, hWc, fun x => ⟨i x, hWsub x⟩⟩

/-! ## The good-cover existence predicate -/

/-- **The WP4 existence question, as a predicate.**  `HasGoodCover X` says that `X` admits a
cover all of whose nonempty finite intersections are contractible.  It is *stated*, never
assumed and never proved, for the Task-4 manifold class; the downstream theory takes an
`IsGoodCover` hypothesis instead. -/
def HasGoodCover (X : Type w) [TopologicalSpace X] : Prop :=
  ∃ (ι : Type w) (U : ι → Set X), IsGoodCover U

/-- The predicate is not vacuous: a contractible space has a good cover, namely the
one-element cover by the whole space. -/
theorem hasGoodCover_of_contractible (X : Type w) [TopologicalSpace X] [ContractibleSpace X] :
    HasGoodCover X := by
  classical
  refine ⟨PUnit.{w + 1}, fun _ => Set.univ, ?_, ?_, ?_⟩
  · intro _; exact isOpen_univ
  · intro x; exact ⟨PUnit.unit, Set.mem_univ x⟩
  · intro n σ _
    have huniv : inter (fun _ : PUnit.{w + 1} => (Set.univ : Set X)) σ = Set.univ := by
      ext x; simp [inter]
    rw [huniv]
    exact (Homeomorph.Set.univ X).contractibleSpace

/-- In particular the model space of the Task-4 manifolds has a good cover. -/
theorem hasGoodCover_carrier : HasGoodCover SpinCore.LorentzCarrier :=
  hasGoodCover_of_contractible _

end SpineTop

namespace LorentzFrames

open SpineTop CechSpinLift SpinCore

universe u

variable (M : Type u) [TopologicalSpace M] [ChartedSpace LorentzCarrier M]

variable {M}

/-- A chosen contractible open neighbourhood of a point of a Task-4 manifold: the chart
preimage of a small ball. -/
def contractibleNhd (x : M) : Set M :=
  Classical.choose
    (exists_contractible_open_nhds LorentzCarrier (isOpen_univ (X := M)) (Set.mem_univ x))

theorem contractibleNhd_spec (x : M) :
    IsOpen (contractibleNhd x) ∧ x ∈ contractibleNhd x ∧ contractibleNhd x ⊆ Set.univ ∧
      ContractibleSpace (contractibleNhd x) :=
  Classical.choose_spec
    (exists_contractible_open_nhds LorentzCarrier (isOpen_univ (X := M)) (Set.mem_univ x))

variable (M)

/-- **The contractible chart-ball cover of a Task-4 manifold**, indexed by the points of `M`:
around each point the chart preimage of a small ball.  Every member is contractible.

This is *not* claimed to be a good cover: its finite intersections are not controlled. -/
def contractibleCover : CechCover M M :=
  ⟨contractibleNhd, fun x => (contractibleNhd_spec x).1,
    fun x => ⟨x, (contractibleNhd_spec x).2.1⟩⟩

@[simp] theorem contractibleCover_U (x : M) : (contractibleCover M).U x = contractibleNhd x :=
  rfl

/-- Each member of the contractible chart-ball cover is contractible. -/
theorem contractibleCover_contractible (x : M) :
    ContractibleSpace ((contractibleCover M).U x) :=
  (contractibleNhd_spec x).2.2.2

end LorentzFrames
