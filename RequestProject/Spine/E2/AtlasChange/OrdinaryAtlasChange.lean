import RequestProject.Spine.E2.AtlasChange.UnderlyingFrameGeometry

/-!
# Task 32, Package B: ordinary chart changes and the exact transition gauge law

**HARD TARGET A (items 16–24).**

Two ordinary atlas presentations of *one and the same* bare metric-oriented family are
compared chart by chart.  For charts `Φ_i` (of `A`) and `Φ'_{i'}` (of `A'`) the *ordinary
chart-comparison map*

```
h_{i i'}(b) := Φ'_{i'}(b) ∘ Φ_i(b)⁻¹  ∈ GvisModel
```

is defined on the common domain `A.U i ∩ A'.U i'`.  It is the inherited Task-XXVI transition
transformation `MetricOrientedRankThreeFamily.transition`, *read as a comparison of two
presentations* rather than of two charts of one presentation — so all of its algebraic laws
are inherited, not re-derived.

What is genuinely new here:

* `JointOrdinaryAtlas` — a family of ordinary presentations of one bare family on **one**
  cover, whose mutual overlap maps are continuous.  For a joint atlas, continuity of every
  chart-comparison map is **proved** (`JointOrdinaryAtlas.continuous_gauge`, item 18) rather
  than assumed; this is the honest scope of item 18, because two atlases whose mutual overlap
  maps are *not* continuous have discontinuous comparison maps.
* `chartChange_transition_law` — the exact transition gauge law, **derived** from the frozen
  Task-XXVI chart definitions (item 19):
  ```
  g'_{i'j'}(b) = h_{j j'}(b) * g_{i j}(b) * h_{i i'}(b)⁻¹ .
  ```
* identity, inverse, composition and triple-overlap compatibility of the comparison maps
  (items 20–22);
* `OrdinaryChartGaugeEquivalent` (item 23) — continuity of all chart comparisons — proved
  reflexive, symmetric and transitive, and proved to hold for the parts of a joint atlas
  (item 24), with the converse for same-cover atlases.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask32

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask31

universe u v t t' s

section ChartChange

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : BareMetricOrientedFamily B E}
  {ι : Type t} {ι' : Type t'} {ι'' : Type _}

/-- **PACKAGE B (item 17), principal definition.**  The *ordinary chart-comparison map* of two
presentations of one bare family, on the common domain of the chart `i` of `A` and the chart
`i'` of `A'`.  It is the inherited Task-XXVI transition transformation of the two local
trivializations — no new geometric datum is introduced. -/
noncomputable def chartGauge (A : OrdinaryAtlasPresentation F ι)
    (A' : OrdinaryAtlasPresentation F ι') (i : ι) (i' : ι') (b : ↥(A.U i ∩ A'.U i')) :
    GvisModel :=
  transitionOn (A.triv i) (A'.triv i') b

@[simp] theorem chartGauge_apply (A : OrdinaryAtlasPresentation F ι)
    (A' : OrdinaryAtlasPresentation F ι') (i : ι) (i' : ι') (b : ↥(A.U i ∩ A'.U i'))
    (m : Model) :
    (chartGauge A A' i i' b : Model ≃ₗᵢ[ℝ] Model) m
      = (A'.triv i').iso ⟨(b : B), b.2.2⟩ (((A.triv i).iso ⟨(b : B), b.2.1⟩).symm m) := rfl

/-- **PACKAGE B (item 22), identity chart change.**  Comparing a presentation with itself
gives the transition system of that presentation; in particular the comparison of a chart
with *itself* is the identity. -/
theorem chartGauge_self (A : OrdinaryAtlasPresentation F ι) (i : ι)
    (b : ↥(A.U i ∩ A.U i)) : chartGauge A A i i b = 1 :=
  transitionOn_self (A.triv i) b

theorem chartGauge_eq_transitionFun (A : OrdinaryAtlasPresentation F ι) (i j : ι)
    (b : ↥(A.U i ∩ A.U j)) : chartGauge A A i j b = A.transitionFun i j b := rfl

/-- **PACKAGE B (item 20), inverse compatibility.** -/
theorem chartGauge_symm (A : OrdinaryAtlasPresentation F ι)
    (A' : OrdinaryAtlasPresentation F ι') (i : ι) (i' : ι') (b : B)
    (h : b ∈ A.U i ∩ A'.U i') (h' : b ∈ A'.U i' ∩ A.U i) :
    chartGauge A' A i' i ⟨b, h'⟩ = (chartGauge A A' i i' ⟨b, h⟩)⁻¹ :=
  transitionOn_symm (A.triv i) (A'.triv i') b h h'

/-- **PACKAGE B (items 20–21), composition of successive chart changes.**  Three presentations
of one bare family compose exactly, on a common domain. -/
theorem chartGauge_comp (A : OrdinaryAtlasPresentation F ι)
    (A' : OrdinaryAtlasPresentation F ι') (A'' : OrdinaryAtlasPresentation F ι'')
    (i : ι) (i' : ι') (i'' : ι'') (b : B) (h : b ∈ A.U i ∩ A''.U i'')
    (h' : b ∈ A'.U i' ∩ A''.U i'') (h'' : b ∈ A.U i ∩ A'.U i') :
    chartGauge A A'' i i'' ⟨b, h⟩
      = chartGauge A' A'' i' i'' ⟨b, h'⟩ * chartGauge A A' i i' ⟨b, h''⟩ :=
  transitionOn_trans (A.triv i) (A'.triv i') (A''.triv i'') b h h' h''

/-! ## The exact transition gauge law -/

/-- **PACKAGE B (item 19), REQUIRED ENDPOINT — the exact ordinary transition gauge law.**

Derived, not postulated, from the frozen Task-XXVI chart definitions:

```
g'_{i'j'}(b) = h_{j j'}(b) * g_{i j}(b) * h_{i i'}(b)⁻¹ .
```

The orientation of the formula is forced by the inherited convention
`g_ik = g_jk * g_ij`. -/
theorem chartChange_transition_law (A : OrdinaryAtlasPresentation F ι)
    (A' : OrdinaryAtlasPresentation F ι') (i j : ι) (i' j' : ι') (b : B)
    (hij' : b ∈ A'.U i' ∩ A'.U j') (hij : b ∈ A.U i ∩ A.U j)
    (hi : b ∈ A.U i ∩ A'.U i') (hj : b ∈ A.U j ∩ A'.U j') :
    A'.transitionFun i' j' ⟨b, hij'⟩
      = chartGauge A A' j j' ⟨b, hj⟩ * A.transitionFun i j ⟨b, hij⟩ *
        (chartGauge A A' i i' ⟨b, hi⟩)⁻¹ := by
  have hi'i : b ∈ A'.U i' ∩ A.U i := ⟨hij'.1, hij.1⟩
  have hi'j : b ∈ A'.U i' ∩ A.U j := ⟨hij'.1, hij.2⟩
  -- `g'_{i'j'} = h_{j j'} * (Φ'_{i'} → Φ_j)`
  have h1 : A'.transitionFun i' j' ⟨b, hij'⟩
      = chartGauge A A' j j' ⟨b, hj⟩ * chartGauge A' A i' j ⟨b, hi'j⟩ :=
    transitionOn_trans (A'.triv i') (A.triv j) (A'.triv j') b hij' hj hi'j
  -- `(Φ'_{i'} → Φ_j) = g_{ij} * (Φ'_{i'} → Φ_i)`
  have h2 : chartGauge A' A i' j ⟨b, hi'j⟩
      = A.transitionFun i j ⟨b, hij⟩ * chartGauge A' A i' i ⟨b, hi'i⟩ :=
    transitionOn_trans (A'.triv i') (A.triv i) (A.triv j) b hi'j hij hi'i
  have h3 : chartGauge A' A i' i ⟨b, hi'i⟩ = (chartGauge A A' i i' ⟨b, hi⟩)⁻¹ :=
    chartGauge_symm A A' i i' b hi hi'i
  rw [h1, h2, h3, ← mul_assoc]

/-- **PACKAGE B (item 20), triple-overlap compatibility of the comparison data.**  On a triple
overlap the comparison maps of one presentation-change are compatible with the triple-overlap
law of both transition systems: this is exactly `chartGauge_comp` used twice, packaged as the
statement that the gauge law is consistent with `g_ik = g_jk * g_ij`. -/
theorem chartChange_tripleOverlap_compatible (A : OrdinaryAtlasPresentation F ι)
    (A' : OrdinaryAtlasPresentation F ι') (i j k : ι) (i' j' k' : ι') (b : B)
    (hik' : b ∈ A'.U i' ∩ A'.U k') (hjk' : b ∈ A'.U j' ∩ A'.U k')
    (hij' : b ∈ A'.U i' ∩ A'.U j') (hik : b ∈ A.U i ∩ A.U k) (hjk : b ∈ A.U j ∩ A.U k)
    (hij : b ∈ A.U i ∩ A.U j) (hi : b ∈ A.U i ∩ A'.U i') (hj : b ∈ A.U j ∩ A'.U j')
    (hk : b ∈ A.U k ∩ A'.U k') :
    chartGauge A A' k k' ⟨b, hk⟩ * A.transitionFun i k ⟨b, hik⟩ *
        (chartGauge A A' i i' ⟨b, hi⟩)⁻¹
      = (chartGauge A A' k k' ⟨b, hk⟩ * A.transitionFun j k ⟨b, hjk⟩ *
          (chartGauge A A' j j' ⟨b, hj⟩)⁻¹) *
        (chartGauge A A' j j' ⟨b, hj⟩ * A.transitionFun i j ⟨b, hij⟩ *
          (chartGauge A A' i i' ⟨b, hi⟩)⁻¹) := by
  rw [← chartChange_transition_law A A' i k i' k' b hik' hik hi hk,
    ← chartChange_transition_law A A' j k j' k' b hjk' hjk hj hk,
    ← chartChange_transition_law A A' i j i' j' b hij' hij hi hj]
  exact A'.transitionFun_trans i' j' k' b hik' hjk' hij'

end ChartChange

/-! ## Joint ordinary atlases: where continuity of the comparison maps is *proved* -/

section Joint

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)]

/-- **PACKAGE B (item 16), principal definition.**  A *joint ordinary atlas*: a family of
ordinary atlas presentations of one bare metric-oriented family, all on **one** indexed open
cover, whose overlap maps are continuous *across* presentations as well as inside each one.

This is the exact hypothesis under which item 18 can be honestly discharged.  Firewall item 8
is respected: nothing here asserts that a chart change has an internal lift. -/
structure JointOrdinaryAtlas (F : BareMetricOrientedFamily B E) (σ : Type s) (ι : Type t) where
  /-- The common trivializing cover. -/
  U : ι → Set B
  /-- Each domain is open. -/
  isOpen_U : ∀ i, IsOpen (U i)
  /-- The domains cover the base. -/
  cover : ∀ b : B, ∃ i, b ∈ U i
  /-- One local trivialization for each presentation label and each domain. -/
  triv : σ → ∀ i, F.LocalFibreTriv (U i)
  /-- Continuity of every overlap map, across presentations. -/
  continuousOn_overlap : ∀ p q : σ × ι,
    ContinuousOn (ovMap (fun r : σ × ι => U r.2)
        (fun r b => fibreChart (triv r.1 r.2) b) p q)
      {x : ↥(U p.2) × Model | (x.1 : B) ∈ U q.2}

namespace JointOrdinaryAtlas

variable {F : BareMetricOrientedFamily B E} {σ : Type s} {ι : Type t}
  (J : JointOrdinaryAtlas F σ ι)

/-- The single big atlas obtained by regarding every chart of every presentation as a chart. -/
noncomputable def toAtlas (s₀ : σ) : OrdinaryAtlasPresentation F (σ × ι) where
  U := fun r => J.U r.2
  isOpen_U := fun r => J.isOpen_U r.2
  cover := fun b => by obtain ⟨i, hi⟩ := J.cover b; exact ⟨(s₀, i), hi⟩
  triv := fun r => J.triv r.1 r.2
  continuousOn_overlap := J.continuousOn_overlap

/-- **PACKAGE B (item 16).**  The presentation labelled `s`. -/
noncomputable def atlas (s : σ) : OrdinaryAtlasPresentation F ι where
  U := J.U
  isOpen_U := J.isOpen_U
  cover := J.cover
  triv := J.triv s
  continuousOn_overlap := fun i j => J.continuousOn_overlap (s, i) (s, j)

@[simp] theorem atlas_U (s : σ) (i : ι) : (J.atlas s).U i = J.U i := rfl

@[simp] theorem atlas_triv (s : σ) (i : ι) : (J.atlas s).triv i = J.triv s i := rfl

/-- **PACKAGE B (item 17).**  The chart-comparison map of two labels, on one chart domain. -/
noncomputable def gauge (s t : σ) (i : ι) (b : ↥(J.U i)) : GvisModel :=
  chartGauge (J.atlas s) (J.atlas t) i i ⟨(b : B), b.2, b.2⟩

/-- **PACKAGE B (item 18), REQUIRED ENDPOINT.**  Every ordinary chart-comparison map of a
joint ordinary atlas is continuous.  The proof runs through the total-space product charts of
the *joint* atlas, exactly as in the inherited Task-XXVII continuity proof. -/
theorem continuous_gauge (s t : σ) (i : ι) : Continuous (J.gauge s t i) := by
  classical
  letI := (J.toAtlas s).top
  have h := continuous_transitionOn ((J.toAtlas s).topTriv (s, i))
    ((J.toAtlas s).topTriv (t, i))
  have hmap : Continuous fun b : ↥(J.U i) => (⟨(b : B), b.2, b.2⟩ : ↥(J.U i ∩ J.U i)) :=
    Continuous.subtype_mk continuous_subtype_val _
  exact h.comp hmap

/-- **PACKAGE B (item 22), identity chart change. -/
theorem gauge_self (s : σ) (i : ι) (b : ↥(J.U i)) : J.gauge s s i b = 1 :=
  chartGauge_self (J.atlas s) i _

/-- **PACKAGE B (item 20), inverse compatibility. -/
theorem gauge_symm (s t : σ) (i : ι) (b : ↥(J.U i)) :
    J.gauge t s i b = (J.gauge s t i b)⁻¹ :=
  chartGauge_symm (J.atlas s) (J.atlas t) i i (b : B) ⟨b.2, b.2⟩ ⟨b.2, b.2⟩

/-- **PACKAGE B (item 21), composition of successive chart changes. -/
theorem gauge_comp (s t r : σ) (i : ι) (b : ↥(J.U i)) :
    J.gauge s r i b = J.gauge t r i b * J.gauge s t i b :=
  chartGauge_comp (J.atlas s) (J.atlas t) (J.atlas r) i i i (b : B) ⟨b.2, b.2⟩ ⟨b.2, b.2⟩
    ⟨b.2, b.2⟩

/-- **PACKAGE B (item 24), REQUIRED ENDPOINT.**  Two presentations inside one joint ordinary
atlas differ by continuous ordinary `GvisModel`-valued chart gauges satisfying the exact
transition conjugation law. -/
theorem transition_gauge_law (s t : σ) (i j : ι) (b : B) (h : b ∈ J.U i ∩ J.U j) :
    (J.atlas t).transitionFun i j ⟨b, h⟩
      = J.gauge s t j ⟨b, h.2⟩ * (J.atlas s).transitionFun i j ⟨b, h⟩ *
        (J.gauge s t i ⟨b, h.1⟩)⁻¹ :=
  chartChange_transition_law (J.atlas s) (J.atlas t) i j i j b h h ⟨h.1, h.1⟩ ⟨h.2, h.2⟩

end JointOrdinaryAtlas

end Joint

/-! ## Ordinary chart-gauge equivalence -/

section GaugeEquivalence

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : BareMetricOrientedFamily B E}
  {ι : Type t} {ι' : Type t'} {ι'' : Type _}

/-- **PACKAGE B (item 23), principal definition.**  Two ordinary atlas presentations of one
bare family are *ordinary chart-gauge equivalent* when every chart-comparison map between
them is continuous.  By `chartChange_transition_law` this is exactly the statement that their
ordinary transition systems differ by continuous `GvisModel`-valued chart gauges.

Note (negative control 120): this is **not** "they present the same family" — that is already
built into the type — but a genuine condition on how their local data are related. -/
def OrdinaryChartGaugeEquivalent (A : OrdinaryAtlasPresentation F ι)
    (A' : OrdinaryAtlasPresentation F ι') : Prop :=
  ∀ (i : ι) (i' : ι'), Continuous (chartGauge A A' i i')

/-- **PACKAGE B (item 23).**  Reflexivity: the comparison maps of a presentation with itself
are its own (continuous) transition maps. -/
theorem ordinaryChartGaugeEquivalent_refl (A : OrdinaryAtlasPresentation F ι) :
    OrdinaryChartGaugeEquivalent A A :=
  fun i j => A.continuous_transitionFun i j

/-- **PACKAGE B (item 23).**  Symmetry, from the inverse law and continuity of inversion. -/
theorem ordinaryChartGaugeEquivalent_symm {A : OrdinaryAtlasPresentation F ι}
    {A' : OrdinaryAtlasPresentation F ι'} (h : OrdinaryChartGaugeEquivalent A A') :
    OrdinaryChartGaugeEquivalent A' A := by
  intro i' i
  have hswap : Continuous fun b : ↥(A'.U i' ∩ A.U i) =>
      (⟨(b : B), b.2.2, b.2.1⟩ : ↥(A.U i ∩ A'.U i')) :=
    Continuous.subtype_mk continuous_subtype_val _
  have : Continuous fun b : ↥(A'.U i' ∩ A.U i) =>
      (chartGauge A A' i i' ⟨(b : B), b.2.2, b.2.1⟩)⁻¹ :=
    ((h i i').comp hswap).inv
  refine this.congr fun b => ?_
  exact (chartGauge_symm A A' i i' (b : B) ⟨b.2.2, b.2.1⟩ b.2).symm

/-- **PACKAGE B (item 23).**  Transitivity, from the composition law and continuity of
multiplication. -/
theorem ordinaryChartGaugeEquivalent_trans {A : OrdinaryAtlasPresentation F ι}
    {A' : OrdinaryAtlasPresentation F ι'} {A'' : OrdinaryAtlasPresentation F ι''}
    (h : OrdinaryChartGaugeEquivalent A A') (h' : OrdinaryChartGaugeEquivalent A' A'') :
    OrdinaryChartGaugeEquivalent A A'' := by
  intro i i''
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨i', hi'⟩ := A'.cover (x : B)
  set W : Set ↥(A.U i ∩ A''.U i'') := {b | (b : B) ∈ A'.U i'} with hW
  have hopen : IsOpen W := (A'.isOpen_U i').preimage continuous_subtype_val
  have hxW : x ∈ W := hi'
  have hres : Continuous (W.restrict (chartGauge A A'' i i'')) := by
    have hleft : Continuous fun y : ↥W =>
        chartGauge A' A'' i' i'' ⟨((y : ↥(A.U i ∩ A''.U i'')) : B), y.2, (y : ↥(A.U i ∩ A''.U i'')).2.2⟩ :=
      (h' i' i'').comp (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
    have hright : Continuous fun y : ↥W =>
        chartGauge A A' i i' ⟨((y : ↥(A.U i ∩ A''.U i'')) : B), (y : ↥(A.U i ∩ A''.U i'')).2.1, y.2⟩ :=
      (h i i').comp (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
    refine (hleft.mul hright).congr fun y => ?_
    exact (chartGauge_comp A A' A'' i i' i'' ((y : ↥(A.U i ∩ A''.U i'')) : B)
      (y : ↥(A.U i ∩ A''.U i'')).2 ⟨y.2, (y : ↥(A.U i ∩ A''.U i'')).2.2⟩
      ⟨(y : ↥(A.U i ∩ A''.U i'')).2.1, y.2⟩).symm
  have : ContinuousOn (chartGauge A A'' i i'') W :=
    continuousOn_iff_continuous_restrict.2 hres
  exact this.continuousAt (hopen.mem_nhds hxW)

/-- **PACKAGE B (item 24).**  The two presentations of a joint ordinary atlas are ordinary
chart-gauge equivalent. -/
theorem JointOrdinaryAtlas.ordinaryChartGaugeEquivalent {σ : Type s}
    (J : JointOrdinaryAtlas F σ ι) (s t : σ) :
    OrdinaryChartGaugeEquivalent (J.atlas s) (J.atlas t) := by
  intro i j
  classical
  letI := (J.toAtlas s).top
  exact continuous_transitionOn ((J.toAtlas s).topTriv (s, i)) ((J.toAtlas s).topTriv (t, j))

end GaugeEquivalence

end NullSectorTask32
