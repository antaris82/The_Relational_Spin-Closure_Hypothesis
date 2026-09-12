import RequestProject.Spine.Geometry.TangentInstance

/-!
# Task 10, WP0 : correcting the Task-4 global-assumption status

Task 9 asserted, in the docstring of `NerveGeom.NerveTheoremStatement`, that in the Task-4
manifold model "`hopen`, `hcover` and `hparacompact` are available (a manifold charted on a
finite-dimensional normed space is locally compact, second countable in the Task-4 model,
hence paracompact)".  **That assertion is wrong** and is corrected here and in
`RequestProject.Spine.Nerve.Cochain.ComparisonSpec`.

Task 4 assumes exactly

```
  [TopologicalSpace M] [ChartedSpace LorentzCarrier M]   (+ [IsManifold carrierModel ⊤ M])
```

and *nothing else*.  In particular the following are **not** hypotheses of Task 4 and are
**not** derived anywhere in the project:

| property | status in the Task-4 layer |
| --- | --- |
| Hausdorffness (`T2Space`) | `NOT_ASSUMED`, `NOT_DERIVED` |
| second countability (`SecondCountableTopology`) | `NOT_ASSUMED`, `NOT_DERIVED`, and **refuted** below |
| paracompactness (`ParacompactSpace`) | `NOT_ASSUMED`, `NOT_DERIVED` |
| metrisability | `NOT_ASSUMED`, `NOT_DERIVED` |
| numerability of an arbitrary open cover | `NOT_ASSUMED`, `NOT_DERIVED` |
| existence of a good cover | `NOT_ASSUMED`, `NOT_DERIVED` (Task 7, `MISSING`) |

The implication

`charted on ℝ⁴  ⟹  second countable / paracompact`

is **false**, and this module proves the second-countability half of that at theorem level, so
that the corrected status is mechanically checkable rather than merely documented:

* `SpineTask10.chartedNotSecondCountable` — an explicit topological space, charted on the
  Task-4 carrier `SpinCore.LorentzCarrier = ℝ × (Fin 3 → ℝ)` and a genuine
  `IsManifold carrierModel ⊤` object, which is **not** second countable.  It is the disjoint
  union of continuum-many copies of the model space.
* `SpineTask10.not_secondCountable_of_charted` — consequently no theorem of the shape
  "every Task-4 manifold is second countable" can be proved.

For Hausdorffness and paracompactness no counterexample is formalised here; the statement made
is only the (weaker, and true) one that the project neither assumes nor derives them.  The
classical counterexamples — the line with two origins for Hausdorffness, the Prüfer surface
for paracompactness — are not available in pinned Mathlib and are out of scope for Task 10.

**Nothing is added to Task 4.**  This module introduces no new hypothesis anywhere in the
Spine; it only exhibits a counterexample and thereby corrects a status claim.
-/

noncomputable section

namespace SpineTask10

open Topology TopologicalSpace SpinCore LorentzFrames

/-! ## Disjoint unions of copies of the model space are charted manifolds -/

section Sigma

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  (ι : Type*) (n : WithTop ℕ∞)

/-- The disjoint union of `ι` copies of the model space `H` is charted on `H`: the chart at a
point of the `i`-th copy is the identity chart of that copy, transported along the open
embedding `Sigma.mk i`. -/
scoped instance chartedSigma [Nonempty H] : ChartedSpace H (Σ _ : ι, H) where
  atlas := Set.range (fun i : ι =>
    (OpenPartialHomeomorph.refl H).lift_openEmbedding
      (Topology.IsOpenEmbedding.sigmaMk (σ := fun _ : ι => H) (i := i)))
  chartAt p := (OpenPartialHomeomorph.refl H).lift_openEmbedding
      (Topology.IsOpenEmbedding.sigmaMk (σ := fun _ : ι => H) (i := p.1))
  mem_chart_source p := by
    rw [OpenPartialHomeomorph.lift_openEmbedding_source]
    exact ⟨p.2, trivial, rfl⟩
  chart_mem_atlas p := ⟨p.1, rfl⟩

/-- The disjoint union of copies of the model space is a `C^n` manifold: the chart transitions
are either the identity (same copy) or have empty source (different copies). -/
scoped instance isManifoldSigma [Nonempty H] : IsManifold I n (Σ _ : ι, H) where
  compatible {e} e' he he' := by
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := he'
    by_cases hij : i = j
    · subst hij
      rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
      exact (contDiffGroupoid n I).compatible (chartedSpaceSelf_atlas.2 rfl)
        (chartedSpaceSelf_atlas.2 rfl)
    · apply ContDiffGroupoid.mem_of_source_eq_empty
      ext x
      refine ⟨?_, fun hx => hx.elim⟩
      rintro ⟨hx₁, hx₂⟩
      simp_all [OpenPartialHomeomorph.lift_openEmbedding_source,
        OpenPartialHomeomorph.lift_openEmbedding_target]

/-- A disjoint union of uncountably many copies of a nonempty space is never second
countable: a countable dense subset would have to meet each of the uncountably many pairwise
disjoint open pieces. -/
theorem not_secondCountable_sigma {H : Type*} [TopologicalSpace H] [Nonempty H] {ι : Type*}
    (hι : ¬ Countable ι) : ¬ SecondCountableTopology (Σ _ : ι, H) := by
  intro hsc
  have hsep : SeparableSpace (Σ _ : ι, H) := SecondCountableTopology.to_separableSpace
  obtain ⟨s, hcount, hdense⟩ := exists_countable_dense (α := Σ _ : ι, H)
  have hopen : ∀ i : ι, IsOpen (Set.range (fun x : H => (⟨i, x⟩ : Σ _ : ι, H))) :=
    fun i => Topology.IsOpenEmbedding.sigmaMk.isOpen_range
  have hne : ∀ i : ι, (Set.range (fun x : H => (⟨i, x⟩ : Σ _ : ι, H))).Nonempty :=
    fun i => ⟨⟨i, Classical.arbitrary H⟩, ⟨_, rfl⟩⟩
  choose f hf hf' using fun i : ι => hdense.exists_mem_open (hopen i) (hne i)
  have hfst : ∀ i, (f i).1 = i := by
    intro i
    obtain ⟨x, hx⟩ := hf' i
    rw [← hx]
  have := hcount.to_subtype
  have hinj : Function.Injective (fun i : ι => (⟨f i, hf i⟩ : s)) := by
    intro i j hij
    have hfij : f i = f j := congrArg Subtype.val hij
    rw [← hfst i, ← hfst j, hfij]
  exact hι hinj.countable

end Sigma

/-! ## The counterexample -/

/-- **The Task-10 WP0 counterexample**: continuum-many disjoint copies of the Task-4 carrier
space `ℝ × (Fin 3 → ℝ)`. -/
abbrev BigChartedSpace : Type := Σ _ : ℝ, LorentzCarrier

instance : ChartedSpace LorentzCarrier BigChartedSpace := chartedSigma ℝ

instance : IsManifold carrierModel ⊤ BigChartedSpace := isManifoldSigma carrierModel ℝ ⊤

/-- **WP0, principal.**  There is a space satisfying *exactly* the Task-4 hypotheses — charted
on the four-dimensional carrier, and a `C^∞` manifold for the Task-4 model with corners — which
is **not** second countable. -/
theorem chartedNotSecondCountable : ¬ SecondCountableTopology BigChartedSpace :=
  not_secondCountable_sigma (fun _ => Cardinal.not_countable_real Set.countable_univ)

/-- **WP0, corrected status.**  "Charted on the Task-4 carrier (and a manifold for the Task-4
model) implies second countable" is **false**.  A fortiori the Task-4 layer does not supply
second countability, and the Task-9 claim that it does — and that paracompactness follows from
it — is withdrawn. -/
theorem not_secondCountable_of_charted :
    ¬ (∀ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace LorentzCarrier M),
        SecondCountableTopology M) := by
  intro h
  exact chartedNotSecondCountable (h BigChartedSpace inferInstance inferInstance)

end SpineTask10
