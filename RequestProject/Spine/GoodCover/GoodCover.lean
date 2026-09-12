import RequestProject.Spine.Cech.Cochain

/-!
# Task 7, WP3 : the exact good-cover notion, and the implications actually needed

This module is Spin-independent: it only speaks about an indexed family of subsets
`U : ι → Set X` and the topology of its finite overlaps.  It fixes the terminology that WP3
insists must not be conflated, and proves exactly the implications the Task-6 constancy
conditions consume.

## The hierarchy of overlap conditions

For a subset `s ⊆ X` (here always a finite overlap `inter U σ = ⋂ t, U (σ t)`):

```
   ContractibleSpace s   ⟹   IsPathConnected s   ⟹   IsConnected s   ⟹   IsPreconnected s
```

with the first two implications requiring `s` to be nonempty in the last step only
(`IsPreconnected` is the condition that survives for `s = ∅`).  All four notions are kept
distinct: `contractible_ne_preconnected` records that the implication chain is *strict*
(the empty set is preconnected and is not contractible), so "preconnected" is genuinely
weaker and the good-cover hypothesis is not a renaming of the Task-6 hypothesis.

## The good-cover predicate

`GoodCoverZ2.IsGoodCover U` is the conventional condition:

* every `U i` is open;
* the family covers `X`;
* **every nonempty finite intersection `U i₀ ∩ ⋯ ∩ U i_k` is contractible.**

The intersections are taken in exactly the form the Čech/nerve layer uses
(`CechZ2.inter`), so no second overlap model is introduced.

`IsGoodCover.isPreconnected_inter` is the only consequence the Task-6 bridge needs; the pair
and triple forms `isPreconnected_pair` / `isPreconnected_triple` are the two instances that
appear in the Spin-defect constancy conditions (see
`RequestProject.Spine.GoodCover.Constancy`).

**Acyclic covers are a strictly weaker notion and are treated separately** in
`RequestProject.Spine.GoodCover.AcyclicCover`; `IsGoodCover` is *not* defined by acyclicity
here, and the implication "good ⇒ acyclic" is *not* proved (it needs homotopy invariance of
the Task-5 singular theory, which is the WP9 dependency).
-/

namespace GoodCoverZ2

open CechZ2

universe w t

variable {X : Type w} [TopologicalSpace X] {ι : Type t}

/-! ## The four notions, and the implications between them -/

/-- A contractible subspace is path connected — Mathlib's instance
`ContractibleSpace → PathConnectedSpace`, transported to sets. -/
theorem isPathConnected_of_contractible {s : Set X} (h : ContractibleSpace s) :
    IsPathConnected s := by
  haveI := h
  exact (isPathConnected_iff_pathConnectedSpace).2 inferInstance

/-- A contractible subspace is connected (in particular nonempty). -/
theorem isConnected_of_contractible {s : Set X} (h : ContractibleSpace s) : IsConnected s :=
  (isPathConnected_of_contractible h).isConnected

/-- A contractible subspace is preconnected.  This is the implication the Čech bridge uses. -/
theorem isPreconnected_of_contractible {s : Set X} (h : ContractibleSpace s) :
    IsPreconnected s :=
  (isConnected_of_contractible h).isPreconnected

/-- **Non-conflation control.**  Preconnected does *not* imply contractible: the empty set is
preconnected, and it is not contractible (a contractible space is path connected, hence
nonempty). -/
theorem contractible_ne_preconnected :
    IsPreconnected (∅ : Set X) ∧ ¬ ContractibleSpace ((∅ : Set X)) := by
  refine ⟨isPreconnected_empty, fun h => ?_⟩
  obtain ⟨x, hx⟩ := (isConnected_of_contractible h).nonempty
  exact hx

/-! ## Good covers -/

/-- **The good-cover predicate.**  An open cover all of whose *nonempty* finite intersections
are contractible.  Intersections are the ones of the nerve, `CechZ2.inter`. -/
structure IsGoodCover (U : ι → Set X) : Prop where
  /-- Every member of the cover is open. -/
  isOpen : ∀ i, IsOpen (U i)
  /-- The family covers the space. -/
  covers : ∀ x : X, ∃ i, x ∈ U i
  /-- Every nonempty finite intersection of *cover members* is contractible.  The tuples have
  length `n + 1`: the empty tuple is excluded, since its intersection is the whole space and
  requiring *that* to be contractible would be a condition on `X`, not on the cover. -/
  contractible_inter : ∀ {n : ℕ} (σ : Fin (n + 1) → ι), (inter U σ).Nonempty →
    ContractibleSpace (inter U σ)

namespace IsGoodCover

variable {U : ι → Set X} (h : IsGoodCover U)
include h

/-- Every finite overlap of a good cover is preconnected (the empty overlaps trivially). -/
theorem isPreconnected_inter {n : ℕ} (σ : Fin (n + 1) → ι) :
    IsPreconnected (inter U σ) := by
  rcases Set.eq_empty_or_nonempty (inter U σ) with he | hne
  · rw [he]; exact isPreconnected_empty
  · exact isPreconnected_of_contractible (h.contractible_inter σ hne)

/-- Every nonempty finite overlap of a good cover is path connected. -/
theorem isPathConnected_inter {n : ℕ} (σ : Fin (n + 1) → ι) (hne : (inter U σ).Nonempty) :
    IsPathConnected (inter U σ) :=
  isPathConnected_of_contractible (h.contractible_inter σ hne)

/-- Every simplex of the nerve of a good cover has contractible support. -/
theorem contractible_nerve {n : ℕ} (σ : Nerve U n) : ContractibleSpace (inter U σ.idx) :=
  h.contractible_inter σ.idx σ.nonempty

end IsGoodCover

/-! ## The pair and triple overlaps, in the form the Spin bridge consumes -/

omit [TopologicalSpace X] in
theorem inter_pair' (U : ι → Set X) (i j : ι) : inter U ![i, j] = U i ∩ U j := by
  ext x
  rw [mem_inter_iff]
  constructor
  · intro hx; exact ⟨hx 0, hx 1⟩
  · rintro ⟨h1, h2⟩ s; fin_cases s <;> simpa using ‹_›

omit [TopologicalSpace X] in
theorem inter_triple' (U : ι → Set X) (i j k : ι) :
    inter U ![i, j, k] = U i ∩ U j ∩ U k := by
  ext x
  rw [mem_inter_iff]
  constructor
  · intro hx; exact ⟨⟨hx 0, hx 1⟩, hx 2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩ s; fin_cases s <;> simpa using ‹_›

namespace IsGoodCover

variable {U : ι → Set X} (h : IsGoodCover U)
include h

/-- **The pair form.**  Double overlaps of a good cover are preconnected. -/
theorem isPreconnected_pair (i j : ι) : IsPreconnected (U i ∩ U j) := by
  rw [← inter_pair' U i j]
  exact h.isPreconnected_inter _

/-- **The triple form.**  Triple overlaps of a good cover are preconnected. -/
theorem isPreconnected_triple (i j k : ι) : IsPreconnected (U i ∩ U j ∩ U k) := by
  rw [← inter_triple' U i j k]
  exact h.isPreconnected_inter _

end IsGoodCover

end GoodCoverZ2
