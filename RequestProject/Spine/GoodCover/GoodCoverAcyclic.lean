import RequestProject.Spine.GoodCover.AcyclicCover
import RequestProject.Spine.Cohomology.HomotopyInvariance

/-!
# Task 8, WP10 : a good cover is an acyclic cover — now unconditionally

Task 7 defined `GoodCoverZ2.IsGoodCover` (all nonempty finite overlaps contractible) and
`GoodCoverZ2.IsAcyclicCover` (all nonempty finite overlaps preconnected with vanishing
positive-degree native singular mod-2 cohomology) and kept them strictly apart: the implication
`good ⇒ acyclic` was available **only** under the Task-7 hypothesis
`GoodCoverSpec.HomotopyInvariance`.

With the Task-8 theorem `Mod2Cohomology.cohomology_succ_eq_zero_of_contractible` that hypothesis
is gone, and the implication becomes a theorem of the Spine.

```
    good cover  ⟹  acyclic cover      (GoodCoverZ2.isAcyclicCover_of_isGoodCover)
```

together with the two degrees the certification path actually consumes,

```
    H¹_sing(U_{i₀} ∩ ⋯ ∩ U_{i_k}; ℤ₂) = 0 ,   H²_sing(U_{i₀} ∩ ⋯ ∩ U_{i_k}; ℤ₂) = 0 .
```

Classification: `GOOD_COVER_ACYCLIC`, `DERIVED_NATIVE`.
-/

noncomputable section

namespace GoodCoverZ2

open CechZ2 Mod2Cohomology

universe u t

variable {X : Type u} [TopologicalSpace X] {ι : Type t} {U : ι → Set X}

/-- **WP10.**  Every nonempty finite overlap of a good cover has vanishing singular mod-2
cohomology in every positive degree. -/
theorem cohomology_inter_succ_eq_zero (h : IsGoodCover U) {n : ℕ} (σ : Fin (n + 1) → ι)
    (hne : (inter U σ).Nonempty) (k : ℕ)
    (q : Cohomology (TopCat.of (inter U σ)) (k + 1)) : q = 0 := by
  haveI := h.contractible_inter σ hne
  exact cohomology_succ_eq_zero_of_contractible (TopCat.of (inter U σ)) k q

/-- Degree one. -/
theorem cohomology_inter_one_eq_zero (h : IsGoodCover U) {n : ℕ} (σ : Fin (n + 1) → ι)
    (hne : (inter U σ).Nonempty) (q : Cohomology (TopCat.of (inter U σ)) 1) : q = 0 :=
  cohomology_inter_succ_eq_zero h σ hne 0 q

/-- Degree two — the degree carrying the Spin-lift obstruction. -/
theorem cohomology_inter_two_eq_zero (h : IsGoodCover U) {n : ℕ} (σ : Fin (n + 1) → ι)
    (hne : (inter U σ).Nonempty) (q : Cohomology (TopCat.of (inter U σ)) 2) : q = 0 :=
  cohomology_inter_succ_eq_zero h σ hne 1 q

/-- **WP10, the endpoint.**  A good cover is an acyclic cover, unconditionally.  This is the
implication Task 7 deliberately refused to assume; it is now derived from the native
homotopy-invariance theorem. -/
theorem isAcyclicCover_of_isGoodCover (h : IsGoodCover U) : IsAcyclicCover U :=
  ⟨h.isOpen, h.covers, fun σ => h.isPreconnected_inter σ,
    fun σ hne k q => cohomology_inter_succ_eq_zero h σ hne k q⟩

end GoodCoverZ2
