import RequestProject.Spine.Emergent.Symmetric

/-!
# Spine / Emergent : the change-of-chart law and the remaining smooth gate

**Sixth module of the manifold-emergence layer (Task 32, Outcome C component).**

The topological reconstruction of `RequestProject.Spine.Emergent.Reconstruction` is complete:
the emergent base is a charted space over the local model, Hausdorff under the closed-graph
condition and second countable for a countable index type.  What is *not* automatic is
smoothness, and this module says exactly what is missing and no more.

* `EmergentBase.BaseGluingData.chart_eq_chart_of_mem_W` — the **change-of-chart law**: on the
  incidence domain the two charts differ precisely by the primitive's identification map
  `φ_ij`.  So the coordinate changes of the emergent atlas are the `φ_ij` themselves — no
  other transition maps arise.
* `EmergentBase.BaseGluingData.SmoothGluing` — consequently the exact extra condition needed
  for a *smooth* atlas is that the primitive's identification maps be smooth on their
  incidence domains.  It is an explicit condition on the primitive, not a derived fact:
  nothing in the topological reconstruction implies it.
* `EmergentBase.symmetricGluing.smoothGluing` — the neutral sector satisfies it (the
  identifications are the identity).

**What is not claimed here (closed in Task 33).**  This module produces no
`IsManifold` instance: packaging the emergent atlas as a member of the `contDiffGroupoid` is
a further step, taken in `RequestProject.Spine.Emergent.SmoothStructure`, where
`BaseGluingData.isManifold_of_smoothGluing` proves that `SmoothGluing` does imply Mathlib's
`IsManifold` for *this* atlas.  No metric, connection, transport, holonomy or curvature
appears anywhere in this layer.
-/

noncomputable section

namespace EmergentBase

universe u t

namespace BaseGluingData

variable {V : Type u} [TopologicalSpace V] {ι : Type t} (B : BaseGluingData V ι)

/-- **DERIVED (Task 32), the change-of-chart law.**  Over the incidence domain the chart of
the piece `i` and the chart of the piece `j` are related exactly by the primitive's
identification map `φ_ij`: the coordinate changes of the emergent atlas are the `φ_ij`. -/
theorem chart_eq_chart_of_mem_W (i j : ι) {x : V} (hx : x ∈ B.W i j) :
    B.chart i ⟨x, B.W_subset i j hx⟩
      = B.chart j ⟨B.φ i j x, B.W_subset j i (B.φ_mapsTo i j hx)⟩ :=
  (B.mk_eq_mk_iff).2 ⟨hx, rfl⟩

/-- **DERIVED (Task 32).**  Two charts overlap exactly over the incidence domains: the image
of the piece `i` meets the image of the piece `j` only in points coming from `W i j`. -/
theorem mem_chartRange_inter_iff (i j : ι) (x : (B.D i : Set V)) :
    B.chart i x ∈ B.chartRange j ↔ (x : V) ∈ B.W i j := by
  constructor
  · rintro ⟨y, hy⟩
    have := (B.mk_eq_mk_iff).1 hy
    exact (B.rel_symm this).1
  · intro hx
    exact ⟨⟨B.φ i j (x : V), B.W_subset j i (B.φ_mapsTo i j hx)⟩,
      (B.chart_eq_chart_of_mem_W i j hx).symm⟩

end BaseGluingData

/-! ## The remaining smooth gate -/

variable {ι : Type t}

/-- **NEWLY DEFINED (Task 32), the exact missing smoothness condition.**  A base-gluing datum
in the (real, finite-dimensional) local model is *smooth* when its identification maps are
smooth on their incidence domains.  By the change-of-chart law this is precisely the
condition under which the emergent atlas is a smooth atlas; it is a condition on the
primitive and is not implied by the topological reconstruction. -/
def BaseGluingData.SmoothGluing (B : BaseGluingData LocalModel ι) : Prop :=
  ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (B.φ i j) (B.W i j)

/-- **DERIVED (Task 32).**  The neutral sector satisfies the smoothness condition: its
identification maps are the identity. -/
theorem symmetricGluing.smoothGluing {D : Set LocalModel} (hD : IsOpen D) :
    (symmetricGluing ι hD).SmoothGluing := fun _ _ => contDiffOn_id

/-- **DERIVED (Task 32).**  For a smooth base-gluing datum every coordinate change of the
emergent atlas is smooth, and each such coordinate change is one of the `φ_ij`.  This is the
whole content of "smooth compatibility" at the level reached by Task 32; the packaging of the
atlas as a Mathlib `IsManifold` structure is performed in Task 33
(`RequestProject.Spine.Emergent.SmoothStructure`). -/
theorem smooth_chart_changes {B : BaseGluingData LocalModel ι} (h : B.SmoothGluing) :
    (∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (B.φ i j) (B.W i j)) ∧
    (∀ (i j : ι) {x : LocalModel} (hx : x ∈ B.W i j),
      B.chart i ⟨x, B.W_subset i j hx⟩
        = B.chart j ⟨B.φ i j x, B.W_subset j i (B.φ_mapsTo i j hx)⟩) :=
  ⟨h, fun i j _ hx => B.chart_eq_chart_of_mem_W i j hx⟩

end EmergentBase

end
