import RequestProject.Spine.E2.Topology.AtlasTopology

/-!
# Task 27: adding a compatible chart to an atlas (generic core, continued)

A local chart which is *not* a member of the atlas but whose overlap maps with all atlas
charts are continuous is automatically a homeomorphism for the atlas topology.  The proof
does not repeat the construction of the topology: the extended atlas has the same admissible
topology as the original one (by the uniqueness theorem `ChartAtlas.IsAdmissible.eq_top`),
and the new chart is a chart of the extended atlas.

This generic statement is what makes item 63 (a topological fibre trivialization induces a
topological frame trivialization) provable for *arbitrary* compatible trivializations, not
only for the members of the chosen atlas.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask27

open Topology

universe u v w t

variable {B : Type u} [TopologicalSpace B] {C : B → Type v} {M : Type w} [TopologicalSpace M]
  {ι : Type t}

namespace ChartAtlas

variable (A : ChartAtlas C M ι) (V : Set B) (χ : ∀ b : V, C (b : B) ≃ M)

/-- The domains of the atlas extended by one further chart over `V`. -/
def optU : Option ι → Set B := fun o => o.elim V A.U

@[simp] theorem optU_none : A.optU V none = V := rfl

@[simp] theorem optU_some (i : ι) : A.optU V (some i) = A.U i := rfl

/-- The charts of the atlas extended by one further chart over `V`. -/
def optChart : ∀ (o : Option ι) (b : A.optU V o), C (b : B) ≃ M
  | none => χ
  | some i => A.chart i

/-- **NEWLY DEFINED, principal.**  The atlas extended by one further compatible chart. -/
noncomputable def addChart (hV : IsOpen V)
    (h1 : ∀ i, ContinuousOn (ovMap (A.optU V) (A.optChart V χ) none (some i))
      {p : (A.optU V none) × M | (p.1 : B) ∈ A.optU V (some i)})
    (h2 : ∀ i, ContinuousOn (ovMap (A.optU V) (A.optChart V χ) (some i) none)
      {p : (A.optU V (some i)) × M | (p.1 : B) ∈ A.optU V none}) :
    ChartAtlas C M (Option ι) where
  U := A.optU V
  isOpen_U := by
    rintro (_ | i)
    · exact hV
    · exact A.isOpen_U i
  cover := fun b => by
    obtain ⟨i, hi⟩ := A.cover b
    exact ⟨some i, hi⟩
  chart := A.optChart V χ
  continuousOn_overlap := by
    rintro (_ | i) (_ | j)
    · have hid : ovMap (A.optU V) (A.optChart V χ) none none
          = fun p : (A.optU V none) × M => p.2 := by
        funext p
        rw [ovMap_apply (U := A.optU V) (chart := A.optChart V χ) p p.1.2]
        exact (χ p.1).apply_symm_apply p.2
      rw [hid]
      exact continuous_snd.continuousOn
    · exact h1 j
    · exact h2 i
    · exact A.continuousOn_overlap i j

variable (hV : IsOpen V)
  (h1 : ∀ i, ContinuousOn (ovMap (A.optU V) (A.optChart V χ) none (some i))
    {p : (A.optU V none) × M | (p.1 : B) ∈ A.optU V (some i)})
  (h2 : ∀ i, ContinuousOn (ovMap (A.optU V) (A.optChart V χ) (some i) none)
    {p : (A.optU V (some i)) × M | (p.1 : B) ∈ A.optU V none})

/-- **DERIVED, principal.**  Adding a compatible chart does not change the topology of the
total carrier: the extended atlas is admissible for the original atlas, so by uniqueness the
two generated topologies coincide. -/
theorem addChart_top : (A.addChart V χ hV h1 h2).top = A.top := by
  letI := (A.addChart V χ hV h1 h2).top
  have hadm := (A.addChart V χ hV h1 h2).top_isAdmissible
  refine ChartAtlas.IsAdmissible.eq_top A ?_
  exact
    { continuous_base := hadm.continuous_base
      continuous_chart := fun i => hadm.continuous_chart (some i)
      continuous_chartSymm := fun i => hadm.continuous_chartSymm (some i) }

/-- **DERIVED, principal.**  The added chart is continuous for the atlas topology. -/
theorem continuous_addChart :
    @Continuous _ _ (@instTopologicalSpaceSubtype (Total C) _ A.top) _
      ((A.addChart V χ hV h1 h2).chartFun none) := by
  have hEq : (A.addChart V χ hV h1 h2).top = A.top := A.addChart_top V χ hV h1 h2
  letI := (A.addChart V χ hV h1 h2).top
  have hadm := (A.addChart V χ hV h1 h2).top_isAdmissible
  have h := hadm.continuous_chart none
  rw [hEq] at h
  exact h

/-- **DERIVED, principal.**  The inverse of the added chart is continuous for the atlas
topology. -/
theorem continuous_addChart_symm :
    @Continuous _ _ _ (@instTopologicalSpaceSubtype (Total C) _ A.top)
      ((A.addChart V χ hV h1 h2).chartSymm none) := by
  have hEq : (A.addChart V χ hV h1 h2).top = A.top := A.addChart_top V χ hV h1 h2
  letI := (A.addChart V χ hV h1 h2).top
  have hadm := (A.addChart V χ hV h1 h2).top_isAdmissible
  have h := hadm.continuous_chartSymm none
  rw [hEq] at h
  exact h

end ChartAtlas

end NullSectorTask27
