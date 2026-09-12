import RequestProject.Spine.Nerve.Geometry.PuncturedSimplex

/-!
# The open standard cell

The open cell `Δ° = |Δ[r]| \ |∂Δ[r]|` and its two elementary point-set properties: it is open,
and together with the punctured cell `|Δ[r]| \ {b_r}` it covers the realized simplex.

This is pure point-set geometry of the realized standard simplex.  It is kept separate from
the homological standard-cell excision (`RequestProject.Spine.Nerve.StandardCell.Excision`)
so that the singular-simplex factorisation through the open cells
(`RequestProject.Spine.Nerve.CellFamily.SingularFactorization`) can use the open cell without
importing any Excision proof.
-/

noncomputable section

open CategoryTheory Limits Simplicial SSet

universe u

namespace SpineTask23

section StandardCell

variable (r : ℕ)

/-- The open cell `Δ° = |Δ[r]| \ |∂Δ[r]|`. -/
def openStdCell : Set ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})) :=
  (Set.range (SSet.toTop.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι))ᶜ

theorem isOpen_openStdCell : IsOpen (openStdCell.{u} r) :=
  SpineTask17.isOpen_compl_realized_boundary.{u} r

theorem openStdCell_union_puncturedCell :
    openStdCell.{u} r ∪ puncturedCell.{u} r = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  by_cases hx : x ∈ Set.range (SSet.toTop.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι)
  · obtain ⟨b, rfl⟩ := hx
    exact Or.inr (cellBdryIncl_mem_puncturedCell.{u} r b)
  · exact Or.inl hx

end StandardCell

end SpineTask23
