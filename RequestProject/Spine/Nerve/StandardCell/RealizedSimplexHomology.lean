import RequestProject.Spine.AlgebraicTopology.Contractible
import RequestProject.Spine.Nerve.Geometry.StandardSimplex

/-!
# Homology of the realized standard simplex

The single corollary obtained by feeding the contractibility of the realized standard simplex
(`RequestProject.Spine.Nerve.Geometry.StandardSimplex`) into the generic vanishing theorem
`SpineTask18.isZero_homology_of_contractible`
(`RequestProject.Spine.AlgebraicTopology.Contractible`):

`H_q^{sing}(|Δ[r]|; ℤ₂) = 0` for every positive `q`.

It is kept in its own module so that neither the generic contractibility theory nor the
point-set geometry of the realized simplex has to import the other.
-/

noncomputable section

open CategoryTheory Limits Simplicial SSet CategoryTheory.Limits

universe u

namespace SpineTask18

/-- **Instantiated at the realized standard simplex.**  `H_q(|Δ[r]|; ℤ₂) = 0` for
every positive `q`. -/
theorem isZero_homology_realized_simplex (r : ℕ) (m : ℕ) :
    IsZero ((singCx (SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))).homology (m + 1)) :=
  isZero_homology_of_contractible m

end SpineTask18
