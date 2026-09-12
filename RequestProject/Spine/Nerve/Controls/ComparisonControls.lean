import RequestProject.Spine.AlgebraicTopology.RelativeChains
import RequestProject.Spine.AlgebraicTopology.SkeletalAttachment
import RequestProject.Spine.Nerve.Controls.GeneratorProbe

/-!
# Task 14, WP17 : consistency controls

These are **controls**, not substitutes for the general theorems.  Two of them compare the
project's machinery with the concrete computations of Nakahara, *Geometry, Topology and
Physics*, 2nd ed., Chapter 3 (see `TASK14_TOPOLOGY_SOURCES.md` for the exact pages); two more
are smoke tests of the WP3 and WP7 constructions introduced in Task 14.

| control | Nakahara reference | status |
| --- | --- | --- |
| filled triangle: `H_{>0} = 0` | Example 3.9, PDF p. 128 | `nakahara_filled_triangle` |
| boundary of a triangle (`S¹`): `H₁ ≠ 0` | Example 3.8, PDF p. 127 | `nakahara_circle_nontrivial` |
| boundary of a tetrahedron (`S²`) | Exercise 3.3, PDF p. 129 | **not performed** — see below |
| relative chains of `(X,X)` vanish | — | `relChain_self_subsingleton` |
| the `r`-cells of the attachment are the nondegenerate `r`-simplices | — | `cellIndexTopEquiv` |

**Boundary of a tetrahedron.**  Nakahara states `H₂(S²) ≅ ℤ`, `H₁(S²) = 0` only as an exercise
(Exercise 3.3) and computes no simplicial-set model; the project has no machinery for computing
the homology of `∂Δ[3]` as a simplicial set (its degenerate simplices are infinite in each
degree), and building one is not on the Task-14 dependency path.  This control is therefore
**not performed**, and is recorded as such rather than silently omitted.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet NerveGeom SpineTask13

universe u

namespace SpineTask14

/-! ## Nakahara controls -/

/-- **Control (Nakahara, Example 3.9 — the filled triangle).**  Every positive-degree cycle of
the simplicial `ℤ₂`-chain complex of `Δ[2]` is a boundary, i.e. `H_{>0}(Δ[2];ℤ₂) = 0`.  This
agrees with Nakahara's computation `H₁(K) = 0` for `K` the filled triangle.  (The project
result is the general `Δ[n]`; only `n = 2` is Nakahara's example.) -/
theorem nakahara_filled_triangle (p : ℕ) (z : SSetChain (Δ[2] : SSet.{0}) (p + 1))
    (hz : sSetBoundary (Δ[2] : SSet.{0}) p z = 0) :
    ∃ w, sSetBoundary (Δ[2] : SSet.{0}) (p + 1) w = z :=
  ⟨_, SpineTask12.stdSimplex_chain_acyclic 2 p z hz⟩

/-- **Control (Nakahara, Example 3.8 — the boundary of a triangle, a triangulation of `S¹`).**
`∂Δ[2]` carries a `1`-cycle that is not a boundary, so `H₁(∂Δ[2];ℤ₂) ≠ 0`.  Nakahara computes
`H₁ ≅ ℤ` with integral coefficients; over `ℤ₂` the corresponding statement is non-vanishing,
which is what is checked here.  The *exact* isomorphism `H₁ ≅ ℤ₂` is **not** claimed. -/
theorem nakahara_circle_nontrivial :
    sSetBoundary SpineTask12.circleModel 0 SpineTask12.fundamentalCycle = 0 ∧
      ∀ w, sSetBoundary SpineTask12.circleModel 1 w ≠ SpineTask12.fundamentalCycle :=
  SpineTask12.boundary2_homology_one_ne_zero

/-! ## Smoke tests for the Task-14 constructions -/

/-- **Control.**  The relative chain module of the pair `(X,X)` vanishes. -/
theorem relChain_self_subsingleton (X : SSet.{u}) (q : ℕ) :
    Subsingleton (RelChainMod (𝟙 X) q) := by
  have hid : sSetChainMap (𝟙 X) q = LinearMap.id := by
    ext x
    simp [sSetChainMap]
  have htop : LinearMap.range (sSetChainMap (𝟙 X) q) = ⊤ := by
    rw [hid]
    exact LinearMap.range_eq_top.2 Function.surjective_id
  rw [show RelChainMod (𝟙 X) q
      = (SSetChain X q ⧸ LinearMap.range (sSetChainMap (𝟙 X) q)) from rfl, htop]
  infer_instance

/-- **Control.**  In the critical dimension `n = r` the cells attached by WP3 are exactly the
nondegenerate `r`-simplices: the only epimorphism `⦋r⦌ ⟶ ⦋r⦌` is the identity.  This is the
consistency check against Task 13, where `N_r(K^{(r)},K^{(r-1)})` was proved to be free on
`NDeg_r(K)`. -/
def cellIndexTopEquiv (X : SSet.{u}) (r : ℕ) : CellIndex X r r ≃ X.nonDegenerate r where
  toFun z := z.1
  invFun σ := ⟨σ, 𝟙 _, inferInstance⟩
  left_inv := by
    rintro ⟨σ, f, hf⟩
    have hfid : f = 𝟙 _ := SimplexCategory.eq_id_of_epi f
    subst hfid
    rfl
  right_inv _ := rfl

end SpineTask14
