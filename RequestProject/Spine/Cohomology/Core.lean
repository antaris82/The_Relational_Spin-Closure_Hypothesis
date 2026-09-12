import RequestProject.Spine.Cohomology.Cochain
import RequestProject.Spine.Cohomology.Coboundary
import RequestProject.Spine.Cohomology.Cohomology
import RequestProject.Spine.Cohomology.Functorial
import RequestProject.Spine.Cohomology.AlexanderWhitney
import RequestProject.Spine.Cohomology.Cup
import RequestProject.Spine.Cohomology.CupDescent
import RequestProject.Spine.Cohomology.CechBridgeSpec
import RequestProject.Spine.Cohomology.CharTwo
import RequestProject.Spine.Cohomology.PrismMaps
import RequestProject.Spine.Cohomology.Prism

/-!
# Spine / Cohomology : the native singular mod-2 cohomology layer (Task 5)

This module is the endpoint of the Task-5 layer: a genuine singular cohomology theory with
`ℤ/2` coefficients, constructed **inside** the Spine from Mathlib primitives only.

* `Cochain.lean` (WP2) — singular simplices as the values of Mathlib's singular simplicial set
  `TopCat.toSSet`, reindexing along simplex-category morphisms, the face operators, and the
  cochain modules `Cⁿ(X;ℤ₂) = Sing_n X → ZMod 2` (a genuine function type, with the `Pi`
  module structure; never an opaque carrier and never typeclass data).
* `Coboundary.lean` (WP3) — the coboundary `δ : Cⁿ → Cⁿ⁺¹` as the unsigned sum over faces
  (unsigned because `-1 = 1` in `ZMod 2`), as a `ZMod 2`-linear map, and the theorem
  `δ ∘ δ = 0`, proved from the cosimplicial identity `SimplexCategory.δ_comp_δ`.
* `Cohomology.lean` (WP4) — `Zⁿ = ker δ`, `Bⁿ = im δ` (with `B⁰ = 0`), the theorem
  `Bⁿ ⊆ Zⁿ`, and `Hⁿ(X;ℤ₂) = Zⁿ/Bⁿ` as an actual quotient module, degree-generic (hence in
  particular for `n = 0,1,2,3,4`).
* `Functorial.lean` (WP5) — the pullback `f* : Cⁿ(Y;ℤ₂) → Cⁿ(X;ℤ₂)` of a continuous map, its
  commutation with `δ` (from naturality of `TopCat.toSSet`), the induced map on `Hⁿ`, and the
  two functor laws.
* `AlexanderWhitney.lean`, `Cup.lean`, `CupDescent.lean` (WP6) — the front/back inclusions, the
  Alexander–Whitney product on cochains, the Leibniz rule `δ(f ⌣ g) = δf ⌣ g + f ⌣ δg`, and
  the descended products `H¹ × H¹ → H²` and `H² × H² → H⁴` with their cup squares.
* `CechBridgeSpec.lean` (WP8) — the *specification* of the still-missing comparison between the
  Task-3 fixed-cover Čech obstruction class and `H²_sing(X;ℤ₂)`, together with the conditional
  transport theorem.  No comparison is constructed, and the two carriers are **not** identified.

**What is not claimed.**  No Stiefel–Whitney class, no `w₂(TM)`, no fundamental class, no
Poincaré duality, no Wu class, no Steenrod operations, no classifying space, no Thom space, no
principal-bundle framework.  The relationship of this layer to the external Lean projects that
were inspected is documented in `TASK05_EXTERNAL_SOURCES.md`; no external project is imported
or copied, and the import closure of this module consists of Mathlib and Spine modules only.
-/

/-! ## Axiom audit of the Task-5 principal declarations

Each of the following must report only `[propext, Classical.choice, Quot.sound]`. -/

#print axioms Mod2Cohomology.Cochain
#print axioms Mod2Cohomology.face_face
#print axioms Mod2Cohomology.coboundary_coboundary
#print axioms Mod2Cohomology.d_comp_d
#print axioms Mod2Cohomology.coboundaries_le_cocycles
#print axioms Mod2Cohomology.Cohomology
#print axioms Mod2Cohomology.mk_eq_zero_iff
#print axioms Mod2Cohomology.pullback_d
#print axioms Mod2Cohomology.Hmap
#print axioms Mod2Cohomology.Hmap_id
#print axioms Mod2Cohomology.Hmap_comp
#print axioms Mod2Cohomology.coboundary_cup
#print axioms Mod2Cohomology.cup_cocycle
#print axioms Mod2Cohomology.cupH11
#print axioms Mod2Cohomology.cupH22
#print axioms Mod2Cohomology.cupSquare1
#print axioms Mod2Cohomology.cupSquare2
#print axioms Mod2Cohomology.comparison_vanishing_iff_exists_coherent
