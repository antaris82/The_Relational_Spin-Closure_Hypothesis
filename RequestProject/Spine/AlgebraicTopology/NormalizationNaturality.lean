import RequestProject.Spine.AlgebraicTopology.Normalization
import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-!
# Task 21, source-side input : naturality of the normalization homotopy

Task 13 built, for every simplicial set `S`, the Dold–Kan data on the project's own
unnormalized `ℤ₂`-chain complex:

* the projector `SpineTask13.proj S q` (`P∞`), which is natural (`normInc_natural`);
* the contracting homotopy `SpineTask13.normHtpy S q`, with `∂h + h∂ = id + P∞`
  (`normHtpy_zero`, `normHtpy_succ`).

What Task 13 did *not* record is that the homotopy is natural as well.  That is the single
missing ingredient needed to descend the normalization to a **relative** chain complex, and it
is supplied here.  Nothing else is added: the homotopy is the pinned Mathlib
`AlgebraicTopology.DoldKan.homotopyPInftyToId`, and naturality is proved by the same induction
that defines it.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
open Opposite Simplicial AlgebraicTopology AlgebraicTopology.DoldKan NerveGeom SpineTask13

universe u

namespace SpineTask21

/-- **The homotopies `P q ≃ id` of the Dold–Kan machinery are natural.** -/
theorem homotopyPToId_hom_naturality {C : Type*} [Category C] [Preadditive C]
    {X Y : SimplicialObject C} (f : X ⟶ Y) (q n : ℕ) :
    f.app (op ⦋n⦌) ≫ (homotopyPToId Y q).hom n (n + 1)
      = (homotopyPToId X q).hom n (n + 1) ≫ f.app (op ⦋n + 1⦌) := by
  induction q with
  | zero => simp [homotopyPToId]
  | succ q ih =>
    simp only [homotopyHσToZero, Homotopy.trans_hom, Homotopy.ofEq_hom, Pi.zero_apply,
      Homotopy.add_hom, Homotopy.compLeft_hom, add_zero, Homotopy.nullHomotopy'_hom,
      ComplexShape.down_Rel, homotopyPToId, dif_pos, zero_add, comp_add, add_comp]
    rw [ih, ← assoc, P_f_naturality, assoc, assoc, hσ'_naturality q n (n + 1) rfl f]

/-- The homotopy `P∞ ≃ id` is natural. -/
theorem homotopyPInftyToId_hom_naturality {C : Type*} [Category C] [Preadditive C]
    {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    f.app (op ⦋n⦌) ≫ (homotopyPInftyToId Y).hom n (n + 1)
      = (homotopyPInftyToId X).hom n (n + 1) ≫ f.app (op ⦋n + 1⦌) :=
  homotopyPToId_hom_naturality f (n + 2) n

/-- **Naturality of the normalization homotopy** of Task 13: for every morphism of simplicial
sets `φ : S ⟶ T`, `C(φ) ∘ h_S = h_T ∘ C(φ)`. -/
theorem normHtpy_natural {S T : SSet.{u}} (φ : S ⟶ T) (q : ℕ) (x : SSetChain S q) :
    sSetChainMap φ (q + 1) (normHtpy S q x) = normHtpy T q (sSetChainMap φ q x) := by
  have h := congrArg ModuleCat.Hom.hom
    (homotopyPInftyToId_hom_naturality (freeSSetModuleMap φ) q)
  have hx := congrFun (congrArg DFunLike.coe h) x
  simpa using hx.symm

end SpineTask21
