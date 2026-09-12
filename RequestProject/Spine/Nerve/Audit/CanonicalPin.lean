import RequestProject.Spine.Nerve.Basic.CanonicalMap
import Mathlib.AlgebraicTopology.DoldKan.Normalized
import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Task 13, WP2/WP7/WP10/WP16 : compile probes for the pinned-library audit

Everything in this module is a **compile probe**: each declaration exists only to make the
pinned Mathlib v4.28.0 declaration it names part of the build, so that the classification in
`TASK13_NORMALIZED_SKELETAL_COMPARISON.md` is machine-checked rather than asserted.  Nothing
in the Spine depends on this module.

A probe can only certify *presence*.  Absence (no singular relative homology, no excision, no
long exact sequence of a pair, no CW/cell-attachment decomposition of `SSet.toTop.obj X`) is
certified in the audit document by exhaustive name searches over the pinned environment; it
cannot be witnessed by a Lean declaration.

## WP2 — normalization infrastructure (all `PINNED_DIRECT`)

`alternatingFaceMapComplex`, `normalizedMooreComplex`, `inclusionOfMooreComplexMap`,
`DoldKan.PInfty`, `DoldKan.QInfty`, `DoldKan.homotopyPInftyToId`, `DoldKan.σ_comp_PInfty`,
`DoldKan.decomposition_Q`, `DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi`,
`DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`,
`CategoryTheory.Abelian.DoldKan.equivalence`.

## WP16 — quasi-isomorphism vs. chain-homotopy equivalence

The pin has **no** theorem "quasi-isomorphism of complexes of vector spaces ⇒ chain-homotopy
equivalence".  What it has is the K-projective machinery for `CochainComplex C ℤ`
(`CochainComplex.isKProjective_of_projective`, `CochainComplex.IsKProjective.Qh_map_bijective`)
from which that statement is derivable; hence the classification `PINNED_ADAPTABLE`.
-/

noncomputable section

namespace SpineTask13

open CategoryTheory Opposite Simplicial AlgebraicTopology AlgebraicTopology.DoldKan

universe u

/-! ## WP2 probes -/

/-- Pinned: the normalized Moore complex functor. -/
def probeMooreComplex : SimplicialObject (ModuleCat.{u} (ZMod 2)) ⥤
    ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ :=
  normalizedMooreComplex (ModuleCat.{u} (ZMod 2))

/-- Pinned: the inclusion of the Moore complex into the alternating face map complex. -/
def probeMooreInclusion (Y : SimplicialObject (ModuleCat.{u} (ZMod 2))) :
    (normalizedMooreComplex (ModuleCat.{u} (ZMod 2))).obj Y ⟶
      (alternatingFaceMapComplex (ModuleCat.{u} (ZMod 2))).obj Y :=
  inclusionOfMooreComplexMap Y

/-- **Pinned, `PINNED_DIRECT`**: the *subcomplex* form of the normalization theorem — the Moore
complex is chain-homotopy equivalent to the alternating face map complex.  This is the pinned
statement closest to Objective A; it is about the Moore **subcomplex**, whereas Objective A
needs the **quotient** by the degeneracies, which the pin does not provide. -/
def probeMooreHomotopyEquiv (Y : SimplicialObject (ModuleCat.{u} (ZMod 2))) :
    HomotopyEquiv ((normalizedMooreComplex (ModuleCat.{u} (ZMod 2))).obj Y)
      ((alternatingFaceMapComplex (ModuleCat.{u} (ZMod 2))).obj Y) :=
  homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex

/-- Pinned: the Dold–Kan equivalence for an abelian category. -/
def probeDoldKanEquivalence :
    SimplicialObject (ModuleCat.{u} (ZMod 2)) ≌ ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ :=
  CategoryTheory.Abelian.DoldKan.equivalence

/-- Pinned: `N₁` is the normalized Moore complex, in the Karoubi envelope. -/
def probeN₁Iso :
    (DoldKan.N₁ : SimplicialObject (ModuleCat.{u} (ZMod 2)) ⥤ _) ≅
      normalizedMooreComplex (ModuleCat.{u} (ZMod 2)) ⋙
        Idempotents.toKaroubi (ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ) :=
  N₁_iso_normalizedMooreComplex_comp_toKaroubi (ModuleCat.{u} (ZMod 2))

/-! ## WP16 probes : the algebraic bridge -/

/-- Pinned: a complex of projectives which is strictly bounded above is K-projective. -/
theorem probeIsKProjective (K : CochainComplex (ModuleCat.{u} (ZMod 2)) ℤ) (d : ℤ)
    [K.IsStrictlyLE d] [∀ n : ℤ, Projective (K.X n)] : K.IsKProjective :=
  CochainComplex.isKProjective_of_projective K d

/-- Pinned: for a K-projective complex, the localisation functor from the homotopy category to
the derived category is bijective on morphisms.  This is the pinned ingredient from which
"quasi-isomorphism between complexes of vector spaces is a chain-homotopy equivalence" is
derivable; the statement itself is **not** in the pin. -/
theorem probeQhBijective [HasDerivedCategory.{u} (ModuleCat.{u} (ZMod 2))]
    (K : CochainComplex (ModuleCat.{u} (ZMod 2)) ℤ)
    (L : HomotopyCategory (ModuleCat.{u} (ZMod 2)) (ComplexShape.up ℤ)) [K.IsKProjective] :
    Function.Bijective (DerivedCategory.Qh.map (X := (HomotopyCategory.quotient _ _).obj K)
      (Y := L)) :=
  CochainComplex.IsKProjective.Qh_map_bijective K L

/-- Pinned: free `ℤ₂`-modules — the degreewise objects of every complex in this project — are
projective. -/
instance probeFreeProjective (α : Type u) : Projective (ModuleCat.of (ZMod 2) (α →₀ ZMod 2)) :=
  inferInstance

/-! ## Axiom audit of the Task-13 principal declarations -/

#print axioms SpineTask13.afmc_d_hom
#print axioms SpineTask13.degenSubmodule
#print axioms SpineTask13.boundary_degen_mem
#print axioms SpineTask13.degenSubmodule_eq_supported
#print axioms SpineTask13.normBoundary
#print axioms SpineTask13.normBoundary_comp_normBoundary
#print axioms SpineTask13.normProj_comm
#print axioms SpineTask13.normInc_comm
#print axioms SpineTask13.normProj_comp_normInc
#print axioms SpineTask13.normInc_comp_normProj
#print axioms SpineTask13.normHtpy_zero
#print axioms SpineTask13.normHtpy_succ
#print axioms SpineTask13.normProj_natural
#print axioms SpineTask13.normInc_natural
#print axioms SpineTask13.normMap_comm
#print axioms SpineTask13.normChainEquiv
#print axioms SpineTask13.degenerate_of_mem_skeleton
#print axioms SpineTask13.normChain_skeleton_subsingleton
#print axioms SpineTask13.relNormChain_subsingleton_of_lt
#print axioms SpineTask13.relNormChain_subsingleton_of_gt
#print axioms SpineTask13.relNormProj
#print axioms SpineTask13.relNormInc
#print axioms SpineTask13.relNormProj_comp_relNormInc
#print axioms SpineTask13.relNormChainEquiv
#print axioms SpineTask13.nonDegenerateSkeletonEquiv
#print axioms SpineTask13.normJ
#print axioms SpineTask13.normJ_normProj
#print axioms SpineTask13.normJ_comm
#print axioms SpineTask13.chainMap_degen_mem

end SpineTask13
