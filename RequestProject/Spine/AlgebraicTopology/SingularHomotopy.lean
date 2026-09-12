import RequestProject.Spine.AlgebraicTopology.Contractible
import RequestProject.Spine.AlgebraicTopology.SingularHomology

/-!
# Task 19, WP1 : homotopy invariance and transport of singular homology

Task 18 proves the chain-level prism identity and packages it as
`SpineTask18.homologyMap_eq_of_prism`, but only for the two ends `endMap H e0`, `endMap H e1`
of an explicit prism homotopy.  This module turns that into the statements that the rest of
Task 19 uses:

* `SpineTask19.homologyMap_eq_of_homotopic` — homotopic maps induce the same map on singular
  homology;
* `SpineTask19.isIso_homologyMap_of_homotopyEquiv` — a homotopy equivalence induces isomorphisms
  in every degree;
* `SpineTask19.singHomologyIsoOfHomotopyEquiv`, `SpineTask19.singHomologyIsoOfHomeo` — the
  resulting isomorphisms, the second being the transport used for Task 17's homeomorphisms.
-/

noncomputable section

open CategoryTheory NerveGeom SpineTask18

universe u

namespace SpineTask19

variable {X Y Z : TopCat.{u}}

/-- The singular chain complex, as a functor on spaces. -/
abbrev singCxFunctor : TopCat.{u} ⥤ Cx.{u} :=
  TopCat.toSSet ⋙ SpineTask14.sSetChainComplexFunctor

theorem singCxFunctor_map (g : X ⟶ Y) : singCxFunctor.map g = singCxMap g := rfl

/-- **Homotopy invariance.** -/
theorem homologyMap_eq_of_homotopy {f g : X ⟶ Y}
    (h : (ConcreteCategory.hom f).Homotopy (ConcreteCategory.hom g)) (q : ℕ) :
    HomologicalComplex.homologyMap (singCxMap f) q
      = HomologicalComplex.homologyMap (singCxMap g) q := by
  have h0 : endMap (ofHomotopy h) e0 = f := by
    rw [endMap, endMapC_ofHomotopy_e0]
    rfl
  have h1 : endMap (ofHomotopy h) e1 = g := by
    rw [endMap, endMapC_ofHomotopy_e1]
    rfl
  have hp := homologyMap_eq_of_prism (ofHomotopy h) q
  rwa [h0, h1] at hp

/-- **Homotopy invariance**, in `Homotopic` form. -/
theorem homologyMap_eq_of_homotopic {f g : X ⟶ Y}
    (h : (ConcreteCategory.hom f).Homotopic (ConcreteCategory.hom g)) (q : ℕ) :
    HomologicalComplex.homologyMap (singCxMap f) q
      = HomologicalComplex.homologyMap (singCxMap g) q :=
  homologyMap_eq_of_homotopy h.some q

theorem homologyMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (q : ℕ) :
    HomologicalComplex.homologyMap (singCxMap (f ≫ g)) q
      = HomologicalComplex.homologyMap (singCxMap f) q
        ≫ HomologicalComplex.homologyMap (singCxMap g) q := by
  rw [← singCxFunctor_map, singCxFunctor.map_comp, HomologicalComplex.homologyMap_comp]
  rfl

theorem homologyMap_id (q : ℕ) :
    HomologicalComplex.homologyMap (singCxMap (𝟙 X)) q = 𝟙 _ := by
  have h : singCxMap (𝟙 X) = 𝟙 (singCx X) := singCxFunctor.map_id X
  rw [h, HomologicalComplex.homologyMap_id]

/-- **A homotopy equivalence induces isomorphisms on singular homology.** -/
theorem isIso_homologyMap_of_homotopyEquiv (e : ContinuousMap.HomotopyEquiv ↥X ↥Y) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (singCxMap (TopCat.ofHom e.toFun)) q) := by
  set F : X ⟶ Y := TopCat.ofHom e.toFun with hF
  set G : Y ⟶ X := TopCat.ofHom e.invFun with hG
  have hFG : HomologicalComplex.homologyMap (singCxMap F) q
      ≫ HomologicalComplex.homologyMap (singCxMap G) q = 𝟙 _ := by
    rw [← homologyMap_comp, ← homologyMap_id (X := X) q]
    refine homologyMap_eq_of_homotopic ?_ q
    exact e.left_inv
  have hGF : HomologicalComplex.homologyMap (singCxMap G) q
      ≫ HomologicalComplex.homologyMap (singCxMap F) q = 𝟙 _ := by
    rw [← homologyMap_comp, ← homologyMap_id (X := Y) q]
    refine homologyMap_eq_of_homotopic ?_ q
    exact e.right_inv
  exact ⟨HomologicalComplex.homologyMap (singCxMap G) q, hFG, hGF⟩

/-- The isomorphism of singular homology induced by a homotopy equivalence. -/
def singHomologyIsoOfHomotopyEquiv (e : ContinuousMap.HomotopyEquiv ↥X ↥Y) (q : ℕ) :
    (singCx X).homology q ≅ (singCx Y).homology q :=
  haveI := isIso_homologyMap_of_homotopyEquiv e q
  asIso (HomologicalComplex.homologyMap (singCxMap (TopCat.ofHom e.toFun)) q)

theorem singHomologyIsoOfHomotopyEquiv_hom (e : ContinuousMap.HomotopyEquiv ↥X ↥Y) (q : ℕ) :
    (singHomologyIsoOfHomotopyEquiv e q).hom
      = HomologicalComplex.homologyMap (singCxMap (TopCat.ofHom e.toFun)) q := rfl

/-- The isomorphism of singular homology induced by a homeomorphism. -/
def singHomologyIsoOfHomeo (h : ↥X ≃ₜ ↥Y) (q : ℕ) :
    (singCx X).homology q ≅ (singCx Y).homology q :=
  singHomologyIsoOfHomotopyEquiv h.toHomotopyEquiv q

end SpineTask19
