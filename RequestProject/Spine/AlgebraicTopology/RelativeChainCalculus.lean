import RequestProject.Spine.AlgebraicTopology.RelativeChains

/-!
# Composition calculus for maps of relative chain complexes

Generic homological algebra: three small lemmas saying that the relative chain map
`relChainCxMap` attached to a commuting square of simplicial maps is compatible with
composition of squares, and depends on the square only through its right-hand vertical when
the horizontal maps agree.

Nothing here mentions a nerve, a cover, a skeleton or a cell; the declarations keep their
historical `SpineTask22` namespace so that no downstream statement had to be edited.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet NerveGeom SpineTask14

universe u

namespace SpineTask22

section RelMapCalculus

variable {S T S' T' S'' T'' : SSet.{u}}

theorem relChainCxMap_square_comp (f : S ⟶ T) (f' : S' ⟶ T') (f'' : S'' ⟶ T'')
    {u : S ⟶ S'} {v : T ⟶ T'} (h : f ≫ v = u ≫ f')
    {u' : S' ⟶ S''} {v' : T' ⟶ T''} (h' : f' ≫ v' = u' ≫ f'') :
    f ≫ (v ≫ v') = (u ≫ u') ≫ f'' :=
  calc f ≫ (v ≫ v') = (f ≫ v) ≫ v' := (Category.assoc _ _ _).symm
    _ = (u ≫ f') ≫ v' := by rw [h]
    _ = u ≫ (f' ≫ v') := Category.assoc _ _ _
    _ = u ≫ (u' ≫ f'') := by rw [h']
    _ = (u ≫ u') ≫ f'' := (Category.assoc _ _ _).symm

/-- The relative comparison map depends only on the map of total objects. -/
theorem relChainCxMap_eq_of_v (f : S ⟶ T) (f' : S' ⟶ T')
    {u u' : S ⟶ S'} {v v' : T ⟶ T'} {h : f ≫ v = u ≫ f'} {h' : f ≫ v' = u' ≫ f'}
    (hv : v = v') : relChainCxMap f f' u v h = relChainCxMap f f' u' v' h' := by
  subst hv; rfl

/-- Relative comparison maps compose. -/
theorem relChainCxMap_comp (f : S ⟶ T) (f' : S' ⟶ T') (f'' : S'' ⟶ T'')
    {u : S ⟶ S'} {v : T ⟶ T'} (h : f ≫ v = u ≫ f')
    {u' : S' ⟶ S''} {v' : T' ⟶ T''} (h' : f' ≫ v' = u' ≫ f'') :
    relChainCxMap f f' u v h ≫ relChainCxMap f' f'' u' v' h'
      = relChainCxMap f f'' (u ≫ u') (v ≫ v') (relChainCxMap_square_comp f f' f'' h h') := by
  refine HomologicalComplex.hom_ext _ _ fun q => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Submodule.Quotient.mk (sSetChainMap v' q (sSetChainMap v q y))
    = Submodule.Quotient.mk (sSetChainMap (v ≫ v') q y)
  refine congrArg _ ?_
  show Finsupp.mapDomain _ (Finsupp.mapDomain _ y) = Finsupp.mapDomain _ y
  rw [← Finsupp.mapDomain_comp]
  rfl

end RelMapCalculus

end SpineTask22
