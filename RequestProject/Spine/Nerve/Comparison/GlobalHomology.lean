import RequestProject.Spine.Nerve.Comparison.RelJ
import RequestProject.Spine.Nerve.Comparison.SkeletalInduction
import RequestProject.Spine.Nerve.Skeleton.SkeletalSupport
import RequestProject.Spine.AlgebraicTopology.ExhaustiveHomology

/-!
# The global canonical simplicial–singular comparison

The skeletal induction gives, for every simplicial set `K` and every `r`, that the frozen
canonical map

`J = C_*(η) : C_*^{simp}(Sk K r; ℤ₂) ⟶ C_*^{sing}(|Sk K r|; ℤ₂)`

is a homology isomorphism (`SpineTask16.skeletalInduction`, whose relative hypothesis is
discharged by `SpineTask24.relJIsIso`).  This module assembles those finite-stage statements
into the *global* one, for `J = C_*(η_K)` itself and with **no finite-dimensionality
hypothesis**.

The assembly is the elementary finite-support argument, carried out once and generically in
`RequestProject.Spine.AlgebraicTopology.ExhaustiveHomology`.  What has to be supplied here is
that the two chain complexes really are exhausted by the skeletal families:

* on the simplicial side this is unconditional and purely combinatorial: in degree `q` the
  inclusion `Sk K (q+1) ⟶ K` is *bijective* on `q`-simplices (`skeleton_app_bijective`), so
  every simplicial chain of degree `q` already lives in `Sk K (q+1)`;
* on the singular side it is the point-set statement `NerveSkeleton.SkeletalSupport K` of
  `RequestProject.Spine.Nerve.Skeleton.SkeletalSupport`: `|Sk K r| → |K|` is injective and
  every singular simplex of `|K|` factors through some `|Sk K r|`.  Both halves are theorems:
  `NerveSkeleton.skeletalSupport` proves the second one for every simplicial set, from the
  compactness of `Δ^q_top` and `NerveTopology.exists_skeletal_factorization`.

The main theorem is therefore the **unconditional** `globalHomologyIso`; the version carrying
the point-set hypothesis, `globalHomologyIso_of_skeletalSupport`, is kept as the intermediate
step.  The finite-dimensional theorem `SpineTask16.finiteDimensional_homologyIso` is unchanged,
is *not* used here, and is subsumed by `globalHomologyIso`
(`homologyIso_of_hasDimensionLT` records the subsumption).
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet SpineTask13 SpineTask14 NerveSkeleton

universe u

namespace NerveComparison

variable (K : SSet.{u})

/-- The simplicial chain complexes of the skeleta. -/
abbrev simpFamily : ℕ ⥤ ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ :=
  NerveSkeleton.skFunctor K ⋙ sSetChainComplexFunctor

/-- The singular chain complexes of the realized skeleta. -/
abbrev singFamily : ℕ ⥤ ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ :=
  NerveSkeleton.skFunctor K ⋙ SSet.toTop ⋙ TopCat.toSSet ⋙ sSetChainComplexFunctor

/-- The simplicial chain complex of `K`. -/
abbrev simpCx : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ := sSetChainComplexFunctor.obj K

/-- The singular chain complex of `|K|`. -/
abbrev singCx : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ :=
  sSetChainComplexFunctor.obj (Sing K)

/-- The cocone of simplicial chain complexes of the skeleta over the simplicial chain complex
of `K`. -/
def simpCocone : simpFamily K ⟶ (Functor.const ℕ).obj (simpCx K) where
  app r := sSetChainComplexFunctor.map (skIncl K r)
  naturality _ _ _ := by
    dsimp
    rw [← Functor.map_comp, Category.comp_id]
    rfl

/-- The cocone of singular chain complexes of the realized skeleta over the singular chain
complex of `|K|`. -/
def singCocone : singFamily K ⟶ (Functor.const ℕ).obj (singCx K) where
  app r := sSetChainComplexFunctor.map (singSkIncl K r)
  naturality _ _ _ := by
    dsimp
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, Category.comp_id]
    rfl

/-- The frozen canonical comparison on the skeleta, as a map of families. -/
def famJ : simpFamily K ⟶ singFamily K where
  app r := sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk K r))
  naturality {r s} h := by
    dsimp
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg sSetChainComplexFunctor.map (sSetTopAdj.unit.naturality _)

/-- The frozen canonical comparison for `K` itself. -/
abbrev globalJ : simpCx K ⟶ singCx K := sSetChainComplexFunctor.map (sSetTopAdj.unit.app K)

/-- The comparison square: the canonical map is natural in `K`. -/
theorem famJ_comp_singCocone (r : ℕ) :
    (famJ K).app r ≫ (singCocone K).app r = (simpCocone K).app r ≫ globalJ K := by
  dsimp [famJ, singCocone, simpCocone]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg sSetChainComplexFunctor.map (sSetTopAdj.unit.naturality (skIncl K r)).symm

/-! ## Degreewise behaviour of a linearised map of simplicial sets -/

/-- The chain map attached to a morphism of simplicial sets is `Finsupp.mapDomain` on
simplices. -/
theorem chainMap_apply {S T : SSet.{u}} (f : S ⟶ T) (q : ℕ)
    (x : (sSetChainComplexFunctor.obj S).X q) :
    ((sSetChainComplexFunctor.map f).f q).hom x = Finsupp.mapDomain (f.app (op ⦋q⦌)) x := rfl

/-- If a morphism of simplicial sets is injective in dimension `q`, so is the induced map of
chains. -/
theorem chainMap_injective {S T : SSet.{u}} (f : S ⟶ T) (q : ℕ)
    (hf : Function.Injective (f.app (op ⦋q⦌))) :
    Function.Injective (((sSetChainComplexFunctor.map f).f q).hom) :=
  Finsupp.mapDomain_injective hf

/-- If a morphism of simplicial sets is bijective in dimension `q`, the induced map of chains is
surjective. -/
theorem chainMap_surjective {S T : SSet.{u}} (f : S ⟶ T) (q : ℕ)
    (hf : Function.Bijective (f.app (op ⦋q⦌))) :
    Function.Surjective (((sSetChainComplexFunctor.map f).f q).hom) := by
  intro x
  set e : (S _⦋q⦌) ≃ (T _⦋q⦌) := Equiv.ofBijective _ hf with he
  refine ⟨Finsupp.equivMapDomain e.symm x, ?_⟩
  have h1 : Finsupp.mapDomain (f.app (op ⦋q⦌)) (Finsupp.equivMapDomain e.symm x)
      = Finsupp.equivMapDomain e (Finsupp.equivMapDomain e.symm x) :=
    (Finsupp.equivMapDomain_eq_mapDomain e _).symm
  have h2 : Finsupp.equivMapDomain e (Finsupp.equivMapDomain e.symm x) = x := by
    rw [← Finsupp.equivMapDomain_trans]
    simp
  rw [chainMap_apply, h1, h2]

/-! ## The simplicial side is exhausted by the skeleta, unconditionally -/

/-- The skeletal inclusion is injective in every dimension. -/
theorem skIncl_app_injective (r : ℕ) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((skIncl K r).app n) := fun _ _ h => Subtype.ext h

/-- In dimension `q` the inclusion of the `(q+1)`-skeleton is bijective: every `q`-simplex of
`K` lies in `Sk K (q+1)`. -/
theorem skIncl_app_bijective (q : ℕ) :
    Function.Bijective ((skIncl K (q + 1)).app (op ⦋q⦌)) :=
  ⟨skIncl_app_injective K (q + 1) _, fun x => ⟨⟨x, K.mem_skeleton x (Nat.lt_succ_self q)⟩, rfl⟩⟩

/-- **Simplicial exhaustion.**  Every simplicial chain of degree `q` comes from the
`(q+1)`-skeleton. -/
theorem simp_exhaustive (i : ℕ) (x : (simpCx K).X i) :
    ∃ (r : ℕ) (y : ((simpFamily K).obj r).X i),
      (((simpCocone K).app r).f i).hom y = x :=
  ⟨i + 1, (chainMap_surjective (skIncl K (i + 1)) i (skIncl_app_bijective K i) x).choose,
    (chainMap_surjective (skIncl K (i + 1)) i (skIncl_app_bijective K i) x).choose_spec⟩

/-- **Simplicial injectivity.**  The chains of a skeleton inject into the chains of `K`. -/
theorem simp_injective (r i : ℕ) :
    Function.Injective ((((simpCocone K).app r).f i).hom) :=
  chainMap_injective _ _ (skIncl_app_injective K r _)

/-! ## The singular side, under the point-set input -/

/-- **Singular injectivity**: unconditional, since the realized skeleta are subspaces. -/
theorem sing_injective (r i : ℕ) :
    Function.Injective ((((singCocone K).app r).f i).hom) :=
  chainMap_injective _ _ (singSkIncl_injective K r _)

/-- **Singular exhaustion**, from `SkeletalSupport`: a singular chain has finite support, each
of whose simplices lies in some skeleton; the largest of those indices works for the whole
chain. -/
theorem sing_exhaustive_aux (h : SkeletalSupport K) (i : ℕ)
    (x : (Sing K) _⦋i⦌ →₀ ZMod 2) :
    ∃ (r : ℕ) (y : (Sing (Sk K r)) _⦋i⦌ →₀ ZMod 2),
      Finsupp.mapDomain ((singSkIncl K r).app (op ⦋i⦌)) y = x := by
  classical
  choose st τ hτ using h i
  refine ⟨x.support.sup st, ?_⟩
  set r : ℕ := x.support.sup st with hr
  -- every simplex of the support already lies in `Sk K r`
  have hmem : ∀ σ ∈ x.support,
      ∃ ψ : (Sing (Sk K r)) _⦋i⦌, (singSkIncl K r).app (op ⦋i⦌) ψ = σ := by
    intro σ hσ
    have hle : st σ ≤ r := Finset.le_sup hσ
    refine ⟨(TopCat.toSSet.map (SSet.toTop.map ((NerveSkeleton.skFunctor K).map (homOfLE hle)))).app
      (op ⦋i⦌) (τ σ), ?_⟩
    have hcomp : (TopCat.toSSet.map (SSet.toTop.map ((NerveSkeleton.skFunctor K).map (homOfLE hle))))
        ≫ singSkIncl K r = singSkIncl K (st σ) := by
      dsimp [singSkIncl]
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
    exact (congrFun (congrArg (fun m : Sing (Sk K (st σ)) ⟶ Sing K => m.app (op ⦋i⦌)) hcomp)
      (τ σ)).trans (hτ σ)
  choose ψ hψ using hmem
  refine ⟨∑ σ ∈ x.support.attach, Finsupp.single (ψ σ.1 σ.2) (x σ.1), ?_⟩
  rw [← Finsupp.lmapDomain_apply (ZMod 2) (ZMod 2), map_sum]
  have hsingle : ∀ σ ∈ x.support.attach,
      Finsupp.lmapDomain (ZMod 2) (ZMod 2) ((singSkIncl K r).app (op ⦋i⦌))
          (Finsupp.single (ψ σ.1 σ.2) (x σ.1))
        = Finsupp.single σ.1 (x σ.1) := by
    intro σ _
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hψ σ.1 σ.2]
  rw [Finset.sum_congr rfl hsingle,
    Finset.sum_attach _ (fun σ => Finsupp.single σ (x σ))]
  exact Finsupp.sum_single x

/-- **Singular exhaustion**, from `SkeletalSupport`: a singular chain has finite support, each
of whose simplices lies in some skeleton; the largest of those indices works for the whole
chain. -/
theorem sing_exhaustive (h : SkeletalSupport K) (i : ℕ) (x : (singCx K).X i) :
    ∃ (r : ℕ) (y : ((singFamily K).obj r).X i),
      (((singCocone K).app r).f i).hom y = x :=
  sing_exhaustive_aux K h i x

/-! ## The global comparison theorem -/

/-- **The global canonical simplicial–singular comparison**, for an arbitrary simplicial set and
in every degree, given the point-set input `SkeletalSupport K`.  No finite-dimensionality,
finiteness or `Fintype` hypothesis appears. -/
theorem globalHomologyIso_of_skeletalSupport (h : SkeletalSupport K) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (sSetTopAdj.unit.app K)) q) := by
  have hstage : ∀ r q, IsIso (HomologicalComplex.homologyMap ((famJ K).app r) q) := fun r q =>
    SpineTask16.skeletalInduction K (fun r => SpineTask24.relJIsIso K r) r q
  refine SpineExhaustion.isIso_homologyMap_of_exhaustive (simpCocone K) (singCocone K)
    (famJ K) (globalJ K) ?_ ?_ ?_ ?_ ?_ hstage q
  · exact famJ_comp_singCocone K
  · exact simp_injective K
  · exact sing_injective K
  · exact simp_exhaustive K
  · exact sing_exhaustive K h

/-- **The global canonical simplicial–singular comparison, unconditionally.**  For every
simplicial set `K` and every degree `q` the frozen canonical map
`J_K = C_*(η_K) : C_*^{simp}(K;ℤ₂) ⟶ C_*^{sing}(|K|;ℤ₂)` is a homology isomorphism.  There is
no dimension bound, no finiteness hypothesis and no replacement map. -/
theorem globalHomologyIso (K : SSet.{u}) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (sSetTopAdj.unit.app K)) q) :=
  globalHomologyIso_of_skeletalSupport K (NerveSkeleton.skeletalSupport K) q

/-- The finite-dimensional comparison theorem `SpineTask16.finiteDimensional_homologyIso` is
subsumed by `globalHomologyIso`: neither the dimension bound `[K.HasDimensionLT d]` nor the
relative hypothesis `RelJIsIso` is needed any more.  The hypotheses are retained here only to
exhibit the exact statement that is subsumed, and are unused. -/
theorem homologyIso_of_hasDimensionLT (K : SSet.{u}) (d : ℕ) [K.HasDimensionLT d]
    (_hrel : ∀ r, SpineTask14.RelJIsIso K r) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (sSetTopAdj.unit.app K)) q) :=
  globalHomologyIso K q

end NerveComparison
