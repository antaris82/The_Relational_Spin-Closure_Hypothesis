import RequestProject.Spine.AlgebraicTopology.Normalization
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Task 14, WP7 : the minimal relative chain complex

The pinned Mathlib (v4.28.0) has **no** relative singular chain complex, no relative singular
homology and no excision (see `TASK14_SPECIALIZED_CELL_ATTACHMENT.md` for the full audit).
What it does have is the abelian-category machinery for homological complexes, including the
long exact homology sequence attached to a short exact sequence of complexes.  This module
supplies exactly the missing wrapper, and nothing more:

for a morphism of simplicial sets `f : S ⟶ T` we build

* `sSetChainComplexFunctor` — the project's own unnormalized `ℤ₂`-chain complex, packaged as a
  functor `SSet ⥤ ChainComplex (ModuleCat ℤ₂) ℕ`.  Degreewise it *is* `NerveGeom.SSetChain`
  and its differential *is* `NerveGeom.sSetBoundary` (`sSetChainComplexFunctor_d`), so this is
  not a parallel theory;
* `RelChainMod f q = C_q(T)/im C_q(f)` and `relChainCx f` — the relative complex as an honest
  quotient (WP7.1–WP7.3);
* `relProj f` — the quotient chain map;
* `relSC f` — the short complex `C_*(S) → C_*(T) → C_*(T,S)`;
* `relSC_shortExact` — **it is short exact** as soon as `f` is degreewise injective (WP7.5).

Applying this to `TopCat.toSSet.map i` for an injective continuous map `i : A ⟶ X` gives the
relative *singular* chain complex `C_*^{sing}(X,A;ℤ₂)`; applying it to a simplicial subcomplex
inclusion gives the relative simplicial one.  Both specialisations are recorded at the end.

Functoriality for maps of pairs (WP7.4) is `relChainCxMap`.

Nothing in this module assumes, or needs, excision.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial AlgebraicTopology NerveGeom SpineTask13

universe u

namespace SpineTask14

/-! ## The project's chain complex, as a functor -/

/-- The free `ℤ₂`-simplicial-module functor `S ↦ ℤ₂[S]`.  On objects it is the Task-13
`freeSSetModule`. -/
def freeSSetFunctor : SSet.{u} ⥤ SimplicialObject (ModuleCat.{u} (ZMod 2)) where
  obj S := freeSSetModule S
  map {S T} f :=
    { app := fun n => ModuleCat.ofHom (Finsupp.lmapDomain (ZMod 2) (ZMod 2) (f.app n))
      naturality := by
        intro n m g
        ext x
        show Finsupp.mapDomain _ (Finsupp.mapDomain _ _)
          = Finsupp.mapDomain _ (Finsupp.mapDomain _ _)
        rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
        exact congrArg (fun h => Finsupp.mapDomain h x) (funext fun y =>
          congrFun (f.naturality g) y) }
  map_id S := by
    ext n x
    show Finsupp.mapDomain _ x = x
    exact Finsupp.mapDomain_id
  map_comp f g := by
    ext n x
    show Finsupp.mapDomain _ x = Finsupp.mapDomain _ (Finsupp.mapDomain _ x)
    rw [← Finsupp.mapDomain_comp]
    rfl

/-- The unnormalized `ℤ₂`-chain complex of a simplicial set, as a functor. -/
def sSetChainComplexFunctor : SSet.{u} ⥤ ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ :=
  freeSSetFunctor ⋙ alternatingFaceMapComplex _

/-- Degreewise the functor is the project's own chain module. -/
theorem sSetChainComplexFunctor_X (S : SSet.{u}) (q : ℕ) :
    (sSetChainComplexFunctor.obj S).X q = ModuleCat.of (ZMod 2) (SSetChain S q) := rfl

/-- The differential is the project's own boundary. -/
theorem sSetChainComplexFunctor_d (S : SSet.{u}) (q : ℕ) :
    ((sSetChainComplexFunctor.obj S).d (q + 1) q).hom = sSetBoundary S q := afmc_d_hom S q

/-- The functorial action is the project's own chain map. -/
theorem sSetChainComplexFunctor_map_f {S T : SSet.{u}} (f : S ⟶ T) (q : ℕ) :
    ((sSetChainComplexFunctor.map f).f q).hom = sSetChainMap f q := rfl

/-! ## WP7.1–WP7.3 : the relative complex as a quotient -/

/-- **WP7.1.**  The relative chain module `C_q(T,S) = C_q(T)/im C_q(f)`. -/
abbrev RelChainMod {S T : SSet.{u}} (f : S ⟶ T) (q : ℕ) : Type u :=
  SSetChain T q ⧸ LinearMap.range (sSetChainMap f q)

/-- **WP7.2.**  The differential descends to the quotient. -/
def relBoundary {S T : SSet.{u}} (f : S ⟶ T) (q : ℕ) :
    RelChainMod f (q + 1) →ₗ[ZMod 2] RelChainMod f q :=
  Submodule.mapQ _ _ (sSetBoundary T q) (by
    rintro _ ⟨y, rfl⟩
    exact ⟨sSetBoundary S q y,
      congrFun (congrArg DFunLike.coe (sSetBoundary_naturality f q)) y⟩)

theorem relBoundary_mk {S T : SSet.{u}} (f : S ⟶ T) (q : ℕ) (x : SSetChain T (q + 1)) :
    relBoundary f q (Submodule.Quotient.mk x) = Submodule.Quotient.mk (sSetBoundary T q x) := rfl

theorem relBoundary_comp {S T : SSet.{u}} (f : S ⟶ T) (q : ℕ) :
    (relBoundary f q).comp (relBoundary f (q + 1)) = 0 := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
  show Submodule.Quotient.mk (sSetBoundary T q (sSetBoundary T (q + 1) x)) = 0
  rw [show sSetBoundary T q (sSetBoundary T (q + 1) x)
      = ((sSetBoundary T q).comp (sSetBoundary T (q + 1))) x from rfl,
    sSetBoundary_comp_sSetBoundary]
  rfl

/-- **WP7, the relative chain complex** `C_*(T,S)`. -/
def relChainCx {S T : SSet.{u}} (f : S ⟶ T) : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ :=
  ChainComplex.of (fun q => ModuleCat.of (ZMod 2) (RelChainMod f q))
    (fun q => ModuleCat.ofHom (relBoundary f q))
    (fun q => by
      rw [← ModuleCat.ofHom_comp, relBoundary_comp]
      exact ModuleCat.hom_ext rfl)

theorem relChainCx_X {S T : SSet.{u}} (f : S ⟶ T) (q : ℕ) :
    (relChainCx f).X q = ModuleCat.of (ZMod 2) (RelChainMod f q) := rfl

theorem relChainCx_d {S T : SSet.{u}} (f : S ⟶ T) (q : ℕ) :
    (relChainCx f).d (q + 1) q = ModuleCat.ofHom (relBoundary f q) :=
  ChainComplex.of_d _ _ _ q

theorem down_rel {i j : ℕ} (h : (ComplexShape.down ℕ).Rel i j) : i = j + 1 := by
  simp only [ComplexShape.down_Rel] at h
  omega

/-- **WP7.3.**  The quotient maps form a chain map `C_*(T) ⟶ C_*(T,S)`. -/
def relProj {S T : SSet.{u}} (f : S ⟶ T) :
    sSetChainComplexFunctor.obj T ⟶ relChainCx f where
  f q := ModuleCat.ofHom ((LinearMap.range (sSetChainMap f q)).mkQ)
  comm' i j hij := by
    obtain rfl := down_rel hij
    rw [relChainCx_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    show relBoundary f j (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (((sSetChainComplexFunctor.obj T).d (j + 1) j).hom x)
    rw [show ((sSetChainComplexFunctor.obj T).d (j + 1) j).hom = sSetBoundary T j from
      afmc_d_hom T j]
    rfl

@[simp] theorem relProj_f_apply {S T : SSet.{u}} (f : S ⟶ T) (q : ℕ) (x : SSetChain T q) :
    ((relProj f).f q).hom x = Submodule.Quotient.mk x := rfl

/-! ## WP7.5 : the short exact sequence -/

/-- The short complex `C_*(S) → C_*(T) → C_*(T,S)`. -/
def relSC {S T : SSet.{u}} (f : S ⟶ T) : ShortComplex (ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ) :=
  ShortComplex.mk (sSetChainComplexFunctor.map f) (relProj f) (by
    refine HomologicalComplex.hom_ext _ _ (fun q => ?_)
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    show Submodule.Quotient.mk (sSetChainMap f q x) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩)

/-- **WP7.5.  The relative short exact sequence.**  For a degreewise injective morphism of
simplicial sets `f`,

`0 → C_*(S) → C_*(T) → C_*(T,S) → 0`

is a short exact sequence of chain complexes of `ℤ₂`-modules. -/
theorem relSC_shortExact {S T : SSet.{u}} (f : S ⟶ T)
    (hf : ∀ n, Function.Injective (f.app n)) : (relSC f).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun q => ?_)
  have hinj : Function.Injective (sSetChainMap f q) := Finsupp.mapDomain_injective (hf _)
  have hmono : Mono ((relSC f).map
      (HomologicalComplex.eval (ModuleCat.{u} (ZMod 2)) (ComplexShape.down ℕ) q)).f :=
    (ModuleCat.mono_iff_injective _).2 hinj
  have hepi : Epi ((relSC f).map
      (HomologicalComplex.eval (ModuleCat.{u} (ZMod 2)) (ComplexShape.down ℕ) q)).g :=
    (ModuleCat.epi_iff_surjective _).2 (fun z => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      exact ⟨x, rfl⟩)
  refine { mono_f := hmono, epi_g := hepi, exact := ?_ }
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  · intro x hx
    exact (Submodule.Quotient.mk_eq_zero _).1 hx

/-! ## WP7.4 : functoriality for maps of pairs -/

/-- **WP7.4.**  A commuting square of simplicial sets induces a map of relative complexes. -/
def relChainCxMap {S T S' T' : SSet.{u}} (f : S ⟶ T) (f' : S' ⟶ T')
    (u : S ⟶ S') (v : T ⟶ T') (hsq : f ≫ v = u ≫ f') :
    relChainCx f ⟶ relChainCx f' where
  f q := ModuleCat.ofHom (Submodule.mapQ _ _ (sSetChainMap v q) (by
    rintro _ ⟨y, rfl⟩
    refine ⟨sSetChainMap u q y, ?_⟩
    show sSetChainMap f' q (sSetChainMap u q y) = sSetChainMap v q (sSetChainMap f q y)
    have h : sSetChainMap (u ≫ f') q = sSetChainMap (f ≫ v) q := by rw [hsq]
    have h' := congrFun (congrArg DFunLike.coe h) y
    show Finsupp.mapDomain (f'.app _) (Finsupp.mapDomain (u.app _) y)
      = Finsupp.mapDomain (v.app _) (Finsupp.mapDomain (f.app _) y)
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    exact h'))
  comm' i j hij := by
    obtain rfl := down_rel hij
    rw [relChainCx_d, relChainCx_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hb := congrFun (congrArg DFunLike.coe (sSetBoundary_naturality v j)) y
    refine congrArg (Submodule.Quotient.mk (p := LinearMap.range (sSetChainMap f' j))) ?_
    first
      | exact hb
      | exact hb.symm

/-- The comparison of relative complexes is compatible with the projections. -/
theorem relChainCxMap_relProj {S T S' T' : SSet.{u}} (f : S ⟶ T) (f' : S' ⟶ T')
    (u : S ⟶ S') (v : T ⟶ T') (hsq : f ≫ v = u ≫ f') :
    relProj f ≫ relChainCxMap f f' u v hsq = sSetChainComplexFunctor.map v ≫ relProj f' := by
  refine HomologicalComplex.hom_ext _ _ (fun q => ?_)
  exact ModuleCat.hom_ext (LinearMap.ext fun x => rfl)

/-! ## Specialisations : the singular and the simplicial pair -/

/-- The relative **singular** chain complex `C_*^{sing}(X,A;ℤ₂)` of a topological pair, defined
as the quotient of the singular chains of `X` by the image of those of `A`.  It is the general
construction applied to the singular simplicial sets. -/
abbrev relSingChainCx {A X : TopCat.{u}} (i : A ⟶ X) :
    ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ :=
  relChainCx (TopCat.toSSet.map i)

/-- A continuous injection induces a degreewise injection of singular simplicial sets. -/
theorem toSSet_map_injective {A X : TopCat.{u}} (i : A ⟶ X) (hi : Function.Injective i) (n) :
    Function.Injective ((TopCat.toSSet.map i).app n) := by
  intro s t hst
  have h : s.down ≫ i = t.down ≫ i := congrArg ULift.down hst
  refine ULift.ext _ _ ?_
  show (s.down : SimplexCategory.toTop.obj n.unop ⟶ A) = t.down
  refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
  exact hi (congrArg (fun (g : SimplexCategory.toTop.obj n.unop ⟶ X) => g x) h)

/-- **The relative singular short exact sequence** of a topological pair `A ⊆ X`. -/
theorem relSingSC_shortExact {A X : TopCat.{u}} (i : A ⟶ X) (hi : Function.Injective i) :
    (relSC (TopCat.toSSet.map i)).ShortExact :=
  relSC_shortExact _ (toSSet_map_injective i hi)

/-- The relative **simplicial** chain complex of a subcomplex inclusion. -/
abbrev relSimpChainCx {X : SSet.{u}} {A B : X.Subcomplex} (h : A ≤ B) :
    ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ :=
  relChainCx (SSet.Subcomplex.homOfLE h)

theorem subcomplex_homOfLE_injective {X : SSet.{u}} {A B : X.Subcomplex} (h : A ≤ B) (n) :
    Function.Injective ((SSet.Subcomplex.homOfLE h).app n) := by
  intro s t hst
  exact Subtype.ext (congrArg (fun z : ↑(B.obj n) => (z : X.obj n)) hst)

/-- **The relative simplicial short exact sequence** of a pair of subcomplexes. -/
theorem relSimpSC_shortExact {X : SSet.{u}} {A B : X.Subcomplex} (h : A ≤ B) :
    (relSC (SSet.Subcomplex.homOfLE h)).ShortExact :=
  relSC_shortExact _ (subcomplex_homOfLE_injective h)

end SpineTask14
