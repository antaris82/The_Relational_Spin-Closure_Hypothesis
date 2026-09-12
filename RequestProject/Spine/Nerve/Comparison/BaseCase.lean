import RequestProject.Spine.Nerve.Comparison.SkeletalStep

/-!
# Task 15, WP12 : the base case, and the conditional skeletal induction

Task 14 supplied the *step* of the skeletal induction, conditional on the two topological
blockers.  This module supplies the missing **base case**, unconditionally, and assembles the
two into the conditional induction over all skeleta.

* `skZero_isEmpty` — `K^{(-1)} = Sk K 0` is the empty simplicial set (its `0`-skeleton in the
  project's indexing is `Sk K 1`).
* `singSkZero_isEmpty` — hence `|Sk K 0|` is the empty space and its singular simplicial set is
  empty as well.
* `baseCase` — **`J = C_*(η)` is a homology isomorphism on `Sk K 0`**, unconditionally: both
  chain complexes are zero.
* `skeletalInduction` — for every `r`, `J` is a homology isomorphism on `Sk K r`, given the
  standard-cell monomorphism statement `StandardCellMono` and the relative comparison
  isomorphism `RelJIsIso` at every level.  Both hypotheses are explicit; nothing is assumed.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet SpineTask13 SpineTask14

universe u

namespace SpineTask15

variable (X : SSet.{u})

/-! ## The bottom of the skeletal filtration is empty -/

/-- `Sk X 0` has no simplices: a simplex of the `0`-skeleton would have a nondegenerate
representative of dimension `< 0`. -/
instance skZero_isEmpty (n : SimplexCategoryᵒᵖ) : IsEmpty ((Sk X 0).obj n) := by
  constructor
  obtain ⟨Δ⟩ := n
  induction Δ using SimplexCategory.rec with | _ k => ?_
  rintro ⟨x, hx⟩
  obtain ⟨m, f, hf, y, hy⟩ := X.exists_nonDegenerate x
  have hymem : y.1 ∈ (X.skeleton 0).obj (op (SimplexCategory.mk m)) :=
    nonDeg_mem_of_mem _ x hx f y.1 hy
  exact absurd ((X.mem_skeleton_obj_iff_of_nonDegenerate y 0).1 hymem) (Nat.not_lt_zero m)

/-- `Sk X 0` is the initial simplicial set. -/
def skZero_isInitial : IsInitial (Sk X 0) :=
  IsInitial.ofUniqueHom
    (fun _ => { app := fun n x => (skZero_isEmpty X n).elim x
                naturality := fun m _ _ => by funext x; exact (skZero_isEmpty X m).elim x })
    (fun _ _ => by ext n x; exact (skZero_isEmpty X n).elim x)

/-- `|Sk X 0|` is the empty space. -/
instance realSkZero_isEmpty : IsEmpty (Real.{u}.obj (Sk X 0)) :=
  Function.isEmpty ((IsInitial.isInitialObj Real.{u} _ (skZero_isInitial X)).to (PEmpty.{u + 1}))

/-- The singular simplicial set of `|Sk X 0|` is empty as well: the topological simplices are
nonempty, and there are no maps from a nonempty space to the empty space. -/
instance singSkZero_isEmpty (n : SimplexCategoryᵒᵖ) : IsEmpty ((SingSk X 0).obj n) := by
  constructor
  intro g
  obtain ⟨p⟩ := (inferInstance : Nonempty (SimplexCategory.toTop.{u}.obj n.unop))
  exact (realSkZero_isEmpty X).elim ((forget TopCat).map g.down p)

/-! ## The base case -/

theorem isZero_chain_of_isEmpty (S : SSet.{u}) [hS : ∀ n, IsEmpty (S.obj n)] (q : ℕ) :
    IsZero ((sSetChainComplexFunctor.obj S).X q) := by
  haveI : Subsingleton ((sSetChainComplexFunctor.obj S).X q) :=
    ⟨fun a b => Finsupp.ext fun x => (hS _).elim x⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- **The base case of the skeletal induction.**  `J = C_*(η)` is a homology isomorphism on
`Sk X 0`, because both chain complexes are zero. -/
theorem baseCase (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk X 0))) q) := by
  haveI hcomp : ∀ i, IsIso ((sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk X 0))).f i) := by
    intro i
    have h₁ := isZero_chain_of_isEmpty (Sk X 0) i
    have h₂ := isZero_chain_of_isEmpty (SingSk X 0) i
    have he : (sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk X 0))).f i
        = (h₁.iso h₂).hom := h₁.eq_of_src _ _
    rw [he]
    infer_instance
  haveI : IsIso (sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk X 0))) :=
    HomologicalComplex.Hom.isIso_of_components _
  have hh := (HomologicalComplex.homologyMapIso
    (asIso (sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk X 0)))) q).isIso_hom
  simpa using hh

/-! ## The conditional skeletal induction -/

/-- **WP12, the induction.**  Given the standard-cell monomorphism statement and the relative
comparison isomorphism at every level, `J` is a homology isomorphism on every skeleton. -/
theorem skeletalInduction (hcell : ∀ r, StandardCellMono.{u} r)
    (hrel : ∀ r, RelJIsIso X r) :
    ∀ (r q : ℕ), IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk X r))) q) := by
  intro r
  induction r with
  | zero => exact baseCase X
  | succ s ih => exact fun q => oneSkeletonStep_of_standardCell X s (hcell s) ih (hrel s) q


/-! ## From skeleta to a finite-dimensional simplicial set -/

/-- For a simplicial set of dimension `< d` the `d`-th skeleton is everything. -/
theorem skeleton_eq_top (d : ℕ) [X.HasDimensionLT d] : X.skeleton d = ⊤ := by
  rw [Subcomplex.eq_top_iff_of_hasDimensionLT _ d]
  intro i hi x _
  exact X.mem_skeleton x hi

/-- Hence `Sk X d ≅ X`. -/
def skTopIso (d : ℕ) [X.HasDimensionLT d] : Sk X d ≅ X :=
  eqToIso (congrArg Subcomplex.toSSet (skeleton_eq_top X d)) ≪≫ Subcomplex.topIso X

/-- **WP12, the finite-dimensional statement.**  For a simplicial set of dimension `< d`, the
canonical map `J = C_*(η_X)` is a homology isomorphism, given the standard-cell monomorphism
statement and the relative comparison isomorphism at every level. -/
theorem finiteDimensional_homologyIso (d : ℕ) [X.HasDimensionLT d]
    (hcell : ∀ r, StandardCellMono.{u} r) (hrel : ∀ r, RelJIsIso X r) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (sSetTopAdj.unit.app X)) q) := by
  set e := skTopIso X d with he
  have hnat : e.hom ≫ sSetTopAdj.unit.app X
      = sSetTopAdj.unit.app (Sk X d) ≫ TopCat.toSSet.map (SSet.toTop.map e.hom) :=
    sSetTopAdj.unit.naturality e.hom
  have hmap : sSetChainComplexFunctor.map e.hom
        ≫ sSetChainComplexFunctor.map (sSetTopAdj.unit.app X)
      = sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk X d))
        ≫ sSetChainComplexFunctor.map (TopCat.toSSet.map (SSet.toTop.map e.hom)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hnat]
  have hL : IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map e.hom) q) := by
    have := (HomologicalComplex.homologyMapIso
      (sSetChainComplexFunctor.mapIso e) q).isIso_hom
    simpa using this
  have hR : IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (TopCat.toSSet.map (SSet.toTop.map e.hom))) q) := by
    have := (HomologicalComplex.homologyMapIso
      (sSetChainComplexFunctor.mapIso ((TopCat.toSSet).mapIso (SSet.toTop.mapIso e))) q).isIso_hom
    simpa using this
  have hSk : IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (sSetTopAdj.unit.app (Sk X d))) q) :=
    skeletalInduction X hcell hrel d q
  have hcomp : IsIso (HomologicalComplex.homologyMap (sSetChainComplexFunctor.map e.hom) q
      ≫ HomologicalComplex.homologyMap
        (sSetChainComplexFunctor.map (sSetTopAdj.unit.app X)) q) := by
    rw [← HomologicalComplex.homologyMap_comp, hmap, HomologicalComplex.homologyMap_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (HomologicalComplex.homologyMap (sSetChainComplexFunctor.map e.hom) q) _

end SpineTask15
