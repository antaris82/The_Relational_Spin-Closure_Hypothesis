import RequestProject.Spine.Nerve.Skeleton.Filtration
import RequestProject.Spine.Nerve.Geometry.SkeletalFactorization

/-!
# Skeletal support: the point-set input of the global comparison

The skeletal induction produces a homology isomorphism on every skeleton `Sk K r` of a
simplicial set `K`.  Passing from the skeleta to `K` itself needs two point-set facts about the
realization:

* **the realized skeleta really are subspaces of `|K|`**, i.e. `|Sk K r| → |K|` is injective.
  This is *proved* here, unconditionally: `K` is the colimit of its skeleta
  (`NerveSkeleton.skIsColimit`), realization preserves colimits, all the transition maps
  `|Sk K r| → |Sk K (r+1)|` are injective (the Task-15 reduction to the standard cell together
  with the Task-16 point model), and a leg of a colimit of injections over `ℕ` is injective;
* **every singular simplex of `|K|` already lives in some `|Sk K r|`**, the proposition
  `SkeletalSupport K`.  This too is now *proved*, unconditionally, in `skeletalSupport`: the
  domain `Δ^q_top` of a singular simplex is compact, so the point-set factorization theorem
  `NerveTopology.exists_skeletal_factorization` (the image of a compact set meets only
  finitely many cells, hence has bounded carrier dimension, and the realized skeleton is a
  closed subspace) factors it continuously through some `|Sk K r|`.

Nothing in this file is an assumption; `SkeletalSupport` is kept as a named proposition only
because the downstream assembly is stated in terms of it.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet SpineTask13

universe u

namespace NerveSkeleton

variable (K : SSet.{u})

/-! ## The realized skeleta are subspaces of `|K|` -/

/-- Every transition map of the realized skeletal filtration is injective. -/
theorem realization_transition_injective {a b : ℕ} (h : a ≤ b) :
    Function.Injective (SpineTask15.Real.map ((skFunctor K).map (homOfLE h))) := by
  induction b with
  | zero =>
      have ha : a = 0 := Nat.le_zero.1 h
      subst ha
      have hid : (skFunctor K).map (homOfLE h) = 𝟙 _ := by
        rw [Subsingleton.elim (homOfLE h) (𝟙 (0 : ℕ))]
        exact (skFunctor K).map_id 0
      rw [hid, CategoryTheory.Functor.map_id]
      exact fun x y hxy => hxy
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with hlt | hge
      · have hab : a ≤ b := Nat.lt_succ_iff.1 hlt
        rw [skFunctor_map_succ K hab h, Functor.map_comp]
        intro x y hxy
        exact ih hab (SpineTask15.realization_skInc_injective K b
          (SpineTask16.standardCellMono b) hxy)
      · have ha : a = b + 1 := le_antisymm h hge
        subst ha
        have hid : (skFunctor K).map (homOfLE h) = 𝟙 _ := by
          rw [Subsingleton.elim (homOfLE h) (𝟙 (b + 1 : ℕ))]
          exact (skFunctor K).map_id (b + 1)
        rw [hid, CategoryTheory.Functor.map_id]
        exact fun x y hxy => hxy

/-- **The realization of a skeleton injects into the realization.**  No hypothesis. -/
theorem realization_skIncl_injective (r : ℕ) :
    Function.Injective (SpineTask15.Real.map (skIncl K r)) := by
  have hc : IsColimit (SpineTask15.Real.mapCocone (skCocone K)) :=
    isColimitOfPreserves _ (skIsColimit K)
  exact SpineDirectedUnion.injective_ι_of_injective_transitions hc
    (fun {a b} h => realization_transition_injective K h) r

/-! ## The remaining point-set input -/

/-- The singular simplicial set of the realization of a simplicial set. -/
abbrev Sing (K : SSet.{u}) : SSet.{u} := TopCat.toSSet.obj (SSet.toTop.obj K)

/-- The map of singular simplicial sets induced by the realized skeletal inclusion. -/
abbrev singSkIncl (r : ℕ) : Sing (Sk K r) ⟶ Sing K :=
  TopCat.toSSet.map (SSet.toTop.map (skIncl K r))

/-- **The point-set input of the global comparison**: every singular simplex of `|K|` is a
singular simplex of some `|Sk K r|`. -/
def SkeletalSupport (K : SSet.{u}) : Prop :=
  ∀ (q : ℕ) (σ : (Sing K) _⦋q⦌),
    ∃ (r : ℕ) (τ : (Sing (Sk K r)) _⦋q⦌), (singSkIncl K r).app (op ⦋q⦌) τ = σ

/-- A continuous map with injective underlying function induces an injective map of singular
simplicial sets in every dimension. -/
theorem toSSet_map_app_injective {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Function.Injective f)
    (n : SimplexCategoryᵒᵖ) : Function.Injective ((TopCat.toSSet.map f).app n) := by
  haveI : Mono f := (TopCat.mono_iff_injective f).2 hf
  intro a b hab
  exact ULift.ext _ _ ((cancel_mono f).1 (congrArg ULift.down hab))

/-- The singular simplices of `|Sk K r|` inject into those of `|K|`; unconditional. -/
theorem singSkIncl_injective (r : ℕ) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((singSkIncl K r).app n) :=
  toSSet_map_app_injective _ (realization_skIncl_injective K r) n

/-! ## The point-set input is a theorem -/

/-- **Skeletal support holds for every simplicial set.**  A singular `q`-simplex of `|K|` is a
continuous map from the compact space `Δ^q_top`, so it factors continuously through a finite
skeleton by `NerveTopology.exists_skeletal_factorization`; the factorization *is* the required
singular simplex of `|Sk K r|`.  No finiteness hypothesis on `K` is used. -/
theorem skeletalSupport (K : SSet.{u}) : SkeletalSupport K := by
  intro q σ
  obtain ⟨r, g', hg'⟩ := NerveTopology.exists_skeletal_factorization K
    ((TopCat.toSSetObjEquiv (SSet.toTop.obj K) (op ⦋q⦌)) σ)
  refine ⟨r, (TopCat.toSSetObjEquiv (SSet.toTop.obj (Sk K r)) (op ⦋q⦌)).symm g', ?_⟩
  apply (TopCat.toSSetObjEquiv (SSet.toTop.obj K) (op ⦋q⦌)).injective
  ext t
  exact hg' t

end NerveSkeleton
