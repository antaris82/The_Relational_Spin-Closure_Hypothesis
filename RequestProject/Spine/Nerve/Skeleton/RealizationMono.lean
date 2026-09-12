import RequestProject.Spine.Nerve.Skeleton.Pushout
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Task 15, WP2/WP3 : realization of the skeletal inclusion

## WP2, in one line

An exhaustive search of the pinned environment shows that `SSet.toTop` occurs in exactly one
file of the pinned library, `Mathlib/AlgebraicTopology/SingularSet.lean`, where it is *defined*
as a left Kan extension and shown to be a left adjoint (`sSetTopAdj`), together with the
identification `SSet.toTopSimplex : stdSimplex ⋙ toTop ≅ SimplexCategory.toTop` on
representables.  There is **no** theorem in the pin about injectivity, embeddings, closed
embeddings, cofibrations, preservation of monomorphisms, preservation of limits, or a
pointwise/quotient model of `|X|`.  See `TASK15_AUDIT.md` for the itemised inventory.

## WP3, what is proved here

The Task-14 blocker `B2` ("geometric realization of a monomorphism is injective") is *not*
proved here.  What is proved is a **sharp reduction of it to a single statement about the
standard cell**:

> `realization_skInc_injective` :
> if `|∂Δ[r]| → |Δ[r]|` is injective, then `|K^{(r-1)}| → |K^{(r)}|` is injective,
> for **every** simplicial set `K`.

The proof is honest topology, not a restatement:

* the WP1 pushout square is realized (`skeletalIsPushout_toTop`) and pushed into `Type`
  through the forgetful functor, which preserves colimits because it is a left adjoint;
* `Type` is adhesive, so a pushout of a monomorphism is a monomorphism
  (`Adhesive.mono_of_isPushout_of_mono_right`);
* the left vertical map of the square is the coproduct of the boundary inclusions, and a
  coproduct of injections in `Type` is injective (`sigmaMap_injective`), transported through
  the coproduct comparison of the colimit-preserving functor `Real`.

Consequently `SpineTask14.RealizationInjective` — the hypothesis that the one-skeleton step of
Task 14 carries — follows from the single standard-cell statement `StandardCellMono r`.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet SpineTask13 SpineTask14

universe u

namespace SpineTask15

/-! ## Coproducts of injections in `Type` -/

/-- A coproduct of injective maps of types is injective. -/
theorem sigmaMap_injective {J : Type u} {f g : J → Type u} (p : ∀ j, f j ⟶ g j)
    (hp : ∀ j, Function.Injective (p j)) :
    Function.Injective (Limits.Sigma.map p) := by
  have hsq : Limits.Sigma.map p ≫ (Types.coproductIso g).hom
      = (Types.coproductIso f).hom ≫ (fun x => ⟨x.1, p x.1 x.2⟩ : (Σ j, f j) → Σ j, g j) := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [← Category.assoc, Sigma.ι_map, Category.assoc, Types.coproductIso_ι_comp_hom,
      ← Category.assoc, Types.coproductIso_ι_comp_hom]
    rfl
  have hmid : Function.Injective (fun x => ⟨x.1, p x.1 x.2⟩ : (Σ j, f j) → Σ j, g j) := by
    rintro ⟨j, x⟩ ⟨k, y⟩ h
    obtain ⟨rfl, h2⟩ := Sigma.mk.injEq .. ▸ h
    exact congrArg (Sigma.mk j) (hp j (eq_of_heq h2))
  have : Function.Injective (Limits.Sigma.map p ≫ (Types.coproductIso g).hom) := by
    rw [hsq]
    exact hmid.comp ((Types.coproductIso f).toEquiv.injective)
  exact Function.Injective.of_comp this

/-! ## Realization, as a functor to sets -/

/-- Geometric realization, followed by the forgetful functor to sets. -/
abbrev Real : SSet.{u} ⥤ Type u := SSet.toTop.{u} ⋙ forget TopCat.{u}

instance : PreservesColimitsOfSize.{u, u} (forget TopCat.{u}) :=
  TopCat.adj₂.leftAdjoint_preservesColimits

instance : PreservesColimitsOfSize.{u, u} (Real.{u}) := by
  unfold Real
  infer_instance

/-- Realization of a coproduct of maps is (up to the canonical comparison isomorphisms) the
coproduct of the realizations; hence it is injective as soon as each factor is. -/
theorem Real_sigmaMap_injective {J : Type u} {f g : J → SSet.{u}} (p : ∀ j, f j ⟶ g j)
    (hp : ∀ j, Function.Injective (Real.map (p j))) :
    Function.Injective (Real.map (Limits.Sigma.map p)) := by
  have hsq : sigmaComparison Real.{u} f ≫ Real.map (Limits.Sigma.map p)
      = Limits.Sigma.map (fun j => Real.map (p j)) ≫ sigmaComparison Real.{u} g := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [← Category.assoc, ι_comp_sigmaComparison, ← Functor.map_comp, Sigma.ι_map,
      Functor.map_comp, ← Category.assoc, Sigma.ι_map, Category.assoc,
      ι_comp_sigmaComparison]
  have hgbij : Function.Bijective (sigmaComparison Real.{u} g) :=
    (isIso_iff_bijective _).1 inferInstance
  have hfbij : Function.Bijective (sigmaComparison Real.{u} f) :=
    (isIso_iff_bijective _).1 inferInstance
  have hcomp : Function.Injective (sigmaComparison Real.{u} f ≫ Real.map (Limits.Sigma.map p)) := by
    rw [hsq]
    exact hgbij.1.comp (sigmaMap_injective _ hp)
  intro x y hxy
  obtain ⟨x', rfl⟩ := hfbij.2 x
  obtain ⟨y', rfl⟩ := hfbij.2 y
  exact congrArg (sigmaComparison Real.{u} f) (hcomp hxy)

/-! ## WP3 : the reduction of the skeletal realization inclusion to the standard cell -/

/-- **The standard-cell monomorphism statement.**  This is the *only* remaining input needed
for injectivity of the realized skeletal inclusion, for every simplicial set.  It is a
statement about a single fixed pair of simplicial sets, with no free variables besides `r`. -/
def StandardCellMono (r : ℕ) : Prop :=
  Function.Injective (Real.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι)

variable (X : SSet.{u}) (r : ℕ)

/-- **WP3, the reduction.**  If the realization of the boundary inclusion of the standard
`r`-simplex is injective, then the realization of the skeletal inclusion
`K^{(r-1)} ↪ K^{(r)}` is injective, for **every** simplicial set `K`.

The proof: the WP1 pushout square is carried to `Type` by the colimit-preserving functor
`Real`; the left vertical map is a coproduct of copies of `|∂Δ[r]| → |Δ[r]|`, hence
injective; and `Type` is adhesive, so a pushout of a monomorphism is a monomorphism. -/
theorem realization_skInc_injective (h : StandardCellMono.{u} r) :
    Function.Injective (Real.map (skInc X r)) := by
  have hpush : IsPushout (Real.map (attachMap X r)) (Real.map (bdryMap X r))
      (Real.map (skInc X r)) (Real.map (cellMap X r)) := (skeletalIsPushout X r).map Real
  have hmono : Mono (Real.map (bdryMap X r)) := by
    rw [CategoryTheory.mono_iff_injective]
    exact Real_sigmaMap_injective _ fun _ => h
  have hres := Adhesive.mono_of_isPushout_of_mono_right hpush
  rwa [CategoryTheory.mono_iff_injective] at hres

/-! ## The `r = 0` instance of the standard-cell statement -/

/-- `∂Δ[0]` has no simplices at all: every map `⦋n⦌ ⟶ ⦋0⦌` is surjective. -/
instance boundaryZero_isEmpty (n : SimplexCategoryᵒᵖ) :
    IsEmpty (((∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u}).obj n) := by
  constructor
  rintro ⟨x, hx⟩
  refine hx fun b => ⟨0, ?_⟩
  rw [Fin.fin_one_eq_zero b, Fin.fin_one_eq_zero (stdSimplex.asOrderHom x 0)]

/-- Hence `∂Δ[0]` is the initial simplicial set. -/
def boundaryZero_isInitial : IsInitial (((∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex)) : SSet.{u}) :=
  IsInitial.ofUniqueHom
    (fun _ => { app := fun n x => (boundaryZero_isEmpty n).elim x
                naturality := fun m _ _ => by funext x; exact (boundaryZero_isEmpty m).elim x })
    (fun _ _ => by ext n x; exact (boundaryZero_isEmpty n).elim x)

/-- **The standard-cell statement holds for `r = 0`.**  `|∂Δ[0]|` is the empty space, because
realization preserves the initial object. -/
theorem standardCellMono_zero : StandardCellMono.{u} 0 := by
  have hI : IsInitial (Real.{u}.obj (((∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex)) : SSet.{u})) :=
    IsInitial.isInitialObj _ _ boundaryZero_isInitial
  have : IsEmpty (Real.{u}.obj (((∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex)) : SSet.{u})) :=
    Function.isEmpty (hI.to (PEmpty.{u + 1}))
  exact fun a b _ => Subsingleton.elim a b

end SpineTask15
