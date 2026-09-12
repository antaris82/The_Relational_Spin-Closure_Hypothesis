import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Increasing unions as colimits in `Type`

Two elementary facts about an `ℕ`-indexed diagram of types, used to identify a simplicial set
with the union of its skeleta and to transport that identification through a colimit-preserving
functor.

* `isColimitOfInjectiveJointlySurjective` — a cocone whose legs are injective and jointly
  surjective is a colimit cocone.  (The diagram is then an increasing union of subsets of the
  cocone point.)
* `injective_ι_of_injective_transitions` — conversely, in a colimit cocone over an `ℕ`-indexed
  diagram whose transition maps are injective, every leg is injective.

Nothing here mentions simplicial sets or topology.
-/

noncomputable section

open CategoryTheory Limits

universe u

namespace SpineDirectedUnion

variable {F : ℕ ⥤ Type u} (c : Cocone F)

/-- **An increasing union is a colimit.**  A cocone in `Type` over an `ℕ`-indexed diagram whose
legs are injective and jointly surjective is a colimit cocone. -/
def isColimitOfInjectiveJointlySurjective
    (hinj : ∀ r, Function.Injective (c.ι.app r))
    (hsurj : ∀ a : c.pt, ∃ (r : ℕ) (x : F.obj r), c.ι.app r x = a) : IsColimit c := by
  choose st sx hst using hsurj
  have hfac : ∀ (s : Cocone F) (r : ℕ) (x : F.obj r),
      s.ι.app (st (c.ι.app r x)) (sx (c.ι.app r x)) = s.ι.app r x := by
    intro s r x
    set a := c.ι.app r x with ha
    have h₁ : r ≤ max r (st a) := le_max_left _ _
    have h₂ : st a ≤ max r (st a) := le_max_right _ _
    have hkey : F.map (homOfLE h₁) x = F.map (homOfLE h₂) (sx a) := by
      apply hinj (max r (st a))
      have e₁ : c.ι.app (max r (st a)) (F.map (homOfLE h₁) x) = c.ι.app r x :=
        congrFun (c.w (homOfLE h₁)) x
      have e₂ : c.ι.app (max r (st a)) (F.map (homOfLE h₂) (sx a)) = c.ι.app (st a) (sx a) :=
        congrFun (c.w (homOfLE h₂)) (sx a)
      rw [e₁, e₂, hst a]
    have f₁ : s.ι.app (max r (st a)) (F.map (homOfLE h₁) x) = s.ι.app r x :=
      congrFun (s.w (homOfLE h₁)) x
    have f₂ : s.ι.app (max r (st a)) (F.map (homOfLE h₂) (sx a)) = s.ι.app (st a) (sx a) :=
      congrFun (s.w (homOfLE h₂)) (sx a)
    rw [← f₂, ← hkey, f₁]
  exact
    { desc := fun s a => s.ι.app (st a) (sx a)
      fac := fun s r => funext fun x => hfac s r x
      uniq := fun s m hm => funext fun a => by
        have : m (c.ι.app (st a) (sx a)) = s.ι.app (st a) (sx a) :=
          congrFun (hm (st a)) (sx a)
        rw [hst a] at this
        exact this }

/-- **Legs of a colimit of injections are injective.**  If all transition maps of an `ℕ`-indexed
diagram of types are injective, then so is every leg of a colimit cocone. -/
theorem injective_ι_of_injective_transitions {c : Cocone F} (hc : IsColimit c)
    (htr : ∀ {r s : ℕ} (h : r ≤ s), Function.Injective (F.map (homOfLE h))) (r : ℕ) :
    Function.Injective (c.ι.app r) := by
  intro x y hxy
  obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc x y).1 hxy
  exact htr (leOfHom f) hf

end SpineDirectedUnion
