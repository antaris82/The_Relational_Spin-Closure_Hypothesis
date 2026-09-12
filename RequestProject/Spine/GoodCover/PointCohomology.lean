import RequestProject.Spine.Cohomology.Cohomology

/-!
# Task 7, WP9 (partial) : the Task-5 singular cohomology of a one-point space

Acyclicity of a cover means that its overlaps have the cohomology of a point.  This module
computes, **natively and unconditionally**, the mod-2 singular cohomology of a space with at
most one point in the Task-5 theory:

```
    Hⁿ⁺¹_sing(X;ℤ₂) = 0        for every subsingleton, nonempty `X`.
```

The computation is elementary and uses no homotopy theory: on a subsingleton space there is
exactly one singular `n`-simplex in each degree (`Mod2Cohomology.simplexSubsingleton`,
`Mod2Cohomology.simplexNonempty`), so a cochain is determined by a single value and the
coboundary multiplies that value by the number of faces, `n + 2`.  Modulo two this is the
identity in odd degrees and zero in even degrees, so the complex is

```
    ℤ₂ --0--> ℤ₂ --1--> ℤ₂ --0--> ℤ₂ --1--> ⋯
```

whose cohomology vanishes above degree zero.

**Scope.**  This is the *coefficient* input of an acyclicity statement, not homotopy
invariance: it says nothing about a general contractible space.  Passing from "contractible"
to "has the cohomology of a point" is exactly the missing WP9 theorem (homotopy invariance of
the Task-5 quotient), which is recorded as a hypothesis in
`RequestProject.Spine.GoodCover.SingularComparisonSpec` and is *not* proved.
-/

noncomputable section

namespace Mod2Cohomology

open CategoryTheory Opposite

universe u

/-- On a subsingleton space there is at most one singular `n`-simplex. -/
instance simplexSubsingleton (X : TopCat.{u}) [Subsingleton X] (n : ℕ) :
    Subsingleton (Simplex X n) := by
  constructor
  intro f g
  apply (TopCat.toSSetObjEquiv X (op (SimplexCategory.mk n))).injective
  ext x
  exact Subsingleton.elim _ _

/-- On a nonempty space there is at least one singular `n`-simplex (a constant map). -/
instance simplexNonempty (X : TopCat.{u}) [Nonempty X] (n : ℕ) : Nonempty (Simplex X n) :=
  ⟨(TopCat.toSSetObjEquiv X (op (SimplexCategory.mk n))).symm
    ⟨fun _ => Classical.arbitrary X, continuous_const⟩⟩

/-- An odd natural number is `1` in `ℤ/2`. -/
theorem natCast_zmod2_of_odd {n : ℕ} (h : Odd n) : (n : ZMod 2) = 1 := by
  obtain ⟨k, hk⟩ := h
  subst hk
  push_cast
  rw [two_mul, CharTwo.add_self_eq_zero, zero_add]

variable {X : TopCat.{u}} [Subsingleton X] [Nonempty X]

omit [Nonempty X] in
/-- On a subsingleton space the coboundary multiplies the (unique) value of a cochain by the
number of faces, `n + 2`. -/
theorem coboundary_subsingleton (n : ℕ) (c : Cochain X n) (σ : Simplex X (n + 1))
    (τ : Simplex X n) : coboundary n c σ = ((n : ZMod 2) + 2) * c τ := by
  classical
  rw [coboundary_apply]
  have h : ∀ i : Fin (n + 2), c (face i σ) = c τ := by
    intro i; congr 1; exact Subsingleton.elim _ _
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  simp [Finset.card_univ, nsmul_eq_mul]

/-- **The mod-2 singular cohomology of a point vanishes above degree zero**, in the native
Task-5 theory.  In odd degrees the only cocycle is `0`; in even positive degrees every cochain
is a coboundary. -/
theorem cohomology_succ_eq_zero_of_subsingleton (n : ℕ) (q : Cohomology X (n + 1)) : q = 0 := by
  classical
  obtain ⟨z, rfl⟩ := mk_surjective q
  rw [mk_eq_zero_iff]
  have hz : d X (n + 1) (z : Cochain X (n + 1)) = 0 := z.2
  rcases Nat.even_or_odd n with he | ho
  · have hzero : (z : Cochain X (n + 1)) = 0 := by
      funext σ
      have hval := congrFun hz (Classical.arbitrary (Simplex X (n + 2)))
      rw [d_apply, coboundary_subsingleton (n + 1) (z : Cochain X (n + 1)) _ σ] at hval
      have hodd : (((n + 1 : ℕ) : ZMod 2) + 2) = 1 := by
        rw [natCast_zmod2_of_odd (Even.add_one he)]
        decide
      rw [hodd, one_mul] at hval
      exact hval
    rw [hzero]
    exact Submodule.zero_mem _
  · refine ⟨fun _ => (z : Cochain X (n + 1)) (Classical.arbitrary (Simplex X (n + 1))), ?_⟩
    funext σ
    rw [d_apply, coboundary_subsingleton n _ σ (Classical.arbitrary (Simplex X n))]
    rw [natCast_zmod2_of_odd ho]
    have h1 : ((1 : ZMod 2) + 2) = 1 := by decide
    rw [h1, one_mul]
    exact congrArg _ (Subsingleton.elim _ _)

/-- The degree-two case, which is what an acyclicity hypothesis on a cover needs. -/
theorem cohomology_two_eq_zero_of_subsingleton (q : Cohomology X 2) : q = 0 :=
  cohomology_succ_eq_zero_of_subsingleton 1 q

end Mod2Cohomology
