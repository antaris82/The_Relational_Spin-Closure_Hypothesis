import RequestProject.Spine.Cohomology.Cochain

/-!
# Task 5, WP3 : the singular mod-2 coboundary and `δ² = 0`

The coboundary of a singular `n`-cochain `f` is the `(n+1)`-cochain

`(δ f) σ = ∑_{i : Fin (n+2)} f (∂ᵢ σ)`.

**Why there are no signs.**  The integral singular coboundary is the *alternating* sum
`∑ᵢ (-1)^i f(∂ᵢ σ)`.  Here the coefficient ring is `ZMod 2`, in which `-1 = 1`, so every sign
is `1` and the alternating sum is the plain sum.  This is a simplification of bookkeeping only:
the cancellation in `δ² = 0` is *not* obtained from signs but from the cosimplicial identity

`SimplexCategory.δ_comp_δ : i ≤ j → δ i ≫ δ j.succ = δ j ≫ δ i.castSucc`,

which pairs the index set `Fin (n+3) × Fin (n+2)` of the double sum into two halves carrying
equal terms; the two halves then cancel because `x + x = 0` in `ZMod 2`.  In the integral case
the same pairing is used and the signs of the paired terms are opposite; in characteristic two
both mechanisms coincide.  Nothing about the cochain-complex law is postulated.

## Contents

* `Mod2Cohomology.coboundary` — the coboundary as a function;
* `Mod2Cohomology.d` — the coboundary as a `ZMod 2`-linear map `Cⁿ →ₗ Cⁿ⁺¹`;
* `Mod2Cohomology.coboundary_coboundary` / `Mod2Cohomology.d_comp_d` — the theorem `δ² = 0`,
  in pointwise and in linear-map form.
-/

noncomputable section

namespace Mod2Cohomology

open CategoryTheory Opposite Finset

universe u

variable {X : TopCat.{u}}

/-- The **singular mod-2 coboundary** `δ : Cⁿ → Cⁿ⁺¹`, the (unsigned, because `-1 = 1` in
`ZMod 2`) sum of the values of `f` on all faces. -/
def coboundary (n : ℕ) (f : Cochain X n) : Cochain X (n + 1) :=
  fun σ => ∑ i : Fin (n + 2), f (face i σ)

@[simp] theorem coboundary_apply (n : ℕ) (f : Cochain X n) (σ : Simplex X (n + 1)) :
    coboundary n f σ = ∑ i : Fin (n + 2), f (face i σ) := rfl

theorem coboundary_add (n : ℕ) (f g : Cochain X n) :
    coboundary n (f + g) = coboundary n f + coboundary n g := by
  funext σ
  simp [coboundary, Finset.sum_add_distrib]

theorem coboundary_smul (n : ℕ) (c : ZMod 2) (f : Cochain X n) :
    coboundary n (c • f) = c • coboundary n f := by
  funext σ
  simp [coboundary, Finset.mul_sum]

/-- The coboundary as a `ZMod 2`-linear map `δⁿ : Cⁿ(X;ℤ₂) →ₗ Cⁿ⁺¹(X;ℤ₂)`. -/
def d (X : TopCat.{u}) (n : ℕ) : Cochain X n →ₗ[ZMod 2] Cochain X (n + 1) where
  toFun := coboundary n
  map_add' := coboundary_add n
  map_smul' := coboundary_smul n

@[simp] theorem d_apply (n : ℕ) (f : Cochain X n) : d X n f = coboundary n f := rfl

@[simp] theorem d_apply_simplex (n : ℕ) (f : Cochain X n) (σ : Simplex X (n + 1)) :
    d X n f σ = ∑ i : Fin (n + 2), f (face i σ) := rfl

/-! ## `δ² = 0` -/

/-- **The cochain-complex law `δ ∘ δ = 0`**, proved from the cosimplicial identity
`SimplexCategory.δ_comp_δ`.

The double sum runs over `Fin (n+3) × Fin (n+2)`, its `(i,j)`-term being `f` of the simplex
reindexed along `δ j ≫ δ i`.  Splitting the index set along `j.castSucc < i` and using
`δ_comp_δ` to match `(i,j) ↦ (j.castSucc, i.pred)` gives two halves with identical terms; over
`ZMod 2` their sum vanishes. -/
theorem coboundary_coboundary (n : ℕ) (f : Cochain X n) :
    coboundary (n + 1) (coboundary n f) = 0 := by
  classical
  funext σ
  show (∑ i : Fin (n + 3), ∑ j : Fin (n + 2), f (face j (face i σ))) = 0
  have hterm : ∀ (i : Fin (n + 3)) (j : Fin (n + 2)),
      f (face j (face i σ)) = f (reindex (SimplexCategory.δ j ≫ SimplexCategory.δ i) σ) := by
    intro i j; rw [face_face]
  simp only [hterm]
  rw [← Fintype.sum_prod_type (f := fun p : Fin (n + 3) × Fin (n + 2) =>
    f (reindex (SimplexCategory.δ p.2 ≫ SimplexCategory.δ p.1) σ))]
  set T : Fin (n + 3) × Fin (n + 2) → ZMod 2 := fun p =>
    f (reindex (SimplexCategory.δ p.2 ≫ SimplexCategory.δ p.1) σ) with hT
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => p.2.castSucc < p.1) T]
  have key :
      (∑ p ∈ Finset.univ.filter (fun p : Fin (n + 3) × Fin (n + 2) => p.2.castSucc < p.1), T p)
        = ∑ p ∈ Finset.univ.filter
            (fun p : Fin (n + 3) × Fin (n + 2) => ¬ p.2.castSucc < p.1), T p := by
    refine Finset.sum_bij' (fun p hp => (p.2.castSucc, p.1.pred (by
        simp only [Finset.mem_filter] at hp
        have h := hp.2
        intro h0; rw [h0] at h; exact absurd h (by simp [Fin.lt_def]))))
      (fun p hp => (p.2.succ, p.1.castPred (by
        simp only [Finset.mem_filter] at hp
        have h := hp.2
        simp only [not_lt] at h
        intro hlast
        rw [hlast] at h
        have hb := p.2.isLt
        simp [Fin.le_def, Fin.val_last] at h
        omega))) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      simp only [not_lt, Fin.le_def, Fin.val_castSucc, Fin.val_pred]
      simp [Fin.lt_def] at ha
      omega
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      simp only [not_lt, Fin.le_def, Fin.val_castSucc] at ha
      simp [Fin.lt_def, Fin.val_succ]
      omega
    · intro a _; ext <;> simp
    · intro a _; ext <;> simp
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      have hle : a.2 ≤ a.1.pred
          (by intro h0; rw [h0] at ha; exact absurd ha (by simp [Fin.lt_def])) := by
        simp only [Fin.le_def, Fin.val_pred]
        simp [Fin.lt_def] at ha
        omega
      have hid := SimplexCategory.δ_comp_δ (n := n) hle
      simp only [hT]
      congr 2
      rw [Fin.succ_pred] at hid
      exact hid
  rw [key]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  exact h2 _

/-- `δ² = 0` in linear-map form: the composite `Cⁿ →ₗ Cⁿ⁺¹ →ₗ Cⁿ⁺²` is the zero map. -/
theorem d_comp_d (n : ℕ) : (d X (n + 1)).comp (d X n) = 0 := by
  ext f
  exact congrFun (coboundary_coboundary n f) _

@[simp] theorem d_d (n : ℕ) (f : Cochain X n) : d X (n + 1) (d X n f) = 0 :=
  coboundary_coboundary n f

end Mod2Cohomology
