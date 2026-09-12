import RequestProject.Spine.Cohomology.AlexanderWhitney

/-!
# Task 5, WP6 (part 2) : the Alexander–Whitney cup product on cochains and the Leibniz rule

For `f ∈ Cᵖ(X;ℤ₂)` and `g ∈ Cᑫ(X;ℤ₂)` the Alexander–Whitney product is

`(f ⌣ g)(τ) = f (front_p τ) · g (back_q τ)`,  `τ` a `(p+q)`-simplex.

The main theorem of this module is the **Leibniz rule** in the form

`δ(f ⌣ g)(τ) = (δf)(frontBig τ) · g(backSmall τ) + f(front τ) · (δg)(backBig τ)`

for a `(p+q+1)`-simplex `τ`.  (There is no sign because `-1 = 1` in `ZMod 2`.)  Stating it
pointwise with the four explicit inclusions of
`RequestProject.Spine.Cohomology.AlexanderWhitney` avoids the dependent-type friction caused by
`(p+1)+q ≠ (p+q)+1`; the degreewise consequences used for the descent to cohomology are derived
from it in `RequestProject.Spine.Cohomology.CupDescent`.

The proof is the classical index bookkeeping: the `p+q+2` faces of `τ` split into those that
delete a vertex of the front part and those that delete a vertex of the back part, and the two
"middle" terms of the right-hand side coincide, hence cancel mod 2.
-/

noncomputable section

namespace Mod2Cohomology

open CategoryTheory Opposite SimplexCategory Finset

universe u

variable {X : TopCat.{u}}

/-! ## The cup product of cochains -/

/-- The **Alexander–Whitney cup product** of a `p`-cochain and a `q`-cochain. -/
def cup {p q : ℕ} (f : Cochain X p) (g : Cochain X q) : Cochain X (p + q) :=
  fun τ => f (reindex (frontIncl p q) τ) * g (reindex (backIncl p q) τ)

@[simp] theorem cup_apply {p q : ℕ} (f : Cochain X p) (g : Cochain X q)
    (τ : Simplex X (p + q)) :
    cup f g τ = f (reindex (frontIncl p q) τ) * g (reindex (backIncl p q) τ) := rfl

theorem cup_add_left {p q : ℕ} (f₁ f₂ : Cochain X p) (g : Cochain X q) :
    cup (f₁ + f₂) g = cup f₁ g + cup f₂ g := by
  funext τ; simp [cup, add_mul]

theorem cup_add_right {p q : ℕ} (f : Cochain X p) (g₁ g₂ : Cochain X q) :
    cup f (g₁ + g₂) = cup f g₁ + cup f g₂ := by
  funext τ; simp [cup, mul_add]

theorem cup_smul_left {p q : ℕ} (c : ZMod 2) (f : Cochain X p) (g : Cochain X q) :
    cup (c • f) g = c • cup f g := by
  funext τ; simp [cup, mul_assoc]

theorem cup_smul_right {p q : ℕ} (c : ZMod 2) (f : Cochain X p) (g : Cochain X q) :
    cup f (c • g) = c • cup f g := by
  funext τ; simp [cup]; ring

@[simp] theorem cup_zero_left {p q : ℕ} (g : Cochain X q) :
    cup (0 : Cochain X p) g = 0 := by funext τ; simp [cup]

@[simp] theorem cup_zero_right {p q : ℕ} (f : Cochain X p) :
    cup f (0 : Cochain X q) = 0 := by funext τ; simp [cup]

/-! ## The Leibniz rule -/

/-- **The Leibniz rule for the mod-2 Alexander–Whitney product.**

For a `(p+q+1)`-simplex `τ`,

`δ(f ⌣ g)(τ) = (δ f)(frontBig τ) · g(backSmall τ) + f(front τ) · (δ g)(backBig τ)`.

There is no sign because `-1 = 1` in `ZMod 2`; the two middle terms, which in the signed
version cancel by their signs, here cancel because `x + x = 0`. -/
theorem coboundary_cup {p q : ℕ} (f : Cochain X p) (g : Cochain X q)
    (τ : Simplex X (p + q + 1)) :
    coboundary (p + q) (cup f g) τ
      = coboundary p f (reindex (frontBig p q) τ) * g (reindex (backSmall p q) τ)
        + f (reindex (frontIncl p (q + 1)) τ)
            * coboundary q g (reindex (backIncl p (q + 1)) τ) := by
  classical
  set A : Fin (p + q + 2) → ZMod 2 := fun i =>
    f (reindex (frontIncl p q ≫ SimplexCategory.δ i) τ)
      * g (reindex (backIncl p q ≫ SimplexCategory.δ i) τ) with hA
  set B : Fin (p + 2) → ZMod 2 := fun k =>
    f (reindex (SimplexCategory.δ k ≫ frontBig p q) τ) * g (reindex (backSmall p q) τ) with hB
  set C : Fin (q + 2) → ZMod 2 := fun l =>
    f (reindex (frontIncl p (q + 1)) τ)
      * g (reindex (SimplexCategory.δ l ≫ backIncl p (q + 1)) τ) with hC
  -- the left-hand side
  have hLHS : coboundary (p + q) (cup f g) τ = ∑ i : Fin (p + q + 2), A i := by
    simp only [coboundary_apply, cup_apply, hA, face_def, reindex_reindex]
  -- the two right-hand terms
  have hT1 : coboundary p f (reindex (frontBig p q) τ) * g (reindex (backSmall p q) τ)
      = ∑ k : Fin (p + 2), B k := by
    simp only [coboundary_apply, hB, face_def, reindex_reindex, Finset.sum_mul]
  have hT2 : f (reindex (frontIncl p (q + 1)) τ)
        * coboundary q g (reindex (backIncl p (q + 1)) τ) = ∑ l : Fin (q + 2), C l := by
    simp only [coboundary_apply, hC, face_def, reindex_reindex, Finset.mul_sum]
  -- the two middle terms agree
  have hBlast : B (Fin.last (p + 1))
      = f (reindex (frontIncl p (q + 1)) τ) * g (reindex (backSmall p q) τ) := by
    simp only [hB, delta_last_comp_frontBig]
  have hC0 : C 0 = f (reindex (frontIncl p (q + 1)) τ) * g (reindex (backSmall p q) τ) := by
    simp only [hC, delta_zero_comp_backIncl]
  -- splitting the two right-hand sums
  have hBsplit : (∑ k : Fin (p + 2), B k)
      = (∑ k : Fin (p + 1), B k.castSucc) + B (Fin.last (p + 1)) := Fin.sum_univ_castSucc B
  have hCsplit : (∑ l : Fin (q + 2), C l) = C 0 + ∑ l : Fin (q + 1), C l.succ :=
    Fin.sum_univ_succ C
  -- splitting the left-hand sum
  have hlow : (∑ k : Fin (p + 1), B k.castSucc)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin (p + q + 2) => i.val ≤ p), A i := by
    refine Finset.sum_bij' (fun k _ => (⟨k.val, by omega⟩ : Fin (p + q + 2)))
      (fun i hi => (⟨i.val, by
        simp only [Finset.mem_filter] at hi
        omega⟩ : Fin (p + 1))) ?_ ?_ ?_ ?_ ?_
    · intro k _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Nat.lt_succ_iff.mp k.isLt
    · intro i _; exact Finset.mem_univ _
    · intro k _; rfl
    · intro i _; rfl
    · intro k _
      have hk : k.val ≤ p := Nat.lt_succ_iff.mp k.isLt
      simp only [hA, hB]
      rw [frontIncl_comp_delta_of_le p q ⟨k.val, by omega⟩ hk,
        backIncl_comp_delta_of_le p q ⟨k.val, by omega⟩ hk]
      rfl
  have hhigh : (∑ l : Fin (q + 1), C l.succ)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin (p + q + 2) => ¬ i.val ≤ p), A i := by
    refine Finset.sum_bij' (fun l _ => (⟨l.val + p + 1, by omega⟩ : Fin (p + q + 2)))
      (fun i hi => (⟨i.val - p - 1, by
        simp only [Finset.mem_filter] at hi
        have := i.isLt
        omega⟩ : Fin (q + 1))) ?_ ?_ ?_ ?_ ?_
    · intro l _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro i _; exact Finset.mem_univ _
    · intro l _
      exact Fin.ext (by show l.val + p + 1 - p - 1 = l.val; omega)
    · intro i hi
      simp only [Finset.mem_filter] at hi
      exact Fin.ext (by show i.val - p - 1 + p + 1 = i.val; omega)
    · intro l _
      have hl : p < l.val + p + 1 := by omega
      simp only [hA, hC]
      rw [frontIncl_comp_delta_of_gt p q ⟨l.val + p + 1, by omega⟩ hl,
        backIncl_comp_delta_of_gt p q ⟨l.val + p + 1, by omega⟩ hl]
      congr 2
      refine congrArg (fun m : Fin (q + 2) =>
        reindex (SimplexCategory.δ m ≫ backIncl p (q + 1)) τ) ?_
      exact Fin.ext (by show (l : ℕ) + 1 = (l : ℕ) + p + 1 - p; omega)
  have hAsplit : (∑ i : Fin (p + q + 2), A i)
      = (∑ i ∈ Finset.univ.filter (fun i : Fin (p + q + 2) => i.val ≤ p), A i)
        + ∑ i ∈ Finset.univ.filter (fun i : Fin (p + q + 2) => ¬ i.val ≤ p), A i :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hLHS, hT1, hT2, hBsplit, hCsplit, hAsplit, ← hlow, ← hhigh, hBlast, hC0]
  have hchar : ∀ x : ZMod 2, x + x = 0 := by decide
  set S1 := ∑ k : Fin (p + 1), B k.castSucc
  set S2 := ∑ l : Fin (q + 1), C l.succ
  set E := f (reindex (frontIncl p (q + 1)) τ) * g (reindex (backSmall p q) τ)
  calc S1 + S2 = S1 + S2 + (E + E) := by rw [hchar E, add_zero]
    _ = S1 + E + (E + S2) := by ring

end Mod2Cohomology
