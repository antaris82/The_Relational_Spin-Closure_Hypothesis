import RequestProject.Spine.Cohomology.Cochain

/-!
# Task 8, WP3 (a) : the combinatorial input of the singular prism

The prism operator is built from three families of morphisms of `SimplexCategory`, indexed by
**natural numbers** rather than by `Fin`s.  Natural-number indexing is not a convenience: it is
what makes the prism bookkeeping possible, because the standard identities

```
    δ_b ≫ σ_a = σ_{a-1} ≫ δ_b        (b < a)
    δ_b ≫ σ_a = σ_a ≫ δ_{b-1}        (b > a+1)
    δ_b ≫ σ_a = 𝟙                    (b = a or b = a+1)
```

change the *dimension* of the intermediate object, so the `Fin`-indexed Mathlib forms
(`SimplexCategory.δ_comp_σ_of_le` etc.) carry casts that obstruct the double-sum manipulation.
The `ℕ`-indexed families below have fixed source and target and only their parameters move.

## Contents

* `Mod2Cohomology.deltaN m s : [m] ⟶ [m+1]` — the `s`-th coface, `ℕ`-indexed;
* `Mod2Cohomology.sigmaN m r : [m+1] ⟶ [m]` — the `r`-th codegeneracy, `ℕ`-indexed;
* `Mod2Cohomology.betaN m r : [m] ⟶ [1]` — the "cut at `r`" map, sending the vertices
  `0,…,r-1` to `0` and `r,…,m` to `1`.  This is the combinatorial shadow of the interval
  coordinate of the prism: `betaN m 0` is constant `1` and `betaN m r` for `r > m` is
  constant `0`;
* `Mod2Cohomology.delta_eq`, `Mod2Cohomology.sigma_eq` — the `ℕ`-indexed families agree with
  Mathlib's `SimplexCategory.δ` and `SimplexCategory.σ`;
* `Mod2Cohomology.deltaN_comp_sigmaN_lt` / `_gt` / `_eq` — the three simplicial identities;
* `Mod2Cohomology.deltaN_comp_betaN` — the interval-coordinate identity
  `δ_s ≫ β_r = β_{r-1}` if `s < r`, `= β_r` otherwise.
-/

noncomputable section

namespace Mod2Cohomology

open CategoryTheory SimplexCategory

/-! ## The three `ℕ`-indexed families -/

/-- The `s`-th coface `[m] ⟶ [m+1]`, indexed by a natural number: the monotone injection that
skips the vertex `s` (and is the identity-like inclusion when `s > m+1`). -/
def deltaN (m s : ℕ) : SimplexCategory.mk m ⟶ SimplexCategory.mk (m + 1) :=
  SimplexCategory.mkHom
    { toFun := fun k => ⟨if (k : ℕ) < s then (k : ℕ) else (k : ℕ) + 1, by
        have := k.isLt; split <;> omega⟩
      monotone' := by
        intro a b hab
        simp only [Fin.le_def] at hab ⊢
        split <;> split <;> omega }

/-- The `r`-th codegeneracy `[m+1] ⟶ [m]`, indexed by a natural number: the monotone surjection
that repeats the vertex `r`. -/
def sigmaN (m r : ℕ) : SimplexCategory.mk (m + 1) ⟶ SimplexCategory.mk m :=
  SimplexCategory.mkHom
    { toFun := fun k => ⟨min (if (k : ℕ) ≤ r then (k : ℕ) else (k : ℕ) - 1) m, by omega⟩
      monotone' := by
        intro a b hab
        simp only [Fin.le_def] at hab ⊢
        split <;> split <;> omega }

/-- The **cut map** `[m] ⟶ [1]`: vertices `< r` go to `0`, vertices `≥ r` go to `1`.  In the
prism this records at which vertex the singular simplex jumps from the `f`-end of the homotopy
to the `g`-end. -/
def betaN (m r : ℕ) : SimplexCategory.mk m ⟶ SimplexCategory.mk 1 :=
  SimplexCategory.mkHom
    { toFun := fun k => (⟨if (k : ℕ) < r then 0 else 1, by split <;> omega⟩ : Fin 2)
      monotone' := by
        intro a b hab
        simp only [Fin.le_def] at hab ⊢
        split <;> split <;> omega }

@[simp] theorem deltaN_val (m s : ℕ) (k : Fin (m + 1)) :
    ((deltaN m s).toOrderHom k : ℕ) = if (k : ℕ) < s then (k : ℕ) else (k : ℕ) + 1 := rfl

@[simp] theorem sigmaN_val (m r : ℕ) (k : Fin (m + 2)) :
    ((sigmaN m r).toOrderHom k : ℕ) = min (if (k : ℕ) ≤ r then (k : ℕ) else (k : ℕ) - 1) m := rfl

@[simp] theorem betaN_val (m r : ℕ) (k : Fin (m + 1)) :
    ((betaN m r).toOrderHom k : ℕ) = if (k : ℕ) < r then 0 else 1 := rfl

/-! ## Extensionality and composition, at the level of values -/

/-- Two morphisms of the simplex category agree as soon as their underlying monotone maps agree
numerically. -/
theorem simplexHom_ext {a b : ℕ} {p q : SimplexCategory.mk a ⟶ SimplexCategory.mk b}
    (h : ∀ k : Fin (a + 1), (p.toOrderHom k : ℕ) = (q.toOrderHom k : ℕ)) : p = q := by
  apply SimplexCategory.Hom.ext
  ext k
  exact h k

@[simp] theorem simplexHom_comp_val {a b c : ℕ} (p : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (q : SimplexCategory.mk b ⟶ SimplexCategory.mk c) (k : Fin (a + 1)) :
    ((p ≫ q).toOrderHom k : ℕ) = (q.toOrderHom (p.toOrderHom k) : ℕ) := rfl

@[simp] theorem simplexHom_id_val {a : ℕ} (k : Fin (a + 1)) :
    ((SimplexCategory.Hom.toOrderHom (𝟙 (SimplexCategory.mk a)) k : Fin (a + 1)) : ℕ)
      = (k : ℕ) := rfl

/-! ## Agreement with Mathlib's `Fin`-indexed families -/

/-- `deltaN` is Mathlib's coface. -/
theorem delta_eq (m : ℕ) (j : Fin (m + 2)) : SimplexCategory.δ j = deltaN m (j : ℕ) := by
  refine simplexHom_ext fun k => ?_
  rw [deltaN_val]
  show ((j.succAbove k : Fin (m + 2)) : ℕ) = _
  rcases lt_or_ge (k : ℕ) (j : ℕ) with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    simp [h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)]
    simp [Nat.not_lt.2 h, Fin.val_succ]

/-- `sigmaN` is Mathlib's codegeneracy. -/
theorem sigma_eq (m : ℕ) (i : Fin (m + 1)) : SimplexCategory.σ i = sigmaN m (i : ℕ) := by
  refine simplexHom_ext fun k => ?_
  rw [sigmaN_val]
  show ((i.predAbove k : Fin (m + 1)) : ℕ) = _
  have hk := k.isLt
  have hi := i.isLt
  rcases le_or_gt (k : ℕ) (i : ℕ) with h | h
  · rw [Fin.predAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega), if_pos h,
      Fin.coe_castPred]
    omega
  · rw [Fin.predAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega),
      if_neg (Nat.not_le.2 h), Fin.val_pred]
    omega

/-! ## The simplicial identities used by the prism -/

/-- Simplicial identity, first branch: `δ_b ≫ σ_a = σ_{a-1} ≫ δ_b` for `b < a`. -/
theorem deltaN_comp_sigmaN_lt {n a b : ℕ} (ha : a ≤ n + 1) (hb : b < a) :
    deltaN (n + 1) b ≫ sigmaN (n + 1) a = sigmaN n (a - 1) ≫ deltaN n b := by
  refine simplexHom_ext fun k => ?_
  have hk := k.isLt
  simp only [simplexHom_comp_val, deltaN_val, sigmaN_val]
  split_ifs <;> omega

/-- Simplicial identity, second branch: `δ_b ≫ σ_a = σ_a ≫ δ_{b-1}` for `b > a + 1`. -/
theorem deltaN_comp_sigmaN_gt {n a b : ℕ} (ha : a ≤ n + 1) (hb : a + 1 < b) (hbn : b ≤ n + 2) :
    deltaN (n + 1) b ≫ sigmaN (n + 1) a = sigmaN n a ≫ deltaN n (b - 1) := by
  refine simplexHom_ext fun k => ?_
  have hk := k.isLt
  simp only [simplexHom_comp_val, deltaN_val, sigmaN_val]
  split_ifs <;> omega

/-- Simplicial identity, degenerate branch: `δ_b ≫ σ_a = 𝟙` for `b = a` and for `b = a + 1`.
These are exactly the two faces of the prism that produce the endpoints of the homotopy. -/
theorem deltaN_comp_sigmaN_eq {m a b : ℕ} (ha : a ≤ m) (hb : b = a ∨ b = a + 1) :
    deltaN m b ≫ sigmaN m a = 𝟙 (SimplexCategory.mk m) := by
  refine simplexHom_ext fun k => ?_
  have hk := k.isLt
  simp only [simplexHom_comp_val, deltaN_val, sigmaN_val, simplexHom_id_val]
  rcases hb with rfl | rfl <;> (split_ifs <;> omega)

/-- The behaviour of the cut maps under cofaces. -/
theorem deltaN_comp_betaN (m s r : ℕ) :
    deltaN m s ≫ betaN (m + 1) r = betaN m (if s < r then r - 1 else r) := by
  refine simplexHom_ext fun k => ?_
  have hk := k.isLt
  simp only [simplexHom_comp_val, deltaN_val, betaN_val]
  split_ifs <;> omega

end Mod2Cohomology
