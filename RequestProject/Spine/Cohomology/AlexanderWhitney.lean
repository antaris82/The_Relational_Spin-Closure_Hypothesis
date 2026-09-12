import RequestProject.Spine.Cohomology.Cohomology

/-!
# Task 5, WP6 (part 1) : the Alexander–Whitney front/back inclusions

The Alexander–Whitney cup product of a `p`-cochain and a `q`-cochain evaluates the two factors
on the *front `p`-face* and the *back `q`-face* of a `(p+q)`-simplex.  Both faces are
reindexings along explicit monotone injections of the simplex category:

* `frontIncl p q : [p] ⟶ [p+q]`, `i ↦ i`             (the first `p+1` vertices);
* `backIncl p q  : [q] ⟶ [p+q]`, `i ↦ i + p`         (the last `q+1` vertices).

For the Leibniz rule one also needs the two "shifted" inclusions into `[p+q+1]`

* `frontBig p q   : [p+1] ⟶ [p+q+1]`, `i ↦ i`;
* `backSmall p q  : [q] ⟶ [p+q+1]`,  `i ↦ i + p + 1`,

which cannot be obtained from `frontIncl` / `backIncl` by re-instantiating the indices,
because `(p+1)+q` and `(p+q)+1` are not definitionally equal in Lean for a variable `q`.
(`frontIncl p (q+1)` and `backIncl p (q+1)` *do* land in `[p+q+1]`, since `p+(q+1)` reduces to
`(p+q)+1`, and are reused as the small front face and the big back face.)

This module records these four maps and the six composition identities with the cofaces `δ i`
that drive the Leibniz rule in `RequestProject.Spine.Cohomology.Cup`.
-/

noncomputable section

namespace Mod2Cohomology

open CategoryTheory Opposite SimplexCategory

/-! ## The four inclusions -/

/-- The front inclusion `[p] ⟶ [p+q]`, `i ↦ i`. -/
def frontIncl (p q : ℕ) : SimplexCategory.mk p ⟶ SimplexCategory.mk (p + q) :=
  SimplexCategory.mkHom ⟨fun i => ⟨i.val, by omega⟩, fun _ _ h => Fin.mk_le_mk.mpr h⟩

/-- The back inclusion `[q] ⟶ [p+q]`, `i ↦ i + p`. -/
def backIncl (p q : ℕ) : SimplexCategory.mk q ⟶ SimplexCategory.mk (p + q) :=
  SimplexCategory.mkHom
    ⟨fun i => ⟨i.val + p, by omega⟩, fun _ _ h => Fin.mk_le_mk.mpr (Nat.add_le_add_right h p)⟩

/-- The shifted front inclusion `[p+1] ⟶ [p+q+1]`, `i ↦ i`. -/
def frontBig (p q : ℕ) : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk (p + q + 1) :=
  SimplexCategory.mkHom ⟨fun i => ⟨i.val, by omega⟩, fun _ _ h => Fin.mk_le_mk.mpr h⟩

/-- The shifted back inclusion `[q] ⟶ [p+q+1]`, `i ↦ i + p + 1`. -/
def backSmall (p q : ℕ) : SimplexCategory.mk q ⟶ SimplexCategory.mk (p + q + 1) :=
  SimplexCategory.mkHom
    ⟨fun i => ⟨i.val + p + 1, by omega⟩,
      fun _ _ h => Fin.mk_le_mk.mpr (Nat.add_le_add_right (Nat.add_le_add_right h p) 1)⟩

/-! ## The six composition identities

They express, for a `(p+q+1)`-simplex, how the front and back faces of a face `∂ᵢ τ` relate to
the faces of the front and back faces of `τ`. -/

/-- For `i ≤ p`: the front `p`-face of `∂ᵢ τ` is the `i`-th face of the front `(p+1)`-face
of `τ`. -/
theorem frontIncl_comp_delta_of_le (p q : ℕ) (i : Fin (p + q + 2)) (h : i.val ≤ p) :
    frontIncl p q ≫ SimplexCategory.δ i
      = SimplexCategory.δ (⟨i.val, by omega⟩ : Fin (p + 2)) ≫ frontBig p q := by
  ext k
  have hk : k.val < p + 1 := k.isLt
  dsimp [frontIncl, frontBig, δ, Fin.succAbove]
  split_ifs with h1 h2
  · rfl
  · exfalso; simp only [Fin.lt_def, Fin.val_castSucc] at *; omega
  · exfalso; simp only [Fin.lt_def, Fin.val_castSucc] at *; omega
  · rfl

/-- For `i ≤ p`: the back `q`-face of `∂ᵢ τ` is the (shifted) back `q`-face of `τ`. -/
theorem backIncl_comp_delta_of_le (p q : ℕ) (i : Fin (p + q + 2)) (h : i.val ≤ p) :
    backIncl p q ≫ SimplexCategory.δ i = backSmall p q := by
  ext k
  have hk : k.val < q + 1 := k.isLt
  dsimp [backIncl, backSmall, δ, Fin.succAbove]
  split_ifs with h1
  · exfalso; simp only [Fin.lt_def] at *; omega
  · show _ = (k : ℕ) + p + 1
    rfl

/-- For `i > p`: the front `p`-face of `∂ᵢ τ` is the (small) front `p`-face of `τ`. -/
theorem frontIncl_comp_delta_of_gt (p q : ℕ) (i : Fin (p + q + 2)) (h : p < i.val) :
    frontIncl p q ≫ SimplexCategory.δ i = frontIncl p (q + 1) := by
  ext k
  have hk : k.val < p + 1 := k.isLt
  dsimp [frontIncl, δ, Fin.succAbove]
  split_ifs with h1
  · rfl
  · exfalso; apply h1; rw [Fin.lt_def]; show (k : ℕ) < (i : ℕ); omega

/-- For `i > p`: the back `q`-face of `∂ᵢ τ` is the `(i-p)`-th face of the big back
`(q+1)`-face of `τ`. -/
theorem backIncl_comp_delta_of_gt (p q : ℕ) (i : Fin (p + q + 2)) (h : p < i.val) :
    backIncl p q ≫ SimplexCategory.δ i
      = SimplexCategory.δ (⟨i.val - p, by omega⟩ : Fin (q + 2)) ≫ backIncl p (q + 1) := by
  ext k
  have hk : k.val < q + 1 := k.isLt
  dsimp [backIncl, δ, Fin.succAbove]
  split_ifs with h1 h2
  · rfl
  · exfalso; simp only [Fin.lt_def, Fin.val_castSucc] at *; omega
  · exfalso; simp only [Fin.lt_def, Fin.val_castSucc] at *; omega
  · show _ = (k : ℕ) + 1 + p
    dsimp only
    omega

/-- The last face of the front `(p+1)`-face is the small front `p`-face. -/
theorem delta_last_comp_frontBig (p q : ℕ) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫ frontBig p q = frontIncl p (q + 1) := by
  ext k
  have hk : k.val < p + 1 := k.isLt
  dsimp [frontIncl, frontBig, δ, Fin.succAbove]
  split_ifs with h1
  · rfl
  · exfalso; apply h1; rw [Fin.lt_def]; show (k : ℕ) < p + 1; omega

/-- The zeroth face of the big back `(q+1)`-face is the shifted back `q`-face. -/
theorem delta_zero_comp_backIncl (p q : ℕ) :
    SimplexCategory.δ (0 : Fin (q + 2)) ≫ backIncl p (q + 1) = backSmall p q := by
  ext k
  have hk : k.val < q + 1 := k.isLt
  dsimp [backIncl, backSmall, δ, Fin.succAbove]
  show _ = (k : ℕ) + p + 1
  omega

end Mod2Cohomology
