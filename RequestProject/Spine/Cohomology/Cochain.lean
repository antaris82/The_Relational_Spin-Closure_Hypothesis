import Mathlib

/-!
# Task 5, WP2 : native singular `ℤ₂`-cochains

This is the first module of the native mod-2 singular cohomology layer of the Spine.  It is
built **only** on Mathlib primitives (`TopCat`, the singular simplicial set `TopCat.toSSet`,
`SimplexCategory`, `ZMod 2`); no external Lean project is imported, and no module of
`RequestProject.Experiment1` / `RequestProject.Experiment2` is reachable from it.

## Contents

* `Mod2Cohomology.Simplex X n` — the type of singular `n`-simplices of a space `X`, i.e. the
  value of Mathlib's singular simplicial set `TopCat.toSSet.obj X` on `[n]ᵒᵖ`.  Elements are
  (up to Mathlib's packaging) continuous maps `Δⁿ → X`; the carrier is *not* opaque.
* `Mod2Cohomology.reindex` — the contravariant action of a simplex-category morphism on
  singular simplices, with its functoriality lemmas.
* `Mod2Cohomology.face` — the `i`-th face operator, `reindex` along the coface `δ i`.
* `Mod2Cohomology.Cochain X n = Simplex X n → ZMod 2` — singular `n`-cochains, with the
  `ZMod 2`-module structure inherited from the `Pi` type (so `AddCommGroup` and
  `Module (ZMod 2)` are *derived*, never postulated).

Nothing in this file is a hypothesis, a typeclass input or an opaque carrier.
-/

noncomputable section

namespace Mod2Cohomology

open CategoryTheory Opposite

universe u

/-! ## Singular simplices -/

/-- The set of **singular `n`-simplices** of a topological space `X`: the value of Mathlib's
singular simplicial set `TopCat.toSSet.obj X` at `[n]ᵒᵖ`.  Concretely a singular `n`-simplex is
a continuous map from the topological `n`-simplex to `X`. -/
abbrev Simplex (X : TopCat.{u}) (n : ℕ) : Type u :=
  (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))

/-- **Reindexing** of singular simplices along a morphism `a : [m] ⟶ [n]` of the simplex
category: precomposition of a singular `n`-simplex with the affine map induced by `a`.  This is
the contravariant structure map of the singular simplicial set. -/
def reindex {X : TopCat.{u}} {m n : ℕ}
    (a : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (σ : Simplex X n) : Simplex X m :=
  (TopCat.toSSet.obj X).map a.op σ

@[simp] theorem reindex_id {X : TopCat.{u}} {n : ℕ} (σ : Simplex X n) :
    reindex (𝟙 (SimplexCategory.mk n)) σ = σ := by
  simp [reindex]

/-- Functoriality of reindexing: reindexing along `a` after reindexing along `b` is reindexing
along the composite `a ≫ b`.  (The order reversal is the usual contravariance.) -/
theorem reindex_reindex {X : TopCat.{u}} {m n k : ℕ}
    (a : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : SimplexCategory.mk n ⟶ SimplexCategory.mk k) (σ : Simplex X k) :
    reindex a (reindex b σ) = reindex (a ≫ b) σ := by
  unfold reindex
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]

/-- The **`i`-th face** of a singular `(n+1)`-simplex: reindexing along the `i`-th coface
`δ i : [n] ⟶ [n+1]` of the simplex category. -/
def face {X : TopCat.{u}} {n : ℕ} (i : Fin (n + 2)) (σ : Simplex X (n + 1)) : Simplex X n :=
  reindex (SimplexCategory.δ i) σ

theorem face_def {X : TopCat.{u}} {n : ℕ} (i : Fin (n + 2)) (σ : Simplex X (n + 1)) :
    face i σ = reindex (SimplexCategory.δ i) σ := rfl

/-- Two successive faces are one reindexing along a composite of two cofaces.  This is the
only input needed for `δ² = 0` besides the cosimplicial identity `SimplexCategory.δ_comp_δ`. -/
theorem face_face {X : TopCat.{u}} {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2))
    (σ : Simplex X (n + 2)) :
    face j (face i σ) = reindex (SimplexCategory.δ j ≫ SimplexCategory.δ i) σ :=
  reindex_reindex _ _ σ

/-! ## Cochains -/

/-- **Singular `n`-cochains with `ℤ/2` coefficients**: `ℤ/2`-valued functions on the singular
`n`-simplices.  This is a genuine function type; its `AddCommGroup` and `Module (ZMod 2)`
structures are the ones Mathlib derives for `Pi` types. -/
abbrev Cochain (X : TopCat.{u}) (n : ℕ) : Type u := Simplex X n → ZMod 2

example (X : TopCat.{u}) (n : ℕ) : AddCommGroup (Cochain X n) := inferInstance
example (X : TopCat.{u}) (n : ℕ) : Module (ZMod 2) (Cochain X n) := inferInstance

@[simp] theorem Cochain.add_apply {X : TopCat.{u}} {n : ℕ} (f g : Cochain X n)
    (σ : Simplex X n) : (f + g) σ = f σ + g σ := rfl

@[simp] theorem Cochain.zero_apply {X : TopCat.{u}} {n : ℕ} (σ : Simplex X n) :
    (0 : Cochain X n) σ = 0 := rfl

@[simp] theorem Cochain.smul_apply {X : TopCat.{u}} {n : ℕ} (c : ZMod 2) (f : Cochain X n)
    (σ : Simplex X n) : (c • f) σ = c * f σ := rfl

/-- Cochains are determined by their values on simplices. -/
theorem Cochain.ext {X : TopCat.{u}} {n : ℕ} {f g : Cochain X n}
    (h : ∀ σ, f σ = g σ) : f = g := funext h

end Mod2Cohomology
