import RequestProject.Spine.Cohomology.Cohomology

/-!
# Task 5, WP5 : functoriality of the native singular mod-2 cohomology

For a continuous map `f : X ⟶ Y` of spaces we construct the pullback of cochains, prove that
it is a map of cochain complexes (`f* ∘ δ = δ ∘ f*`), and descend it to cohomology.  The two
functor laws `(𝟙 X)* = id` and `(f ≫ g)* = f* ∘ g*` are proved both on cochains and on
cohomology.

Everything rests on the *naturality* of Mathlib's singular simplicial-set functor
`TopCat.toSSet`: the induced map on singular simplices commutes with reindexing, hence with
the face operators; no separate compatibility is postulated.

## Contents

* `Mod2Cohomology.simplexMap` — the pushforward on singular simplices, with
  `simplexMap_reindex` and `simplexMap_face`;
* `Mod2Cohomology.pullback` — `f* : Cⁿ(Y;ℤ₂) →ₗ Cⁿ(X;ℤ₂)`;
* `Mod2Cohomology.pullback_d` — `f* ∘ δ = δ ∘ f*`;
* `Mod2Cohomology.cocyclesMap`, `Mod2Cohomology.Hmap` — the induced maps on `Zⁿ` and `Hⁿ`;
* `Mod2Cohomology.Hmap_id`, `Mod2Cohomology.Hmap_comp` — functoriality on cohomology.
-/

noncomputable section

namespace Mod2Cohomology

open CategoryTheory Opposite

universe u

variable {X Y Z : TopCat.{u}}

/-! ## Pushforward of singular simplices -/

/-- The map induced by a continuous map on singular `n`-simplices: postcomposition with `f`,
i.e. the `n`-th component of `TopCat.toSSet.map f`. -/
def simplexMap (f : X ⟶ Y) (n : ℕ) (σ : Simplex X n) : Simplex Y n :=
  (TopCat.toSSet.map f).app (op (SimplexCategory.mk n)) σ

/-- **Naturality**: the pushforward of singular simplices commutes with reindexing along any
morphism of the simplex category. -/
theorem simplexMap_reindex (f : X ⟶ Y) {m n : ℕ}
    (a : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (σ : Simplex X n) :
    simplexMap f m (reindex a σ) = reindex a (simplexMap f n σ) := by
  have h := (TopCat.toSSet.map f).naturality a.op
  exact (congrFun h σ).symm

/-- In particular the pushforward commutes with the face operators. -/
theorem simplexMap_face (f : X ⟶ Y) {n : ℕ} (i : Fin (n + 2)) (σ : Simplex X (n + 1)) :
    simplexMap f n (face i σ) = face i (simplexMap f (n + 1) σ) :=
  simplexMap_reindex f _ σ

@[simp] theorem simplexMap_id {n : ℕ} (σ : Simplex X n) : simplexMap (𝟙 X) n σ = σ := by
  simp [simplexMap]

theorem simplexMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) {n : ℕ} (σ : Simplex X n) :
    simplexMap (f ≫ g) n σ = simplexMap g n (simplexMap f n σ) := by
  simp [simplexMap]

/-! ## Pullback of cochains -/

/-- The **pullback of cochains** `f* : Cⁿ(Y;ℤ₂) →ₗ Cⁿ(X;ℤ₂)`, precomposition with the
pushforward of singular simplices. -/
def pullback (f : X ⟶ Y) (n : ℕ) : Cochain Y n →ₗ[ZMod 2] Cochain X n where
  toFun c := fun σ => c (simplexMap f n σ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pullback_apply (f : X ⟶ Y) (n : ℕ) (c : Cochain Y n) (σ : Simplex X n) :
    pullback f n c σ = c (simplexMap f n σ) := rfl

/-- **`f*` is a map of cochain complexes**: `f*(δ c) = δ (f* c)`. -/
theorem pullback_d (f : X ⟶ Y) (n : ℕ) (c : Cochain Y n) :
    pullback f (n + 1) (d Y n c) = d X n (pullback f n c) := by
  funext σ
  simp only [pullback_apply, d_apply_simplex]
  exact Finset.sum_congr rfl fun i _ => by rw [simplexMap_face]

@[simp] theorem pullback_id (n : ℕ) (c : Cochain X n) : pullback (𝟙 X) n c = c := by
  funext σ; simp

theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (c : Cochain Z n) :
    pullback (f ≫ g) n c = pullback f n (pullback g n c) := by
  funext σ; simp [simplexMap_comp]

/-! ## The induced maps on cocycles, coboundaries and cohomology -/

theorem pullback_mem_cocycles (f : X ⟶ Y) (n : ℕ) {c : Cochain Y n} (hc : c ∈ cocycles Y n) :
    pullback f n c ∈ cocycles X n := by
  rw [mem_cocycles_iff] at hc ⊢
  rw [← pullback_d f n c, hc, map_zero]

/-- The induced map on cocycles `Zⁿ(Y;ℤ₂) →ₗ Zⁿ(X;ℤ₂)`. -/
def cocyclesMap (f : X ⟶ Y) (n : ℕ) : cocycles Y n →ₗ[ZMod 2] cocycles X n :=
  (pullback f n).restrict (fun _ hc => pullback_mem_cocycles f n hc)

@[simp] theorem cocyclesMap_coe (f : X ⟶ Y) (n : ℕ) (z : cocycles Y n) :
    ((cocyclesMap f n z : cocycles X n) : Cochain X n) = pullback f n (z : Cochain Y n) := rfl

theorem pullback_mem_coboundaries (f : X ⟶ Y) (n : ℕ) {c : Cochain Y n}
    (hc : c ∈ coboundaries Y n) : pullback f n c ∈ coboundaries X n := by
  cases n with
  | zero =>
      rw [coboundaries_zero, Submodule.mem_bot] at hc
      rw [coboundaries_zero, Submodule.mem_bot, hc, map_zero]
  | succ n =>
      obtain ⟨b, rfl⟩ := hc
      exact ⟨pullback f n b, (pullback_d f n b).symm⟩

theorem cocyclesMap_mem (f : X ⟶ Y) (n : ℕ) {z : cocycles Y n} (hz : z ∈ coboundariesIn Y n) :
    cocyclesMap f n z ∈ coboundariesIn X n :=
  pullback_mem_coboundaries f n hz

/-- The **induced map on cohomology** `f* : Hⁿ(Y;ℤ₂) →ₗ Hⁿ(X;ℤ₂)`. -/
def Hmap (f : X ⟶ Y) (n : ℕ) : Cohomology Y n →ₗ[ZMod 2] Cohomology X n :=
  Submodule.mapQ (coboundariesIn Y n) (coboundariesIn X n) (cocyclesMap f n)
    (fun _ hz => cocyclesMap_mem f n hz)

@[simp] theorem Hmap_mk (f : X ⟶ Y) (n : ℕ) (z : cocycles Y n) :
    Hmap f n (mk z) = mk (cocyclesMap f n z) := rfl

/-- Functoriality, unit law: `(𝟙 X)* = id` on `Hⁿ`. -/
theorem Hmap_id (n : ℕ) : Hmap (𝟙 X) n = LinearMap.id := by
  ext x
  obtain ⟨z, rfl⟩ := mk_surjective x
  exact congrArg mk (Subtype.ext (pullback_id n (z : Cochain X n)))

/-- Functoriality, composition law: `(f ≫ g)* = f* ∘ g*` on `Hⁿ`. -/
theorem Hmap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    Hmap (f ≫ g) n = (Hmap f n).comp (Hmap g n) := by
  ext x
  obtain ⟨z, rfl⟩ := mk_surjective x
  exact congrArg mk (Subtype.ext (pullback_comp f g n (z : Cochain Z n)))

end Mod2Cohomology
