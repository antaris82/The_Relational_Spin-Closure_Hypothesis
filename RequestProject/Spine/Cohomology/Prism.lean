import RequestProject.Spine.Cohomology.PrismMaps
import RequestProject.Spine.Cohomology.CharTwo
import RequestProject.Spine.Cohomology.Functorial

/-!
# Task 8, WP3 : the native singular prism operator

Let `H : X × I → Y` be a homotopy from `f` to `g`.  The classical prism decomposition of
`Δⁿ × I` into `n+1` simplices produces, for every singular `n`-simplex `s` of `X`, a family of
singular `(n+1)`-simplices of `Y`

```
    h_i(s) = H ∘ (s × id) ∘ p_i ,        i = 0, …, n
```

where `p_i : Δⁿ⁺¹ → Δⁿ × I` is the affine map sending the vertices `0,…,i` to
`(0,0),…,(i,0)` and the vertices `i+1,…,n+1` to `(i,1),…,(n,1)`.  In the native Task-5 model a
singular simplex *is* a continuous map `Δᵏ → X` (Mathlib's `TopCat.toSSet` is the restricted
Yoneda embedding along `SimplexCategory.toTop`), so `p_i` can be described completely by a pair
of morphisms of the simplex category:

* `sigmaN n i : [n+1] ⟶ [n]`, the `Δⁿ`-component, and
* `betaN (n+1) (i+1) : [n+1] ⟶ [1]`, the `I`-component.

This is the definition of `Mod2Cohomology.prismPiece` below: it is genuinely the standard
prism, not a substitute, and *all* of its face identities are consequences of the simplicial
identities of `PrismMaps.lean` together with functoriality of `SimplexCategory.toTop`.

## Contents

* `Mod2Cohomology.unitCoord` — the interval coordinate `Δ¹ → I`;
* `Mod2Cohomology.prismPiece H a b s` — the singular simplex `t ↦ H(β(t), s(α(t)))`;
* `Mod2Cohomology.reindex_prismPiece`, `Mod2Cohomology.prismPiece_reindex` — the two
  functorialities;
* `Mod2Cohomology.prismPiece_betaN_zero`, `Mod2Cohomology.prismPiece_betaN_top` — the two
  endpoint identifications, from `H(1,·) = g` and `H(0,·) = f`;
* `Mod2Cohomology.prism H i s` — the `i`-th prism simplex;
* `Mod2Cohomology.prismK H n : Cⁿ⁺¹(Y;ℤ₂) →ₗ Cⁿ(X;ℤ₂)` — the cochain-level prism operator;
* `Mod2Cohomology.prismK_identity` — **the chain-homotopy identity**
  `δ ∘ K + K ∘ δ = g* + f*` in every degree `n+1`, and
  `Mod2Cohomology.prismK_identity_zero` — its degree-zero form `K ∘ δ = g* + f*`.

The `+` on the right-hand side is the characteristic-two form of the classical `g_# - f_#`;
the translation is `Mod2Cohomology.CharTwo.signed_vs_unsigned`.
-/

noncomputable section

namespace Mod2Cohomology

open CategoryTheory Opposite SimplexCategory

universe u

/-! ## The topological standard simplex, concretely -/

/-- The topological standard `n`-simplex, as the object of `TopCat` that represents singular
`n`-simplices. -/
abbrev Dtop (n : ℕ) : TopCat.{u} := SimplexCategory.toTop.obj (SimplexCategory.mk n)

/-- The barycentric coordinates of a point of the topological standard simplex. -/
def coord {n : ℕ} (t : Dtop.{u} n) (k : Fin (n + 1)) : ℝ := t.down.val k

theorem coord_nonneg {n : ℕ} (t : Dtop.{u} n) (k : Fin (n + 1)) : 0 ≤ coord t k := t.down.2.1 k

theorem coord_sum {n : ℕ} (t : Dtop.{u} n) : ∑ k, coord t k = 1 := t.down.2.2

/-- The coordinates of the image of a point under the affine map induced by a morphism of the
simplex category: the `k`-th coordinate is the sum of the coordinates of the fibre. -/
theorem coord_toTop_map {m n : ℕ} (a : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (t : Dtop.{u} m) (k : Fin (n + 1)) :
    coord ((SimplexCategory.toTop.map a) t) k
      = ∑ l ∈ Finset.univ.filter (fun l => a.toOrderHom l = k), coord t l := by
  show (FunOnFinite.linearMap ℝ ℝ (⇑(ConcreteCategory.hom a)) t.down.val) k = _
  rw [FunOnFinite.linearMap_apply_apply]
  rfl

/-- The **interval coordinate** `Δ¹ → I`, the last barycentric coordinate. -/
def unitCoord : C(Dtop.{u} 1, unitInterval) where
  toFun t := ⟨t.down.val 1, ⟨t.down.2.1 1, stdSimplex.le_one t.down 1⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_apply (1 : Fin 2)).comp continuous_subtype_val).comp continuous_uliftDown

theorem unitCoord_betaN_zero {m : ℕ} (t : Dtop.{u} m) :
    unitCoord ((SimplexCategory.toTop.map (betaN m 0)) t) = 1 := by
  apply Subtype.ext
  show coord ((SimplexCategory.toTop.map (betaN m 0)) t) 1 = 1
  rw [coord_toTop_map, Finset.filter_true_of_mem (fun l _ => by
    apply Fin.ext; rw [betaN_val]; simp)]
  exact coord_sum t

theorem unitCoord_betaN_top {m r : ℕ} (hr : m < r) (t : Dtop.{u} m) :
    unitCoord ((SimplexCategory.toTop.map (betaN m r)) t) = 0 := by
  apply Subtype.ext
  show coord ((SimplexCategory.toTop.map (betaN m r)) t) 1 = 0
  rw [coord_toTop_map, Finset.filter_false_of_mem (fun l _ hl => by
    have h1 : ((betaN m r).toOrderHom l : ℕ) = 1 := by rw [hl]; rfl
    rw [betaN_val] at h1
    have hl2 : (l : ℕ) < m + 1 := l.isLt
    split at h1 <;> omega)]
  simp

/-! ## Singular simplices as continuous maps -/

variable {X Y : TopCat.{u}}

/-- A singular simplex, viewed as the continuous map it is. -/
def toMap {n : ℕ} (s : Simplex X n) : Dtop.{u} n ⟶ X := ULift.down s

/-- A continuous map `Δⁿ → X`, viewed as a singular simplex. -/
def ofMap {n : ℕ} (p : Dtop.{u} n ⟶ X) : Simplex X n := ULift.up p

theorem simplex_ext {n : ℕ} {s s' : Simplex X n} (h : ∀ t, toMap s t = toMap s' t) : s = s' := by
  apply ULift.ext
  exact TopCat.ext h

@[simp] theorem toMap_reindex {m n : ℕ} (a : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (s : Simplex X n) (t : Dtop.{u} m) :
    toMap (reindex a s) t = toMap s ((SimplexCategory.toTop.map a) t) := rfl

@[simp] theorem toMap_simplexMap (p : X ⟶ Y) (n : ℕ) (s : Simplex X n) (t : Dtop.{u} n) :
    toMap (simplexMap p n s) t = p (toMap s t) := rfl

theorem toTop_map_comp_apply {a b c : ℕ} (p : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (q : SimplexCategory.mk b ⟶ SimplexCategory.mk c) (t : Dtop.{u} a) :
    (SimplexCategory.toTop.map (p ≫ q)) t
      = (SimplexCategory.toTop.map q) ((SimplexCategory.toTop.map p) t) := by
  rw [Functor.map_comp]; rfl

/-! ## The prism simplices -/

variable {f g : X ⟶ Y}

/-- **A prism piece.**  Given a homotopy `H` from `f` to `g`, a "shape" morphism `a : [k] ⟶ [m]`
and a "cut" morphism `b : [k] ⟶ [1]`, this is the singular `k`-simplex of `Y`

```
    t ↦ H ( b(t) , s(a(t)) ) .
```

Every simplex occurring in the prism decomposition and in all its faces is of this form. -/
def prismPiece (H : ContinuousMap.Homotopy f.hom g.hom) {k m : ℕ}
    (a : SimplexCategory.mk k ⟶ SimplexCategory.mk m)
    (b : SimplexCategory.mk k ⟶ SimplexCategory.mk 1) (s : Simplex X m) : Simplex Y k :=
  ofMap (TopCat.ofHom
    { toFun := fun t => H (unitCoord ((SimplexCategory.toTop.map b) t),
        (toMap s) ((SimplexCategory.toTop.map a) t))
      continuous_toFun := by
        apply H.continuous.comp
        exact (unitCoord.continuous.comp (SimplexCategory.toTop.map b).hom.continuous).prodMk
          ((toMap s).hom.continuous.comp (SimplexCategory.toTop.map a).hom.continuous) })

@[simp] theorem toMap_prismPiece (H : ContinuousMap.Homotopy f.hom g.hom) {k m : ℕ}
    (a : SimplexCategory.mk k ⟶ SimplexCategory.mk m)
    (b : SimplexCategory.mk k ⟶ SimplexCategory.mk 1) (s : Simplex X m) (t : Dtop.{u} k) :
    toMap (prismPiece H a b s) t
      = H (unitCoord ((SimplexCategory.toTop.map b) t),
          (toMap s) ((SimplexCategory.toTop.map a) t)) := rfl

/-- Reindexing a prism piece composes both of its structure morphisms. -/
theorem reindex_prismPiece (H : ContinuousMap.Homotopy f.hom g.hom) {j k m : ℕ}
    (c : SimplexCategory.mk j ⟶ SimplexCategory.mk k)
    (a : SimplexCategory.mk k ⟶ SimplexCategory.mk m)
    (b : SimplexCategory.mk k ⟶ SimplexCategory.mk 1) (s : Simplex X m) :
    reindex c (prismPiece H a b s) = prismPiece H (c ≫ a) (c ≫ b) s := by
  refine simplex_ext fun t => ?_
  rw [toMap_reindex, toMap_prismPiece, toMap_prismPiece,
    toTop_map_comp_apply, toTop_map_comp_apply]

/-- Reindexing the input of a prism piece composes its shape morphism. -/
theorem prismPiece_reindex (H : ContinuousMap.Homotopy f.hom g.hom) {k m m' : ℕ}
    (a : SimplexCategory.mk k ⟶ SimplexCategory.mk m)
    (b : SimplexCategory.mk k ⟶ SimplexCategory.mk 1)
    (c : SimplexCategory.mk m ⟶ SimplexCategory.mk m') (s : Simplex X m') :
    prismPiece H a b (reindex c s) = prismPiece H (a ≫ c) b s := by
  refine simplex_ext fun t => ?_
  rw [toMap_prismPiece, toMap_prismPiece, toMap_reindex, toTop_map_comp_apply]

/-- **First endpoint.**  A prism piece whose cut morphism is `betaN k 0` (constantly `1` on
`Δ¹`) is the pushforward along `g`. -/
theorem prismPiece_betaN_zero (H : ContinuousMap.Homotopy f.hom g.hom) {k m : ℕ}
    (a : SimplexCategory.mk k ⟶ SimplexCategory.mk m) (s : Simplex X m) :
    prismPiece H a (betaN k 0) s = simplexMap g k (reindex a s) := by
  refine simplex_ext fun t => ?_
  rw [toMap_prismPiece, toMap_simplexMap, toMap_reindex, unitCoord_betaN_zero]
  exact H.apply_one _

/-- **Second endpoint.**  A prism piece whose cut morphism is `betaN k r` with `r > k`
(constantly `0` on `Δ¹`) is the pushforward along `f`. -/
theorem prismPiece_betaN_top (H : ContinuousMap.Homotopy f.hom g.hom) {k m r : ℕ} (hr : k < r)
    (a : SimplexCategory.mk k ⟶ SimplexCategory.mk m) (s : Simplex X m) :
    prismPiece H a (betaN k r) s = simplexMap f k (reindex a s) := by
  refine simplex_ext fun t => ?_
  rw [toMap_prismPiece, toMap_simplexMap, toMap_reindex, unitCoord_betaN_top hr]
  exact H.apply_zero _

/-- **The `i`-th prism simplex** of a singular `m`-simplex `s`: the standard `(m+1)`-simplex
`[v₀ … v_i w_i … w_m]` of the prism `Δᵐ × I`, pushed into `Y` by the homotopy. -/
def prism (H : ContinuousMap.Homotopy f.hom g.hom) {m : ℕ} (i : Fin (m + 1))
    (s : Simplex X m) : Simplex Y (m + 1) :=
  prismPiece H (sigmaN m (i : ℕ)) (betaN (m + 1) ((i : ℕ) + 1)) s

/-! ## The cochain-level prism operator -/

/-- **The prism operator on cochains** `K : Cⁿ⁺¹(Y;ℤ₂) →ₗ Cⁿ(X;ℤ₂)`, the mod-2 sum of the
values of a cochain on the `n+1` prism simplices.  This is the transpose of the classical chain
prism `P : Cₙ(X) → Cₙ₊₁(Y)`. -/
def prismK (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) :
    Cochain Y (n + 1) →ₗ[ZMod 2] Cochain X n where
  toFun c := fun s => ∑ i : Fin (n + 1), c (prism H i s)
  map_add' _ _ := by funext s; simp [Finset.sum_add_distrib]
  map_smul' _ _ := by funext s; simp [Finset.mul_sum]

@[simp] theorem prismK_apply (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ)
    (c : Cochain Y (n + 1)) (s : Simplex X n) :
    prismK H n c s = ∑ i : Fin (n + 1), c (prism H i s) := rfl


/-! ## Faces of the prism simplices -/

/-- Every face of a prism simplex is again a prism piece, with the two structure morphisms
precomposed by a coface. -/
theorem face_prism (H : ContinuousMap.Homotopy f.hom g.hom) {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 3)) (s : Simplex X (n + 1)) :
    face j (prism H i s)
      = prismPiece H (deltaN (n + 1) (j : ℕ) ≫ sigmaN (n + 1) (i : ℕ))
          (deltaN (n + 1) (j : ℕ) ≫ betaN (n + 2) ((i : ℕ) + 1)) s := by
  rw [face_def, prism, delta_eq, reindex_prismPiece]

/-- A prism simplex of a face is a prism piece, with the shape morphism postcomposed by a
coface. -/
theorem prism_face (H : ContinuousMap.Homotopy f.hom g.hom) {n : ℕ} (i : Fin (n + 1))
    (j : Fin (n + 2)) (s : Simplex X (n + 1)) :
    prism H i (face j s)
      = prismPiece H (sigmaN n (i : ℕ) ≫ deltaN n (j : ℕ)) (betaN (n + 1) ((i : ℕ) + 1)) s := by
  rw [face_def, prism, delta_eq, prismPiece_reindex]

/-! ## The combinatorial core of the prism identity -/

/-- A telescoping sum in characteristic two: consecutive terms cancel and only the two ends
survive.  This is where the two families of degenerate prism faces annihilate each other. -/
theorem telescope_charTwo (A : ℕ → ZMod 2) (N : ℕ) :
    ∑ a ∈ Finset.range (N + 1), (A a + A (a + 1)) = A 0 + A (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have h : ∀ x y z : ZMod 2, (x + y) + (y + z) = x + z := by decide
      exact h _ _ _

/-- **The double-sum identity underlying the prism relation**, isolated as a statement about
three arbitrary families of elements of `ZMod 2` satisfying the four face relations.

`T a b` stands for the `b`-th face of the `a`-th prism simplex, `S a b` for the `a`-th prism
simplex of the `b`-th face, and `A r` for a degenerate prism face.  The hypotheses are exactly
the four simplicial identities; the conclusion is that the two double sums differ by the two
endpoint terms. -/
theorem prism_double_sum (n : ℕ) (S T : ℕ → ℕ → ZMod 2) (A : ℕ → ZMod 2)
    (hlt : ∀ a b, a ≤ n + 1 → b < a → T a b = S (a - 1) b)
    (hgt : ∀ a b, a ≤ n + 1 → a + 1 < b → b ≤ n + 2 → T a b = S a (b - 1))
    (hd1 : ∀ a, a ≤ n + 1 → T a a = A a)
    (hd2 : ∀ a, a ≤ n + 1 → T a (a + 1) = A (a + 1)) :
    (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 2), S a b)
      + (∑ a ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 3), T a b)
      = A 0 + A (n + 2) := by
  have hrow : ∀ a ∈ Finset.range (n + 2),
      (∑ b ∈ Finset.range (n + 3), T a b)
        = (∑ b ∈ Finset.range a, S (a - 1) b) + (A a + A (a + 1))
          + ∑ i ∈ Finset.range (n + 1 - a), S a (a + 1 + i) := by
    intro a ha
    have ha' : a ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have e1 : (∑ b ∈ Finset.range (n + 3), T a b)
        = (∑ b ∈ Finset.Ico 0 a, T a b) + (∑ b ∈ Finset.Ico a (a + 2), T a b)
          + ∑ b ∈ Finset.Ico (a + 2) (n + 3), T a b := by
      rw [Finset.sum_Ico_consecutive _ (Nat.zero_le a) (by omega),
        Finset.sum_Ico_consecutive _ (Nat.zero_le (a + 2)) (by omega), Finset.range_eq_Ico]
    rw [e1]
    congr 1
    · congr 1
      · rw [← Finset.range_eq_Ico]
        exact Finset.sum_congr rfl fun b hb => hlt a b ha' (Finset.mem_range.mp hb)
      · rw [Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega),
          Finset.Ico_self, Finset.sum_empty, zero_add, hd1 a ha', hd2 a ha']
    · rw [Finset.sum_Ico_eq_sum_range]
      have he : n + 3 - (a + 2) = n + 1 - a := by omega
      rw [he]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      rw [hgt a (a + 2 + i) ha' (by omega) (by omega)]
      congr 1
      omega
  rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, Finset.sum_add_distrib,
    telescope_charTwo A (n + 1)]
  have hP1 : (∑ a ∈ Finset.range (n + 2), ∑ b ∈ Finset.range a, S (a - 1) b)
      = ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (a + 1), S a b := by
    rw [Finset.sum_range_succ' (fun a => ∑ b ∈ Finset.range a, S (a - 1) b) (n + 1)]
    simp
  have hP3 : (∑ a ∈ Finset.range (n + 2), ∑ i ∈ Finset.range (n + 1 - a), S a (a + 1 + i))
      = ∑ a ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1 - a), S a (a + 1 + i) := by
    rw [Finset.sum_range_succ]
    simp
  rw [hP1, hP3]
  have hcomb : (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (a + 1), S a b)
      + (∑ a ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1 - a), S a (a + 1 + i))
      = ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 2), S a b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have h2 : (∑ i ∈ Finset.range (n + 1 - a), S a (a + 1 + i))
        = ∑ b ∈ Finset.Ico (a + 1) (n + 2), S a b := by
      rw [Finset.sum_Ico_eq_sum_range]
      have he : n + 2 - (a + 1) = n + 1 - a := by omega
      rw [he]
    rw [h2]
    simp only [Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le (a + 1)) (by omega)
  rw [show (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 2), S a b) +
      ((∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (a + 1), S a b) +
        (A 0 + A (n + 1 + 1)) +
        ∑ a ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1 - a), S a (a + 1 + i))
      = (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 2), S a b) +
        (((∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (a + 1), S a b) +
          ∑ a ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1 - a), S a (a + 1 + i))
          + (A 0 + A (n + 1 + 1))) from by ring, hcomb]
  have h2 : ∀ x y : ZMod 2, x + (x + y) = y := by decide
  exact h2 _ _

/-! ## The prism identity -/

/-- **The chain-homotopy identity of the prism operator**, in the degree-`(n+1)` form

```
    δ ∘ K + K ∘ δ  =  g*  +  f*  .
```

Over signed coefficients the right-hand side would be `g* - f*`; in characteristic two the two
statements are the same, see `Mod2Cohomology.CharTwo.signed_vs_unsigned`.  The identity is
*proved*, not postulated: the two double sums of faces of prism simplices and of prism
simplices of faces cancel term by term via `Mod2Cohomology.prism_double_sum`, and the surviving
terms are exactly the two endpoints of the homotopy. -/
theorem prismK_identity (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ)
    (c : Cochain Y (n + 1)) :
    d X n (prismK H n c) + prismK H (n + 1) (d Y (n + 1) c)
      = pullback g (n + 1) c + pullback f (n + 1) c := by
  funext s
  set S : ℕ → ℕ → ZMod 2 := fun a b =>
    c (prismPiece H (sigmaN n a ≫ deltaN n b) (betaN (n + 1) (a + 1)) s) with hSdef
  set T : ℕ → ℕ → ZMod 2 := fun a b =>
    c (prismPiece H (deltaN (n + 1) b ≫ sigmaN (n + 1) a)
        (deltaN (n + 1) b ≫ betaN (n + 2) (a + 1)) s) with hTdef
  set A : ℕ → ZMod 2 := fun r =>
    c (prismPiece H (𝟙 (SimplexCategory.mk (n + 1))) (betaN (n + 1) r) s) with hAdef
  -- the four face relations
  have hlt : ∀ a b, a ≤ n + 1 → b < a → T a b = S (a - 1) b := by
    intro a b ha hb
    have h1 := deltaN_comp_sigmaN_lt (n := n) ha hb
    have h2 : deltaN (n + 1) b ≫ betaN (n + 2) (a + 1) = betaN (n + 1) ((a - 1) + 1) := by
      rw [deltaN_comp_betaN, if_pos (by omega)]
      congr 1
      omega
    simp only [hSdef, hTdef, h1, h2]
  have hgt : ∀ a b, a ≤ n + 1 → a + 1 < b → b ≤ n + 2 → T a b = S a (b - 1) := by
    intro a b ha hb hbn
    have h1 := deltaN_comp_sigmaN_gt (n := n) ha hb hbn
    have h2 : deltaN (n + 1) b ≫ betaN (n + 2) (a + 1) = betaN (n + 1) (a + 1) := by
      rw [deltaN_comp_betaN, if_neg (by omega)]
    simp only [hSdef, hTdef, h1, h2]
  have hd1 : ∀ a, a ≤ n + 1 → T a a = A a := by
    intro a ha
    have h1 := deltaN_comp_sigmaN_eq (m := n + 1) ha (Or.inl rfl)
    have h2 : deltaN (n + 1) a ≫ betaN (n + 2) (a + 1) = betaN (n + 1) a := by
      rw [deltaN_comp_betaN, if_pos (by omega)]
      congr 1
    simp only [hAdef, hTdef, h1, h2]
  have hd2 : ∀ a, a ≤ n + 1 → T a (a + 1) = A (a + 1) := by
    intro a ha
    have h1 := deltaN_comp_sigmaN_eq (m := n + 1) ha (Or.inr rfl)
    have h2 : deltaN (n + 1) (a + 1) ≫ betaN (n + 2) (a + 1) = betaN (n + 1) (a + 1) := by
      rw [deltaN_comp_betaN, if_neg (by omega)]
    simp only [hAdef, hTdef, h1, h2]
  -- the two sums
  have hL : (d X n (prismK H n c)) s
      = ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 2), S a b := by
    have e0 : (d X n (prismK H n c)) s
        = ∑ j : Fin (n + 2), ∑ i : Fin (n + 1), c (prism H i (face j s)) := rfl
    rw [e0]
    have e1 : ∀ j : Fin (n + 2), (∑ i : Fin (n + 1), c (prism H i (face j s)))
        = ∑ a ∈ Finset.range (n + 1), S a (j : ℕ) := by
      intro j
      rw [← Fin.sum_univ_eq_sum_range (fun a => S a (j : ℕ)) (n + 1)]
      exact Finset.sum_congr rfl fun i _ => by rw [prism_face]
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => e1 j,
      Fin.sum_univ_eq_sum_range (fun b => ∑ a ∈ Finset.range (n + 1), S a b) (n + 2),
      Finset.sum_comm]
  have hR : (prismK H (n + 1) (d Y (n + 1) c)) s
      = ∑ a ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 3), T a b := by
    have e0 : (prismK H (n + 1) (d Y (n + 1) c)) s
        = ∑ i : Fin (n + 2), ∑ j : Fin (n + 3), c (face j (prism H i s)) := rfl
    rw [e0]
    have e1 : ∀ i : Fin (n + 2), (∑ j : Fin (n + 3), c (face j (prism H i s)))
        = ∑ b ∈ Finset.range (n + 3), T (i : ℕ) b := by
      intro i
      rw [← Fin.sum_univ_eq_sum_range (fun b => T (i : ℕ) b) (n + 3)]
      exact Finset.sum_congr rfl fun j _ => by rw [face_prism]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => e1 i,
      Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range (n + 3), T a b) (n + 2)]
  -- the two endpoints
  have hA0 : A 0 = (pullback g (n + 1) c) s := by
    simp only [hAdef]
    rw [prismPiece_betaN_zero, reindex_id]
    rfl
  have hAtop : A (n + 2) = (pullback f (n + 1) c) s := by
    simp only [hAdef]
    rw [prismPiece_betaN_top H (by omega), reindex_id]
    rfl
  show (d X n (prismK H n c)) s + (prismK H (n + 1) (d Y (n + 1) c)) s
    = (pullback g (n + 1) c) s + (pullback f (n + 1) c) s
  rw [hL, hR, ← hA0, ← hAtop]
  exact prism_double_sum n S T A hlt hgt hd1 hd2

/-- **The degree-zero form of the prism identity.**  In degree zero there is no `δ` to the left
of `K`, and the identity reduces to `K ∘ δ = g* + f*`.  This is the statement that the two
endpoints of the homotopy of a singular `0`-simplex are the two faces of a singular
`1`-simplex of `Y`. -/
theorem prismK_identity_zero (H : ContinuousMap.Homotopy f.hom g.hom) (c : Cochain Y 0) :
    prismK H 0 (d Y 0 c) = pullback g 0 c + pullback f 0 c := by
  funext s
  have e0 : (prismK H 0 (d Y 0 c)) s = ∑ j : Fin 2, c (face j (prism H 0 s)) := by
    show (∑ i : Fin 1, (d Y 0 c) (prism H i s)) = _
    rw [Fin.sum_univ_one]
    rfl
  have hface : ∀ j : Fin 2, face j (prism H 0 s)
      = prismPiece H (deltaN 0 (j : ℕ) ≫ sigmaN 0 0)
          (deltaN 0 (j : ℕ) ≫ betaN 1 1) s := by
    intro j
    rw [face_def, prism, delta_eq, reindex_prismPiece]
    rfl
  have hid : ∀ j : Fin 2, deltaN 0 (j : ℕ) ≫ sigmaN 0 0 = 𝟙 (SimplexCategory.mk 0) := by
    intro j
    have hj : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
    exact deltaN_comp_sigmaN_eq (m := 0) (Nat.le_refl 0) (by rcases hj with h | h <;> omega)
  have h0 : face (0 : Fin 2) (prism H 0 s) = simplexMap g 0 s := by
    rw [hface 0, hid 0, deltaN_comp_betaN, if_pos (by norm_num), prismPiece_betaN_zero,
      reindex_id]
  have h1 : face (1 : Fin 2) (prism H 0 s) = simplexMap f 0 s := by
    rw [hface 1, hid 1, deltaN_comp_betaN, if_neg (by norm_num),
      prismPiece_betaN_top H (by norm_num), reindex_id]
  rw [e0, Fin.sum_univ_two, h0, h1]
  rfl

end Mod2Cohomology
