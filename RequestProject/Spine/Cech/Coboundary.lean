import RequestProject.Spine.Cech.Cochain

/-!
# Task 6, WP3 : the Čech coboundary and the theorem `δ² = 0`

The **conventional** Čech coboundary of an `n`-cochain `c` on a cover `U` is the alternating
sum over the faces of an `(n+1)`-simplex of the nerve,

`(δ c)(i₀ … i_{n+1}) = ∑_{t=0}^{n+1} (-1)^t · c(i₀ … î_t … i_{n+1})`,

where `î_t` means that the index in position `t` is deleted (`Fin.succAbove t` on positions).

**Relation to the implementation.**  The coefficients here are `ZMod 2`, in which `-1 = 1`, so
every sign `(-1)^t` equals `1` and the alternating sum *is* the plain sum.  The implementation
`CechZ2.coboundary` uses the plain sum, and `CechZ2.coboundary_eq_alternating` proves that it
agrees with the conventional alternating formula, so the collapse of signs is a theorem and not
a silent change of convention.

**`δ² = 0` is proved, not assumed, and it is proved without any Spin input.**  The mechanism is
the simplicial identity `CechZ2.succAbove_comm` for `Fin.succAbove` (deleting two positions in
either order gives the same subtuple), which pairs the index set `Fin (n+3) × Fin (n+2)` of the
double sum into two halves carrying identical terms; over `ZMod 2` the two halves cancel because
`x + x = 0`.  In the integral case the same pairing is used and the two paired signs are
opposite; in characteristic two both mechanisms coincide.

## Contents

* `CechZ2.succAbove_comm` — the `Fin` face identity `δᵢ ∘ δⱼ`-style commutation;
* `CechZ2.coboundary`, `CechZ2.d` — the coboundary as a function and as a `ZMod 2`-linear map;
* `CechZ2.coboundary_eq_alternating` — agreement with the conventional alternating formula;
* `CechZ2.coboundary_coboundary`, `CechZ2.d_comp_d`, `CechZ2.d_d` — the theorem `δ² = 0`.
-/

namespace CechZ2

open Finset

universe w t

variable {X : Type w} {ι : Type t} {U : ι → Set X}

/-! ## The face identity in `Fin` -/

/-- The simplicial identity for `Fin.succAbove`: for `i ≤ j`, inserting first at `i` and then
at `j.succ` is the same as inserting first at `j` and then at `i.castSucc`.  Dually (which is
how it is used below) deleting two positions of a tuple in either order gives the same
subtuple.  This is the only combinatorial input to `δ² = 0`. -/
theorem succAbove_comm {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) (x : Fin n) :
    (j.succ).succAbove (i.succAbove x) = (i.castSucc).succAbove (j.succAbove x) := by
  apply Fin.ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.val_castSucc, Fin.val_succ] at *
  split_ifs <;> simp_all <;> omega

/-! ## The coboundary -/

/-- The **Čech coboundary** `δ : Čⁿ(U;ℤ₂) → Čⁿ⁺¹(U;ℤ₂)`, the (unsigned, because `-1 = 1` in
`ZMod 2`) sum of the values of `c` on all faces. -/
def coboundary (n : ℕ) (c : Cochain U n) : Cochain U (n + 1) :=
  fun σ => ∑ t : Fin (n + 2), c (face t σ)

@[simp] theorem coboundary_apply (n : ℕ) (c : Cochain U n) (σ : Nerve U (n + 1)) :
    coboundary n c σ = ∑ t : Fin (n + 2), c (face t σ) := rfl

/-- **The conventional alternating Čech formula.**  The implementation agrees with the
alternating sum `∑ (-1)^t c(… î_t …)`; the signs are invisible because `-1 = 1` in `ZMod 2`. -/
theorem coboundary_eq_alternating (n : ℕ) (c : Cochain U n) (σ : Nerve U (n + 1)) :
    coboundary n c σ = ∑ t : Fin (n + 2), (-1 : ZMod 2) ^ (t : ℕ) * c (face t σ) := by
  refine Finset.sum_congr rfl fun t _ => ?_
  have h : (-1 : ZMod 2) = 1 := by decide
  rw [h, one_pow, one_mul]

theorem coboundary_add (n : ℕ) (c c' : Cochain U n) :
    coboundary n (c + c') = coboundary n c + coboundary n c' := by
  funext σ
  simp [coboundary, Finset.sum_add_distrib]

theorem coboundary_smul (n : ℕ) (r : ZMod 2) (c : Cochain U n) :
    coboundary n (r • c) = r • coboundary n c := by
  funext σ
  simp [coboundary, Finset.mul_sum]

/-- The Čech coboundary as a `ZMod 2`-linear map `δⁿ : Čⁿ(U;ℤ₂) →ₗ Čⁿ⁺¹(U;ℤ₂)`. -/
def d (U : ι → Set X) (n : ℕ) : Cochain U n →ₗ[ZMod 2] Cochain U (n + 1) where
  toFun := coboundary n
  map_add' := coboundary_add n
  map_smul' := coboundary_smul n

@[simp] theorem d_apply (n : ℕ) (c : Cochain U n) : d U n c = coboundary n c := rfl

@[simp] theorem d_apply_nerve (n : ℕ) (c : Cochain U n) (σ : Nerve U (n + 1)) :
    d U n c σ = ∑ t : Fin (n + 2), c (face t σ) := rfl

/-! ## `δ² = 0` -/

/-- **The Čech cochain-complex law `δ ∘ δ = 0`.**

The double sum runs over `Fin (n+3) × Fin (n+2)`; its `(s,t)`-term is the value of `c` on the
subtuple obtained by deleting position `s` and then position `t`.  Splitting the index set along
`t.castSucc < s` and using `succAbove_comm` to match `(s,t) ↦ (t.castSucc, s.pred)` gives two
halves with identical terms; over `ZMod 2` their sum vanishes.

No Spin-theoretic input is used, and nothing is postulated. -/
theorem coboundary_coboundary (n : ℕ) (c : Cochain U n) :
    coboundary (n + 1) (coboundary n c) = 0 := by
  classical
  funext σ
  show (∑ s : Fin (n + 3), ∑ t : Fin (n + 2), c (face t (face s σ))) = 0
  rw [← Fintype.sum_prod_type (f := fun p : Fin (n + 3) × Fin (n + 2) =>
    c (face p.2 (face p.1 σ)))]
  set T : Fin (n + 3) × Fin (n + 2) → ZMod 2 := fun p => c (face p.2 (face p.1 σ)) with hT
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : Fin (n + 3) × Fin (n + 2) => p.2.castSucc < p.1) T]
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
      have hne : a.1 ≠ 0 := by
        intro h0; rw [h0] at ha; exact absurd ha (by simp [Fin.lt_def])
      have hle : a.2 ≤ a.1.pred hne := by
        simp only [Fin.le_def, Fin.val_pred]
        simp [Fin.lt_def] at ha
        omega
      have hcomm := succAbove_comm (i := a.2) (j := a.1.pred hne) hle
      rw [Fin.succ_pred] at hcomm
      simp only [hT]
      congr 1
      apply Nerve.ext
      funext u
      exact congrArg σ.idx (hcomm u)
  rw [key]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  exact h2 _

/-- `δ² = 0` in linear-map form: the composite `Čⁿ →ₗ Čⁿ⁺¹ →ₗ Čⁿ⁺²` is the zero map. -/
theorem d_comp_d (n : ℕ) : (d U (n + 1)).comp (d U n) = 0 := by
  ext c
  exact congrFun (coboundary_coboundary n c) _

@[simp] theorem d_d (n : ℕ) (c : Cochain U n) : d U (n + 1) (d U n c) = 0 :=
  coboundary_coboundary n c

end CechZ2
