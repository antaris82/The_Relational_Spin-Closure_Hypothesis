import Mathlib

/-!
# Task 7, WP5 (a) : abstract presimplicial `ℤ₂` cochain complexes

This module is the *Spin-independent, cover-independent* half of WP5.  It defines what a
**presimplicial (semi-simplicial) set** is — a family of "simplices" in each degree together
with face operators satisfying the presimplicial identity — and builds its simplicial cochain
complex with constant coefficients in `ℤ/2`:

* `NerveZ2.Presimplicial` — objects `obj n` and faces `face t : obj (n+1) → obj n`, with the
  identity `dᵢ ∘ d_{j+1} = dⱼ ∘ d_{i}` for `i ≤ j` (written with `Fin.succ` / `Fin.castSucc`);
* `NerveZ2.Presimplicial.Cochain S n = S.obj n → ZMod 2` — genuine `ℤ₂`-valued functions on
  `n`-simplices;
* `coboundary` / `d` — the simplicial coboundary, together with the theorem
  `coboundary_eq_alternating` that it *is* the conventional alternating sum (the signs are
  invisible because `-1 = 1` in `ZMod 2`);
* `coboundary_coboundary` — the **theorem** `δ² = 0`, proved from the presimplicial identity
  alone;
* `cocycles`, `coboundaries`, `Cohomology` — the simplicial cohomology `Hⁿ_simp(S;ℤ₂)` as a
  genuine quotient module.

Nothing here mentions covers, Spin lifts, manifolds or singular simplices; the nerve of a
cover is fed in as one *instance* in `RequestProject.Spine.GoodCover.NerveIdentification`.

The construction is the standard one for a semi-simplicial object; no degeneracies are needed,
and none are assumed.
-/

namespace NerveZ2

open Finset

universe u

/-- A **presimplicial set** (semi-simplicial set): a family of simplex types together with
face operators obeying the presimplicial identity.

`face t x` deletes the `t`-th vertex of `x`.  The identity says that deleting two vertices in
either order gives the same result, in the usual indexed form: for `i ≤ j`,
`d_i ∘ d_{j+1} = d_j ∘ d_{i}`. -/
structure Presimplicial where
  /-- The type of `n`-simplices. -/
  obj : ℕ → Type u
  /-- The `t`-th face operator. -/
  face : {n : ℕ} → Fin (n + 2) → obj (n + 1) → obj n
  /-- The presimplicial identity. -/
  face_comm : ∀ {n : ℕ} (i j : Fin (n + 2)), i ≤ j → ∀ x : obj (n + 2),
    face i (face j.succ x) = face j (face i.castSucc x)

namespace Presimplicial

variable (S : Presimplicial.{u})

/-- **Degree-`n` simplicial cochains with constant coefficients in `ℤ/2`**: a genuine function
type, with the `Pi`-derived module structure. -/
abbrev Cochain (n : ℕ) : Type u := S.obj n → ZMod 2

example (n : ℕ) : AddCommGroup (S.Cochain n) := inferInstance
example (n : ℕ) : Module (ZMod 2) (S.Cochain n) := inferInstance

/-- The **simplicial coboundary**, the (unsigned, because `-1 = 1` in `ZMod 2`) sum of the
values of `c` on all faces. -/
def coboundary (n : ℕ) (c : S.Cochain n) : S.Cochain (n + 1) :=
  fun σ => ∑ t : Fin (n + 2), c (S.face t σ)

@[simp] theorem coboundary_apply (n : ℕ) (c : S.Cochain n) (σ : S.obj (n + 1)) :
    S.coboundary n c σ = ∑ t : Fin (n + 2), c (S.face t σ) := rfl

/-- **The conventional alternating formula.**  The implementation agrees with
`∑ (-1)ᵗ c(d_t σ)`; the signs collapse because `-1 = 1` in `ZMod 2`. -/
theorem coboundary_eq_alternating (n : ℕ) (c : S.Cochain n) (σ : S.obj (n + 1)) :
    S.coboundary n c σ = ∑ t : Fin (n + 2), (-1 : ZMod 2) ^ (t : ℕ) * c (S.face t σ) := by
  refine Finset.sum_congr rfl fun t _ => ?_
  have h : (-1 : ZMod 2) = 1 := by decide
  rw [h, one_pow, one_mul]

theorem coboundary_add (n : ℕ) (c c' : S.Cochain n) :
    S.coboundary n (c + c') = S.coboundary n c + S.coboundary n c' := by
  funext σ
  simp [coboundary, Finset.sum_add_distrib]

theorem coboundary_smul (n : ℕ) (r : ZMod 2) (c : S.Cochain n) :
    S.coboundary n (r • c) = r • S.coboundary n c := by
  funext σ
  simp [coboundary, Finset.mul_sum]

/-- The simplicial coboundary as a `ZMod 2`-linear map. -/
def d (n : ℕ) : S.Cochain n →ₗ[ZMod 2] S.Cochain (n + 1) where
  toFun := S.coboundary n
  map_add' := S.coboundary_add n
  map_smul' := S.coboundary_smul n

@[simp] theorem d_apply (n : ℕ) (c : S.Cochain n) : S.d n c = S.coboundary n c := rfl

/-- **`δ² = 0` for any presimplicial set.**  The double sum over `Fin (n+3) × Fin (n+2)` is
split along `t.castSucc < s`; the presimplicial identity matches the two halves term by term
via `(s,t) ↦ (t.castSucc, s.pred)`, and in characteristic two the two equal halves cancel. -/
theorem coboundary_coboundary (n : ℕ) (c : S.Cochain n) :
    S.coboundary (n + 1) (S.coboundary n c) = 0 := by
  classical
  funext σ
  show (∑ s : Fin (n + 3), ∑ t : Fin (n + 2), c (S.face t (S.face s σ))) = 0
  rw [← Fintype.sum_prod_type (f := fun p : Fin (n + 3) × Fin (n + 2) =>
    c (S.face p.2 (S.face p.1 σ)))]
  set T : Fin (n + 3) × Fin (n + 2) → ZMod 2 := fun p => c (S.face p.2 (S.face p.1 σ)) with hT
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
      have hcomm := S.face_comm (i := a.2) (j := a.1.pred hne) hle σ
      rw [Fin.succ_pred] at hcomm
      simp only [hT]
      exact congrArg c hcomm
  rw [key]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  exact h2 _

/-- `δ² = 0` in linear-map form. -/
theorem d_comp_d (n : ℕ) : (S.d (n + 1)).comp (S.d n) = 0 := by
  ext c
  exact congrFun (S.coboundary_coboundary n c) _

@[simp] theorem d_d (n : ℕ) (c : S.Cochain n) : S.d (n + 1) (S.d n c) = 0 :=
  S.coboundary_coboundary n c

/-! ## Simplicial cohomology of a presimplicial set -/

/-- `Zⁿ_simp = ker δⁿ`. -/
def cocycles (n : ℕ) : Submodule (ZMod 2) (S.Cochain n) := LinearMap.ker (S.d n)

/-- `Bⁿ_simp = im δⁿ⁻¹`, with `B⁰ = 0`. -/
def coboundaries : (n : ℕ) → Submodule (ZMod 2) (S.Cochain n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (S.d n)

theorem coboundaries_le_cocycles (n : ℕ) : S.coboundaries n ≤ S.cocycles n := by
  cases n with
  | zero => simp [coboundaries]
  | succ n =>
      rintro c ⟨b, rfl⟩
      exact S.d_d n b

/-- `Bⁿ` seen inside `Zⁿ`. -/
def coboundariesIn (n : ℕ) : Submodule (ZMod 2) (S.cocycles n) :=
  Submodule.comap (S.cocycles n).subtype (S.coboundaries n)

/-- **Simplicial cohomology of a presimplicial set**, `Hⁿ_simp(S;ℤ₂) = Zⁿ/Bⁿ`, a genuine
quotient module. -/
def Cohomology (n : ℕ) : Type u := (S.cocycles n) ⧸ (S.coboundariesIn n)

instance (n : ℕ) : AddCommGroup (S.Cohomology n) :=
  inferInstanceAs (AddCommGroup ((S.cocycles n) ⧸ (S.coboundariesIn n)))

instance (n : ℕ) : Module (ZMod 2) (S.Cohomology n) :=
  inferInstanceAs (Module (ZMod 2) ((S.cocycles n) ⧸ (S.coboundariesIn n)))

/-- The class of a simplicial cocycle. -/
def cohomologyClass {n : ℕ} (z : S.cocycles n) : S.Cohomology n :=
  Submodule.Quotient.mk (p := S.coboundariesIn n) z

end Presimplicial

end NerveZ2
