import RequestProject.Spine.AlgebraicTopology.AffineSimplices

/-!
# Task 18, WP4/WP5 (algebraic core) : barycentric subdivision of linear chains

Barycentric subdivision is constructed here on the *linear* chains `LChain (Δs n) k` of the
geometric standard simplex, by the classical cone recursion:

* `SpineTask18.lcone b` — the cone on a linear chain with apex `b`;
* `SpineTask18.sd n k` — `sd(p) = b_p · sd(∂p)`, a chain endomorphism (`lbd_sd`);
* `SpineTask18.sdT n k` — the chain homotopy `∂T + T∂ = id + sd` (`sdT_homotopy`);
* naturality of both under affine reparametrisation (`lmap_sd`, `lmap_sdT`), which is what
  transports the construction to arbitrary singular chains.

Everything is over `ZMod 2`, so the classical signs disappear and `-` is `+`.
-/

noncomputable section

open CategoryTheory Opposite Simplicial NerveGeom

universe u v

namespace SpineTask18

/-! ## Characteristic two -/

/-- In a `ZMod 2`-module every element is its own negative. -/
theorem mod2_add_self {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) : x + x = 0 := by
  rw [← one_smul (ZMod 2) x, ← add_smul, show (1 + 1 : ZMod 2) = 0 from by decide, zero_smul]

/-- Induction principle for `ZMod 2`-valued `Finsupp`s: it suffices to treat `single p 1`. -/
@[elab_as_elim]
theorem lchain_induction {α : Type*} {P : (α →₀ ZMod 2) → Prop} (c : α →₀ ZMod 2)
    (h0 : P 0) (hadd : ∀ f g, P f → P g → P (f + g))
    (hsingle : ∀ p, P (Finsupp.single p (1 : ZMod 2))) : P c := by
  induction c using Finsupp.induction_linear with
  | zero => exact h0
  | add f g hf hg => exact hadd _ _ hf hg
  | single p a =>
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · simpa using h0
    · exact hsingle p

/-! ## The cone operator and the augmentation -/

/-- The cone with apex `b` on a linear chain. -/
def lcone {V : Type v} (b : V) (k : ℕ) : LChain V k →ₗ[ZMod 2] LChain V (k + 1) :=
  Finsupp.lmapDomain _ _ (fun p => Fin.cons b p)

@[simp] theorem lcone_single {V : Type v} (b : V) {k : ℕ} (p : Fin (k + 1) → V) (c : ZMod 2) :
    lcone b k (Finsupp.single p c) = Finsupp.single (Fin.cons b p) c :=
  Finsupp.mapDomain_single

/-- The augmentation of `0`-chains. -/
def laug (V : Type v) : LChain V 0 →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.linearCombination (ZMod 2) (fun _ => (1 : ZMod 2))

@[simp] theorem laug_single {V : Type v} (p : Fin 1 → V) (c : ZMod 2) :
    laug V (Finsupp.single p c) = c := by
  simp [laug]

theorem cons_comp_succAbove_zero {V : Type v} {k : ℕ} (b : V) (p : Fin (k + 1) → V) :
    (Fin.cons b p : Fin (k + 2) → V) ∘ Fin.succAbove 0 = p := by
  funext j
  simp [Fin.succAbove_zero]

theorem cons_comp_succAbove_succ {V : Type v} {k : ℕ} (b : V) (p : Fin (k + 2) → V)
    (j : Fin (k + 2)) :
    (Fin.cons b p : Fin (k + 3) → V) ∘ Fin.succAbove j.succ
      = Fin.cons b (p ∘ Fin.succAbove j) := by
  funext l
  induction l using Fin.cases with
  | zero => simp
  | succ l => simp [Fin.succ_succAbove_succ]

/-- `∂(b · c) = c + b · ∂c` in positive degrees. -/
theorem lbd_lcone {V : Type v} (b : V) {k : ℕ} (c : LChain V (k + 1)) :
    lbd V (k + 1) (lcone b (k + 1) c) = c + lcone b k (lbd V k c) := by
  induction c using lchain_induction with
  | h0 => simp
  | hadd f g hf hg =>
    simp only [map_add, hf, hg]
    abel
  | hsingle p =>
    rw [lcone_single, lbd_single, Fin.sum_univ_succ, cons_comp_succAbove_zero,
      lbd_single, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by
      rw [lcone_single, cons_comp_succAbove_succ]

/-- `∂(b · c) = c + ε(c)·b` in degree zero. -/
theorem lbd_lcone_zero {V : Type v} (b : V) (c : LChain V 0) :
    lbd V 0 (lcone b 0 c) = c + Finsupp.single (fun _ => b) (laug V c) := by
  induction c using lchain_induction with
  | h0 => simp
  | hadd f g hf hg =>
    simp only [map_add, hf, hg, Finsupp.single_add]
    abel
  | hsingle p =>
    rw [lcone_single, lbd_single, Fin.sum_univ_succ, cons_comp_succAbove_zero,
      Fin.sum_univ_succ, laug_single]
    have h1 : (Fin.cons b p : Fin 2 → V) ∘ Fin.succAbove (Fin.succ 0) = fun _ => b := by
      funext l
      have hl : l = 0 := Subsingleton.elim _ _
      subst hl
      rfl
    rw [h1]
    simp

/-- The augmentation kills boundaries. -/
theorem laug_lbd {V : Type v} (c : LChain V 1) : laug V (lbd V 0 c) = 0 := by
  induction c using lchain_induction with
  | h0 => simp
  | hadd f g hf hg => simp only [map_add, hf, hg, add_zero]
  | hsingle p =>
    rw [lbd_single, map_sum]
    simp only [laug_single, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    decide

/-- Naturality of the cone. -/
theorem lmap_lcone {V : Type v} {W : Type*} (h : V → W) (b : V) {k : ℕ} (c : LChain V k) :
    lmap h (k + 1) (lcone b k c) = lcone (h b) k (lmap h k c) := by
  induction c using lchain_induction with
  | h0 => simp
  | hadd f g hf hg => simp only [map_add, hf, hg]
  | hsingle p =>
    rw [lcone_single, lmap_single, lmap_single, lcone_single]
    congr 1
    funext l
    induction l using Fin.cases with
    | zero => simp
    | succ l => simp

/-! ## Barycentres -/

/-- The barycentre of the affine simplex spanned by `p`. -/
def bary {n k : ℕ} (p : Fin (k + 1) → Δs n) : Δs n := combo p stdSimplex.barycenter

/-- An affine reparametrisation carries barycentres to barycentres. -/
theorem bary_combo {m n k : ℕ} (q : Fin (m + 1) → Δs n) (p : Fin (k + 1) → Δs m) :
    bary (fun i => combo q (p i)) = combo q (bary p) := by
  rw [bary, bary, ← combo_comp]
  rfl

/-! ## Subdivision -/

/-- **WP4.**  Barycentric subdivision of linear chains of the standard `n`-simplex. -/
def sd (n : ℕ) : ∀ k, LChain (Δs n) k →ₗ[ZMod 2] LChain (Δs n) k
  | 0 => LinearMap.id
  | k + 1 => Finsupp.linearCombination (ZMod 2) (fun p : Fin (k + 2) → Δs n =>
      lcone (bary p) k (sd n k (lbd (Δs n) k (Finsupp.single p 1))))

@[simp] theorem sd_zero (n : ℕ) (c : LChain (Δs n) 0) : sd n 0 c = c := rfl

theorem sd_single {n k : ℕ} (p : Fin (k + 2) → Δs n) :
    sd n (k + 1) (Finsupp.single p 1)
      = lcone (bary p) k (sd n k (lbd (Δs n) k (Finsupp.single p 1))) := by
  show Finsupp.linearCombination _ _ _ = _
  rw [Finsupp.linearCombination_single, one_smul]

/-- **WP5.**  The subdivision homotopy of linear chains. -/
def sdT (n : ℕ) : ∀ k, LChain (Δs n) k →ₗ[ZMod 2] LChain (Δs n) (k + 1)
  | 0 => 0
  | k + 1 => Finsupp.linearCombination (ZMod 2) (fun p : Fin (k + 2) → Δs n =>
      lcone (bary p) (k + 1)
        (Finsupp.single p 1 + sdT n k (lbd (Δs n) k (Finsupp.single p 1))))

@[simp] theorem sdT_zero (n : ℕ) (c : LChain (Δs n) 0) : sdT n 0 c = 0 := rfl

theorem sdT_single {n k : ℕ} (p : Fin (k + 2) → Δs n) :
    sdT n (k + 1) (Finsupp.single p 1)
      = lcone (bary p) (k + 1)
        (Finsupp.single p 1 + sdT n k (lbd (Δs n) k (Finsupp.single p 1))) := by
  show Finsupp.linearCombination _ _ _ = _
  rw [Finsupp.linearCombination_single, one_smul]

/-- **WP4, chain map.**  Subdivision commutes with the boundary. -/
theorem lbd_sd (n : ℕ) : ∀ (k : ℕ) (c : LChain (Δs n) (k + 1)),
    lbd (Δs n) k (sd n (k + 1) c) = sd n k (lbd (Δs n) k c)
  | 0, c => by
    induction c using lchain_induction with
    | h0 => simp
    | hadd f g hf hg => simp only [map_add, hf, hg]
    | hsingle p =>
      rw [sd_single, sd_zero, lbd_lcone_zero, laug_lbd]
      simp
  | k + 1, c => by
    induction c using lchain_induction with
    | h0 => simp
    | hadd f g hf hg => simp only [map_add, hf, hg]
    | hsingle p =>
      rw [sd_single, lbd_lcone, lbd_sd n k, lbd_lbd, map_zero, map_zero, add_zero]

/-- **WP5, the homotopy identity.**  `∂T + T∂ = id + sd`. -/
theorem sdT_homotopy (n : ℕ) : ∀ (k : ℕ) (c : LChain (Δs n) (k + 1)),
    lbd (Δs n) (k + 1) (sdT n (k + 1) c) + sdT n k (lbd (Δs n) k c)
      = c + sd n (k + 1) c
  | 0, c => by
    induction c using lchain_induction with
    | h0 => simp
    | hadd f g hf hg =>
      simp only [map_add]
      rw [add_add_add_comm, hf, hg, add_add_add_comm]
    | hsingle p =>
      rw [sdT_single, sdT_zero, add_zero, lbd_lcone]
      simp [sd_single]
  | k + 1, c => by
    induction c using lchain_induction with
    | h0 => simp
    | hadd f g hf hg =>
      simp only [map_add]
      rw [add_add_add_comm, hf, hg, add_add_add_comm]
    | hsingle p =>
      have h := sdT_homotopy n k (lbd (Δs n) (k + 1) (Finsupp.single p (1 : ZMod 2)))
      rw [show lbd (Δs n) k (lbd (Δs n) (k + 1) (Finsupp.single p (1 : ZMod 2))) = 0 from
        lbd_lbd _, map_zero, add_zero] at h
      have hY : lbd (Δs n) (k + 1)
          (Finsupp.single p (1 : ZMod 2)
            + sdT n (k + 1) (lbd (Δs n) (k + 1) (Finsupp.single p (1 : ZMod 2))))
          = sd n (k + 1) (lbd (Δs n) (k + 1) (Finsupp.single p (1 : ZMod 2))) := by
        rw [map_add, h, ← add_assoc, mod2_add_self, zero_add]
      rw [sdT_single, lbd_lcone, hY, sd_single]
      rw [show ∀ A B C : LChain (Δs n) (k + 2), A + B + C + B = A + C + (B + B) from
        fun A B C => by abel, mod2_add_self, add_zero]

/-! ## Naturality under affine reparametrisation -/

theorem lmap_lbd_apply {V : Type v} {W : Type*} (h : V → W) (k : ℕ) (c : LChain V (k + 1)) :
    lmap h k (lbd V k c) = lbd W k (lmap h (k + 1) c) :=
  congrFun (congrArg DFunLike.coe (lmap_lbd h k)) c

/-- Subdivision is natural for affine reparametrisation. -/
theorem lmap_sd {m n : ℕ} (q : Fin (m + 1) → Δs n) : ∀ (k : ℕ) (c : LChain (Δs m) k),
    lmap (combo q) k (sd m k c) = sd n k (lmap (combo q) k c)
  | 0, c => by simp
  | k + 1, c => by
    induction c using lchain_induction with
    | h0 => simp
    | hadd f g hf hg => simp only [map_add, hf, hg]
    | hsingle p =>
      rw [sd_single, lmap_lcone, lmap_sd q k, lmap_single,
        show combo q (bary p) = bary ((combo q) ∘ p) from (bary_combo q p).symm,
        lmap_lbd_apply, lmap_single, sd_single]

/-- The subdivision homotopy is natural for affine reparametrisation. -/
theorem lmap_sdT {m n : ℕ} (q : Fin (m + 1) → Δs n) : ∀ (k : ℕ) (c : LChain (Δs m) k),
    lmap (combo q) (k + 1) (sdT m k c) = sdT n k (lmap (combo q) k c)
  | 0, c => by simp
  | k + 1, c => by
    induction c using lchain_induction with
    | h0 => simp
    | hadd f g hf hg => simp only [map_add, hf, hg]
    | hsingle p =>
      rw [sdT_single, lmap_lcone, lmap_single,
        show combo q (bary p) = bary ((combo q) ∘ p) from (bary_combo q p).symm, sdT_single]
      congr 1
      rw [map_add, lmap_single, lmap_sdT q k, lmap_lbd_apply, lmap_single]

end SpineTask18
