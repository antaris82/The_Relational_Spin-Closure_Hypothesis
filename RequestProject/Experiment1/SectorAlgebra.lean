import Mathlib

/-!
# Two complementary idempotent sectors: an assumption audit

This file rebuilds the split-complex `1+1` Lorentz construction from a *weaker* primitive
assumption than the one used in `RequestProject.Experiment1.SplitComplexLorentz`.

**Primitive data** (and nothing else): a two–dimensional commutative associative unital
`ℝ`-algebra `A` together with two nonzero complementary orthogonal idempotents `p q : A`:

`p * p = p`, `q * q = q`, `p * q = 0`, `p + q = 1`, `p ≠ 0`, `q ≠ 0`, `finrank ℝ A = 2`.

Everything else — the isomorphism `A ≃ₐ[ℝ] ℝ × ℝ`, the split generator `ε = p - q` with
`ε² = 1`, the sector-exchanging involution `σ`, the multiplicative norm `N`, the indefinite
quadratic form, the norm-one group, the exponential parametrisation of its positive branch,
the reciprocal exponential action and the standard `1+1` Lorentz formulas — is *derived*.

No physical interpretation is asserted anywhere in this file.
-/

noncomputable section

open Real

namespace Sector

/-- **Primitive assumptions.** A two-dimensional commutative unital real algebra `A`
together with two nonzero complementary orthogonal idempotents `p`, `q`.

All the structure used later in this file is derived from these fields; nothing about a
split-complex multiplication table, a conjugation, a norm or a boost is assumed. -/
structure SectorAlgebra (A : Type*) [CommRing A] [Algebra ℝ A] where
  /-- the first idempotent -/
  p : A
  /-- the second idempotent -/
  q : A
  /-- `p` is idempotent -/
  sq_p : p * p = p
  /-- `q` is idempotent -/
  sq_q : q * q = q
  /-- `p` and `q` are orthogonal -/
  orth : p * q = 0
  /-- `p` and `q` are complementary -/
  sum_eq_one : p + q = 1
  /-- the first sector is nonzero -/
  p_ne_zero : p ≠ 0
  /-- the second sector is nonzero -/
  q_ne_zero : q ≠ 0
  /-- `A` is two-dimensional over `ℝ` -/
  finrank_eq : Module.finrank ℝ A = 2

namespace SectorAlgebra

variable {A : Type*} [CommRing A] [Algebra ℝ A] (S : SectorAlgebra A)

lemma orth' : S.q * S.p = 0 := by rw [mul_comm]; exact S.orth

lemma nontrivial' (S : SectorAlgebra A) : Nontrivial A := ⟨S.p, 0, S.p_ne_zero⟩

/-! ## 2. The sector decomposition -/

/-- `p` and `q` are linearly independent over `ℝ`. -/
theorem linearIndependent_pair : LinearIndependent ℝ ![S.p, S.q] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  constructor
  · have h1 : (s • S.p + t • S.q) * S.p = 0 := by rw [h, zero_mul]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, S.sq_p, S.orth'] at h1
    simp only [smul_zero, add_zero] at h1
    by_contra hs
    exact S.p_ne_zero (by
      have := congrArg (fun z => s⁻¹ • z) h1
      simpa [smul_smul, inv_mul_cancel₀ hs] using this)
  · have h1 : (s • S.p + t • S.q) * S.q = 0 := by rw [h, zero_mul]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, S.sq_q, S.orth] at h1
    simp only [smul_zero, zero_add] at h1
    by_contra ht
    exact S.q_ne_zero (by
      have := congrArg (fun z => t⁻¹ • z) h1
      simpa [smul_smul, inv_mul_cancel₀ ht] using this)

/-- `p, q` is a basis of `A` (using `dim A = 2`). -/
def basis : Module.Basis (Fin 2) ℝ A :=
  basisOfLinearIndependentOfCardEqFinrank S.linearIndependent_pair (by simp [S.finrank_eq])

lemma coe_basis : ⇑S.basis = ![S.p, S.q] :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

/-- The `p`-coordinate of an element. -/
def coordP (x : A) : ℝ := S.basis.repr x 0

/-- The `q`-coordinate of an element. -/
def coordQ (x : A) : ℝ := S.basis.repr x 1

/-- **Existence of coordinates**: every `x ∈ A` is `a • p + b • q`. -/
theorem decomp (x : A) : x = S.coordP x • S.p + S.coordQ x • S.q := by
  have h := S.basis.sum_repr x
  rw [Fin.sum_univ_two, S.coe_basis] at h
  simpa [coordP, coordQ] using h.symm

/-- **Uniqueness of coordinates.** -/
theorem coords_unique {a b a' b' : ℝ} (h : a • S.p + b • S.q = a' • S.p + b' • S.q) :
    a = a' ∧ b = b' := by
  have h0 : (a - a') • S.p + (b - b') • S.q = 0 := by
    rw [sub_smul, sub_smul]; rw [sub_add_sub_comm, h, sub_self]
  have := (LinearIndependent.pair_iff.mp S.linearIndependent_pair) _ _ h0
  exact ⟨by linarith [sub_eq_zero.mp (by linarith [this.1] : a - a' = 0)],
    by linarith [sub_eq_zero.mp (by linarith [this.2] : b - b' = 0)]⟩

@[simp] theorem coordP_smul_add_smul (a b : ℝ) : S.coordP (a • S.p + b • S.q) = a :=
  (S.coords_unique (S.decomp (a • S.p + b • S.q)).symm).1

@[simp] theorem coordQ_smul_add_smul (a b : ℝ) : S.coordQ (a • S.p + b • S.q) = b :=
  (S.coords_unique (S.decomp (a • S.p + b • S.q)).symm).2

/-- **Existence and uniqueness of the sector coordinates.** -/
theorem existsUnique_coords (x : A) : ∃! ab : ℝ × ℝ, x = ab.1 • S.p + ab.2 • S.q := by
  refine ⟨(S.coordP x, S.coordQ x), S.decomp x, ?_⟩
  rintro ⟨a, b⟩ h
  have := S.coords_unique (h.symm.trans (S.decomp x))
  exact Prod.ext this.1 this.2

/-- **The multiplication rule in sector coordinates.** -/
theorem mul_decomp (a b c d : ℝ) :
    (a • S.p + b • S.q) * (c • S.p + d • S.q) = (a * c) • S.p + (b * d) • S.q := by
  simp only [add_mul, mul_add, smul_mul_smul_comm, S.sq_p, S.sq_q, S.orth, S.orth', smul_zero,
    add_zero, zero_add]

theorem p_eq : S.p = (1 : ℝ) • S.p + (0 : ℝ) • S.q := by simp

theorem q_eq : S.q = (0 : ℝ) • S.p + (1 : ℝ) • S.q := by simp

@[simp] theorem coordP_p : S.coordP S.p = 1 := by
  conv_lhs => rw [S.p_eq]
  exact S.coordP_smul_add_smul 1 0

@[simp] theorem coordQ_p : S.coordQ S.p = 0 := by
  conv_lhs => rw [S.p_eq]
  exact S.coordQ_smul_add_smul 1 0

@[simp] theorem coordP_q : S.coordP S.q = 0 := by
  conv_lhs => rw [S.q_eq]
  exact S.coordP_smul_add_smul 0 1

@[simp] theorem coordQ_q : S.coordQ S.q = 1 := by
  conv_lhs => rw [S.q_eq]
  exact S.coordQ_smul_add_smul 0 1

@[simp] theorem coordP_one : S.coordP 1 = 1 := by
  conv_lhs => rw [← S.sum_eq_one]
  simpa using S.coordP_smul_add_smul 1 1

@[simp] theorem coordQ_one : S.coordQ 1 = 1 := by
  conv_lhs => rw [← S.sum_eq_one]
  simpa using S.coordQ_smul_add_smul 1 1

theorem one_eq : (1 : A) = (1 : ℝ) • S.p + (1 : ℝ) • S.q := by
  simp [S.sum_eq_one]

@[simp] theorem coordP_add (x y : A) : S.coordP (x + y) = S.coordP x + S.coordP y := by
  simp [coordP]

@[simp] theorem coordQ_add (x y : A) : S.coordQ (x + y) = S.coordQ x + S.coordQ y := by
  simp [coordQ]

@[simp] theorem coordP_smul (r : ℝ) (x : A) : S.coordP (r • x) = r * S.coordP x := by
  simp [coordP]

@[simp] theorem coordQ_smul (r : ℝ) (x : A) : S.coordQ (r • x) = r * S.coordQ x := by
  simp [coordQ]

@[simp] theorem coordP_sub (x y : A) : S.coordP (x - y) = S.coordP x - S.coordP y := by
  simp [coordP]

@[simp] theorem coordQ_sub (x y : A) : S.coordQ (x - y) = S.coordQ x - S.coordQ y := by
  simp [coordQ]

@[simp] theorem coordP_neg (x : A) : S.coordP (-x) = -S.coordP x := by simp [coordP]

@[simp] theorem coordQ_neg (x : A) : S.coordQ (-x) = -S.coordQ x := by simp [coordQ]

@[simp] theorem coordP_zero : S.coordP 0 = 0 := by simp [coordP]

@[simp] theorem coordQ_zero : S.coordQ 0 = 0 := by simp [coordQ]

@[simp] theorem coordP_mul (x y : A) : S.coordP (x * y) = S.coordP x * S.coordP y := by
  conv_lhs => rw [S.decomp x, S.decomp y, S.mul_decomp]
  simp

@[simp] theorem coordQ_mul (x y : A) : S.coordQ (x * y) = S.coordQ x * S.coordQ y := by
  conv_lhs => rw [S.decomp x, S.decomp y, S.mul_decomp]
  simp

theorem ext_coords {x y : A} (hp : S.coordP x = S.coordP y) (hq : S.coordQ x = S.coordQ y) :
    x = y := by
  rw [S.decomp x, S.decomp y, hp, hq]

/-- The coordinate map, as a morphism of unital `ℝ`-algebras `A → ℝ × ℝ`. -/
def toProd : A →ₐ[ℝ] ℝ × ℝ where
  toFun x := (S.coordP x, S.coordQ x)
  map_one' := by simp
  map_mul' x y := by simp
  map_zero' := by simp
  map_add' x y := by simp
  commutes' r := by
    have : (algebraMap ℝ A) r = r • (1 : A) := Algebra.algebraMap_eq_smul_one r
    simp [this, Prod.ext_iff, Algebra.algebraMap_eq_smul_one]

@[simp] lemma toProd_apply (x : A) : S.toProd x = (S.coordP x, S.coordQ x) := rfl

theorem toProd_bijective : Function.Bijective S.toProd := by
  constructor
  · intro x y h
    simp only [toProd_apply, Prod.mk.injEq] at h
    exact S.ext_coords h.1 h.2
  · rintro ⟨a, b⟩
    exact ⟨a • S.p + b • S.q, by simp⟩

/-- **Theorem (not a definition): `A ≅ ℝ × ℝ` as a unital `ℝ`-algebra**, with the
coordinatewise multiplication on `ℝ × ℝ`. -/
def equivProd : A ≃ₐ[ℝ] ℝ × ℝ := AlgEquiv.ofBijective S.toProd S.toProd_bijective

@[simp] lemma equivProd_apply (x : A) : S.equivProd x = (S.coordP x, S.coordQ x) := rfl

theorem exists_algEquiv_prod (S : SectorAlgebra A) : Nonempty (A ≃ₐ[ℝ] ℝ × ℝ) :=
  ⟨S.equivProd⟩

/-- Scalars are detected by the coordinates: `r • 1 = s • 1` forces `r = s`. -/
theorem smul_one_injective (S : SectorAlgebra A) {r s : ℝ}
    (h : r • (1 : A) = s • (1 : A)) : r = s := by
  have := congrArg S.coordP h
  simpa using this

/-! ## 3. The split generator, derived -/

/-- The split generator, **defined** from the sector decomposition. -/
def epsilon : A := S.p - S.q

/-- **`ε² = 1` is derived**, not postulated. -/
theorem epsilon_sq : S.epsilon * S.epsilon = 1 := by
  have h : S.epsilon * S.epsilon = S.p * S.p - S.p * S.q - S.q * S.p + S.q * S.q := by
    simp only [epsilon, mul_sub, sub_mul]; ring
  rw [h, S.sq_p, S.sq_q, S.orth, S.orth']
  simpa using S.sum_eq_one

@[simp] theorem coordP_epsilon : S.coordP S.epsilon = 1 := by simp [epsilon]

@[simp] theorem coordQ_epsilon : S.coordQ S.epsilon = -1 := by simp [epsilon]

/-- The idempotents are recovered from `ε` as `(1 ± ε)/2`. -/
theorem p_eq_half_one_add_epsilon : S.p = (2 : ℝ)⁻¹ • (1 + S.epsilon) := by
  rw [epsilon, ← S.sum_eq_one]
  rw [show S.p + S.q + (S.p - S.q) = (2 : ℝ) • S.p by rw [two_smul]; ring]
  rw [smul_smul]
  norm_num

theorem q_eq_half_one_sub_epsilon : S.q = (2 : ℝ)⁻¹ • (1 - S.epsilon) := by
  rw [epsilon, ← S.sum_eq_one]
  rw [show S.p + S.q - (S.p - S.q) = (2 : ℝ) • S.q by rw [two_smul]; ring]
  rw [smul_smul]
  norm_num

/-- Since both sectors are nonzero, `ε ≠ 1`. -/
theorem epsilon_ne_one : S.epsilon ≠ 1 := by
  intro h
  apply S.q_ne_zero
  have h2 : (2 : ℝ) • S.q = 0 := by
    have : S.p - S.q = S.p + S.q := by rw [← S.sum_eq_one] at h; exact h ▸ rfl
    rw [two_smul]; linear_combination (norm := module) -this
  have := congrArg (fun z => (2 : ℝ)⁻¹ • z) h2
  simpa [smul_smul] using this

/-- Since both sectors are nonzero, `ε ≠ -1`. -/
theorem epsilon_ne_neg_one : S.epsilon ≠ -1 := by
  intro h
  apply S.p_ne_zero
  have h2 : (2 : ℝ) • S.p = 0 := by
    have : S.p - S.q = -(S.p + S.q) := by rw [← S.sum_eq_one] at h; exact h ▸ rfl
    rw [two_smul]; linear_combination (norm := module) this
  have := congrArg (fun z => (2 : ℝ)⁻¹ • z) h2
  simpa [smul_smul] using this

/-- Coordinates in the `1, ε` frame: `t • 1 + x • ε = (t + x) • p + (t - x) • q`. -/
theorem smul_one_add_smul_epsilon (t x : ℝ) :
    t • (1 : A) + x • S.epsilon = (t + x) • S.p + (t - x) • S.q := by
  rw [← S.sum_eq_one, epsilon]
  module

/-! ## 4. The sector-exchanging involution, derived -/

/-- The sector-exchanging involution `σ (a p + b q) = b p + a q`, defined through the
unique sector decomposition. -/
def sigmaHom : A →ₐ[ℝ] A where
  toFun x := S.coordQ x • S.p + S.coordP x • S.q
  map_one' := by simp [S.sum_eq_one]
  map_mul' x y := by rw [S.mul_decomp]; simp
  map_zero' := by simp
  map_add' x y := by simp; module
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp [← S.sum_eq_one, smul_add]

@[simp] lemma sigmaHom_apply (x : A) : S.sigmaHom x = S.coordQ x • S.p + S.coordP x • S.q := rfl

@[simp] theorem sigmaHom_smul_add_smul (a b : ℝ) :
    S.sigmaHom (a • S.p + b • S.q) = b • S.p + a • S.q := by simp

@[simp] theorem coordP_sigmaHom (x : A) : S.coordP (S.sigmaHom x) = S.coordQ x := by simp

@[simp] theorem coordQ_sigmaHom (x : A) : S.coordQ (S.sigmaHom x) = S.coordP x := by simp

/-- `σ` is involutive. -/
theorem sigmaHom_sigmaHom (x : A) : S.sigmaHom (S.sigmaHom x) = x := by
  refine S.ext_coords ?_ ?_ <;> simp

/-- `σ` exchanges the two sectors. -/
@[simp] theorem sigmaHom_p : S.sigmaHom S.p = S.q := by simp

@[simp] theorem sigmaHom_q : S.sigmaHom S.q = S.p := by simp

/-- Consequently `σ ε = -ε`. -/
theorem sigmaHom_epsilon : S.sigmaHom S.epsilon = -S.epsilon := by
  rw [epsilon, map_sub, S.sigmaHom_p, S.sigmaHom_q]
  ring

/-- `σ` as an algebra automorphism of `A`. -/
def sigmaEquiv : A ≃ₐ[ℝ] A :=
  AlgEquiv.ofAlgHom S.sigmaHom S.sigmaHom (by ext x; exact S.sigmaHom_sigmaHom x)
    (by ext x; exact S.sigmaHom_sigmaHom x)

@[simp] lemma sigmaEquiv_apply (x : A) : S.sigmaEquiv x = S.sigmaHom x := rfl

/-- **Uniqueness.** Relative to the chosen complementary pair `(p, q)`, `σ` is the *only*
unital `ℝ`-algebra endomorphism of `A` exchanging `p` and `q`; this justifies speaking of
*the* sector-exchanging involution. -/
theorem sigmaHom_unique (f : A →ₐ[ℝ] A) (hp : f S.p = S.q) (hq : f S.q = S.p) :
    f = S.sigmaHom := by
  ext x
  conv_lhs => rw [S.decomp x]
  rw [map_add, map_smul, map_smul, hp, hq]
  simp [add_comm]

/-! ## 5. The multiplicative norm, derived from the involution -/

/-- The norm, read off from `x σ(x) = N(x) • 1`. -/
def N (x : A) : ℝ := S.coordP x * S.coordQ x

/-- `x σ(x)` is the scalar `N x`. -/
theorem mul_sigmaHom (x : A) : x * S.sigmaHom x = S.N x • (1 : A) := by
  conv_lhs => rw [S.decomp x]
  rw [S.sigmaHom_smul_add_smul, S.mul_decomp, ← S.sum_eq_one, N]
  rw [smul_add]
  rw [mul_comm (S.coordQ x) (S.coordP x)]

/-- `N x` is the *unique* scalar with `x σ(x) = r • 1`. -/
theorem N_unique {x : A} {r : ℝ} (h : x * S.sigmaHom x = r • (1 : A)) : r = S.N x :=
  S.smul_one_injective (h.symm.trans (S.mul_sigmaHom x))

@[simp] theorem N_smul_add_smul (a b : ℝ) : S.N (a • S.p + b • S.q) = a * b := by simp [N]

@[simp] theorem N_one : S.N (1 : A) = 1 := by simp [N]

/-- **Multiplicativity of the norm**, derived (not assumed). -/
theorem N_mul (x y : A) : S.N (x * y) = S.N x * S.N y := by
  simp only [N, S.coordP_mul, S.coordQ_mul]; ring

@[simp] theorem N_p : S.N S.p = 0 := by simp [N]

@[simp] theorem N_epsilon : S.N S.epsilon = -1 := by simp [N]

/-! ## 6. The indefinite quadratic form -/

/-- With `a = t + x`, `b = t - x` the norm is the indefinite form `t² - x²`. -/
theorem N_lightcone (t x : ℝ) : S.N ((t + x) • S.p + (t - x) • S.q) = t ^ 2 - x ^ 2 := by
  simp [N]; ring

/-- The same in the `1, ε` frame: `N (t • 1 + x • ε) = t² - x²`.  Since `1, ε` is a basis
(`basis_one_epsilon` below), this exhibits the diagonal form `diag(1, -1)`, i.e. signature
`(1,1)`. -/
theorem N_one_epsilon_frame (t x : ℝ) : S.N (t • (1 : A) + x • S.epsilon) = t ^ 2 - x ^ 2 := by
  rw [S.smul_one_add_smul_epsilon, S.N_lightcone]

/-- `c` is introduced **here**, purely as a coordinate scale; it is not derived. -/
theorem N_lightcone_c (c t x : ℝ) :
    S.N ((c * t + x) • S.p + (c * t - x) • S.q) = c ^ 2 * t ^ 2 - x ^ 2 := by
  simp [N]; ring

/-- `1` and `ε` form a basis of `A`, in which `N` is `diag(1, -1)`. -/
theorem linearIndependent_one_epsilon : LinearIndependent ℝ ![(1 : A), S.epsilon] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  rw [S.smul_one_add_smul_epsilon] at h
  have h0 : (s + t) • S.p + (s - t) • S.q = (0 : ℝ) • S.p + (0 : ℝ) • S.q := by
    simpa using h
  have := S.coords_unique h0
  constructor <;> linarith [this.1, this.2]

/-- The form is genuinely indefinite: it takes the value `1` and the value `-1`. -/
theorem N_indefinite : S.N (1 : A) = 1 ∧ S.N S.epsilon = -1 := ⟨S.N_one, S.N_epsilon⟩

/-- The symmetric bilinear form polarising `N`. -/
def polar (x y : A) : ℝ := (S.N (x + y) - S.N x - S.N y) / 2

theorem polar_eq (x y : A) :
    S.polar x y = (S.coordP x * S.coordQ y + S.coordQ x * S.coordP y) / 2 := by
  simp [polar, N]; ring

theorem polar_self (x : A) : S.polar x x = S.N x := by
  rw [polar_eq, N]; ring

/-- The polar form is nondegenerate; together with `N_one_epsilon_frame` this says the
quadratic form has signature `(1,1)`. -/
theorem polar_nondegenerate {x : A} (h : ∀ y, S.polar x y = 0) : x = 0 := by
  have h1 := h S.p
  have h2 := h S.q
  rw [polar_eq] at h1 h2
  simp at h1 h2
  refine S.ext_coords ?_ ?_ <;> simp [h1, h2]

/-! ## 7. The norm-one structure, constructed intrinsically -/

/-- The norm-one subset of `A`. -/
def U1 : Set A := {g | S.N g = 1}

@[simp] lemma mem_U1 {g : A} : g ∈ S.U1 ↔ S.N g = 1 := Iff.rfl

/-- **Invertibility is derived, not assumed**: `g σ(g) = 1` for norm-one `g`. -/
theorem mul_sigmaHom_of_mem_U1 {g : A} (h : g ∈ S.U1) : g * S.sigmaHom g = 1 := by
  rw [S.mul_sigmaHom, S.mem_U1.mp h, one_smul]

theorem isUnit_of_mem_U1 {g : A} (h : g ∈ S.U1) : IsUnit g :=
  IsUnit.of_mul_eq_one (S.sigmaHom g) (S.mul_sigmaHom_of_mem_U1 h)

theorem one_mem_U1 : (1 : A) ∈ S.U1 := by simp

theorem mul_mem_U1 {g h : A} (hg : g ∈ S.U1) (hh : h ∈ S.U1) : g * h ∈ S.U1 := by
  simp only [mem_U1, S.N_mul, S.mem_U1.mp hg, S.mem_U1.mp hh, one_mul]

/-- The inverse of a norm-one element is again of norm one (and is `σ g`). -/
theorem sigmaHom_mem_U1 {g : A} (hg : g ∈ S.U1) : S.sigmaHom g ∈ S.U1 := by
  have := S.mem_U1.mp hg
  simp only [mem_U1, N, S.coordP_sigmaHom, S.coordQ_sigmaHom]
  rw [mul_comm]
  simpa [N] using this

/-- The norm-one condition in sector coordinates. -/
theorem mem_U1_iff_coords (a b : ℝ) : a • S.p + b • S.q ∈ S.U1 ↔ a * b = 1 := by simp

/-- The reciprocal relation `b = a⁻¹`, derived solely from `N = 1`. -/
theorem coordQ_eq_inv_coordP {g : A} (hg : g ∈ S.U1) : S.coordQ g = (S.coordP g)⁻¹ := by
  have h : S.coordP g * S.coordQ g = 1 := S.mem_U1.mp hg
  have ha : S.coordP g ≠ 0 := by rintro h0; rw [h0, zero_mul] at h; exact zero_ne_one h
  field_simp
  linear_combination h

/-- The norm-one elements, as a subgroup of the unit group of `A`. -/
def U1Group : Subgroup Aˣ where
  carrier := {g : Aˣ | S.N (g : A) = 1}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq, Units.val_mul, S.N_mul] at *
    rw [hg, hh, one_mul]
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at *
    have : S.N ((g : A) * (↑g⁻¹ : A)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, S.N_one]
    rw [S.N_mul, hg, one_mul] at this
    exact this

@[simp] lemma mem_U1Group {g : Aˣ} : g ∈ S.U1Group ↔ S.N (g : A) = 1 := Iff.rfl

/-! ## 8. The positive norm-one branch -/

/-- The positive branch of the norm-one set.  (No topological claim is made: this is
*not* asserted to be the identity component.) -/
def U1pos : Set A := {g : A | ∃ a : ℝ, 0 < a ∧ g = a • S.p + a⁻¹ • S.q}

theorem U1pos_subset_U1 : S.U1pos ⊆ S.U1 := by
  rintro g ⟨a, ha, rfl⟩
  simp [mul_inv_cancel₀ (ne_of_gt ha)]

theorem one_mem_U1pos : (1 : A) ∈ S.U1pos :=
  ⟨1, one_pos, by simp [← S.sum_eq_one]⟩

theorem mul_mem_U1pos {g h : A} (hg : g ∈ S.U1pos) (hh : h ∈ S.U1pos) : g * h ∈ S.U1pos := by
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨b, hb, rfl⟩ := hh
  refine ⟨a * b, mul_pos ha hb, ?_⟩
  rw [S.mul_decomp, mul_inv]

theorem sigmaHom_mem_U1pos {g : A} (hg : g ∈ S.U1pos) : S.sigmaHom g ∈ S.U1pos := by
  obtain ⟨a, ha, rfl⟩ := hg
  refine ⟨a⁻¹, inv_pos.mpr ha, ?_⟩
  rw [S.sigmaHom_smul_add_smul, inv_inv]

/-- Each element of the positive branch has a *unique* positive coordinate. -/
theorem U1pos_unique_coord {g : A} (hg : g ∈ S.U1pos) :
    ∃! a : ℝ, 0 < a ∧ g = a • S.p + a⁻¹ • S.q := by
  obtain ⟨a, ha, rfl⟩ := hg
  refine ⟨a, ⟨ha, rfl⟩, ?_⟩
  rintro c ⟨hc, hce⟩
  exact ((S.coords_unique hce).1).symm

/-- The one-parameter family of positive norm-one elements. -/
def gElem (η : ℝ) : A := exp η • S.p + exp (-η) • S.q

@[simp] theorem coordP_gElem (η : ℝ) : S.coordP (S.gElem η) = exp η := by simp [gElem]

@[simp] theorem coordQ_gElem (η : ℝ) : S.coordQ (S.gElem η) = exp (-η) := by simp [gElem]

@[simp] theorem N_gElem (η : ℝ) : S.N (S.gElem η) = 1 := by
  simp [gElem, ← Real.exp_add]

theorem gElem_zero : S.gElem 0 = 1 := by simp [gElem, ← S.sum_eq_one]

theorem gElem_add (η₁ η₂ : ℝ) : S.gElem (η₁ + η₂) = S.gElem η₁ * S.gElem η₂ := by
  rw [gElem, gElem, gElem, S.mul_decomp, ← Real.exp_add, ← Real.exp_add]
  ring_nf

theorem gElem_mul_gElem_neg (η : ℝ) : S.gElem η * S.gElem (-η) = 1 := by
  rw [← S.gElem_add, add_neg_cancel, S.gElem_zero]

theorem gElem_injective : Function.Injective S.gElem := by
  intro η₁ η₂ h
  have h2 : exp η₁ = exp η₂ := by
    have := congrArg S.coordP h
    simpa using this
  exact Real.exp_eq_exp.mp h2

theorem gElem_mem_U1pos (η : ℝ) : S.gElem η ∈ S.U1pos :=
  ⟨exp η, Real.exp_pos η, by rw [gElem, Real.exp_neg]⟩

/-- **Exponential parametrisation.** Every element of the positive norm-one branch is
`g η = e^η p + e^{-η} q` for a unique real `η`. -/
theorem exists_unique_eta {g : A} (hg : g ∈ S.U1pos) : ∃! η : ℝ, g = S.gElem η := by
  obtain ⟨a, ha, rfl⟩ := hg
  refine ⟨Real.log a, ?_, ?_⟩
  · show a • S.p + a⁻¹ • S.q = exp (Real.log a) • S.p + exp (-Real.log a) • S.q
    rw [Real.exp_log ha, Real.exp_neg, Real.exp_log ha]
  · intro η h
    have h' : a • S.p + a⁻¹ • S.q = exp η • S.p + exp (-η) • S.q := h
    have ha' := (S.coords_unique h').1
    rw [ha', Real.log_exp]

theorem U1pos_eq_range_gElem : S.U1pos = Set.range S.gElem := by
  ext g
  constructor
  · intro hg
    obtain ⟨η, h, -⟩ := S.exists_unique_eta hg
    exact ⟨η, h.symm⟩
  · rintro ⟨η, rfl⟩
    exact S.gElem_mem_U1pos η

/-- `g η` as a unit of `A`. -/
def gUnit (η : ℝ) : Aˣ where
  val := S.gElem η
  inv := S.gElem (-η)
  val_inv := S.gElem_mul_gElem_neg η
  inv_val := by rw [← S.gElem_add, neg_add_cancel, S.gElem_zero]

@[simp] lemma gUnit_val (η : ℝ) : (S.gUnit η : A) = S.gElem η := rfl

@[simp] lemma gUnit_inv (η : ℝ) : ((S.gUnit η)⁻¹ : Aˣ) = S.gUnit (-η) := Units.ext rfl

/-- The exponential parametrisation as a monoid homomorphism from `(ℝ, +)`. -/
def gHom : Multiplicative ℝ →* Aˣ where
  toFun η := S.gUnit (Multiplicative.toAdd η)
  map_one' := Units.ext (by simpa using S.gElem_zero)
  map_mul' η₁ η₂ := Units.ext (by simpa using S.gElem_add _ _)

@[simp] lemma gHom_apply (η : Multiplicative ℝ) :
    S.gHom η = S.gUnit (Multiplicative.toAdd η) := rfl

theorem gHom_injective : Function.Injective S.gHom := by
  intro η₁ η₂ h
  have : S.gElem (Multiplicative.toAdd η₁) = S.gElem (Multiplicative.toAdd η₂) :=
    congrArg Units.val h
  exact Multiplicative.toAdd.injective (S.gElem_injective this)

/-- **`(ℝ, +)` is isomorphic to the positive norm-one branch.** -/
def etaEquiv : Multiplicative ℝ ≃* S.gHom.range := MonoidHom.ofInjective S.gHom_injective

/-- The underlying set of the group `gHom.range` is exactly the positive branch. -/
theorem coe_gHom_range : (fun u : Aˣ => (u : A)) '' (S.gHom.range : Set Aˣ) = S.U1pos := by
  ext g
  constructor
  · rintro ⟨u, ⟨η, rfl⟩, rfl⟩
    exact S.gElem_mem_U1pos _
  · intro hg
    obtain ⟨η, h, -⟩ := S.exists_unique_eta hg
    exact ⟨S.gUnit η, ⟨Multiplicative.ofAdd η, rfl⟩, h.symm⟩

/-- The positive branch sits inside the norm-one group. -/
theorem gHom_range_le_U1Group : S.gHom.range ≤ S.U1Group := by
  rintro u ⟨η, rfl⟩
  simp [U1Group]

/-! ## 9. The reciprocal action, derived -/

/-- **The reciprocal exponential action is derived**, as plain multiplication by `g η`. -/
theorem gElem_mul (η u v : ℝ) :
    S.gElem η * (u • S.p + v • S.q) = (exp η * u) • S.p + (exp (-η) * v) • S.q := by
  rw [gElem, S.mul_decomp]

@[simp] theorem coordP_gElem_mul (η : ℝ) (z : A) :
    S.coordP (S.gElem η * z) = exp η * S.coordP z := by simp

@[simp] theorem coordQ_gElem_mul (η : ℝ) (z : A) :
    S.coordQ (S.gElem η * z) = exp (-η) * S.coordQ z := by simp

/-- Norm preservation, obtained from multiplicativity of `N` and `N (g η) = 1`. -/
theorem N_gElem_mul (η : ℝ) (z : A) : S.N (S.gElem η * z) = S.N z := by
  rw [S.N_mul, S.N_gElem, one_mul]

/-- `u' v' = u v`. -/
theorem coord_product_invariant (η u v : ℝ) :
    S.coordP (S.gElem η * (u • S.p + v • S.q)) * S.coordQ (S.gElem η * (u • S.p + v • S.q))
      = u * v := by
  have := S.N_gElem_mul η (u • S.p + v • S.q)
  simpa [N] using this

/-! ### The positive branch is a proper subgroup of the norm-one set

The exponential parametrisation covers **exactly half** of `U₁`: the norm-one set also
contains `-g η`, and `-1 ∉ U₁⁺`.  This is an honest limitation of obligation 8 and the
reason the positive branch has to be isolated by hand. -/

theorem neg_one_mem_U1 : (-1 : A) ∈ S.U1 := by
  simp [mem_U1, N]

theorem neg_one_not_mem_U1pos : (-1 : A) ∉ S.U1pos := by
  rintro ⟨a, ha, h⟩
  have h' : (-1 : ℝ) • S.p + (-1 : ℝ) • S.q = a • S.p + a⁻¹ • S.q := by
    rw [← h, ← S.sum_eq_one]; module
  have := (S.coords_unique h').1
  linarith

theorem U1pos_ne_U1 : S.U1pos ≠ S.U1 := by
  intro h
  exact S.neg_one_not_mem_U1pos (h ▸ S.neg_one_mem_U1)

/-- The full norm-one set is the union of the positive branch and its negative. -/
theorem mem_U1_iff_exists : ∀ g : A, g ∈ S.U1 ↔ ∃ η : ℝ, g = S.gElem η ∨ g = -S.gElem η := by
  intro g
  constructor
  · intro hg
    have hab : S.coordP g * S.coordQ g = 1 := S.mem_U1.mp hg
    have ha : S.coordP g ≠ 0 := by
      rintro h0; rw [h0, zero_mul] at hab; exact zero_ne_one hab
    have hb : S.coordQ g = (S.coordP g)⁻¹ := S.coordQ_eq_inv_coordP hg
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · refine ⟨Real.log (-S.coordP g), Or.inr ?_⟩
      have hpos' : 0 < -S.coordP g := by linarith
      rw [gElem, Real.exp_log hpos', Real.exp_neg, Real.exp_log hpos']
      conv_lhs => rw [S.decomp g, hb]
      rw [show -((-S.coordP g) • S.p + (-S.coordP g)⁻¹ • S.q)
            = S.coordP g • S.p + (-(-S.coordP g)⁻¹) • S.q by module]
      rw [← inv_neg, neg_neg]
    · refine ⟨Real.log (S.coordP g), Or.inl ?_⟩
      rw [gElem, Real.exp_log hpos, Real.exp_neg, Real.exp_log hpos]
      conv_lhs => rw [S.decomp g, hb]
  · rintro ⟨η, rfl | rfl⟩
    · simp [mem_U1]
    · simp [mem_U1, N, ← Real.exp_add]

/-! ## 10. The standard `1+1` Lorentz formulas, as corollaries

The positive constant `c` is introduced **here**, purely as a coordinate scale on the
already-derived null coordinates; nothing about it is derived. -/

/-- The null coordinates of the boosted element: `u' = e^η u`. -/
theorem coordP_gElem_lightcone (η c t x : ℝ) :
    S.coordP (S.gElem η * ((c * t + x) • S.p + (c * t - x) • S.q)) = exp η * (c * t + x) := by
  simp

/-- The null coordinates of the boosted element: `v' = e^{-η} v`. -/
theorem coordQ_gElem_lightcone (η c t x : ℝ) :
    S.coordQ (S.gElem η * ((c * t + x) • S.p + (c * t - x) • S.q)) = exp (-η) * (c * t - x) := by
  simp

end SectorAlgebra

/-! The following three lemmas are statements about real numbers only; they convert the
derived reciprocal action into the familiar hyperbolic form. -/

/-- `c t' = (u' + v')/2 = cosh η · c t + sinh η · x`. -/
theorem lorentz_ct (η ct x : ℝ) :
    (exp η * (ct + x) + exp (-η) * (ct - x)) / 2 = cosh η * ct + sinh η * x := by
  rw [Real.cosh_eq, Real.sinh_eq]; ring

/-- `x' = (u' - v')/2 = sinh η · c t + cosh η · x`. -/
theorem lorentz_x (η ct x : ℝ) :
    (exp η * (ct + x) - exp (-η) * (ct - x)) / 2 = sinh η * ct + cosh η * x := by
  rw [Real.cosh_eq, Real.sinh_eq]; ring

/-- **Sign convention.** Replacing `η` by `-η` (equivalently: exchanging the roles of the
two sectors, or replacing `x` by `-x`) yields the boost with the opposite off-diagonal
signs.  Applying two of these three changes at once restores the original signs. -/
theorem lorentz_ct_opposite_sign (η ct x : ℝ) :
    (exp (-η) * (ct + x) + exp η * (ct - x)) / 2 = cosh η * ct - sinh η * x := by
  rw [Real.cosh_eq, Real.sinh_eq]; ring

theorem lorentz_x_opposite_sign (η ct x : ℝ) :
    (exp (-η) * (ct + x) - exp η * (ct - x)) / 2 = -(sinh η * ct) + cosh η * x := by
  rw [Real.cosh_eq, Real.sinh_eq]; ring

/-- Invariance of the Minkowski form in the `(ct, x)` variables. -/
theorem minkowski_invariant (η ct x : ℝ) :
    (cosh η * ct + sinh η * x) ^ 2 - (sinh η * ct + cosh η * x) ^ 2 = ct ^ 2 - x ^ 2 := by
  have h : cosh η ^ 2 - sinh η ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq η
  nlinarith [h]

/-- With `β = tanh η` one has `γ = cosh η = 1/√(1 - β²)`. -/
theorem gamma_eq_cosh (η : ℝ) : cosh η = 1 / Real.sqrt (1 - tanh η ^ 2) := by
  have hc : 0 < cosh η := Real.cosh_pos η
  have hid : 1 - tanh η ^ 2 = (1 / cosh η) ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh, div_pow, div_pow]
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq η]
  rw [hid, Real.sqrt_sq (by positivity)]
  field_simp

/-- The image of the line `x = 0` has slope `β = x'/(ct') = tanh η`. -/
theorem velocity_eq_tanh (η ct : ℝ) (h : ct ≠ 0) :
    (sinh η * ct + cosh η * 0) / (cosh η * ct + sinh η * 0) = tanh η := by
  have hc : cosh η ≠ 0 := ne_of_gt (Real.cosh_pos η)
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring

/-- `|β| < 1`. -/
theorem abs_tanh_lt_one (η : ℝ) : |tanh η| < 1 :=
  abs_lt.mpr ⟨Real.neg_one_lt_tanh η, Real.tanh_lt_one η⟩

/-- Invariance of `c²t² - x²` under the derived action, in the `(ct, x)` variables. -/
theorem minkowski_invariant_c (η c t x : ℝ) :
    (cosh η * (c * t) + sinh η * x) ^ 2 - (sinh η * (c * t) + cosh η * x) ^ 2
      = c ^ 2 * t ^ 2 - x ^ 2 := by
  rw [minkowski_invariant]; ring

namespace SectorAlgebra

variable {A : Type*} [CommRing A] [Algebra ℝ A] (S : SectorAlgebra A)

/-- The full `1+1` Lorentz statement in the derived setting: the boosted null coordinates
recombine into the standard hyperbolic transformation, and `c²t² - x²` is preserved. -/
theorem lorentz_boost (η c t x : ℝ) :
    (S.coordP (S.gElem η * ((c * t + x) • S.p + (c * t - x) • S.q))
        + S.coordQ (S.gElem η * ((c * t + x) • S.p + (c * t - x) • S.q))) / 2
      = cosh η * (c * t) + sinh η * x ∧
    (S.coordP (S.gElem η * ((c * t + x) • S.p + (c * t - x) • S.q))
        - S.coordQ (S.gElem η * ((c * t + x) • S.p + (c * t - x) • S.q))) / 2
      = sinh η * (c * t) + cosh η * x := by
  rw [S.coordP_gElem_lightcone, S.coordQ_gElem_lightcone]
  exact ⟨lorentz_ct η (c * t) x, lorentz_x η (c * t) x⟩

/-! ## 11. Sectorwise invariant dual pairings -/

/-- **Sectorwise invariant dual pairing** in the `p`-sector: if `k₊` transforms
contragrediently, `k₊' = e^{-η} k₊`, then `k₊' u' = k₊ u`. -/
theorem dual_pairing_p_invariant (η kp u v : ℝ) :
    (exp (-η) * kp) * S.coordP (S.gElem η * (u • S.p + v • S.q)) = kp * u := by
  simp only [S.coordP_gElem_mul, S.coordP_smul_add_smul]
  rw [show exp (-η) * kp * (exp η * u) = (exp (-η) * exp η) * (kp * u) by ring,
    ← Real.exp_add]
  simp

/-- **Sectorwise invariant dual pairing** in the `q`-sector: if `k₋' = e^{η} k₋`, then
`k₋' v' = k₋ v`. -/
theorem dual_pairing_q_invariant (η km u v : ℝ) :
    (exp η * km) * S.coordQ (S.gElem η * (u • S.p + v • S.q)) = km * v := by
  simp only [S.coordQ_gElem_mul, S.coordQ_smul_add_smul]
  rw [show exp η * km * (exp (-η) * v) = (exp η * exp (-η)) * (km * v) by ring,
    ← Real.exp_add]
  simp

/-- Optional corollary, notation only: writing `Φ₊ = k₊ u`, `Φ₋ = k₋ v`, the complex
exponentials `e^{iΦ±}` are unchanged.  No interpretation is attached to these quantities. -/
theorem cexp_dual_pairing_p_invariant (η kp u v : ℝ) :
    Complex.exp (Complex.I *
        ((exp (-η) * kp) * S.coordP (S.gElem η * (u • S.p + v • S.q)) : ℝ))
      = Complex.exp (Complex.I * ((kp * u : ℝ))) := by
  rw [S.dual_pairing_p_invariant]

theorem cexp_dual_pairing_q_invariant (η km u v : ℝ) :
    Complex.exp (Complex.I *
        ((exp η * km) * S.coordQ (S.gElem η * (u • S.p + v • S.q)) : ℝ))
      = Complex.exp (Complex.I * ((km * v : ℝ))) := by
  rw [S.dual_pairing_q_invariant]

end SectorAlgebra

/-! ## 12. The final dependency theorem -/

/-- **Final dependency theorem.**

Let `A` be a two-dimensional commutative unital real algebra containing two nonzero
complementary orthogonal idempotents `p, q` (these seven hypotheses are the *only*
assumptions).  Then there exist `ε`, an involution `σ`, a norm `N` and a one-parameter
family `g` such that:

1. `A ≅ ℝ × ℝ` as unital `ℝ`-algebras, and `p, q` give unique coordinates;
2. `ε = p - q` satisfies `ε² = 1` (and `ε ≠ ±1`);
3. `σ` is the sector-exchanging involutive algebra automorphism;
4. `x σ x = N x • 1` with `N (a p + b q) = a b`, and `N` is multiplicative;
5. the positive norm-one elements are exactly the `g η = e^η p + e^{-η} q`, uniquely, and
   `η ↦ g η` is a one-parameter group;
6. the multiplicative action of `g η` is `(u, v) ↦ (e^η u, e^{-η} v)`;
7. this action preserves `u v`;
8. after the coordinate identification `u = ct + x`, `v = ct - x` it is the standard
   `1+1` Lorentz boost and preserves `c²t² - x²`;
9. contragredient coefficients give sectorwise invariant dual pairings.

No physical interpretation is asserted. -/
theorem sector_dependency_theorem {A : Type*} [CommRing A] [Algebra ℝ A] (p q : A)
    (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hsum : p + q = 1)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hdim : Module.finrank ℝ A = 2) :
    ∃ (eps : A) (sigma : A →ₐ[ℝ] A) (N : A → ℝ) (g : ℝ → A),
      -- 1. the sector decomposition
      (Nonempty (A ≃ₐ[ℝ] ℝ × ℝ)) ∧
      (∀ z : A, ∃! ab : ℝ × ℝ, z = ab.1 • p + ab.2 • q) ∧
      (∀ a b c d : ℝ, (a • p + b • q) * (c • p + d • q) = (a * c) • p + (b * d) • q) ∧
      -- 2. the split generator
      (eps = p - q ∧ eps * eps = 1 ∧ eps ≠ 1 ∧ eps ≠ -1) ∧
      -- 3. the sector-exchanging involution
      ((∀ a b : ℝ, sigma (a • p + b • q) = b • p + a • q) ∧
        (∀ z, sigma (sigma z) = z) ∧ sigma p = q ∧ sigma q = p ∧ sigma eps = -eps ∧
        (∀ f : A →ₐ[ℝ] A, f p = q → f q = p → f = sigma)) ∧
      -- 4. the multiplicative norm
      ((∀ z, z * sigma z = N z • (1 : A)) ∧ (∀ a b : ℝ, N (a • p + b • q) = a * b) ∧
        (∀ z w, N (z * w) = N z * N w)) ∧
      -- 5. the positive norm-one branch
      ((∀ η : ℝ, g η = exp η • p + exp (-η) • q) ∧
        (∀ z : A, (∃ a : ℝ, 0 < a ∧ z = a • p + a⁻¹ • q) ↔ ∃ η : ℝ, z = g η) ∧
        (∀ z : A, (∃ a : ℝ, 0 < a ∧ z = a • p + a⁻¹ • q) → ∃! η : ℝ, z = g η) ∧
        g 0 = 1 ∧ (∀ η₁ η₂, g (η₁ + η₂) = g η₁ * g η₂) ∧ (∀ η, g η * g (-η) = 1) ∧
        (∀ η, N (g η) = 1)) ∧
      -- 6. the reciprocal action, derived
      (∀ η u v : ℝ, g η * (u • p + v • q) = (exp η * u) • p + (exp (-η) * v) • q) ∧
      -- 7. invariance of `u v`, intrinsically and in coordinates
      (∀ (η : ℝ) (z : A), N (g η * z) = N z) ∧
      (∀ η u v : ℝ, (exp η * u) * (exp (-η) * v) = u * v) ∧
      -- 8. the standard `1+1` Lorentz boost
      (∀ η c t x : ℝ,
        (exp η * (c * t + x) + exp (-η) * (c * t - x)) / 2 = cosh η * (c * t) + sinh η * x ∧
        (exp η * (c * t + x) - exp (-η) * (c * t - x)) / 2 = sinh η * (c * t) + cosh η * x ∧
        (cosh η * (c * t) + sinh η * x) ^ 2 - (sinh η * (c * t) + cosh η * x) ^ 2
          = c ^ 2 * t ^ 2 - x ^ 2) ∧
      -- 9. sectorwise invariant dual pairings
      (∀ η kp km u v : ℝ,
        (exp (-η) * kp) * (exp η * u) = kp * u ∧ (exp η * km) * (exp (-η) * v) = km * v) := by
  let S : Sector.SectorAlgebra A :=
    { p := p, q := q, sq_p := hp, sq_q := hq, orth := hpq, sum_eq_one := hsum,
      p_ne_zero := hp0, q_ne_zero := hq0, finrank_eq := hdim }
  have hexp : ∀ η : ℝ, exp η * exp (-η) = 1 := by
    intro η; rw [← Real.exp_add]; simp
  refine ⟨S.epsilon, S.sigmaHom, S.N, S.gElem,
    S.exists_algEquiv_prod, S.existsUnique_coords, S.mul_decomp,
    ⟨rfl, S.epsilon_sq, S.epsilon_ne_one, S.epsilon_ne_neg_one⟩,
    ⟨S.sigmaHom_smul_add_smul, S.sigmaHom_sigmaHom, S.sigmaHom_p, S.sigmaHom_q,
      S.sigmaHom_epsilon, fun f hf hf' => S.sigmaHom_unique f hf hf'⟩,
    ⟨S.mul_sigmaHom, S.N_smul_add_smul, S.N_mul⟩,
    ⟨fun η => rfl, ?_, ?_, S.gElem_zero, S.gElem_add, S.gElem_mul_gElem_neg, S.N_gElem⟩,
    S.gElem_mul, S.N_gElem_mul, ?_, ?_, ?_⟩
  · intro z
    constructor
    · intro hz
      obtain ⟨η, h, -⟩ := S.exists_unique_eta hz
      exact ⟨η, h⟩
    · rintro ⟨η, rfl⟩
      exact S.gElem_mem_U1pos η
  · intro z hz
    exact S.exists_unique_eta hz
  · intro η u v
    rw [show exp η * u * (exp (-η) * v) = (exp η * exp (-η)) * (u * v) by ring, hexp, one_mul]
  · intro η c t x
    exact ⟨lorentz_ct η (c * t) x, lorentz_x η (c * t) x, minkowski_invariant_c η c t x⟩
  · intro η kp km u v
    constructor
    · rw [show exp (-η) * kp * (exp η * u) = (exp η * exp (-η)) * (kp * u) by ring, hexp, one_mul]
    · rw [show exp η * km * (exp (-η) * v) = (exp η * exp (-η)) * (km * v) by ring, hexp, one_mul]

/-! ## Consistency of the primitive assumptions

The hypotheses of `sector_dependency_theorem` are not vacuous: `ℝ × ℝ` with
`p = (1, 0)`, `q = (0, 1)` satisfies all of them. -/

/-! ## Sharpness: the dimension hypothesis is load-bearing

The implication "nonzero complementary orthogonal idempotents `⇒` `A ≅ ℝ × ℝ`" is **false**
without `dimℝ A = 2`.  In `ℝ³` the pair `p = (1,0,0)`, `q = (0,1,1)` satisfies every one of
the idempotent hypotheses, yet `p, q` do not span, and `ℝ³ ≉ ℝ × ℝ`. -/

namespace Counterexample

/-- The three-dimensional test algebra. -/
abbrev B : Type := ℝ × ℝ × ℝ

/-- A nonzero idempotent of `ℝ³`. -/
def pc : B := (1, 0, 0)

/-- Its complementary orthogonal idempotent. -/
def qc : B := (0, 1, 1)

theorem pc_sq : pc * pc = pc := by norm_num [pc, Prod.ext_iff]

theorem qc_sq : qc * qc = qc := by norm_num [qc, Prod.ext_iff]

theorem pc_mul_qc : pc * qc = 0 := by norm_num [pc, qc, Prod.ext_iff]

theorem pc_add_qc : pc + qc = 1 := by norm_num [pc, qc, Prod.ext_iff]

theorem pc_ne_zero : pc ≠ 0 := by simp [pc, Prod.ext_iff]

theorem qc_ne_zero : qc ≠ 0 := by simp [qc, Prod.ext_iff]

/-- **Obstruction.** Without the dimension hypothesis the sector decomposition fails:
`(0, 1, 0)` is not of the form `a p + b q`. -/
theorem no_sector_decomposition : ¬ ∀ x : B, ∃ a b : ℝ, x = a • pc + b • qc := by
  intro h
  obtain ⟨a, b, hab⟩ := h (0, 1, 0)
  have h1 := congrArg (fun z : B => z.2.1) hab
  have h2 := congrArg (fun z : B => z.2.2) hab
  simp [pc, qc] at h1 h2
  exact one_ne_zero (h1.trans h2.symm)

/-- **Obstruction.** `ℝ³` is not isomorphic to `ℝ × ℝ`, so complementary idempotents alone
do not force the split-complex algebra. -/
theorem not_algEquiv_prod : IsEmpty (B ≃ₐ[ℝ] ℝ × ℝ) := by
  refine ⟨fun e => ?_⟩
  have h := e.toLinearEquiv.finrank_eq
  simp at h

end Counterexample

/-- A witness that the primitive assumptions are satisfiable. -/
def prodSectorAlgebra : Sector.SectorAlgebra (ℝ × ℝ) where
  p := (1, 0)
  q := (0, 1)
  sq_p := by norm_num [Prod.ext_iff]
  sq_q := by norm_num [Prod.ext_iff]
  orth := by norm_num [Prod.ext_iff]
  sum_eq_one := by norm_num [Prod.ext_iff]
  p_ne_zero := by simp [Prod.ext_iff]
  q_ne_zero := by simp [Prod.ext_iff]
  finrank_eq := by simp

end Sector
