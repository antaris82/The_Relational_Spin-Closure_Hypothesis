import Mathlib

/-!
# Carrier audit: commutativity, carrier reformulation, and necessity of the sector hypotheses

This file is independent of `RequestProject.Experiment1.SectorAlgebra`.  It settles three questions
about the *primitive carrier data* used there.

* `Sector.commutative_of_finrank_two` — a two-dimensional unital associative real algebra is
  automatically commutative.  Hence commutativity is **not** a primitive assumption.
* `Sector.splitGenerator_iff_sectorPair` — in any unital real algebra, the existence of a
  nontrivial split generator (`ε² = 1`, `ε ≠ ±1`) is *equivalent* to the existence of two
  nonzero complementary orthogonal idempotents.  Hence passing from one description to the
  other is a **reformulation** of the carrier information, not a weakening of it.
* `Sector.DualNumbers` — a two-dimensional unital real algebra with a nonzero square-zero
  element, in which the *degenerate* sector pair `p = 1`, `q = 0` satisfies every idempotent
  equation.  It is not isomorphic to `ℝ × ℝ`, so the hypotheses `p ≠ 0`, `q ≠ 0` are
  load-bearing.  Only the algebraic obstruction is proved; no kinematic reading is attached.

No physical interpretation is asserted anywhere in this file.
-/

noncomputable section

open Module

namespace Sector

/-! ## 1. Commutativity is derivable, not primitive -/

/-- **Commutativity is not a primitive assumption.**  Every two-dimensional associative
unital real algebra is commutative.

Proof route: real scalars are central; some `a` lies outside `ℝ·1` (else the dimension
would be at most one); `{1, a}` is then linearly independent, hence a basis; expanding two
general elements in this basis, both products equal the same expression. -/
theorem commutative_of_finrank_two
    {A : Type*} [Ring A] [Algebra ℝ A]
    (hdim : Module.finrank ℝ A = 2) :
    ∀ x y : A, x * y = y * x := by
  have hnt : Nontrivial A := by
    rcases subsingleton_or_nontrivial A with hs | hn
    · exfalso
      have h0 : Module.finrank ℝ A = 0 := by
        have : Subsingleton A := hs
        simp [Module.finrank_zero_of_subsingleton]
      omega
    · exact hn
  have hex : ∃ a : A, a ∉ Submodule.span ℝ ({1} : Set A) := by
    by_contra h
    push_neg at h
    have htop : Submodule.span ℝ ({1} : Set A) = ⊤ := by
      rw [eq_top_iff]; intro x _; exact h x
    have h1 : Module.finrank ℝ (Submodule.span ℝ ({1} : Set A))
        ≤ (Set.toFinset ({1} : Set A)).card := finrank_span_le_card _
    rw [htop] at h1
    simp [finrank_top, hdim] at h1
  obtain ⟨a, ha⟩ := hex
  have hli : LinearIndependent ℝ ![(1 : A), a] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have ht : t = 0 := by
      by_contra ht
      apply ha
      have h2 : t • a = (-s) • (1 : A) := by
        rw [← sub_eq_zero, show t • a - (-s) • (1 : A) = s • (1 : A) + t • a by module, h]
      have h3 := congrArg (fun z : A => t⁻¹ • z) h2
      simp only [smul_smul, inv_mul_cancel₀ ht, one_smul] at h3
      rw [h3]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    subst ht
    simp at h
    exact ⟨h, rfl⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ A := by simp [hdim]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ⇑b = ![(1 : A), a] := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hrepr : ∀ x : A, ∃ α β : ℝ, x = α • (1 : A) + β • a := by
    intro x
    refine ⟨b.repr x 0, b.repr x 1, ?_⟩
    conv_lhs => rw [← b.sum_repr x]
    simp [Fin.sum_univ_succ, hb]
  intro x y
  obtain ⟨α, β, rfl⟩ := hrepr x
  obtain ⟨γ, δ, rfl⟩ := hrepr y
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

/-- The commutative ring structure supplied by `commutative_of_finrank_two`.  This is a
definition, not an instance, so that it can be introduced locally where needed. -/
def commRingOfFinrankTwo {A : Type*} [Ring A] [Algebra ℝ A]
    (hdim : Module.finrank ℝ A = 2) : CommRing A :=
  { (inferInstance : Ring A) with mul_comm := commutative_of_finrank_two hdim }

/-! ## 2. The two carrier descriptions are equivalent -/

/-- Carrier description A: a nontrivial split generator. -/
def HasNontrivialSplitGenerator (A : Type*) [Ring A] : Prop :=
  ∃ ε : A, ε * ε = 1 ∧ ε ≠ 1 ∧ ε ≠ -1

/-- Carrier description B: two nonzero complementary orthogonal idempotents. -/
def HasNontrivialSectorPair (A : Type*) [Ring A] : Prop :=
  ∃ p q : A,
    p * p = p ∧ q * q = q ∧ p * q = 0 ∧ p + q = 1 ∧ p ≠ 0 ∧ q ≠ 0

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- In a unital real algebra, `2 • z = 0` forces `z = 0`. -/
private theorem two_smul_eq_zero_iff' (z : A) : (2 : ℝ) • z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have := congrArg (fun w : A => (2 : ℝ)⁻¹ • w) h
    simpa [smul_smul] using this
  · rintro rfl; simp

omit [Algebra ℝ A] in
/-- Orthogonality of a complementary idempotent pair is automatically two-sided. -/
theorem orth_symm_of_sector {p q : A} (hq : q * q = q) (hsum : p + q = 1) : q * p = 0 := by
  have hp : p = 1 - q := by rw [← hsum]; abel
  rw [hp, mul_sub, mul_one, hq, sub_self]

/-- **Sector pair `⇒` split generator.**  If `p, q` are nonzero complementary orthogonal
idempotents then `ε := p - q` satisfies `ε² = 1` and `ε ≠ ±1`. -/
theorem splitGenerator_of_sectorPair {p q : A}
    (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hsum : p + q = 1)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    (p - q) * (p - q) = 1 ∧ (p - q) ≠ 1 ∧ (p - q) ≠ -1 := by
  have hqp : q * p = 0 := orth_symm_of_sector hq hsum
  refine ⟨?_, ?_, ?_⟩
  · have hexp : (p - q) * (p - q) = p * p - p * q - (q * p) + q * q := by noncomm_ring
    rw [hexp, hp, hq, hpq, hqp, sub_zero, sub_zero]
    exact hsum
  · intro h
    apply hq0
    rw [← two_smul_eq_zero_iff']
    have : p - q = p + q := by rw [h, hsum]
    have h2 : q + q = 0 := by linear_combination (norm := module) -this
    rw [show (2 : ℝ) • q = q + q by module, h2]
  · intro h
    apply hp0
    rw [← two_smul_eq_zero_iff']
    have : p - q = -(p + q) := by rw [h, hsum]
    have h2 : p + p = 0 := by linear_combination (norm := module) this
    rw [show (2 : ℝ) • p = p + p by module, h2]

/-- **Split generator `⇒` sector pair.**  If `ε² = 1` and `ε ≠ ±1` then
`p := (1+ε)/2`, `q := (1-ε)/2` are nonzero complementary orthogonal idempotents. -/
theorem sectorPair_of_splitGenerator {e : A}
    (he : e * e = 1) (he1 : e ≠ 1) (he2 : e ≠ -1) :
    ((2 : ℝ)⁻¹ • (1 + e)) * ((2 : ℝ)⁻¹ • (1 + e)) = (2 : ℝ)⁻¹ • (1 + e) ∧
    ((2 : ℝ)⁻¹ • (1 - e)) * ((2 : ℝ)⁻¹ • (1 - e)) = (2 : ℝ)⁻¹ • (1 - e) ∧
    ((2 : ℝ)⁻¹ • (1 + e)) * ((2 : ℝ)⁻¹ • (1 - e)) = 0 ∧
    ((2 : ℝ)⁻¹ • (1 + e)) + ((2 : ℝ)⁻¹ • (1 - e)) = 1 ∧
    ((2 : ℝ)⁻¹ • (1 + e)) ≠ 0 ∧ ((2 : ℝ)⁻¹ • (1 - e)) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [smul_mul_smul_comm]
    rw [show (1 + e) * (1 + e) = 1 + e + e + e * e by noncomm_ring, he]
    rw [show (1 : A) + e + e + 1 = (2 : ℝ) • (1 + e) by module, smul_smul]
    norm_num
  · rw [smul_mul_smul_comm]
    rw [show (1 - e) * (1 - e) = 1 - e - e + e * e by noncomm_ring, he]
    rw [show (1 : A) - e - e + 1 = (2 : ℝ) • (1 - e) by module, smul_smul]
    norm_num
  · rw [smul_mul_smul_comm]
    rw [show (1 + e) * (1 - e) = 1 - e * e by noncomm_ring, he, sub_self, smul_zero]
  · module
  · intro h
    apply he2
    have h1 : (1 : A) + e = 0 := by
      have := congrArg (fun z : A => (2 : ℝ) • z) h
      simpa [smul_smul] using this
    linear_combination (norm := module) h1
  · intro h
    apply he1
    have h1 : (1 : A) - e = 0 := by
      have := congrArg (fun z : A => (2 : ℝ) • z) h
      simpa [smul_smul] using this
    linear_combination (norm := module) -h1

/-- **The two carrier descriptions are equivalent** in every unital real algebra (no
dimension hypothesis is needed).  Replacing the nontrivial split generator by the
nontrivial complementary sector pair is a *reformulation* of the carrier information, not a
weakening of it. -/
theorem splitGenerator_iff_sectorPair :
    HasNontrivialSplitGenerator A ↔ HasNontrivialSectorPair A := by
  constructor
  · rintro ⟨e, he, he1, he2⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sectorPair_of_splitGenerator he he1 he2
    exact ⟨_, _, h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨p, q, hp, hq, hpq, hsum, hp0, hq0⟩
    obtain ⟨h1, h2, h3⟩ := splitGenerator_of_sectorPair hp hq hpq hsum hp0 hq0
    exact ⟨p - q, h1, h2, h3⟩

/-! ## 3. The nonzero-sector hypotheses are necessary -/

namespace DualNumbers

/-- The two-dimensional real algebra of dual numbers `ℝ[δ]/(δ²)`. -/
abbrev D : Type := TrivSqZeroExt ℝ ℝ

/-- The nonzero square-zero element `δ`. -/
def delta : D := TrivSqZeroExt.inr 1

theorem delta_sq : delta * delta = 0 := by simp [delta]

theorem delta_ne_zero : delta ≠ 0 := by simp [delta, TrivSqZeroExt.ext_iff]

theorem finrank_D : Module.finrank ℝ D = 2 := by simp [TrivSqZeroExt]

/-- The *degenerate* sector pair: all four idempotent equations hold for `p = 1`, `q = 0`. -/
theorem degenerate_pair :
    (1 : D) * 1 = 1 ∧ (0 : D) * 0 = 0 ∧ (1 : D) * 0 = 0 ∧ (1 : D) + 0 = 1 := by
  norm_num

/-- The symmetric degenerate choice `p = 0`, `q = 1` satisfies the same equations; the two
degenerate choices differ only by exchanging the names of the sectors. -/
theorem degenerate_pair_swapped :
    (0 : D) * 0 = 0 ∧ (1 : D) * 1 = 1 ∧ (0 : D) * 1 = 0 ∧ (0 : D) + 1 = 1 := by
  norm_num

/-- `ℝ × ℝ` has no nonzero square-zero element. -/
theorem prod_no_nilpotent (x : ℝ × ℝ) (hx : x * x = 0) : x = 0 := by
  have h1 : x.1 * x.1 = 0 := congrArg Prod.fst hx
  have h2 : x.2 * x.2 = 0 := congrArg Prod.snd hx
  have : x.1 = 0 := by nlinarith
  have : x.2 = 0 := by nlinarith
  ext <;> assumption

/-- **Structural obstruction.**  `D` is a two-dimensional unital real algebra which is not
isomorphic to `ℝ × ℝ`, because it contains a nonzero square-zero element and `ℝ × ℝ` does
not.  Hence dropping `p ≠ 0` (or, symmetrically, `q ≠ 0`) from the carrier data genuinely
weakens it: the remaining equations no longer pin down `ℝ × ℝ`. -/
theorem not_algEquiv_prod : IsEmpty (D ≃ₐ[ℝ] ℝ × ℝ) := by
  refine ⟨fun e => ?_⟩
  have h1 : e delta * e delta = 0 := by rw [← map_mul, delta_sq, map_zero]
  have h2 : e delta = 0 := prod_no_nilpotent _ h1
  exact delta_ne_zero (by simpa using congrArg e.symm h2)

/-- The dual numbers do **not** carry a nontrivial sector pair, so this example is
consistent with `splitGenerator_iff_sectorPair`: it only shows that the nonzero hypotheses
cannot be dropped. -/
theorem not_hasNontrivialSectorPair : ¬ HasNontrivialSectorPair D := by
  rintro ⟨p, q, hp, hq, hpq, hsum, hp0, hq0⟩
  -- `p` is an idempotent of `D`; its scalar part is `0` or `1` and its `δ`-part vanishes.
  have hfst : p.fst * p.fst = p.fst := congrArg TrivSqZeroExt.fst hp
  have hsnd : p.fst * p.snd + p.fst * p.snd = p.snd := by
    have := congrArg TrivSqZeroExt.snd hp
    simpa [TrivSqZeroExt.snd_mul, mul_comm] using this
  have hq' : q = 1 - p := by rw [← hsum]; abel
  have hqfst : q.fst = 1 - p.fst := by rw [hq']; simp
  have hqsnd : q.snd = -p.snd := by rw [hq']; simp
  have hcases : p.fst = 0 ∨ p.fst = 1 := by
    rcases mul_eq_zero.mp (show p.fst * (p.fst - 1) = 0 by nlinarith) with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases hcases with h0 | h1
  · -- `p.fst = 0` forces `p.snd = 0`, i.e. `p = 0`
    apply hp0
    have : p.snd = 0 := by rw [h0] at hsnd; simpa using hsnd.symm
    exact TrivSqZeroExt.ext h0 this
  · -- `p.fst = 1` forces `p.snd = 0` hence `q = 0`
    apply hq0
    have hps : p.snd = 0 := by
      rw [h1] at hsnd; linarith
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [hqfst, h1]; simp
    · rw [hqsnd, hps]; simp

end DualNumbers

end Sector
