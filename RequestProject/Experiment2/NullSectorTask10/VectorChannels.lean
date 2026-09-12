import RequestProject.Experiment2.NullSectorTask10.AlgebraExtension

/-!
# Task 10, Layer 4: longitudinal and transverse channels of the algebra action

The real longitudinal/transverse classification (§11) comes first.  Only after
it is proved is the internally derived central plane `Z = spanℝ{1, S}` used to
ask the eigenchannel question (§13), and only then is the longitudinal channel
compared with the two transverse ones (§14).

Neutral vocabulary throughout: `DISTINGUISHED AXIS`, `LONGITUDINAL`,
`TRANSVERSE`, `CHANNEL`, `WEIGHT`.  No angular-momentum, spin or polarization
name occurs, and none is intended: §15 of the task explicitly forbids reading a
physical mode into any channel found here.
-/

namespace NullSectorTask10

open NullSectorTask01 NullSectorTask04 NullSectorTask07 NullSectorTask08
open NullSectorTask09

/-! ## Central scalars: elementary arithmetic of `Z` acting on the carrier -/

/-- A central scalar of `Z`, written in the derived normal form. -/
def zsc (u v : ℝ) : W := u • w1 + v • wS

theorem zsc_mem_Z (u v : ℝ) : zsc u v ∈ Z := smul_add_smul_mem_Z u v

theorem zsc_mul_zsc (u v u' v' : ℝ) :
    zsc u v ⋆ zsc u' v' = zsc (u * u' - v * v') (u * v' + v * u') := by
  simp only [zsc]
  exact central_mul_rule u v u' v'

theorem zsc_smul (u v : ℝ) (x : W) :
    zsc u v ⋆ x = u • x + v • (wS ⋆ x) := by
  simp only [zsc, add_mul_W, smul_mul_W, one_mul_W]

/-- **FREENESS.**  A nonzero central scalar annihilates no nonzero carrier
element. -/
theorem zsc_mul_eq_zero {u v : ℝ} {ψ : W} (hψ : ψ ≠ 0) (h : zsc u v ⋆ ψ = 0) :
    u = 0 ∧ v = 0 := by
  have hmul : zsc u (-v) ⋆ (zsc u v ⋆ ψ) = ((u * u + v * v) • ψ) := by
    rw [← mul_assoc_W, zsc_mul_zsc]
    have e1 : u * u - -v * v = u * u + v * v := by ring
    have e2 : u * v + -v * u = 0 := by ring
    rw [e1, e2, zsc_smul]
    simp
  rw [h, mul_zero_W] at hmul
  have hsum : u * u + v * v = 0 := by
    by_contra hne
    exact hψ (by
      have := hmul.symm
      have h' : ((u * u + v * v) • ψ) = 0 := this
      rcases smul_eq_zero.1 h' with h1 | h1
      · exact absurd h1 hne
      · exact h1)
  constructor
  · nlinarith [sq_nonneg u, sq_nonneg v]
  · nlinarith [sq_nonneg u, sq_nonneg v]

/-! ## §11 — the real longitudinal/transverse classification -/

/-- The **real transverse plane** inside the carrier: the image of the old
transverse plane. -/
def TransW : Submodule ℝ W := Submodule.span ℝ {wB, wC}

/-- The **longitudinal line** inside the carrier: the image of the distinguished
axis. -/
def LongW : Submodule ℝ W := Submodule.span ℝ {wA}

theorem mem_LongW_iff (x : W) : x ∈ LongW ↔ ∃ a : ℝ, x = a • wA := by
  rw [LongW, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩

theorem mem_TransW_iff (x : W) : x ∈ TransW ↔ ∃ b c : ℝ, x = b • wB + c • wC := by
  rw [TransW, Submodule.mem_span_pair]
  constructor
  · rintro ⟨b, c, rfl⟩; exact ⟨b, c, rfl⟩
  · rintro ⟨b, c, rfl⟩; exact ⟨b, c, rfl⟩

/-- **THE LONGITUDINAL DIRECTION IS FIXED.** -/
theorem Phi_fixes_LongW {x : W} (θ : ℝ) (hx : x ∈ LongW) : Phi θ x = x := by
  obtain ⟨a, rfl⟩ := (mem_LongW_iff x).1 hx
  rw [map_smul, Phi_wA]

/-- **THE TRANSVERSE PLANE IS PRESERVED.** -/
theorem Phi_preserves_TransW {x : W} (θ : ℝ) (hx : x ∈ TransW) : Phi θ x ∈ TransW := by
  obtain ⟨b, c, rfl⟩ := (mem_TransW_iff x).1 hx
  rw [map_add, map_smul, map_smul, Phi_wB, Phi_wC]
  refine (mem_TransW_iff _).2 ⟨b * Real.cos θ + c * (- Real.sin θ),
    b * Real.sin θ + c * Real.cos θ, ?_⟩
  module

/-- **THE EXACT FIXED SET OF THE WHOLE FAMILY.**  A carrier element is fixed by
every `Φθ` exactly when its four rotating coordinates vanish, i.e. when it lies
in the span of `1, A, R, S`.  In particular, inside the embedded old rest space
the distinguished axis is the *only* fixed direction. -/
theorem Phi_fixed_iff (x : W) :
    (∀ θ : ℝ, Phi θ x = x) ↔ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0 := by
  constructor
  · intro h
    have h2 := congrFun (h (Real.pi / 2)) 2
    have h3 := congrFun (h (Real.pi / 2)) 3
    have h4 := congrFun (h (Real.pi / 2)) 4
    have h5 := congrFun (h (Real.pi / 2)) 5
    rw [Phi_coord_2] at h2
    rw [Phi_coord_3] at h3
    rw [Phi_coord_4] at h4
    rw [Phi_coord_5] at h5
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two] at h2 h3 h4 h5
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h2, h3, h4, h5⟩ θ
    funext i
    fin_cases i <;> simp [h2, h3, h4, h5]

/-- Inside the embedded old rest space the fixed directions are exactly the
longitudinal ones. -/
theorem Phi_fixed_rest_iff {x : W}
    (hx : x ∈ Submodule.span ℝ ({wA, wB, wC} : Set W)) :
    (∀ θ : ℝ, Phi θ x = x) ↔ x ∈ LongW := by
  have hcoord : x 0 = 0 ∧ x 4 = 0 ∧ x 5 = 0 ∧ x 6 = 0 ∧ x 7 = 0 := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
        rcases hy with h | h | h <;> subst h <;>
          exact ⟨by simp [wA, wB, wC], by simp [wA, wB, wC], by simp [wA, wB, wC],
            by simp [wA, wB, wC], by simp [wA, wB, wC]⟩
    | zero => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | add y z _ _ hy hz =>
        exact ⟨by simp [hy.1, hz.1], by simp [hy.2.1, hz.2.1],
          by simp [hy.2.2.1, hz.2.2.1], by simp [hy.2.2.2.1, hz.2.2.2.1],
          by simp [hy.2.2.2.2, hz.2.2.2.2]⟩
    | smul r y _ hy =>
        exact ⟨by simp [hy.1], by simp [hy.2.1], by simp [hy.2.2.1],
          by simp [hy.2.2.2.1], by simp [hy.2.2.2.2]⟩
  rw [Phi_fixed_iff]
  constructor
  · rintro ⟨h2, h3, _, _⟩
    refine (mem_LongW_iff x).2 ⟨x 1, ?_⟩
    funext i
    fin_cases i <;> simp [wA, hcoord.1, h2, h3, hcoord.2.1, hcoord.2.2.1,
      hcoord.2.2.2.1, hcoord.2.2.2.2]
  · intro hL
    obtain ⟨a, rfl⟩ := (mem_LongW_iff x).1 hL
    exact ⟨by simp [wA], by simp [wA], by simp [wA], by simp [wA]⟩

/-- **NO FURTHER INVARIANT REAL SUBSPACE.**  A subspace of the transverse plane
invariant under the whole family is either zero or the entire plane. -/
theorem TransW_irreducible (V : Submodule ℝ W) (hV : V ≤ TransW)
    (hinv : ∀ (θ : ℝ) (x : W), x ∈ V → Phi θ x ∈ V) :
    V = ⊥ ∨ V = TransW := by
  by_cases hzero : ∀ x ∈ V, x = 0
  · left
    refine le_antisymm (fun x hx => ?_) bot_le
    simp only [Submodule.mem_bot]
    exact hzero x hx
  · right
    push_neg at hzero
    obtain ⟨x, hxV, hxne⟩ := hzero
    obtain ⟨b, c, rfl⟩ := (mem_TransW_iff x).1 (hV hxV)
    have hy : Phi (Real.pi / 2) (b • wB + c • wC) = (-c) • wB + b • wC := by
      rw [map_add, map_smul, map_smul, Phi_wB, Phi_wC,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      module
    have hyV : ((-c) • wB + b • wC) ∈ V := by
      rw [← hy]; exact hinv _ _ hxV
    have hbc : b * b + c * c ≠ 0 := by
      intro h
      apply hxne
      have hb : b = 0 := by nlinarith [sq_nonneg b, sq_nonneg c]
      have hc : c = 0 := by nlinarith [sq_nonneg b, sq_nonneg c]
      rw [hb, hc]; simp
    have hB : wB ∈ V := by
      have hcomb : (b * b + c * c) • wB
          = b • (b • wB + c • wC) - c • ((-c) • wB + b • wC) := by module
      have : (b * b + c * c) • wB ∈ V := by
        rw [hcomb]
        exact sub_mem (Submodule.smul_mem _ _ hxV) (Submodule.smul_mem _ _ hyV)
      have := Submodule.smul_mem V (b * b + c * c)⁻¹ this
      rwa [smul_smul, inv_mul_cancel₀ hbc, one_smul] at this
    have hC : wC ∈ V := by
      have hcomb : (b * b + c * c) • wC
          = c • (b • wB + c • wC) + b • ((-c) • wB + b • wC) := by module
      have : (b * b + c * c) • wC ∈ V := by
        rw [hcomb]
        exact add_mem (Submodule.smul_mem _ _ hxV) (Submodule.smul_mem _ _ hyV)
      have := Submodule.smul_mem V (b * b + c * c)⁻¹ this
      rwa [smul_smul, inv_mul_cancel₀ hbc, one_smul] at this
    refine le_antisymm hV ?_
    rw [TransW, Submodule.span_le]
    rintro z (hz | hz) <;> subst hz
    · exact hB
    · exact hC

/-! ## §12 — the `Z`-linear extension of the transverse plane -/

/-- The `Z`-line generated by a carrier element: its real span together with its
`S`-multiple. -/
def Zline (ψ : W) : Submodule ℝ W := Submodule.span ℝ {ψ, wS ⋆ ψ}

theorem mem_Zline_iff (ψ x : W) :
    x ∈ Zline ψ ↔ ∃ a b : ℝ, x = a • ψ + b • (wS ⋆ ψ) := by
  rw [Zline, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩; exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩; exact ⟨a, b, rfl⟩

theorem self_mem_Zline (ψ : W) : ψ ∈ Zline ψ :=
  (mem_Zline_iff ψ ψ).2 ⟨1, 0, by module⟩

/-- The `Z`-linear extension of the transverse plane: the real span of the
transverse generators and of their `S`-multiples. -/
def TransZ : Submodule ℝ W := Submodule.span ℝ {wB, wC, wP, wQ}

theorem mem_TransZ_iff (x : W) :
    x ∈ TransZ ↔ x 0 = 0 ∧ x 1 = 0 ∧ x 6 = 0 ∧ x 7 = 0 := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        rcases hy with h | h | h | h <;> subst h <;>
          exact ⟨by simp [wB, wC, wP, wQ], by simp [wB, wC, wP, wQ],
            by simp [wB, wC, wP, wQ], by simp [wB, wC, wP, wQ]⟩
    | zero => exact ⟨rfl, rfl, rfl, rfl⟩
    | add y z _ _ hy hz =>
        exact ⟨by simp [hy.1, hz.1], by simp [hy.2.1, hz.2.1],
          by simp [hy.2.2.1, hz.2.2.1], by simp [hy.2.2.2, hz.2.2.2]⟩
    | smul r y _ hy =>
        exact ⟨by simp [hy.1], by simp [hy.2.1], by simp [hy.2.2.1],
          by simp [hy.2.2.2]⟩
  · rintro ⟨h0, h1, h6, h7⟩
    have hx : x = x 2 • wB + x 3 • wC + x 4 • wP + x 5 • wQ := by
      funext i
      fin_cases i <;> simp [wB, wC, wP, wQ, h0, h1, h6, h7]
    rw [hx]
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem wB_mem_TransZ : wB ∈ TransZ := Submodule.subset_span (by simp)

/-! ## §13 — transverse `Z`-eigenchannels -/

/-- **A TRANSVERSE `Z`-CHANNEL**: a nonzero element of the `Z`-linear transverse
plane whose transformation under every `Φθ` is multiplication by one central
scalar.  No formula is prescribed. -/
def IsZChannel (ψ : W) : Prop :=
  ψ ≠ 0 ∧ ψ ∈ TransZ ∧ ∀ θ : ℝ, ∃ u v : ℝ, Phi θ ψ = zsc u v ⋆ ψ

/-- The first derived channel generator. -/
def chPlus : W := wB - wP

/-- The second derived channel generator. -/
def chMinus : W := wB + wP

theorem wS_mul_chPlus : wS ⋆ chPlus = wC - wQ := by
  simp only [chPlus, sub_eq_add_neg, mul_add_W, mul_neg_W, wit8_wS_wB, wit8_wS_wP]
  module

theorem wS_mul_chMinus : wS ⋆ chMinus = -(wC + wQ) := by
  simp only [chMinus, mul_add_W, wit8_wS_wB, wit8_wS_wP]
  module

theorem mem_Zline_chPlus_iff (x : W) :
    x ∈ Zline chPlus ↔ ∃ a b : ℝ, x = a • (wB - wP) + b • (wC - wQ) := by
  rw [mem_Zline_iff, wS_mul_chPlus]
  rfl

theorem mem_Zline_chMinus_iff (x : W) :
    x ∈ Zline chMinus ↔ ∃ a b : ℝ, x = a • (wB + wP) + b • (wC + wQ) := by
  rw [mem_Zline_iff, wS_mul_chMinus]
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨a, -b, ?_⟩
    simp only [chMinus]
    module
  · rintro ⟨a, b, rfl⟩
    refine ⟨a, -b, ?_⟩
    simp only [chMinus]
    module

/-- **TRANSFORMATION FACTOR OF THE FIRST CHANNEL.**  Derived, not prescribed. -/
theorem Phi_on_Zline_chPlus {x : W} (θ : ℝ) (hx : x ∈ Zline chPlus) :
    Phi θ x = zsc (Real.cos θ) (Real.sin θ) ⋆ x := by
  obtain ⟨a, b, rfl⟩ := (mem_Zline_chPlus_iff x).1 hx
  rw [zsc_smul]
  simp only [sub_eq_add_neg, map_add, map_smul, map_neg, Phi_wB, Phi_wC,
    Phi_wP, Phi_wQ, wit8_wS_wB, wit8_wS_wC, wit8_wS_wP, wit8_wS_wQ]
  module

/-- **TRANSFORMATION FACTOR OF THE SECOND CHANNEL.** -/
theorem Phi_on_Zline_chMinus {x : W} (θ : ℝ) (hx : x ∈ Zline chMinus) :
    Phi θ x = zsc (Real.cos θ) (- Real.sin θ) ⋆ x := by
  obtain ⟨a, b, rfl⟩ := (mem_Zline_chMinus_iff x).1 hx
  rw [zsc_smul]
  simp only [map_add, map_smul, Phi_wB, Phi_wC, Phi_wP, Phi_wQ,
    wit8_wS_wB, wit8_wS_wC, wit8_wS_wP, wit8_wS_wQ]
  module

/-! ### Coordinates of multiplication by the central element -/

theorem wS_mul_coord_2 (ψ : W) : (wS ⋆ ψ) 2 = ψ 5 := by simp [wS]
theorem wS_mul_coord_3 (ψ : W) : (wS ⋆ ψ) 3 = - ψ 4 := by simp [wS]
theorem wS_mul_coord_4 (ψ : W) : (wS ⋆ ψ) 4 = ψ 3 := by simp [wS]
theorem wS_mul_coord_5 (ψ : W) : (wS ⋆ ψ) 5 = - ψ 2 := by simp [wS]

/-! ### The exact classification of transverse `Z`-channels -/

theorem Zline_chPlus_le_TransZ : Zline chPlus ≤ TransZ := by
  intro x hx
  obtain ⟨a, b, rfl⟩ := (mem_Zline_chPlus_iff x).1 hx
  refine (mem_TransZ_iff _).2 ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [wB, wC, wP, wQ]

theorem Zline_chMinus_le_TransZ : Zline chMinus ≤ TransZ := by
  intro x hx
  obtain ⟨a, b, rfl⟩ := (mem_Zline_chMinus_iff x).1 hx
  refine (mem_TransZ_iff _).2 ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [wB, wC, wP, wQ]

/-- **EXACT CLASSIFICATION (§13).**  The transverse `Z`-channels are precisely
the nonzero elements of the two derived `Z`-lines.  Neither the lines nor the
factors were prescribed: they are forced by the single requirement that the
transformation be multiplication by a central scalar. -/
theorem zChannel_classification (ψ : W) :
    IsZChannel ψ ↔ ψ ≠ 0 ∧ (ψ ∈ Zline chPlus ∨ ψ ∈ Zline chMinus) := by
  constructor
  · rintro ⟨hne, hmem, hfac⟩
    obtain ⟨u, v, huv⟩ := hfac (Real.pi / 2)
    obtain ⟨h0, h1, h6, h7⟩ := (mem_TransZ_iff ψ).1 hmem
    rw [zsc_smul] at huv
    have e2 := congrFun huv 2
    have e3 := congrFun huv 3
    have e4 := congrFun huv 4
    have e5 := congrFun huv 5
    rw [Phi_coord_2, Real.cos_pi_div_two, Real.sin_pi_div_two] at e2
    rw [Phi_coord_3, Real.cos_pi_div_two, Real.sin_pi_div_two] at e3
    rw [Phi_coord_4, Real.cos_pi_div_two, Real.sin_pi_div_two] at e4
    rw [Phi_coord_5, Real.cos_pi_div_two, Real.sin_pi_div_two] at e5
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wS_mul_coord_2,
      wS_mul_coord_3, wS_mul_coord_4, wS_mul_coord_5] at e2 e3 e4 e5
    -- the four forced coordinate equations
    have E2 : - ψ 3 = u * ψ 2 + v * ψ 5 := by linarith
    have E3 : ψ 2 = u * ψ 3 - v * ψ 4 := by linarith
    have E4 : - ψ 5 = u * ψ 4 + v * ψ 3 := by linarith
    have E5 : ψ 4 = u * ψ 5 - v * ψ 2 := by linarith
    have hA : ψ 2 ^ 2 + ψ 3 ^ 2 + ψ 4 ^ 2 + ψ 5 ^ 2 ≠ 0 := by
      intro hzero
      apply hne
      have c2 : ψ 2 = 0 := by nlinarith [sq_nonneg (ψ 2), sq_nonneg (ψ 3), sq_nonneg (ψ 4), sq_nonneg (ψ 5)]
      have c3 : ψ 3 = 0 := by nlinarith [sq_nonneg (ψ 2), sq_nonneg (ψ 3), sq_nonneg (ψ 4), sq_nonneg (ψ 5)]
      have c4 : ψ 4 = 0 := by nlinarith [sq_nonneg (ψ 2), sq_nonneg (ψ 3), sq_nonneg (ψ 4), sq_nonneg (ψ 5)]
      have c5 : ψ 5 = 0 := by nlinarith [sq_nonneg (ψ 2), sq_nonneg (ψ 3), sq_nonneg (ψ 4), sq_nonneg (ψ 5)]
      funext i
      fin_cases i <;> simp [h0, h1, c2, c3, c4, c5, h6, h7]
    have hu : u = 0 := by
      have hmul : u * (ψ 2 ^ 2 + ψ 3 ^ 2 + ψ 4 ^ 2 + ψ 5 ^ 2) = 0 := by
        linear_combination (-(ψ 2)) * E2 + (-(ψ 3)) * E3 + (-(ψ 4)) * E4 + (-(ψ 5)) * E5
      rcases mul_eq_zero.1 hmul with h | h
      · exact h
      · exact absurd h hA
    subst hu
    -- with the real part gone the sign is forced
    have F2 : - ψ 3 = v * ψ 5 := by linarith [E2]
    have F3 : ψ 2 = - (v * ψ 4) := by linarith [E3]
    have F4 : - ψ 5 = v * ψ 3 := by linarith [E4]
    have F5 : ψ 4 = - (v * ψ 2) := by linarith [E5]
    have hv2 : (v ^ 2 - 1) * ψ 3 = 0 := by linear_combination F2 + (-v) * F4
    have hv3 : (v ^ 2 - 1) * ψ 2 = 0 := by linear_combination (-1 : ℝ) * F3 + v * F5
    by_cases hv : v ^ 2 = 1
    · have hvpm : v = 1 ∨ v = -1 := by
        have hfac : (v - 1) * (v + 1) = 0 := by linear_combination hv
        rcases mul_eq_zero.1 hfac with h | h
        · left; linarith
        · right; linarith
      refine ⟨hne, ?_⟩
      rcases hvpm with rfl | rfl
      · left
        refine (mem_Zline_chPlus_iff ψ).2 ⟨ψ 2, ψ 3, ?_⟩
        have k4 : ψ 4 = - ψ 2 := by linarith [F5]
        have k5 : ψ 5 = - ψ 3 := by linarith [F2]
        funext i
        fin_cases i <;> simp [wB, wC, wP, wQ, h0, h1, h6, h7, k4, k5]
      · right
        refine (mem_Zline_chMinus_iff ψ).2 ⟨ψ 2, ψ 3, ?_⟩
        have k4 : ψ 4 = ψ 2 := by linarith [F5]
        have k5 : ψ 5 = ψ 3 := by linarith [F2]
        funext i
        fin_cases i <;> simp [wB, wC, wP, wQ, h0, h1, h6, h7, k4, k5]
    · exfalso
      have hne1 : v ^ 2 - 1 ≠ 0 := fun h => hv (by linarith)
      have c3 : ψ 3 = 0 := by
        rcases mul_eq_zero.1 hv2 with h | h
        · exact absurd h hne1
        · exact h
      have c2 : ψ 2 = 0 := by
        rcases mul_eq_zero.1 hv3 with h | h
        · exact absurd h hne1
        · exact h
      have c5 : ψ 5 = 0 := by
        have := F4; rw [c3] at this; linarith
      have c4 : ψ 4 = 0 := by
        have := F5; rw [c2] at this; linarith
      apply hne
      funext i
      fin_cases i <;> simp [h0, h1, c2, c3, c4, c5, h6, h7]
  · rintro ⟨hne, hcase⟩
    rcases hcase with hx | hx
    · exact ⟨hne, Zline_chPlus_le_TransZ hx,
        fun θ => ⟨Real.cos θ, Real.sin θ, Phi_on_Zline_chPlus θ hx⟩⟩
    · exact ⟨hne, Zline_chMinus_le_TransZ hx,
        fun θ => ⟨Real.cos θ, - Real.sin θ, Phi_on_Zline_chMinus θ hx⟩⟩

/-! ## §14 — the longitudinal channel, compared with the transverse ones -/

/-- **THE LONGITUDINAL CHANNEL.**  Its transformation factor is the constant
central unit: the distinguished axis carries the trivial factor. -/
theorem Phi_on_LongW {x : W} (θ : ℝ) (hx : x ∈ LongW) : Phi θ x = zsc 1 0 ⋆ x := by
  rw [Phi_fixes_LongW θ hx, zsc_smul]
  module

/-- The two transverse factors are mutually inverse central scalars. -/
theorem transverse_factors_inverse (θ : ℝ) :
    zsc (Real.cos θ) (Real.sin θ) ⋆ zsc (Real.cos θ) (- Real.sin θ) = zsc 1 0 := by
  rw [zsc_mul_zsc]
  have h1 : Real.cos θ * Real.cos θ - Real.sin θ * -Real.sin θ = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have h2 : Real.cos θ * -Real.sin θ + Real.sin θ * Real.cos θ = 0 := by ring
  rw [h1, h2]

/-- **THE THREE CHANNELS ARE GENUINELY DIFFERENT.**  At a quarter turn the
longitudinal factor is the central unit while the two transverse factors are the
two opposite central square roots of `-1`; in particular no two of the three
coincide. -/
theorem channel_factors_distinct :
    zsc (Real.cos (Real.pi / 2)) (Real.sin (Real.pi / 2)) = zsc 0 1 ∧
    zsc (Real.cos (Real.pi / 2)) (- Real.sin (Real.pi / 2)) = zsc 0 (-1) ∧
    zsc 0 1 ≠ zsc 1 0 ∧ zsc 0 (-1) ≠ zsc 1 0 ∧ zsc 0 1 ≠ zsc 0 (-1) := by
  refine ⟨by rw [Real.cos_pi_div_two, Real.sin_pi_div_two],
    by rw [Real.cos_pi_div_two, Real.sin_pi_div_two],
    ?_, ?_, ?_⟩ <;>
  · intro hcon
    have := congrFun hcon 7
    simp [zsc, w1, wS] at this
    try linarith

/-! ## §4 — both Task-09 central norm branches are preserved -/

theorem nRe_Phi (θ : ℝ) (x : W) : nRe (Phi θ x) = nRe x := by
  simp only [nRe, Phi_coord_0, Phi_coord_1, Phi_coord_2, Phi_coord_3,
    Phi_coord_4, Phi_coord_5, Phi_coord_6, Phi_coord_7]
  linear_combination (- x 2 ^ 2 - x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2) * Real.sin_sq_add_cos_sq θ

theorem nSc_Phi (θ : ℝ) (x : W) : nSc (Phi θ x) = nSc x := by
  simp only [nSc, Phi_coord_0, Phi_coord_1, Phi_coord_2, Phi_coord_3,
    Phi_coord_4, Phi_coord_5, Phi_coord_6, Phi_coord_7]
  linear_combination (2 * (x 2 * x 5 - x 3 * x 4)) * Real.sin_sq_add_cos_sq θ

/-- **NO BRANCH IS PREFERRED AND NO BRANCH IS EXCHANGED.**  Each of the two
Task-09 central-valued quadratic branches is preserved by the whole family
separately. -/
theorem Ncand_Phi (z θ : ℝ) (x : W) : Ncand z (Phi θ x) = Ncand z x := by
  simp only [Ncand, nRe_Phi, nSc_Phi]

theorem both_branches_preserved (θ : ℝ) (x : W) :
    Ncand 1 (Phi θ x) = Ncand 1 x ∧ Ncand (-1) (Phi θ x) = Ncand (-1) x :=
  ⟨Ncand_Phi 1 θ x, Ncand_Phi (-1) θ x⟩

end NullSectorTask10
