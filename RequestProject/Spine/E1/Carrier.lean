import Mathlib

/-!
# Spine / E1 : the intrinsic real spin-factor carrier `𝒮 = ℝ ⊕ ℝ³`

This is the root module of the intrinsic Lorentz/Clifford/Spin core.  It defines the real
rank-three spin factor **without any reference to `ℂ`, to Hermitian matrices, to
determinants or to Lorentz geometry**:

* carrier `SpinCore.LorentzCarrier := ℝ × (Fin 3 → ℝ)`;
* Euclidean inner product `sip u v = u₀v₀ + u₁v₁ + u₂v₂`;
* Jordan product `(a,u) ∘ (b,v) = (ab + ⟪u,v⟫, a•v + b•u)`;
* unit `1 = (1,0)`;
* the intrinsic trace `strS`, the intrinsic Lorentz quadratic form `NS`, its polarization
  `BS`, and the square cone `ConeS`;
* the purely real coordinate equivalence `spinToVec : 𝒮 ≃ₗ[ℝ] (Fin 4 → ℝ)`;
* the Jordan centroid computation (`centroid_eq_scalars`,
  `no_complex_structure_in_centroid`).

`sJ_jordan` proves that `(𝒮, ∘, 1)` is a real unital commutative Jordan algebra.

**Import firewall.**  This module imports `Mathlib` only.  The historical Hermitian
comparison layer (`Herm₂(ℂ)`, the Jordan-cone automorphism group, the frozen Task-8/Task-9
chain) is *not* in the transitive closure of this module; the comparison with that layer
lives in the comparison endpoint `RequestProject.Comparison.E1Hermitian`, which imports
this module and not conversely.

**Provenance.**  Upstream experiment 1, module `Task9SpinFactor` (intrinsic sections C1,
C3, the real coordinate equivalence, and Part D).  The Hermitian comparison sections C2/C4
of that module were split off into the comparison endpoint.
-/
noncomputable section

open Matrix

namespace SpinCore

/-! ## The real spin factor (no `ℂ`, no matrices, no Lorentz data) -/

/-- The real spin factor carrier `𝒮 = ℝ ⊕ ℝ³`. -/
abbrev LorentzCarrier : Type := ℝ × (Fin 3 → ℝ)

/-- The standard Euclidean inner product on `V = ℝ³`. -/
def sip (u v : Fin 3 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

theorem sip_comm (u v : Fin 3 → ℝ) : sip u v = sip v u := by unfold sip; ring

theorem sip_add_left (u v w : Fin 3 → ℝ) : sip (u + v) w = sip u w + sip v w := by
  unfold sip; simp [Pi.add_apply]; ring

theorem sip_smul_left (r : ℝ) (u v : Fin 3 → ℝ) : sip (r • u) v = r * sip u v := by
  unfold sip; simp [Pi.smul_apply]; ring

theorem sip_self_nonneg (u : Fin 3 → ℝ) : 0 ≤ sip u u := by
  unfold sip; nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]

theorem sip_self_eq_zero {u : Fin 3 → ℝ} (h : sip u u = 0) : u = 0 := by
  simp only [sip] at h
  have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
  have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
  have h2 : u 2 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
  funext i
  fin_cases i <;> simpa using by first | exact h0 | exact h1 | exact h2

/-- **C1 (definition).**  The spin-factor Jordan product. -/
def sJ (x y : LorentzCarrier) : LorentzCarrier :=
  (x.1 * y.1 + sip x.2 y.2, x.1 • y.2 + y.1 • x.2)

/-- The spin-factor unit. -/
def sOne : LorentzCarrier := (1, 0)

@[simp] theorem sJ_fst (x y : LorentzCarrier) : (sJ x y).1 = x.1 * y.1 + sip x.2 y.2 := rfl
@[simp] theorem sJ_snd (x y : LorentzCarrier) : (sJ x y).2 = x.1 • y.2 + y.1 • x.2 := rfl

/-- **C1.1 (commutativity).** -/
theorem sJ_comm (x y : LorentzCarrier) : sJ x y = sJ y x := by
  apply Prod.ext
  · show x.1 * y.1 + sip x.2 y.2 = y.1 * x.1 + sip y.2 x.2
    rw [sip_comm]; ring
  · show x.1 • y.2 + y.1 • x.2 = y.1 • x.2 + x.1 • y.2
    abel

/-- **C1.2 (unit).** -/
@[simp] theorem sJ_one_left (x : LorentzCarrier) : sJ sOne x = x := by
  apply Prod.ext
  · show 1 * x.1 + sip 0 x.2 = x.1
    unfold sip; simp
  · show (1 : ℝ) • x.2 + x.1 • (0 : Fin 3 → ℝ) = x.2
    simp

@[simp] theorem sJ_one_right (x : LorentzCarrier) : sJ x sOne = x := by
  rw [sJ_comm, sJ_one_left]

/-- **C1.3 (bilinearity, left).** -/
theorem sJ_add_left (x y z : LorentzCarrier) : sJ (x + y) z = sJ x z + sJ y z := by
  apply Prod.ext
  · show (x.1 + y.1) * z.1 + sip (x.2 + y.2) z.2
      = (x.1 * z.1 + sip x.2 z.2) + (y.1 * z.1 + sip y.2 z.2)
    rw [sip_add_left]; ring
  · show (x.1 + y.1) • z.2 + z.1 • (x.2 + y.2)
      = (x.1 • z.2 + z.1 • x.2) + (y.1 • z.2 + z.1 • y.2)
    rw [add_smul, smul_add]; abel

theorem sJ_smul_left (r : ℝ) (x y : LorentzCarrier) : sJ (r • x) y = r • sJ x y := by
  apply Prod.ext
  · show (r * x.1) * y.1 + sip (r • x.2) y.2 = r * (x.1 * y.1 + sip x.2 y.2)
    rw [sip_smul_left]; ring
  · show (r * x.1) • y.2 + y.1 • (r • x.2) = r • (x.1 • y.2 + y.1 • x.2)
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- **C1 (Jordan identity).**  `(x ∘ y) ∘ (x ∘ x) = x ∘ (y ∘ (x ∘ x))`. -/
theorem sJ_jordan (x y : LorentzCarrier) : sJ (sJ x y) (sJ x x) = sJ x (sJ y (sJ x x)) := by
  obtain ⟨a, u⟩ := x
  obtain ⟨b, v⟩ := y
  apply Prod.ext
  · show (a * b + sip u v) * (a * a + sip u u) + sip (a • v + b • u) (a • u + a • u)
      = a * (b * (a * a + sip u u) + sip v (a • u + a • u))
        + sip u (b • (a • u + a • u) + (a * a + sip u u) • v)
    simp only [sip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · show (a * b + sip u v) • (a • u + a • u) + (a * a + sip u u) • (a • v + b • u)
      = a • (b • (a • u + a • u) + (a * a + sip u u) • v)
        + (b * (a * a + sip u u) + sip v (a • u + a • u)) • u
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sip, Pi.add_apply]
    ring

/-! ## C3 (intrinsic structures on the spin factor) -/

/-- **C3.** The spin-factor trace. -/
def strS (x : LorentzCarrier) : ℝ := 2 * x.1

/-- **C3.** The spin-factor quadratic norm. -/
def NS (x : LorentzCarrier) : ℝ := x.1 ^ 2 - sip x.2 x.2

/-- **C3.** The polarization of `N_𝒮`. -/
def BS (x y : LorentzCarrier) : ℝ := (NS (x + y) - NS x - NS y) / 2

theorem BS_eq (x y : LorentzCarrier) : BS x y = x.1 * y.1 - sip x.2 y.2 := by
  unfold BS NS sip
  show ((x.1 + y.1) ^ 2 - ((x.2 + y.2) 0 * (x.2 + y.2) 0 + (x.2 + y.2) 1 * (x.2 + y.2) 1
      + (x.2 + y.2) 2 * (x.2 + y.2) 2)
    - (x.1 ^ 2 - (x.2 0 * x.2 0 + x.2 1 * x.2 1 + x.2 2 * x.2 2))
    - (y.1 ^ 2 - (y.2 0 * y.2 0 + y.2 1 * y.2 1 + y.2 2 * y.2 2))) / 2 = _
  simp only [Pi.add_apply]
  ring

/-- **C3.** The intrinsic square cone of the spin factor. -/
def ConeS : Set LorentzCarrier := {x : LorentzCarrier | ∃ y : LorentzCarrier, x = sJ y y}

/-- The Cayley–Hamilton identity on the spin factor, in intrinsic form. -/
theorem sJ_cayleyHamilton (x : LorentzCarrier) :
    sJ x x - strS x • x + NS x • sOne = 0 := by
  apply Prod.ext
  · show (x.1 * x.1 + sip x.2 x.2) - (2 * x.1) * x.1 + (x.1 ^ 2 - sip x.2 x.2) * 1 = 0
    ring
  · show (x.1 • x.2 + x.1 • x.2) - (2 * x.1) • x.2 + (x.1 ^ 2 - sip x.2 x.2) • (0 : Fin 3 → ℝ)
      = 0
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring

/-! ## Real coordinates on the carrier -/

/-- The coordinate equivalence `𝒮 ≃ ℝ⁴` (purely real). -/
def spinToVec : LorentzCarrier ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun x := ![x.1, x.2 0, x.2 1, x.2 2]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' r x := by funext i; fin_cases i <;> simp
  invFun v := (v 0, ![v 1, v 2, v 3])
  left_inv x := by
    apply Prod.ext
    · simp
    · funext i; fin_cases i <;> simp
  right_inv v := by funext i; fin_cases i <;> rfl

@[simp] theorem spinToVec_apply (x : LorentzCarrier) :
    spinToVec x = ![x.1, x.2 0, x.2 1, x.2 2] := rfl

/-! ## Part D : the Jordan centroid of the spin factor -/

/-- **D (definition).** The centroid of the real Jordan algebra `𝒮`. -/
def IsCentroid (T : LorentzCarrier →ₗ[ℝ] LorentzCarrier) : Prop :=
  ∀ x y : LorentzCarrier, T (sJ x y) = sJ (T x) y ∧ T (sJ x y) = sJ x (T y)

/-- Basis vectors of `V = ℝ³`, used for the centroid computation. -/
def evec (i : Fin 3) : Fin 3 → ℝ := fun j => if j = i then 1 else 0

theorem sip_evec (i j : Fin 3) : sip (evec i) (evec j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [sip, evec]

/-- **D1.** The centroid of the real spin factor consists exactly of the real multiples of
the identity. -/
theorem centroid_eq_scalars (T : LorentzCarrier →ₗ[ℝ] LorentzCarrier) (hT : IsCentroid T) :
    ∃ c : ℝ, ∀ x : LorentzCarrier, T x = c • x := by
  -- `T x = T 1 ∘ x` for all `x`
  have hTx : ∀ x : LorentzCarrier, T x = sJ (T sOne) x := by
    intro x
    have h := (hT x sOne).2
    rw [sJ_one_right] at h
    rw [h, sJ_comm]
  set c : LorentzCarrier := T sOne with hc
  -- the vector part of `c` must vanish
  have hvec : ∀ v w : Fin 3 → ℝ,
      sip v w • c.2 = sip c.2 v • w := by
    intro v w
    have h := (hT ((0 : ℝ), v) ((0 : ℝ), w)).1
    rw [hTx, hTx] at h
    have h2 := congrArg Prod.snd h
    simp only [sJ_snd, sJ_fst] at h2
    -- left side: c ∘ (v∘w) has vector part (sip v w) • c.2
    -- right side: (c ∘ v) ∘ w has vector part (sip c.2 v) • w
    simpa using h2
  have hc2 : c.2 = 0 := by
    have h0 := hvec (evec 0) (evec 0)
    have h1 := hvec (evec 1) (evec 1)
    norm_num [sip_evec] at h0 h1
    have hz1 : c.2 1 = 0 := by simpa [evec] using congrFun h0 1
    have hz2 : c.2 2 = 0 := by simpa [evec] using congrFun h0 2
    have hz0 : c.2 0 = 0 := by simpa [evec] using congrFun h1 0
    funext i
    fin_cases i <;> simp [hz0, hz1, hz2]
  refine ⟨c.1, fun x => ?_⟩
  rw [hTx]
  apply Prod.ext
  · show c.1 * x.1 + sip c.2 x.2 = c.1 * x.1
    rw [hc2]
    simp [sip]
  · show c.1 • x.2 + x.1 • c.2 = c.1 • x.2
    rw [hc2]
    simp

/-- **D2.**  There is no complex structure in the centroid: no centroid element squares to
`-id`.  Hence the real Jordan Lorentz carrier contains no internal central complex scalar
operator. -/
theorem no_complex_structure_in_centroid (T : LorentzCarrier →ₗ[ℝ] LorentzCarrier) (hT : IsCentroid T) :
    T ∘ₗ T ≠ -LinearMap.id := by
  intro hsq
  obtain ⟨c, hc⟩ := centroid_eq_scalars T hT
  have h := congrArg (fun (S : LorentzCarrier →ₗ[ℝ] LorentzCarrier) => S sOne) hsq
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply] at h
  rw [hc (T sOne), hc sOne] at h
  have h1 : (c * c) * (sOne : LorentzCarrier).1 = -(sOne : LorentzCarrier).1 := by
    have := congrArg Prod.fst h
    simpa [smul_smul] using this
  simp only [sOne, mul_one] at h1
  nlinarith [sq_nonneg c]

end SpinCore
