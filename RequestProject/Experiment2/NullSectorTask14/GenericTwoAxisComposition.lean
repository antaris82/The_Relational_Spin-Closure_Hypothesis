import RequestProject.Experiment2.NullSectorTask14.GenericAxis

/-!
# Task 14, Layer 13 (§40–§43): two arbitrary nonparallel axes and the closure test

* §40 — the mixed slice intersections for two arbitrary unit axes, with the exact
  exceptional condition;
* §41 — the generic mixed generator products, and the fact that they stay inside the
  minimal implementer algebra;
* §42 — the composition of two arbitrary-axis reference implementations;
* §43 — the closure test: is the product again a single reference implementation of some
  derived spatial transformation, without new noncentral degrees of freedom?
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## §40 — mixed slices for two arbitrary unit axes -/

/-- **DERIVED (§40).**  For unit axes, `h(n,m) = 1` forces `n = m`. -/
theorem eq_of_h3_eq_one {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m)
    (h : h3 n m = 1) : n = m := by
  simp only [IsUnitAxis, h3, dot3_apply] at hn hm h
  have h1 : (n.1 - m.1) ^ 2 + (n.2.1 - m.2.1) ^ 2 + (n.2.2 - m.2.2) ^ 2 = 0 := by
    nlinarith [hn, hm, h]
  have s1 := sq_nonneg (n.1 - m.1)
  have s2 := sq_nonneg (n.2.1 - m.2.1)
  have s3 := sq_nonneg (n.2.2 - m.2.2)
  have e1 : n.1 - m.1 = 0 := by nlinarith [h1, s1, s2, s3]
  have e2 : n.2.1 - m.2.1 = 0 := by nlinarith [h1, s1, s2, s3]
  have e3 : n.2.2 - m.2.2 = 0 := by nlinarith [h1, s1, s2, s3]
  simp only [Prod.ext_iff]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **DERIVED (§40).**  For unit axes, `h(n,m) = -1` forces `n = -m`. -/
theorem eq_neg_of_h3_eq_neg_one {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m)
    (h : h3 n m = -1) : n = -m := by
  simp only [IsUnitAxis, h3, dot3_apply] at hn hm h
  have s1 := sq_nonneg (n.1 + m.1)
  have s2 := sq_nonneg (n.2.1 + m.2.1)
  have s3 := sq_nonneg (n.2.2 + m.2.2)
  have h1 : (n.1 + m.1) ^ 2 + (n.2.1 + m.2.1) ^ 2 + (n.2.2 + m.2.2) ^ 2 = 0 := by
    nlinarith [hn, hm, h]
  have e1 : n.1 + m.1 = 0 := by nlinarith [h1, s1, s2, s3]
  have e2 : n.2.1 + m.2.1 = 0 := by nlinarith [h1, s1, s2, s3]
  have e3 : n.2.2 + m.2.2 = 0 := by nlinarith [h1, s1, s2, s3]
  simp only [Prod.ext_iff, Prod.neg_mk, Prod.fst_neg, Prod.snd_neg]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **PRINCIPAL THEOREM (§40): `generic_two_axis_slice_intersections`.**  For two unit
axes and an arbitrary left carrier, a nonzero simultaneous eigenvector forces
`h(n,m) = σ τ`, hence `n = ±m`.  For nonparallel axes all four mixed intersections
therefore vanish. -/
theorem generic_mixed_intersection_zero {n m : Vec3} (hn : IsUnitAxis n)
    (hm : IsUnitAxis m) (hne : n ≠ m) (hne' : n ≠ -m) (L : Submodule ℝ W)
    (σ τ : ℝ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) {ψ : W} (hψ : ψ ∈ L)
    (hn' : spat n ⋆ ψ = σ • ψ) (hm' : spat m ⋆ ψ = τ • ψ) : ψ = 0 := by
  have hanti := spat_anticomm n m
  have happ : (spat n ⋆ spat m + spat m ⋆ spat n) ⋆ ψ = ((2 * h3 n m) • w1) ⋆ ψ := by
    rw [hanti]
  rw [add_mul_W, mul_assoc_W, mul_assoc_W, hn', hm', mul_smul_W, mul_smul_W, hn', hm',
    smul_mul_W, one_mul_W] at happ
  have e : (τ * σ) • ψ + (σ * τ) • ψ = (2 * h3 n m) • ψ := by
    simpa [smul_smul] using happ
  have hkey : ((2 : ℝ) * σ * τ - 2 * h3 n m) • ψ = 0 := by
    rw [sub_smul, show ((2 : ℝ) * σ * τ) • ψ = (τ * σ) • ψ + (σ * τ) • ψ by
      rw [← add_smul]; congr 1; ring, e, sub_self]
  rcases smul_eq_zero.1 hkey with hzero | hzero
  · exfalso
    have hh : h3 n m = σ * τ := by linarith [hzero]
    rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;>
      simp only [one_mul, mul_one, neg_mul, mul_neg, neg_neg] at hh
    · exact hne (eq_of_h3_eq_one hn hm hh)
    · exact hne' (eq_neg_of_h3_eq_neg_one hn hm hh)
    · exact hne' (eq_neg_of_h3_eq_neg_one hn hm hh)
    · exact hne (eq_of_h3_eq_one hn hm hh)
  · exact hzero

/-! ## §41 — generic mixed generator products -/

theorem Jmap_mem_ImplAlg (n : Vec3) : Jmap n ∈ ImplAlg :=
  ⟨by simp, by simp, by simp, by simp⟩

/-- **PRINCIPAL THEOREM (§41): `generic_mixed_generator_products`.**  The products of two
generic generator directions decompose into the inherited spatial form and the emergent
bilinear spatial operation, and stay inside the minimal implementer algebra found in
§26. -/
theorem generic_generator_products (n m : Vec3) :
    Jmap n ⋆ Jmap m = (-(h3 n m)) • w1 + (-1 : ℝ) • Jmap (spCross n m) ∧
    Jmap n ⋆ Jmap m + Jmap m ⋆ Jmap n = (-(2 * h3 n m)) • w1 ∧
    Jmap n ⋆ Jmap m - Jmap m ⋆ Jmap n = (-2 : ℝ) • Jmap (spCross n m) ∧
    Jmap n ⋆ Jmap m ∈ ImplAlg :=
  ⟨Jmap_mul n m, Jmap_symmetric_product n m, Jmap_antisymmetric_product n m,
    ImplAlg_productClosed _ (Jmap_mem_ImplAlg n) _ (Jmap_mem_ImplAlg m)⟩

/-! ## The inherited quadratic datum of the implementer algebra -/

/-- **NEUTRAL DEFINITION.**  The sum of squares of the four occupied coordinates of an
element of the minimal implementer algebra.  No metric interpretation is attached. -/
def qnrm (x : W) : ℝ := x 0 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2

theorem qnrm_qelt (a b c d : ℝ) : qnrm (qelt a b c d) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  simp [qnrm]

/-- **DERIVED.**  The quadratic datum is multiplicative on the minimal implementer
algebra. -/
theorem qnrm_mul {x y : W} (hx : x ∈ ImplAlg) (hy : y ∈ ImplAlg) :
    qnrm (x ⋆ y) = qnrm x * qnrm y := by
  obtain ⟨a, b, c, d, rfl⟩ := (mem_ImplAlg_iff x).1 hx
  obtain ⟨a', b', c', d', rfl⟩ := (mem_ImplAlg_iff y).1 hy
  rw [qelt_mul, qnrm_qelt, qnrm_qelt, qnrm_qelt]
  ring

theorem Un_mem_ImplAlg (n : Vec3) (θ : ℝ) : Un n θ ∈ ImplAlg := by
  rw [Un]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ⟨rfl, rfl, rfl, rfl⟩)
    (Submodule.smul_mem _ _ (Jmap_mem_ImplAlg n))

theorem Un_qelt (n : Vec3) (θ : ℝ) :
    Un n θ = qelt (Real.cos (θ / 2)) (-(Real.sin (θ / 2) * n.2.2))
      (Real.sin (θ / 2) * n.2.1) (-(Real.sin (θ / 2) * n.1)) := by
  funext i
  fin_cases i <;> simp [Un, qelt, Jmap, w1, wP, wQ, wR] <;> ring

theorem qnrm_Un {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) : qnrm (Un n θ) = 1 := by
  have hsum : n.1 ^ 2 + n.2.1 ^ 2 + n.2.2 ^ 2 = 1 := by
    simp only [IsUnitAxis, h3, dot3_apply] at hn
    nlinarith [hn]
  have hpy := Real.sin_sq_add_cos_sq (θ / 2)
  rw [Un_qelt, qnrm_qelt]
  nlinarith [hsum, hpy]

/-! ## §43 — the closure theorem -/

/-- **PRINCIPAL THEOREM (§43): every unit element of the minimal implementer algebra *is* a
reference implementation.**  No extra noncentral degree of freedom occurs. -/
theorem exists_axis_repr {z : W} (hz : z ∈ ImplAlg) (hnorm : qnrm z = 1) :
    ∃ (k : Vec3) (ψ : ℝ), IsUnitAxis k ∧ z = Un k ψ := by
  obtain ⟨a, b, c, d, rfl⟩ := (mem_ImplAlg_iff z).1 hz
  rw [qnrm_qelt] at hnorm
  by_cases hr : b ^ 2 + c ^ 2 + d ^ 2 = 0
  · have hb : b = 0 := by nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hc : c = 0 := by nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hd : d = 0 := by nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have ha : a = 1 ∨ a = -1 := by
      have : a ^ 2 = 1 := by rw [hb, hc, hd] at hnorm; linarith
      have h2 : (a - 1) * (a + 1) = 0 := by nlinarith [this]
      rcases mul_eq_zero.1 h2 with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases ha with rfl | rfl
    · refine ⟨(1, 0, 0), 0, by simp [IsUnitAxis, h3], ?_⟩
      rw [Un_zero, hb, hc, hd]
      funext i; fin_cases i <;> simp [qelt, w1, wP, wQ, wR]
    · refine ⟨(1, 0, 0), 2 * Real.pi, by simp [IsUnitAxis, h3], ?_⟩
      rw [hb, hc, hd, Un, show 2 * Real.pi / 2 = Real.pi by ring, Real.cos_pi,
        Real.sin_pi]
      funext i; fin_cases i <;> simp [qelt, Jmap, w1, wP, wQ, wR]
  · have hrpos : 0 < b ^ 2 + c ^ 2 + d ^ 2 := by
      rcases lt_trichotomy (b ^ 2 + c ^ 2 + d ^ 2) 0 with h | h | h
      · nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
      · exact absurd h hr
      · exact h
    set r : ℝ := Real.sqrt (b ^ 2 + c ^ 2 + d ^ 2) with hrdef
    have hrp : 0 < r := Real.sqrt_pos.2 hrpos
    have hrsq : r ^ 2 = b ^ 2 + c ^ 2 + d ^ 2 := Real.sq_sqrt (le_of_lt hrpos)
    have hane : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hle : -1 ≤ a ∧ a ≤ 1 := by
      constructor <;> nlinarith [hane]
    refine ⟨(d / r, -(c / r), b / r), -2 * Real.arccos a, ?_, ?_⟩
    · simp only [IsUnitAxis, h3, dot3_apply]
      field_simp
      nlinarith [hrsq]
    · have hhalf : (-2 * Real.arccos a) / 2 = -Real.arccos a := by ring
      have hcos : Real.cos ((-2 * Real.arccos a) / 2) = a := by
        rw [hhalf, Real.cos_neg, Real.cos_arccos hle.1 hle.2]
      have hsin : Real.sin ((-2 * Real.arccos a) / 2) = -r := by
        rw [hhalf, Real.sin_neg, Real.sin_arccos]
        congr 1
        rw [hrdef]
        congr 1
        nlinarith [hnorm]
      rw [Un, hcos, hsin]
      funext i
      fin_cases i <;>
        simp [qelt, Jmap, w1, wP, wQ, wR] <;> field_simp
  
/-- **PRINCIPAL THEOREM (§42, §43): `generic_reference_composition_closes`.**  The product
of two arbitrary-axis reference implementations is again a reference implementation, of a
single derived axis and parameter.  Verdict: **CLOSED** — no extra noncentral degree of
freedom is needed. -/
theorem generic_reference_composition_closes {n m : Vec3} (hn : IsUnitAxis n)
    (hm : IsUnitAxis m) (θ φ : ℝ) :
    ∃ (k : Vec3) (ψ : ℝ), IsUnitAxis k ∧ Un n θ ⋆ Un m φ = Un k ψ := by
  refine exists_axis_repr (ImplAlg_productClosed _ (Un_mem_ImplAlg n θ) _
    (Un_mem_ImplAlg m φ)) ?_
  rw [qnrm_mul (Un_mem_ImplAlg n θ) (Un_mem_ImplAlg m φ), qnrm_Un hn, qnrm_Un hm]
  norm_num

/-- **DERIVED (§42).**  The explicit shape of the mixed product: a real multiple of the
unit plus a derived generator direction, with the coefficients expressed through the
inherited spatial form and the emergent bilinear operation only. -/
theorem generic_reference_product_shape (n m : Vec3) (θ φ : ℝ) :
    Un n θ ⋆ Un m φ
      = (Real.cos (θ / 2) * Real.cos (φ / 2)
          - Real.sin (θ / 2) * Real.sin (φ / 2) * h3 n m) • w1
        - Jmap ((Real.cos (θ / 2) * Real.sin (φ / 2)) • m
            + (Real.sin (θ / 2) * Real.cos (φ / 2)) • n
            + (Real.sin (θ / 2) * Real.sin (φ / 2)) • spCross n m) := by
  funext i
  fin_cases i <;>
    simp [Un, Jmap, spCross, h3, w1, wP, wQ, wR, wit8MulFun] <;> ring

end NullSectorTask14
