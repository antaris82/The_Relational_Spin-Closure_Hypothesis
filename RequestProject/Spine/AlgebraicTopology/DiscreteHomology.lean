import RequestProject.Spine.AlgebraicTopology.SingularHZero

/-!
# Task 19, WP2 : singular homology of a totally disconnected space, and of two points

For a totally disconnected space every singular simplex is constant, so the singular chain
complex collapses: in each degree it is the free `ℤ₂`-module on the points, and the boundary
`C_{q+1} → C_q` is multiplication by `q mod 2`.  Consequently

* `SpineTask19.isZero_homology_td` — `H_q(X;ℤ₂) = 0` for `q > 0`;
* `SpineTask19.hcls_zero_eq_zero` — in degree `0` the class map is injective;
* `SpineTask19.h0TwoEquiv` — for a two-point space, `H₀(X;ℤ₂) ≅ ℤ₂ ⊕ ℤ₂`, with the two point
  classes as a basis (`h0_two_spanning`, `h0_two_indep`).

This is the low-degree input needed by the `r = 1` standard cell pair and by the base of the
sphere induction (`|∂Δ[1]| ≃ₜ Fin 2 = S⁰`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial NerveGeom SpineTask18

universe u

namespace SpineTask19

variable {X : TopCat.{u}}

/-- The value of a singular simplex at the first vertex. -/
def valN {n : ℕ} (σ : Sing X n) : X := sMap σ (stdSimplex.vertex 0)

@[simp] theorem valN_constSimp {n : ℕ} (x : X) : valN (constSimp x n) = x := by
  rw [valN, constSimp, sMap_sOf]
  rfl

theorem constSimp_injective {n : ℕ} : Function.Injective (fun x : X => constSimp x n) :=
  fun x y h => by
    have hh := congrArg (valN (X := X) (n := n)) h
    rwa [valN_constSimp, valN_constSimp] at hh

instance preconnectedSpace_Δs (n : ℕ) : PreconnectedSpace (Δs n) :=
  Subtype.preconnectedSpace (convex_stdSimplex ℝ (Fin (n + 1))).isPreconnected

/-- Reindexing a chain of constant simplices into another degree. -/
def shiftC (n m : ℕ) :
    SSetChain (TopCat.toSSet.obj X) n →ₗ[ZMod 2] SSetChain (TopCat.toSSet.obj X) m :=
  Finsupp.lmapDomain _ _ (fun σ => constSimp (valN σ) m)

@[simp] theorem shiftC_single {n m : ℕ} (σ : Sing X n) (a : ZMod 2) :
    shiftC n m (Finsupp.single σ a) = Finsupp.single (constSimp (valN σ) m) a :=
  Finsupp.mapDomain_single

section TD

variable [TotallyDisconnectedSpace ↥X]

theorem sing_eq_constSimp {n : ℕ} (σ : Sing X n) : σ = constSimp (valN σ) n := by
  have hsub : (Set.range (sMap σ)).Subsingleton :=
    IsPreconnected.subsingleton (isPreconnected_range (sMap σ).continuous)
  refine Eq.trans (sOf_sMap σ).symm (congrArg sOf (ContinuousMap.ext fun x => ?_))
  exact hsub ⟨x, rfl⟩ ⟨stdSimplex.vertex 0, rfl⟩

theorem shiftC_injective (n m : ℕ) : Function.Injective (shiftC (X := X) n m) := by
  refine Finsupp.mapDomain_injective (fun σ τ h => ?_)
  have hv : valN σ = valN τ := constSimp_injective h
  rw [sing_eq_constSimp σ, sing_eq_constSimp τ, hv]

theorem singBd_shiftC (q : ℕ) (z : SSetChain (TopCat.toSSet.obj X) q) :
    singBd X q (shiftC q (q + 1) z) = (q : ZMod 2) • z := by
  induction z using lchain_induction with
  | h0 => simp
  | hadd f g hf hg => rw [map_add, map_add, hf, hg, smul_add]
  | hsingle σ =>
    rw [shiftC_single, singBd_constSimp, mul_one, Finsupp.smul_single, smul_eq_mul, mul_one]
    conv_rhs => rw [sing_eq_constSimp σ]

theorem singBd_eq_shiftC (q : ℕ) (z : SSetChain (TopCat.toSSet.obj X) (q + 1)) :
    singBd X q z = (q : ZMod 2) • shiftC (q + 1) q z := by
  induction z using lchain_induction with
  | h0 => simp
  | hadd f g hf hg => rw [map_add, map_add, hf, hg, smul_add]
  | hsingle σ =>
    conv_lhs => rw [sing_eq_constSimp σ]
    rw [singBd_constSimp, mul_one, shiftC_single, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem singBd_zero_eq_zero (z : SSetChain (TopCat.toSSet.obj X) 1) : singBd X 0 z = 0 := by
  rw [singBd_eq_shiftC 0 z]
  simp

/-- **In degree `0` there are no boundaries**, so the class map is injective. -/
theorem hcls_zero_eq_zero (z : SSetChain (TopCat.toSSet.obj X) 0)
    (h : hcls (K := singCx X) z (mem_Zc_zero z) = 0) : z = 0 := by
  rw [hcls_sing_eq_zero_iff] at h
  obtain ⟨w, hw⟩ := h
  rw [← hw, singBd_zero_eq_zero]

/-- **WP2.**  A totally disconnected space has vanishing singular homology in positive
degrees. -/
theorem isZero_homology_td (q : ℕ) : IsZero ((singCx X).homology (q + 1)) := by
  refine ModuleCat.isZero_iff_subsingleton.2 (subsingleton_of_forall_eq 0 fun t => ?_)
  obtain ⟨z, hz, rfl⟩ := hcls_surjective t
  rcases Nat.even_or_odd q with hq | hq
  · -- `q` even, so `q + 1` is odd: every cycle is a boundary
    have hone : ((q + 1 : ℕ) : ZMod 2) = 1 := by
      obtain ⟨k, rfl⟩ := hq
      push_cast
      rw [mod2_add_self, zero_add]
    rw [hcls_sing_eq_zero_iff]
    refine ⟨shiftC (q + 1) (q + 2) z, ?_⟩
    rw [singBd_shiftC (q + 1) z, hone, one_smul]
  · -- `q` odd, so the differential out of degree `q + 1` is injective
    have hone : ((q : ℕ) : ZMod 2) = 1 := by
      obtain ⟨k, rfl⟩ := hq
      push_cast
      rw [show (2 : ZMod 2) = 0 from by decide, zero_mul, zero_add]
    have hzz : singBd X q z = 0 := mem_Zc_sing.1 hz
    rw [singBd_eq_shiftC q z, hone, one_smul] at hzz
    have hz0 : z = 0 := shiftC_injective (q + 1) q (by rw [hzz, map_zero])
    have h0mem : (0 : (singCx X).X (q + 1)) ∈ Zc (singCx X) (q + 1) := by
      rw [← hz0]; exact hz
    exact (hcls_congr hz h0mem hz0).trans (hcls_zero h0mem)

end TD

/-! ## Two points -/

section TwoPoint

variable [TotallyDisconnectedSpace ↥X] (p₀ p₁ : X)

theorem chain_zero_eq_two (hne : p₀ ≠ p₁) (hall : ∀ x : X, x = p₀ ∨ x = p₁)
    (z : SSetChain (TopCat.toSSet.obj X) 0) :
    z = Finsupp.single (constSimp p₀ 0) (z (constSimp p₀ 0))
      + Finsupp.single (constSimp p₁ 0) (z (constSimp p₁ 0)) := by
  classical
  refine Finsupp.ext fun σ => ?_
  have hσ := sing_eq_constSimp σ
  rcases hall (valN σ) with h | h
  · have hs : σ = constSimp p₀ 0 := by rw [hσ, h]
    subst hs
    have hne' : constSimp p₀ 0 ≠ constSimp p₁ 0 := fun hc => hne (constSimp_injective hc)
    rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne', add_zero]
  · have hs : σ = constSimp p₁ 0 := by rw [hσ, h]
    subst hs
    have hne' : constSimp p₁ 0 ≠ constSimp p₀ 0 := fun hc => hne (constSimp_injective hc).symm
    rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne', zero_add]

theorem h0_two_spanning (hne : p₀ ≠ p₁) (hall : ∀ x : X, x = p₀ ∨ x = p₁)
    (t : (singCx X).homology 0) :
    ∃ a b : ZMod 2, t = a • ptCls X p₀ + b • ptCls X p₁ := by
  obtain ⟨z, hz, rfl⟩ := hcls_surjective t
  obtain ⟨a, b, hzz⟩ : ∃ a b : ZMod 2, (z : SSetChain (TopCat.toSSet.obj X) 0)
      = Finsupp.single (constSimp p₀ 0) a + Finsupp.single (constSimp p₁ 0) b :=
    ⟨_, _, chain_zero_eq_two p₀ p₁ hne hall z⟩
  refine ⟨a, b, ?_⟩
  rw [ptCls, ptCls, ← hcls_smul, ← hcls_smul, ← hcls_add]
  refine hcls_congr _ _ ?_
  rw [Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  exact hzz

theorem h0_two_indep (hne : p₀ ≠ p₁) (a b : ZMod 2)
    (h : a • ptCls X p₀ + b • ptCls X p₁ = 0) : a = 0 ∧ b = 0 := by
  have hne' : constSimp p₀ 0 ≠ constSimp p₁ 0 := fun hc => hne (constSimp_injective hc)
  rw [ptCls, ptCls, ← hcls_smul, ← hcls_smul, ← hcls_add] at h
  have hz := hcls_zero_eq_zero _ h
  rw [Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at hz
  have hz' : (Finsupp.single (constSimp p₀ 0) a + Finsupp.single (constSimp p₁ 0) b
      : SSetChain (TopCat.toSSet.obj X) 0) = 0 := hz
  constructor
  · have h1 := congrArg (fun c : SSetChain (TopCat.toSSet.obj X) 0 => c (constSimp p₀ 0)) hz'
    simpa [Finsupp.single_eq_of_ne hne'] using h1
  · have h2 := congrArg (fun c : SSetChain (TopCat.toSSet.obj X) 0 => c (constSimp p₁ 0)) hz'
    simpa [Finsupp.single_eq_of_ne (Ne.symm hne')] using h2

/-- The linear map `ℤ₂ ⊕ ℤ₂ → H₀(X)` given by the two point classes. -/
def twoPointMap : (ZMod 2 × ZMod 2) →ₗ[ZMod 2] (singCx X).homology 0 where
  toFun ab := ab.1 • ptCls X p₀ + ab.2 • ptCls X p₁
  map_add' u v := by
    show (u.1 + v.1) • _ + (u.2 + v.2) • _ = _
    rw [add_smul, add_smul]
    abel
  map_smul' c u := by
    show (c * u.1) • _ + (c * u.2) • _ = c • (u.1 • _ + u.2 • _)
    rw [smul_add, mul_smul, mul_smul]

theorem twoPointMap_bijective (hne : p₀ ≠ p₁) (hall : ∀ x : X, x = p₀ ∨ x = p₁) :
    Function.Bijective (twoPointMap p₀ p₁) := by
  constructor
  · intro u v huv
    have hd : (u.1 - v.1) • ptCls X p₀ + (u.2 - v.2) • ptCls X p₁ = 0 := by
      have hh : u.1 • ptCls X p₀ + u.2 • ptCls X p₁
          = v.1 • ptCls X p₀ + v.2 • ptCls X p₁ := huv
      rw [sub_smul, sub_smul,
        show u.1 • ptCls X p₀ - v.1 • ptCls X p₀ + (u.2 • ptCls X p₁ - v.2 • ptCls X p₁)
          = (u.1 • ptCls X p₀ + u.2 • ptCls X p₁) - (v.1 • ptCls X p₀ + v.2 • ptCls X p₁) from by
            abel, hh, sub_self]
    obtain ⟨h1, h2⟩ := h0_two_indep p₀ p₁ hne _ _ hd
    exact Prod.ext (sub_eq_zero.1 h1) (sub_eq_zero.1 h2)
  · intro t
    obtain ⟨a, b, hab⟩ := h0_two_spanning p₀ p₁ hne hall t
    exact ⟨(a, b), hab.symm⟩

/-- **WP2.**  `H₀(X;ℤ₂) ≅ ℤ₂ ⊕ ℤ₂` for a two-point (totally disconnected) space. -/
def h0TwoEquiv (hne : p₀ ≠ p₁) (hall : ∀ x : X, x = p₀ ∨ x = p₁) :
    (singCx X).homology 0 ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
  (LinearEquiv.ofBijective (twoPointMap p₀ p₁) (twoPointMap_bijective p₀ p₁ hne hall)).symm

end TwoPoint

end SpineTask19
