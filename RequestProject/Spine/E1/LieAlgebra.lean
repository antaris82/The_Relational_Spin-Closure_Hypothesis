import Mathlib
import RequestProject.Spine.E1.Bivector

/-!
# Task 10, Branch 4 (part 2) : `Λ²𝒮 ≅ 𝔤_B`

Consumed Task 1–9 data: the carrier `𝒮 = SpinCore.LorentzCarrier` and the polarized form `B_𝒮`.
Everything here is intrinsic: no orientation, no cone, no topology, no matrix generators,
no mention of `so(1,3)` (that comparison lives in `Task10LieCompare.lean`).

The proof is a completely explicit "coordinates of a skew endomorphism" argument:
a skew endomorphism `A` is determined by the three numbers `(A 1)₂ j` and the three
numbers `⟨(A (0,eᵢ))₂ , eⱼ⟩` with `i < j`, and every such datum is realised by an
explicit bivector.  Hence `Φ` is onto, `finrank 𝔤_B = 6 = finrank Λ²𝒮`, and `Φ` is
an isomorphism.
-/

noncomputable section

namespace SpinCore

open SpinCore

/-! ## Elementary helpers on the Euclidean part -/

theorem sip_sub_left (u v w : Fin 3 → ℝ) : sip (u - v) w = sip u w - sip v w := by
  simp only [sip, Pi.sub_apply]; ring

theorem sip_evec_right (w : Fin 3 → ℝ) (j : Fin 3) : sip w (evec j) = w j := by
  fin_cases j <;> simp [sip, evec]

theorem vec_ext_evec {w : Fin 3 → ℝ} (h : ∀ j, sip w (evec j) = 0) : w = 0 := by
  funext j
  have := h j
  rw [sip_evec_right] at this
  simpa using this

/-- The three "spatial" basis vectors of the carrier. -/
def bvec (i : Fin 3) : LorentzCarrier := (0, evec i)

@[simp] theorem bvec_fst (i : Fin 3) : (bvec i).1 = 0 := rfl
@[simp] theorem bvec_snd (i : Fin 3) : (bvec i).2 = evec i := rfl

/-- Decomposition of a carrier element along `1` and the three spatial vectors. -/
theorem spin_decomp (x : LorentzCarrier) :
    x = x.1 • sOne + (x.2 0) • bvec 0 + (x.2 1) • bvec 1 + (x.2 2) • bvec 2 := by
  apply Prod.ext
  · simp [sOne, bvec]
  · funext j
    fin_cases j <;> simp [sOne, bvec, evec]

/-! ## Structure of a `B_𝒮`-skew endomorphism -/

/-- The "boost part" of a skew endomorphism. -/
def gvec (A : Module.End ℝ LorentzCarrier) : Fin 3 → ℝ := (A sOne).2

/-- The "rotation coefficients" of a skew endomorphism. -/
def cc (A : Module.End ℝ LorentzCarrier) (i j : Fin 3) : ℝ := sip (A (bvec i)).2 (evec j)

variable {A B : Module.End ℝ LorentzCarrier}

theorem gB_one_fst (hA : A ∈ gB) : (A sOne).1 = 0 := by
  have h := hA sOne sOne
  rw [BS_eq, BS_eq] at h
  have e2 : (sOne : LorentzCarrier).1 = (1 : ℝ) := rfl
  have e3 : (sOne : LorentzCarrier).2 = (0 : Fin 3 → ℝ) := rfl
  rw [e2, e3, sip_zero_left, sip_zero_right] at h
  linarith

theorem gB_vec_fst (hA : A ∈ gB) (u : Fin 3 → ℝ) :
    (A ((0, u) : LorentzCarrier)).1 = sip (gvec A) u := by
  have h := hA sOne ((0, u) : LorentzCarrier)
  rw [BS_eq, BS_eq] at h
  have e1 : (((0 : ℝ), u) : LorentzCarrier).1 = (0 : ℝ) := rfl
  have e1' : (((0 : ℝ), u) : LorentzCarrier).2 = u := rfl
  have e2 : (sOne : LorentzCarrier).1 = (1 : ℝ) := rfl
  have e3 : (sOne : LorentzCarrier).2 = (0 : Fin 3 → ℝ) := rfl
  rw [e1, e1', e2, e3, sip_zero_left] at h
  rw [gvec]
  linarith

theorem gB_anti (hA : A ∈ gB) (u v : Fin 3 → ℝ) :
    sip (A ((0, u) : LorentzCarrier)).2 v = - sip (A ((0, v) : LorentzCarrier)).2 u := by
  have h : (A ((0, u) : LorentzCarrier)).1 * 0 - sip (A ((0, u) : LorentzCarrier)).2 v
      + (0 * (A ((0, v) : LorentzCarrier)).1 - sip u (A ((0, v) : LorentzCarrier)).2) = 0 := by
    have h0 := hA ((0, u) : LorentzCarrier) ((0, v) : LorentzCarrier)
    rw [BS_eq, BS_eq] at h0
    exact h0
  have hs : sip u (A ((0, v) : LorentzCarrier)).2 = sip (A ((0, v) : LorentzCarrier)).2 u := sip_comm _ _
  rw [hs] at h
  linarith

theorem cc_antisymm (hA : A ∈ gB) (i j : Fin 3) : cc A i j = - cc A j i := by
  simpa [cc, bvec] using gB_anti hA (evec i) (evec j)

theorem cc_self (hA : A ∈ gB) (i : Fin 3) : cc A i i = 0 := by
  have := cc_antisymm hA i i
  linarith

/-- **Rigidity.**  A skew endomorphism with vanishing coordinates vanishes. -/
theorem gB_eq_zero (hA : A ∈ gB) (hg : gvec A = 0)
    (h01 : cc A 0 1 = 0) (h02 : cc A 0 2 = 0) (h12 : cc A 1 2 = 0) : A = 0 := by
  have hone : A sOne = 0 := by
    apply Prod.ext
    · simpa using gB_one_fst hA
    · simpa using hg
  have hcc : ∀ i j, cc A i j = 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [cc_self hA, cc_antisymm hA 1 0, cc_antisymm hA 2 0, cc_antisymm hA 2 1]
  have hbv : ∀ k, A (bvec k) = 0 := by
    intro k
    apply Prod.ext
    · have := gB_vec_fst hA (evec k)
      rw [hg] at this
      simpa [bvec, sip_zero_left] using this
    · have : (A (bvec k)).2 = 0 := by
        apply vec_ext_evec
        intro j
        exact hcc k j
      simpa using this
  apply LinearMap.ext
  intro x
  conv_lhs => rw [spin_decomp x]
  simp [map_add, map_smul, hone, hbv]

/-- **Rigidity, comparison form.** -/
theorem gB_ext (hA : A ∈ gB) (hB : B ∈ gB) (hg : gvec A = gvec B)
    (h01 : cc A 0 1 = cc B 0 1) (h02 : cc A 0 2 = cc B 0 2) (h12 : cc A 1 2 = cc B 1 2) :
    A = B := by
  have hsub : A - B ∈ gB := Submodule.sub_mem gB hA hB
  have hgv : gvec (A - B) = 0 := by
    funext j
    have : gvec (A - B) j = gvec A j - gvec B j := rfl
    rw [this, hg]
    simp
  have hcc : ∀ i j, cc (A - B) i j = cc A i j - cc B i j := by
    intro i j
    show sip ((A - B) (bvec i)).2 (evec j) = _
    have : ((A - B) (bvec i)).2 = (A (bvec i)).2 - (B (bvec i)).2 := rfl
    rw [this, sip_sub_left]
    rfl
  have := gB_eq_zero hsub hgv (by rw [hcc, h01]; ring) (by rw [hcc, h02]; ring)
    (by rw [hcc, h12]; ring)
  have h := sub_eq_zero.mp this
  exact h

/-! ## Explicit evaluation of the elementary skew endomorphisms -/

theorem Kend_one_vec (w : Fin 3 → ℝ) (x : LorentzCarrier) :
    Kend sOne ((0, w) : LorentzCarrier) x = (-sip w x.2, -(x.1 • w)) := by
  rw [Kend_apply]
  apply Prod.ext
  · show BS ((0, w) : LorentzCarrier) x * 1 - BS sOne x * 0 = -sip w x.2
    rw [BS_eq, BS_eq]
    show (0 * x.1 - sip w x.2) * 1 - _ = _
    ring
  · show BS ((0, w) : LorentzCarrier) x • (0 : Fin 3 → ℝ) - BS sOne x • w = -(x.1 • w)
    have h : BS sOne x = x.1 := by
      rw [BS_eq]
      show 1 * x.1 - sip 0 x.2 = x.1
      rw [sip_zero_left]; ring
    rw [h]
    simp

theorem Kend_vec_vec (w w' : Fin 3 → ℝ) (x : LorentzCarrier) :
    Kend ((0, w) : LorentzCarrier) ((0, w') : LorentzCarrier) x
      = (0, sip w x.2 • w' - sip w' x.2 • w) := by
  rw [Kend_apply]
  have h1 : BS ((0, w) : LorentzCarrier) x = -sip w x.2 := by
    rw [BS_eq]; show 0 * x.1 - sip w x.2 = _; ring
  have h2 : BS ((0, w') : LorentzCarrier) x = -sip w' x.2 := by
    rw [BS_eq]; show 0 * x.1 - sip w' x.2 = _; ring
  rw [h1, h2]
  apply Prod.ext
  · show -sip w' x.2 * 0 - -sip w x.2 * 0 = 0
    ring
  · show -sip w' x.2 • w - -sip w x.2 • w' = sip w x.2 • w' - sip w' x.2 • w
    module

/-! ## The explicit right inverse -/

/-- The explicit bivector realising a prescribed coordinate datum. -/
def zmap : (Fin 6 → ℝ) →ₗ[ℝ] (⋀[ℝ]^2 LorentzCarrier) :=
  (LinearMap.proj 0).smulRight (-(wedge sOne (bvec 0)))
  + (LinearMap.proj 1).smulRight (-(wedge sOne (bvec 1)))
  + (LinearMap.proj 2).smulRight (-(wedge sOne (bvec 2)))
  + (LinearMap.proj 3).smulRight (wedge (bvec 0) (bvec 1))
  + (LinearMap.proj 4).smulRight (wedge (bvec 0) (bvec 2))
  + (LinearMap.proj 5).smulRight (wedge (bvec 1) (bvec 2))

theorem Phi0_zmap (c : Fin 6 → ℝ) :
    Phi0 (zmap c)
      = c 0 • (-(Kend sOne (bvec 0))) + c 1 • (-(Kend sOne (bvec 1)))
        + c 2 • (-(Kend sOne (bvec 2))) + c 3 • Kend (bvec 0) (bvec 1)
        + c 4 • Kend (bvec 0) (bvec 2) + c 5 • Kend (bvec 1) (bvec 2) := by
  show Phi0 (_ + _ + _ + _ + _ + _) = _
  simp only [LinearMap.smulRight_apply, LinearMap.proj_apply,
    map_add, map_smul, map_neg, Phi0_wedge]

theorem Phi0_zmap_apply (c : Fin 6 → ℝ) (x : LorentzCarrier) :
    Phi0 (zmap c) x
      = c 0 • (-(Kend sOne (bvec 0) x)) + c 1 • (-(Kend sOne (bvec 1) x))
        + c 2 • (-(Kend sOne (bvec 2) x)) + c 3 • Kend (bvec 0) (bvec 1) x
        + c 4 • Kend (bvec 0) (bvec 2) x + c 5 • Kend (bvec 1) (bvec 2) x := by
  rw [Phi0_zmap]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply]

/-- The six coordinates of an endomorphism. -/
def psi (A : Module.End ℝ LorentzCarrier) : Fin 6 → ℝ :=
  ![gvec A 0, gvec A 1, gvec A 2, cc A 0 1, cc A 0 2, cc A 1 2]

/-! ### Explicit values of the elementary skew endomorphisms on the basis -/

theorem Kend_one_bvec_one (i : Fin 3) : Kend sOne (bvec i) sOne = (0, -evec i) := by
  rw [bvec, Kend_one_vec]
  have h1 : (sOne : LorentzCarrier).1 = (1 : ℝ) := rfl
  have h2 : (sOne : LorentzCarrier).2 = (0 : Fin 3 → ℝ) := rfl
  rw [h1, h2, sip_zero_right, one_smul, neg_zero]

theorem Kend_bvec_bvec_one (i j : Fin 3) : Kend (bvec i) (bvec j) sOne = 0 := by
  rw [bvec, bvec, Kend_vec_vec]
  have h2 : (sOne : LorentzCarrier).2 = (0 : Fin 3 → ℝ) := rfl
  rw [h2, sip_zero_right, sip_zero_right, zero_smul, zero_smul, sub_zero]
  rfl

theorem Kend_one_bvec_bvec (i k : Fin 3) :
    Kend sOne (bvec i) (bvec k) = (-(if i = k then (1 : ℝ) else 0), 0) := by
  rw [bvec, Kend_one_vec, bvec_snd, bvec_fst, sip_evec, zero_smul, neg_zero]

theorem Kend_bvec_bvec_bvec (i j k : Fin 3) :
    Kend (bvec i) (bvec j) (bvec k)
      = (0, (if i = k then (1 : ℝ) else 0) • evec j
            - (if j = k then (1 : ℝ) else 0) • evec i) := by
  rw [bvec, bvec, Kend_vec_vec, bvec_snd, sip_evec, sip_evec]

/-! ### The coordinates of `Φ₀ (zmap c)` -/

theorem gvec_zmap (c : Fin 6 → ℝ) (j : Fin 3) :
    gvec (Phi0 (zmap c)) j = ![c 0, c 1, c 2] j := by
  rw [gvec, Phi0_zmap_apply]
  simp only [Kend_one_bvec_one, Kend_bvec_bvec_one]
  fin_cases j <;> simp [evec]

theorem cc_zmap_01 (c : Fin 6 → ℝ) : cc (Phi0 (zmap c)) 0 1 = c 3 := by
  rw [cc, Phi0_zmap_apply]
  simp only [Kend_one_bvec_bvec, Kend_bvec_bvec_bvec]
  simp [sip, evec]

theorem cc_zmap_02 (c : Fin 6 → ℝ) : cc (Phi0 (zmap c)) 0 2 = c 4 := by
  rw [cc, Phi0_zmap_apply]
  simp only [Kend_one_bvec_bvec, Kend_bvec_bvec_bvec]
  simp [sip, evec]

theorem cc_zmap_12 (c : Fin 6 → ℝ) : cc (Phi0 (zmap c)) 1 2 = c 5 := by
  rw [cc, Phi0_zmap_apply]
  simp only [Kend_one_bvec_bvec, Kend_bvec_bvec_bvec]
  simp [sip, evec]

theorem psi_Phi0_zmap (c : Fin 6 → ℝ) : psi (Phi0 (zmap c)) = c := by
  funext i
  fin_cases i
  · simpa [psi] using gvec_zmap c 0
  · simpa [psi] using gvec_zmap c 1
  · simpa [psi] using gvec_zmap c 2
  · simpa [psi] using cc_zmap_01 c
  · simpa [psi] using cc_zmap_02 c
  · simpa [psi] using cc_zmap_12 c

/-! ## `Φ` is an isomorphism -/

theorem Phi_surjective : Function.Surjective Phi := by
  rintro ⟨A, hA⟩
  refine ⟨zmap (psi A), ?_⟩
  have key := psi_Phi0_zmap (psi A)
  have hmem : Phi0 (zmap (psi A)) ∈ gB := Phi0_range_le ⟨_, rfl⟩
  have h0 : gvec (Phi0 (zmap (psi A))) 0 = gvec A 0 := by simpa [psi] using congrFun key 0
  have h1 : gvec (Phi0 (zmap (psi A))) 1 = gvec A 1 := by simpa [psi] using congrFun key 1
  have h2 : gvec (Phi0 (zmap (psi A))) 2 = gvec A 2 := by simpa [psi] using congrFun key 2
  have h3 : cc (Phi0 (zmap (psi A))) 0 1 = cc A 0 1 := by simpa [psi] using congrFun key 3
  have h4 : cc (Phi0 (zmap (psi A))) 0 2 = cc A 0 2 := by simpa [psi] using congrFun key 4
  have h5 : cc (Phi0 (zmap (psi A))) 1 2 = cc A 1 2 := by simpa [psi] using congrFun key 5
  have hg : gvec (Phi0 (zmap (psi A))) = gvec A := by
    funext j; fin_cases j
    exacts [h0, h1, h2]
  exact Subtype.ext (by rw [Phi_coe]; exact gB_ext hmem hA hg h3 h4 h5)

/-- The composite `ℝ⁶ → Λ²𝒮 → 𝔤_B`. -/
def zPhi : (Fin 6 → ℝ) →ₗ[ℝ] gB := Phi.comp zmap

theorem zPhi_injective : Function.Injective zPhi := by
  intro c c' h
  have h' : Phi0 (zmap c) = Phi0 (zmap c') := congrArg Subtype.val h
  rw [← psi_Phi0_zmap c, ← psi_Phi0_zmap c', h']

theorem zmap_injective : Function.Injective zmap := by
  intro c c' h
  rw [← psi_Phi0_zmap c, ← psi_Phi0_zmap c', h]

theorem zmap_surjective : Function.Surjective zmap := by
  have hrank : Module.finrank ℝ (Fin 6 → ℝ) = Module.finrank ℝ (⋀[ℝ]^2 LorentzCarrier) := by
    rw [finrank_extPow2, Module.finrank_fin_fun]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 zmap_injective

theorem Phi_injective : Function.Injective Phi := by
  intro z z' h
  obtain ⟨c, rfl⟩ := zmap_surjective z
  obtain ⟨c', rfl⟩ := zmap_surjective z'
  have hz : zPhi c = zPhi c' := h
  rw [zPhi_injective hz]

/-- **E3 (main).**  The intrinsic isomorphism `Λ²𝒮 ≅ 𝔤_B`. -/
def bivectorEquivSkew : (⋀[ℝ]^2 LorentzCarrier) ≃ₗ[ℝ] gB :=
  LinearEquiv.ofBijective Phi ⟨Phi_injective, Phi_surjective⟩

@[simp] theorem bivectorEquivSkew_apply (z : ⋀[ℝ]^2 LorentzCarrier) :
    (bivectorEquivSkew z : Module.End ℝ LorentzCarrier) = Phi0 z := rfl

theorem bivectorEquivSkew_wedge (u v : LorentzCarrier) :
    (bivectorEquivSkew (wedge u v) : Module.End ℝ LorentzCarrier) = Kend u v := by
  rw [bivectorEquivSkew_apply, Phi0_wedge]

/-- **E3.**  `𝔤_B` is six-dimensional. -/
theorem finrank_gB : Module.finrank ℝ gB = 6 := by
  have := LinearEquiv.finrank_eq bivectorEquivSkew
  rw [finrank_extPow2] at this
  exact this.symm

/-- **E3 (bracket).**  On `𝔤_B` the Lie bracket is the commutator. -/
theorem gBLie_bracket (A B : gBLie) :
    ((⁅A, B⁆ : gBLie) : Module.End ℝ LorentzCarrier)
      = (A : Module.End ℝ LorentzCarrier) * B - (B : Module.End ℝ LorentzCarrier) * A := rfl

end SpinCore
