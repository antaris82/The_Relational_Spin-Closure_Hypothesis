import Mathlib
import RequestProject.Spine.E1.LieAlgebra

/-!
# Task 10, optional Branch F : the Hodge operator on `Λ²𝒮`

**Consumed Task 1–9 data.**  The carrier `𝒮`, the polarized form `B_𝒮`, the exterior square
`Λ²𝒮` and the map `Φ` of Branch 4.

**Extra datum.**  A *volume form* on `𝒮`.  We use `volS`, the determinant of the coordinates
in the Task-9 spin-factor frame `(1, e₀, e₁, e₂)` (written out as the cofactor expansion of
the 4×4 coordinate determinant).  Up to the positive normalisation fixed by `B_𝒮`, the only
remaining freedom is a **sign** — the orientation, a `DISCRETE_COMPONENT_SELECTION`, not a
new continuous primitive.  `hodgeStar_unique` shows that the operator is determined by
`(B_𝒮, volS)` alone, and `hodgeStar_opposite_orientation` records that the opposite
orientation gives exactly `-⋆`.

Main results:

* `hodgeStar_char` : `vol(u, v, ⋆(x ∧ y)) = ⟨u ∧ v, x ∧ y⟩`, the defining Hodge identity.
  The induced form on `Λ²𝒮` is *not* a new primitive: it is written through `Φ` as
  `⟨u ∧ v, β⟩ = -B(Φ(β) u, v)` (see `inducedForm_eq`);
* `hodgeStar_unique` : the identity determines `⋆` uniquely;
* `hodgeStar_star` : `⋆² = -1`, a second derived complex structure.
-/

noncomputable section

namespace SpinCore

open SpinCore

/-! ## The volume form (orientation datum) -/

/-- The volume form of the Task-9 frame: the cofactor expansion of the determinant of the
coordinate matrix with rows `a, b, c, d`.  This is the single extra datum of Branch F, and
only its sign is a genuine choice. -/
def volS (a b c d : LorentzCarrier) : ℝ :=
  a.1 * (b.2 0 * (c.2 1 * d.2 2 - c.2 2 * d.2 1)
          - b.2 1 * (c.2 0 * d.2 2 - c.2 2 * d.2 0)
          + b.2 2 * (c.2 0 * d.2 1 - c.2 1 * d.2 0))
  - a.2 0 * (b.1 * (c.2 1 * d.2 2 - c.2 2 * d.2 1)
          - b.2 1 * (c.1 * d.2 2 - c.2 2 * d.1)
          + b.2 2 * (c.1 * d.2 1 - c.2 1 * d.1))
  + a.2 1 * (b.1 * (c.2 0 * d.2 2 - c.2 2 * d.2 0)
          - b.2 0 * (c.1 * d.2 2 - c.2 2 * d.1)
          + b.2 2 * (c.1 * d.2 0 - c.2 0 * d.1))
  - a.2 2 * (b.1 * (c.2 0 * d.2 1 - c.2 1 * d.2 0)
          - b.2 0 * (c.1 * d.2 1 - c.2 1 * d.1)
          + b.2 1 * (c.1 * d.2 0 - c.2 0 * d.1))

/-- The frame is unimodular for `volS`. -/
theorem volS_frame : volS sOne (bvec 0) (bvec 1) (bvec 2) = 1 := by
  simp [volS, sOne, bvec, evec]

/-! ### The six frame values of `volS` in the last two slots -/

theorem volS_10 (u v : LorentzCarrier) : volS u v sOne (bvec 0) = u.2 1 * v.2 2 - u.2 2 * v.2 1 := by
  simp [volS, sOne, bvec, evec]

theorem volS_11 (u v : LorentzCarrier) : volS u v sOne (bvec 1) = -(u.2 0 * v.2 2) + u.2 2 * v.2 0 := by
  simp [volS, sOne, bvec, evec]

theorem volS_12 (u v : LorentzCarrier) : volS u v sOne (bvec 2) = u.2 0 * v.2 1 - u.2 1 * v.2 0 := by
  simp [volS, sOne, bvec, evec]; ring

theorem volS_01 (u v : LorentzCarrier) :
    volS u v (bvec 0) (bvec 1) = u.1 * v.2 2 - u.2 2 * v.1 := by
  simp [volS, bvec, evec]

theorem volS_02 (u v : LorentzCarrier) :
    volS u v (bvec 0) (bvec 2) = -(u.1 * v.2 1 - u.2 1 * v.1) := by
  simp [volS, bvec, evec]; ring

theorem volS_23 (u v : LorentzCarrier) :
    volS u v (bvec 1) (bvec 2) = u.1 * v.2 0 - u.2 0 * v.1 := by
  simp [volS, bvec, evec]

/-! ## The volume pairing as a linear functional on `Λ²𝒮` -/

/-- For fixed `u, v` the alternating map `(p,q) ↦ vol(u,v,p,q)`. -/
def volAlt (u v : LorentzCarrier) : LorentzCarrier [⋀^Fin 2]→ₗ[ℝ] ℝ where
  toFun m := volS u v (m 0) (m 1)
  map_update_add' := by
    intro _ m i p q
    fin_cases i <;> simp [Function.update, volS] <;> ring
  map_update_smul' := by
    intro _ m i r p
    fin_cases i <;> simp [Function.update, volS] <;> ring
  map_eq_zero_of_eq' := by
    intro m i j hij hne
    fin_cases i <;> fin_cases j <;> simp_all [volS] <;> ring

/-- The volume pairing `β ↦ vol(u,v,β)` as a linear functional on `Λ²𝒮`. -/
def volPair (u v : LorentzCarrier) : (⋀[ℝ]^2 LorentzCarrier) →ₗ[ℝ] ℝ :=
  exteriorPower.alternatingMapLinearEquiv (volAlt u v)

@[simp] theorem volPair_wedge (u v p q : LorentzCarrier) :
    volPair u v (wedge p q) = volS u v p q := by
  rw [volPair, wedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-! ## The Hodge operator -/

/-- The explicit Hodge image of a decomposable bivector, in the Task-9 frame. -/
def hodgeFun (x y : LorentzCarrier) : ⋀[ℝ]^2 LorentzCarrier :=
  (x.2 1 * y.2 2 - x.2 2 * y.2 1) • wedge sOne (bvec 0)
  + (x.2 2 * y.2 0 - x.2 0 * y.2 2) • wedge sOne (bvec 1)
  + (x.2 0 * y.2 1 - x.2 1 * y.2 0) • wedge sOne (bvec 2)
  - (x.1 * y.2 0 - x.2 0 * y.1) • wedge (bvec 1) (bvec 2)
  + (x.1 * y.2 1 - x.2 1 * y.1) • wedge (bvec 0) (bvec 2)
  - (x.1 * y.2 2 - x.2 2 * y.1) • wedge (bvec 0) (bvec 1)

theorem hodgeFun_add_left (x x' y : LorentzCarrier) :
    hodgeFun (x + x') y = hodgeFun x y + hodgeFun x' y := by
  simp only [hodgeFun, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  module

theorem hodgeFun_add_right (x y y' : LorentzCarrier) :
    hodgeFun x (y + y') = hodgeFun x y + hodgeFun x y' := by
  simp only [hodgeFun, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  module

theorem hodgeFun_smul_left (r : ℝ) (x y : LorentzCarrier) :
    hodgeFun (r • x) y = r • hodgeFun x y := by
  simp only [hodgeFun, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  module

theorem hodgeFun_smul_right (r : ℝ) (x y : LorentzCarrier) :
    hodgeFun x (r • y) = r • hodgeFun x y := by
  simp only [hodgeFun, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  module

theorem hodgeFun_self (x : LorentzCarrier) : hodgeFun x x = 0 := by
  simp only [hodgeFun]
  module

/-- The alternating map underlying the Hodge operator. -/
def hodgeAlt : LorentzCarrier [⋀^Fin 2]→ₗ[ℝ] (⋀[ℝ]^2 LorentzCarrier) where
  toFun m := hodgeFun (m 0) (m 1)
  map_update_add' := by
    intro _ m i x y
    fin_cases i <;>
      simp [Function.update, hodgeFun_add_left, hodgeFun_add_right]
  map_update_smul' := by
    intro _ m i r x
    fin_cases i <;>
      simp [Function.update, hodgeFun_smul_left, hodgeFun_smul_right]
  map_eq_zero_of_eq' := by
    intro m i j hij hne
    fin_cases i <;> fin_cases j <;> simp_all [hodgeFun_self]

/-- **F (definition).**  The Hodge operator `⋆ : Λ²𝒮 → Λ²𝒮` of `(B_𝒮, volS)`. -/
def hodgeStar : (⋀[ℝ]^2 LorentzCarrier) →ₗ[ℝ] (⋀[ℝ]^2 LorentzCarrier) :=
  exteriorPower.alternatingMapLinearEquiv hodgeAlt

@[simp] theorem hodgeStar_wedge (x y : LorentzCarrier) : hodgeStar (wedge x y) = hodgeFun x y := by
  rw [hodgeStar, wedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-! ## The defining Hodge identity -/

/-- The induced form on `Λ²𝒮` written through `Φ`, on decomposables. -/
theorem inducedForm_eq (u v x y : LorentzCarrier) :
    -BS (Kend x y u) v = BS u x * BS v y - BS u y * BS v x := by
  rw [Kend_apply, BS_sub_left, BS_smul_left, BS_smul_left]
  have h1 : BS y u = BS u y := BS_symm y u
  have h2 : BS x u = BS u x := BS_symm x u
  have h3 : BS x v = BS v x := BS_symm x v
  have h4 : BS y v = BS v y := BS_symm y v
  rw [h1, h2, h3, h4]
  ring

/-- **F (characterisation).**  `vol(u, v, ⋆(x∧y)) = ⟨u∧v, x∧y⟩`, the defining property of the
Hodge operator for the pair `(B_𝒮, volS)`. -/
theorem hodgeStar_char (u v x y : LorentzCarrier) :
    volPair u v (hodgeStar (wedge x y)) = -BS (Kend x y u) v := by
  rw [hodgeStar_wedge, hodgeFun, inducedForm_eq]
  simp only [map_add, map_sub, map_smul, volPair_wedge, smul_eq_mul,
    volS_10, volS_11, volS_12, volS_01, volS_02, volS_23, BS_eq, sip]
  ring

/-! ## `⋆² = -1` -/

/-- The coordinate action of `⋆` in the frame used by `zmap`. -/
def hodgeCoord (c : Fin 6 → ℝ) : Fin 6 → ℝ := ![-c 5, c 4, -c 3, c 2, -c 1, c 0]

@[simp] theorem hodgeCoord_0 (c : Fin 6 → ℝ) : hodgeCoord c 0 = -c 5 := rfl
@[simp] theorem hodgeCoord_1 (c : Fin 6 → ℝ) : hodgeCoord c 1 = c 4 := rfl
@[simp] theorem hodgeCoord_2 (c : Fin 6 → ℝ) : hodgeCoord c 2 = -c 3 := rfl
@[simp] theorem hodgeCoord_3 (c : Fin 6 → ℝ) : hodgeCoord c 3 = c 2 := rfl
@[simp] theorem hodgeCoord_4 (c : Fin 6 → ℝ) : hodgeCoord c 4 = -c 1 := rfl
@[simp] theorem hodgeCoord_5 (c : Fin 6 → ℝ) : hodgeCoord c 5 = c 0 := rfl

theorem zmap_apply_eq (c : Fin 6 → ℝ) :
    zmap c = c 0 • (-(wedge sOne (bvec 0))) + c 1 • (-(wedge sOne (bvec 1)))
      + c 2 • (-(wedge sOne (bvec 2))) + c 3 • wedge (bvec 0) (bvec 1)
      + c 4 • wedge (bvec 0) (bvec 2) + c 5 • wedge (bvec 1) (bvec 2) := rfl

theorem hodgeFun_one_bvec0 : hodgeFun sOne (bvec 0) = -wedge (bvec 1) (bvec 2) := by
  simp [hodgeFun, sOne, bvec, evec]

theorem hodgeFun_one_bvec1 : hodgeFun sOne (bvec 1) = wedge (bvec 0) (bvec 2) := by
  simp [hodgeFun, sOne, bvec, evec]

theorem hodgeFun_one_bvec2 : hodgeFun sOne (bvec 2) = -wedge (bvec 0) (bvec 1) := by
  simp [hodgeFun, sOne, bvec, evec]

theorem hodgeFun_bvec01 : hodgeFun (bvec 0) (bvec 1) = wedge sOne (bvec 2) := by
  simp [hodgeFun, sOne, bvec, evec]

theorem hodgeFun_bvec02 : hodgeFun (bvec 0) (bvec 2) = -wedge sOne (bvec 1) := by
  simp [hodgeFun, sOne, bvec, evec]; module

theorem hodgeFun_bvec12 : hodgeFun (bvec 1) (bvec 2) = wedge sOne (bvec 0) := by
  simp [hodgeFun, sOne, bvec, evec]

theorem hodgeStar_zmap (c : Fin 6 → ℝ) : hodgeStar (zmap c) = zmap (hodgeCoord c) := by
  rw [zmap_apply_eq, zmap_apply_eq]
  simp only [map_add, map_smul, map_neg, hodgeStar_wedge, hodgeFun_one_bvec0,
    hodgeFun_one_bvec1, hodgeFun_one_bvec2, hodgeFun_bvec01, hodgeFun_bvec02, hodgeFun_bvec12,
    hodgeCoord_0, hodgeCoord_1, hodgeCoord_2, hodgeCoord_3, hodgeCoord_4, hodgeCoord_5]
  module

/-- **F (main).**  `⋆² = -1` on `Λ²𝒮`: a second derived complex structure. -/
theorem hodgeStar_star (z : ⋀[ℝ]^2 LorentzCarrier) : hodgeStar (hodgeStar z) = -z := by
  obtain ⟨c, rfl⟩ := zmap_surjective z
  rw [hodgeStar_zmap, hodgeStar_zmap]
  have h : hodgeCoord (hodgeCoord c) = -c := by
    funext i
    fin_cases i <;> simp
  rw [h, map_neg]

theorem hodgeStar_comp_hodgeStar : hodgeStar.comp hodgeStar = -LinearMap.id := by
  apply LinearMap.ext
  intro z
  simpa using hodgeStar_star z

/-! ## Uniqueness, and dependence on the orientation only -/

theorem volPair_separating {z : ⋀[ℝ]^2 LorentzCarrier} (h : ∀ u v : LorentzCarrier, volPair u v z = 0) :
    z = 0 := by
  obtain ⟨c, rfl⟩ := zmap_surjective z
  have key : ∀ u v : LorentzCarrier,
      -(c 0 * volS u v sOne (bvec 0)) - c 1 * volS u v sOne (bvec 1)
        - c 2 * volS u v sOne (bvec 2) + c 3 * volS u v (bvec 0) (bvec 1)
        + c 4 * volS u v (bvec 0) (bvec 2) + c 5 * volS u v (bvec 1) (bvec 2) = 0 := by
    intro u v
    have hz := h u v
    rw [zmap_apply_eq] at hz
    simp only [map_add, map_smul, map_neg, volPair_wedge, smul_eq_mul] at hz
    linarith
  have h0 := key sOne (bvec 0)
  have h1 := key sOne (bvec 1)
  have h2 := key sOne (bvec 2)
  have h3 := key (bvec 0) (bvec 1)
  have h4 := key (bvec 0) (bvec 2)
  have h5 := key (bvec 1) (bvec 2)
  simp only [volS_10, volS_11, volS_12, volS_01, volS_02, volS_23] at h0 h1 h2 h3 h4 h5
  simp [sOne, bvec, evec] at h0 h1 h2 h3 h4 h5
  have hc : c = 0 := by
    funext i
    fin_cases i <;> simp <;> linarith
  rw [hc, map_zero]

/-- **F (uniqueness).**  The Hodge identity determines `⋆` completely: it is a function of
`B_𝒮` and the volume form only, so no further datum is hidden in the construction. -/
theorem hodgeStar_unique (T : (⋀[ℝ]^2 LorentzCarrier) →ₗ[ℝ] (⋀[ℝ]^2 LorentzCarrier))
    (hT : ∀ u v x y : LorentzCarrier, volPair u v (T (wedge x y)) = -BS (Kend x y u) v) :
    T = hodgeStar := by
  have hwedge : ∀ x y : LorentzCarrier, T (wedge x y) = hodgeStar (wedge x y) := by
    intro x y
    have hzero : ∀ u v : LorentzCarrier, volPair u v (T (wedge x y) - hodgeStar (wedge x y)) = 0 := by
      intro u v
      rw [map_sub, hT u v x y, hodgeStar_char]
      ring
    exact sub_eq_zero.1 (volPair_separating hzero)
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := zmap_surjective z
  rw [zmap_apply_eq]
  simp only [map_add, map_smul, map_neg, hwedge]

/-- **F (orientation dependence).**  Reversing the orientation (`volS ↦ -volS`, hence
`volPair ↦ -volPair`) replaces `⋆` by `-⋆`, and changes nothing else. -/
theorem hodgeStar_opposite_orientation (u v x y : LorentzCarrier) :
    -(volPair u v ((-hodgeStar) (wedge x y))) = -BS (Kend x y u) v := by
  rw [LinearMap.neg_apply, map_neg, neg_neg, hodgeStar_char]

end SpinCore
