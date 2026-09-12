import RequestProject.Experiment1.SectorAlgebra
import RequestProject.Experiment1.LorentzMatrix
import RequestProject.Experiment1.CarrierEquivalence

/-!
# From the sector carrier to the proper orthochronous `1+1` Lorentz group

This file connects the intrinsically derived positive norm-one action of
`RequestProject.Experiment1.SectorAlgebra` with the *independently defined* matrix group
`Lorentz.SO11Plus` of `RequestProject.Experiment1.LorentzMatrix`.

Contents.

* `U1posUnits` — the positive norm-one branch as a genuine subgroup of `Aˣ`, and
  `positiveNormOne_equiv_additiveReal : Multiplicative ℝ ≃* U1posUnits S`.
* `basisTX` — the `(T, X)` basis `{1, ε}` of `A`; by construction `z = T·1 + X·ε` is exactly
  the coordinate change `u = T + X`, `v = T - X` on the sector coordinates.
* `regMatrix` — the matrix of the regular multiplicative action in that basis, and
  `regularAction_matrix_eq_lorentzBoost : regMatrix (gElem η) = Lorentz.B η`.
* `regularAction_faithful` — the representation is faithful.
* `positiveNormOne_mulEquiv_SO11Plus : U1posUnits S ≃* Lorentz.SO11Plus`, together with
  `Phi_coe_eq_regMatrix`, which certifies that this isomorphism *is* the regular action in
  `(T, X)` coordinates and not an abstract relabelling.
* `sector_dependency_theorem_v3` — the corrected dependency theorem: it assumes only
  `[Ring A] [Algebra ℝ A]`, `finrank ℝ A = 2` and the two nonzero complementary orthogonal
  idempotents (commutativity is *derived*), and all of its Lorentz and dual-pairing clauses
  are stated for the algebraic action `g_η * z`.

No physical interpretation is asserted anywhere in this file.  `T`, `X`, `c` are coordinate
symbols; `c` is never derived and the group-identification theorem does not involve it.
-/

noncomputable section

open Real

namespace Sector

namespace SectorAlgebra

variable {A : Type*} [CommRing A] [Algebra ℝ A] (S : SectorAlgebra A)

/-! ## 1. The positive norm-one branch as a subgroup of the units -/

/-- The positive norm-one branch, packaged as a subgroup of `Aˣ`.  Membership is defined by
the intrinsic condition `↑u ∈ U1pos`, i.e. `↑u = a p + a⁻¹ q` with `a > 0`. -/
def U1posUnits : Subgroup Aˣ where
  carrier := {u : Aˣ | (u : A) ∈ S.U1pos}
  one_mem' := by simpa using S.one_mem_U1pos
  mul_mem' := by
    intro u v hu hv
    simpa using S.mul_mem_U1pos hu hv
  inv_mem' := by
    intro u hu
    obtain ⟨a, ha, hval⟩ := hu
    have hinv : ((u⁻¹ : Aˣ) : A) = a⁻¹ • S.p + a • S.q := by
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [hval, S.mul_decomp, mul_inv_cancel₀ (ne_of_gt ha),
        inv_mul_cancel₀ (ne_of_gt ha), ← S.sum_eq_one]
      module
    exact ⟨a⁻¹, inv_pos.mpr ha, by rw [hinv, inv_inv]⟩

theorem mem_U1posUnits_iff (u : Aˣ) : u ∈ S.U1posUnits ↔ (u : A) ∈ S.U1pos := Iff.rfl

theorem gUnit_mem_U1posUnits (η : ℝ) : S.gUnit η ∈ S.U1posUnits := S.gElem_mem_U1pos η

/-- The exponential parametrisation as a monoid homomorphism into the subgroup. -/
def etaHom : Multiplicative ℝ →* S.U1posUnits where
  toFun η := ⟨S.gUnit (Multiplicative.toAdd η), S.gUnit_mem_U1posUnits _⟩
  map_one' := by
    apply Subtype.ext
    exact Units.ext (by simpa using S.gElem_zero)
  map_mul' η₁ η₂ := by
    apply Subtype.ext
    exact Units.ext (by simpa using S.gElem_add _ _)

@[simp] theorem etaHom_coe (η : ℝ) :
    (((S.etaHom (Multiplicative.ofAdd η) : S.U1posUnits) : Aˣ) : A) = S.gElem η := rfl

theorem etaHom_bijective : Function.Bijective S.etaHom := by
  constructor
  · intro η₁ η₂ h
    have : S.gElem (Multiplicative.toAdd η₁) = S.gElem (Multiplicative.toAdd η₂) :=
      congrArg (fun u : S.U1posUnits => ((u : Aˣ) : A)) h
    exact Multiplicative.toAdd.injective (S.gElem_injective this)
  · rintro ⟨u, hu⟩
    obtain ⟨η, hη, -⟩ := S.exists_unique_eta hu
    exact ⟨Multiplicative.ofAdd η, Subtype.ext (Units.ext hη.symm)⟩

/-- **The positive norm-one subgroup is `(ℝ, +)`.** -/
def positiveNormOne_equiv_additiveReal : Multiplicative ℝ ≃* S.U1posUnits :=
  MulEquiv.ofBijective S.etaHom S.etaHom_bijective

@[simp] theorem positiveNormOne_equiv_additiveReal_coe (η : ℝ) :
    (((S.positiveNormOne_equiv_additiveReal (Multiplicative.ofAdd η) : S.U1posUnits) : Aˣ) : A)
      = S.gElem η := rfl

/-- Every element of the positive norm-one subgroup is `g η` for a unique `η`. -/
theorem exists_unique_eta_units (u : S.U1posUnits) : ∃! η : ℝ, ((u : Aˣ) : A) = S.gElem η :=
  S.exists_unique_eta u.2

/-! ## 2. The `(T, X)` basis and the regular action -/

/-- The basis `{1, ε}` of `A`.  Since `1 = p + q` and `ε = p - q`, writing `z = T·1 + X·ε` is
*exactly* the linear coordinate change `u = T + X`, `v = T - X` on the sector coordinates. -/
def basisTX : Module.Basis (Fin 2) ℝ A :=
  basisOfLinearIndependentOfCardEqFinrank S.linearIndependent_one_epsilon (by simp [S.finrank_eq])

theorem coe_basisTX : ⇑S.basisTX = ![(1 : A), S.epsilon] :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

theorem basisTX_zero : S.basisTX 0 = (1 : A) := by rw [coe_basisTX]; rfl

theorem basisTX_one : S.basisTX 1 = S.epsilon := by rw [coe_basisTX]; rfl

theorem reprTX (a b : ℝ) :
    S.basisTX.repr (a • (1 : A) + b • S.epsilon) = Finsupp.single 0 a + Finsupp.single 1 b := by
  rw [← S.basisTX_zero, ← S.basisTX_one, map_add, map_smul, map_smul,
    Module.Basis.repr_self, Module.Basis.repr_self]
  simp [Finsupp.smul_single]

@[simp] theorem reprTX_zero (a b : ℝ) : S.basisTX.repr (a • (1 : A) + b • S.epsilon) 0 = a := by
  rw [reprTX]; simp

@[simp] theorem reprTX_one (a b : ℝ) : S.basisTX.repr (a • (1 : A) + b • S.epsilon) 1 = b := by
  rw [reprTX]; simp

/-- The `T` coordinate of `z`, i.e. `(u + v)/2` in sector coordinates. -/
def coordT (z : A) : ℝ := (S.coordP z + S.coordQ z) / 2

/-- The `X` coordinate of `z`, i.e. `(u - v)/2` in sector coordinates. -/
def coordX (z : A) : ℝ := (S.coordP z - S.coordQ z) / 2

@[simp] theorem coordT_lightcone (u v : ℝ) : S.coordT (u • S.p + v • S.q) = (u + v) / 2 := by
  simp [coordT]

@[simp] theorem coordX_lightcone (u v : ℝ) : S.coordX (u • S.p + v • S.q) = (u - v) / 2 := by
  simp [coordX]

/-- The `(T, X)` decomposition of an element: `z = T·1 + X·ε`. -/
theorem decompTX (z : A) : z = S.coordT z • (1 : A) + S.coordX z • S.epsilon := by
  rw [S.smul_one_add_smul_epsilon]
  conv_lhs => rw [S.decomp z]
  simp only [coordT, coordX]
  module

/-- The `(T, X)` coordinates are the `{1, ε}`-basis coordinates. -/
theorem coordT_eq_repr (z : A) : S.coordT z = S.basisTX.repr z 0 := by
  conv_rhs => rw [S.decompTX z]
  rw [S.reprTX_zero]

theorem coordX_eq_repr (z : A) : S.coordX z = S.basisTX.repr z 1 := by
  conv_rhs => rw [S.decompTX z]
  rw [S.reprTX_one]

/-- The matrix of the regular multiplicative action of `z` in the `(T, X)` basis. -/
def regMatrix (z : A) : Matrix (Fin 2) (Fin 2) ℝ :=
  LinearMap.toMatrix S.basisTX S.basisTX (LinearMap.mulLeft ℝ z)

theorem regMatrix_apply (z : A) (i j : Fin 2) :
    S.regMatrix z i j = S.basisTX.repr (z * S.basisTX j) i := by
  simp [regMatrix, LinearMap.toMatrix_apply]

theorem regMatrix_one : S.regMatrix 1 = 1 := by
  simp [regMatrix]

theorem regMatrix_mul (z w : A) : S.regMatrix (z * w) = S.regMatrix z * S.regMatrix w := by
  simp [regMatrix, LinearMap.mulLeft_mul, LinearMap.toMatrix_comp S.basisTX S.basisTX]

/-- The regular representation `A →* Matrix (Fin 2) (Fin 2) ℝ`. -/
def regRep : A →* Matrix (Fin 2) (Fin 2) ℝ where
  toFun := S.regMatrix
  map_one' := S.regMatrix_one
  map_mul' := S.regMatrix_mul

@[simp] theorem regRep_apply (z : A) : S.regRep z = S.regMatrix z := rfl

/-- The regular representation is injective: `z` is recovered as the image of `1`. -/
theorem regMatrix_injective : Function.Injective S.regMatrix := by
  intro z w h
  have h1 : LinearMap.mulLeft ℝ z = LinearMap.mulLeft ℝ w :=
    (LinearMap.toMatrix S.basisTX S.basisTX).injective h
  have h2 := congrArg (fun f : A →ₗ[ℝ] A => f 1) h1
  simpa using h2

/-! ## 3. The action matrix is the standard boost matrix -/

theorem gElem_eq_cosh_sinh (η : ℝ) : S.gElem η = cosh η • (1 : A) + sinh η • S.epsilon := by
  rw [S.smul_one_add_smul_epsilon, gElem, Real.cosh_eq, Real.sinh_eq]
  module

theorem gElem_mul_epsilon (η : ℝ) :
    S.gElem η * S.epsilon = sinh η • (1 : A) + cosh η • S.epsilon := by
  have hep : S.epsilon = (1 : ℝ) • S.p + (-1 : ℝ) • S.q := by
    simp only [epsilon]; module
  rw [S.smul_one_add_smul_epsilon, gElem, hep, S.mul_decomp, Real.cosh_eq, Real.sinh_eq]
  module

/-- **The regular action of `g η` in the `(T, X)` basis is exactly the standard boost matrix.**
This starts from the algebraic element `g η` and the algebraic coordinate maps; it is not a
detached identity between real exponentials. -/
theorem regularAction_matrix_eq_lorentzBoost (η : ℝ) : S.regMatrix (S.gElem η) = Lorentz.B η := by
  have c0 : S.gElem η * S.basisTX 0 = cosh η • (1 : A) + sinh η • S.epsilon := by
    rw [S.basisTX_zero, mul_one, S.gElem_eq_cosh_sinh]
  have c1 : S.gElem η * S.basisTX 1 = sinh η • (1 : A) + cosh η • S.epsilon := by
    rw [S.basisTX_one, S.gElem_mul_epsilon]
  ext i j
  rw [S.regMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, c0, c1, S.reprTX_zero, S.reprTX_one,
      Lorentz.B_apply_00, Lorentz.B_apply_01, Lorentz.B_apply_10, Lorentz.B_apply_11]

/-- `T' = cosh η · T + sinh η · X`, obtained from the algebraic action. -/
theorem coordT_gElem_mul (η : ℝ) (z : A) :
    S.coordT (S.gElem η * z) = cosh η * S.coordT z + sinh η * S.coordX z := by
  simp only [coordT, coordX, S.coordP_gElem_mul, S.coordQ_gElem_mul, Real.cosh_eq, Real.sinh_eq]
  ring

/-- `X' = sinh η · T + cosh η · X`, obtained from the algebraic action. -/
theorem coordX_gElem_mul (η : ℝ) (z : A) :
    S.coordX (S.gElem η * z) = sinh η * S.coordT z + cosh η * S.coordX z := by
  simp only [coordT, coordX, S.coordP_gElem_mul, S.coordQ_gElem_mul, Real.cosh_eq, Real.sinh_eq]
  ring

/-- The action in coordinates: `(T', X') = B(η) (T, X)`, starting from `g η * z`. -/
theorem regularAction_coords (η : ℝ) (z : A) :
    ![S.coordT (S.gElem η * z), S.coordX (S.gElem η * z)]
      = (Lorentz.B η).mulVec ![S.coordT z, S.coordX z] := by
  rw [Lorentz.lorentzBoostMatrix_mulVec]
  ext i
  fin_cases i <;> simp [S.coordT_gElem_mul, S.coordX_gElem_mul]

/-- The Minkowski form `T² - X²` is preserved by the algebraic action. -/
theorem minkowski_invariant_action (η : ℝ) (z : A) :
    S.coordT (S.gElem η * z) ^ 2 - S.coordX (S.gElem η * z) ^ 2
      = S.coordT z ^ 2 - S.coordX z ^ 2 := by
  rw [S.coordT_gElem_mul, S.coordX_gElem_mul]
  nlinarith [Real.cosh_sq_sub_sinh_sq η]

/-! ## 4. Faithfulness -/

/-- The representation of the positive norm-one subgroup by the regular action in `(T, X)`
coordinates, valued in `GL(2, ℝ)`. -/
def rho : S.U1posUnits →* Matrix.GeneralLinearGroup (Fin 2) ℝ :=
  (Units.map S.regRep).comp (S.U1posUnits).subtype

@[simp] theorem rho_coe (u : S.U1posUnits) :
    ((S.rho u : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = S.regMatrix ((u : Aˣ) : A) := rfl

/-- **Faithfulness.**  `ρ g = 1` forces `g = 1`. -/
theorem regularAction_faithful {u : S.U1posUnits} (h : S.rho u = 1) : u = 1 := by
  have h1 : S.regMatrix ((u : Aˣ) : A) = S.regMatrix 1 := by
    have := congrArg (fun M : Matrix.GeneralLinearGroup (Fin 2) ℝ =>
      (M : Matrix (Fin 2) (Fin 2) ℝ)) h
    rw [S.regMatrix_one]
    simpa using this
  have h2 : ((u : Aˣ) : A) = 1 := S.regMatrix_injective h1
  exact Subtype.ext (Units.ext h2)

/-- **Faithfulness, injective form.** -/
theorem rho_injective : Function.Injective S.rho := by
  intro u v h
  have h1 : S.regMatrix ((u : Aˣ) : A) = S.regMatrix ((v : Aˣ) : A) := by
    have := congrArg (fun M : Matrix.GeneralLinearGroup (Fin 2) ℝ =>
      (M : Matrix (Fin 2) (Fin 2) ℝ)) h
    simpa using this
  exact Subtype.ext (Units.ext (S.regMatrix_injective h1))

/-! ## 5. The exact Lorentz-group isomorphism -/

/-- `(ℝ, +)` is isomorphic to the independently defined `SO₀(1,1)`; this uses the
classification theorem, not any property of the sector algebra. -/
def rapidityEquivSO11Plus : Multiplicative ℝ ≃* Lorentz.SO11Plus := by
  refine MulEquiv.ofBijective
    ({ toFun := fun η => ⟨Lorentz.BSL (Multiplicative.toAdd η), Lorentz.BSL_mem _⟩
       map_one' := ?_
       map_mul' := ?_ } : Multiplicative ℝ →* Lorentz.SO11Plus) ?_
  · apply Subtype.ext; apply Subtype.ext
    simpa using Lorentz.lorentzBoostMatrix_zero
  · intro η₁ η₂
    apply Subtype.ext; apply Subtype.ext
    simpa using (Lorentz.lorentzBoostMatrix_group_law
      (Multiplicative.toAdd η₁) (Multiplicative.toAdd η₂)).symm
  · constructor
    · intro η₁ η₂ h
      have : Lorentz.B (Multiplicative.toAdd η₁) = Lorentz.B (Multiplicative.toAdd η₂) :=
        congrArg (fun M : Lorentz.SO11Plus =>
          ((M : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) h
      exact Multiplicative.toAdd.injective (Lorentz.rapidity_unique this)
    · rintro ⟨M, hM⟩
      obtain ⟨η, hη, -⟩ := (Lorentz.SO11Plus_eq_range M).mp hM
      exact ⟨Multiplicative.ofAdd η, Subtype.ext (by simpa using hη.symm)⟩

@[simp] theorem rapidityEquivSO11Plus_coe (η : ℝ) :
    ((rapidityEquivSO11Plus (Multiplicative.ofAdd η) :
        Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Lorentz.B η := rfl

/-- **The exact Lorentz-group identification.**  The positive norm-one unit group of the
carrier is isomorphic, as a group, to the independently defined proper orthochronous `1+1`
Lorentz group. -/
def positiveNormOne_mulEquiv_SO11Plus : S.U1posUnits ≃* Lorentz.SO11Plus :=
  (S.positiveNormOne_equiv_additiveReal).symm.trans rapidityEquivSO11Plus

/-- The isomorphism **is** the regular action in `(T, X)` coordinates: its matrix at `u` is
the matrix of multiplication by `u`. -/
theorem Phi_coe_eq_regMatrix (u : S.U1posUnits) :
    ((S.positiveNormOne_mulEquiv_SO11Plus u : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)
      = S.regMatrix ((u : Aˣ) : A) := by
  obtain ⟨η, hη, -⟩ := S.exists_unique_eta_units u
  have hu : u = S.positiveNormOne_equiv_additiveReal (Multiplicative.ofAdd η) :=
    Subtype.ext (Units.ext hη)
  rw [hη, S.regularAction_matrix_eq_lorentzBoost, hu, positiveNormOne_mulEquiv_SO11Plus,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply, rapidityEquivSO11Plus_coe]

/-- The isomorphism agrees with the faithful representation `ρ`. -/
theorem Phi_eq_rho (u : S.U1posUnits) :
    ((S.positiveNormOne_mulEquiv_SO11Plus u : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)
      = ((S.rho u : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [S.Phi_coe_eq_regMatrix, S.rho_coe]

/-! ## 6. The usual `c, t, x` notation, as a corollary only

`c` is introduced here for the first time, purely as a coordinate scale.  It is not derived,
no positivity is required for the algebraic identities, and the group-identification theorem
above does not mention it. -/

/-- With `T = c t`, the derived action gives the familiar boost formula for `c t`. -/
theorem lorentz_ct_of_action (η c t x : ℝ) :
    S.coordT (S.gElem η * ((c * t + x) • S.p + (c * t - x) • S.q))
      = cosh η * (c * t) + sinh η * x := by
  rw [S.coordT_gElem_mul, S.coordT_lightcone, S.coordX_lightcone]
  ring_nf

/-- With `T = c t`, the derived action gives the familiar boost formula for `x`. -/
theorem lorentz_x_of_action (η c t x : ℝ) :
    S.coordX (S.gElem η * ((c * t + x) • S.p + (c * t - x) • S.q))
      = sinh η * (c * t) + cosh η * x := by
  rw [S.coordX_gElem_mul, S.coordT_lightcone, S.coordX_lightcone]
  ring_nf

/-- `c²t'² - x'² = c²t² - x²`, derived from the algebraic action. -/
theorem minkowski_invariant_c_of_action (η c t x : ℝ) :
    S.coordT (S.gElem η * ((c * t + x) • S.p + (c * t - x) • S.q)) ^ 2
        - S.coordX (S.gElem η * ((c * t + x) • S.p + (c * t - x) • S.q)) ^ 2
      = c ^ 2 * t ^ 2 - x ^ 2 := by
  rw [S.minkowski_invariant_action, S.coordT_lightcone, S.coordX_lightcone]
  ring_nf

end SectorAlgebra

/-! ## 7. The corrected dependency theorem

Commutativity is **not** assumed: it is derived from `finrank ℝ A = 2` via
`Sector.commutative_of_finrank_two`.  Every Lorentz clause is stated for the algebraic
action `g η * z`, and the dual-pairing clauses use the sector coordinates of `g η * (u p + v q)`.
-/

/-- **Corrected final dependency theorem.**

Primitive data: a two-dimensional associative unital real algebra `A` (commutativity is
*derived*, not assumed) together with two nonzero complementary orthogonal idempotents
`p, q`.  Then there are `ε`, an involution `σ`, a norm `N`, a one-parameter family `g` and
coordinate maps `cP, cQ, cT, cX` such that:

1. `A ≅ ℝ × ℝ`, `p, q` give unique coordinates, and multiplication is coordinatewise;
2. `A` is commutative and `ε = p - q` satisfies `ε² = 1`, `ε ≠ ±1`;
3. `σ` is the sector-exchanging involution and `z σ z = N z · 1` with `N (a p + b q) = a b`
   multiplicative;
4. the positive norm-one elements are exactly the `g η`, uniquely, forming a one-parameter
   group;
5. the multiplicative action of `g η` is the reciprocal action on sector coordinates and
   preserves `N`;
6. **in the coordinates `T = (u+v)/2`, `X = (u-v)/2` the action of `g η` is the standard
   boost**, and it preserves `T² - X²`; with `T = ct` this is the familiar form;
7. **the positive norm-one unit group is isomorphic to the independently defined
   `SO₀(1,1)`**, by an isomorphism whose matrix at `u` is the matrix of multiplication by
   `u` in the `(T, X)` basis, and this representation is faithful;
8. contragredient coefficients give sectorwise invariant dual pairings of the action with
   its contragredient — an invariance statement about a representation and its
   contragredient, *not* evidence of Lorentz covariance, which is supplied by clause 7.

No physical interpretation is asserted. -/
theorem sector_dependency_theorem_v3 {A : Type*} [Ring A] [Algebra ℝ A] (p q : A)
    (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hsum : p + q = 1)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hdim : Module.finrank ℝ A = 2) :
    (∀ x y : A, x * y = y * x) ∧
    ∃ (eps : A) (sigma : A →ₐ[ℝ] A) (N : A → ℝ) (g : ℝ → A)
      (cP cQ cT cX : A → ℝ) (G : Subgroup Aˣ),
      -- 1. the sector decomposition
      (Nonempty (A ≃ₐ[ℝ] ℝ × ℝ)) ∧
      (∀ z : A, ∃! ab : ℝ × ℝ, z = ab.1 • p + ab.2 • q) ∧
      (∀ a b c d : ℝ, (a • p + b • q) * (c • p + d • q) = (a * c) • p + (b * d) • q) ∧
      -- 2. the split generator
      (eps = p - q ∧ eps * eps = 1 ∧ eps ≠ 1 ∧ eps ≠ -1) ∧
      -- 3. involution and norm
      ((∀ z, sigma (sigma z) = z) ∧ sigma p = q ∧ sigma q = p ∧
        (∀ z, z * sigma z = N z • (1 : A)) ∧ (∀ a b : ℝ, N (a • p + b • q) = a * b) ∧
        (∀ z w, N (z * w) = N z * N w)) ∧
      -- 4. the positive norm-one branch and its exponential parametrisation
      ((∀ η : ℝ, g η = exp η • p + exp (-η) • q) ∧
        (∀ z : A, (∃ a : ℝ, 0 < a ∧ z = a • p + a⁻¹ • q) ↔ ∃ η : ℝ, z = g η) ∧
        (∀ z : A, (∃ a : ℝ, 0 < a ∧ z = a • p + a⁻¹ • q) → ∃! η : ℝ, z = g η) ∧
        g 0 = 1 ∧ (∀ η₁ η₂, g (η₁ + η₂) = g η₁ * g η₂) ∧ (∀ η, g η * g (-η) = 1) ∧
        (∀ η, N (g η) = 1) ∧
        (∀ u : Aˣ, u ∈ G ↔ ∃ η : ℝ, ((u : A)) = g η) ∧
        Nonempty (Multiplicative ℝ ≃* G)) ∧
      -- 5. the reciprocal action on sector coordinates
      ((∀ z : A, z = cP z • p + cQ z • q) ∧
        (∀ η u v : ℝ, g η * (u • p + v • q) = (exp η * u) • p + (exp (-η) * v) • q) ∧
        (∀ η u v : ℝ, cP (g η * (u • p + v • q)) = exp η * u) ∧
        (∀ η u v : ℝ, cQ (g η * (u • p + v • q)) = exp (-η) * v) ∧
        (∀ (η : ℝ) (z : A), N (g η * z) = N z)) ∧
      -- 6. the Lorentz boost, in terms of the algebraic action
      ((∀ z : A, cT z = (cP z + cQ z) / 2 ∧ cX z = (cP z - cQ z) / 2) ∧
        (∀ (η : ℝ) (z : A),
          cT (g η * z) = cosh η * cT z + sinh η * cX z ∧
          cX (g η * z) = sinh η * cT z + cosh η * cX z) ∧
        (∀ (η : ℝ) (z : A),
          ![cT (g η * z), cX (g η * z)] = (Lorentz.B η).mulVec ![cT z, cX z]) ∧
        (∀ (η : ℝ) (z : A), cT (g η * z) ^ 2 - cX (g η * z) ^ 2 = cT z ^ 2 - cX z ^ 2) ∧
        (∀ η c t x : ℝ,
          cT (g η * ((c * t + x) • p + (c * t - x) • q)) = cosh η * (c * t) + sinh η * x ∧
          cX (g η * ((c * t + x) • p + (c * t - x) • q)) = sinh η * (c * t) + cosh η * x ∧
          cT (g η * ((c * t + x) • p + (c * t - x) • q)) ^ 2
            - cX (g η * ((c * t + x) • p + (c * t - x) • q)) ^ 2 = c ^ 2 * t ^ 2 - x ^ 2)) ∧
      -- 7. the exact group identification, realised by the regular action
      (∃ (rep : A → Matrix (Fin 2) (Fin 2) ℝ) (Phi : G ≃* Lorentz.SO11Plus),
        Function.Injective rep ∧
        (∀ z w : A, rep (z * w) = rep z * rep w) ∧
        (∀ η : ℝ, rep (g η) = Lorentz.B η) ∧
        (∀ u : G, ((Phi u : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
            Matrix (Fin 2) (Fin 2) ℝ) = rep ((u : Aˣ) : A))) ∧
      -- 8. subordinate: invariant pairings with the contragredient coefficients
      (∀ η kp km u v : ℝ,
        (exp (-η) * kp) * cP (g η * (u • p + v • q)) = kp * u ∧
        (exp η * km) * cQ (g η * (u • p + v • q)) = km * v) := by
  have hcomm := Sector.commutative_of_finrank_two (A := A) hdim
  refine ⟨hcomm, ?_⟩
  letI : CommRing A := Sector.commRingOfFinrankTwo hdim
  let S : Sector.SectorAlgebra A :=
    { p := p, q := q, sq_p := hp, sq_q := hq, orth := hpq, sum_eq_one := hsum,
      p_ne_zero := hp0, q_ne_zero := hq0, finrank_eq := hdim }
  refine ⟨S.epsilon, S.sigmaHom, S.N, S.gElem, S.coordP, S.coordQ, S.coordT, S.coordX,
    S.U1posUnits,
    S.exists_algEquiv_prod, S.existsUnique_coords, S.mul_decomp,
    ⟨rfl, S.epsilon_sq, S.epsilon_ne_one, S.epsilon_ne_neg_one⟩,
    ⟨S.sigmaHom_sigmaHom, S.sigmaHom_p, S.sigmaHom_q, S.mul_sigmaHom, S.N_smul_add_smul,
      S.N_mul⟩,
    ⟨fun η => rfl, ?_, ?_, S.gElem_zero, S.gElem_add, S.gElem_mul_gElem_neg, S.N_gElem, ?_,
      ⟨S.positiveNormOne_equiv_additiveReal⟩⟩,
    ⟨S.decomp, S.gElem_mul, ?_, ?_, S.N_gElem_mul⟩,
    ⟨fun z => ⟨rfl, rfl⟩, ?_, S.regularAction_coords, S.minkowski_invariant_action, ?_⟩,
    ⟨S.regMatrix, S.positiveNormOne_mulEquiv_SO11Plus, S.regMatrix_injective, S.regMatrix_mul,
      S.regularAction_matrix_eq_lorentzBoost, S.Phi_coe_eq_regMatrix⟩,
    ?_⟩
  · intro z
    constructor
    · intro hz
      obtain ⟨η, h, -⟩ := S.exists_unique_eta hz
      exact ⟨η, h⟩
    · rintro ⟨η, rfl⟩
      exact S.gElem_mem_U1pos η
  · intro z hz
    exact S.exists_unique_eta hz
  · intro u
    constructor
    · intro hu
      obtain ⟨η, h, -⟩ := S.exists_unique_eta hu
      exact ⟨η, h⟩
    · rintro ⟨η, hη⟩
      show ((u : A)) ∈ S.U1pos
      rw [hη]
      exact S.gElem_mem_U1pos η
  · intro η u v
    rw [S.gElem_mul]
    simp
  · intro η u v
    rw [S.gElem_mul]
    simp
  · intro η z
    exact ⟨S.coordT_gElem_mul η z, S.coordX_gElem_mul η z⟩
  · intro η c t x
    exact ⟨S.lorentz_ct_of_action η c t x, S.lorentz_x_of_action η c t x,
      S.minkowski_invariant_c_of_action η c t x⟩
  · intro η kp km u v
    exact ⟨S.dual_pairing_p_invariant η kp u v, S.dual_pairing_q_invariant η km u v⟩

/-! ## 8. Non-vacuity

The hypotheses of `sector_dependency_theorem_v3` are satisfiable: `ℝ × ℝ` with
`p = (1, 0)`, `q = (0, 1)` satisfies all of them, and the resulting positive norm-one unit
group really is isomorphic to `SO₀(1,1)`. -/

theorem sector_dependency_hypotheses_satisfiable :
    ∃ p q : ℝ × ℝ, p * p = p ∧ q * q = q ∧ p * q = 0 ∧ p + q = 1 ∧ p ≠ 0 ∧ q ≠ 0 ∧
      Module.finrank ℝ (ℝ × ℝ) = 2 :=
  ⟨(1, 0), (0, 1), by norm_num [Prod.ext_iff], by norm_num [Prod.ext_iff],
    by norm_num [Prod.ext_iff], by norm_num [Prod.ext_iff], by simp [Prod.ext_iff],
    by simp [Prod.ext_iff], by simp⟩

/-- A concrete instance of the group identification. -/
theorem prod_positiveNormOne_mulEquiv_SO11Plus :
    Nonempty (Sector.prodSectorAlgebra.U1posUnits ≃* Lorentz.SO11Plus) :=
  ⟨Sector.prodSectorAlgebra.positiveNormOne_mulEquiv_SO11Plus⟩

end Sector
