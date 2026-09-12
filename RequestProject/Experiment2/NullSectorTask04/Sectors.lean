import RequestProject.Experiment2.NullSectorTask04.RestSpace
import RequestProject.Experiment2.NullSectorTask02.FixedUnit

/-!
# Task 04, Layer 3: the family of longitudinal 1+1 sectors

For each unit spacelike direction `s` orthogonal to `e₀` we obtain an isometric
copy of the Task-01/02 longitudinal carrier inside `Vec4`.

The longitudinal product used here is **not** redefined: it is the product
reconstructed in Task 02 as the unique bilinear, unital, `Q2`-multiplicative
product with unit `u₀ = (1,0)`, namely `NullSectorTask02.recU`.  No Task-01
split-complex declaration is used.
-/

namespace NullSectorTask04

open NullSectorTask01

/-! ## Unit spacelike directions -/

/-- A unit spatial direction: `L4`-orthogonal to `e₀` and of `Q4`-square `-1`. -/
def UnitSpacelike (s : Vec4) : Prop := L4 e₀ s = 0 ∧ Q4 s = -1

theorem unitSpacelike_iff (s : Vec4) : UnitSpacelike s ↔ s ∈ Rest ∧ h s s = 1 := by
  have hL : L4 e₀ s = s.1 := L4_e₀_left s
  have hh : h s s = - Q4 s := h_self s
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_Rest s).2 (by rw [← hL]; exact h1), ?_⟩
    rw [hh, h2]; norm_num
  · rintro ⟨h1, h2⟩
    rw [hh] at h2
    exact ⟨by rw [hL]; exact (mem_Rest s).1 h1, by linarith⟩

/-- Coordinate form: unit spatial directions are exactly the `sp v` with
`dot3 v v = 1`. -/
theorem unitSpacelike_sp_iff (v : Vec3) : UnitSpacelike (sp v) ↔ dot3 v v = 1 := by
  rw [unitSpacelike_iff, h_sp]
  simp

theorem unitSpacelike_spatial {s : Vec4} (hs : UnitSpacelike s) :
    s = sp s.2 ∧ dot3 s.2 s.2 = 1 := by
  have h1 : s ∈ Rest := ((unitSpacelike_iff s).1 hs).1
  refine ⟨rest_eq_sp h1, ?_⟩
  have := ((unitSpacelike_iff s).1 hs).2
  rwa [rest_eq_sp h1, h_sp] at this

/-- Every nonzero rest vector is a positive multiple of a unit spatial direction. -/
theorem exists_unitSpacelike_of_ne_zero {v : Vec3} (hv : v ≠ 0) :
    ∃ (r : ℝ) (s : Vec4), 0 < r ∧ UnitSpacelike s ∧ sp v = r • s := by
  have hpos : 0 < dot3 v v := lt_of_le_of_ne (dot3_self_nonneg v)
    (fun hc => hv ((dot3_self_eq_zero_iff v).1 hc.symm))
  set r : ℝ := Real.sqrt (dot3 v v) with hr
  have hrpos : 0 < r := Real.sqrt_pos.2 hpos
  refine ⟨r, sp ((r⁻¹ : ℝ) • v), hrpos, ?_, ?_⟩
  · rw [unitSpacelike_sp_iff, dot3_smul_left, dot3_smul_right]
    field_simp
    rw [hr, Real.sq_sqrt hpos.le]
  · rw [← sp_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt hrpos), one_smul]

/-- There is at least one unit spatial direction. -/
theorem unitSpacelike_s₁ : UnitSpacelike (sp s₁) :=
  (unitSpacelike_sp_iff s₁).2 dot3_s₁_s₁

theorem unitSpacelike_s₂ : UnitSpacelike (sp s₂) :=
  (unitSpacelike_sp_iff s₂).2 dot3_s₂_s₂

theorem unitSpacelike_s₃ : UnitSpacelike (sp s₃) :=
  (unitSpacelike_sp_iff s₃).2 dot3_s₃_s₃

theorem unitSpacelike_neg {s : Vec4} (hs : UnitSpacelike s) : UnitSpacelike (-s) := by
  obtain ⟨h1, h2⟩ := hs
  refine ⟨by rw [L4_neg_right, h1, neg_zero], ?_⟩
  obtain ⟨t, a, b, c⟩ := s
  simp [Q4] at h2 ⊢
  linarith

/-! ## The longitudinal embedding attached to a direction -/

/-- The longitudinal embedding attached to the pair `(e₀, s)`. -/
def iotaS (s : Vec4) (X : Long) : Vec4 := X.1 • e₀ + X.2 • s

@[simp] theorem iotaS_apply (s : Vec4) (X : Long) : iotaS s X = X.1 • e₀ + X.2 • s := rfl

theorem iotaS_add (s : Vec4) (X Y : Long) : iotaS s (X + Y) = iotaS s X + iotaS s Y := by
  simp [iotaS, add_smul]; abel

theorem iotaS_smul (c : ℝ) (s : Vec4) (X : Long) : iotaS s (c • X) = c • iotaS s X := by
  simp [iotaS, smul_add, smul_smul]

theorem iotaS_coord (s : Vec4) (X : Long) :
    iotaS s X = (X.1 * 1 + X.2 * s.1, X.2 • s.2) := by
  obtain ⟨t, x⟩ := X
  obtain ⟨s0, w⟩ := s
  simp [iotaS, e₀, Prod.ext_iff]

/-- **Every unit rest direction gives an exact 1+1 Lorentz embedding.** -/
theorem Q4_iotaS {s : Vec4} (hs : UnitSpacelike s) (X : Long) :
    Q4 (iotaS s X) = X.1 ^ 2 - X.2 ^ 2 := by
  obtain ⟨t, x⟩ := X
  obtain ⟨s0, a, b, c⟩ := s
  obtain ⟨h1, h2⟩ := hs
  simp [e₀] at h1
  subst h1
  simp [Q4] at h2
  simp [iotaS, e₀, Q4]
  nlinarith [h2]

/-- Equivalently, in terms of the Task-01/02 longitudinal form. -/
theorem Q4_iotaS_Q2 {s : Vec4} (hs : UnitSpacelike s) (X : Long) :
    Q4 (iotaS s X) = Q2 X := by
  rw [Q4_iotaS hs]; rfl

/-- **Polarized version.**  The embedding is an isometry for the bilinear forms. -/
theorem L4_iotaS {s : Vec4} (hs : UnitSpacelike s) (X Y : Long) :
    L4 (iotaS s X) (iotaS s Y) = NullSectorTask02.L2 X Y := by
  have hQ : ∀ Z : Long, Q4 (iotaS s Z) = Q2 Z := Q4_iotaS_Q2 hs
  have hadd : Q4 (iotaS s (X + Y)) = Q2 (X + Y) := hQ (X + Y)
  rw [iotaS_add] at hadd
  simp only [L4, NullSectorTask02.L2]
  rw [hadd, hQ X, hQ Y]

/-- The embedding is injective for a unit direction. -/
theorem iotaS_injective {s : Vec4} (hs : UnitSpacelike s) : Function.Injective (iotaS s) := by
  intro X Y hXY
  have h1 : L4 (iotaS s X) e₀ = L4 (iotaS s Y) e₀ := by rw [hXY]
  have h2 : L4 (iotaS s X) s = L4 (iotaS s Y) s := by rw [hXY]
  simp only [iotaS, L4_add_left, L4_smul_left] at h1 h2
  rw [L4_symm e₀ e₀] at h1
  have he : L4 e₀ e₀ = 1 := by simp [e₀]
  have hes : L4 s e₀ = 0 := by rw [L4_symm]; exact hs.1
  have hes' : L4 e₀ s = 0 := hs.1
  have hss : L4 s s = -1 := by rw [L4_self]; exact hs.2
  rw [he, hes] at h1
  rw [hes', hss] at h2
  apply Prod.ext
  · simpa using h1
  · have : X.2 * -1 = Y.2 * -1 := by linarith [h2]
    simpa using this

/-! ## The longitudinal product, imported from Task 02 -/

/-- Neutral Task-04 alias for the product reconstructed in Task 02 as the unique
bilinear, unital (`u₀`), `Q2`-multiplicative product on `Long`. -/
noncomputable def muLong : NullSectorTask02.BiProd := NullSectorTask02.recU

/-- `muLong` is admissible at `u₀` in the Task-02 sense. -/
theorem muLong_admissible : NullSectorTask02.AdmissibleAt NullSectorTask02.u₀ muLong :=
  NullSectorTask02.recU_admissible

/-- `muLong` is *the* Task-02 reconstruction: it is the unique admissible product
at `u₀`. -/
theorem muLong_unique {μ : NullSectorTask02.BiProd}
    (hμ : NullSectorTask02.AdmissibleAt NullSectorTask02.u₀ μ) : μ = muLong :=
  NullSectorTask02.fixedUnit_unique hμ muLong_admissible

@[simp] theorem muLong_apply (X Y : Long) :
    muLong X Y = (X.1 * Y.1 + X.2 * Y.2, X.1 * Y.2 + X.2 * Y.1) := rfl

theorem muLong_unit_left (X : Long) : muLong NullSectorTask02.u₀ X = X :=
  muLong_admissible.1.1 X

theorem muLong_unit_right (X : Long) : muLong X NullSectorTask02.u₀ = X :=
  muLong_admissible.1.2 X

theorem muLong_qmul (X Y : Long) : Q2 (muLong X Y) = Q2 X * Q2 Y :=
  muLong_admissible.2 X Y

theorem muLong_comm (X Y : Long) : muLong X Y = muLong Y X :=
  NullSectorTask02.fixedUnit_commutative muLong_admissible X Y

theorem muLong_assoc (X Y Z : Long) : muLong (muLong X Y) Z = muLong X (muLong Y Z) :=
  NullSectorTask02.fixedUnit_associative muLong_admissible X Y Z

/-! ## The sector product -/

/-- The product on the longitudinal plane `span(e₀,s)`, obtained by transporting
`muLong` through `iotaS s`. -/
noncomputable def sectorProd (s : Vec4) (X Y : Long) : Vec4 := iotaS s (muLong X Y)

@[simp] theorem sectorProd_apply (s : Vec4) (X Y : Long) :
    sectorProd s X Y = iotaS s (muLong X Y) := rfl

/-- The embedding for `-s` is the embedding for `s` with reversed second
coordinate. -/
theorem iotaS_neg (s : Vec4) (X : Long) : iotaS (-s) X = iotaS s (X.1, -X.2) := by
  simp [iotaS]

/-- The sector product depends only on the plane, not on the sign of `s`:
replacing `s` by `-s` reverses the coordinate and leaves the product unchanged. -/
theorem sectorProd_neg (s : Vec4) (X Y : Long) :
    sectorProd (-s) X Y = sectorProd s (X.1, -X.2) (Y.1, -Y.2) := by
  rw [sectorProd, sectorProd, iotaS_neg]
  congr 1
  apply Prod.ext <;> simp; ring


end NullSectorTask04
