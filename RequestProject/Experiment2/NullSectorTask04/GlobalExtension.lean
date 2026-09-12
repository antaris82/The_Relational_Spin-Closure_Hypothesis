import RequestProject.Experiment2.NullSectorTask04.Sectors

/-!
# Task 04, Layer 4: unknown global bilinear products and sector compatibility

An unknown real bilinear map on the ambient carrier is carried by
`LinearMap.BilinMap ℝ Vec4 Vec4`; bilinearity is therefore part of the carrier
and is never an extra hypothesis.

The only hypothesis imposed is `SectorCompatible`: the product restricts, in
every longitudinal 1+1 sector `span(e₀,s)`, to the product reconstructed in
Task 02.  No commutativity, associativity, unit, multiplicativity, or
covariance is assumed.

Everything proved here is a *consequence* of sector compatibility.
-/

namespace NullSectorTask04

open NullSectorTask01

/-- Carrier of an unknown real bilinear product on `Vec4`. -/
abbrev BiProd4 : Type := LinearMap.BilinMap ℝ Vec4 Vec4

/-- The principal Task-04 input: the product restricts to the reconstructed
longitudinal product in **every** longitudinal sector. -/
def SectorCompatible (M : BiProd4) : Prop :=
  ∀ s : Vec4, UnitSpacelike s → ∀ X Y : Long, M (iotaS s X) (iotaS s Y) = iotaS s (muLong X Y)

/-- `M` is commutative. -/
def Commutative4 (M : BiProd4) : Prop := ∀ X Y, M X Y = M Y X

/-- `M` is associative. -/
def Associative4 (M : BiProd4) : Prop := ∀ X Y Z, M (M X Y) Z = M X (M Y Z)

/-- `M` is `Q4`-multiplicative. -/
def Q4Multiplicative (M : BiProd4) : Prop := ∀ X Y, Q4 (M X Y) = Q4 X * Q4 Y

/-- `e₀` is a two-sided unit for `M`. -/
def GlobalUnit (M : BiProd4) : Prop := (∀ X, M e₀ X = X) ∧ (∀ X, M X e₀ = X)

/-! ## Elementary bilinear bookkeeping -/

@[simp] theorem M_smul_left (M : BiProd4) (c : ℝ) (X Y : Vec4) :
    M (c • X) Y = c • M X Y := by simp

@[simp] theorem M_smul_right (M : BiProd4) (c : ℝ) (X Y : Vec4) :
    M X (c • Y) = c • M X Y := by simp

@[simp] theorem M_add_left (M : BiProd4) (X Y Z : Vec4) :
    M (X + Y) Z = M X Z + M Y Z := by simp

@[simp] theorem M_add_right (M : BiProd4) (X Y Z : Vec4) :
    M X (Y + Z) = M X Y + M X Z := by simp

/-! ## Every ambient vector lies in some longitudinal sector -/

theorem iotaS_u₀ (s : Vec4) : iotaS s NullSectorTask02.u₀ = e₀ := by
  simp [iotaS, NullSectorTask02.u₀]

theorem iotaS_s₀ (s : Vec4) : iotaS s NullSectorTask02.s₀ = s := by
  simp [iotaS, NullSectorTask02.s₀]

/-- Any rest vector is a scalar multiple of a unit direction, with the scalar
squaring to its Euclidean square. -/
theorem exists_rest_rep (v : Vec3) :
    ∃ (r : ℝ) (s : Vec4), UnitSpacelike s ∧ sp v = r • s ∧ dot3 v v = r ^ 2 := by
  by_cases hv : v = 0
  · refine ⟨0, sp s₁, unitSpacelike_s₁, ?_, ?_⟩
    · simp [hv, sp]
    · simp [hv]
  · obtain ⟨r, s, hr, hs, hrs⟩ := exists_unitSpacelike_of_ne_zero hv
    refine ⟨r, s, hs, hrs, ?_⟩
    obtain ⟨hsp, hd⟩ := unitSpacelike_spatial hs
    have hv2 : v = r • s.2 := by
      have : sp v = sp (r • s.2) := by rw [hrs, sp_smul, ← hsp]
      exact sp_injective this
    rw [hv2, dot3_smul_left, dot3_smul_right, hd]
    ring

/-- **Every ambient vector belongs to a longitudinal sector.** -/
theorem exists_sector_rep (X : Vec4) :
    ∃ (s : Vec4) (Y : Long), UnitSpacelike s ∧ X = iotaS s Y := by
  obtain ⟨r, s, hs, hsp, _⟩ := exists_rest_rep X.2
  refine ⟨s, (X.1, r), hs, ?_⟩
  rw [iotaS]
  simp only []
  rw [← hsp]
  exact vec4_decomp X

/-! ## The global unit is derived, not assumed -/

section
variable {M : BiProd4} (hM : SectorCompatible M)
include hM

theorem M_e₀_e₀ : M e₀ e₀ = e₀ := by
  have := hM (sp s₁) unitSpacelike_s₁ NullSectorTask02.u₀ NullSectorTask02.u₀
  rw [iotaS_u₀] at this
  rw [this, muLong_unit_left, iotaS_u₀]

/-- **GLOBAL UNIT: DERIVED (left).** -/
theorem M_unit_left (X : Vec4) : M e₀ X = X := by
  obtain ⟨s, Y, hs, rfl⟩ := exists_sector_rep X
  rw [← iotaS_u₀ s, hM s hs, muLong_unit_left]

/-- **GLOBAL UNIT: DERIVED (right).** -/
theorem M_unit_right (X : Vec4) : M X e₀ = X := by
  obtain ⟨s, Y, hs, rfl⟩ := exists_sector_rep X
  rw [← iotaS_u₀ s, hM s hs, muLong_unit_right]

theorem M_globalUnit : GlobalUnit M := ⟨M_unit_left hM, M_unit_right hM⟩

/-- The square of a unit spatial direction is forced to be `e₀`. -/
theorem M_unit_spacelike_sq {s : Vec4} (hs : UnitSpacelike s) : M s s = e₀ := by
  have := hM s hs NullSectorTask02.s₀ NullSectorTask02.s₀
  rw [iotaS_s₀] at this
  rw [this]
  have : muLong NullSectorTask02.s₀ NullSectorTask02.s₀ = NullSectorTask02.u₀ := by
    apply Prod.ext <;> simp [NullSectorTask02.s₀, NullSectorTask02.u₀]
  rw [this, iotaS_u₀]

/-- **Pure spatial squares.**  For an arbitrary rest vector (not only a unit one)
the square is forced. -/
theorem M_rest_sq (v : Vec3) : M (sp v) (sp v) = (dot3 v v) • e₀ := by
  obtain ⟨r, s, hs, hsp, hd⟩ := exists_rest_rep v
  rw [hsp, M_smul_left, M_smul_right, M_unit_spacelike_sq hM hs, hd, smul_smul]
  ring_nf

/-- Coordinate-free restatement of the previous theorem. -/
theorem M_rest_sq' {X : Vec4} (hX : X ∈ Rest) : M X X = (h X X) • e₀ := by
  rw [rest_eq_sp hX, M_rest_sq hM, h_sp]

/-- **Polarization between distinct spatial directions.**  Sector compatibility
fixes exactly the symmetric combination. -/
theorem M_rest_symm (v w : Vec3) :
    M (sp v) (sp w) + M (sp w) (sp v) = (2 * dot3 v w) • e₀ := by
  have hvw := M_rest_sq hM (v + w)
  rw [sp_add] at hvw
  rw [M_add_left, M_add_right, M_add_right] at hvw
  rw [M_rest_sq hM v, M_rest_sq hM w] at hvw
  have hd : dot3 (v + w) (v + w) = dot3 v v + (2 * dot3 v w) + dot3 w w := by
    simp only [dot3_apply]
    obtain ⟨a, b, c⟩ := v; obtain ⟨a', b', c'⟩ := w
    simp; ring
  rw [hd, add_smul, add_smul] at hvw
  linear_combination (norm := abel) hvw

/-- **Complete bilinear expansion of a sector-compatible product.**  Everything
except the rest-space block is determined. -/
theorem M_expand (X Y : Vec4) :
    M X Y = (X.1 * Y.1) • e₀ + X.1 • sp Y.2 + Y.1 • sp X.2 + M (sp X.2) (sp Y.2) := by
  conv_lhs => rw [vec4_decomp X, vec4_decomp Y]
  rw [M_add_left, M_add_right, M_add_right, M_smul_left, M_smul_left, M_smul_right,
    M_smul_right, M_e₀_e₀ hM]
  rw [M_unit_left hM (sp Y.2), M_unit_right hM (sp X.2)]
  rw [smul_smul]
  abel

end

end NullSectorTask04
