import RequestProject.Experiment2.NullSectorTask06.SafeBase

/-!
# Task 06, Layer 1: the clean generic extension theorem (RE-DERIVED)

The generic theorem

```
SectorCompatible M  ↔  ∃ A, Alternating A ∧ M = extensionFromDefect A
```

exists in Task 04 only inside `NullSectorTask04.Classification`, which also
contains an explicit nonzero alternating witness.  In accordance with the
Task-06 contamination firewall that module is **not** imported; the generic
theorem is re-proved here from the safe base alone.

The codomain of the defect is the *full* carrier `Vec4`: nothing here assumes
that the defect is purely spatial.  (Whether the temporal output component must
vanish is a Phase-A rigidity question, answered later and only under a symmetry
hypothesis.)

Nothing in this file is a nonzero alternating map: `symForced` is symmetric,
`extensionFromDefect` and `defectOfProd` are constructions applied to an
*abstract* argument, and the only concrete defect appearing here is `0`.
-/

namespace NullSectorTask06

open NullSectorTask01 NullSectorTask04

/-! ## The forced symmetric branch -/

/-- The product obtained from the forced symmetric data alone (zero defect). -/
noncomputable def symForced : BiProd4 :=
  LinearMap.mk₂ ℝ
    (fun X Y => (X.1 * Y.1 + dot3 X.2 Y.2,
      X.1 * Y.2.1 + Y.1 * X.2.1, X.1 * Y.2.2.1 + Y.1 * X.2.2.1,
      X.1 * Y.2.2.2 + Y.1 * X.2.2.2))
    (by intro X₁ X₂ Y; apply vec4_ext <;> simp [dot3] <;> ring)
    (by intro c X Y; apply vec4_ext <;> simp [dot3] <;> ring)
    (by intro X Y₁ Y₂; apply vec4_ext <;> simp [dot3] <;> ring)
    (by intro c X Y; apply vec4_ext <;> simp [dot3] <;> ring)

@[simp] theorem symForced_apply (X Y : Vec4) :
    symForced X Y = (X.1 * Y.1 + dot3 X.2 Y.2,
      X.1 * Y.2.1 + Y.1 * X.2.1, X.1 * Y.2.2.1 + Y.1 * X.2.2.1,
      X.1 * Y.2.2.2 + Y.1 * X.2.2.2) := rfl

/-- Vector form of the forced symmetric branch. -/
theorem symForced_eq (X Y : Vec4) :
    symForced X Y = (X.1 * Y.1 + dot3 X.2 Y.2) • e₀ + X.1 • sp Y.2 + Y.1 • sp X.2 := by
  apply vec4_ext <;> simp [e₀, sp]

/-- Coordinate-free description of the forced symmetric branch. -/
theorem symForced_coordfree (X Y : Vec4) :
    symForced X Y = (L4 X e₀) • Y + (L4 Y e₀) • X - (L4 X Y) • e₀ := by
  apply vec4_ext <;> simp [e₀, dot3]; ring

theorem symForced_comm : Commutative4 symForced := by
  intro X Y; apply vec4_ext <;> simp [dot3] <;> ring

theorem symForced_rest (v w : Vec3) : symForced (sp v) (sp w) = (dot3 v w) • e₀ := by
  apply vec4_ext <;> simp [e₀, sp, dot3]

/-! ## Defect data -/

/-- A defect datum: a bilinear map on rest-space coordinates with values in the
**full** ambient carrier. -/
abbrev RestDefect : Type := Vec3 →ₗ[ℝ] Vec3 →ₗ[ℝ] Vec4

/-- The alternating condition on a defect. -/
def Alternating (A : RestDefect) : Prop := ∀ v, A v v = 0

theorem alternating_antisymm {A : RestDefect} (hA : Alternating A) (v w : Vec3) :
    A v w = - A w v := by
  have hvw := hA (v + w)
  simp only [map_add, LinearMap.add_apply] at hvw
  rw [hA v, hA w] at hvw
  have h0 : A v w + A w v = 0 := by rw [← hvw]; abel
  exact eq_neg_of_add_eq_zero_left h0

theorem alternating_zero : Alternating (0 : RestDefect) := by intro v; simp

/-- The global product attached to a defect datum. -/
noncomputable def extensionFromDefect (A : RestDefect) : BiProd4 :=
  LinearMap.mk₂ ℝ (fun X Y => symForced X Y + A X.2 Y.2)
    (by intro X₁ X₂ Y; simp only [Prod.snd_add, map_add, LinearMap.add_apply]; abel)
    (by intro c X Y; simp only [Prod.smul_snd, map_smul, LinearMap.smul_apply, smul_add])
    (by intro X Y₁ Y₂; simp only [Prod.snd_add, map_add]; abel)
    (by intro c X Y; simp only [Prod.smul_snd, map_smul, smul_add])

@[simp] theorem extensionFromDefect_apply (A : RestDefect) (X Y : Vec4) :
    extensionFromDefect A X Y = symForced X Y + A X.2 Y.2 := rfl

/-- The defect of a bilinear product: the rest-space block minus the forced
symmetric contribution. -/
noncomputable def defectOfProd (M : BiProd4) : RestDefect :=
  LinearMap.mk₂ ℝ (fun v w => M (sp v) (sp w) - (dot3 v w) • e₀)
    (by
      intro v₁ v₂ w
      dsimp only
      rw [sp_add, M_add_left, dot3_add_left, add_smul]; abel)
    (by
      intro c v w
      dsimp only
      rw [sp_smul, M_smul_left, dot3_smul_left, mul_smul, smul_sub])
    (by
      intro v w₁ w₂
      dsimp only
      rw [sp_add, M_add_right, dot3_add_right, add_smul]; abel)
    (by
      intro c v w
      dsimp only
      rw [sp_smul, M_smul_right, dot3_smul_right, mul_smul, smul_sub])

@[simp] theorem defectOfProd_apply (M : BiProd4) (v w : Vec3) :
    defectOfProd M v w = M (sp v) (sp w) - (dot3 v w) • e₀ := rfl

section
variable {M : BiProd4} (hM : SectorCompatible M)
include hM

/-- The defect of a sector-compatible product is alternating. -/
theorem defectOfProd_alternating : Alternating (defectOfProd M) := by
  intro v
  rw [defectOfProd_apply, M_rest_sq hM v, sub_self]

/-- A sector-compatible product is its forced symmetric part plus its defect. -/
theorem eq_extensionFromDefect : M = extensionFromDefect (defectOfProd M) := by
  apply LinearMap.ext; intro X; apply LinearMap.ext; intro Y
  rw [extensionFromDefect_apply, defectOfProd_apply, symForced_eq, M_expand hM X Y]
  module

end

/-- **Converse.**  Every alternating defect reconstructs a sector-compatible
product. -/
theorem extensionFromDefect_sectorCompatible {A : RestDefect} (hA : Alternating A) :
    SectorCompatible (extensionFromDefect A) := by
  intro s hs X Y
  obtain ⟨hsp, hd⟩ := unitSpacelike_spatial hs
  have hs1 : s.1 = 0 := by
    have := (unitSpacelike_iff s).1 hs
    exact (mem_Rest s).1 this.1
  have hiota : ∀ Z : Long, iotaS s Z = (Z.1, Z.2 • s.2) := by
    intro Z
    apply vec4_ext <;> simp [iotaS, e₀, hs1]
  have hA' : A (X.2 • s.2) (Y.2 • s.2) = 0 := by
    simp [hA s.2]
  rw [extensionFromDefect_apply, hiota X, hiota Y, hiota (muLong X Y)]
  rw [show ((X.1, X.2 • s.2) : Vec4).2 = X.2 • s.2 from rfl,
    show ((Y.1, Y.2 • s.2) : Vec4).2 = Y.2 • s.2 from rfl, hA', add_zero]
  apply vec4_ext
  · simp only [symForced_apply, muLong_apply]
    rw [dot3_smul_left, dot3_smul_right, hd]
    ring
  · simp [dot3]; ring
  · simp [dot3]; ring
  · simp [dot3]; ring

/-- **RE-DERIVED: the clean generic extension theorem.**  A bilinear product is
sector compatible if and only if it is the forced symmetric branch plus an
alternating rest-space defect. -/
theorem sectorCompatible_iff_defect (M : BiProd4) :
    SectorCompatible M ↔ ∃ A : RestDefect, Alternating A ∧ M = extensionFromDefect A := by
  constructor
  · intro hM
    exact ⟨defectOfProd M, defectOfProd_alternating hM, eq_extensionFromDefect hM⟩
  · rintro ⟨A, hA, rfl⟩
    exact extensionFromDefect_sectorCompatible hA

/-- The defect datum is uniquely determined by the product. -/
theorem defect_unique {A B : RestDefect} (h : extensionFromDefect A = extensionFromDefect B) :
    A = B := by
  apply LinearMap.ext; intro v; apply LinearMap.ext; intro w
  have := congrArg (fun (N : BiProd4) => N (sp v) (sp w)) h
  simp only [extensionFromDefect_apply, sp_snd] at this
  exact add_left_cancel this

/-- Recovering the defect from the reconstructed product. -/
theorem defectOfProd_extensionFromDefect (A : RestDefect) :
    defectOfProd (extensionFromDefect A) = A := by
  apply LinearMap.ext; intro v; apply LinearMap.ext; intro w
  rw [defectOfProd_apply, extensionFromDefect_apply, sp_snd, sp_snd, symForced_rest]
  abel

/-- The zero defect reproduces the symmetric branch. -/
theorem extensionFromDefect_zero : extensionFromDefect 0 = symForced := by
  apply LinearMap.ext; intro X; apply LinearMap.ext; intro Y
  simp

/-- The zero-defect branch is sector compatible. -/
theorem symForced_sectorCompatible : SectorCompatible symForced := by
  rw [← extensionFromDefect_zero]
  exact extensionFromDefect_sectorCompatible alternating_zero

/-! ## Symmetric and alternating parts of a sector-compatible product -/

/-- Symmetric part of a bilinear product. -/
noncomputable def SymPart (M : BiProd4) (X Y : Vec4) : Vec4 := (1/2 : ℝ) • (M X Y + M Y X)

/-- Alternating part of a bilinear product. -/
noncomputable def AltPart (M : BiProd4) (X Y : Vec4) : Vec4 := (1/2 : ℝ) • (M X Y - M Y X)

theorem sym_add_alt (M : BiProd4) (X Y : Vec4) : SymPart M X Y + AltPart M X Y = M X Y := by
  simp only [SymPart, AltPart, ← smul_add]
  rw [show M X Y + M Y X + (M X Y - M Y X) = (2 : ℝ) • M X Y by rw [two_smul]; abel]
  rw [smul_smul, show (1/2 : ℝ) * 2 = 1 by norm_num, one_smul]

section
variable {M : BiProd4} (hM : SectorCompatible M)
include hM

/-- **The symmetric part is completely forced by sector compatibility.** -/
theorem symPart_eq (X Y : Vec4) : SymPart M X Y = symForced X Y := by
  have hMX := eq_extensionFromDefect hM
  rw [SymPart, hMX]
  simp only [extensionFromDefect_apply]
  rw [symForced_comm Y X, alternating_antisymm (defectOfProd_alternating hM) Y.2 X.2]
  rw [show symForced X Y + defectOfProd M X.2 Y.2 + (symForced X Y + -defectOfProd M X.2 Y.2)
      = (2 : ℝ) • symForced X Y by rw [two_smul]; abel]
  rw [smul_smul, show (1/2 : ℝ) * 2 = 1 by norm_num, one_smul]

/-- **The remaining freedom is exactly the alternating part, supported on the
rest space.** -/
theorem altPart_eq (X Y : Vec4) : AltPart M X Y = defectOfProd M X.2 Y.2 := by
  have hMX := eq_extensionFromDefect hM
  have hxy : M X Y = symForced X Y + defectOfProd M X.2 Y.2 :=
    congrArg (fun N : BiProd4 => N X Y) hMX
  have hyx : M Y X = symForced Y X + defectOfProd M Y.2 X.2 :=
    congrArg (fun N : BiProd4 => N Y X) hMX
  rw [AltPart, hxy, hyx]
  rw [symForced_comm Y X, alternating_antisymm (defectOfProd_alternating hM) Y.2 X.2]
  rw [show symForced X Y + defectOfProd M X.2 Y.2 - (symForced X Y + -defectOfProd M X.2 Y.2)
      = (2 : ℝ) • defectOfProd M X.2 Y.2 by rw [two_smul]; abel]
  rw [smul_smul, show (1/2 : ℝ) * 2 = 1 by norm_num, one_smul]

end

/-! ## A defect is determined by its values on the three basis pairs -/

/-- An alternating defect vanishing on the three basis pairs is zero. -/
theorem alternating_eq_zero_of_basis {A : RestDefect} (hA : Alternating A)
    (h12 : A r₁ r₂ = 0) (h23 : A r₂ r₃ = 0) (h31 : A r₃ r₁ = 0) : A = 0 := by
  have h21 : A r₂ r₁ = 0 := by rw [alternating_antisymm hA, h12, neg_zero]
  have h32 : A r₃ r₂ = 0 := by rw [alternating_antisymm hA, h23, neg_zero]
  have h13 : A r₁ r₃ = 0 := by rw [alternating_antisymm hA, h31, neg_zero]
  apply LinearMap.ext; intro v; apply LinearMap.ext; intro w
  conv_lhs => rw [rest_basis_expansion v, rest_basis_expansion w]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.zero_apply, hA r₁, hA r₂, hA r₃, h12, h21, h23, h32, h13, h31,
    smul_zero, add_zero]

/-- **General bilinear expansion of an alternating defect.**  Every alternating
defect is determined by its three basis-pair values; this is pure bilinearity
and alternation, with no symmetry input and no explicit map. -/
theorem alternating_expand {A : RestDefect} (hA : Alternating A) (v w : Vec3) :
    A v w = (v.1 * w.2.1 - v.2.1 * w.1) • A r₁ r₂
      + (v.2.1 * w.2.2 - v.2.2 * w.2.1) • A r₂ r₃
      + (v.2.2 * w.1 - v.1 * w.2.2) • A r₃ r₁ := by
  conv_lhs => rw [rest_basis_expansion v, rest_basis_expansion w]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hA r₁, hA r₂, hA r₃, smul_zero]
  rw [alternating_antisymm hA r₂ r₁, alternating_antisymm hA r₃ r₂,
    alternating_antisymm hA r₁ r₃]
  module

/-- Two alternating defects agreeing on the three basis pairs are equal. -/
theorem alternating_ext {A B : RestDefect} (hA : Alternating A) (hB : Alternating B)
    (h12 : A r₁ r₂ = B r₁ r₂) (h23 : A r₂ r₃ = B r₂ r₃) (h31 : A r₃ r₁ = B r₃ r₁) :
    A = B := by
  have hAB : Alternating (A - B) := by
    intro v; simp only [LinearMap.sub_apply, hA v, hB v, sub_self]
  have := alternating_eq_zero_of_basis hAB
    (by simp only [LinearMap.sub_apply, h12, sub_self])
    (by simp only [LinearMap.sub_apply, h23, sub_self])
    (by simp only [LinearMap.sub_apply, h31, sub_self])
  exact sub_eq_zero.1 this

end NullSectorTask06
