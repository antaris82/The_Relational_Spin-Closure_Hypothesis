import RequestProject.Experiment2.NullSectorTask12.HalfAngleRelation
import RequestProject.Experiment2.NullSectorTask12.CentralAction
import RequestProject.Experiment2.NullSectorTask12.CarrierEndomorphisms

/-!
# Task 13, Layer 0: the inherited (safe) base

## Import ledger (INHERITED)

The imports of this module are the three Task-12 reconstruction modules

* `RequestProject.Experiment2.NullSectorTask12.HalfAngleRelation`
  (which itself brings in `Task12.SafeBase → LeftCarrier → GeneratedCarrier →
  DimensionClassification → MinimalCarrier → CarrierFamily → AxisRelation` and the
  inherited `Task10.HalfAngleSectors`),
* `RequestProject.Experiment2.NullSectorTask12.CentralAction`,
* `RequestProject.Experiment2.NullSectorTask12.CarrierEndomorphisms`.

Transitively this is exactly the uncontaminated chain

`Task01 → Task04 → Task06 → Task07 → Task08.FullVec4Embedding → Task09.SafeBase →
 … → Task09.Existence → Task10.SafeBase → Task10.AxisDecomposition →
 Task10.OldAxialRotation → Task10.AlgebraExtension → Task10.HalfAngleSectors →
 Task12.SafeBase → … → Task12.CarrierEndomorphisms`.

In particular **no `Identification` (late comparison) module of any earlier task** is
reachable from any Task-13 reconstruction module, and the Task-10/Task-11 explicit lifts
are *not* reachable from here: the reference lift `Uref` first enters in
`RequestProject.Experiment2.NullSectorTask13.ReferenceRestriction`, strictly after the arbitrary
minimal carrier and its slices have been defined (§12, §46).

Inherited data actually used in Task 13:

* the associative carrier `W`, the product `⋆`, the unit `w1`, associativity and the
  complete derived multiplication table (INHERITED, Task 08);
* the exact center `Z = spanℝ{w1, wS}`, `wS ⋆ wS = -w1` (INHERITED, Task 09);
* the axial algebra-automorphism family `Phi` (INHERITED, Task 10);
* the axis-relative sectors `SectorPlus = {ψ | wA ⋆ ψ = ψ}`,
  `SectorMinus = {ψ | wA ⋆ ψ = -ψ}` (INHERITED, Task 10);
* left carriers, minimal left carriers, `Lgen`, `Zspan`, `StabL`, the trace identity,
  the carrier equivalence `CarrierEquiv` and the internal endomorphism layer
  (INHERITED, Task 12).

## Firewalls

*Experiment-1 firewall (§2)*: no construction, theorem, name or file of Experiment 1 is
used anywhere in Task 13.

*Conventional-representation firewall (§3)*: no spinor, `ℂ²`, Pauli, `SU(2)`, `Spin`,
projective- or spin-representation notion occurs in the reconstruction core.  The single
module `Task13.Identification` is labelled COMPARISON ONLY and is imported by nothing but
`Task13.Task13`.

*Physical-target firewall (§4)*: none of the forbidden words of §4 occurs as a
construction, an import or a target anywhere in Task 13.

*Full-rotation firewall (§5)*: only the already inherited one-parameter axial family
about the already selected axis `wA` occurs; no second spatial direction is rotated, no
rotation group, no boost and no carrier-level Lorentz action is constructed.

## Content of this module

Bookkeeping only: neutral names for the two inherited axis-relative sectors, and the
inherited central normal form together with its arithmetic.
-/

namespace NullSectorTask13

open NullSectorTask08 NullSectorTask09 NullSectorTask10 NullSectorTask12

/-! ## Neutral names for the inherited axis-relative sectors -/

/-- **INHERITED (§6).**  The plus sector of the selected axis: `{ψ | A ⋆ ψ = ψ}`. -/
abbrev Hplus : Submodule ℝ W := SectorPlus

/-- **INHERITED (§6).**  The minus sector of the selected axis: `{ψ | A ⋆ ψ = -ψ}`. -/
abbrev Hminus : Submodule ℝ W := SectorMinus

theorem mem_Hplus_iff (ψ : W) : ψ ∈ Hplus ↔ wA ⋆ ψ = ψ := mem_SectorPlus_iff_axis ψ

theorem mem_Hminus_iff (ψ : W) : ψ ∈ Hminus ↔ wA ⋆ ψ = -ψ := mem_SectorMinus_iff_axis ψ

/-- **INHERITED.**  On the plus sector the transverse channel `R` acts as the central
element `S`. -/
theorem wR_mul_eq_wS_mul_of_mem_Hplus {ψ : W} (hψ : ψ ∈ Hplus) : wR ⋆ ψ = wS ⋆ ψ :=
  (mem_SectorPlus_iff ψ).1 hψ

/-- **INHERITED.**  On the minus sector the transverse channel `R` acts as `-S`. -/
theorem wR_mul_eq_neg_wS_mul_of_mem_Hminus {ψ : W} (hψ : ψ ∈ Hminus) :
    wR ⋆ ψ = -(wS ⋆ ψ) := (mem_SectorMinus_iff ψ).1 hψ

/-! ## The inherited central normal form -/

/-- **INHERITED NORMAL FORM.**  The element `a • 1 + b • S` of the exact center.  (The
same normal form as in Tasks 09–11; it is reproduced here so that the Task-13
reconstruction core does not import a Task-11 module before §12.) -/
noncomputable def zz (a b : ℝ) : W := a • w1 + b • wS

@[simp] theorem zz_coord_0 (a b : ℝ) : zz a b 0 = a := by simp [zz, w1, wS]
@[simp] theorem zz_coord_7 (a b : ℝ) : zz a b 7 = b := by simp [zz, w1, wS]

@[simp] theorem zz_one_zero : zz 1 0 = w1 := by
  funext i; fin_cases i <;> simp [zz, w1, wS]

theorem zz_mem_Z (a b : ℝ) : zz a b ∈ Z := smul_add_smul_mem_Z a b

theorem mem_Z_iff_zz (z : W) : z ∈ Z ↔ ∃ a b : ℝ, z = zz a b := by
  constructor
  · intro hz
    obtain ⟨a, b, rfl⟩ := (mem_Z_iff z).1 hz
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩; exact zz_mem_Z a b

theorem zz_mul_zz (a b c d : ℝ) :
    zz a b ⋆ zz c d = zz (a * c - b * d) (a * d + b * c) := by
  funext i; fin_cases i <;> simp [zz, w1, wS]

theorem zz_mul (a b : ℝ) (ψ : W) : zz a b ⋆ ψ = a • ψ + b • (wS ⋆ ψ) := by
  rw [zz, add_mul_W, smul_mul_W, smul_mul_W, one_mul_W]

theorem zz_central (a b : ℝ) (x : W) : zz a b ⋆ x = x ⋆ zz a b :=
  Z_central (zz_mem_Z a b) x

/-- **DERIVED.**  A central element is zero exactly when both of its coefficients
vanish. -/
theorem zz_eq_zero_iff (a b : ℝ) : zz a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 7⟩
  · rintro ⟨rfl, rfl⟩
    funext i; fin_cases i <;> simp [zz, w1, wS]

end NullSectorTask13
