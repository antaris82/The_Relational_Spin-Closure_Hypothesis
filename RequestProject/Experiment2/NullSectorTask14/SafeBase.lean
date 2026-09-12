import RequestProject.Experiment2.NullSectorTask13.SelectionAudit
import RequestProject.Experiment2.NullSectorTask11.CenterRigidity

/-!
# Task 14, Layer 0: the inherited (safe) base

## Import ledger (INHERITED)

The imports are

* `RequestProject.Experiment2.NullSectorTask13.SelectionAudit`, whose transitive closure is the whole
  uncontaminated Task-08 → Task-13 reconstruction chain
  (`Task08.FullVec4Embedding → Task09.Existence → Task10.HalfAngleSectors →
  Task11.GeneratorSeparation → Task12.CarrierEndomorphisms → Task13.FixedCarrierLocus`);
* `RequestProject.Experiment2.NullSectorTask11.CenterRigidity`, the exact-center theorem, imported
  explicitly because Task 14 uses it as a *named dependency* in the word-defect analysis
  (§14, §45).

**No `Identification` (late comparison) module of any earlier task is reachable from any
Task-14 reconstruction module.**  The single Task-14 comparison module
`RequestProject.Experiment2.NullSectorTask14.Identification` is imported by nothing but
`RequestProject.Experiment2.NullSectorTask14.Task14`.

## Inherited data actually used

* the associative carrier `W` with product `⋆`, unit `w1`, associativity and the complete
  derived multiplication table (INHERITED, Task 08);
* the old carrier `Vec4`, its rest space `Rest`, the inherited positive spatial form
  `dot3`, the three old spatial directions `dirA, dirB, dirC` and the embedding
  `iota3` (INHERITED, Tasks 01/04/08);
* the exact center `Z = spanℝ{w1, wS}` with `wS ⋆ wS = -w1` and the exact-center theorem
  `center_eq_Z` (INHERITED, Tasks 09/11);
* the A-axis old rotation `rot`, its unique algebra extension `Phi`, and the A-axis
  reference implementer `Ustd = Uref` (INHERITED, Tasks 10/11);
* left carriers, minimal left carriers, `Lgen`, `esph`, the sphere parametrization
  `minimal_eq_Lgen_esph` and the carrier equivalence `CarrierEquiv`
  (INHERITED, Tasks 12/13).

## Firewalls

*Experiment-1 firewall (§2).*  No construction, theorem, name or file of Experiment 1 is
used anywhere in Task 14.

*Conventional full-rotation firewall (§3).*  None of the conventional full-rotation
targets listed in §3 of the task occurs as a target, definition, proof shortcut, theorem
name or import in any Task-14 reconstruction module.  Recognition of such structures is
confined to `Task14.Identification`, labelled COMPARISON ONLY.

*Physical firewall (§4).*  None of the forbidden physical words of §4 occurs as a
construction, an import or a target anywhere in Task 14.  A spatial direction is selected
as an algebraic direction only.

*No-full-spatial-structure firewall (§5).*  Task 14 begins with two *separately*
reconstructed one-axis systems.  A generic-axis system is constructed only in Phase II
(§35), from data derived in Phase I.

## Content of this module

Bookkeeping only: the embedding of old spatial vectors into the carrier, the inherited
spatial form under a neutral name, the elementary symmetric relations used throughout, and
a restatement of the exact-center theorem.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08 NullSectorTask09
open NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13

/-! ## Old spatial vectors inside the carrier -/

/-- **INHERITED (notation).**  The inherited positive spatial form, written `h`. -/
abbrev h3 (n m : Vec3) : ℝ := dot3 n m

/-- **INHERITED (notation).**  The image in the carrier of an old spatial vector.  This is
the inherited embedding `iota3` applied to the inherited spatial inclusion `sp`; no new
structure is introduced. -/
noncomputable def spat (n : Vec3) : W := iota3 (sp n)

@[simp] theorem spat_coord_0 (n : Vec3) : spat n 0 = 0 := rfl
@[simp] theorem spat_coord_1 (n : Vec3) : spat n 1 = n.1 := rfl
@[simp] theorem spat_coord_2 (n : Vec3) : spat n 2 = n.2.1 := rfl
@[simp] theorem spat_coord_3 (n : Vec3) : spat n 3 = n.2.2 := rfl
@[simp] theorem spat_coord_4 (n : Vec3) : spat n 4 = 0 := rfl
@[simp] theorem spat_coord_5 (n : Vec3) : spat n 5 = 0 := rfl
@[simp] theorem spat_coord_6 (n : Vec3) : spat n 6 = 0 := rfl
@[simp] theorem spat_coord_7 (n : Vec3) : spat n 7 = 0 := rfl

theorem spat_add (n m : Vec3) : spat (n + m) = spat n + spat m := by
  funext i; fin_cases i <;> simp [spat, sp]

theorem spat_smul (a : ℝ) (n : Vec3) : spat (a • n) = a • spat n := by
  funext i; fin_cases i <;> simp [spat, sp]

@[simp] theorem spat_wA : spat (1, 0, 0) = wA := by
  funext i; fin_cases i <;> simp [spat, sp, wA]

@[simp] theorem spat_wB : spat (0, 1, 0) = wB := by
  funext i; fin_cases i <;> simp [spat, sp, wB]

@[simp] theorem spat_wC : spat (0, 0, 1) = wC := by
  funext i; fin_cases i <;> simp [spat, sp, wC]

theorem spat_eq_zero_iff (n : Vec3) : spat n = 0 ↔ n = 0 := by
  constructor
  · intro hn
    have h1 := congrFun hn 1
    have h2 := congrFun hn 2
    have h3 := congrFun hn 3
    simp only [spat_coord_1, spat_coord_2, spat_coord_3] at h1 h2 h3
    simp only [Prod.ext_iff]
    exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩
  · rintro rfl
    funext i; fin_cases i <;> simp [spat, sp]

/-! ## The inherited symmetric relations -/

/-- **INHERITED (polarization of the old square law, Task 08).**  The anticommutator of
two embedded old spatial vectors is twice the inherited spatial form. -/
theorem spat_anticomm (n m : Vec3) :
    spat n ⋆ spat m + spat m ⋆ spat n = (2 * h3 n m) • w1 := by
  funext i; fin_cases i <;> simp [wit8MulFun, w1, dot3] <;> ring

/-- **INHERITED.**  The square of an embedded spatial vector is the inherited spatial
form. -/
theorem spat_sq (n : Vec3) : spat n ⋆ spat n = (h3 n n) • w1 := by
  funext i; fin_cases i <;> simp [wit8MulFun, w1, dot3] <;> ring

/-- **INHERITED.**  Two `h`-orthogonal spatial directions anticommute. -/
theorem spat_anticomm_of_orth {n m : Vec3} (hnm : h3 n m = 0) :
    spat n ⋆ spat m = -(spat m ⋆ spat n) := by
  have hsum := spat_anticomm n m
  rw [hnm, mul_zero, zero_smul] at hsum
  exact eq_neg_of_add_eq_zero_left hsum

/-! ## The exact center, restated -/

/-- **INHERITED (Task 11, `center_eq_Z`).**  An element commuting with the whole carrier
lies in the exact center. -/
theorem mem_Z_of_comm_all {z : W} (hz : ∀ x : W, z ⋆ x = x ⋆ z) : z ∈ Z := by
  have hmem : z ∈ CenterW := hz
  rwa [center_eq_Z] at hmem

/-- **INHERITED (Task 11).**  Conversely every central element commutes with everything. -/
theorem comm_all_of_mem_Z {z : W} (hz : z ∈ Z) (x : W) : z ⋆ x = x ⋆ z := Z_central hz x

/-- **INHERITED (Task 11), packaged.**  Exact characterization of the center. -/
theorem comm_all_iff_mem_Z (z : W) : (∀ x : W, z ⋆ x = x ⋆ z) ↔ z ∈ Z :=
  ⟨mem_Z_of_comm_all, fun hz => comm_all_of_mem_Z hz⟩

end NullSectorTask14
