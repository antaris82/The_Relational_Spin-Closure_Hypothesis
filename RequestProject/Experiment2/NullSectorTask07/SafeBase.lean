import RequestProject.Experiment2.NullSectorTask06.AssociativityObstruction

/-!
# Task 07, Layer 0: the inherited (safe) base

This module fixes the *inherited* mathematical data of Task 07 and introduces
the single neutral abbreviation `oldSq` for the diagonal square law that the
previous tasks proved to be forced on the original carrier.

## Import ledger (INHERITED)

The only import is `RequestProject.Experiment2.NullSectorTask06.AssociativityObstruction`,
whose transitive closure is

```
RequestProject.Experiment2.NullSectorTask01.Basic
RequestProject.Experiment2.NullSectorTask02.LorentzData
RequestProject.Experiment2.NullSectorTask02.CandidateProduct
RequestProject.Experiment2.NullSectorTask02.FixedUnit
RequestProject.Experiment2.NullSectorTask04.Lorentz4
RequestProject.Experiment2.NullSectorTask04.RestSpace
RequestProject.Experiment2.NullSectorTask04.Sectors
RequestProject.Experiment2.NullSectorTask04.GlobalExtension
RequestProject.Experiment2.NullSectorTask06.SafeBase
RequestProject.Experiment2.NullSectorTask06.GenericExtension
RequestProject.Experiment2.NullSectorTask06.AssociativityObstruction
```

In particular none of the Task-06 *late conventional identification* modules
(`Task06.Identification`, `Task06.Task04Comparison`) and none of the Task-04
identification modules are imported anywhere in the Task-07 core.

Inherited declarations actually used:

* `NullSectorTask01.Vec4`, `NullSectorTask01.Q4`;
* `NullSectorTask04.L4`, `NullSectorTask04.e₀`, `NullSectorTask04.Rest`,
  `NullSectorTask04.Vec3`, `NullSectorTask04.sp`, `NullSectorTask04.dot3`,
  `NullSectorTask04.vec4_ext`, `NullSectorTask04.vec4_decomp`;
* `NullSectorTask04.BiProd4`, `NullSectorTask04.SectorCompatible`,
  `NullSectorTask04.Associative4`, and the forced consequences
  `M_unit_left`, `M_unit_right`, `M_rest_sq`, `M_rest_symm`, `M_expand`;
* `NullSectorTask06.symForced` (the forced symmetric product `μsym`),
  `NullSectorTask06.r₁`, `NullSectorTask06.r₂`;
* `NullSectorTask06.no_associative_sectorCompatible` (the universal Task-06
  associativity obstruction — INPUT MOTIVATION only).
-/

namespace NullSectorTask07

open NullSectorTask01 NullSectorTask04 NullSectorTask06

/-! ## The forced symmetric product, under a neutral Task-07 name -/

/-- `μsym`: the symmetric product forced on the original carrier by the family
of longitudinal sectors.  This is *not* a new Task-07 definition; it is the
inherited `NullSectorTask06.symForced`. -/
noncomputable abbrev musym : BiProd4 := symForced

/-! ## The forced diagonal square law -/

/-- **Neutral notation for the inherited square law.**  `oldSq X` is the value
that *every* sector-compatible product must assign to `X ⋆ X`. -/
noncomputable def oldSq (X : Vec4) : Vec4 := musym X X

/-- `oldSq X = μsym X X` (definitional, recorded as a theorem because the audit
refers to it). -/
theorem oldSq_eq_musym (X : Vec4) : oldSq X = musym X X := rfl

/-- **Coordinate form of the inherited square law.**  For `X = (t, v)`,
`oldSq X = (t² + h(v,v), 2t • v)`. -/
theorem oldSq_apply (X : Vec4) :
    oldSq X = (X.1 * X.1 + dot3 X.2 X.2,
      2 * X.1 * X.2.1, 2 * X.1 * X.2.2.1, 2 * X.1 * X.2.2.2) := by
  apply vec4_ext <;> simp [oldSq, musym] <;> ring

/-- Vector form of the inherited square law. -/
theorem oldSq_vector (X : Vec4) :
    oldSq X = (X.1 * X.1 + dot3 X.2 X.2) • e₀ + (2 * X.1) • sp X.2 := by
  rw [oldSq_apply]; apply vec4_ext <;> simp [e₀, sp]

/-- The time component of the inherited square law is a sum of real squares. -/
theorem oldSq_time (X : Vec4) : (oldSq X).1 = X.1 * X.1 + dot3 X.2 X.2 := by
  rw [oldSq_apply]

/-- **Elementary real positivity.**  The time component of an inherited square
is never negative. -/
theorem oldSq_time_nonneg (X : Vec4) : 0 ≤ (oldSq X).1 := by
  rw [oldSq_time]
  nlinarith [dot3_self_nonneg X.2, sq_nonneg X.1]

/-- The square of a rest vector. -/
theorem oldSq_sp (v : Vec3) : oldSq (sp v) = (dot3 v v) • e₀ := by
  rw [oldSq_apply]; apply vec4_ext <;> simp [e₀, sp]

/-- `e₀` is an idempotent for the inherited square law. -/
@[simp] theorem oldSq_e₀ : oldSq e₀ = e₀ := by
  rw [oldSq_apply]; apply vec4_ext <;> simp [e₀]

/-! ## `oldSq` really is the square law of every sector-compatible product -/

/-- **INHERITED (Task 04 / Task 06).**  Every sector-compatible bilinear product
on the original carrier has *the same* diagonal, namely `oldSq`. -/
theorem sectorCompatible_sq {M : BiProd4} (hM : SectorCompatible M) (X : Vec4) :
    M X X = oldSq X := by
  have hexp := M_expand hM X X
  rw [M_rest_sq hM X.2] at hexp
  rw [hexp, oldSq_vector]
  module

/-! ## The inherited impossibility (INPUT MOTIVATION) -/

/-- **INHERITED Task-06 no-go.**  There is no associative bilinear product
`Vec4 × Vec4 → Vec4` retaining the inherited sector-compatible rules.  Task 07
does not re-prove this; it is restated here as the motivation for changing the
codomain-closure assumption. -/
theorem inherited_no_associative_closure :
    ¬ ∃ M : BiProd4, SectorCompatible M ∧ Associative4 M :=
  not_exists_associative_sectorCompatible

/-! ## The two orthogonal spatial directions used throughout Task 07 -/

/-- First selected spatial direction (a rest-space unit vector). -/
def dirA : Vec4 := sp r₁

/-- Second selected spatial direction (a rest-space unit vector, orthogonal to
`dirA`).  **No third spatial direction is introduced anywhere in Task 07.** -/
def dirB : Vec4 := sp r₂

@[simp] theorem L4_e₀_dirA : L4 e₀ dirA = 0 := by simp [dirA, sp]

@[simp] theorem L4_e₀_dirB : L4 e₀ dirB = 0 := by simp [dirB, sp]

@[simp] theorem Q4_dirA : Q4 dirA = -1 := by simp [dirA, s₁]

@[simp] theorem Q4_dirB : Q4 dirB = -1 := by simp [dirB, s₂]

@[simp] theorem L4_dirA_dirB : L4 dirA dirB = 0 := by simp [dirA, dirB, sp, s₁, s₂]

theorem dirA_mem_Rest : dirA ∈ Rest := sp_mem_Rest _

theorem dirB_mem_Rest : dirB ∈ Rest := sp_mem_Rest _

/-- Inherited square of the first direction. -/
@[simp] theorem oldSq_dirA : oldSq dirA = e₀ := by
  rw [dirA, oldSq_sp]; norm_num [s₁]

/-- Inherited square of the second direction. -/
@[simp] theorem oldSq_dirB : oldSq dirB = e₀ := by
  rw [dirB, oldSq_sp]; norm_num [s₂]

/-- Inherited symmetric product of the two directions. -/
@[simp] theorem musym_dirA_dirB : musym dirA dirB = 0 := by
  rw [dirA, dirB, symForced_rest]; norm_num [s₁, s₂]

/-- **The three chosen vectors of the original carrier are linearly
independent** (needed later, and proved here by pure coordinates). -/
theorem e₀_dirA_dirB_indep {α β γ : ℝ} (hz : α • e₀ + β • dirA + γ • dirB = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  have h1 := congrArg (fun X : Vec4 => X.1) hz
  have h2 := congrArg (fun X : Vec4 => X.2.1) hz
  have h3 := congrArg (fun X : Vec4 => X.2.2.1) hz
  simp [e₀, dirA, dirB, sp, s₁, s₂] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

end NullSectorTask07
