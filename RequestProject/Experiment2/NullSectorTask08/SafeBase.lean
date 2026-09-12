import RequestProject.Experiment2.NullSectorTask07.Minimality

/-!
# Task 08, Layer 0: the inherited (safe) base

Task 08 adds **exactly one** further inherited spatial direction to the
two-generator system reconstructed in Task 07.  This module fixes the old
carrier data of the complete three-direction rest-space system and records the
import ledger.

## Import ledger (INHERITED)

The only import is `RequestProject.Experiment2.NullSectorTask07.Minimality`, whose
transitive closure is

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
RequestProject.Experiment2.NullSectorTask07.SafeBase
RequestProject.Experiment2.NullSectorTask07.AmbientExtension
RequestProject.Experiment2.NullSectorTask07.Polarization
RequestProject.Experiment2.NullSectorTask07.TwoDirections
RequestProject.Experiment2.NullSectorTask07.MixedProduct
RequestProject.Experiment2.NullSectorTask07.NewDirection
RequestProject.Experiment2.NullSectorTask07.ForcedRelations
RequestProject.Experiment2.NullSectorTask07.GeneratedClosure
RequestProject.Experiment2.NullSectorTask07.Minimality
```

In particular:

* `RequestProject.Experiment2.NullSectorTask07.Identification` (the Task-07 late
  conventional identification layer) is **not** reachable from any Task-08
  reconstruction module;
* no Task-05 module is imported anywhere in the project;
* the Task-06 late identification and comparison modules are not reachable
  either.

Inherited declarations actually used in Task 08:

* `NullSectorTask01.Vec4`, `NullSectorTask01.Q4`;
* `NullSectorTask04.L4`, `e₀`, `sp`, `dot3`, `Vec3`, `Rest`, `vec4_ext`;
* `NullSectorTask06.r₁`, `r₂`, `r₃`, `symForced`;
* `NullSectorTask07.oldSq`, `musym`, `dirA`, `dirB`, `AmbientExt` and all of its
  derived two-generator theorems up to and including `Gsub_least`.
-/

namespace NullSectorTask08

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07

/-! ## The third inherited spatial direction (old carrier datum) -/

/-- **INPUT.**  The third inherited rest-space direction of the fixed original
carrier.  No fourth spatial direction is introduced anywhere in Task 08. -/
def dirC : Vec4 := sp r₃

/-! ## The complete inherited orthogonality and normalization data -/

@[simp] theorem L4_e₀_dirC : L4 e₀ dirC = 0 := by simp [dirC, sp]

@[simp] theorem Q4_dirC : Q4 dirC = -1 := by simp [dirC, s₃]

@[simp] theorem L4_dirA_dirC : L4 dirA dirC = 0 := by
  simp [dirA, dirC, sp, s₁, s₃]

@[simp] theorem L4_dirB_dirC : L4 dirB dirC = 0 := by
  simp [dirB, dirC, sp, s₂, s₃]

theorem dirC_mem_Rest : dirC ∈ Rest := sp_mem_Rest _

/-- **INHERITED DATA (summary).**  The complete list of relations required by
the Task-08 statement of the old carrier: the future unit is orthogonal to all
three spatial directions, each spatial direction is normalized, and the three
spatial directions are mutually orthogonal. -/
theorem old_carrier_data :
    L4 e₀ dirA = 0 ∧ L4 e₀ dirB = 0 ∧ L4 e₀ dirC = 0 ∧
    Q4 dirA = -1 ∧ Q4 dirB = -1 ∧ Q4 dirC = -1 ∧
    L4 dirA dirB = 0 ∧ L4 dirA dirC = 0 ∧ L4 dirB dirC = 0 :=
  ⟨L4_e₀_dirA, L4_e₀_dirB, L4_e₀_dirC, Q4_dirA, Q4_dirB, Q4_dirC,
    L4_dirA_dirB, L4_dirA_dirC, L4_dirB_dirC⟩

/-! ## Inherited square and symmetric-product values -/

/-- Inherited square of the third direction. -/
@[simp] theorem oldSq_dirC : oldSq dirC = e₀ := by
  rw [dirC, oldSq_sp]; norm_num [s₃]

/-- Inherited symmetric product of the first and third directions. -/
@[simp] theorem musym_dirA_dirC : musym dirA dirC = 0 := by
  rw [dirA, dirC, symForced_rest]; norm_num [s₁, s₃]

/-- Inherited symmetric product of the second and third directions. -/
@[simp] theorem musym_dirB_dirC : musym dirB dirC = 0 := by
  rw [dirB, dirC, symForced_rest]; norm_num [s₂, s₃]

/-! ## Independence of the four selected old vectors -/

/-- **INHERITED.**  The four selected vectors of the original carrier are
linearly independent (transparent coordinate proof). -/
theorem e₀_dir_indep {α β γ δ : ℝ}
    (hz : α • e₀ + β • dirA + γ • dirB + δ • dirC = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 ∧ δ = 0 := by
  have h1 := congrArg (fun X : Vec4 => X.1) hz
  have h2 := congrArg (fun X : Vec4 => X.2.1) hz
  have h3 := congrArg (fun X : Vec4 => X.2.2.1) hz
  have h4 := congrArg (fun X : Vec4 => X.2.2.2) hz
  simp [e₀, dirA, dirB, dirC, sp, s₁, s₂, s₃] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- The coordinate description of the three inherited spatial directions. -/
theorem dir_coords :
    dirA = (0, 1, 0, 0) ∧ dirB = (0, 0, 1, 0) ∧ dirC = (0, 0, 0, 1) :=
  ⟨rfl, rfl, rfl⟩

end NullSectorTask08
