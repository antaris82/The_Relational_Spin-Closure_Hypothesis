import RequestProject.Experiment2.NullSectorTask04.GlobalExtension

/-!
# Task 06, Layer 0: the safe (uncontaminated) base

This module fixes the inherited mathematical data of Task 06.  It imports
exactly one module, `RequestProject.Experiment2.NullSectorTask04.GlobalExtension`, whose
transitive import closure is

```
RequestProject.Experiment2.NullSectorTask01.Basic
RequestProject.Experiment2.NullSectorTask02.LorentzData
RequestProject.Experiment2.NullSectorTask02.CandidateProduct
RequestProject.Experiment2.NullSectorTask02.FixedUnit
RequestProject.Experiment2.NullSectorTask04.Lorentz4
RequestProject.Experiment2.NullSectorTask04.RestSpace
RequestProject.Experiment2.NullSectorTask04.Sectors
RequestProject.Experiment2.NullSectorTask04.GlobalExtension
```

None of these modules contains an explicit nonzero alternating bilinear map on
the three-dimensional rest space, and none of them contains any of the Task-04
witness or isotropy declarations listed in the audit.  The Task-04 modules
`Classification`, `IdentityAudit`, `Isotropy`, `ProperIsotropy`, `Overlap`,
`Identification` and `Task04` are **not** imported anywhere in the Phase-A clean
reconstruction; the only Task-06 module that imports any of them is
`Task06.Task04Comparison`, the late comparison layer.

## Inherited declarations (INPUT)

* `NullSectorTask01.Vec4`, `NullSectorTask01.Q4`, `NullSectorTask01.Long`,
  `NullSectorTask01.Q2`;
* `NullSectorTask04.L4` and its bilinearity/symmetry lemmas, `NullSectorTask04.e₀`;
* `NullSectorTask04.Rest`, `NullSectorTask04.Vec3`, `NullSectorTask04.sp`,
  `NullSectorTask04.dot3`, `NullSectorTask04.h`, `NullSectorTask04.s₁/s₂/s₃`;
* `NullSectorTask04.UnitSpacelike`, `NullSectorTask04.iotaS`,
  `NullSectorTask04.muLong` (the independently reconstructed 1+1 product);
* `NullSectorTask04.BiProd4`, `NullSectorTask04.SectorCompatible`,
  `NullSectorTask04.Commutative4`, `NullSectorTask04.Associative4`,
  `NullSectorTask04.Q4Multiplicative`, `NullSectorTask04.GlobalUnit`, and the
  consequences of sector compatibility proved in `GlobalExtension`
  (`M_unit_left`, `M_unit_right`, `M_rest_sq`, `M_rest_symm`, `M_expand`, ...).

Everything else used by Task 06 is re-derived inside the Task-06 namespace.

## Fresh Task-06 material in this file

Only coordinate infrastructure: componentwise extensionality for spatial
coordinates, the neutral names `r₁, r₂, r₃` for the orthonormal rest basis, and
its orthonormality and expansion lemmas.  No multiplication table is assumed on
`r₁, r₂, r₃`.
-/

namespace NullSectorTask06

open NullSectorTask01 NullSectorTask04

/-! ## Componentwise extensionality -/

/-- Componentwise extensionality for spatial coordinates. -/
theorem vec3_ext {v w : Vec3} (h1 : v.1 = w.1) (h2 : v.2.1 = w.2.1) (h3 : v.2.2 = w.2.2) :
    v = w := by
  obtain ⟨a, b, c⟩ := v; obtain ⟨a', b', c'⟩ := w; simp_all

/-! ## The orthonormal rest basis (coordinate infrastructure only) -/

/-- First rest-basis direction. -/
abbrev r₁ : Vec3 := s₁
/-- Second rest-basis direction. -/
abbrev r₂ : Vec3 := s₂
/-- Third rest-basis direction. -/
abbrev r₃ : Vec3 := s₃

@[simp] theorem dot3_r₁_r₂ : dot3 r₁ r₂ = 0 := by norm_num [s₁, s₂]
@[simp] theorem dot3_r₂_r₁ : dot3 r₂ r₁ = 0 := by norm_num [s₁, s₂]
@[simp] theorem dot3_r₁_r₃ : dot3 r₁ r₃ = 0 := by norm_num [s₁, s₃]
@[simp] theorem dot3_r₃_r₁ : dot3 r₃ r₁ = 0 := by norm_num [s₁, s₃]
@[simp] theorem dot3_r₂_r₃ : dot3 r₂ r₃ = 0 := by norm_num [s₂, s₃]
@[simp] theorem dot3_r₃_r₂ : dot3 r₃ r₂ = 0 := by norm_num [s₂, s₃]

/-- Expansion of a spatial vector in the rest basis. -/
theorem rest_basis_expansion (v : Vec3) : v = v.1 • r₁ + v.2.1 • r₂ + v.2.2 • r₃ := by
  obtain ⟨a, b, c⟩ := v; apply vec3_ext <;> simp [s₁, s₂, s₃]

/-- The rest basis directions are unit spacelike. -/
theorem unitSpacelike_r₁ : UnitSpacelike (sp r₁) := unitSpacelike_s₁
theorem unitSpacelike_r₂ : UnitSpacelike (sp r₂) := unitSpacelike_s₂
theorem unitSpacelike_r₃ : UnitSpacelike (sp r₃) := unitSpacelike_s₃

end NullSectorTask06
