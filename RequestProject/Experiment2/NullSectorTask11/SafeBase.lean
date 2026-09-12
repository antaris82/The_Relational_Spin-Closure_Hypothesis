import RequestProject.Experiment2.NullSectorTask10.AlgebraExtension

/-!
# Task 11, Layer 0: the inherited (safe) base

## Import ledger (INHERITED)

The single import of this module is `RequestProject.Experiment2.NullSectorTask10.AlgebraExtension`,
hence the uncontaminated chain

`Task01 → Task04 → Task06 → Task07 → Task08.FullVec4Embedding →
 Task09.SafeBase → Task09.RealScalarNoGo → Task09.CentralPlane →
 Task09.UnknownQuadraticMap → Task09.Rigidity → Task09.Existence →
 Task10.SafeBase → Task10.AxisDecomposition → Task10.OldAxialRotation →
 Task10.AlgebraExtension`.

In particular **no identification / late-comparison module** of any earlier task
is reachable from any Task-11 reconstruction module, and — as demanded by §5 of
the task — the Task-10 module `InternalLift`, which contains the explicit
reference lift `Ustd`, is **not** imported here.  It first enters in
`RequestProject.Experiment2.NullSectorTask11.ReferenceExistence`, strictly after the upper
classification has been established.

Inherited data actually used in Task 11:

* the associative carrier `W` with the bilinear product `⋆`, the two-sided unit
  `w1`, associativity and the complete derived multiplication table of the eight
  derived basis elements `w1, wA, wB, wC, wP, wQ, wR, wS` (INHERITED, Task 08);
* the central two-plane `Z = spanℝ{w1, wS}` with `wS ⋆ wS = -w1` and its
  centrality (INHERITED, Task 09);
* the two central quadratic branches `Ncand 1 = N₊` and `Ncand (-1) = N₋`
  together with their coefficient functions `nRe, nSc` (INHERITED, Task 09) —
  used only in the explicitly *conditional* compatibility layer;
* the axial algebra-automorphism family `Phi : ℝ → (W →ₗ[ℝ] W)` with
  `Phi 0 = id`, `Phi (θ+φ) = Phi θ ∘ Phi φ` and bijectivity (INHERITED,
  Task 10).

## Firewalls

*Experiment-1 firewall*: no construction, theorem, name or file of Experiment 1
is used anywhere in Task 11.

*Physical-target firewall*: none of the forbidden target words of §2 occurs as a
construction, an import or a target in any Task-11 module.

*Conventional-algebra firewall*: no `Complex`, `ℂ`, `Matrix`, determinant,
complex phase, projective representation, unitary group, `Spin` group, `SU(2)`
or Clifford-group notion is used in the reconstruction core.  The final module
`Identification.lean` is labelled `COMPARISON ONLY` and is imported by nothing
except the top-level `Task11.lean`.

## Content of this module

Bookkeeping only: a normal form for elements of the inherited central plane, its
arithmetic, and the elementary coordinate lemmas used throughout.  Nothing new
is assumed.
-/

namespace NullSectorTask11

open NullSectorTask08 NullSectorTask09 NullSectorTask10

/-! ## Normal form in the inherited central plane -/

/-- **INHERITED NORMAL FORM.**  The element of the central two-plane with
coefficients `a` (on the unit) and `b` (on the derived central element `S`). -/
noncomputable def zc (a b : ℝ) : W := a • w1 + b • wS

@[simp] theorem zc_coord_0 (a b : ℝ) : zc a b 0 = a := by simp [zc, w1, wS]
@[simp] theorem zc_coord_7 (a b : ℝ) : zc a b 7 = b := by simp [zc, w1, wS]

@[simp] theorem zc_coord_1 (a b : ℝ) : zc a b 1 = 0 := by simp [zc, w1, wS]
@[simp] theorem zc_coord_2 (a b : ℝ) : zc a b 2 = 0 := by simp [zc, w1, wS]
@[simp] theorem zc_coord_3 (a b : ℝ) : zc a b 3 = 0 := by simp [zc, w1, wS]
@[simp] theorem zc_coord_4 (a b : ℝ) : zc a b 4 = 0 := by simp [zc, w1, wS]
@[simp] theorem zc_coord_5 (a b : ℝ) : zc a b 5 = 0 := by simp [zc, w1, wS]
@[simp] theorem zc_coord_6 (a b : ℝ) : zc a b 6 = 0 := by simp [zc, w1, wS]

@[simp] theorem zc_one_zero : zc 1 0 = w1 := by
  funext i; fin_cases i <;> simp [zc, w1, wS]

theorem zc_mem_Z (a b : ℝ) : zc a b ∈ Z := smul_add_smul_mem_Z a b

theorem zc_injective {a b a' b' : ℝ} (h : zc a b = zc a' b') : a = a' ∧ b = b' :=
  Z_coeff_unique h

/-- **INHERITED.**  The multiplication rule of the central plane. -/
theorem zc_mul_zc (a b c d : ℝ) :
    zc a b ⋆ zc c d = zc (a * c - b * d) (a * d + b * c) :=
  central_mul_rule a b c d

/-- **INHERITED.**  Every element of the central plane commutes with everything. -/
theorem zc_central (a b : ℝ) (x : W) : zc a b ⋆ x = x ⋆ zc a b :=
  Z_central (zc_mem_Z a b) x

theorem zc_smul (r a b : ℝ) : r • zc a b = zc (r * a) (r * b) := by
  simp only [zc, smul_add, smul_smul]

theorem zc_add (a b c d : ℝ) : zc a b + zc c d = zc (a + c) (b + d) := by
  simp only [zc]; module

/-- A central element is determined by its two surviving coordinates. -/
theorem eq_zc_of_mem_Z {x : W} (hx : x ∈ Z) : x = zc (x 0) (x 7) := by
  obtain ⟨a, b, rfl⟩ := (mem_Z_iff x).1 hx
  show _ = zc _ _
  rw [show (a • w1 + b • wS) 0 = a from by simp [w1, wS],
    show (a • w1 + b • wS) 7 = b from by simp [w1, wS]]
  rfl

end NullSectorTask11
