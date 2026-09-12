import RequestProject.Experiment2.NullSectorTask09.Existence

/-!
# Task 10, Layer 0: the inherited (safe) base

## Import ledger (INHERITED)

The single import is `RequestProject.Experiment2.NullSectorTask09.Existence`, hence the
uncontaminated chain

`Task01 → Task04 → Task06 → Task07 → Task08.FullVec4Embedding →
 Task09.SafeBase → Task09.RealScalarNoGo → Task09.CentralPlane →
 Task09.UnknownQuadraticMap → Task09.Rigidity → Task09.Existence`.

In particular **no** identification / late-comparison module of any earlier
task (`Task04.Identification`, `Task06.Identification`,
`Task07.Identification`, `Task08.Identification`, `Task09.Identification`) is
imported by any Task-10 reconstruction module.  They enter, if at all, only in
`RequestProject.Experiment2.NullSectorTask10.Identification`, which is imported by nothing
but the top-level `Task10.lean`.  No Task-05 module exists in the project.

Inherited data actually used in Task 10:

* the associative carrier `W = Wit8 = Fin 8 → ℝ` with the bilinear product
  `wit8Mul` (notation `⋆`), the two-sided unit `w1` and associativity;
* the eight derived basis elements `w1, wA, wB, wC, wP, wQ, wR, wS` and the
  complete derived multiplication table;
* the injective linear embedding `iota3 : Vec4 →ₗ[ℝ] W` with
  `iota3_e₀, iota3_dirA, iota3_dirB, iota3_dirC`;
* the old Lorentz form `Q4`, its polarization `L4`, the rest space `Rest`, the
  Euclidean rest form `dot3` and the three old spatial directions
  `dirA, dirB, dirC`;
* the internally derived central plane `Z = spanℝ{w1, wS}` of Task 09 together
  with its multiplication rule and centrality;
* the two Task-09 central-valued quadratic branches `Ncand 1` and `Ncand (-1)`
  (`N₊` and `N₋`), used only in the branch-compatibility theorem.

## Representation-target firewall

None of the words `spin`, `spinor`, `helicity`, `photon`, `fermion`, `Pauli`,
`SU(2)`, `Spin(3)`, `double cover`, `Weyl`, `Dirac`, `polarization vector`,
`Jones vector` occurs as a construction, an import or a target in any Task-10
reconstruction module.  They may appear only in the final module
`Identification.lean`, always labelled `COMPARISON ONLY`.

## Content of this module

Purely bookkeeping: the eight-coefficient normal form of an arbitrary carrier
element, and the resulting extensionality principle for real-linear maps on the
carrier.  Nothing new is assumed.
-/

namespace NullSectorTask10

open NullSectorTask01 NullSectorTask04 NullSectorTask07 NullSectorTask08
open NullSectorTask09

/-! ## Coordinates of the derived basis -/

@[simp] theorem w1_coords : (w1 0 = 1) ∧ (w1 1 = 0) := by constructor <;> simp [w1]

/-- **NORMAL FORM (INHERITED).**  Every carrier element is its coordinate
combination of the eight derived basis elements. -/
theorem basis_expand (x : W) :
    x = x 0 • w1 + x 1 • wA + x 2 • wB + x 3 • wC
      + x 4 • wP + x 5 • wQ + x 6 • wR + x 7 • wS := by
  funext i
  fin_cases i <;> simp [w1, wA, wB, wC, wP, wQ, wR, wS]

/-- **EXTENSIONALITY.**  A real-linear map on the carrier is determined by its
values on the eight derived basis elements. -/
theorem linMap_ext {f g : W →ₗ[ℝ] W}
    (h1 : f w1 = g w1) (hA : f wA = g wA) (hB : f wB = g wB) (hC : f wC = g wC)
    (hP : f wP = g wP) (hQ : f wQ = g wQ) (hR : f wR = g wR) (hS : f wS = g wS) :
    f = g := by
  refine LinearMap.ext fun x => ?_
  conv_lhs => rw [basis_expand x]
  conv_rhs => rw [basis_expand x]
  simp only [map_add, map_smul, h1, hA, hB, hC, hP, hQ, hR, hS]

/-- A carrier element is zero iff all eight coordinates vanish. -/
theorem eq_zero_iff_coords (x : W) :
    x = 0 ↔ x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧
             x 4 = 0 ∧ x 5 = 0 ∧ x 6 = 0 ∧ x 7 = 0 := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    funext i
    fin_cases i <;> assumption

end NullSectorTask10
