import RequestProject.Experiment2.NullSectorTask08.DirectWitness

/-!
# Task 08, Layer 11: the full old-carrier embedding — critical theorem

The direct witness goes further than the Task-07 one: the **complete** original
carrier embeds into it, linearly and injectively, in such a way that the
inherited old square law holds for *every* old vector, and polarization then
recovers the whole inherited symmetric product.

This closes the proof gap explicitly left open by Task 07, namely the
non-vacuity of the full ambient-extension hypothesis set.
-/

namespace NullSectorTask08

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07

/-! ## The embedding -/

/-- **THE FULL OLD-CARRIER EMBEDDING.**  `e₀ ↦ 1, a ↦ A, b ↦ B, c ↦ C`, extended
linearly. -/
def iota3 : Vec4 →ₗ[ℝ] Wit8 where
  toFun X := ![X.1, X.2.1, X.2.2.1, X.2.2.2, 0, 0, 0, 0]
  map_add' := by intro X Y; funext i; fin_cases i <;> simp
  map_smul' := by intro c X; funext i; fin_cases i <;> simp

@[simp] theorem iota3_apply (X : Vec4) :
    iota3 X = ![X.1, X.2.1, X.2.2.1, X.2.2.2, 0, 0, 0, 0] := rfl

@[simp] theorem iota3_e₀ : iota3 e₀ = w1 := by
  funext i; fin_cases i <;> simp [e₀, w1]

@[simp] theorem iota3_dirA : iota3 dirA = wA := by
  funext i; fin_cases i <;> simp [dirA, sp, s₁, wA]

@[simp] theorem iota3_dirB : iota3 dirB = wB := by
  funext i; fin_cases i <;> simp [dirB, sp, s₂, wB]

@[simp] theorem iota3_dirC : iota3 dirC = wC := by
  funext i; fin_cases i <;> simp [dirC, sp, s₃, wC]

/-- **INJECTIVE.**  The full old carrier embeds injectively. -/
theorem iota3_injective : Function.Injective iota3 := by
  intro X Y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  apply vec4_ext
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3

/-! ## Square preservation for every old vector -/

/-- **CRITICAL TASK-08 THEOREM.**  The inherited old square law holds for every
embedded old vector of the complete original carrier. -/
theorem iota3_oldSq (X : Vec4) : iota3 (oldSq X) = wit8Mul (iota3 X) (iota3 X) := by
  funext i
  fin_cases i <;> simp [oldSq_apply, dot3] <;> ring

/-- The same statement in the `PreservesOldSquares` form of the abstract
ambient-extension interface. -/
theorem iota3_preservesOldSquares : PreservesOldSquares wit8Mul iota3 := by
  intro X; exact (iota3_oldSq X).symm

/-! ## The ambient-extension witness -/

/-- **EXISTENCE WITNESS FOR THE FULL AMBIENT INTERFACE.**  The eight-dimensional
carrier, with the derived product, the derived unit and the full old-carrier
embedding, is an ambient extension in exactly the abstract sense used in Tasks
07 and 08. -/
def wit8Ambient : AmbientExt Wit8 where
  mul := wit8Mul
  oneE := w1
  assoc := wit8Associative
  unit := wit8TwoSidedUnit
  iota := iota3
  iota_inj := iota3_injective
  iota_e₀ := iota3_e₀
  oldsq := iota3_preservesOldSquares

@[simp] theorem wit8Ambient_mul : wit8Ambient.mul = wit8Mul := rfl
@[simp] theorem wit8Ambient_oneE : wit8Ambient.oneE = w1 := rfl
@[simp] theorem wit8Ambient_iota : wit8Ambient.iota = iota3 := rfl

/-- The two Task-07 generators of the witness ambient extension are the witness
basis elements, and so is the Task-08 third generator. -/
theorem wit8Ambient_generators :
    wit8Ambient.genA = wA ∧ wit8Ambient.genB = wB ∧ genC wit8Ambient = wC := by
  refine ⟨?_, ?_, ?_⟩
  · rw [AmbientExt.genA, wit8Ambient_iota, iota3_dirA]
  · rw [AmbientExt.genB, wit8Ambient_iota, iota3_dirB]
  · rw [genC, wit8Ambient_iota, iota3_dirC]

/-- **THERE EXISTS A REAL ASSOCIATIVE AMBIENT EXTENSION OF THE COMPLETE OLD
`Vec4` CARRIER PRESERVING THE INHERITED OLD SQUARE LAW.** -/
theorem ambient_existence : Nonempty (AmbientExt Wit8) := ⟨wit8Ambient⟩

/-- The same statement spelled out: a bilinear associative unital product, an
injective linear embedding of the complete original carrier sending the future
unit to the ambient unit, and retention of the inherited square law for every
old vector. -/
theorem ambient_existence_explicit :
    ∃ (m : Wit8 →ₗ[ℝ] Wit8 →ₗ[ℝ] Wit8) (u : Wit8) (j : Vec4 →ₗ[ℝ] Wit8),
      AssociativeE m ∧ TwoSidedUnitE m u ∧ Function.Injective j ∧ j e₀ = u ∧
        ∀ X : Vec4, m (j X) (j X) = j (oldSq X) :=
  ⟨wit8Mul, w1, iota3, wit8Associative, wit8TwoSidedUnit, iota3_injective,
    iota3_e₀, iota3_preservesOldSquares⟩

/-! ## Recovery of the full old symmetric product -/

/-- **POLARIZATION RECOVERS THE FULL OLD SYMMETRIC PRODUCT.**  For arbitrary old
vectors the anticommutator of the embedded vectors is twice the embedded
inherited symmetric product.  Proved here by polarizing the full square
preservation theorem. -/
theorem iota3_symmetric_product (X Y : Vec4) :
    wit8Mul (iota3 X) (iota3 Y) + wit8Mul (iota3 Y) (iota3 X)
      = (2 : ℝ) • iota3 (musym X Y) :=
  wit8Ambient.polarization X Y

/-- The witness therefore reproduces the complete previously reconstructed
symmetric product structure of the old carrier, not merely a three-generator
fragment. -/
theorem iota3_full_old_structure :
    Function.Injective iota3 ∧
    (∀ X : Vec4, iota3 (oldSq X) = wit8Mul (iota3 X) (iota3 X)) ∧
    (∀ X Y : Vec4, wit8Mul (iota3 X) (iota3 Y) + wit8Mul (iota3 Y) (iota3 X)
      = (2 : ℝ) • iota3 (musym X Y)) :=
  ⟨iota3_injective, iota3_oldSq, iota3_symmetric_product⟩

end NullSectorTask08
