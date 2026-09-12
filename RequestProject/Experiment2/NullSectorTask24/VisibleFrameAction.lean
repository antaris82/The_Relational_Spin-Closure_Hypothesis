import RequestProject.Experiment2.NullSectorTask24.IntrinsicFrames

/-!
# Task 24, Package C: the visible action on the intrinsic frame carrier

Items 25–29.  The action is defined by acting with the inherited visible action on each of
the three frame vectors; orthonormality and positive orientation are preserved (these are the
two preservation theorems of Package A), and the group-action laws are exactly the inherited
laws of the visible action on `E`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask24

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21 NullSectorTask23

/-- **DERIVED (item 26).**  The visible action preserves exact orthonormality. -/
theorem gact_orthonormalTriple (g : Gvis) {f : Fin 3 → E} (h : IsOrthonormalTriple f) :
    IsOrthonormalTriple fun i => gact g (f i) := by
  intro i j
  rw [gact_ip]
  exact h i j

/-- **DERIVED (item 27).**  The visible action preserves positive orientation. -/
theorem gact_positivelyOriented (g : Gvis) {f : Fin 3 → E} (h : IsPositivelyOriented f) :
    IsPositivelyOriented fun i => gact g (f i) := by
  have := gact_triple g (f 0) (f 1) (f 2)
  show 0 < triple (gact g (f 0)) (gact g (f 1)) (gact g (f 2))
  rw [this]
  exact h

/-- **NEWLY DEFINED (item 25).**  The action of a visible transformation on a frame. -/
noncomputable def frameSmul (g : Gvis) (F : FramePlus) : FramePlus :=
  ⟨fun i => gact g (F.vec i), gact_orthonormalTriple g F.2.1, gact_positivelyOriented g F.2.2⟩

noncomputable instance : SMul Gvis FramePlus := ⟨frameSmul⟩

@[simp] theorem frameSmul_vec (g : Gvis) (F : FramePlus) (i : Fin 3) :
    (g • F).vec i = gact g (F.vec i) := rfl

/-- **DERIVED (items 28, 29).**  The group-action laws. -/
noncomputable instance : MulAction Gvis FramePlus where
  one_smul F := FramePlus.ext fun i => by simp
  mul_smul g g' F := FramePlus.ext fun i => by simp [gact_mul]

theorem frame_one_smul (F : FramePlus) : (1 : Gvis) • F = F := one_smul _ _

theorem frame_mul_smul (g g' : Gvis) (F : FramePlus) : (g * g') • F = g • (g' • F) :=
  mul_smul g g' F

end NullSectorTask24
