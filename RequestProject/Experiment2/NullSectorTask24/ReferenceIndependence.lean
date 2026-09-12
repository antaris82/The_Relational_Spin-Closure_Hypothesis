import RequestProject.Experiment2.NullSectorTask24.FrameTorsor

/-!
# Task 24, Package F: a reference frame coordinatizes, it does not define

**Hard target B.**

Only now (item 39) is a reference frame chosen.  It produces a *coordinate* bijection
`Gvis ≃ FramePlus` (items 40–42); a second reference frame produces a second one, and the two
differ exactly by translation by the unique visible transformation carrying the first
reference frame to the second (items 44, 45).  The conceptual endpoint (items 46, 47) is that
all reference choices give canonically equivalent coordinate presentations, while the carrier
`FramePlus` itself was defined in Package B without any reference frame.

Item 43 (topological strengthening) is deliberately **not** pursued: the visible carrier
carries its inherited topology, but no topology on `FramePlus` was inherited, and building
one would be a new development.  This is recorded as an unresolved obligation, not as a
failure.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask24

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21 NullSectorTask23

/-- **NEWLY DEFINED (item 40).**  The coordinate map attached to a reference frame. -/
noncomputable def coord (F₀ : FramePlus) (g : Gvis) : FramePlus := g • F₀

@[simp] theorem coord_apply (F₀ : FramePlus) (g : Gvis) : coord F₀ g = g • F₀ := rfl

@[simp] theorem coord_one (F₀ : FramePlus) : coord F₀ 1 = F₀ := one_smul _ _

theorem coord_injective (F₀ : FramePlus) : Function.Injective (coord F₀) := fun _ _ h =>
  frameAction_cancel h

theorem coord_surjective (F₀ : FramePlus) : Function.Surjective (coord F₀) := fun F =>
  frameAction_transitive F₀ F

/-- **PACKAGE F (item 41), principal.**  The coordinate map is bijective. -/
theorem coord_bijective (F₀ : FramePlus) : Function.Bijective (coord F₀) :=
  ⟨coord_injective F₀, coord_surjective F₀⟩

/-- **PACKAGE F (item 42), principal endpoint.**  The reference-frame coordinate
equivalence. -/
noncomputable def coordEquiv (F₀ : FramePlus) : Gvis ≃ FramePlus :=
  Equiv.ofBijective (coord F₀) (coord_bijective F₀)

@[simp] theorem coordEquiv_apply (F₀ : FramePlus) (g : Gvis) : coordEquiv F₀ g = g • F₀ := rfl

theorem coordEquiv_symm_apply (F₀ F : FramePlus) : (coordEquiv F₀).symm F = frameHom F₀ F := by
  refine (coordEquiv F₀).injective ?_
  rw [Equiv.apply_symm_apply, coordEquiv_apply, frameHom_smul]

/-! ## Change of reference (items 44, 45) -/

/-- **PACKAGE F (item 45), principal.**  The two coordinate maps attached to two reference
frames differ exactly by translation by the unique visible transformation carrying the first
reference frame to the second. -/
theorem coord_change (F₀ F₁ : FramePlus) (g : Gvis) :
    coord F₁ g = coord F₀ (g * frameHom F₀ F₁) := by
  rw [coord_apply, coord_apply, mul_smul, frameHom_smul]

theorem coordEquiv_change (F₀ F₁ : FramePlus) :
    coordEquiv F₁ = (Equiv.mulRight (frameHom F₀ F₁)).trans (coordEquiv F₀) :=
  Equiv.ext fun g => coord_change F₀ F₁ g

/-- **PACKAGE F.**  In transition form: the composite of one coordinate presentation with the
inverse of another is exactly right translation. -/
theorem coordEquiv_transition (F₀ F₁ : FramePlus) (g : Gvis) :
    (coordEquiv F₀).symm (coordEquiv F₁ g) = g * frameHom F₀ F₁ := by
  rw [coordEquiv_symm_apply]
  refine (frameHom_unique ?_).symm
  exact (coord_change F₀ F₁ g).symm

/-- **PACKAGE F (items 46, 47), principal endpoint.**  For any two reference frames there is
exactly one visible transformation intertwining the two coordinate presentations; hence all
reference choices give canonically equivalent presentations, and the reference frame
coordinatizes `FramePlus` rather than defining it. -/
theorem reference_independence (F₀ F₁ : FramePlus) :
    ∃! k : Gvis, ∀ g : Gvis, coord F₁ g = coord F₀ (g * k) := by
  refine ⟨frameHom F₀ F₁, coord_change F₀ F₁, fun k hk => ?_⟩
  have h1 := hk 1
  rw [coord_one, one_mul, coord_apply] at h1
  exact (frameHom_unique h1.symm)

/-! ## Negative control (item 75) -/

/-- **NEGATIVE CONTROL (item 75).**  The coordinate presentation genuinely depends on the
reference frame: distinct reference frames give distinct coordinate maps.  The existence of a
reference equivalence therefore does not make any reference frame intrinsic. -/
theorem coord_ne_of_ne {F₀ F₁ : FramePlus} (h : F₀ ≠ F₁) : coord F₀ ≠ coord F₁ := by
  intro hEq
  exact h (by simpa using congrFun hEq 1)

end NullSectorTask24
