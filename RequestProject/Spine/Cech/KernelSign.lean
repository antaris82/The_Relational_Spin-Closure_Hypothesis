import RequestProject.Spine.Cech.Cohomology
import RequestProject.Spine.E2.Cech.Coboundary

/-!
# Task 6, WP5 : the kernel `{±1}` written additively as `ℤ₂`

The Task-3 defect takes its values in the kernel `ker ρ` of the internal projection, a
*multiplicative* group; the Čech complex of WP2–WP4 has *additive* coefficients `ZMod 2`.  This
module fixes, once and for all, the dictionary between the two, and it does so as **data**, not
as a silent convention change:

`CechSpinZ2.KernelSign P` bundles a sign map `sgn : L → ℤ₂` together with its inverse
`ofZ : ℤ₂ → ker ρ` and the two laws that make it a group isomorphism `ker ρ ≅ ℤ₂`:

* `sgn (u * v) = sgn u + sgn v` for kernel elements — **multiplication becomes addition**;
* `sgn 1 = 0` (derived) — **the neutral element `+1` becomes `0`**;
* `ofZ 1` is the nontrivial kernel element, so in the Spin instance `-1` becomes `1`.

`KernelSign.kerMulEquiv` packages this as a genuine `MulEquiv` `ker ρ ≃* Multiplicative ℤ₂`,
and `KernelSign.sgn_injOn` / `sgn_eq_zero_iff` record that the dictionary loses no information.

Nothing here refers to Spin: the datum is stated for an arbitrary
`NullSectorTask28.InternalProjection`.  The instance for the intrinsic Spin projection is
`RequestProject.Spine.Cech.SpinKernelSign`, which *reuses* the Task-4 sign map
`LorentzFrames.spinSign` rather than introducing a second one.
-/

namespace CechSpinZ2

open NullSectorTask28

universe u v

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G]

/-- **WP5, principal.**  The canonical additive presentation of the kernel of an internal
projection: a group isomorphism `ker ρ ≅ ℤ₂`, given as a sign map with an inverse. -/
structure KernelSign (P : InternalProjection L G) where
  /-- The sign of an element, as an element of `ℤ/2`. -/
  sgn : L → ZMod 2
  /-- The inverse dictionary: the kernel element with the given sign. -/
  ofZ : ZMod 2 → L
  /-- `ofZ` lands in the kernel. -/
  ofZ_mem : ∀ z, ofZ z ∈ P.Ker
  /-- `sgn ∘ ofZ = id`. -/
  sgn_ofZ : ∀ z, sgn (ofZ z) = z
  /-- `ofZ ∘ sgn = id` on the kernel. -/
  ofZ_sgn : ∀ {u : L}, u ∈ P.Ker → ofZ (sgn u) = u
  /-- Multiplication of kernel elements corresponds to addition mod two. -/
  sgn_mul : ∀ {u v : L}, u ∈ P.Ker → v ∈ P.Ker → sgn (u * v) = sgn u + sgn v

namespace KernelSign

variable {P : InternalProjection L G} (S : KernelSign P)

/-- **`+1 ↦ 0`.**  The neutral element has sign zero. -/
@[simp] theorem sgn_one : S.sgn 1 = 0 := by
  have h := S.sgn_mul (u := (1 : L)) (v := (1 : L)) (Subgroup.one_mem _) (Subgroup.one_mem _)
  rw [one_mul] at h
  have key : ∀ x : ZMod 2, x = x + x → x = 0 := by decide
  exact key _ h

theorem ofZ_zero : S.ofZ 0 = 1 := by
  rw [← S.sgn_one, S.ofZ_sgn (Subgroup.one_mem _)]

/-- Inversion is invisible in characteristic two. -/
theorem sgn_inv {u : L} (hu : u ∈ P.Ker) : S.sgn u⁻¹ = S.sgn u := by
  have h := S.sgn_mul (Subgroup.inv_mem _ hu) hu
  rw [inv_mul_cancel, S.sgn_one] at h
  have key : ∀ x y : ZMod 2, 0 = x + y → x = y := by decide
  exact key _ _ h

/-- The dictionary is injective on the kernel: no information is lost. -/
theorem sgn_injOn {u v : L} (hu : u ∈ P.Ker) (hv : v ∈ P.Ker) (h : S.sgn u = S.sgn v) :
    u = v := by
  rw [← S.ofZ_sgn hu, ← S.ofZ_sgn hv, h]

/-- A kernel element is trivial exactly when its sign vanishes. -/
theorem sgn_eq_zero_iff {u : L} (hu : u ∈ P.Ker) : S.sgn u = 0 ↔ u = 1 := by
  constructor
  · intro h
    exact S.sgn_injOn hu (Subgroup.one_mem _) (by rw [h, S.sgn_one])
  · rintro rfl
    exact S.sgn_one

/-- **WP5, packaged endpoint.**  The canonical group isomorphism `ker ρ ≃ ℤ₂`, with the
multiplicative structure on the left and the additive one on the right. -/
def kerMulEquiv : P.Ker ≃* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (S.sgn (u : L))
  invFun z := ⟨S.ofZ (Multiplicative.toAdd z), S.ofZ_mem _⟩
  left_inv u := Subtype.ext (S.ofZ_sgn u.2)
  right_inv z := by
    apply Multiplicative.toAdd.injective
    exact S.sgn_ofZ _
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    exact S.sgn_mul u.2 v.2

@[simp] theorem kerMulEquiv_apply (u : P.Ker) :
    S.kerMulEquiv u = Multiplicative.ofAdd (S.sgn (u : L)) := rfl

end KernelSign

end CechSpinZ2
