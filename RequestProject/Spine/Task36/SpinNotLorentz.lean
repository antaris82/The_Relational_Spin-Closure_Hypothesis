import RequestProject.Spine.Task36.OrientationReversing

/-!
# Task 36 / §12 : Spin-type data do not imply a regular Lorentz solder

**Task-36 separation module.**

## What §12 asked for, and what is actually proved here

The external discussion proposed `S⁴` as the decisive separation case: a smooth manifold
that is Spin and carries Riemannian metrics, but carries **no Lorentz metric**, the
obstruction being the non-vanishing Euler characteristic (no nowhere-zero vector field).

That concrete case is **NOT formalized here, and is not claimed.**  The audit of the pinned
Mathlib `v4.28.0` shows that none of the required standard results is available:

```text
    Euler characteristic of a smooth manifold      : ABSENT
    Poincaré–Hopf / hairy-ball in the form needed  : ABSENT
    Stiefel–Whitney classes, w₁, w₂                : ABSENT
    Lorentzian metrics on a manifold               : ABSENT
    Spin structures on a smooth manifold           : ABSENT (project-native only)
```

Re-implementing that topology library is explicitly out of scope for Task 36, so the concrete
`S⁴` instantiation is classified **BLOCKED BY INFRASTRUCTURE** in
`TASK36_COUNTERTEST_MATRIX.md` and is **not counted as a theorem-level pass**.

## What *is* proved: the exact project-native separation

The structural lesson of §12 — *Spin-type lift data alone must not buy you the Lorentz
geometry* — is nevertheless testable at the exact level the project formalizes, and it is a
genuine theorem here:

* `Task36.spin_does_not_imply_lorentz_conditional` — the conditional separation certificate:
  over **any** base gluing whose tangent determinant cocycle admits no continuous
  nowhere-vanishing 0-cochain trivialization, native Spin transition data exist (the trivial
  cocycle always does) while **no** native Spin datum whatsoever can be regularly soldered to
  `TM`;
* `Task36.spin_does_not_imply_lorentz_moebius` — the concrete witness: on the
  orientation-reversing four-dimensional gluing there *are* native Spin transition data, the
  emergent base *is* a `C^∞` four-manifold, and yet the internal Lorentz bundle admits no
  regular solder with `TM`, for any Spin seed.

## Honest classification of the gate (§§9, 12, 18)

In the concrete witness the failure occurs at the **orientation** gate, not at the
Euler-characteristic gate that rules out a Lorentz metric on `S⁴`, and not at the Spin-lifting
(triple-overlap) gate.  So this theorem establishes

```text
    native Spin transition data  ⇏  regular Lorentz solder
```

but it is **not** the `S⁴` theorem, and it must not be reported as one.  The two separations
have different causes and the matrix records them separately.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task36

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase
open EmergentBase.BaseGluingData

universe t

/-- **NEWLY DEFINED (Task 36), §12 — the conditional separation certificate.**

Over any base gluing, native Spin transition data always exist (the trivial Spin cocycle is
one).  If in addition the determinant cocycle of the genuine tangent transitions is not the
coboundary of a continuous nowhere-vanishing 0-cochain, then no native Spin datum at all can
be regularly soldered to the tangent bundle.

Spin-type data therefore do **not** buy the Lorentz-geometric identification: the two are
separated by an independent global condition. -/
theorem spin_does_not_imply_lorentz_conditional {ι : Type t}
    (B : BaseGluingData LocalModel ι)
    (hobstr : ¬ ∃ a : ι → LocalModel → ℝ,
      (∀ i, ContinuousOn (a i) (B.D i)) ∧
      (∀ i y, a i y ≠ 0) ∧
      (∀ i j, ∀ y ∈ B.W i j,
        LinearMap.det ((B.tangentTransitionMap i j y : LocalModel →ₗ[ℝ] LocalModel))
          * a i y = a j (B.φ i j y))) :
    Nonempty (NativeSpinTransitionData ↥SpinGroup (emergentCover B)) ∧
    (∀ S : NativeSpinTransitionData ↥SpinGroup (emergentCover B),
      IsEmpty (SmoothTangentSolderData B S)) :=
  ⟨⟨trivialCocycle (↥SpinGroup) (emergentCover B)⟩,
   fun S => orientation_obstruction_nonzero_implies_no_solder hobstr S⟩

/-- **NEWLY DEFINED (Task 36), PRINCIPAL §12 — the concrete project-native separation.**

On the orientation-reversing four-dimensional gluing:

1. the gluing is smooth and the emergent base is a `C^∞` four-manifold;
2. native Spin transition data exist — in particular the trivial Spin cocycle;
3. no native Spin datum whatsoever admits a regular solder with `TM`.

So "there is Spin-type transition data over a smooth four-manifold" does not imply "the
internal Lorentz bundle is the tangent bundle".

This is **not** the `S⁴` example: here the failure is at the orientation gate, whereas the
`S⁴` obstruction is the Euler characteristic, which the pinned Mathlib cannot express. -/
theorem spin_does_not_imply_lorentz_moebius :
    moebiusGluing.SmoothGluing ∧
    IsManifold localModelI (⊤ : ℕ∞) (Space moebiusGluing) ∧
    Nonempty (NativeSpinTransitionData ↥SpinGroup (emergentCover moebiusGluing)) ∧
    (∀ S : NativeSpinTransitionData ↥SpinGroup (emergentCover moebiusGluing),
      IsEmpty (SmoothTangentSolderData moebiusGluing S)) :=
  ⟨moebiusGluing_smoothGluing,
   loopGluingOf_isManifold Unit LoopTwist.flip,
   ⟨trivialCocycle (↥SpinGroup) (emergentCover moebiusGluing)⟩,
   orientation_reversing_gluing_no_solder⟩

end Task36

end

/-! ## Axiom audit -/

#print axioms Task36.spin_does_not_imply_lorentz_conditional
#print axioms Task36.spin_does_not_imply_lorentz_moebius
