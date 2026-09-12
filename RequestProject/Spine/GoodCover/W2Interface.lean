import RequestProject.Spine.GoodCover.SingularComparisonSpec

/-!
# Task 7, WP14 : the interface a future `w₂(TM)` must satisfy — and no definition of `w₂`

Once the Spin-lift obstruction can be transported to `H²_sing(M;ℤ₂)` (conditionally, see
`RequestProject.Spine.GoodCover.SingularComparisonSpec`), the natural next question is whether
it equals the second Stiefel–Whitney class of the tangent bundle.  **This module deliberately
does not define `w₂`,** and in particular does not set `w₂(TM) := [z]_sing`: that would make
the comparison a tautology and destroy its content.

Instead it fixes the *interface*.  `W2Datum X` is what an independent construction must
deliver: a mod-2 degree-two class attached to the data, natural under pullback along
continuous maps.  `AgreesWithSpinObstruction` is the *statement to be proved later*, phrased
so that it can only be established by producing a `W2Datum` from an independent construction.

## The three candidate routes (audit)

* **Route A — conventional Stiefel–Whitney theory.**  Real vector bundles → classifying space
  `BO(n)` or the Thom isomorphism → Steenrod squares → `wᵢ`.  Missing in pinned Mathlib:
  Steenrod squares, Thom spaces, Thom isomorphism, classifying spaces of `O(n)`,
  characteristic classes of real bundles.  Scope: *major*.
* **Route B — the Wu route in dimension four.**  Fundamental class `[M]` → Poincaré duality →
  Wu class `v₂` → `w₂ = v₂ + v₁²`.  Missing in pinned Mathlib: fundamental classes of closed
  manifolds, Poincaré duality, Wu classes, the Wu formula.  Scope: *major*; it additionally
  needs the cup product (which *is* available natively, Task 5) and compactness/orientability
  hypotheses Task 4 does not carry.
* **Route C — an alternative standard theorem.**  For a `SO(n)`-bundle, `w₂` is *defined* in
  some treatments as the Spin-lift obstruction; that is exactly the circular route this task
  forbids, so Route C is rejected in this form.  No other independent standard construction is
  shorter than A or B in the pinned library.

## The next dependency DAG (all edges below are currently missing)

```
  singular H* (native, done)  ─┐
  cup product (native, done)  ─┤
                               ├─► Steenrod squares ─► Thom iso ─► w(TM) ─► w₂   (Route A)
  homotopy invariance (WP9) ──┘
                               └─► fundamental class ─► Poincaré duality ─► v₂ ─► w₂ (Route B)
```

The first node needed by *both* routes, and the only one whose inputs already exist natively,
remains **homotopy invariance of the Task-5 singular theory** (WP9).
-/

noncomputable section

namespace GoodCoverSpec

open CategoryTheory

universe u t

variable {X : TopCat.{u}} {ι : Type t} {Fib : ↥X → Type u}
  [∀ x, AddCommGroup (Fib x)] [∀ x, Module ℝ (Fib x)]

/-- **WP14, the interface.**  What an independent construction of the second Stiefel–Whitney
class must deliver for the Task-4 Lorentz frame data: a degree-two mod-2 singular class of the
base, attached to the frame data.

This is a *specification*: it is never constructed here, never assumed anywhere in the Spine,
and it is not an axiom.  In particular `cls` is **not** defined to be the Spin-lift
obstruction. -/
structure W2Interface (X : TopCat.{u}) (ι : Type t) (Fib : ↥X → Type u)
    [∀ x, AddCommGroup (Fib x)] [∀ x, Module ℝ (Fib x)] where
  /-- The class an independent construction has to produce. -/
  cls : LorentzFrames.LorentzFrameData (↥X) Fib ι → Mod2Cohomology.Cohomology X 2

/-- **The statement a future task must prove**: the independently constructed class agrees with
the transported Spin-lift class.  It is stated, never assumed, and never used to define either
side. -/
def AgreesWithSpinObstruction (W : W2Interface X ι Fib)
    (Φ : LorentzFrames.LorentzFrameData (↥X) Fib ι) (C : Comparison Φ.cover.U)
    (h : GoodCoverZ2.IsGoodCover Φ.cover.U) (D : LorentzFrames.FrameSpinLifts Φ) : Prop :=
  W.cls Φ = frameSingularClass C h D

/-- **Why the interface is worth having.**  If a future independent construction satisfies the
comparison statement, then the Stiefel–Whitney side inherits the Spin criterion — which is the
whole point, and which is *not* available by definition. -/
theorem spinStructure_iff_of_agrees {W : W2Interface X ι Fib}
    {Φ : LorentzFrames.LorentzFrameData (↥X) Fib ι} {C : Comparison Φ.cover.U}
    {h : GoodCoverZ2.IsGoodCover Φ.cover.U} {D : LorentzFrames.FrameSpinLifts Φ}
    (hW : AgreesWithSpinObstruction W Φ C h D) :
    W.cls Φ = 0 ↔ Nonempty (LorentzFrames.SpinFrameStructure Φ) := by
  rw [AgreesWithSpinObstruction] at hW
  rw [hW]
  exact frameSingularClass_eq_zero_iff_spinStructure C h D

end GoodCoverSpec
