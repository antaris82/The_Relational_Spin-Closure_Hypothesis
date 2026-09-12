import RequestProject.Spine.Cohomology.Coboundary

/-!
# Task 8, WP4 : the characteristic-two sign audit

The classical prism/chain-homotopy identity for **signed** singular chains reads

```
    ∂ P + P ∂  =  g_# - f_# .
```

Over `ℤ/2` the same identity is written

```
    ∂ P + P ∂  =  g_# + f_# ,
```

and the whole difference between the two statements is the single algebraic fact `-1 = 1`
in `ZMod 2`.  This module isolates that fact and its consequences for the Task-5 cochain
modules, so that the sign collapse is *visible in the formal dependency structure* rather
than silently performed.

Nothing here is a new convention: `Mod2Cohomology.coboundary` was already defined in Task 5 as
the unsigned sum over faces, and `alternating_coboundary_eq_coboundary` below **proves** that
the unsigned sum agrees with the alternating one, so the Task-5 convention is the reduction
mod two of the standard signed convention and not a different theory.

## Contents

* `Mod2Cohomology.CharTwo.neg_one` — `(-1 : ZMod 2) = 1`;
* `Mod2Cohomology.CharTwo.neg_cochain`, `Mod2Cohomology.CharTwo.sub_cochain` — `-c = c` and
  `c - c' = c + c'` for cochains;
* `Mod2Cohomology.alternating_coboundary_eq_coboundary` — the alternating face sum equals the
  Task-5 unsigned coboundary;
* `Mod2Cohomology.CharTwo.signed_vs_unsigned` — the exact translation
  `u - v = w ↔ u + v = w` used to pass from the signed prism identity to the mod-2 one.
-/

noncomputable section

namespace Mod2Cohomology

universe u

namespace CharTwo

/-- The whole content of the sign collapse: `-1 = 1` in `ZMod 2`. -/
theorem neg_one : (-1 : ZMod 2) = 1 := by decide

/-- Every element of `ZMod 2` is its own negative. -/
theorem neg_self (x : ZMod 2) : -x = x := by revert x; decide

/-- Every element of `ZMod 2` is its own additive inverse. -/
theorem add_self (x : ZMod 2) : x + x = 0 := by revert x; decide

variable {X : TopCat.{u}} {n : ℕ}

/-- A mod-2 cochain is its own negative. -/
theorem neg_cochain (c : Cochain X n) : -c = c := by
  funext σ; exact neg_self _

/-- Subtraction and addition of mod-2 cochains agree. -/
theorem sub_cochain (c c' : Cochain X n) : c - c' = c + c' := by
  rw [sub_eq_add_neg, neg_cochain]

/-- **The exact translation between the signed and the unsigned chain-homotopy identity.**
A relation `u - v = w` over signed coefficients becomes `u + v = w` in characteristic two, and
conversely.  This is the only step by which the classical prism identity
`∂P + P∂ = g_# - f_#` becomes the mod-2 identity `∂P + P∂ = g_# + f_#`. -/
theorem signed_vs_unsigned (u v w : Cochain X n) : u - v = w ↔ u + v = w := by
  rw [sub_cochain]

end CharTwo

open Finset in
/-- **The Task-5 unsigned coboundary is the reduction of the classical alternating one.**
The classical singular coboundary is `∑ᵢ (-1)ⁱ f(∂ᵢ σ)`; modulo two every sign is `1`, and the
alternating sum is literally the Task-5 sum `Mod2Cohomology.coboundary`. -/
theorem alternating_coboundary_eq_coboundary {X : TopCat.{u}} (n : ℕ) (f : Cochain X n)
    (σ : Simplex X (n + 1)) :
    (∑ i : Fin (n + 2), (-1 : ZMod 2) ^ (i : ℕ) * f (face i σ)) = coboundary n f σ := by
  rw [coboundary_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [CharTwo.neg_one, one_pow, one_mul]

end Mod2Cohomology
