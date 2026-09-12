# TASK 37 — code hygiene

Scope: the five new modules of `RequestProject/Spine/Deformation/` (1 189 lines) and the
Task-36 modules edited by the freeze refactor.

---

## 1. Forbidden constructs

| construct | occurrences in new/edited modules |
|---|---|
| `sorry` | 0 |
| `admit` | 0 |
| new `axiom` | 0 |
| `native_decide` | 0 |
| `unsafe` | 0 |
| `partial` | 0 |
| `implemented_by` | 0 |
| `Matrix.inv` | 0 |
| `simp` / `simpa` | 0 |
| `decide` | 0 |

## 2. Automation actually used in the new modules

| tactic | uses | where | why it is acceptable |
|---|---|---|---|
| `ring` | 5 | `SharedTransport.lean` | closes purely numerical `ℝ`-identities between `cosh`/`sinh` products; no structure of the project is involved |
| `abel` | 1 | `SharedTransport.lean` | reassociates a four-term sum in the additive group of `Cl₃` after the four product terms have been computed explicitly |
| `congr` | 1 | `LoopSharedTransport.lean` | inside an `if`-split, to compare the two branches |
| `split` | 3 | `LoopSharedTransport.lean` | case split of the piecewise-constant transition function |
| `subst` | 5 | `LoopSharedTransport.lean`, `ClosureAdmissibility.lean` | eliminates equations between labels / involutions before applying a frozen theorem |
| `by_contra` | 3 | `SharedTransport.lean`, `LoopSharedTransport.lean` | genuine contrapositive arguments (e.g. "if the projected state were the identity, `sinh λ` would vanish") |

Everything else is `rw`, `rfl`, `exact`, `refine`, `unfold`, `cases`, `conv_lhs` and explicit
structural lemmas, as the project policy prefers.

## 3. `Classical` — the exact, complete list

There are **exactly two** localized `Classical` occurrences in the Task-36/37 layers, both of
the same kind, and this document does **not** claim "no Classical".

### 3.1 `Task36.signFun` — `RequestProject/Spine/Task36/LoopSpinFreedom.lean`, line 189

```text
    open Classical in
    def signFun (σ : κ → Bool) (p q : κ × Bool) (x : Space (loopGluingOf κ LoopTwist.id')) :
        ↥SpinGroup :=
      if p.2 ≠ q.2 ∧ x ∈ wrapSet κ p.1 then zOf (σ p.1) else 1
```

* **why it is there**: the condition contains membership in the open set
  `Task36.wrapSet κ p.1` of the *quotient* emergent base, which is not a decidable predicate.
* **why it is not removed**: a constructive replacement would need a decidable characterisation
  of the wrap component inside the quotient — an auxiliary library whose only effect would be
  to obscure the adversarial control.  Task 37 audited this (§5) and deliberately did not
  over-refactor.
* **what it is used for**: presentation/computation infrastructure only.  It defines a
  piecewise-constant `±1`-valued function on two disjoint *open* sets; the three lemmas
  `signFun_of_eq`, `signFun_of_notMem`, `signFun_of_mem_wrap` immediately replace every later
  use of the `if`.  It enters **no** mathematical hypothesis of any principal statement.

### 3.2 `Task37.Deformation.loopTransportFun` — `Spine/Deformation/LoopSharedTransport.lean`, line 87

The exact `λ`-analogue of 3.1, with `zOf (σ p.1)` replaced by the direction-dependent shared
transport state.  Same justification, same isolation: the three lemmas
`loopTransportFun_of_eq`, `loopTransportFun_of_notMem`, `loopTransportFun_of_mem_wrap` are used
everywhere afterwards.

### 3.3 Correction of `TASK36_CODE_HYGIENE.md`

That document's table reports `| Classical. | 0 |`.  Read literally as "occurrences of the
string `Classical.`" the count is correct, but it is **misleading**: `LoopSpinFreedom.lean`
contains `open Classical in` (line 189).  The corrected statement is:

> Task 36 contains exactly one localized `Classical` exception, `Task36.signFun`, documented in
> §3.1 above.  It is not used in any principal mathematical assumption.

A correction notice with this text has been appended to `TASK36_CODE_HYGIENE.md`.

### 3.4 The removed `Classical` use

`Task36.continuous_det_of_continuous` used the `classical` *tactic* to obtain an arbitrary
basis.  Task 37 replaced it by `Task36.continuous_det_localModel`, which uses the project's
explicit `Fin 4` coordinates.  That `classical` is gone.

## 4. Axiom profile

Every endpoint of the new modules reports exactly

```text
    [propext, Classical.choice, Quot.sound]
```

(`Classical.choice` here is the ambient Mathlib axiom reported for essentially every Mathlib
development, not a use of the `Classical` namespace in a proof.)  No `sorryAx` anywhere.

## 5. Naming discipline

No declaration in the deformation branch names a curvature sign, `kappa`, a cosmological
constant, a sphere, hyperbolic space, de Sitter, anti-de Sitter, Einstein equations, a Riemann
tensor, a connection or a holonomy.  This is enforced mechanically at compile time
(`Spine/Deformation/Firewall.lean`, check 4: 116 declarations scanned).
