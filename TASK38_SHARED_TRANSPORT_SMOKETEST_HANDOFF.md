# TASK 38 — handoff: the shared-transport smoke test

This file describes **only certified Task-37 inputs** and formulates the next experiment.  It
predicts no result and privileges no outcome.

---

## 1. Certified inputs (all proved, all in the green build)

### The single shared native Spin-side transport source

```text
    Task37.Deformation.transportState : ℝ → SpinCore.SpinGroup
        transportState 0            = 1                                   (exact)
        transportState (a + b)      = transportState a * transportState b
        transportState (-a)         = (transportState a)⁻¹
        transportState              injective in λ
```

Derived Lorentz side (never independently chosen):

```text
    projectedTransportState l = SpinCore.spinCover (transportState l)
        projectedTransportState 0   = 1                                   (exact)
        projectedTransportState l  ≠ 1        for every  l ≠ 0
```

### The deformed transition datum on the frozen periodic model

```text
    Task37.Deformation.loopSharedSpin :
        ℝ → NativeSpinTransitionData SpinGroup (emergentCover (loopGluingOf κ LoopTwist.id'))
```

a genuine native Spin transition datum for **every** finite `λ` (continuity on the overlaps
and the exact Čech 1-cocycle law are proved), with

```text
    loopSharedSpin 0 = trivial native seed              (exact regression)
    projected transition of loopSharedSpin 0 = identity
    loopSharedSpin_zero_solder : the frozen Task-36 regular solder solders λ = 0
    for λ ≠ 0 the projected transition on the wrap component is NOT the identity
```

### The interface

```text
    SharedTransportFamily P ι            fields: base, spin          (no Lorentz field)
    ScalarTransportFamily ι              P = ℝ, neutral value 0
    SharedTransportFamily.fixedBase      CONTROL A subcase, IsFixedBase
    RegularClosureSolution F p           fields: smoothGluing, solder
    RegularClosureAdmissible F p         Nonempty (RegularClosureSolution F p)
    regularRegion, NeutralIsolated, NeutralInterval, RegularUnboundedAbove,
    RegularUnboundedBelow, CriticalAbove, SignAsymmetric        (vocabulary only)
```

### Certified non-vacuity

```text
    moebiusTransportFamily_not_admissible      closes at no λ
    selective_family_admissible_zero           closes at λ = 0
    selective_family_not_admissible_of_ne      closes at no λ ≠ 0
    not_forall_regularClosureAdmissible        no universal existence theorem
```

### Certified availability of the frozen endpoints at `λ = 0`

```text
    reconvergence_at_neutral                   Task-36 classical reconvergence at λ = 0
    RegularClosureSolution.reconvergence       every admitted solution inherits it
```

---

## 2. What is NOT available

* **No connection form, no parallel transport along paths, no holonomy, no curvature.**  These
  are NOT FORMALIZED in the repository.  If Task 38 wants to deform a connection rather than a
  transition cocycle, it must first *construct* that layer; Task 37 deliberately did not fake
  it.
* No identification of the project's orientation/Spin obstruction classes with `w₁`, `w₂`.
* No proof that the periodic fixed-cover loop model's emergent base is `S¹ × ℝ³`, and no
  statement about its fundamental group.

---

## 3. The main question of Task 38

> **Starting from the frozen neutral reference solution at `λ = 0`, deform the single shared
> native Spin-side transport source and determine for which finite `λ` there exists a globally
> regular closure solution.**

Formally, for the Spin-side smoke-test family `F = loopTransportFamily κ` (CONTROL A) and then
for co-varying families (MAIN TEST B):

```text
    determine   regularRegion F = { λ : ℝ | RegularClosureAdmissible F λ } .
```

Only **afterwards**, and only for admitted solutions, may a later task ask what metric, what
transport law, what curvature, what symmetry class the solution carries.  No target class may
be supplied as an input.

### Suggested order of work

1. `λ = 0`: already solved (a solution exists, certified).
2. CONTROL A on the periodic fixed-cover loop model: decide, for `λ ≠ 0`, whether the
   intertwining square
   `A_j(φ_ij y) = D(φ_ij)(y) ∘ A_i(y) ∘ ρ(g_ij)` admits a `C^∞`, fibrewise invertible solution
   on the two-patch periodic cover, where `ρ(g_ij)` is now the projected deformed state on the
   wrap component and the identity elsewhere.  Note that the *existence question is genuinely
   open*: it is not settled by any Task-36 or Task-37 theorem.
3. MAIN TEST B: let the base gluing co-vary and ask the same question.
4. Only for admitted `λ`: classify.

---

## 4. Outcomes that must all remain possible

No definition in the Task-37 interface privileges any of:

* only `λ = 0` is regular (`NeutralIsolated`);
* a finite open interval around `0` is regular (`NeutralInterval`);
* disconnected regular branches exist (`regularRegion` is an arbitrary set);
* positive and negative `λ` behave asymmetrically (`SignAsymmetric`);
* regularity fails beyond a finite critical value (`CriticalAbove`);
* all finite `λ` are regular (`RegularUnboundedAbove` and `RegularUnboundedBelow`);
* mixed / local `λ(x)` solutions become necessary (instantiate `P` with a field type);
* maximally symmetric solutions appear — **as an output classification only**;
* non-maximally-symmetric, anisotropic or inhomogeneous solutions appear.

---

## 5. Anti-vacuity obligation for Task 38

If Task 38 finds itself proving `∀ λ, RegularClosureAdmissible F λ`, it must first check that
the proof does **not** rest on:

* `TangentSpace` being definitionally `LocalModel`;
* the identity solder plus an unconstrained Spin datum;
* independently chosen base transitions or independently chosen Lorentz transitions;
* a redefinition of `RegularClosureSolution` with supplied compatibility fields.

If the universal statement survives that review, it must be reported together with an explicit
scientific note explaining why the deformation has no selecting power — that is itself a
result, but it must not be obtained by weakening the definition.
