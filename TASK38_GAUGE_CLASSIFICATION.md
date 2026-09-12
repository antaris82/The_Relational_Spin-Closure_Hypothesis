# TASK 38 — gauge classification

This document states precisely which equivalence relations were used, where their conventions
come from, and what was proved with each.  It is the companion of
`TASK38_SMOKETEST_RESULT.md`.

---

## 1. The two relations

### 1.1 Kernel-valued (pre-existing, Task 31/36)

```text
    SpinNative.GaugeEquiv P S S'
      ⟺ ∃ λ_i : U_i → ker ρ, continuous on U_i,
          S'.g i j x = λ_i x · S.g i j x · (λ_j x)⁻¹   on  U_i ∩ U_j
```

This is the project's equivalence of **Spin lifts of a fixed projected Lorentz cocycle**.
Gauge-equivalent data have the same projection (`SpinNative.project_eq_of_gaugeEquiv`).

### 1.2 Full-group cocycle gauge (introduced by Task 38)

```text
    Task37.Deformation.CocycleGaugeEquiv S S'
      ⟺ ∃ u_i : U_i → G, continuous on U_i,
          S'.g i j x = u_i x · S.g i j x · (u_j x)⁻¹   on  U_i ∩ U_j
```

**The convention was derived, not remembered.**  It is *literally* the law of §1.1 with the
constraint `λ_i ∈ ker ρ` dropped, and the inclusion is proved:

```text
    gaugeEquiv_imp_cocycleGaugeEquiv :
        SpinNative.GaugeEquiv P S S'  →  CocycleGaugeEquiv S S'
```

Continuity is **part of the definition** and is not decorative: without it, on any cover any
two cocycles over a common refinement point are related by a pointwise relabelling
(`u_i(x) := g_{i i₀}(x)`), and the notion would be vacuous.  This is why
`continuous_transportState` — continuity of the Task-37 shared state in its parameter, in the
project's own intrinsic Spin topology — had to be proved before the gauge could be built.

The relation is reflexive, symmetric and transitive (`CocycleGaugeEquiv.refl/symm/trans`) and
is functorial along the native projection (`cocycleGaugeEquiv_project`), which is how the
Lorentz-side statement is obtained: **no independent Lorentz relabelling is ever chosen.**

---

## 2. What was proved

| statement | result |
| --- | --- |
| `spinCocycle_gaugeEquiv_zero l` | the λ-deformed native Spin cocycle is a **coboundary**: it is the neutral one gauge-transformed |
| `spinCocycle_gaugeEquiv l₁ l₂` | any two parameter values are in one Spin gauge orbit |
| `projectedCocycle_gaugeEquiv l₁ l₂` | the projected Lorentz cocycles are in one gauge orbit, via the projected Spin gauge |
| `not_kernelGaugeEquiv_of_ne_zero` | at the kernel-valued relation, λ ≠ 0 is **not** equivalent to 0 |
| `loopParaSolder_A_comparison` | the two solder witnesses differ chartwise by the projected transport state, an element of `SpinCore.GLor` |
| `tangentMetric_loopParaSolder_eq` | the induced tangent Lorentz metrics are **literally equal** |

---

## 3. The explicit gauge

```text
    loopGaugeFun l (n, false) x = 1
    loopGaugeFun l (n, true)  x = transportState ( - l · χ( y₀(x) ) )
```

where `y₀(x)` is the loop coordinate of `x` in the chart of the patch `(n, true)` and `χ` is the
smooth profile `Real.smoothTransition (y₀ - 3)` — zero on the ordinary incidence component
`2 < y₀ < 3`, one on the wrap-around component `4 < y₀ < 5`.

This is **the same profile** that solves the solder equation
(`Task37.Deformation.solderAngle`, `loopParaSolder`): the cocycle equation for the gauge and
the intertwining equation for the solder reduce to the *one* additive identity

```text
    θ_q(φ_pq y) = θ_p(y) + (parameter carried by the transition on that component)
```

proved once as `solderAngle_step` (chart form) and once transported to the base as
`solderAngle_pieceCoord_step`.  That coincidence is the content of Outcome C: the deformation
is absorbed by a redefinition of the local trivialisation, and the solder just follows it.

---

## 4. Why the deformation is absorbable — the structural reason

The frozen periodic model has, for each loop, two patches; the crossing overlap has **two
components**, and in the second patch they are separated by the coordinate gap `3 ≤ y₀ ≤ 4`.
A locally constant obstruction would need the two components to be forced to carry the same
value; they are not, because the gap leaves room for a smooth interpolation inside one patch.

The contrast with the frozen Task-36 `±1` control is instructive and is *not* a contradiction:
there the relabelling was required to stay in the **discrete** kernel, so it was constant on
each connected patch and could not interpolate — which is why distinct sign choices are
genuinely inequivalent there, while the continuous one-parameter family here is not.

---

## 5. Anti-vacuity audit of the universal theorem (Part VI §14)

Classification of the proof of `∀ λ, ControlAAdmissible λ`: **class A — a genuine compensating
regular solder exists**, and additionally **class B** holds (the deformation is a coboundary
direction).  Class **C is rejected**, and this is checked item by item in `TASK38_AUDIT.md` §3.
