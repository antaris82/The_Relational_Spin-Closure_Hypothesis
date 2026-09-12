# TASK 37 — the deformation-ready shared-transport interface

This document is the §8–§19 deliverable of Task 37: the source-level audit of what the project
means by "transport", the identification of the single shared Spin-side deformation source,
and the description of the prepared interface.

Everything stated here is backed by modules that compile in the green Task-37 build; nothing
below is a plan or an intention unless it is explicitly marked **NOT FORMALIZED**.

---

## 1. §8 — exact source-level audit of "transport"

The project's transport-like objects are **not** one object.  They are:

| object | defining module | input dependencies | regularity level | group / type | currently variable? | currently derived? | suitable as deformation variable? |
|---|---|---|---|---|---|---|---|
| native Spin transition cocycle `S.g i j` | `Spine/SpinNative/TransitionData.lean` (an instance of `CechSpinLift.VisibleCocycle`, `Spine/E2/Cech/Cover.lean`) | an emergent cover `emergentCover B` | continuous on each double overlap; exact Čech 1-cocycle law on triple overlaps | `SpinCore.SpinGroup` (intrinsic, from `Cl₃`) | **YES — primitive** | no | **YES — this is the Task-37 deformation source** |
| projected Lorentz cocycle `project internalSpinProjection S` | `Spine/SpinNative/Projection.lean` | the native Spin cocycle | inherits continuity and the cocycle law | `SpinCore.GLor` | no | **YES**, image under `SpinCore.spinCover` | no — it must stay derived |
| projected Lorentz transition `projectedLorentzTransition S i j x` | `Spine/Solder/InternalLorentz.lean` | the native Spin cocycle | continuous; preserves `NS`, `BS`, cone, interior future; `det = 1` | `LocalModel ≃ₗ[ℝ] LocalModel` inside `GLor` | no | **YES** | no — derived |
| tangent coordinate transition `Dφ_ij` (`tangentTransitionMap`) | `Spine/Emergent/TangentTransition.lean` | the base gluing datum `B` only | `C^∞` (from `B.SmoothGluing`); invertibility derived by the chain rule | `LocalModel ≃L[ℝ] LocalModel` | only through `B` | **YES**, from the gluing | not directly — it moves only if the base moves (MAIN TEST B) |
| regular solder comparison `A i y` | `Spine/Solder/RegularSolder.lean` | base gluing + native Spin cocycle | `C^∞` on each chart domain, fibrewise `≃L[ℝ]`, exact intertwining square | `LocalModel ≃L[ℝ] LocalModel` | **YES** — it is the extra datum whose *existence* is the question | no | no — it is the **unknown** of the closure problem, not a knob |
| residual regular gauge | `Spine/Solder/RegularGauge.lean`, `Spine/Task36/GaugeGroup.lean` | a regular solder | `C^∞` | group acting freely and transitively on solders | yes (gauge) | no | no — pure gauge, not physical |
| **Spin / Lorentz connection form** | — | — | — | — | — | — | **NOT FORMALIZED** |
| **parallel transport along a path** | — | — | — | — | — | — | **NOT FORMALIZED** |
| **loop transport (holonomy)** | — | — | — | — | — | — | **NOT FORMALIZED** |
| **curvature** | — | — | — | — | — | — | **NOT FORMALIZED** (and mechanically forbidden by the audits) |

**CONNECTION / PARALLEL-TRANSPORT / LOOP-TRANSPORT DEFORMATION: NOT YET FORMALIZED.**

The project has no differential-form transport datum, no path-transport operator and no
loop-transport (holonomy) map anywhere; the mechanical audit in
`RequestProject/Spine/Task36/Firewall.lean` even *forbids* declaring such an object at this
stage.  Transition functions, connection forms and holonomy are **not** identified with each
other anywhere in this repository, and Task 37 does not pretend otherwise.

Consequence for the stop conditions: the strongest transport object that actually exists is
the **native Spin transition cocycle**, and the deformation interface is prepared exactly
there.

---

## 2. §9 — the ONE shared Spin-side deformation source

`RequestProject/Spine/Deformation/SharedTransport.lean` introduces

```text
    Task37.Deformation.transportState : ℝ → SpinCore.SpinGroup
    transportState l = cosh (l/2) + sinh (l/2) · e₀        (inside the project's own Cl₃)
```

with, as theorems:

* `transportState_zero : transportState 0 = 1` — the neutral value is the group unit exactly;
* `transportState_add : transportState (a + b) = transportState a * transportState b`;
* `transportState_neg : transportState (-a) = (transportState a)⁻¹`;
* `transportState_injective` — distinct parameters give distinct states.

The Lorentz side is **only** ever obtained by projection:

```text
    projectedTransportState l = SpinCore.spinCover (transportState l)
```

* `projectedTransportState_zero : projectedTransportState 0 = 1`;
* `projected_determined_by_spin` — the Lorentz datum is a *function* of the Spin datum;
* `projectedTransportState_apply_sOne` — the explicit action on the intrinsic unit;
* `projectedTransportState_ne_one` — for `λ ≠ 0` the projected datum is **not** the identity,
  so the deformation is genuinely visible to the solder square (unlike the Task-36 kernel
  `±1` twist, which is invisible after projection).

`λ : ℝ` is a finite real parameter.  Extended reals are never used as transition or group
parameters; `λ → 0±` and `λ → ±∞` appear only as limit *regimes* in the vocabulary of §19.

---

## 3. §10, §13 — the interface

`Task37.Deformation.SharedTransportFamily P ι` has exactly two fields:

```text
    base : P → BaseGluingData LocalModel ι
    spin : ∀ p, NativeSpinTransitionData SpinGroup (emergentCover (base p))
```

and **no** Lorentz field; this two-field shape is enforced mechanically by
`RequestProject/Spine/Deformation/Firewall.lean` (check 3).

* The parameter type `P` is generic.  `ScalarTransportFamily ι = SharedTransportFamily ℝ ι` is
  the **constant scalar `λ`** case — the first smoke-test control.  A later
  **local parameter field `λ(x)`** experiment instantiates `P` with a field type (for example
  `P = LocalModel → ℝ`) and needs *no* redesign: nothing in the interface assumes `P = ℝ`.
* The base is allowed to co-vary with the parameter, so mixed, anisotropic and inhomogeneous
  situations are representable.  Freezing the base is available only as the explicitly named
  **fixed-base control subcase** `SharedTransportFamily.fixedBase` / `IsFixedBase`.

---

## 4. §11 — `λ = 0` is exact regression, not analogy

In `Spine/Deformation/LoopSharedTransport.lean` and `Spine/Deformation/NeutralRegression.lean`:

| statement | content |
|---|---|
| `loopSharedSpin_zero` | the `λ = 0` deformed native Spin datum **equals** the frozen trivial seed of the Task-36 periodic control |
| `loopSharedSpin_projected_zero` | the projected Lorentz transition at `λ = 0` is the identity |
| `loopSharedSpin_zero_solder` | the frozen Task-36 regular solder solders the `λ = 0` member |
| `loopTransportFamily_spin_zero`, `loopTransportFamily_projected_zero` | the same, read off the smoke-test family |
| `reconvergence_at_neutral` | the frozen Task-36 `classical_reconvergence` theorem is available at `λ = 0` |

Terminology: `λ = 0` is the **neutral reference sector** / **undeformed reference transport**.
It is *not* called flat: no curvature exists in the project.

---

## 5. §14, §16, §17 — closure solutions, ordering, non-vacuity

`Spine/Deformation/ClosureAdmissibility.lean`:

```text
    structure RegularClosureSolution F p where
      smoothGluing : (F.base p).SmoothGluing
      solder       : SmoothTangentSolderData (F.base p) (F.spin p)

    RegularClosureAdmissible F p : Prop := Nonempty (RegularClosureSolution F p)
```

* The solution object carries **no** supplied compatibility field: the solder's intertwining
  square is between the genuine tangent transitions of the parameter's own base and the
  *projected* native Spin transition of the parameter's own Spin datum.  The two-field shape
  is also enforced mechanically (firewall check 3).
* **Ordering (§16).**  Closure existence is the first and only observable prepared here.  No
  metric/transport/symmetry-classification notion appears in the deformation branch at all.
* **Non-vacuity (§17), proved:**
  * `moebiusTransportFamily_not_admissible` — a family over the frozen orientation-reversing
    model closes at **no** parameter value;
  * `selective_family_admissible_zero` and `selective_family_not_admissible_of_ne` — a
    co-varying family that closes **exactly** at `λ = 0`;
  * `not_forall_regularClosureAdmissible` — there is therefore no universal existence theorem.
* Whether the *Spin-side* smoke-test family `loopTransportFamily` closes for `λ ≠ 0` is
  **deliberately not decided**: that is the Task-38 question.

---

## 6. §15 — the two future experiments

```text
CONTROL A — fixed geometry
    IsFixedBase F        (e.g. loopTransportFamily κ)
    vary the shared Spin-side transport, hold the base frozen,
    ask whether a compatible regular solder still exists.

MAIN TEST B — reciprocal / co-varying closure
    general SharedTransportFamily
    let base gluing, tangent transitions and solder co-vary with the shared Spin-side
    transport, ask whether a regular global closure solution exists.
```

The project hypothesis is about MAIN TEST B.  CONTROL A is diagnostic only and must not be
reported as reciprocal closure.

---

## 7. §19 — regimes prepared, not solved

Vocabulary only (`Spine/Deformation/ClosureAdmissibility.lean`, section `Regimes`):

```text
    regularRegion F           the set of finite λ at which F closes
    NeutralIsolated F         a punctured neighbourhood of 0 closes nowhere
    NeutralInterval F         an open interval around 0 closes everywhere
    RegularUnboundedAbove F   λ → +∞ regime
    RegularUnboundedBelow F   λ → -∞ regime
    CriticalAbove F c         a finite critical parameter above 0
    SignAsymmetric F          the two directions behave differently
```

No theorem decides any of these for the smoke-test family.  `±∞` never occurs as a parameter
value: the two "unbounded" predicates quantify over finite `λ` only.

---

## 8. §12, §18 — leakage and shared-origin firewalls

Mechanically checked in `RequestProject/Spine/Deformation/Firewall.lean` at compile time:

1. the deformation branch is a **leaf**: no other Spine module imports it (201 modules
   checked);
2. it reaches no historical experiment tree and no external project;
3. `SharedTransportFamily` has exactly the fields `[base, spin]`, and
   `RegularClosureSolution` exactly `[smoothGluing, solder]` — no independent Lorentz field,
   no supplied compatibility field;
4. no declaration of the branch names a curvature sign, `kappa`, a cosmological constant, a
   sphere, hyperbolic space, de Sitter, anti-de Sitter, Einstein equations, a Riemann tensor,
   a connection or a holonomy (116 declarations scanned);
5. positive sensitivity controls: the branch really does reach the frozen solder layer, the
   frozen Task-36 comparison endpoint and the intrinsic spin cover.

---

## 9. Stop condition reached

**PASS-A**, with the PASS-B caveat stated explicitly and honestly: Task 36 is frozen and
revalidated; the shared Spin-side deformation source exists and is unique; `λ = 0` reproduces
the frozen reference transport exactly; the Lorentz side is derived; a non-vacuous, falsifiable
closure notion is defined; no curvature class is encoded.  The deformation is prepared at the
level of **transition cocycles**, because that is the strongest transport object the project
actually has — connection and holonomy remain **NOT FORMALIZED**, and Task 38 must construct
them first if it wants to deform them.
