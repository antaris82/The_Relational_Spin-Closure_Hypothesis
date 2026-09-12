# TASK 38 — smoke-test result matrix

Experiment: **CONTROL A**, fixed Task-36/37 periodic control base, native Spin
transition/cocycle deformation only.

Everything below is a statement of the repository's green build
(`lake build RequestProject`, 8 352 jobs, no `sorry`, every endpoint on
`[propext, Classical.choice, Quot.sound]`).

---

## Result matrix

| item | result | source |
| --- | --- | --- |
| λ-domain tested/proved | **finite ℝ** (all of it, not sampled) | `controlAAdmissible_all` |
| λ = 0 admissible | **YES**, by the exact frozen Task-36 solution | `controlAAdmissible_zero` |
| arbitrary λ admissible | **YES**, with an explicitly constructed regular solder | `controlAAdmissible_all`, `loopParaSolder` |
| admissibility locus `R_A` | `R_A = ℝ` | `regularRegion_loopTransportFamily` |
| λ ↔ −λ symmetry | **PROVED** | `controlAAdmissible_neg_iff` |
| Spin gauge equivalence (full-group cocycle gauge) | **SAME ORBIT** for all λ₁, λ₂ | `spinCocycle_gaugeEquiv` |
| Spin gauge equivalence (kernel-valued, the narrower project notion) | **DISTINCT** for λ ≠ 0 | `not_kernelGaugeEquiv_of_ne_zero` |
| Lorentz gauge equivalence (projected cocycle) | **SAME ORBIT** for all λ₁, λ₂ | `projectedCocycle_gaugeEquiv` |
| solder comparison | witnesses differ chartwise by an element of the intrinsic Lorentz group | `loopParaSolder_A_comparison` |
| induced tangent metric | **EQUAL** (literal equality of the bilinear forms) | `tangentMetric_loopParaSolder_eq` |
| transport one-form | **NOT YET DEFINED** | — |
| field strength / curvature | **NOT YET DEFINED** | — |
| **scientific outcome** | **C — universally admissible and pure gauge** | `native_transport_knob_smoketest_certificate` |

The two gauge rows are deliberately **not** merged.  They use different equivalence relations
and say different things:

* the *kernel-valued* relation `SpinNative.GaugeEquiv` identifies two Spin **lifts of one and
  the same projected cocycle**; a nonzero deformation moves the projection, so it is not such a
  relabelling.  This is a statement about lift labels;
* the *full-group* relation `Task37.Deformation.CocycleGaugeEquiv` — the standard "is this
  cocycle a coboundary?" relation, with the same multiplication convention and with continuity
  retained — identifies transition systems that describe the same glued object.  At this
  relation the whole λ-family is one orbit.

---

## Per-quantity λ-dependence table (Part V §13)

| quantity | classification |
| --- | --- |
| native Spin cocycle | **GAUGE EQUIVALENT** (single orbit; not exactly equal for λ ≠ 0) |
| projected Lorentz cocycle | **GAUGE EQUIVALENT** (single orbit; not exactly equal for λ ≠ 0) |
| regular solder witness | **GAUGE EQUIVALENT**, chartwise by the projected transport state, an element of the intrinsic Lorentz group |
| tangent transition `D(φ_ij)` | **EXACTLY EQUAL** — the base is frozen, and all of them are the identity on this model |
| tangent Lorentz metric | **EXACTLY EQUAL** |
| transport one-form / curvature | **NOT YET COMPARABLE** — the objects do not exist in the project |

---

## Stop condition

**PASS-C0** — pure-gauge smoke test.

`∀ λ, ControlAAdmissible λ`, all λ in one certified gauge orbit, and no invariant
tangent-metric change.

Conclusion: on the fixed Task-36/37 control base, the currently formalized native Spin Čech
**transition** deformation is *not* a closure-sensitive degree of freedom and is *not* the
physical transport knob.  This is a successful **negative** smoke test; the next step is the
minimal missing transport layer, specified in `TASK39_CONNECTION_TRANSPORT_GATE_HANDOFF.md`.

---

## Scope of the negative result (what is **not** claimed)

* Nothing is claimed for **MAIN TEST B** (co-varying base).  The Task-37 anti-vacuity control
  `selective_family_not_admissible_of_ne` already shows that a co-varying family *can* be
  admissible exactly at λ = 0, so the closure predicate itself retains selecting power; what
  Task 38 proves is that *this* fixed-base Spin-transition knob does not exercise it.
* Nothing is claimed about other base models.  The wrap-around component and the ordinary
  component of the frozen periodic model are separated by a coordinate gap inside the second
  patch, and the construction uses that gap; a cover without such room is not covered by this
  result.
* Nothing is claimed about curvature, because no curvature object exists in the project.
