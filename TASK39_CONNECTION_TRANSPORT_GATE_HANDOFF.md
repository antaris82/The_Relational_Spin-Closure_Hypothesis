# TASK 39 — handoff: the transport-layer gate  [SUPERSEDED BY TASK 40]

**This document is superseded.**  Its living replacement is `NEXT_PHASE_TRANSPORT_GATE.md`,
which is part of the canonical, machine-validated document set.  This stub is kept only so that
the historical Task-38/39 references (`TASK38_AUDIT.md`, `TASK38_PROVENANCE.md`,
`TASK38_SMOKETEST_RESULT.md`, `PROVENANCE_LEDGER.md`) still resolve.  Nothing here should be
used as a statement of the project's current position.

The original draft contained three statements that the Task-40 review found to be wrong.  They
are quoted below **only** in order to withdraw them; they are invalid statements and must never
be copied forward.

## WITHDRAWN STATEMENT 1 — overgeneralized Task-38 conclusion

> QUOTED INVALID STATEMENT: "a transition-cocycle deformation is a change of trivialisation,
> not a change of geometry."

Wrong because the proved result is scoped to one family on one control base.  The correct,
proved wording is in `NEXT_PHASE_TRANSPORT_GATE.md` §1 and in `PAPER_I_FACT_SHEET.md` §7:
the specific Task-37 native one-parameter Spin Čech-transition deformation on the frozen
periodic fixed-cover control base lies in one full-Spin Čech gauge orbit for all finite λ, and
on that control the regular solder solution spaces at two parameter values are related by the
certified transport with the induced tangent Lorentz metric preserved.  A general Čech
deformation classification is NOT PROVED.

## WITHDRAWN STATEMENT 2 — false Lie-algebra inventory

> QUOTED INVALID STATEMENT: "the project has no Lie algebra" / "the project has **no** Lie
> algebra, no exponential map and no `ContMDiff` sections for the Spin group."

Wrong in its first clause.  The repository does contain an intrinsic six-dimensional
Lorentz-skew Lie algebra `SpinCore.gB` / `SpinCore.gBLie`, linearly equivalent to the bivector
space of the intrinsic Lorentz carrier [CLAIM-L011].  What is missing is the *bridge* to the
infinitesimal structure of the intrinsic `SpinGroup` [CLAIM-B010], [CLAIM-B011] and the smooth
Lie-group package [CLAIM-B001].

## WITHDRAWN STATEMENT 3 — type-incorrect future connection relation

> QUOTED INVALID STATEMENT: "No independent Lorentz-side one-form may be introduced; it must be
> `spinCover ∘ ω`."

Wrong because `spinCover` is a group-level homomorphism while a connection one-form is
Lie-algebra valued.  The corrected architectural requirement is in
`NEXT_PHASE_TRANSPORT_GATE.md` §3: the Lorentz-side connection must be induced through the
differential of the native Spin cover (`dρ_e`) or through an explicitly proved equivalent
infinitesimal representation.

---

Everything else in the original draft (the dependency order of the missing objects, the gate
question, the inherited hard constraints and the expected failure modes) is carried over, in
corrected form, into `NEXT_PHASE_TRANSPORT_GATE.md`.
