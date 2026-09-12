# LOCAL / GLOBAL INTERFACE — where algebra stops and geometry begins

Frozen state: **TASK 39 — INTERMEDIATE PROJECT CLOSURE**.

This document answers five questions and nothing else.

1. Where does purely local algebra stop?
2. Where does global topology enter?
3. Where does smooth geometry enter?
4. Where does tangent geometry enter?
5. Where does the first nontrivial closure condition appear?

Claim IDs refer to `docs/machine/CLAIM_REGISTRY.jsonl`.

---

## 1. Where purely local algebra stops

Everything in `docs/mathematics/LOCAL_MATHEMATICS.md` is linear and multilinear algebra over a
single four-dimensional real vector space: the carrier, its quadratic form, its Clifford
algebra, its Spin group, the native projection, and the topologies these carry
([CLAIM-L001]–[CLAIM-L009]).

The local layer stops exactly at the last statement that quantifies over elements of
`LorentzCarrier` or of `SpinGroup` and over nothing else.  The last such statements are the
double-cover endpoints [CLAIM-L007], [CLAIM-L008] and the continuous local sections
[CLAIM-L009].

## 2. Where global topology enters

At exactly one place: the base-gluing datum `EmergentBase.BaseGluingData` [CLAIM-G001].

It is an **input**, not a consequence, and this is proved: the same local pieces admit
inequivalent emergent bases (`EmergentBase.base_not_determined_by_local_pieces`).  Nothing in
the local algebra selects a gluing, and nothing in the local algebra constrains one.

A second, independent global input arrives with the native Spin transition datum over the
emergent cover: a Čech-level object, which only exists once a cover exists.

## 3. Where smooth geometry enters

At the smoothness predicate `SmoothGluing` on the primitive [CLAIM-G003].  This too is an
input; the project exhibits a continuous gluing for which the smooth gate fails (NC-011).

Once it is assumed, the emergent base is a genuine `C^∞` four-manifold in Mathlib's sense
[CLAIM-G004], and from that point on the differential-geometric vocabulary of the pinned
library is available.

## 4. Where tangent geometry enters

At the tangent transitions [CLAIM-G005].  The theorem
`tangentTransition_eq_derivative_baseTransition` computes the coordinate changes of Mathlib's
*own* tangent bundle of the emergent manifold and identifies them with `D(φ_ij)`.

This is the first moment at which the project talks about `TM` rather than about a model fibre.
It is important that `TM` is Mathlib's construction: nothing is defined so as to make the
desired identification true.

## 5. Where the first nontrivial closure condition appears

At the **solder**, and nowhere earlier.

The internal side and the tangent side are, up to this point, unrelated:
`tangent_spin_base_data_do_not_force_transition_identification` [CLAIM-G006] proves that the
base gluing and the Spin datum together do **not** determine any identification between them.

The solder is the datum that supplies one, and the regular solder is the version that carries
enough regularity to produce geometry [CLAIM-G007], [CLAIM-G008].  Its *existence* is the first
genuinely nontrivial global closure condition of the project: it can fail, and on the
Möbius-type control it provably does [CLAIM-G017].

---

## The exact bridge

```text
    internal Lorentz / Spin data                 native Spin transition datum S
              │                                   (Čech, over the emergent cover)
              │  spinCover, applied pointwise
              ▼
    projected Lorentz transitions                 ρ(S.g i j x) ∈ GLor
              │
              │  the intertwining square of the REGULAR SOLDER:
              │      A j (φ_ij y) v = D(φ_ij) ( A i y ( ρ(S.g i j x) v ) )
              ▼
    actual tangent transitions D(φ_ij)            derivatives of the gluing maps
              │
              │  transport of the intrinsic form BS through the solder frames
              ▼
    tangent Lorentz geometry                      a C^∞ metric field of signature (1,3)
```

Reading the square in words: the solder is the unique place where an *internal* symmetry
(`GLor`, coming from the Clifford/Spin core) is required to agree with an *external* symmetry
(the derivative of a coordinate change on a manifold).  Every global consequence of the project
— orientation compatibility, triviality of the native Spin obstruction, the future-cone
reduction — is extracted from that single equation.

## Why an internal Spin seed does **not** give a Spin structure on an arbitrary tangent bundle

This is the point the project is most careful about, and it is why the Task-36 battery exists.

* The internal Spin datum lives on the **internal** bundle.  Its structure group is the
  project's own `SpinGroup`, and its cocycle condition is an equation between internal
  transition functions.  Nothing in it refers to `TM`.
* The tangent bundle has its own transition functions `D(φ_ij)`, fixed by the base gluing alone.
* A solder is what forces the two systems to be conjugate.  Without one, the two sides can be
  arbitrarily unrelated; with a *weak* one, they are related fibrewise but not regularly, and
  the induced metric can fail to be continuous [CLAIM-G007].
* And the required conjugation can be **impossible**: over the Möbius-type gluing there exist
  native Spin transition data, yet no regular solder exists at all [CLAIM-N009], [CLAIM-G017].
  This is exactly the statement "an internal Spin seed does not imply a Spin structure on the
  tangent bundle", in the project's own vocabulary.

What the project *does* prove is the converse direction, and only under the solder hypothesis:

> if a regular solder exists, then the emergent atlas is orientation compatible and the
> project-native Spin-lifting obstruction of the projected cocycle is trivial
> ([CLAIM-G011], [CLAIM-G013]).

That is the **reconvergence** result of Task 36: conditions that are usually *assumed* at the
start of a spin-geometry construction re-emerge here as *consequences* of a global closure
condition, in a development that never assumed them.

Two warnings belong with it, and are part of the result:

* the conditions are the project's own fixed-cover notions.  They are **not** `w₁(TM) = 0` and
  `w₂(TM) = 0`; no characteristic class exists in this repository [CLAIM-B002], `OP-006`;
* the implication is one-directional.  Nothing says that orientation compatibility plus a
  trivial obstruction *produce* a regular solder; only necessity is proved [CLAIM-B007],
  `OP-011`.

## How Task 36 connects to the present closure point

Task 36 established that the solder is a gate with two independently sensitive obstructions, and
that the discrete Spin-lift freedom survives the bottom-up construction [CLAIM-G018].  Tasks 37
and 38 then asked the obvious next question:

> if the internal Spin transition datum is *deformed*, does the closure condition see it?

The answer, on the frozen periodic control and for the first knob that the project could
actually build, is **no**: the deformation is globally admissible for every parameter value, it
lies in a single full-Spin Čech gauge orbit, and after Task 39 we know that the corresponding
regular solder solution spaces are in bijection with the induced tangent Lorentz metric
preserved ([CLAIM-S001], [CLAIM-S004], [CLAIM-S010]).

So the interface diagram above is *gauge-insensitive at its top arrow*, at least on that
control.  A deformation that only changes the Čech transition functions is a change of
trivialisation; the geometry it induces through the solder does not move.  That is the reason
the present phase closes here and the next question is located one layer deeper, at a
connection / parallel transport / holonomy layer that this repository does not contain
([CLAIM-B003], [CLAIM-B009], `OP-002`–`OP-005`).
