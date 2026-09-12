# LOCAL MATHEMATICS — the intrinsic Lorentz / Clifford / Spin core

Frozen state: **TASK 39 — INTERMEDIATE PROJECT CLOSURE**.

This document describes, in theorem-oriented form, everything the project proves *before any
global topology enters*.  Every object is given with its canonical project name, its Lean
type or defining equation, its defining module, its direct dependencies, its mathematical
role, its theorem-level properties, its assumptions, and an explicit statement of what it does
**not** claim.

Claim IDs refer to `docs/machine/CLAIM_REGISTRY.jsonl`; theorem IDs to
`docs/machine/THEOREM_REGISTRY.jsonl`; object IDs to `docs/machine/OBJECT_REGISTRY.jsonl`.

Four kinds of statement are distinguished throughout:

| marker | meaning |
| --- | --- |
| **PRIMITIVE DATUM** | an input of the project; nothing is claimed about its necessity |
| **DERIVED STRUCTURE** | constructed from earlier data, with no further input |
| **CONVENTION** | a choice (of sign, orientation of a square, multiplication order) that is fixed once and then used everywhere |
| **THEOREM** | proved in Lean, `sorry`-free, axiom-audited |
| **NEGATIVE CONTROL** | an explicit adversarial model whose recorded outcome is a failure |

---

## 1. The primitive datum: a positive Euclidean three-space  [CLAIM-L001]

* **Object** `SpinCore.sip` (OBJ-001), `RequestProject/Spine/E1/Carrier.lean`
* **Lean** `sip : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ`, the standard positive definite inner product
* **Kind** PRIMITIVE DATUM
* **Role** the entire construction starts here.  There is no Lorentzian signature, no metric on
  any manifold, no orientation, no time direction and no spacetime at this point.
* **Does not claim** that ℝ³ is forced, unique, or derived from something more primitive.

## 2. The spin-factor carrier and the derived Lorentz form  [CLAIM-L002]

* **Objects** `SpinCore.LorentzCarrier` (OBJ-002), `SpinCore.NS` (OBJ-003), `SpinCore.BS`
  (OBJ-004), `SpinCore.ConeS` (OBJ-005), `RequestProject/Spine/E1/Carrier.lean`
* **Lean**
  ```text
  LorentzCarrier := ℝ × (Fin 3 → ℝ)
  NS x           := x.1 ^ 2 - sip x.2 x.2
  BS x y         := (NS (x + y) - NS x - NS y) / 2
  ```
* **Kind** DERIVED STRUCTURE
* **Depends on** OBJ-001
* **THEOREM** `SpinCore.lorentz_quadratic_form` (THM-L001): `NS x = x.1 ^ 2 - (x.2 0 ^ 2 +
  x.2 1 ^ 2 + x.2 2 ^ 2)`.  The carrier is a four-dimensional real quadratic space of
  signature `(1,3)`, obtained from a *positive* datum by the spin-factor construction.
* **Role** `BS` is the form that the solder later transports to the tangent bundle; `ConeS` is
  the cone used to define the intrinsic Lorentz group and the future-cone reductions.
* **Does not claim** that any tangent space of any manifold carries this form.  That statement
  requires the global layer and a regular solder.

## 3. The intrinsic Lorentz group

* **Object** `SpinCore.GLor` (OBJ-006), `RequestProject/Spine/E1/LorentzGroup.lean`
* **Kind** DERIVED STRUCTURE + CONVENTION (determinant `1`, cone preserved)
* **Lean characterisation** `SpinCore.mem_lorentz_group_iff`: `F ∈ GLor` iff `F` preserves `NS`,
  preserves the cone in both directions, and has determinant `1`.
* **Does not claim** any identification with a Lorentz group defined in Mathlib or in the
  literature.  `GLor` is the project's own group and every later Lorentz-side statement is a
  statement about it.

## 4. The intrinsic Clifford layer  [CLAIM-L003], [CLAIM-L004], [CLAIM-L005], [CLAIM-L006]

* **Objects** `SpinCore.q3` (OBJ-007), `SpinCore.Cl3` (OBJ-008), `SpinCore.cle` (OBJ-009),
  `SpinCore.spinToCl` (OBJ-010), `RequestProject/Spine/E1/Clifford.lean`
* **Lean**
  ```text
  q3      : QuadraticForm ℝ (Fin 3 → ℝ)        -- the POSITIVE Euclidean form
  Cl3     := CliffordAlgebra q3
  cle i   := ι q3 (evec i)
  spinToCl x := algebraMap ℝ Cl3 x.1 + ι q3 x.2 -- the paravector embedding
  ```
* **THEOREM** `SpinCore.clifford_generator_square` (THM-L002): the generators square to `+1`;
  together with `cle_anticomm` this is the full Clifford relation of the Euclidean form.
* **THEOREM** `SpinCore.paravector_norm` (THM-L003):
  `spinToCl x * cconj (spinToCl x) = algebraMap ℝ Cl3 (NS x)`.  This is the decisive bridge:
  the *Lorentz* norm of the carrier is the Clifford norm of its paravector image inside a
  *Euclidean* Clifford algebra.
* **THEOREM** `SpinCore.clifford_jordan` (THM-L004): the symmetrized Clifford product of two
  embedded elements is the image of the spin-factor Jordan product,
  `2⁻¹ • (A x * A y + A y * A x) = A (x ∘ y)`.
* **THEOREM** `SpinCore.adjoin_spinToCl_eq_top` (THM-L005): the image of the carrier generates
  `Cl3` as a real algebra.
* **Does not claim** an isomorphism of `Cl3` with a Lorentzian Clifford algebra, nor any
  classification or uniqueness statement about Jordan algebras.

## 5. The intrinsic Spin group and the native projection  [CLAIM-L007]

* **Objects** `SpinCore.SpinGroup` (OBJ-011), `SpinCore.spinCover` (OBJ-012),
  `RequestProject/Spine/E1/SpinGroup.lean`, `E1/SpinCover.lean`, `E1/SpinKernel.lean`
* **Lean** `SpinGroup : Subgroup Cl3ˣ`, `spinCover : SpinGroup →* GLor`, defined by the twisted
  Clifford action on the paravector image of the carrier.
* **CONVENTION** the twisted action, and with it the direction of the square that the solder
  later has to satisfy, is fixed here and never re-chosen.
* **THEOREM** `SpinCore.spin_double_cover_of_lorentz` (THM-L006): the action lands in `GLor`,
  every element of `GLor` arises this way, and exactly `±1` act trivially.
* **THEOREM** `SpinCore.spin_double_cover_bundled` (THM-L007): `spinCover` is a surjective
  group homomorphism with central kernel of cardinality two.
* **Assumptions** none beyond §§1–4.  In particular the statement is proved **without** using
  `SL(2,ℂ)`; the comparison with `SL(2,ℂ)` exists separately and is downstream.
* **Does not claim** that `SpinGroup` is a Lie group or that `spinCover` is a smooth covering
  map.

## 6. The intrinsic Lorentz-skew Lie-algebra layer  [CLAIM-L011]

* **Objects** `SpinCore.gB` (OBJ-043), `SpinCore.gBLie` (OBJ-044), the bivector space
  `⋀[ℝ]^2 LorentzCarrier` with its decomposables `SpinCore.wedge` (OBJ-045),
  `SpinCore.bivectorEquivSkew` (OBJ-046)
* **Modules** `RequestProject/Spine/E1/Bivector.lean`, `RequestProject/Spine/E1/LieAlgebra.lean`
* **Lean**
  ```text
  Kend u v x  := BS v x • u - BS u x • v          -- the skew endomorphism of a decomposable
  gB          : Submodule ℝ (Module.End ℝ LorentzCarrier)
                A ∈ gB ↔ ∀ x y, BS (A x) y + BS x (A y) = 0
  gBLie       : LieSubalgebra ℝ (Module.End ℝ LorentzCarrier)   -- carrier gB
  bivectorEquivSkew : (⋀[ℝ]^2 LorentzCarrier) ≃ₗ[ℝ] gB
  ```
* **Kind** DERIVED STRUCTURE
* **Depends on** OBJ-002, OBJ-004 (the carrier and its polarized form only)
* **THEOREM** `SpinCore.gB_bracket_mem` (THM-L015): the commutator of two `BS`-skew
  endomorphisms is `BS`-skew, which is what makes `gBLie` a Lie subalgebra.
* **THEOREM** `SpinCore.gBLie_bracket` (THM-L013): on `gBLie` the Lie bracket **is** the
  commutator `A * B - B * A` of endomorphisms.
* **THEOREM** `SpinCore.bivectorEquivSkew_wedge` (THM-L014): the equivalence sends the
  decomposable bivector `wedge u v` to `Kend u v`.
* **THEOREM** `SpinCore.finrank_gB` (THM-L012): `Module.finrank ℝ gB = 6`.
* **Role** this is the project's own infinitesimal Lorentz sector: a six-dimensional real Lie
  algebra of endomorphisms skew for the intrinsic form `BS`, linearly equivalent to the second
  exterior power of the intrinsic carrier.  Its construction uses the carrier and `BS` only —
  no Clifford algebra, no Spin group, no topology and no smooth structure.
* **Does not claim**, and this is the boundary that the next research phase starts at, that
  this Lie algebra has been identified with an infinitesimal structure of the intrinsic
  `SpinGroup`.  There is no `Lie(SpinGroup)` in this repository, no proved equivalence
  `Lie(SpinGroup) ≃ gB`, and no differential `dρ_e` of the native cover [CLAIM-B010],
  [CLAIM-B011], `OP-012`.  Textbook facts about `Lie(Spin(1,3))` are **not** available here.

## 7. Topological qualification  [CLAIM-L008], [CLAIM-L009], and the boundary [CLAIM-B001]

* **Modules** `RequestProject/Spine/E1/Topology/Core.lean`, `E1/Topology/LocalSection.lean`
* **THEOREM** `SpinCore.spin_double_cover_topological_endpoint` (THM-L008): `SpinGroup` and
  `GLor` are Hausdorff topological groups, `spinCover` is continuous and surjective, and its
  kernel is central and discrete of cardinality two.
* **THEOREM** `SpinCore.spin_double_cover_local_section_endpoint` (THM-L009): around every
  element of `GLor` there is a neighbourhood carrying a **continuous** section of `spinCover`,
  constructed by explicit algebraic inversion of the twisted action — no covering-space theory
  is quoted.
* **BOUNDARY** [CLAIM-B001]: this is the *whole* regularity available on the Spin side.  There
  is no smooth structure on `SpinGroup` and no exponential map, hence no Lie-group package and
  no infinitesimal object *of the Spin group*.  (The project does have the Lorentz-side skew
  Lie algebra `gB`/`gBLie` of §6; what is missing is the bridge between the two — see
  [CLAIM-B010], [CLAIM-B011], `OP-012`.)  Everything later that is stated with `ContinuousOn`
  on the Spin side is stated that way for this reason, and not by oversight.  See open problems
  `OP-001` and `OP-012`.

## 8. The selected native one-parameter subgroup used by the deformation experiment  [CLAIM-L010]

**Classification (machine-readable: `canonical_status: SELECTED_CONTROL`, `exhaustive: false`;
listed under `control_specific_data` in `PROJECT_STATE.json`).**  The Task-37/38 deformation is
a deliberately selected one-parameter subgroup generated by the chosen Clifford direction
`cle 0` — in the source, `transportElem l = cosh(l/2) + sinh(l/2) · cle 0`
(`RequestProject/Spine/Deformation/SharedTransport.lean`), hence one chosen spatial generator.
It is a control slice through the intrinsic Spin structure, **not** a theorem that this
direction is canonical, exhaustive, or the full deformation space.  The family is built from
the intrinsic Spin/Clifford core — that much is certified — but nothing selects `cle 0` from the
primitive Euclidean input, no uniqueness is proved, and the Task-38 pure-gauge outcome is
neither a classification of the native Spin deformation space nor a statement about every
possible native Spin deformation.

* **Objects** `Task37.Deformation.transportState` (OBJ-031),
  `Task37.Deformation.projectedTransportState` (OBJ-032), `Task37.Deformation.paraMap`
  (OBJ-033)
* **Modules** `RequestProject/Spine/Deformation/SharedTransport.lean`,
  `Deformation/ProjectedParaAction.lean`
* **Lean**
  ```text
  transportState l           : ↥SpinGroup            -- built from a paravector generator
  projectedTransportState l  := spinCover (transportState l)
  paraMap l                  : LocalModel →L[ℝ] LocalModel
                             = id + (cosh l - 1) • paraPlane + sinh l • paraSwap
  ```
* **THEOREM** `Task37.Deformation.transportState_add` (THM-L010): `transportState` is a
  one-parameter subgroup, `transportState (a + b) = transportState a * transportState b`.
* **THEOREM** `Task37.Deformation.projectedTransportState_apply` (THM-L011): the native
  projection of the shared state acts on the local model exactly as `paraMap l`.  The identity
  is *computed* inside the project's own Clifford algebra, not postulated.
* **Role** this is the single Spin-side source of the Task-37/38 deformation.  The Lorentz side
  is obtained only through `spinCover`; there is no independent Lorentz-side knob anywhere.
* **Does not claim** — and this is the point most likely to be misread — that `transportState`
  is a connection, a transport one-form, a parallel transport, a holonomy, or the exponential
  of a curvature.  It is a one-parameter subgroup of a group.  See [CLAIM-B003].  Nor is it
  claimed to be the unique or canonical native Spin deformation direction: see the
  classification paragraph opening this section.

---

## Summary table

| object | Lean name | kind | principal theorem | claim |
| --- | --- | --- | --- | --- |
| Euclidean inner product | `SpinCore.sip` | primitive | — | CLAIM-L001 |
| carrier | `SpinCore.LorentzCarrier` | derived | THM-L001 | CLAIM-L002 |
| quadratic form | `SpinCore.NS` | derived | THM-L001 | CLAIM-L002 |
| polarized form | `SpinCore.BS` | derived | — | CLAIM-L002 |
| Lorentz group | `SpinCore.GLor` | derived + convention | — | CLAIM-L002 |
| Clifford algebra | `SpinCore.Cl3` | derived | THM-L002 | CLAIM-L003 |
| paravector embedding | `SpinCore.spinToCl` | derived | THM-L003 | CLAIM-L004 |
| Jordan compatibility | — | theorem | THM-L004 | CLAIM-L005 |
| generation | — | theorem | THM-L005 | CLAIM-L006 |
| Spin group | `SpinCore.SpinGroup` | derived | THM-L006, THM-L007 | CLAIM-L007 |
| native projection | `SpinCore.spinCover` | derived + convention | THM-L007 | CLAIM-L007 |
| skew Lie algebra | `SpinCore.gB`, `SpinCore.gBLie` | derived | THM-L012, THM-L013, THM-L015 | CLAIM-L011 |
| bivectors ≃ skew algebra | `SpinCore.bivectorEquivSkew` | derived | THM-L014 | CLAIM-L011 |
| topological qualification | — | theorem | THM-L008 | CLAIM-L008 |
| continuous local sections | — | theorem | THM-L009 | CLAIM-L009 |
| selected one-parameter subgroup (`cle 0` control direction) | `Task37.Deformation.transportState` | derived construction, `SELECTED_CONTROL`, not exhaustive | THM-L010, THM-L011 | CLAIM-L010 |

## What the local layer does **not** contain

No manifold, no chart, no tangent space, no bundle, no cocycle over a space, no connection, no
curvature: all of those belong to `docs/mathematics/GLOBAL_MATHEMATICS.md` or, in the case of
connections and curvature, to nothing in this repository at all — see [CLAIM-B003] and
`docs/machine/OPEN_PROBLEMS.jsonl`.

It also does not contain any infinitesimal object attached to the *Spin* side: the certified
infinitesimal structure of §6 lives on the Lorentz side, and the identification with an
infinitesimal Spin structure, together with the differential `dρ_e` of the native cover, is
exactly the first open edge of the next phase [CLAIM-B010], [CLAIM-B011], `OP-012`,
`NEXT_PHASE_TRANSPORT_GATE.md`.
