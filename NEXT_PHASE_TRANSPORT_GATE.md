# NEXT PHASE — the transport gate

**Status of this document.** Canonical, validated, and *forward looking*.  It specifies the
smallest next formalization step of the project.  Nothing in it is implemented, and nothing in
it is proved.  It supersedes the Task-38/39 draft `TASK39_CONNECTION_TRANSPORT_GATE_HANDOFF.md`,
which is retained only as a superseded historical stub.

Claim IDs refer to `docs/machine/CLAIM_REGISTRY.jsonl`, object IDs to
`docs/machine/OBJECT_REGISTRY.jsonl`, theorem IDs to `docs/machine/THEOREM_REGISTRY.jsonl`,
problem IDs to `docs/machine/OPEN_PROBLEMS.jsonl`.

---

## 1. What Task 38 actually proved, at its exact scope

The certified statement is [CLAIM-S001], [CLAIM-S004], [CLAIM-S010], [CLAIM-S011]:

> The specific Task-37 native one-parameter Spin Čech-transition deformation on the frozen
> periodic fixed-cover control base lies in one full-Spin Čech gauge orbit for all finite λ.

together with the Task-39 strengthening:

> On that control the regular solder solution spaces for λ₁ and λ₂ are related by the certified
> transport/equivalence, and the induced tangent Lorentz metric is preserved under that
> certified correspondence.

### Overclaim guard

```text
GENERAL ČECH-DEFORMATION CLASSIFICATION:
    NOT PROVED.
```

The following readings are **forbidden** and appear in `docs/paper/PAPER_I_DO_NOT_CLAIM.md` §6:

* "a transition-cocycle deformation is a change of trivialisation, not a change of geometry";
* "transition-cocycle deformations are pure gauge";
* any statement quantified over all Čech transition deformations, all covers, all base gluings,
  or all families.

Nothing is proved about other bases, other covers, co-varying bases or other families
(`OP-007`, `OP-008`).  What the smoke test licenses is a statement about **one** control and
**one** family, and the honest conclusion drawn from it is a *methodological* one: the first
knob the project was able to build sits above the layer at which a geometric degree of freedom
could be detected by the observables the project currently has.

## 2. What infinitesimal structure the repository already has  [CLAIM-L011]

The earlier draft's claim that the project possesses no Lie algebra was incorrect and is
withdrawn here.  It does have one, on the **Lorentz** side:

| object | Lean | module | status |
| --- | --- | --- | --- |
| bivector space | `⋀[ℝ]^2 SpinCore.LorentzCarrier`, decomposables `SpinCore.wedge u v` (OBJ-045) | `RequestProject/Spine/E1/Bivector.lean` | CERTIFIED |
| skew endomorphisms | `SpinCore.gB : Submodule ℝ (Module.End ℝ LorentzCarrier)` (OBJ-043) | `RequestProject/Spine/E1/Bivector.lean` | CERTIFIED |
| Lie subalgebra | `SpinCore.gBLie : LieSubalgebra ℝ (Module.End ℝ LorentzCarrier)` (OBJ-044) | `RequestProject/Spine/E1/Bivector.lean` | CERTIFIED |
| bivectors ≃ skew | `SpinCore.bivectorEquivSkew : (⋀[ℝ]^2 LorentzCarrier) ≃ₗ[ℝ] gB` (OBJ-046) | `RequestProject/Spine/E1/LieAlgebra.lean` | CERTIFIED |

Proved statements (THM-L012 … THM-L015):

```text
SpinCore.gB_bracket_mem        A ∈ gB → B ∈ gB → A * B - B * A ∈ gB
SpinCore.gBLie_bracket         ⁅A, B⁆ = A * B - B * A   (as endomorphisms, for A B : gBLie)
SpinCore.bivectorEquivSkew_wedge   bivectorEquivSkew (wedge u v) = Kend u v
SpinCore.finrank_gB            Module.finrank ℝ gB = 6
```

`gB` is defined by the *intrinsic* skewness condition `BS (A x) y + BS x (A y) = 0` for the
project's own polarized form `BS`; `Kend u v x = BS v x • u - BS u x • v`.  So the six
dimensions (three "rotations", three "boosts") are produced by the project's own Lorentz data,
not imported.

## 3. What is still missing — the infinitesimal Spin bridge

NOT YET CERTIFIED anywhere in this repository:

* a smooth Lie-group structure on the intrinsic `SpinCore.SpinGroup` [CLAIM-B001], `OP-001`;
* a formal identification `Lie(SpinGroup) ≃ gB`, or any equivalent intrinsic infinitesimal
  Spin/Lorentz identification [CLAIM-B010], `OP-012`;
* the differential of the native cover

  ```text
  dρ_e : Lie(SpinGroup) → gB
  ```

  or an explicitly proved equivalent infinitesimal representation [CLAIM-B011], `OP-012`;
* a native Spin connection built from that infinitesimal structure [CLAIM-B003], `OP-002`.

The existing `SpinCore.spinCover : SpinGroup →* GLor` is a **group-level** homomorphism
(OBJ-012).  A connection one-form is infinitesimal, i.e. Lie-algebra valued.  Therefore the
expression `spinCover ∘ ω` is **not** a meaningful definition of a Lorentz connection and must
never be written; the earlier draft of this document did write it, and that is corrected here.

### Future architectural requirement (not a theorem)

> No independent Lorentz connection knob should be introduced.  Once the intrinsic infinitesimal
> Spin/Lorentz structures are related, the Lorentz-side connection must be induced through the
> differential of the native Spin cover, or through an explicitly proved equivalent
> infinitesimal representation.

## 4. The next open edge, exactly

```text
   existing intrinsic Lorentz-skew Lie algebra gB / gBLie      [CERTIFIED, CLAIM-L011]
                 |
                 |  OPEN EDGE: identification / infinitesimal Spin bridge   [CLAIM-B010, OP-012]
                 v
        Lie(SpinGroup)  ?≃  gB                                  [NOT CONSTRUCTED]
                 |
                 |  OPEN EDGE: dρ_e                                        [CLAIM-B011, OP-012]
                 v
      infinitesimal Spin → Lorentz map                          [NOT CONSTRUCTED]
                 |
                 v
        future shared connection                                [NOT CONSTRUCTED, OP-002]
                 |
                 v
     parallel transport / holonomy                              [NOT CONSTRUCTED, OP-003, OP-004]
                 |
                 v
             curvature                                          [NOT CONSTRUCTED, OP-005]
```

Only the top node exists.  Every arrow below it is missing; none of them may be cited as a
dependency of anything in the present release, and `docs/machine/MATHEMATICAL_DAG.json`
deliberately contains **no** edge `Lie(SpinGroup) → gB` (the missing bridges are listed in its
`open_edges` field and in `OPEN_PROBLEMS.jsonl`, not among its `edges`).

## 5. The minimal missing objects, in dependency order

The methodological rule of the project must be preserved: **one native Spin-side source, the
Lorentz side derived through the native cover, the tangent side derived by the solder.**  No
independent Lorentz-side knob at any stage.

1. **The infinitesimal Spin bridge.**  Either a smooth/Lie structure on `SpinGroup` with
   `Lie(SpinGroup) ≃ gB`, or an explicitly proved project-native substitute: an intrinsic
   generator space inside `Cl3` (bivectors and paravector generators, as used by
   `Task37.Deformation.transportState`) together with a proved infinitesimal representation into
   `gB` playing the role of `dρ_e`.  This is the real cost of the next phase and should be
   scoped alone if necessary (`OP-012`).
2. **Local Spin-side transport one-forms.**  For each patch `i` of the emergent cover, a `C^∞`
   field `ω_i` on `D i` valued in the generator space of step 1 (`OP-002`).
3. **The exact transformation law across an overlap**, written with the *already fixed* Čech
   convention `g_ij` of `SpinNative.TransitionData` — it must be **derived** from that
   convention, not chosen by analogy:
   `ω_j = g_ij⁻¹ ω_i g_ij + g_ij⁻¹ d g_ij` in the project's own notation.
4. **Parallel transport along a path** in a chart, as the solution of the transport equation,
   and its chart independence under 3 (`OP-003`).
5. **Loop transport around the wrap-around component** of the frozen periodic model — the first
   place where the two-component periodic overlap can produce a nontrivial invariant
   (`OP-004`).
6. **The field strength** `F = dω + ω ∧ ω` and its gauge covariance (`OP-005`).
7. **Projection to the Lorentz side** of every one of 1–6 through the *infinitesimal* map of
   step 1 — never through `spinCover` applied to a one-form — and **transport to the tangent
   side** through the existing regular solder.

## 6. The gate question for the next phase

Only steps **1–3** should be built, and the gate question is the *same* smoke test, one layer
down:

> For the frozen periodic control base, is there a one-parameter family `ω^(λ)` of native
> Spin-side transport one-forms which is **not** gauge equivalent at the level of the law of
> step 3 — i.e. for which no chartwise Spin gauge carries `ω^(λ)` to `ω^(0)`?

Task 38 fixes the shape of the anti-vacuity obligation for that test:

* build the candidate family from **one** shared Spin-side source, as Task 37 did;
* check that the negative direction is still available — exhibit at least one family that *is*
  gauge equivalent, so that the notion separates;
* only then ask for an invariant.

## 7. Hard constraints inherited from Tasks 36–39

* The base gluing stays frozen (CONTROL A) until the transport layer is decided; a co-varying
  base (MAIN TEST B) is a separate experiment and must not be used to rescue a failed fixed-base
  test.
* No independent Lorentz-side one-form may be introduced; it must be induced through the
  infinitesimal map of step 1 (`dρ_e` or a proved equivalent).  `spinCover ∘ ω` is a type error
  and is forbidden.
* Do not assume that a regular solder exists: it is an additional global gate datum and its
  existence can fail [CLAIM-B007], [CLAIM-G017].
* No curvature, sectional curvature, sphere, hyperbolic space, de Sitter, anti-de Sitter,
  cosmological constant or field equation may appear as an *input* or as a branch selector.
  The field strength of step 6 may only be *computed*, never *targeted*.
* The existing branch firewall must be extended to the new modules before they are trusted: leaf
  property, field lists of any new structure, and the declaration-name token audit.
* No `sorry`, no new axiom, no `native_decide`, no `Matrix.inv`; `#print axioms` on every
  endpoint.

## 8. Expected failure modes to plan for

* The Spin side has **no** smooth structure and no exponential map [CLAIM-B001]; the Lorentz
  side *does* have the certified skew Lie algebra `gB` [CLAIM-L011].  The gap is precisely the
  bridge between them, and it must not be papered over by importing textbook facts about
  `Lie(Spin(1,3))`: nothing of that kind is formalized here.
* Parallel transport needs an ODE existence theorem in the pinned Mathlib; if the general
  statement is unavailable, the frozen periodic model is one-dimensional along the loop
  coordinate and admits an explicit solution, which is enough for the gate question.
* If step 3's transformation law cannot be *derived* from the existing Čech convention, stop and
  report that, rather than choosing a convention by analogy — this is the mistake Task 38 was
  explicitly built to avoid.
