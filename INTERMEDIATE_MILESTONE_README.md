# READ FIRST — intermediate milestone of this project

**Status: TASK 40 — INTERMEDIATE RELEASE HARDENING: PASS / FROZEN.**
(The mathematics is the frozen Task-39 intermediate closure, unchanged; Task 40 corrected the
documentation and the machine-readable snapshot only.)

This is the authoritative entry point.  It is written so that a reviewer can understand what
the project has and has not achieved **without reading the Lean sources**.  Every substantive
claim below carries a stable Claim ID; the full record is in `docs/machine/CLAIM_REGISTRY.jsonl`.

```text
    L = local mathematics      G = global mathematics     S = smoke-test result
    N = negative control       B = blocker / boundary
```

---

## 1. What the project asks

> Starting from nothing but a positive Euclidean three-dimensional space, how far can one get
> towards four-dimensional Lorentzian geometry by *construction* — and at which layer does the
> first genuinely geometric degree of freedom appear?

Everything below is an answer to the first half.  The second half is where the present phase
stops, deliberately and with the reason recorded.

## 2. The primitive mathematical input

* ℝ³ with the **positive definite** Euclidean inner product `SpinCore.sip` [CLAIM-L001].
  No signature, no metric on a manifold, no orientation, no time direction.
* Later, and provably additional, two global inputs:
  a **base-gluing datum** [CLAIM-G001] and a **native Spin transition datum**; and then
  a **regular solder** where one exists [CLAIM-G006], [CLAIM-B007].

## 3. What is derived from it (local layer)

| derived object | statement | claim |
| --- | --- | --- |
| spin-factor carrier ℝ ⊕ ℝ³ with a form of signature (1,3) | `NS x = x₀² − ‖x⃗‖²` | [CLAIM-L002] |
| intrinsic Clifford algebra `Cl₃` of the *positive* form | generators square to `+1` | [CLAIM-L003] |
| paravector embedding | realises the Lorentz norm as the Clifford norm | [CLAIM-L004] |
| Clifford / Jordan compatibility | symmetrized product = Jordan product | [CLAIM-L005] |
| intrinsic Spin group and native projection | surjective, central kernel of order 2 | [CLAIM-L007] |
| topological qualification | Hausdorff topological groups, continuous cover, discrete kernel | [CLAIM-L008] |
| continuous local sections of the cover | explicit algebraic inversion | [CLAIM-L009] |
| intrinsic Lorentz-skew Lie algebra `gB` / `gBLie` ≃ bivectors `⋀²` of the carrier | six-dimensional, bracket = commutator | [CLAIM-L011] |
| a native one-parameter Spin subgroup with explicit projected action | used by the deformation test | [CLAIM-L010] |

Details, with Lean names: `docs/mathematics/LOCAL_MATHEMATICS.md`.

## 4. What additional global data enter later

1. the base gluing (pieces, incidence domains, identification maps) — **not** derivable from the
   local core [CLAIM-G001];
2. its smoothness, an extra hypothesis with an explicit counterexample if dropped [CLAIM-G003];
3. a native Spin transition datum over the emergent cover;
4. a **regular solder** — the decisive coupling, which does not always exist [CLAIM-G017].

## 5. The local-to-global architecture

```text
 ℝ³, positive form ─► carrier, NS/BS ─► Cl₃, paravectors ─► SpinGroup ─► spinCover ─► GLor
                                                                                      │
 BaseGluingData ─► Space B ─► (SmoothGluing) ─► smooth 4-manifold ─► D(φ_ij) = tangent transitions
                                                                                      │
        native Spin transition datum ─► internal Lorentz bundle ─┐                    │
                                                                 ├─ REGULAR SOLDER ───┤
                                                                 │   (the gate)       │
                                              smooth tangent Lorentz metric (1,3) ◄───┘
                                                       │
                     orientation compatibility ── project-native Spin obstruction trivial
                                                       │
                                            future-cone (time-orientation) reduction
```

Stage-by-stage, with inputs, outputs, gates and controls:
`docs/mathematics/GLOBAL_MATHEMATICS.md`.
Where algebra stops and geometry starts: `docs/mathematics/LOCAL_GLOBAL_INTERFACE.md`.

## 6. The current strongest results

* a smooth, Hausdorff, second countable, four-dimensional emergent manifold from a smooth
  gluing [CLAIM-G004];
* the genuine tangent transitions of that manifold are the derivatives of the gluing maps
  [CLAIM-G005];
* a regular solder **is** a bundle equivalence between the internal Lorentz bundle and `TM`, at
  a precisely stated regularity [CLAIM-G008] — continuous total-space maps with `C^∞` local
  representatives.  A regular smooth solder also gives smooth local/projected Lorentz transition
  representatives, so smoothness of the native Spin cocycle is **not** what is needed for smooth
  projected Lorentz bundle data; the stronger total-space smooth packaging is missing for an
  **infrastructure / packaging** reason (no vector-bundle equivalence type in the pinned
  library), and smooth projected Lorentz data is **not** a packaged smooth intrinsic Spin
  Lie-group bundle theory [CLAIM-B001];
* a regular solder induces a `C^∞` tangent Lorentz metric of signature (1,3), tensorial under
  the genuine tangent transitions [CLAIM-G009], [CLAIM-G010];
* **reconvergence**: a regular solder forces project-native orientation compatibility and
  triviality of the project-native Spin-lifting obstruction, in a construction that assumed
  neither [CLAIM-G011], [CLAIM-G013]; both contrapositives are proved [CLAIM-G012],
  [CLAIM-G014];
* a regular solder yields a coherent future-cone reduction [CLAIM-G015];
* the residual freedom of the coupling is exactly a free transitive gauge action [CLAIM-G016];
* the discrete fixed-cover Spin-lift freedom is *not* destroyed [CLAIM-G018], [CLAIM-G019];
* one Lean certificate aggregates the whole frozen state [CLAIM-G023].

## 7. The adversarial negative controls

| id | what it rules out |
| --- | --- |
| [CLAIM-N001], [CLAIM-N002] | reading a fibrewise solder as a geometry: an explicit weak solder has a discontinuous representative *and* a discontinuous induced metric |
| [CLAIM-N003] | "the solder always exists": the Möbius-type gluing admits none, for any Spin datum |
| [CLAIM-N009] | "an internal Spin seed implies a tangent Spin structure": Spin data exist there, a solder does not |
| [CLAIM-N004], [CLAIM-N005] | "the construction canonizes the Spin lift": the discrete freedom survives |
| [CLAIM-N006] | "the closure observable is toothless": no universal existence theorem, and a family that is admissible *only* at the neutral value |
| [CLAIM-N007] | "any two cocycles are gauge equivalent anyway": the narrower kernel-valued relation separates them |
| [CLAIM-N008] | a combinatorial shortcut to the coupling |
| [CLAIM-N010] | vacuously restrictive gates: the one-chart positive control passes |

## 8. The Task-38 smoke test, and its Task-39 strengthenings

The experiment varies **one** thing: the native Spin Čech transition state of the frozen
periodic control base, with the Lorentz side derived only through the native projection
[CLAIM-S012].  The deformation is a **deliberately selected** one-parameter subgroup generated
by the chosen Clifford direction `cle 0` [CLAIM-L010] — a control slice through the intrinsic
Spin structure, not a theorem that this direction is canonical, exhaustive, or the full
deformation space.  On that control:

* every finite parameter value is globally admissible, with an explicitly constructed
  compensating regular solder; the admissibility locus is all of ℝ, solved exactly rather than
  sampled [CLAIM-S001], [CLAIM-S002], [CLAIM-S007];
* the whole family lies in **one** full-Spin Čech gauge orbit, and so does its projection
  [CLAIM-S004], [CLAIM-S005];
* at the narrower kernel-valued relation the parameter values *are* separated — a statement
  about lift labels only [CLAIM-S006];
* along the explicit branch the induced tangent Lorentz metric is literally unchanged
  [CLAIM-S008];
* **Task 39 §4**: the *projected Lorentz* gauge is `C^∞` on every chart domain; the Spin-side
  gauge remains certified as **continuous only** [CLAIM-S009];
* **Task 39 §5**: the regular solder **solution spaces** at two parameter values are in
  explicit bijection, and corresponding solutions induce exactly the same tangent Lorentz
  metric [CLAIM-S010].

The certified scientific reading, scoped exactly [CLAIM-S011]:

> The specific Task-37 native one-parameter Spin Čech-transition deformation on the frozen
> periodic fixed-cover control base is globally admissible for all finite λ and lies in one
> full-Spin Čech gauge orbit.  On that control the regular solder solution spaces at any two
> parameter values correspond, and corresponding solutions induce the same tangent Lorentz
> metric; in particular no λ-dependent tangent Lorentz metric remains.

## 9. What is **not** proved

* no smooth Lie-group package for the intrinsic Spin group; the Spin-side gauge is continuous
  [CLAIM-B001];
* the certified Lie algebra `gB`/`gBLie` [CLAIM-L011] is **not** identified with an
  infinitesimal structure of the intrinsic `SpinGroup`: there is no `Lie(SpinGroup)` object, no
  proved `Lie(SpinGroup) ≃ gB` [CLAIM-B010] and no differential `dρ_e` of the native cover
  [CLAIM-B011].  `spinCover` is group-level and must never be applied to a connection one-form;
* the project-native Spin obstruction is **not** formally compared with `w₂(TM)`, and the
  orientation gate is **not** `w₁(TM) = 0` [CLAIM-B002];
* **no connection, no parallel transport, no holonomy, no curvature, no field equation, no
  cosmology** — no such object exists in the source, and the deformation firewall forbids even
  naming one [CLAIM-B003], [CLAIM-B008];
* the periodic control is **not** proved homeomorphic to `S¹ × ℝ³`, and nothing about its
  fundamental group is proved [CLAIM-B004];
* the fixed-cover lift freedom is **not** `H¹(M; ℤ/2)` [CLAIM-B005];
* the future-cone reduction is **not** proved equivalent to standard time-orientability
  [CLAIM-B006];
* there is **no** general existence theorem for the regular solder [CLAIM-B007];
* where the first genuinely gauge-nontrivial deformation lives is an **open question**
  [CLAIM-B009];
* the Task-38/39 smoke-test result is scoped to the tested family on the frozen periodic
  control base; a general Čech-deformation classification is **not proved** [CLAIM-S011],
  `OP-007`, `OP-008`.

The next research boundary, drawn exactly — existing Lorentz-skew Lie algebra, then the missing
infinitesimal Spin bridge, then `dρ_e`, then a connection, transport, holonomy and curvature —
is in `NEXT_PHASE_TRANSPORT_GATE.md`.

A blunt list of sentences that must never be written appears in
`docs/paper/PAPER_I_DO_NOT_CLAIM.md`.

## 10. How to reproduce the build

```bash
lake build RequestProject                               # 8356 jobs, green
lake build RequestProject.Spine.Audit.Firewall          # legacy/layering firewall
lake build RequestProject.Spine.Task36.Firewall         # adversarial-battery firewall
lake build RequestProject.Spine.Deformation.Firewall    # deformation + closure branch firewall
lake build RequestProject.Spine.Closure.AxiomAudit      # #print axioms on 67 endpoints
python3 audit/verify_documentation_snapshot.py          # documentation snapshot validator
```

Toolchain: Lean `leanprover/lean4:v4.28.0`, Lake `5.0.0-src+7e01a1b`, Mathlib pinned at
`v4.28.0` (see `lake-manifest.json`).  The historical experiment trees are **not** a default
target; build them with `lake build LegacyProvenance`.

Proof hygiene: no `sorry`, no `admit`, no project `axiom`, no `native_decide`, no `unsafe`, no
`implemented_by`, no `Matrix.inv` in the mathematics.  Every audited endpoint reports
`[propext, Classical.choice, Quot.sound]` (`TASK39_AXIOM_AUDIT.md`).  Localized exceptions are
listed exactly in `TASK39_CODE_HYGIENE.md`.

## 11. Where the machine-readable registries live

```text
docs/machine/SCHEMA_VERSION            1
docs/machine/PROJECT_STATE.json        the frozen state in one object
docs/machine/CLAIM_REGISTRY.jsonl      every scientific claim, its status and its scope
docs/machine/THEOREM_REGISTRY.jsonl    every principal theorem, statement text copied from source
docs/machine/OBJECT_REGISTRY.jsonl     every principal mathematical object
docs/machine/MODULE_REGISTRY.jsonl     every relevant Lean module
docs/machine/NEGATIVE_CONTROLS.jsonl   every adversarial control
docs/machine/OPEN_PROBLEMS.jsonl       what is missing, and why
docs/machine/FAILBUILD_LEDGER.jsonl    index of all historical failed builds
docs/machine/PROVENANCE_LEDGER.jsonl   discovery provenance (kept separate from dependency)
docs/machine/MATHEMATICAL_DAG.json     what depends on what
docs/machine/PROVENANCE_DAG.json       how the research path developed
docs/machine/VERIFICATION_DAG.json     what verifies what
docs/machine/SOURCE_MANIFEST.json      sizes and SHA-256 of every source and doc file
docs/machine/RELEASE_MANIFEST.json     the release fingerprint
docs/machine/PROJECT_INDEX.tsv         generated claim/theorem index
docs/graphs/*.dot                      the same three DAGs in Graphviz form
```

Recommended reading order for a future reviewer is given in
`PROJECT_INTERMEDIATE_HANDOFF.md`.
