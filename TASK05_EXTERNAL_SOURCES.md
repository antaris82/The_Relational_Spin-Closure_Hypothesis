# TASK05_EXTERNAL_SOURCES.md — append-only external-source ledger

Scope: Task 5 (native mod-2 singular cohomology foundation for the `w₂` certification branch).

**Policy.** Every external Lean project below was inspected as *scholarly and engineering
reference material only*. None is a dependency of this project. No file was copied, no
namespace was imported, no declaration was mechanically renamed into the Spine, no external
theorem is treated as proved inside this project, and no adapter hides an external dependency.
The Spine builds with all external repositories absent; the mechanical check is
`RequestProject.Spine.Audit.Firewall` (`auditNoExternal`, run over all 132 Spine modules:
external-project imports = 0).

**Attribution is required even though no code was copied.** Where the native construction
converged on the same mathematical design as prior work, this is stated explicitly below, and
no novelty is claimed for the independent reimplementation.

Access method for all entries: public `git clone` on the access date shown, inspection of the
working tree at the recorded commit, outside the project directory. Nothing was vendored.

---

## Entry A — `NetRxn/SK_EFT_Hawking`

| field | value |
|---|---|
| project | SK-EFT Hawking (SKEFTHawking Lean library) |
| owner / author | GitHub user `NetRxn` |
| repository | `https://github.com/NetRxn/SK_EFT_Hawking` |
| commit inspected | `e7abc5d944bf7350d6de14de5ec8cb26c66e7f74` (dated 2026-08-17) |
| access date | 2026-09-08 |
| files inspected | `lean/SKEFTHawking/SingularCohomologyMod2.lean` (full, 1127 lines); `lean/SKEFTHawking/PoincareDualityWu.lean` (full, 93 lines); `lean/SKEFTHawking/SymTFT/StiefelWhitney.lean` (header and declaration list, 363 lines); `README.md`; `lean/lean-toolchain` |
| licence | no `LICENSE` file was found at the repository root at the inspected commit; licence status therefore **not identifiable**. This is a further reason why nothing was copied. |
| Lean/toolchain | `leanprover/lean4:v4.32.0` (this project is pinned to v4.28.0, so the sources are not even directly reusable) |
| classification | **THEOREM_DECOMPOSITION_REFERENCE** + **MATHLIB_API_REFERENCE** for `SingularCohomologyMod2.lean`; **DESIGN_REFERENCE** for `PoincareDualityWu.lean`; **NEGATIVE_CONTROL** for `SymTFT/StiefelWhitney.lean` |

### Mathematical concepts consulted

* that Mathlib supplies the singular *chain* complex but no singular *cohomology*, and that
  `TopCat.toSSet` (the singular simplicial set) is the practical carrier for a cochain-level
  construction;
* that `SimplexCategory.δ_comp_δ` is the identity that drives `δ² = 0`;
* that in characteristic two the alternating sum degenerates to a plain sum, and the
  cancellation in `δ² = 0` becomes a pairing of the index set `Fin (n+3) × Fin (n+2)`;
* that the Alexander–Whitney front/back inclusions have to be re-declared at shifted indices
  because `(p+1)+q` and `(p+q)+1` are not definitionally equal in Lean;
* (from `PoincareDualityWu.lean`) which foundational bricks remain after singular cohomology
  exists on the Wu route: a fundamental-class functional, non-degeneracy of the middle cup
  pairing, finite-dimensionality — i.e. exactly the Poincaré-duality input, which that file
  *assumes as a structure* rather than deriving from a manifold.

### Implementation ideas consulted

* the choice of `(TopCat.toSSet.obj X).obj (op [n]) → ZMod 2` as the cochain carrier;
* the packaging of the coboundary as a `ZMod 2`-linear map, and of `Hⁿ` as a `Submodule`
  quotient of `ker δ`;
* the strategy of proving the Leibniz rule from explicit composition identities between the
  front/back inclusions and the cofaces, split at the index `p`.

### Influence on local design — stated honestly

Yes, the reference influenced local design, and the native construction **converged on
essentially the same mathematics**. The following native statements resemble external
statements at the level of mathematical content (they are the standard textbook definitions,
independently re-derived here, but the prior Lean realisation was inspected first and must be
credited): singular cochain carrier, face operator, coboundary, `δ² = 0`, cocycles,
coboundaries, quotient `Hⁿ`, Alexander–Whitney cup product, Leibniz rule, descended products
`H¹×H¹→H²` and `H²×H²→H⁴`.

The proof architecture of `δ² = 0` also resembles the external one in its mathematical core
(pair the double index set via `δ_comp_δ`; conclude by `x + x = 0`), although the Lean tactic
realisation differs (the native proof splits the index set with
`Finset.sum_filter_add_sum_filter_not` and matches the two halves with `Finset.sum_bij'`,
where the external proof uses `Finset.sum_involution`).

Differences of the native layer: it is degree-generic throughout, it adds a **functoriality
layer** (`pullback`, `pullback_d`, `Hmap`, `Hmap_id`, `Hmap_comp`) that the inspected external
file does not contain, and it states the Leibniz rule in a single degree-generic pointwise form
from which the degreewise descent lemmas are derived, rather than proving separate
`cup_coboundary_*` statements per degree pair.

### What was **not** used

* no line of external Lean source was copied;
* `PoincareDualityWu.lean`'s `PoincareDual4Mid` structure was **not** reproduced and no
  Poincaré-duality datum is assumed anywhere in the Spine;
* `SymTFT/StiefelWhitney.lean` is a **negative control**: it explicitly ships *opaque*
  cohomology carriers plus a `HasStiefelWhitney` typeclass whose instances *supply* the values
  of `w₁, w₂` as data. That is precisely the pattern this task forbids (anti-shortcut
  constraints 4 and 5), and the distinction between the genuine singular-cohomology layer and
  that narrower predicate/substrate layer is recorded here and in `TASK05_AUDIT.md`. It is not
  a construction of `w₂(TM)` for an arbitrary real vector bundle, and it is not used as a
  substitute for conventional `w₂(TM)`.

### Citation for a later paper

> NetRxn, *SK-EFT Hawking* (Lean 4 library), files
> `lean/SKEFTHawking/SingularCohomologyMod2.lean`,
> `lean/SKEFTHawking/PoincareDualityWu.lean`,
> `lean/SKEFTHawking/SymTFT/StiefelWhitney.lean`,
> repository `https://github.com/NetRxn/SK_EFT_Hawking`,
> commit `e7abc5d944bf7350d6de14de5ec8cb26c66e7f74`, accessed 2026-09-08.

---

## Entry B — `TataSatyaPratheek/mathematical-physics-lean`

| field | value |
|---|---|
| project | mathematical-physics-lean (`MathPhysics`) |
| owner / author | Satya Pratheek Tata (GitHub `TataSatyaPratheek`) |
| repository | `https://github.com/TataSatyaPratheek/mathematical-physics-lean` |
| commit inspected | `f897b7f42c6ce9681692c9e7f9160e91bfd9028a` (dated 2026-07-07) |
| access date | 2026-09-08 |
| files inspected | `MathPhysics/FibreBundles/Principal.lean` (full, 176 lines); `lean-toolchain`; `lakefile.lean`; repository-wide scan for `axiom` declarations |
| licence | MIT License, "Copyright (c) 2026 Satya Pratheek Tata" |
| Lean/toolchain | `leanprover/lean4:v4.26.0`; the project does **not** depend on Mathlib — it rebuilds its algebraic foundations itself |
| classification | **DESIGN_REFERENCE** (bundle-structure shape) + **NEGATIVE_CONTROL** (trust boundary) |

### Concepts / ideas consulted

`Principal.lean` bundles a principal `G`-bundle as: a projection `P → B` with surjectivity, a
`RightAction` structure, fibre preservation, freeness and fibrewise transitivity, plus
`GaugeTransformation` with identity, composition and inverse. This is a useful *shape* check
for a future principal-bundle layer of the wider research programme.

### Trust-boundary audit (mandatory finding)

The repository contains **362 `axiom` declarations** across its Lean sources (for example
`MathPhysics/Algebra/CliffordAlgebra.lean` declares `spinGroup`, `spin_twisted_adjoint`,
`spin_adjoint_preserves_form`, `spin_double_cover_kernel` and
`clifford_universal_property` as axioms, and `MathPhysics/Algebra/FinVec.lean` axiomatises
finite sums). Its overall architecture therefore rests on explicit axiomatic foundations and is
**incompatible with the Spine proof policy** (no project-local axioms; every principal
declaration must report only `propext`, `Classical.choice`, `Quot.sound`). No theorem of that
project may be, and none is, treated as part of the trusted kernel here.

### What was not used, and influence

Nothing was imported or copied. No Task-5 declaration is derived from this project; Task 5
deliberately builds **no** general principal-bundle library (explicit non-goal). Influence on
Task 5: none beyond confirming that a hand-rolled principal-bundle structure is feasible but
that its trust posture must be checked before reuse.

### Citation for a later paper

> S. P. Tata, *mathematical-physics-lean*, file `MathPhysics/FibreBundles/Principal.lean`,
> repository `https://github.com/TataSatyaPratheek/mathematical-physics-lean`,
> commit `f897b7f42c6ce9681692c9e7f9160e91bfd9028a`, MIT licence, accessed 2026-09-08.

---

## Entry C — `trigunino/janus-formal`

| field | value |
|---|---|
| project | janus-formal (`JanusFormal`) |
| owner / author | GitHub user `trigunino` |
| repository | `https://github.com/trigunino/janus-formal` |
| commit inspected | `a72627275802c48f4b2ac96629ab0eec1d7d98d7` (dated 2026-07-21) |
| access date | 2026-09-08 |
| files inspected | `JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple/Gates/P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D.lean` (structure of `ambientPinMinusPrincipalBundleCore`, right action, certificate structure); declaration lists of the sibling `…CanonicalPinMinusActualPrincipalBundle4D`, `…ProgramPAmbientPinCActualPrincipalBundle4D`, `…ProgramPAmbientCircleWindingBundle4D` files; `README.md`; `lean-toolchain` |
| licence | no `LICENSE` file found at the repository root at the inspected commit; licence status **not identifiable** |
| Lean/toolchain | `leanprover/lean4:v4.31.0` |
| classification | **DESIGN_REFERENCE** only |

### Concepts / ideas consulted

Architectural evidence that principal-bundle-like total spaces can be reconstructed on top of
existing Mathlib bundle primitives: those files build Mathlib `FiberBundleCore` data whose
`coordChange` is supplied by a Čech-style choice of local lifts satisfying a cocycle condition,
and then read off `FiberBundle` instances and a right regular action. That is a concrete
demonstration that the Čech-cocycle → bundle-core route is viable in Lean.

### Explicit limitation

The setting there is Pin⁻/Pin^c on a specific mapping-torus geometry. That is **not** the
Spin/Lorentz setting of this project, and no assumption of theirs is imported. Whether their
constructions are appropriate for the Spin⁺(1,3)-frame problem was **not** assumed and is not
claimed.

### Influence on Task 5

None on the cohomology layer. Recorded because the wider research programme (Spin lift →
associated Lorentz bundle → soldering) will face the same reconstruction problem; that branch
is deliberately not merged with the present certification branch.

### Citation for a later paper

> trigunino, *janus-formal*, files under
> `JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple/Gates/`
> (Pin⁻ / Pin^c principal-bundle cores), repository
> `https://github.com/trigunino/janus-formal`,
> commit `a72627275802c48f4b2ac96629ab0eec1d7d98d7`, accessed 2026-09-08.

---

## Entry D — `roed314/gq2` (name-collision negative control)

> **Corrected during Task-6 maintenance (2026-09-08).**  The Task-5 version of this entry
> recorded the repository as `roed-math/gq2-lean` / `roed314/gq2-lean` and reported it as
> inaccessible.  That path was wrong.  The correct, accessible repository is
> `https://github.com/roed314/gq2`; it was inspected on 2026-09-08 and the entry below
> replaces the earlier one.  The *classification is unchanged*: **NEGATIVE_CONTROL, NOT_USED**.

| field | value |
|---|---|
| project | gq2 — "A Presentation of the Absolute Galois Group of the 2-adic Numbers" (project site) |
| owner / author | `roed314` (David Roe), with David Turturean (per `CITATION.cff`) |
| repository | `https://github.com/roed314/gq2` |
| commit inspected | `a2b1481f5e87acbb732b1e0fcf308a7ac2a9013a` (HEAD of `main`, dated 2026-09-01) |
| access date | 2026-09-08 |
| access result | clone succeeded; the repository at that commit is the **project web site**: generated Lean documentation (`lean/gq2-claude/**`, `lean/gq2-gpt/**`), blueprints, paper and vendored web assets.  It contains **no `.lean` source files** at this commit (`find . -name '*.lean'` → 0). |
| licence | no repository-level licence file at the inspected commit; the only licences present are those of vendored web components (KaTeX, DOMPurify, marked).  Since nothing was used, no licence obligation arises. |
| file consulted | `lean/gq2-claude/GQ2/StiefelWhitney.html` (generated documentation of the module `GQ2.StiefelWhitney`) |
| concept consulted | the *name* `StiefelWhitney` and the subject matter of that module |
| influence classification | **NEGATIVE_CONTROL**, **NOT_USED** (no code, no statement, no design was taken) |

### What is recorded

The module `GQ2.StiefelWhitney` documents `swOne`/`swTwo`: Stiefel–Whitney (Hasse–Witt)
invariants `w₁ q`, `w₂ q` of *nondegenerate binary quadratic forms* over a dyadic base field,
valued in the Galois cohomology `Hⁱ(G_k, 𝔽₂)`, together with their well-definedness on isometry
classes and their values on diagonal representatives.  This is a **different mathematical
object** from the characteristic class `w₂(TM) ∈ H²(M;ℤ₂)` of the tangent bundle of a manifold:
the quadratic-form invariants live in Galois cohomology of a field, not in the cohomology of a
topological space, and they classify forms up to isometry rather than bundles up to
isomorphism.  The two theories are related only through classical comparison statements in
special situations, none of which is the statement this project needs.

**Methodological consequence, adopted here:** external declarations must never be matched by
name.  In this project the identification of a candidate `w₂` is required to be by
*construction and theorem*, never by declaration name.  Nothing from this repository was
inspected for technique, copied, imported, or relied upon.

---

## Entry E — Lean community discussion on principal bundles in Mathlib

| field | value |
|---|---|
| source type | Lean community discussion / Mathlib issue-tracker context on the historical status of principal-bundle infrastructure |
| access date | 2026-09-08 |
| classification | **BACKGROUND_ONLY** |
| use | historical / API context only |

What is used from it: the background understanding that Mathlib has long had fibre-bundle
infrastructure (`FiberBundle`, `FiberBundleCore`, vector bundles, `Trivialization`) but has not
had a general principal-bundle API, and that characteristic classes of real vector bundles
(Stiefel–Whitney classes in particular) are absent. This is **not** treated as a theorem
source; every statement about the pinned library used in Task 5 was verified directly against
the pinned Mathlib in `TASK05_AUDIT.md`, WP1. No specific claim of any discussion thread is
relied upon, and no thread is cited as evidence for a mathematical fact.

---

## Summary table

| entry | project | classification | code copied | imported | influenced local design | statements resemble external | proof architecture resembles external |
|---|---|---|---|---|---|---|---|
| A | NetRxn/SK_EFT_Hawking | THEOREM_DECOMPOSITION_REFERENCE / MATHLIB_API_REFERENCE / DESIGN_REFERENCE / NEGATIVE_CONTROL (`SymTFT/StiefelWhitney.lean`) | no | no | **yes** | **yes** (standard constructions; convergent) | **partly** (same mathematical pairing in `δ²=0`; different tactic realisation) |
| B | TataSatyaPratheek/mathematical-physics-lean | DESIGN_REFERENCE / NEGATIVE_CONTROL (axiomatic trust boundary) | no | no | no | no | no |
| C | trigunino/janus-formal | DESIGN_REFERENCE | no | no | no | no | no |
| D | roed314/gq2 (corrected path, commit `a2b1481f`) | NEGATIVE_CONTROL / NOT_USED | no | no | no | no | no |
| E | Lean community discussion | BACKGROUND_ONLY | n/a | n/a | no | n/a | n/a |

---

## Addendum (Task 6, 2026-09-08)

* Entry D above has been **corrected**: the repository is `https://github.com/roed314/gq2`,
  inspected at commit `a2b1481f5e87acbb732b1e0fcf308a7ac2a9013a`, and is recorded permanently
  as a name-collision **NEGATIVE_CONTROL** (`GQ2.StiefelWhitney` concerns Stiefel–Whitney /
  Hasse–Witt invariants of quadratic forms in Galois cohomology, not tangent-bundle
  characteristic classes).  Entries A, B, C and E are unchanged.
* **No external Lean project was consulted for the mathematics of Task 6.**  The fixed-cover
  Čech complex, `δ_Č² = 0`, the quotient `Ȟⁿ(𝓤;ℤ₂)`, the refinement pullback and all bridge
  theorems were written from the standard definitions and from material already in this
  repository.  No new external entry of type EXTERNALLY_INFORMED arises; no external project is
  a dependency (`lakefile.toml` requires Mathlib only, and the mechanical `auditNoExternal`
  check reports 0 external-project imports over every Spine module).  Details:
  `TASK06_AUDIT.md`, §9.

---

## Addendum (Task 7, 2026-09-08)

* **No external Lean project was inspected, consulted or copied for Task 7.**  Entries A–E above
  are unchanged and remain the complete external ledger; none of them is a dependency
  (`lakefile.toml` requires Mathlib only, and the mechanical `auditNoExternal` check reports 0
  external-project imports over the 154 Spine modules in the audit environment; 156 modules exist
  in the archive).
* The only sources read while implementing Task 7 were the **pinned Mathlib sources
  themselves**, classified `MATHLIB_API_REFERENCE`:
  `Mathlib/Topology/Homotopy/Contractible.lean`,
  `Mathlib/Topology/Homotopy/LocallyContractible.lean`,
  `Mathlib/Analysis/Convex/Contractible.lean`,
  `Mathlib/Analysis/Normed/Module/Connected.lean`,
  `Mathlib/Topology/OpenPartialHomeomorph/Basic.lean`,
  `Mathlib/Topology/Homeomorph/Lemmas.lean`,
  `Mathlib/AlgebraicTopology/SingularSet.lean`,
  `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`
  (Mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`, Apache-2.0, accessed 2026-09-08).
  Concepts consulted: strong local contractibility and its transfer along open embeddings;
  contractibility of convex sets and balls; the chart-restriction homeomorphisms; the singular
  simplicial set and the geometric realization functor.  Influence: API names and the shape of
  the transfer lemmas; all Task-7 proofs were written here.
* Searched for and **not found** in the pinned library, hence built or specified natively:
  good covers, nerves of open covers, the nerve theorem, simplicial-vs-singular comparison,
  homotopy invariance of singular (co)homology, acyclic-cover theorems.  Classification of the
  absent items: MISSING (see `TASK07_AUDIT.md`, §1).
