# Combined project provenance

This Lean 4 project vendors the Lean sources of **two independent mathematical
developments** into a single Lake library, so that both can be built and imported
simultaneously.

## Canonical experiment names

| Canonical name | Mathematical project | Combined module root |
| --- | --- | --- |
| Experiment 1 / E1 | **Intrinsic Branching from a Derived Lorentz Structure** | `RequestProject.Experiment1` |
| Experiment 2 / E2 | **Split Complex Lorentzian Dynamics** | `RequestProject.Experiment2` |

These are the *established* names of the two experiments and are now used
consistently throughout this repository.

## Source origins

### Experiment 1 — Intrinsic Branching from a Derived Lorentz Structure

* Public project identifier: `Split-Complex-Lorentzian_Kinematics`
* Branch: `Intrinsic-Branching-from-a-Derived-Lorentz-Structure`
* Lean development shipped as an archive inside that repository, containing a
  Lake project whose library is itself called `RequestProject`.
* Vendored here as `RequestProject/Experiment1/` — **152** Lean files.
* Contents include: reconstructed positive Euclidean `R³`, the spin factor, the
  derived Lorentz bilinear structure, the future unit shell, shell
  tangent/rest-space geometry, the Hodge branch, the Clifford branch, and the
  intrinsic Lorentz spin cover (`Task10`…`Task32`, `SpinFinal`, `Herm2`,
  `Minkowski4`, …).

### Experiment 2 — Split Complex Lorentzian Dynamics

* Public project identifier: `Split-Complex_Lorentz_Dynamics`
* Branch: `main`
* Lean development shipped as an archive inside that repository, containing a
  Lake project whose library is also called `RequestProject`.
* Vendored here as `RequestProject/Experiment2/` — **334** Lean files.
* Contents include: `NullSectorTask01`…`NullSectorTask32`, spatial
  reconstruction, `GvisModel`, `Lift`, local/internal transition systems, kernel
  defect, Tasks I–XXXII.

Because both upstream Lake libraries carry the name `RequestProject`, they could
not be added side by side as Lake dependencies (`require`); their sources were
therefore vendored under distinct module roots.

## Packaging/provenance correction (module-root inversion)

The **previous** combined archive of this project used the module roots
`RequestProject.Exp1` and `RequestProject.Exp2` with the labels **reversed**
relative to the established terminology:

| Previous (incorrect) root | Actually contained |
| --- | --- |
| `RequestProject.Exp1` | Split Complex Lorentzian Dynamics (= **Experiment 2**) |
| `RequestProject.Exp2` | Intrinsic Branching from a Derived Lorentz Structure (= **Experiment 1**) |

This has been corrected by the module-path normalization

```text
RequestProject.Exp2.X  →  RequestProject.Experiment1.X     (E1)
RequestProject.Exp1.X  →  RequestProject.Experiment2.X     (E2)
```

**This is a packaging/provenance correction, not a mathematical correction.**
No theorem statement, definition, proof, assumption, option setting or import of
an external library was changed. A mechanical audit (see
`NAMING_NORMALIZATION_AUDIT.md`) shows that after applying only the module-prefix
substitution above, the vendored source trees are byte-identical to their
previous state:

```text
E1 non-path source differences = 0
E2 non-path source differences = 0
```

The `Exp1` / `Exp2` roots no longer exist anywhere in the project; no aliases
were retained.

## Toolchain

Both bundles pin exactly the same toolchain (`leanprover/lean4:v4.28.0`) and the
same Mathlib revision as this project, so no dependency reconciliation was
required.

## No cross-experiment mathematics

**No mathematical E1/E2 bridge has been introduced.** The only file that mentions
both experiments is `RequestProject/CombinedDemo.lean`, which is a pure smoke
test: it imports one representative module from each experiment and re-states
one already-proved result from each. It contains no cross-experiment definition,
no identification of E1 objects with E2 objects (in particular `StabK` is *not*
identified with `GvisModel`, and E1 spin is *not* compared with E2 `Lift`), and
no new mathematical lemma.

The first actual cross-experiment mathematical bridge is deliberately deferred to
a subsequent task.

## Formal policy status

The vendored sources contain no `sorry`, no `admit`, no `axiom` declarations, no
`@[implemented_by]`, no `native_decide` and no `bv_decide`. No new `unsafe` or
`partial` declarations were introduced by this maintenance task (the pre-existing
`partial def` occurrences are upstream metaprogramming helpers in the
experiments' own dependency-audit files, left untouched). The `#print axioms`
output emitted by the developments themselves reports only `propext`,
`Classical.choice`, `Quot.sound`.

## Task 34 — the tangent/solder layer (2026-09-12)

No cross-experiment mathematics was introduced: the new modules sit in
`RequestProject.Spine` and their import closures contain only `Mathlib` and `Spine` modules
(mechanically checked by `RequestProject.Spine.Audit.Firewall` and
`RequestProject.Spine.Audit.ArchitectureDAG`).

The layer answers the question "is the internal Lorentz structure of the Clifford/Spin core
coupled to the tangent geometry of the emergent smooth 4-manifold?" with: **not derivably**,
and it isolates the explicit datum (`SpinNative.TangentSolderData`) that does couple them,
deriving from it the tangent Lorentz metric, the orientation and time orientation, genuine
tangent Lorentz frame data, the equality of its transition cocycle with the projected native
Lorentz cocycle, and a native Spin lift of that cocycle.  Nothing about `w₁`, `w₂`,
connections, curvature or dynamics is claimed.

The historical top-down tangent/frame branch (`Spine/Geometry/**`) remains a *certification
target*: the new firewall check 10 fails to compile if any module of the bottom-up branch
reaches it.  The only module that sees both branches is
`Spine/Comparison/SolderTangentGate.lean`.
