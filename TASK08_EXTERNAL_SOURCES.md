# TASK08_EXTERNAL_SOURCES.md — append-only external-source ledger, Task 8

Scope: Task 8 (native homotopy invariance of the singular mod-2 cohomology of Task 5; hardening
of the Task-7 comparison interfaces).

**Policy (unchanged).**  No external Lean project may become a dependency of `Spine/**`.  No
external implementation may be copied.  Any external formalization *inspected* must be recorded
permanently, with project, owner, repository, file, commit, access date, licence, concept
consulted, theorem decomposition consulted and implementation influence, and classified as one
of `BACKGROUND_ONLY`, `DESIGN_REFERENCE`, `THEOREM_DECOMPOSITION_REFERENCE`,
`MATHLIB_API_REFERENCE`, `NEGATIVE_CONTROL`, `NOT_USED`.

The earlier ledger `TASK05_EXTERNAL_SOURCES.md` is preserved verbatim and remains in force for
the entries it records.

---

## Task-8 entries

**None.**

No external Lean formalization of

* homotopy invariance of singular (co)homology,
* the singular prism operator,
* chain homotopies of singular complexes, or
* simplicial-to-singular comparison

was cloned, opened or inspected during Task 8.  The construction was derived from the standard
textbook prism argument (the decomposition of `Δⁿ × I` into the simplices
`[v₀ … v_i w_i … w_n]`, which is classical mathematics and not attributable to any Lean
project) and from the pinned Mathlib API alone.

Sources actually consulted, for completeness:

| source | classification | what was used |
| --- | --- | --- |
| pinned Mathlib at commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (a declared dependency of this project, not an external project) | `MATHLIB_API_REFERENCE` | `TopCat.toSSet`, `SimplexCategory.toTop`, `stdSimplex`, `ContinuousMap.Homotopy`, `ContinuousMap.HomotopyEquiv`, `SSet.toTop`, `Finset` summation API |
| this project's own Task-5/6/7 layers | — | reused unchanged; see `TASK08_AUDIT.md` §1 |

---

## Mechanical check

`RequestProject.Spine.Audit.Firewall` re-runs the external-import audit over the whole Spine,
including the six new Task-8 modules:

```
  external-project imports = 0
  Experiment1 direct/transitive imports = 0
  Experiment2 direct/transitive imports = 0
```

The Spine builds with all external repositories absent.
