# Task 30 — Code hygiene

## 1. New modules (three) and their imports

```
RequestProject/Spine/SpinNative/TransitionData.lean
    import RequestProject.Spine.E2.Cech.Cover

RequestProject/Spine/SpinNative/Projection.lean
    import RequestProject.Spine.SpinNative.TransitionData

RequestProject/Spine/Comparison/SpinNativeVsSO.lean
    import RequestProject.Spine.SpinNative.Projection
    import RequestProject.Spine.E2.Cech.Obstruction
    import RequestProject.Spine.Geometry.SpinStructure
```

One further import edge was added, from the audit module:

```
RequestProject/Spine/Audit/ArchitectureDAG.lean
    + import RequestProject.Spine.Comparison.SpinNativeVsSO
```

so that the comparison layer is in the environment of the mechanical branch-firewall check.
The audit is not a production module (it is excluded from `dagProductionModules`), so this
does not violate the "no lower module may import the comparison layer" rule.

Total: **6 new import edges**, all mathematically forced.  No existing import line was
removed or redirected; no existing module was moved or renamed.

## 2. Rules of §11 of the task, checked

| rule | status |
|---|---|
| Spin-native definitions must not import high-level obstruction modules | **holds** — closure of `SpinNative.*` contains no `E2.Cech.Defect / Coboundary / Obstruction / Refinement / SpinInstance / Core`, no `Spine.Geometry`, `Spine.Cech`, `Spine.GoodCover`, `Spine.Cohomology`, `Spine.Nerve`, `Spine.Controls`; mechanically checked |
| projection may depend on the Spin/Lorentz projection infrastructure | **holds** — it uses `NullSectorTask28.InternalProjection` only (reached through `E2.Cech.Cover`) |
| the comparison module may import both branches | **holds** — and it is required to (positive controls in the audit) |
| no lower module may import the comparison layer | **holds** — mechanically checked over all production modules |
| no circular dependency | **holds** — the import graph is a DAG; the audit computes closures |
| no umbrella imports | **holds** — no `Spine.*.Core` aggregate is imported by the new modules |
| no chronological production module names | **holds** — module names are `SpinNative.TransitionData`, `SpinNative.Projection`, `Comparison.SpinNativeVsSO`; no `Task30.lean` was created (the pre-existing `E2/Global/Task30.lean` belongs to the older E2 numbering and was not touched) |

## 3. Mechanical branch firewall

`RequestProject/Spine/Audit/ArchitectureDAG.lean` gained check **7**:

* every module under `RequestProject.Spine.SpinNative` is required to reach none of the
  high-level obstruction/geometry/nerve/controls prefixes (negative check, each paired with
  `requireModule`, so it cannot pass vacuously);
* no production module outside the two new prefixes may reach
  `RequestProject.Spine.SpinNative.TransitionData` — the standard branch does not depend on
  the new one either;
* `RequestProject.Spine.Comparison.*` is a leaf of the production DAG;
* positive controls: the comparison module must reach both `SpinNative.TransitionData` and
  `SpinNative.Projection`, and both `E2.Cech.Obstruction` and `Geometry.SpinStructure`.

Reported output of a full build:

```
Stage-1.3 production modules audited: 92 (of 248 production Spine modules); chronological TaskNN modules: 0
generic AlgebraicTopology modules audited: 34, domain-specific imports: 0
low-level Nerve modules audited: 24, high-level imports: 0
comparison layering audited: RelJ → GlobalHomology → GlobalCohomology
Spin branch firewall audited: 2 Spin-native modules, 1 comparison module(s); illegal edges: 0
SPINE ARCHITECTURE AUDIT: all checks passed
SPINE FIREWALL AUDIT: all checks passed   (176 Spine modules, 0 experiment-tree imports)
```

## 4. Metrics (measured, `scripts/arch_metrics.py --prefix RequestProject.Spine`)

| metric | before Task 30 | after Task 30 |
|---|---|---|
| Spine modules | 261 | 264 |
| Spine Lean LOC | 51919 | 52388 |
| internal import edges | 442 | 448 |
| **maximum internal import depth** | **67** | **67 (unchanged)** |

Import-closure sizes of the new endpoints (project-local modules):

```
RequestProject.Spine.SpinNative.Projection        : 25
RequestProject.Spine.Comparison.SpinNativeVsSO    : 62
```

**Did Task 30 increase the maximum import depth?  No.**  The Spin-native branch sits two
modules above `E2.Cech.Cover`, which is far from the longest chain, and the comparison module
is a leaf; the longest chain in the Spine is unchanged.  The snapshot is in
`scripts/task30_metrics_post.txt`.

## 5. Duplication avoided

* `NativeSpinTransitionData` is an `abbrev` for the existing `CechSpinLift.VisibleCocycle`
  at the internal group — no second cocycle structure was introduced.
* The identity/inverse laws are re-exported (`SpinNative.native_transition_laws`), not
  reproved.
* The pointwise sign-forgetting statement `ρ(−u) = ρ(u)` already existed as
  `SpinCore.spinCover_negOneSpin_mul` (Stage 1.2); an attempt to declare it again failed with
  "has already been declared" and was replaced by a citation
  (`SpinCore.proj_ker_mul_eq_spinCover_negOneSpin_mul` merely records that the generic
  `SpinNative.proj_ker_mul` specializes to the inherited theorem).  See
  `TASK30_FAILBUILDS.md`.
* The kernel theory, the defect theory, the coboundary calculus and the obstruction quotient
  are consumed unchanged.

## 6. Prohibitions

No `sorry`, `admit`, new `axiom`, `native_decide`, `unsafe`, `partial` or `implemented_by`
anywhere in the new files (checked by search).  `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json` are unmodified.
