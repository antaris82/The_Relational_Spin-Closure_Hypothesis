# TASK 31 — Code hygiene

All checks below are either mechanically enforced by
`RequestProject/Spine/Audit/ArchitectureDAG.lean` (which **fails to compile** if violated) or
verifiable from the import headers of the eight new modules.

---

## 1. Required checks

| check | verdict | how it is enforced |
|---|---|---|
| no duplicate cocycle theory | **pass** | `SpinNative.KerCocycle` and the pre-existing `LorentzFrames.KerCocycle₁` are identified by the mutually inverse `KerCocycle₁.toNative` / `KerCocycle₁.ofNative`, both `rfl`, and the twists agree (`LorentzFrames.toNative_twist`, `rfl`). The generic theorems are proved once; the Lorentz-frame results are instances. The missing degree-0 nerve API was added to the existing `Cech/CoverNerve.lean`, not duplicated. |
| no downward import from high-level obstruction or Nerve machinery | **pass** | ArchitectureDAG §7 and §8: each of the four uniqueness modules is checked against `E2.Cech.LocalLifts`, `E2.Cech.Defect`, `E2.Cech.Coboundary`, `E2.Cech.Obstruction`, `E2.Cech.Refinement`, `E2.Cech.SpinInstance`, `E2.Cech.Core`, `Spine.Geometry`, `Spine.Cech`, `Spine.GoodCover`, `Spine.Cohomology`, `Spine.Nerve`, `Spine.AlgebraicTopology`, `Spine.Controls`, `Spine.Comparison`. |
| native Spin branch independent of the SO-first lift construction | **pass** | `E2.Cech.LocalLifts` — the module that defines `SpinLiftFamily`, i.e. the SO-first lift — was added to the forbidden list for this task and is unreachable from `Spine.SpinNative.**`. |
| comparison layer is the only place seeing both directions | **pass** | The obstruction (`Comparison.CanonicalSpinSeed`), the Čech/ℤ₂ cohomology (`Comparison.KernelTwistCohomology`) and the Lorentz-frame Spin structures (`Comparison.LorentzSpinUniqueness`) are seen only from `Spine.Comparison.**`; ArchitectureDAG checks that no production module imports a comparison module, and that each comparison module really reaches both of the branches it claims to join (positive controls, so the check cannot pass vacuously). |
| uniqueness layer depends only on minimal Spin-native / twist machinery | **pass** | Import headers: `KernelTwist ← Projection`, `GaugeEquivalence ← KernelTwist`, `Canonical ← GaugeEquivalence`, `Rigidity ← Canonical`. The whole layer sits over `E2.Cech.Cover` + `E2.Lift.*` (kernel predicate) + `E2.CentralDoubleCover`. |
| no circular imports | **pass** | The import graph is a DAG (Lean rejects cycles at build time); the four uniqueness modules form a linear chain, and the comparison modules are sinks. |
| no umbrella imports | **pass** | No new module imports `Mathlib` wholesale or a `*.Core` aggregator; every import names a specific module. (`Mathlib` itself is reached only through the frozen `E2.CentralDoubleCover`, unchanged.) |
| no chronological production filenames | **pass** | New modules: `SpinNative/KernelTwist.lean`, `SpinNative/GaugeEquivalence.lean`, `SpinNative/Canonical.lean`, `SpinNative/Rigidity.lean`, `Comparison/KernelTwistCohomology.lean`, `Comparison/LorentzSpinUniqueness.lean`, `Comparison/CanonicalSpinSeed.lean`, `Controls/SpinNative/KernelTwistControl.lean`. No `Task31.lean`. |

---

## 2. New firewalls added to `Spine/Audit/ArchitectureDAG.lean`

Check **8 — the uniqueness-layer firewall**:

* `requireModule` for each of the four uniqueness modules (so no check is vacuous);
* negative: none of them reaches the SO-first lift construction, the obstruction machinery,
  the Čech/ℤ₂ cohomology, the good-cover layer, the Nerve machinery, the generic algebraic
  topology or the frame geometry;
* positive controls: `KernelTwist` reaches `TransitionData` and `Projection`;
  `GaugeEquivalence` reaches `KernelTwist`; `Canonical` reaches `GaugeEquivalence`;
  `Rigidity` reaches `Canonical` — the layer is a genuine stack, not four unrelated files;
* positive controls for the comparison modules: `Comparison.KernelTwistCohomology` reaches
  both `SpinNative.Rigidity` and `Cech.Cohomology`; `Comparison.CanonicalSpinSeed` reaches
  both `SpinNative.Rigidity` and `E2.Cech.Obstruction`; `Comparison.LorentzSpinUniqueness`
  reaches both `SpinNative.Rigidity` and `Geometry.SpinStructure`.

`E2.Cech.LocalLifts` was added to the Spin-native forbidden list of check 7 as well, so the
Task-30 firewall is now strictly stronger than before.

Audit output of the build:

```
Stage-1.3 production modules audited: 92 (of 255 production Spine modules); chronological TaskNN modules: 0
generic AlgebraicTopology modules audited: 34, domain-specific imports: 0
low-level Nerve modules audited: 24, high-level imports: 0
comparison layering audited: RelJ → GlobalHomology → GlobalCohomology
Spin branch firewall audited: 6 Spin-native modules, 4 comparison module(s); illegal edges: 0
Task-31 uniqueness layer audited: 4 modules, illegal edges: 0
SPINE ARCHITECTURE AUDIT: all checks passed
SPINE FIREWALL AUDIT: all checks passed        (176 Spine modules, zero legacy edges)
```

---

## 3. Metrics

**New modules: 8** (4 production Spin-native, 3 comparison, 1 control).
**Modified modules: 2** (`Cech/CoverNerve.lean` — degree-0 nerve API; `Audit/ArchitectureDAG.lean`
— new firewall).

LOC delta (git, `RequestProject/**`, Task-31 commits): **+1480**, of which

| file | LOC |
|---|---|
| `Spine/SpinNative/KernelTwist.lean` | 277 |
| `Spine/SpinNative/GaugeEquivalence.lean` | 141 |
| `Spine/SpinNative/Canonical.lean` | 137 |
| `Spine/SpinNative/Rigidity.lean` | 172 |
| `Spine/Comparison/KernelTwistCohomology.lean` | 175 |
| `Spine/Comparison/LorentzSpinUniqueness.lean` | 143 |
| `Spine/Comparison/CanonicalSpinSeed.lean` | 155 |
| `Spine/Controls/SpinNative/KernelTwistControl.lean` | 190 |
| `Spine/Cech/CoverNerve.lean` (added) | +28 |
| `Spine/Audit/ArchitectureDAG.lean` (added) | +62 |

Internal dependency edges added (project-internal imports of the new modules):

```
SpinNative.KernelTwist            → SpinNative.Projection
SpinNative.GaugeEquivalence       → SpinNative.KernelTwist
SpinNative.Canonical              → SpinNative.GaugeEquivalence
SpinNative.Rigidity               → SpinNative.Canonical
Comparison.KernelTwistCohomology  → SpinNative.Rigidity, Cech.SpinCocycle
Comparison.LorentzSpinUniqueness  → Comparison.SpinNativeVsSO,
                                    Comparison.KernelTwistCohomology, Cech.SpinKernelSign
Comparison.CanonicalSpinSeed      → Comparison.SpinNativeVsSO,
                                    Comparison.KernelTwistCohomology
Controls.SpinNative.KernelTwistControl → SpinNative.Rigidity, E2.SpinProjection
Audit.ArchitectureDAG             → the three comparison modules and the control (audit only)
```

That is **13** new production/control edges plus 4 audit edges; no edge points from the
standard branch into `SpinNative`, and none from a production module into `Comparison`.

Maximum import depth (longest chain of project modules, Mathlib counted as depth 0) and
closure size (number of distinct project modules transitively imported):

| module | closure | depth |
|---|---|---|
| `SpinNative.TransitionData` | 24 | 22 |
| `SpinNative.Projection` | 25 | 23 |
| `SpinNative.KernelTwist` | 26 | 24 |
| `SpinNative.GaugeEquivalence` | 27 | 25 |
| `SpinNative.Canonical` | 28 | 26 |
| `SpinNative.Rigidity` | 29 | 27 |
| `Controls.SpinNative.KernelTwistControl` | 57 | 28 |
| `Comparison.SpinNativeVsSO` (Task 30) | 62 | 29 |
| `Comparison.KernelTwistCohomology` | 71 | 30 |
| `Comparison.CanonicalSpinSeed` | 76 | 31 |
| `Comparison.LorentzSpinUniqueness` | 78 | 31 |

**Closure size of the final Task-31 endpoint.**  The endpoint
`SpinNative.CanonicalSpinSeed.seed_certificate` lives in `Comparison.CanonicalSpinSeed`:
**76** project modules, maximum import depth **31**.  The purely uniqueness-theoretic
endpoint `SpinNative.native_uniqueness_summary` has a closure of **29** project modules
(depth 27) and reaches no obstruction, cohomology, Nerve or geometry module at all.

---

## 4. Interpretation hygiene

* `SpinNativeControl.nullGluing` is documented as a **gluing** null state only; the words
  "flat", "vacuum", "curvature", "holonomy" appear in the new modules exclusively in negative
  form (statements of what is *not* claimed).
* The two rigidity conditions are named after what they assume
  (`NoNontrivialKernelTwist`, `KernelTwistsGaugeTrivial`), never after their conclusion.
* The cohomological gate names the object it actually uses (`CechZ2.H1 𝓤.U`, the nerve of the
  fixed cover) and never `H¹(X;ℤ₂)`.
