# TASK 31 — Final audit

Environment (unchanged, as required):

```
Lean     4.28.0                    (lean-toolchain, untouched)
Mathlib  8f9d9cff6bd728b17a24e163c9402775d9e6a365   (lake-manifest.json, untouched)
```

---

## 1. Clean build

```
$ rm -rf .lake/build
$ lake build RequestProject
...
Build completed successfully (8300 jobs).
```

No `error:` line in the log.  The two audit modules that gate the architecture are part of
the default target and were rebuilt from scratch; their output is:

```
Spine modules audited: 176
SPINE FIREWALL AUDIT: all checks passed
Stage-1.3 production modules audited: 92 (of 255 production Spine modules); chronological TaskNN modules: 0
generic AlgebraicTopology modules audited: 34, domain-specific imports: 0
low-level Nerve modules audited: 24, high-level imports: 0
comparison layering audited: RelJ → GlobalHomology → GlobalCohomology
Spin branch firewall audited: 6 Spin-native modules, 4 comparison module(s); illegal edges: 0
Task-31 uniqueness layer audited: 4 modules, illegal edges: 0
SPINE ARCHITECTURE AUDIT: all checks passed
```

(A subsequent incremental rebuild after adding the `#print axioms` blocks of
`Comparison/LorentzSpinUniqueness.lean` and `Controls/SpinNative/KernelTwistControl.lean`
also completed successfully, 8105 jobs.)

## 2. Proof-restriction scan

`rg` over the new and modified files (`Spine/SpinNative/**`, `Spine/Comparison/**`,
`Spine/Controls/SpinNative/**`, `Spine/Cech/CoverNerve.lean`) for

```
sorry | admit | axiom | native_decide | unsafe | partial | @[implemented_by]
```

returns **no occurrence**.  Over the whole `Spine` tree the string `sorry` occurs only twice,
both inside doc comments that state that no `sorry` is used.  No `axiom` declaration was
added anywhere.

## 3. `#print axioms` on the principal endpoints

Emitted by the build itself; the blocks live at the end of
`Spine/Comparison/CanonicalSpinSeed.lean`, `Spine/Comparison/LorentzSpinUniqueness.lean` and
`Spine/Controls/SpinNative/KernelTwistControl.lean`.

Uniqueness layer and cohomological gate — all
`[propext, Classical.choice, Quot.sound]`:

```
SpinNative.KerCocycle
SpinNative.twist
SpinNative.project_twist
SpinNative.ratio
SpinNative.exists_kerCocycle_twist_eq
SpinNative.native_kernel_torsor
SpinNative.GaugeEquiv
SpinNative.gaugeEquiv_iff_twist_isGaugeTrivial
SpinNative.canonicalSpinStructure
SpinNative.subsingleton_native_output
SpinNative.NoNontrivialKernelTwist
SpinNative.KernelTwistsGaugeTrivial
SpinNative.data_eq_on_overlaps_of_noNontrivialKernelTwist
SpinNative.gaugeEquiv_of_kernelTwistsGaugeTrivial
SpinNative.subsingleton_gaugeClass
SpinNative.native_uniqueness_summary
SpinNative.d_kerCocycleCochain
SpinNative.kernelTwistsGaugeTrivial_of_cover_H1_trivial
SpinNative.spinStructure_unique_up_to_gauge_of_cover_H1_trivial
SpinNative.CanonicalSpinSeed.seed_certificate
```

Lorentz-frame instance — all `[propext, Classical.choice, Quot.sound]`:

```
LorentzFrames.KerCocycle₁.toNative
LorentzFrames.toNative_twist
LorentzFrames.SpinFrameStructure.toSpinStructureOver
LorentzFrames.spinFrameStructure_eq_on_overlaps_of_rigid
LorentzFrames.spinFrameStructure_gaugeEquiv_of_gate
LorentzFrames.spinFrameStructure_gaugeEquiv_of_cover_H1_trivial
```

Controls — all `[propext, Classical.choice, Quot.sound]`:

```
SpinNativeControl.sign_twist_ne_null
SpinNativeControl.project_sign_twist_eq
SpinNativeControl.not_noNontrivialKernelTwist
SpinNativeControl.two_distinct_native_spin_structures
SpinNativeControl.signTwist_isGaugeTrivial
SpinNativeControl.two_structures_gaugeEquiv
SpinNativeControl.spin_two_distinct_native_spin_structures
```

**No `sorryAx`.  No project-local axiom.  No `native_decide` axiom.**  The profile
`[propext, Classical.choice, Quot.sound]` is exactly the established baseline of the Spine
(cf. `TASK29_AUDIT.md`, `TASK30_AUDIT.md`).

Remark on `Classical.choice`: it enters through Mathlib's topology/`ContinuousOn` API and
through the frozen `InternalProjection` interface, not through the Task-31 constructions.
The canonical selection itself makes no choice: `canonicalSpinStructure P S` has `S` as its
underlying datum and `rfl` as its compatibility proof.

## 4. Endpoints, by Task-31 target

| target | endpoint | file |
|---|---|---|
| U1 canonical selection | `SpinNative.canonicalSpinStructure` | `Spine/SpinNative/Canonical.lean` |
| U2 native determinism | `SpinNative.canonicalSpinStructure_unique`, `SpinNative.subsingleton_native_output` | `Spine/SpinNative/Canonical.lean` |
| §6 residual freedom | `SpinNative.exists_kerCocycle_twist_eq`, `SpinNative.native_kernel_torsor` | `Spine/SpinNative/KernelTwist.lean` |
| §10 negative control | `SpinNative.project_twist`; `SpinNativeControl.two_distinct_native_spin_structures`, `…not_noNontrivialKernelTwist` | `Spine/SpinNative/KernelTwist.lean`, `Spine/Controls/SpinNative/KernelTwistControl.lean` |
| §7 symmetric null sector | `SpinNativeControl.nullGluing`, `…sign_twist_ne_null`, `…two_structures_gaugeEquiv` | `Spine/Controls/SpinNative/KernelTwistControl.lean` |
| U3 rigidity (strict) | `SpinNative.data_eq_on_overlaps_of_noNontrivialKernelTwist` | `Spine/SpinNative/Rigidity.lean` |
| U3 rigidity (gauge) | `SpinNative.gaugeEquiv_of_kernelTwistsGaugeTrivial` | `Spine/SpinNative/Rigidity.lean` |
| U4 subsingleton | `SpinNative.subsingleton_gaugeClass` | `Spine/SpinNative/Rigidity.lean` |
| §8 `H¹` gate | `SpinNative.kernelTwistsGaugeTrivial_of_cover_H1_trivial` | `Spine/Comparison/KernelTwistCohomology.lean` |
| §12 packaged output | `SpinNative.CanonicalSpinSeed`, `…seed_certificate` | `Spine/Comparison/CanonicalSpinSeed.lean` |

## 5. Outcome

**Outcome B, refined by Outcome C** (§17).

* The Bottom-up path produces **one distinguished Spin structure**, with no arbitrary choice
  at any point of the native branch — so Outcome D is excluded, and the answer to question
  (B) of §3 is *no residual choice inside the native construction*.
* Standard kernel twists nevertheless remain mathematically possible, and are exhibited: the
  answer to question (A) of §3 is *yes, the constructor is canonical even though alternative
  Spin structures exist*.
* The exact theorem `rigidity condition ⇒ uniqueness` is proved in two forms (strict and
  gauge), and the rigidity condition is packaged explicitly and shown non-vacuous *and*
  falsifiable.
* The rigidity condition is further reduced, theorem-level, to the vanishing of the
  project's own fixed-cover Čech `Ȟ¹(𝓤;ℤ₂)` on covers with preconnected double overlaps —
  this is the Outcome-C content.  The identification with a **global** `H¹(X;ℤ₂)` is **not**
  performed and **not** claimed; the missing steps are listed in `TASK31_PROVENANCE.md` §6.
* No architecture regression (Outcome E) occurred: the uniqueness layer imports nothing from
  the SO-first obstruction path, and the mechanical DAG audit passes.

The manifold was **not** constructed, and no connection, transport, holonomy, curvature,
torsion or dynamics was introduced.
