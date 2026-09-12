# TASK 33 — audit: architecture firewall, negative controls, and corrected wording

> ### Task-34 correction notice (added by Task 34; the Task-33 text below is preserved verbatim)
>
> Task 33 is mathematically passed and its statements stand.  Two forward-looking remarks are
> now out of date:
>
> 1. Task 33 recorded that nothing about `TM`, solder forms or frames was introduced.  That is
>    correct for Task 33; Task 34 has since built the tangent/solder layer
>    (`Emergent/TangentTransition.lean`, `Spine/Solder/**`,
>    `Comparison/SolderTangentGate.lean`), so the *current* state of the project is described
>    in `TASK34_PROVENANCE.md`.
> 2. The architecture firewall now has one more layer: `Spine.Audit.ArchitectureDAG` check 9
>    additionally covers `Emergent.TangentTransition`, and a new check 10 covers the
>    `Spine.Solder` branch and its single comparison join.
>
> Every `Ȟ¹` statement in this document remains a **fixed-cover Čech `Ȟ¹`** statement about
> the **specific symmetric full-overlap emergent cover**; it is not `H¹(M;ℤ₂) = 0`.


## 1. Architecture DAG / firewall

The production direction is unchanged:

```
local Clifford/Spin core (Spine.E1)
  ↓
local 4D Lorentz model            Emergent.LocalModel
  ↓
base-gluing primitive             Emergent.BaseGluing
  ↓
topological reconstruction        Emergent.Reconstruction
  ↓                     ↘
symmetric sector          non-derivability      Emergent.Symmetric / NonDerivability
  ↓          ↘                    ↓
SmoothGate    SymmetricCanonical  LocalPieceData          (Task 33: two of these are new)
  ↓                ↘
SmoothStructure  →  SymmetricSmooth                        (Task 33, new)
  ↓
adapter                            Emergent.CoverAdapter
  ↓
comparison join (leaf)             Comparison.EmergentSpinGate
```

`RequestProject/Spine/Audit/ArchitectureDAG.lean` — check 9, extended by Task 33 — now runs
the base-free firewall over **ten** emergence modules, including the four Task-33 modules
`Emergent.SmoothStructure`, `Emergent.SymmetricCanonical`, `Emergent.SymmetricSmooth`,
`Emergent.LocalPieceData`.  For each of them the audit mechanically verifies that its import
closure contains **no** module of

```
Spine.E2, Spine.Cech, Spine.Geometry, Spine.Nerve, Spine.GoodCover,
Spine.Cohomology, Spine.AlgebraicTopology, Spine.SpinNative,
Spine.Comparison, Spine.Controls
```

so in particular the smooth-manifold layer cannot silently import the top-down
tangent/frame-geometry branch, the Spin-obstruction machinery or the nerve-comparison
machinery.  Positive controls (`auditReaches`) pin the intended edges
`SmoothGate → SmoothStructure`, `Symmetric → SymmetricCanonical`,
`{SmoothStructure, SymmetricCanonical} → SymmetricSmooth`,
`NonDerivability → LocalPieceData`, so no check can pass vacuously.  The audit compiles as
part of the default target; a violating import makes the build fail.

The smooth closure uses only Mathlib's manifold machinery (`ChartedSpace`,
`OpenPartialHomeomorph`, `ModelWithCorners`, `contDiffGroupoid`,
`isManifold_of_contDiffOn`, `ContMDiff`, `Diffeomorph`).  **No project-level top-down
manifold or tangent construction is imported** — Outcome F did not occur.

There is no umbrella import, no circular dependency, and no `TaskNN` production module.

## 2. Negative controls

| false upgrade to be blocked | control |
|---|---|
| `SmoothGluing` absent → `IsManifold` anyway | `EmergentBase.not_smoothGluing_nonSmoothGluing`: an explicit datum over the local model, satisfying every field of `BaseGluingData` (its `φ` are homeomorphisms), which is **not** `SmoothGluing`; and `nonSmoothGluing_topological_reconstruction`, showing the full Task-32 topological reconstruction still applies to it.  Every positive smooth statement carries `SmoothGluing` as an explicit hypothesis. |
| `Nonempty Homeomorph` called canonical without coherence | `symmetricCanonicalHomeomorph_refl/_symm/_trans` and `symmetric_emergent_base_canonical`; the Task-32 `symmetric_emergent_base_unique` docstring now says "existence" and points at these. |
| same local domains → same global base | `base_incidence_not_determined_by_local_piece_data`, and the stronger `no_reconstruction_from_local_piece_data`: **no** assignment from local-piece data to topological spaces can reproduce the emergent base up to homeomorphism. |
| pointwise trivial Spin transitions → base determined | `SpinNative.spin_data_do_not_determine_base` (unchanged theorem, corrected wording). |
| symmetric fixed-cover `Ȟ¹ = 0` → arbitrary/global `H¹ = 0` | no such theorem exists in the project; the docstrings of `symmetric_emergent_H1_trivial` and of the comparison module now state the restriction explicitly. |
| smooth emergent base → identified with `TM` / Lorentz frames | compile-time architectural control: the emergence layer, including the new smooth modules, may not reach `Spine.Geometry` (frame/Spin-structure geometry) — enforced by `ArchitectureDAG` check 9. |

## 3. Corrected Task-32 wording

| location | before | after |
|---|---|---|
| `Emergent/BaseGluing.lean` (title, prose, structure docstring) | "the minimal missing primitive" / "the minimal base-gluing primitive" | "an explicit sufficient base-gluing primitive", with an explicit paragraph on what is and is not proved |
| `Emergent/Reconstruction.lean` | "the minimal primitive isolated in …" | "the explicit base-gluing primitive isolated in …" |
| `Emergent/NonDerivability.lean` | "a minimal base-incidence primitive is unavoidable"; "two literally identical (trivial) Spin transition data" | "base-incidence information is irreducibly additional"; the Spin form is described as *the same pointwise trivial transition law on two different covers*, explicitly not one typed object |
| `Emergent/Symmetric.lean` (module docstring, `homeomorph`, `symmetric_emergent_base_unique`) | "canonically homeomorphic", "canonicity of the emergent base" | "homeomorphic by the chart of any index" / "existence of a comparison homeomorphism", with pointers to the Task-33 canonical statements |
| `Emergent/SmoothGate.lean` | "No `IsManifold` instance is produced … this task does not take" | records that Task 33 closes the gate in `Emergent/SmoothStructure.lean` |
| `Comparison/EmergentSpinGate.lean` | "minimal missing primitive"; "literally the same Spin transition data" | "explicit base-gluing primitive … irreducibly additional"; "both transition laws are pointwise trivial", plus an explicit scope paragraph for the fixed-cover `Ȟ¹` result |

No theorem statement was weakened by these edits; only documentation was changed, and each
change moves the prose down to exactly what the corresponding formal statement proves.

## 4. Axioms

`#print axioms` is executed at compile time on all Task-33 principal endpoints (end of
`Emergent/SymmetricSmooth.lean` and `Emergent/LocalPieceData.lean`).  All of them depend on a
subset of `propext`, `Classical.choice`, `Quot.sound`; none depends on `sorryAx`.

## 5. Scientific interpretation boundary (unchanged and enforced)

Task 33 certifies structure only:

```
local Clifford/Spin core → local 3+1 Lorentz model
→ irreducibly additional base-incidence/gluing information
→ quotient base → topological 4-manifold → smooth 4-manifold.
```

It does **not** establish that the internal Lorentz model is the tangent geometry of the
emergent base, hence says nothing about a Spin structure of `TM` and nothing about `w₁(TM)`
or `w₂(TM)`.  That is the next gate.
