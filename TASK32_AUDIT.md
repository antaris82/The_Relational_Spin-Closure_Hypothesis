# TASK 32 — final audit

> ### Task-33/34 correction notice (added by Task 34; the Task-32 text below is preserved verbatim)
>
> This document is **historical provenance** for Task 32.  Four of its statements have since
> been corrected or superseded; the original wording is left untouched, and each correction
> is also annotated inline where it occurs.
>
> 1. **"minimal" / "the minimal missing primitive".**  What is proved about
>    `EmergentBase.BaseGluingData` is: *an explicit sufficient base-gluing primitive;
>    cross-piece incidence / identification information is irreducibly additional;
>    field-by-field or universal minimality of `BaseGluingData` is not proved.*
>    (Task 33; `Emergent/LocalPieceData.lean`.)
> 2. **"unique up to canonical homeomorphism" (symmetric sector).**  Task 32 proved the
>    *existence* of a homeomorphism.  Task 33 constructed a distinguished intrinsic-coordinate
>    comparison with identity / inverse / composition coherence and upgraded it to a canonical
>    diffeomorphism (`Emergent/SymmetricCanonical.lean`, `Emergent/SymmetricSmooth.lean`).
> 3. **The smooth gate.**  Task 32 did not close the smooth-manifold gate.  Task 33 proved
>    `SmoothGluing → IsManifold` for the actual reconstructed atlas
>    (`BaseGluingData.isManifold_of_smoothGluing`).
> 4. **"requires solder form" (row 22 / §5).**  Still correct as a statement about Task 32,
>    and now *resolved* by Task 34: the required datum is `SpinNative.TangentSolderData`, the
>    coupling is proved **not** derivable from the Task-32/33 data
>    (`SpinNative.tangent_spin_base_data_do_not_force_transition_identification`), and with the
>    solder datum the tangent Lorentz frame cocycle equals the projected native Lorentz
>    cocycle (`TangentSolderData.projected_eq_tangentFrameTransition`).  See
>    `TASK34_PROVENANCE.md`.
>
> Every `Ȟ¹` statement in this document is a **fixed-cover Čech `Ȟ¹`** statement about the
> **specific symmetric full-overlap emergent cover**.  It is not `H¹(M;ℤ₂) = 0`, and it is not
> a theorem for arbitrary emergent bases.


Environment (unchanged, as frozen): Lean `v4.28.0`, Mathlib
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.  `lean-toolchain`, `lake-manifest.json` and the
Mathlib revision were not modified.

## 1. Clean build

```
rm -rf .lake/build
lake build RequestProject
```

Result: **success**, no errors.  The default target `RequestProject` builds the whole Spine,
including the new modules

```
RequestProject/Spine/Emergent/LocalModel.lean
RequestProject/Spine/Emergent/BaseGluing.lean
RequestProject/Spine/Emergent/Reconstruction.lean
RequestProject/Spine/Emergent/Symmetric.lean
RequestProject/Spine/Emergent/NonDerivability.lean
RequestProject/Spine/Emergent/SmoothGate.lean
RequestProject/Spine/Emergent/CoverAdapter.lean
RequestProject/Spine/Cech/FullNerve.lean
RequestProject/Spine/Comparison/EmergentSpinGate.lean
```

and the updated `RequestProject/Spine/Audit/ArchitectureDAG.lean`, whose run-time checks print

```
Task-32 manifold-emergence firewall audited: 6 base-free modules + 1 adapter +
  1 comparison join; illegal edges: 0
SPINE ARCHITECTURE AUDIT: all checks passed
```

## 2. Proof-hygiene scan

`rg -n "sorry|admit\b|native_decide|axiom |implemented_by|partial def|unsafe "` over all new
and edited files returns **no match**.  No declaration of the project is an `axiom`; the only
`Classical.choice` uses are the standard ones inherited from Mathlib and from the pre-existing
E1/E2 layers (see §3).

## 3. `#print axioms` on the principal new endpoints

The `#print axioms` commands are part of `RequestProject/Spine/Comparison/EmergentSpinGate.lean`
and therefore re-run on every build.  Reported for every endpoint:

| endpoint | axioms |
|---|---|
| `EmergentBase.LocalModel` | `[propext, Classical.choice, Quot.sound]` |
| `EmergentBase.finrank_localModel` | `[propext, Classical.choice, Quot.sound]` |
| `EmergentBase.spin_acts_on_localModel` | `[propext, Classical.choice, Quot.sound]` |
| `EmergentBase.BaseGluingData` | `[propext, Quot.sound]` |
| `EmergentBase.BaseGluingData.atlas_coherence` | `[propext, Quot.sound]` |
| `EmergentBase.BaseGluingData.setoid` | `[propext, Quot.sound]` |
| `EmergentBase.BaseGluingData.isOpenMap_mk` | `[propext, Classical.choice, Quot.sound]` |
| `EmergentBase.BaseGluingData.chartedSpace` | `[propext, Classical.choice, Quot.sound]` |
| `EmergentBase.BaseGluingData.t2Space_of_closedGluingGraph` | `[propext, Classical.choice, Quot.sound]` |
| `EmergentBase.BaseGluingData.secondCountableTopology_space` | `[propext, Classical.choice, Quot.sound]` |
| `EmergentBase.BaseGluingData.emergentManifold` | `[propext, Classical.choice, Quot.sound]` |
| `EmergentBase.BaseGluingData.emergentManifoldCertificate` | `[propext, Classical.choice, Quot.sound]` |
| `EmergentBase.symmetric_emergent_manifold` | `[propext, Classical.choice, Quot.sound]` |
| `EmergentBase.symmetric_emergent_base_unique` | `[propext, Classical.choice, Quot.sound]` |
| `EmergentBase.base_not_determined_by_local_pieces` | `[propext, Classical.choice, Quot.sound]` |
| `EmergentBase.emergentCover` | `[propext, Classical.choice, Quot.sound]` |
| `CechZ2.cohomology_one_eq_zero_of_fullNerve` | `[propext, Classical.choice, Quot.sound]` |
| `SpinNative.emergentSeed` | `[propext, Classical.choice, Quot.sound]` |
| `SpinNative.symmetric_emergent_H1_trivial` | `[propext, Classical.choice, Quot.sound]` |
| `SpinNative.kernelTwistsGaugeTrivial_symmetric_emergent` | `[propext, Classical.choice, Quot.sound]` |
| `SpinNative.symmetric_emergent_spin_unique_up_to_gauge` | `[propext, Classical.choice, Quot.sound]` |
| `SpinNative.emergent_seed_certificate` | `[propext, Classical.choice, Quot.sound]` |
| `SpinNative.spin_data_do_not_determine_base` | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx`.  No project-local axiom.  Only the three standard Lean/Mathlib axioms occur.

## 4. Choice audit

Two constructions use choice, and neither is presented as canonical without justification:

* `BaseGluingData.chartOfPoint` / `chartedSpace` — the chart attached to a point is built
  from `Quotient.out`, a *function* of the point, so `chartAt` is a well-defined function and
  the `ChartedSpace` structure is deterministic given the primitive.  Canonicity of the base
  itself is not claimed through this construction: it is proved separately, up to canonical
  homeomorphism, in `symmetric_emergent_base_unique`.
* `BaseGluingData.isOpenMap_mk` — `Classical.choose` extracts, from openness in the subspace
  topology, an open set of the local model; the statement proved is independent of that
  choice (it is a plain `IsOpenMap` statement).

The canonical objects of the layer — `LocalModel`, `BaseGluingData`, `Space`, `quotMk`,
`chart`, `emergentCover`, `emergentSeed`, `symmetricGluing` — contain no choice in their
definitions.

## 5. What is claimed, and what is not

Claimed (theorem level):

1. the Clifford/Spin core supplies a canonical base-free 4-dimensional Lorentz local model;
2. base incidence is **not** derivable from it, nor from Spin/Lorentz fibre data, and this is
   proved by an explicit pair of counter-models;
3. one minimal explicit primitive (`BaseGluingData`) suffices: from it the emergent base,
   its topology, its open charts, its `ChartedSpace` structure over the local model, its
   Hausdorffness (under the closed-graph condition), its second countability (countable index,
   second-countable model) and its canonicity in the symmetric sector all follow;
4. over the symmetric emergent base the fixed-cover Čech `Ȟ¹(𝓤;ℤ₂)` **vanishes**, closing the
   Task-31 kernel-twist gate: exactly one Spin gauge class;
5. the standard control branch survives the change of base: the Task-30 obstruction statement
   holds verbatim over the emergent base.

Not claimed:

* no `IsManifold`/`SmoothManifoldWithCorners` instance — the exact missing condition is
  isolated as `BaseGluingData.SmoothGluing` (Outcome-C component);
* no solder form, hence no comparison of the emergent `TM`/`P_SO(TM)` with the projected
  Lorentz branch (classified **requires solder form** in `TASK32_PROVENANCE.md` §5);

> **Task-33/34 correction of the two items above.**  The first item was closed by Task 33:
> `BaseGluingData.isManifold_of_smoothGluing` proves `SmoothGluing → IsManifold` for the
> actual reconstructed atlas.  The second was closed by Task 34, in the only sense in which it
> can be closed: the solder form is an explicit additional datum
> (`SpinNative.TangentSolderData`), proved not derivable from the Task-32/33 data, and with it
> the internal Lorentz structure is identified fibrewise with `TM` with exact overlap
> compatibility.  The third and fourth items stand unchanged.
* no identification of the fixed-cover `Ȟ¹(𝓤;ℤ₂)` with `H¹(X;ℤ₂)` (unchanged from Task 31);
* no connection, parallel transport, holonomy, curvature, torsion, metric dynamics or RSCH
  closure anywhere in the layer or its import closure.

## 6. Outcome classification

**Outcome B**, with the Outcome-C smoothness caveat and with the Outcome-E possibility
*excluded* in the symmetric sector (the residual Spin ambiguity is proved to vanish there, it
does not survive).  Outcome F (architecture regression) is excluded mechanically: the
emergence layer imports neither the top-down manifold branch nor any obstruction machinery,
as enforced by `Spine/Audit/ArchitectureDAG.lean` §9.
