# TASK 32 — Manifold-emergence gate: provenance report

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


Environment: Lean `v4.28.0`, Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
(toolchain, manifest and Mathlib revision untouched).  No `sorry`, no `admit`, no new
`axiom`, no `native_decide`, no `unsafe`, no `partial`, no `implemented_by`.

**Outcome: B, refined by C.**
The Spin/Lorentz fibre data provably do *not* determine base incidence (proved, not
asserted).  One minimal explicit base-gluing primitive is isolated; from it together with the
canonical local Clifford/Lorentz core a topological 4-manifold base is reconstructed, unique
up to canonical homeomorphism in the symmetric sector, and the Task-31 kernel/`Ȟ¹` Spin
ambiguity is *eliminated* there (one Spin gauge class).  The remaining open condition is the
packaging of smoothness (Outcome-C component): the exact missing hypothesis is isolated and
named.

> **Task-33 correction.**  "Unique up to canonical homeomorphism" above records only the
> *existence* of a homeomorphism; the distinguished coherent comparison and its upgrade to a
> diffeomorphism are Task 33.  "One minimal explicit base-gluing primitive" overstates the
> theorems: read *an explicit sufficient base-gluing primitive whose cross-piece incidence
> layer is irreducibly additional*.  The smooth gate was closed in Task 33
> (`SmoothGluing → IsManifold` for the actual reconstructed atlas).

---

## 1. Source/DAG audit (§4), answered from the code

**Q1 — which current primitive first mentions `X`?**
`CechSpinLift.CechCover X ι` in `RequestProject/Spine/E2/Cech/Cover.lean`: its field
`U : ι → Set X` is the first object in the Spin chain whose *type* mentions a base.  Below
it, `RequestProject/Spine/E2/Lift/*` and `RequestProject/Spine/E1/*` do not mention a base at
all.  (The independent E2 frame-family layer, `NullSectorTask26/27`, also carries a base `B`,
but it is not in the Spin-native chain.)

**Q2 — which primitive first requires `[TopologicalSpace X]`?**
The same one: `CechCover` needs the topology for its field `isOpen_U`.

**Q3 — which primitive first requires the cover `𝓤`?**
`CechSpinLift.VisibleCocycle G 𝓤` (same file), hence its Spin-side instantiation
`SpinNative.NativeSpinTransitionData L 𝓤`
(`RequestProject/Spine/SpinNative/TransitionData.lean`) and the field
`SpinNative.CanonicalSpinSeed.cover`
(`RequestProject/Spine/Comparison/CanonicalSpinSeed.lean`).

**Q4 — are overlap relations derived or supplied as fields?**
Derived: `CechCover.overlap₂/₃/₄` are *definitions* (`U i ∩ U j`, …).  They are derived from
the cover, and the cover is derived from the base: the incidence information is therefore a
consequence of a *pre-existing point set*, not an independent datum.  This is exactly why it
cannot be recovered from data living over the overlaps.

**Q5 — is there a base-independent incidence/nerve object below `CechCover`?**
No.  `CechZ2.Nerve U n` (`RequestProject/Spine/Cech/Cochain.lean`) is built *from* `U`, hence
from `X`.  Nothing in the project provided an abstract incidence complex before Task 32.

**Q6 — does the local Clifford/Lorentz construction already provide a canonical
4-dimensional local model independent of `M`?**
Yes.  `SpinCore.LorentzCarrier = ℝ × (Fin 3 → ℝ)` (`RequestProject/Spine/E1/Carrier.lean`)
with the intrinsic Lorentz form `SpinCore.NS`, the intrinsic group `SpinCore.GLor`
(`E1/LorentzGroup.lean`) and the double cover `SpinCore.spinCover` (`E1/SpinCover.lean`).
No base, chart, manifold or cover occurs in that closure.  Task 32 only *names* it:
`EmergentBase.LocalModel` (`Spine/Emergent/LocalModel.lean`).

**Q7 — is there a theorem connecting the local model to chart domains or tangent spaces
without assuming `M` first?**
No.  The only place where the local model meets tangent spaces is
`RequestProject/Spine/Geometry/TangentInstance.lean`, which *starts* from a given smooth
manifold `M` modelled on `LorentzCarrier` and instantiates `Bundle.TangentSpace`.  That is
the top-down control branch; it presupposes `M`.

---

## 2. The exact chain, arrow by arrow

| # | from → to | label | declaration |
|---|---|---|---|
| 1 | Clifford/Spin core → local model | **definition** (exposure of existing object) | `EmergentBase.LocalModel` |
| 2 | local model → 4-dimensional real model | **theorem** | `EmergentBase.finrank_localModel` (`= 4`) |
| 3 | Spin core → Lorentz representation on the local model | **theorem** (Task 4/E1, re-exported) | `EmergentBase.spin_acts_on_localModel` |
| 4 | local model + **base incidence** → tagged carrier `X₀ = ⨿ i, D i` | **minimal new primitive** | `EmergentBase.BaseGluingData`, `BaseGluingData.Total` |
| 5 | primitive laws → equivalence relation (no relation has to be *generated*) | **theorem** | `BaseGluingData.setoid`, `rel_refl/rel_symm/rel_trans` |
| 6 | relation → quotient with the quotient topology | **definition** | `BaseGluingData.Space`, `BaseGluingData.quotMk` |
| 7 | openness of incidence domains + continuity of identifications → quotient map is open | **theorem** | `BaseGluingData.isOpenMap_mk` |
| 8 | open quotient map → each piece is an open embedding | **theorem** | `BaseGluingData.isOpenEmbedding_chart`, `chartHomeomorph` |
| 9 | pieces → charted space over the local model | **theorem/definition** | `BaseGluingData.chartedSpace` |
| 10 | closed gluing graph (explicit condition) → Hausdorff | **theorem** | `BaseGluingData.ClosedGluingGraph`, `t2Space_of_closedGluingGraph` |
| 11 | countable index + second-countable model → second countable | **theorem** | `BaseGluingData.secondCountableTopology_space` |
| 12 | all of the above → emergent (topological) manifold | **theorem/definition** | `BaseGluingData.EmergentManifold`, `emergentManifold`, `emergentManifoldCertificate` |
| 13 | neutral (symmetric) sector → canonical quotient `≃ₜ D` | **theorem** | `EmergentBase.symmetricGluing`, `symmetricGluing.homeomorph` |
| 14 | neutral sector → connected, Hausdorff, second countable, 4-dimensional charted base | **theorem** | `EmergentBase.symmetric_emergent_manifold` |
| 15 | canonicity of the emergent base | **theorem** | `EmergentBase.symmetric_emergent_base_unique` (canonical homeomorphism, *not* literal equality) |
| 16 | emergent base → Čech cover interface | **definition** (explicit adapter) | `EmergentBase.emergentCover` |
| 17 | emergent base + Spin core → canonical Spin seed with **no external base** | **definition** | `SpinNative.emergentSeed` |
| 18 | symmetric emergent cover → full nerve → `Ȟ¹(𝓤;ℤ₂) = 0` | **theorem** | `CechZ2.cohomology_one_eq_zero_of_fullNerve`, `SpinNative.symmetric_emergent_H1_trivial` |
| 19 | `Ȟ¹ = 0` → Task-31 gate holds → one Spin gauge class | **theorem** | `SpinNative.kernelTwistsGaugeTrivial_symmetric_emergent`, `symmetric_emergent_spin_unique_up_to_gauge`, `emergent_seed_certificate` |
| 20 | emergent base → standard obstruction still trivial (control branch survives) | **theorem** (Task 30, re-applied) | `SpinNative.emergent_seed_certificate`, item 2 |
| 21 | smooth compatibility of the emergent atlas | **assumption (exact missing condition)** | `BaseGluingData.SmoothGluing`, `EmergentBase.smooth_chart_changes` |
| 22 | emergent `M` → `TM` → `P_SO(TM)` comparison with the projected Lorentz branch | **open** — requires a solder form | not claimed anywhere |

> **Task-34 update of rows 15, 21 and 22.**  Row 15: existence of a homeomorphism (Task 32) →
> distinguished coherent comparison and canonical diffeomorphism (Task 33).  Row 21:
> `SmoothGluing` is no longer only an isolated condition — Task 33 proved it *sufficient* for
> Mathlib's `IsManifold` on the actual atlas.  Row 22: Task 34 proves the coupling is **not**
> derivable from rows 1–21, isolates `SpinNative.TangentSolderData` as the missing datum, and
> with it derives the tangent Lorentz metric, the orientation and time orientation, the
> equality of the tangent frame cocycle with the projected native Lorentz cocycle, and a
> native Spin lift of that cocycle.  No `w₂(TM)` claim is added.

---

## 3. The first irreducible assumption not contained in the Clifford/Spin core

> **`EmergentBase.BaseGluingData`** — the local domains `D i`, the incidence domains
> `W i j ⊆ D i`, the base-point identification maps `φ i j` and their coherence laws.

That this is genuinely irreducible is a **theorem**, not a stipulation:

* `EmergentBase.base_not_determined_by_local_pieces` — two gluing data with *identical* local
  pieces (`(symmetricGluing Bool hD).D = (disjointGluing Bool hD).D`) but different incidence
  data have non-homeomorphic emergent bases (one is connected, the other is not);
* `SpinNative.spin_data_do_not_determine_base` — over the emergent covers of those two bases
  the *same* Spin transition datum (the trivial one, identically `1`) exists, so no function
  of the Spin data can recover the base.

Fibre gluing is therefore not base gluing, and Task 32 ends in Case 2 of §7 with exactly one
new primitive, exposed in full (domains, incidence, identifications, laws) and hidden behind
no "emergence" wrapper.

---

## 4. Status of the three uniqueness claims (§12)

* **A. base construction** — canonical: for identical primitive input the neutral sector
  produces one base up to canonical homeomorphism (`symmetric_emergent_base_unique`,
  `symmetricGluing.homeomorph`).  Literal equality of quotient presentations is deliberately
  not claimed: different index types give different carriers.
* **B. Spin structure modulo kernel gauge** — **closed** on the symmetric emergent base:
  `Ȟ¹(𝓤;ℤ₂)` of the emergent cover vanishes (proved, not assumed), hence exactly one gauge
  class (`symmetric_emergent_spin_unique_up_to_gauge`, `emergent_seed_certificate`).  Note
  this concerns the *emergent* cover of the neutral sector; on a general emergent base the
  Task-31 gate remains a hypothesis, exactly as before.
* **C. metric/connection/geometry** — not addressed, by construction: no connection,
  transport, holonomy, curvature, torsion or dynamics occurs in any module of this layer or
  in its import closure.

---

## 5. Comparison edge with the standard top-down branch (§13)

Classification: **requires solder form.**

What *is* proved: the emergent base is a `ChartedSpace` over the very model space
`SpinCore.LorentzCarrier` on which the standard branch's manifolds are modelled
(`Spine/Geometry/TangentInstance.lean`), and the Task-30 statement "the standard Spin-lift
obstruction of the projected data is trivial for every family of local lifts" holds verbatim
over the emergent base (`emergent_seed_certificate`, item 2).

What is *not* proved, and is not smuggled in: an identification of the local model with the
tangent spaces of the emergent base (a solder form), hence no comparison of `P_SO(TM)` with
the projected Lorentz branch.  The standard route remains an independent certification
branch; nothing in it was weakened, rewritten or made to depend on the emergence layer (see
the firewall checks in `Spine/Audit/ArchitectureDAG.lean`, §9).

> **Task-34 correction of §5.**  The solder form is no longer missing: it is isolated as the
> explicit datum `SpinNative.TangentSolderData` and proved *not* derivable from the Task-32/33
> data.  The comparison with the top-down branch is now performed, in one leaf module
> (`Comparison/SolderTangentGate.lean`), and the top-down branch is still a certification
> target only: firewall checks 9 and 10 fail to compile if the bottom-up branch reaches
> `Spine.Geometry`.

---

## 6. Remaining external inputs after Task 32

```
        Mathlib + Spine.E1 (Clifford / Spin / Lorentz core)      [internal]
                              |
                              v
                 EmergentBase.LocalModel  (4-dim, Lorentz)       [derived]
                              |
     +------------------------+------------------------+
     |                                                 |
     v                                                 v
 BaseGluingData  ......... STILL EXTERNAL ........  NativeSpinTransitionData
 (domains, incidence, identifications)              on the emergent cover     [external]
     |                                                 |
     v                                                 |
 Space B  (quotient, topology, charts)   [derived]     |
     |                                                 |
     +--> ClosedGluingGraph  ......... EXTERNAL condition (Hausdorff)
     +--> Countable ι, SecondCountable V  ... EXTERNAL conditions
     +--> SmoothGluing  ............... EXTERNAL condition (smooth atlas)
     |                                                 |
     v                                                 v
 emergentCover B  [derived]  ------------------>  SpinNative.emergentSeed  [derived]
                                                       |
                                +----------------------+---------------------+
                                |                                            |
                                v                                            v
              symmetric sector: Ȟ¹ = 0 → one Spin gauge class      standard control branch
                        [derived, no assumption]                    (unchanged, independent)
```

Still external after Task 32: the base-gluing primitive itself; the separation, countability
and smoothness conditions listed above; and the Spin gluing datum over the emergent cover.
Everything else on the diagram is derived.  `X`, `[TopologicalSpace X]` and `𝓤` are **no
longer** external inputs of the Spin seed: `SpinNative.emergentSeed` supplies them from the
construction.
