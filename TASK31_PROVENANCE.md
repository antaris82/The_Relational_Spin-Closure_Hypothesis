# TASK 31 — Provenance of the canonical Spin-structure gate

Frozen environment: Lean `4.28.0`, Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
(`lean-toolchain` and `lake-manifest.json` untouched).

---

## 0. Answer to the Task-31 question

> Given the coherent direct Spin-native input, is there exactly one Spin structure selected by
> provenance, and under what minimal condition is it also unique among all compatible Spin
> structures?

**Selection: yes, and it is choice-free.**  Coherent Spin-native gluing data `S` determine
one distinguished Spin structure `SpinNative.canonicalSpinStructure P S` over their own
projection `ρ ∘ S`; the underlying gluing datum *is* `S` and the compatibility with the
projected visible datum is `rfl`.  No local `SO → Spin` lift, no local section of `ρ` and no
`Classical.choice` enters the constructor.

**Uniqueness: no, not by provenance alone.**  Over the same projected data the Spin-native
data form a torsor under the group of continuous kernel-valued Čech 1-cocycles of the cover
(`SpinNative.exists_kerCocycle_twist_eq` + `SpinNative.project_twist`), and this freedom is
*not* empty: on a two-patch cover of a nonempty base with a nontrivial kernel element there
really are two distinct Spin structures over the same projection
(`SpinNativeControl.two_distinct_native_spin_structures`; intrinsic Spin instance
`SpinNativeControl.spin_two_distinct_native_spin_structures`).

**Minimal condition.**  Two conditions were isolated and both are stated so that they expose
exactly what is assumed:

| condition | statement | consequence |
|---|---|---|
| `SpinNative.NoNontrivialKernelTwist P 𝓤` | every kernel 1-cocycle of `𝓤` is pointwise `1` | competitors agree with the native datum **on every double overlap** |
| `SpinNative.KernelTwistsGaugeTrivial P 𝓤` | every kernel 1-cocycle of `𝓤` is a coboundary `λ_i λ_j⁻¹` | competitors are **gauge equivalent** to the native one; the gauge quotient is a `Subsingleton` |

The second is the mathematically correct one: it is the vanishing of the **fixed-cover**
kernel-twist quotient `Z¹(𝓤; ker ρ)/B¹(𝓤; ker ρ)`, and it is implied by the vanishing of the
project's own nerve-level Čech cohomology `Ȟ¹(𝓤;ℤ₂)` on a cover with preconnected double
overlaps (`SpinNative.kernelTwistsGaugeTrivial_of_cover_H1_trivial`).

**Outcome classification (§17): Outcome B, refined by Outcome C.**  Canonical selection
exists and is proved; genuine uniqueness needs the explicit rigidity condition, which has
been reduced, theorem-level, to a fixed-cover `Ȟ¹(𝓤;ℤ₂)`-type vanishing.  The remaining step
to a *global* `H¹(X;ℤ₂)` is **not** taken and **not** claimed (§6 below).

The five notions Task 31 demands be kept apart:

| notion | formal object | status |
|---|---|---|
| canonical selection | `SpinNative.canonicalSpinStructure` | **definition**, choice-free |
| native determinism | `SpinNative.subsingleton_native_output`, `canonicalSpinStructure_unique` | **theorem** |
| gauge equivalence | `SpinNative.GaugeEquiv` (+ `gaugeEquiv_equivalence`) | **definition / equivalence relation** |
| genuine uniqueness | `SpinNative.data_eq_on_overlaps_of_noNontrivialKernelTwist`, `gaugeEquiv_of_kernelTwistsGaugeTrivial`, `subsingleton_gaugeClass` | **theorem under an explicit assumption** |
| remaining `H¹`-type freedom | `SpinNative.KernelTwistsGaugeTrivial`, `kernelTwistsGaugeTrivial_of_cover_H1_trivial` | **assumption / fixed-cover gate; global `H¹` still open** |

---

## 1. First action — audit of the existing torsor / twist machinery (§4)

Result of the audit, before any new code was written.

1. **What measures the difference of two Spin structures with the same `SO` projection?**
   `LorentzFrames.SpinFrameStructure.ratio` (Task 4, WP8, in
   `RequestProject/Spine/Geometry/SpinStructure.lean`) produces a
   `LorentzFrames.KerCocycle₁ Φ`: a continuous `{±1}`-valued Čech 1-cocycle on the *fixed*
   frame cover.  Nothing else in the project measured that difference.
2. **In which form?**  A **raw cocycle on a fixed cover** — a structure with a
   kernel-valuedness field and an exact 1-cocycle field.  No quotient, no gauge class, no
   equivalence relation on Spin structures existed.
3. **Fixed-cover torsor or genuine `H¹` classification?**  Fixed-cover torsor only:
   `LorentzFrames.SpinFrameStructure.spinStructure_torsor` states `twist_ratio` /
   `ratio_twist` pointwise.  There was no `H¹(M;ℤ₂)` classification of Spin structures, and
   there still is none (see §6).
4. **Which equivalence relation on Spin structures was available?**  None.  Only literal
   equality of the transition maps.  This is why Task 31 had to introduce `GaugeEquiv`
   explicitly rather than "identify" structures silently.
5. **Does the native constructor already select a representative without a lift choice?**
   Yes — but before Task 31 that fact was not stated: `SpinNative.nativeLiftFamily` (Task 30)
   exhibits Spin-native data as lifts of their own projection with `rfl`, and Task 31 turns
   this into the named canonical object.

Consequences for the implementation, all honoured:

* the generic `SpinNative.KerCocycle` is the *same* structure as `LorentzFrames.KerCocycle₁`;
  the two are related by the mutually inverse `KerCocycle₁.toNative` / `KerCocycle₁.ofNative`
  and the twists agree (`LorentzFrames.toNative_twist`, all three by `rfl`).  No cocycle
  theory is duplicated: the generic statements are proved once and the Lorentz-frame results
  are instances;
* the degree-2 machinery (`CechSpinLift.IsKerCochain₁`, `delta₁`, `Cohomologous`,
  `ObstructionClass`) is **not** imported into the uniqueness layer — it belongs to the
  SO-first branch;
* the missing degree-0 nerve API (`CechSpinZ2.nerve₀`, `face_nerve₁_zero`, `face_nerve₁_one`,
  `inter_single`) was added to the existing `RequestProject/Spine/Cech/CoverNerve.lean`
  rather than duplicated in a new module.

---

## 2. The code-derived dependency chain

Each arrow is marked with its kind.  All names are the real Lean names.

```
primitive native Spin data
    SpinNative.NativeSpinTransitionData L 𝓤                       [definition, Task 30]
        │  (= CechSpinLift.VisibleCocycle at the internal group; nothing new)
        ↓  definition
native coherent gluing
    fields  continuousOn_g,  cocycle  (exact Čech 1-cocycle law)   [definition]
        │
        ├── definition ────────────────────────────────────────────┐
        ↓                                                          ↓
projection through ρ                                     distinguished Spin structure
    SpinNative.project P S                [definition]       SpinNative.SpinStructureOver
    SpinNative.project_g                  [theorem, rfl]      SpinNative.canonicalSpinStructure
    SpinNative.project_eq_of_ker_factor   [theorem]                   [definition, U1]
        │                                                     canonicalSpinStructure_data  [rfl]
        ↓ theorem (Task 30)                                    canonicalSpinStructure_unique
    SpinNative.projected_obstruction_trivial_of_lifts                 [theorem, U2]
    (the *existing* standard obstruction is trivial)          subsingleton_native_output
                                                                      [theorem, U2]
        ↓
residual kernel-twist freedom
    SpinNative.KerCocycle P 𝓤                                  [definition]
    SpinNative.twist S ε                                       [definition]
    SpinNative.project_twist                                   [theorem — negative control]
    SpinNative.ratio P hproj                                   [definition]
    SpinNative.twist_ratio / ratio_twist                       [theorem]
    SpinNative.exists_kerCocycle_twist_eq                      [theorem — every competitor]
    SpinNative.native_kernel_torsor                            [theorem — packaged torsor]
        ↓
equivalence layer
    SpinNative.KerCochain₀, KerCochain₀.delta                  [definition]
    SpinNative.KerCocycle.IsGaugeTrivial                       [definition]
    SpinNative.GaugeEquiv                                      [definition — equivalence]
    SpinNative.gaugeEquiv_equivalence                          [theorem]
    SpinNative.gaugeEquiv_iff_twist_isGaugeTrivial             [theorem — uses centrality]
    SpinNative.project_eq_of_gaugeEquiv                        [theorem]
        ↓
exact rigidity condition
    SpinNative.NoNontrivialKernelTwist                         [assumption, named]
    SpinNative.KernelTwistsGaugeTrivial                        [assumption, named — H¹-type]
    KernelTwistsGaugeTrivial.of_noNontrivialKernelTwist        [theorem]
    noNontrivialKernelTwist_of_subsingleton_index              [theorem — non-vacuity]
    noNontrivialKernelTwist_of_trivial_kernel                  [theorem — non-vacuity]
    SpinNativeControl.not_noNontrivialKernelTwist              [theorem — it can fail]
        ↓
strongest certified uniqueness
    SpinNative.data_eq_on_overlaps_of_noNontrivialKernelTwist  [theorem, U3 strict]
    SpinNative.gaugeEquiv_of_kernelTwistsGaugeTrivial          [theorem, U3 gauge]
    SpinNative.GaugeClass                                      [quotient]
    SpinNative.subsingleton_gaugeClass                         [theorem, U4]
    SpinNative.native_uniqueness_summary                       [theorem — packaged]
        ↓
cohomological gate (comparison layer)
    SpinNative.kerCocycleCochain                               [definition]
    SpinNative.d_kerCocycleCochain                             [theorem — δa = 0]
    SpinNative.kernelTwistsGaugeTrivial_of_cover_H1_trivial    [theorem — Ȟ¹(𝓤;ℤ₂) gate]
    SpinNative.spinStructure_unique_up_to_gauge_of_cover_H1_trivial [theorem]
    identification with global H¹(X;ℤ₂)                        [STILL OPEN — see §6]
        ↓
packaged handoff
    SpinNative.CanonicalSpinSeed                               [definition]
    CanonicalSpinSeed.projected / canonical                    [definition]
    CanonicalSpinSeed.obstruction_trivial                      [theorem, Task 30]
    CanonicalSpinSeed.residual_freedom                         [theorem]
    CanonicalSpinSeed.unique_up_to_gauge_of_gate               [theorem]
    CanonicalSpinSeed.unique_up_to_gauge_of_cover_H1_trivial   [theorem]
    CanonicalSpinSeed.seed_certificate                         [theorem — packaged]
```

Lorentz-frame instance (comparison layer,
`RequestProject/Spine/Comparison/LorentzSpinUniqueness.lean`):

```
LorentzFrames.KerCocycle₁.toNative / ofNative        [definition, mutually inverse, rfl]
LorentzFrames.toNative_twist                         [theorem, rfl]
LorentzFrames.SpinFrameStructure.toSpinStructureOver [definition]
LorentzFrames.spinFrameStructure_eq_on_overlaps_of_rigid          [theorem, U3 strict]
LorentzFrames.spinFrameStructure_gaugeEquiv_of_gate               [theorem, U3 gauge]
LorentzFrames.spinFrameStructure_gaugeEquiv_of_cover_H1_trivial   [theorem, Ȟ¹ gate]
```

---

## 3. The symmetric (null) gluing sector — §7, tested, not assumed

The maximally symmetric Spin-native gluing state is
`SpinNativeControl.nullGluing L 𝓤` : `g̃_ij ≡ 1`.  It is a **gluing** null state; it is not
called flat spacetime, and no connection, transport, holonomy or curvature exists anywhere in
this layer.

Result, on the two-patch cover `SpinNativeControl.twoPatchCover X` of a nonempty base, for
any kernel element `z ≠ 1` with `z * z = 1`:

* `SpinNativeControl.signTwist` is a genuine kernel 1-cocycle (`ε_ij = z` off the diagonal);
* `SpinNativeControl.sign_twist_ne_null` — the twisted state differs from the null state;
* `SpinNativeControl.project_sign_twist_eq` — the projection is unchanged;
* `SpinNativeControl.two_distinct_native_spin_structures` — hence two distinct Spin
  structures over the same projected data;
* `SpinNativeControl.not_noNontrivialKernelTwist` — strict rigidity fails on this cover.

**So the symmetric native gluing does *not* by itself eliminate the residual kernel
ambiguity.**  This is a Task-31 result, not a failure.

The same control also delimits it honestly: `SpinNativeControl.signTwist_isGaugeTrivial`
shows this particular cocycle *is* a coboundary, so the two structures are gauge equivalent
(`SpinNativeControl.two_structures_gaugeEquiv`).  On a two-patch cover the residual freedom is
therefore pure gauge.  **No gauge-nontrivial kernel twist is exhibited anywhere in the
project**; producing one requires a cover whose nerve has nonzero `Ȟ¹`, which this control
does not construct.  Consequently the project currently proves neither that the fixed-cover
kernel-twist quotient is always trivial nor that it can be nontrivial.

---

## 4. What is *not* claimed

* No manifold is constructed, and none is derivable from the Task-31 layer.
* No connection, transport, holonomy, curvature, torsion or dynamics occurs; the uniqueness
  layer's import closure contains no such object.
* `GaugeEquiv` is a cocycle-level equivalence.  It is **not** proved here to be an
  isomorphism of principal bundles: the project has no total-space presentation of the glued
  object (this is the standing Task-4 boundary, see `TASK04_AUDIT.md`).
* Literal record equality of two Spin structures over the same projection is **not** claimed
  and would be false as stated, since the gluing maps are unconstrained off the overlaps.
  All strict statements are "on every double overlap".
* No identification of any class with `w₂(TM)` is made.

---

## 5. Remaining external inputs — the handoff list for the manifold task

These are exactly the inputs that the next stage must remove.  All of them are visible in the
type of `SpinNative.CanonicalSpinSeed L G X ι`:

| input | where it enters | remark |
|---|---|---|
| the base set `X` | parameter of `CanonicalSpinSeed`, of `CechCover X ι` | **given, not derived** |
| the topology `[TopologicalSpace X]` | instance parameter | **given**; used for `ContinuousOn` of every gluing datum |
| the index type `ι` | parameter | **given**; arbitrary type, no finiteness or ordering |
| the Čech cover `𝓤 : CechCover X ι` | field `cover` | **given**: patches `U i`, openness, covering property |
| the overlap structure `overlap₂`, `overlap₃` | derived from `𝓤` | `𝓤.U i ∩ 𝓤.U j`, `… ∩ 𝓤.U k` |
| the group `L` and its topology, `IsTopologicalGroup L` | parameters | Spin-side algebra, frozen |
| the visible group `G` and its topology | parameters | target of `ρ` |
| the projection `P : InternalProjection L G` | field `proj` | frozen interface: continuity, surjectivity, local sections, central and discrete kernel |
| (gate only) preconnectedness of the double overlaps | hypothesis of the cohomological gate | automatic on a good cover (`GoodCoverZ2.isPreconnected_overlap₂`) |
| (gate only) a kernel dictionary `KernelSign P` | hypothesis | frozen `CechSpinZ2.spinKernelSign` for the intrinsic Spin cover |

Nothing else is used.  In particular no smooth structure, no metric, no tangent bundle and no
frame bundle occur in the generic layer; the Lorentz-frame data `LorentzFrameData M Fib ι`
appear only in the comparison instance
`RequestProject/Spine/Comparison/LorentzSpinUniqueness.lean`.

---

## 6. The gap to a global `H¹(X;ℤ₂)` — stated, not smuggled

What is proved: on a cover with preconnected double overlaps, and with respect to a kernel
dictionary `ker ρ ≅ ℤ₂`,

```
    (∀ h : CechZ2.H1 𝓤.U, h = 0)   ⟹   SpinNative.KernelTwistsGaugeTrivial P 𝓤
                                   ⟹   the Spin structure over the projected data is
                                        unique up to gauge equivalence.
```

`CechZ2.H1 𝓤.U` is the degree-1 cohomology of the **nerve of the given cover** with constant
`ℤ₂` coefficients, as constructed in `RequestProject/Spine/Cech/Cohomology.lean`.  Two steps
would be needed to turn this into a statement about `H¹(X;ℤ₂)`:

1. **cover → base.**  A comparison of `Ȟ*(𝓤;ℤ₂)` with the singular cohomology of `X`.  The
   project contains this only as an explicit *specification*
   (`RequestProject/Spine/Cech/SingularBridgeSpec.lean`,
   `RequestProject/Spine/GoodCover/SingularComparisonSpec.lean`,
   `RequestProject/Spine/Cohomology/CechBridgeSpec.lean`) and as the nerve comparison
   programme of `RequestProject/Spine/Nerve/**`; it is **not discharged** for degree 1 here.
2. **cover independence.**  Stability of the gate under refinement of the cover.  The
   project has refinement machinery for the degree-2 obstruction
   (`RequestProject/Spine/E2/Cech/Refinement.lean`, `RequestProject/Spine/Cech/Refinement.lean`)
   but no degree-1 statement that the kernel-twist quotient is refinement invariant.

Until both are available, the honest reading of the Task-31 endpoint is:

> the Spin structure produced by Spin-native provenance is canonical and deterministic, and
> it is unique up to gauge equivalence **on the given cover** exactly when that cover carries
> no nontrivial kernel-twist class.

---

## 7. Status of the two branches

Both branches required by Task 30 are preserved and neither was weakened.

* Standard SO-first control branch: `M → TM → P_SO → SO-valued transition data → local Spin
  lifts → ℤ₂ defect → obstruction`, unchanged; the uniqueness layer does not import
  `E2.Cech.LocalLifts`, `E2.Cech.Defect`, `E2.Cech.Coboundary` or `E2.Cech.Obstruction`
  (mechanically enforced, see `TASK31_CODE_HYGIENE.md`).
* Spin-native branch: `Spin-valued coherent gluing → ρ → SO/Lorentz gluing`, now extended by
  the uniqueness layer, still importing only the cover, the projection and the kernel
  predicate.
* The two meet only in `RequestProject/Spine/Comparison/**`, which no production module
  imports.
