# TASK 35 — Smooth solder / bundle-equivalence closure gate: provenance report

Environment: Lean `v4.28.0`, Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
(toolchain, `lakefile.toml` and `lake-manifest.json` untouched; no external project imported).
No `sorry`, no `admit`, no new `axiom`, no `native_decide`, no `unsafe`, no `partial`, no
`implemented_by`, no `Matrix.inv` in any new module.  Full build green
(`lake build RequestProject`, 8327 jobs, architecture audit passing).

---

## 0. Verdict

**The decisive question is answered YES, and the answer is a theorem.**

> `SpinNative.smooth_solder_iff_regular_bundle_equivalence`
> (`Spine/Solder/BundleEquivalence.lean`)
>
> For a smooth Task-33 base gluing `B` and an emergent Spin seed `S`,
> `Nonempty (SmoothTangentSolderData B S)` **iff** there is a fibrewise continuous-linear
> equivalence field `L` whose induced total-space maps `InternalLorentzBundle(S) → TM` and
> `TM → InternalLorentzBundle(S)` are both continuous, with `C^∞` local representatives `A i`
> in the charts of the pieces, satisfying the exact intertwining law.

So the missing regular coupling of Task 34 **is exactly** a bundle-level equivalence
`InternalLorentzBundle(S) ≃ TM`; no further geometric primitive is hidden between the two
notions.  This is stop condition **PASS-A for the decisive question**.

Two residual items are named exactly, in the PASS-B sense, and are *not* claimed:

* **BLOCKED BY INFRASTRUCTURE / ADDITIONAL DATUM.**  The equivalence is delivered at the
  **TOPOLOGICAL** level (total-space homeomorphism covering `id_M`, fibrewise linear) with
  **SMOOTH** local representatives.  A *smooth* total-space diffeomorphism is not claimed, for
  a mathematical reason, not a packaging one: the internal Lorentz bundle is built from the
  native Spin seed, whose own transition datum is only **continuous**
  (`NativeSpinTransitionData.continuousOn_g`).  Upgrading it requires the additional datum
  "the native Spin transition cocycle is smooth", which the project does not have.
  Independently, the pin contains no smooth-vector-bundle-equivalence type (see
  `TASK35_AUDIT.md` §2).
* **ADDITIONAL THEOREM.**  A *global* smooth future-directed timelike vector field.  What is
  derived is the reduction data and a `C^∞` representative *on each chart*, together with the
  exact gluing criterion.

The Spin endpoint is classified **TOPOLOGICAL SPIN LIFT**, not smooth `Spin(TM)`
(`spin_endpoint_topological`); the missing hypothesis is named in §9 below.

---

## 1. Dependency-DAG repair (task §1) — done before any new mathematics

`Spine/Solder/InternalLorentz.lean` no longer imports `Spine/Emergent/TangentTransition.lean`
(no declaration in it needs tangent geometry); `Spine/Solder/Independence.lean` now imports the
tangent-transition branch **and** the internal-Lorentz branch directly.  The architecture audit
`Spine/Audit/ArchitectureDAG.lean` was changed accordingly: the edge
`Solder.InternalLorentz → Emergent.TangentTransition` is now **forbidden** mechanically, and
`Solder.Independence` is *required* to reach both branches (so the check is not vacuous).

Resulting shape, now visible in the import graph and not only in prose:

```text
actual atlas  →  Emergent.TangentTransition ─────────┐
                                                     ├─→ Solder.Independence → Solder.Solder → …
native Spin   →  Solder.InternalLorentz ─────────────┘
```

## 2. Correction of the Task-34 claim (task §2)

Task 34 proved, for a concrete smooth rescaling gluing, that the raw tangent transition and the
raw projected Lorentz transition differ.  The exact content is

* **"direct/raw transition identification is not forced"** — and *not* "the solder coupling is
  proved non-derivable" in any universal sense; the very same control admits weak
  `TangentSolderData`, and Task 35 exhibits a *regular* solder for it
  (`SpinNative.rescaleRegularSolder`).  Raw transition inequality is therefore **not** an
  obstruction to solder equivalence.
* the Task-34 gate closes at the **FIBREWISE/algebraic** level only; the **TOPOLOGICAL/SMOOTH**
  solder gate was left open, and is what Task 35 closes.

Annotations recording this were added (without deleting historical wording) to
`TASK34_PROVENANCE.md`, `TASK34_AUDIT.md`, `TASK34_DOCUMENTATION_REPAIR.md`,
`TASK34_CODE_HYGIENE.md`, and to the module docstring of `Spine/Solder/Independence.lean`.

## 3. API audit (task §3)

See `TASK35_AUDIT.md`.  Summary: `VectorBundleCore`, `tangentBundleCore`, trivializations,
`Bundle.TotalSpace`, `ContinuousLinearMap`/`ContinuousLinearEquiv`, `ContinuousLinearMap.inverse`,
`contDiffAt_map_inverse`, `ContDiffOn.fderivWithin/clm_comp/clm_apply` are present and used; a
vector-bundle **equivalence** type and any pseudo-Riemannian/Lorentzian **metric structure** are
absent, so both were built natively with their local-coordinate content stated explicitly.

## 4. The weak Task-34 datum is insufficient (task §4) — NEGATIVE CONTROL, proved

`Spine/Solder/WeakInsufficiency.lean`, on the flat Task-33 emergent manifold
`flatBase = symmetricGluing Unit isOpen_univ`:

* `badSolder : TangentSolderData flatBase (trivialCocycle …)` — a genuine weak Task-34 datum
  whose frame field is `2 • id` at one point and `id` elsewhere;
* `badSolder_rep_not_continuousOn` — its representative in the **actual** tangent
  trivialization is not continuous;
* `badSolder_metric_not_continuousOn` — the fibrewise Task-34 "metric" coefficient of the same
  datum is not continuous either;
* `weak_solder_not_regular` — therefore no `SmoothTangentSolderData` induces it.

No use is made of the definitional equality `TangentSpace localModelI x = LocalModel` as
evidence of regularity; that equality is precisely what the control defeats.

## 5. The regular solder (task §5)

`SpinNative.SmoothTangentSolderData B S` (`Spine/Solder/RegularSolder.lean`) is **local on the
cover**:

* `A : ι → LocalModel → (LocalModel ≃L[ℝ] LocalModel)` — for each piece `i`, a comparison in the
  *chart coordinates* of that piece between the internal Lorentz fibre and the genuine tangent
  space;
* `contDiffOn_A : ∀ i, ContDiffOn ℝ ⊤ (fun y => (A i y : LocalModel →L[ℝ] LocalModel)) (B.D i)`;
* `intertwine` — the overlap square, in the **exact** index order and composition convention
  *derived from* `VectorBundleCore.coordChange` and `tangentBundleCore_coordChange`, not by
  analogy:

```text
        internal fibre j  ──ρ(g̃_ij)(x)──▶  internal fibre i
              │ A j (φ_ij y)                        │ A i y
              ▼                                     ▼
        tangent chart j  ◀──D(φ_ij)(y)────  tangent chart i
```

i.e. `A j (φ_ij y) = D(φ_ij)(y) ∘ A i y ∘ ρ(g̃_ij)(x)` with `x = chart i ⟨y⟩`, derived from
`tangentBundleCore.coordChange ⟨pieceChart i⟩ ⟨pieceChart j⟩ (chart i ⟨y⟩) = D(φ_ij)(y)` and
`(internalLorentzBundleCore S).coordChange i j x = ρ(g̃_{j i})(x)`.

Compatibility with Task 34 is kept but clearly separated: `toTangentSolderData` is the
**forgetful** map to the weak object (using an off-patch default value that no theorem depends
on), and §4 shows the forgetful map is not surjective.

Consequences proved here: `contDiffOn_A_symm`, `localFrame`/`localFrame_compat` (patch frames
without any arbitrary index choice), and
`contDiffOn_solderLorentzRep` — **a regular solder forces the projected internal Lorentz
transition to have a `C^∞` chart representative** (SMOOTH), even though the native Spin datum
itself is only continuous.

## 6. Regular soldering = bundle equivalence (task §6) — PRINCIPAL THEOREM

`Spine/Solder/BundleEquivalence.lean`.  Native certificate
`SolderBundle.CoreBundleEquiv Z₁ Z₂` (fibrewise `≃L`, continuous total maps both ways), with

* `toHomeomorph : Z₁.TotalSpace ≃ₜ Z₂.TotalSpace`, `toHomeomorph_proj` (covers `id_M`),
  `toHomeomorph_apply` (fibrewise formula);
* `coreRep`/`coreRep_symm_comp` — the local representatives and the exact coordinate-change
  square;
* project instance: `tangentCore h` is Mathlib's own `tangentBundleCore` of the Task-33 atlas;
  `coreRep_eq` proves the local representative of the induced map **is** `A i`, and
  `continuousOn_coreRep(_inv)` its two-sided regularity;
* `toCoreBundleEquiv`, `toTangentHomeomorph`;
* converse `smoothTangentSolderData_of_localRep`;
* the iff `smooth_solder_iff_regular_bundle_equivalence` (see §0).

This is **not** called a merely fibrewise family: the total-space maps are proved continuous in
both directions, and the local representatives are `C^∞`.

## 7. The smooth Lorentz metric (task §7)

`Spine/Solder/SmoothMetric.lean`, from `SpinCore.BS` and the regular solder only:
`metricCoeff_symm` (symmetry), `metricCoeff_nondegenerate` (nondegeneracy),
`metricCoeff_signature` (signature `(1,3)`: one positive direction, three-dimensional negative
definite complement), `metricCoeff_transform` (chart/piece independence: the tensor law under
`D(φ_ij)`), and `contDiffOn_metricCoeff` (**SMOOTH**: `ContDiffOn ℝ ⊤` on `B.D i`, for all
`i, u, v`).  Packaged as `smooth_tangent_lorentz_metric`.  `tangentMetric_localFrame` links the
result to the Task-34 fibrewise object; the Task-34 object alone is *not* called a smooth
Lorentz metric.

## 8. Orientation and time orientation (task §8)

`Spine/Solder/OrientationTime.lean`.  No arbitrary index-choice function occurs.

| item | status |
|---|---|
| orientation reduction: `frameChange_det = 1` | **DERIVED** |
| time-orientation reduction: `futureCone_transform`, `futureCone_eq_of_mem` | **DERIVED** |
| chosen smooth representative *on each chart*: `timeField`, `contDiffOn_timeField`, `timeField_mem_futureCone`, `metricCoeff_timeField = 1` | **DERIVED (SMOOTH, local)** |
| *global* smooth timelike field | **ADDITIONAL THEOREM.**  `timeField_glue_iff` gives the exact obstruction: the local fields glue iff the projected Lorentz cocycle fixes the intrinsic unit `sOne`; `timeField_glue_of_trivial` is the positive special case.  A partition-of-unity argument is not carried out |

Packaged as `orientation_time_orientation_status`.  The Task-34 expression
`x ↦ tangentLinearEquiv (idx x) sOne` is **not** claimed to be a smooth global time field.

## 9. Regularity level of the Spin endpoint (task §9)

`spin_endpoint_topological` (`Spine/Comparison/SmoothSolderGate.lean`) records exactly:

1. tangent Lorentz frame cocycle = projected native Lorentz cocycle (**DERIVED**);
2. the native Spin datum is a Spin lift of that cocycle (**DERIVED**);
3. its regularity is **continuity** (the seed's own condition), while the *projected Lorentz*
   transition is `C^∞` in chart coordinates thanks to the regular solder.

Classification: **TOPOLOGICAL SPIN LIFT.**  It is *not* upgraded to a smooth `Spin(TM)`.  The
missing hypothesis/infrastructure is named exactly: a **smooth** structure on the intrinsic Spin
group together with a **smooth** local section of `SpinCore.spinCover` — the project currently
certifies only the *continuous* local section (`SpinCore.spinCover_hasLocalSection`), so
smoothness of the lift does not follow from smoothness of the projected transition.  No `w₁`,
`w₂` or Stiefel–Whitney statement is imported, assumed or proved anywhere in Task 35.

## 10. Positive controls and non-vacuity (task §10)

`Spine/Solder/RegularExamples.lean`:

* `symmetricRegularSolder` — the symmetric canonical Task-33 gluing (`A ≡ id`);
* `rescaleRegularSolder` — the Task-34 rescaling gluing, with `A₀ = id`, `A₁ = 2 • id`;
  `nonempty_smoothTangentSolderData_rescaleGluing`;
* `rescale_const_id_not_solder` — on that same gluing the *constant identity* comparison is
  **not** a solder.

Hence the structure is non-vacuous and genuinely constrains: raw transitions differ, yet a
nontrivial local gauge gives a regular bundle equivalence.  There is deliberately **no**
theorem `Nonempty (SmoothTangentSolderData B S)` for arbitrary `B, S`; such a theorem would be
the red flag the task warns about.

## 11. Residual gauge freedom (task §11)

`Spine/Solder/RegularGauge.lean`: `RegularTangentGauge B` is the group of `C^∞` chartwise
tangent-bundle automorphism fields (not arbitrary pointwise automorphisms).  `act` preserves
regular solder data, `exists_regularGauge` is transitivity, `regularGauge_unique` is freeness;
`regular_solder_torsor` packages the three.  With freeness *and* transitivity proved, the word
"torsor" is justified for the **regular** structure; the Task-34 wording, which used the word
for arbitrary pointwise automorphism fields, is annotated rather than deleted.

## 12. The principal certificate (task §12)

`SpinNative.SmoothTangentSolderData.smooth_solder_tangent_certificate`
(`Spine/Comparison/SmoothSolderGate.lean`), nine clauses: the Task-33 smooth four-manifold; the
genuine tangent transitions as derivatives of the actual atlas; the internal transitions as the
projected native Spin transitions; the intertwining with `C^∞` local representatives; the bundle
equivalence covering `id_M`; the smooth Lorentz metric (symmetry, nondegeneracy, tensor law,
`C^∞` coefficients); orientation and time orientation at the exact level proved; the frame
cocycle equality; the Spin lift at topological level.

It contains no `w₁`, `w₂`, Stiefel–Whitney class, Levi-Civita connection, spin connection,
curvature, torsion, Einstein equation, dynamics or quantization — and neither does its import
closure below `Mathlib`.

## 13. Modules added and edited

Added (all `sorry`-free, each ending with in-source `#print axioms`):

```
RequestProject/Spine/Solder/RegularSolder.lean
RequestProject/Spine/Solder/RegularExamples.lean
RequestProject/Spine/Solder/BundleEquivalence.lean
RequestProject/Spine/Solder/SmoothMetric.lean
RequestProject/Spine/Solder/OrientationTime.lean
RequestProject/Spine/Solder/WeakInsufficiency.lean
RequestProject/Spine/Solder/RegularGauge.lean
RequestProject/Spine/Comparison/SmoothSolderGate.lean
```

Edited: `Spine/Solder/InternalLorentz.lean` (import removal + docstring),
`Spine/Solder/Independence.lean` (imports, docstring annotation, hygiene),
`Spine/Solder/Solder.lean` (hygiene only), `Spine/Audit/ArchitectureDAG.lean` (firewall
extension).  No pre-existing theorem statement was changed.

## 14. Hygiene and axioms

See `TASK35_CODE_HYGIENE.md`.  Every Task-35 endpoint reports
`[propext, Classical.choice, Quot.sound]`.

## 15. Failed builds

See `TASK35_FAILBUILDS.md` (twelve entries; none changed a statement, an assumption or the
architecture).

---

# CORRECTION NOTICE (Task 36, §§1–3)

The Task-35 text above is preserved verbatim.  Three of its classifications were reviewed in
Task 36 and two of them were found to be overstatements.  The corrected classifications are:

1. **Smooth bundle equivalence.**  Task 35 attributed the absence of a *smooth* total-space
   bundle equivalence to the fact that the native Spin cocycle is only required to be
   continuous.  That is too strong, and it conflates *internal Lorentz bundle smoothness*
   with *smooth Spin bundle structure*.  Task 35 already proves, through
   `SpinNative.SmoothTangentSolderData.contDiffOn_solderLorentzRep`, that the projected
   Lorentz transition representatives are `C^∞`; Task 36 uses exactly that to prove
   `Task36.internal_bundle_coordChange_smooth_in_charts` and to build
   `Task36.RegularBundleCertificate` (continuous total-space equivalence, continuous inverse,
   fibrewise linearity, smooth local representatives, smooth local representatives of the
   inverse, exact transition intertwining), with `Task36.nonempty_regularBundleCertificate_iff`.
   The correct classification is

   ```text
   smooth total-space packaging : BLOCKED BY INFRASTRUCTURE
   ```

   (the pinned Mathlib has no vector-bundle morphism/equivalence type), **not** "requires
   smooth native Spin transitions".

2. **Smoothness of the native Spin lift.**  This is an additional *theorem/infrastructure*
   problem, not an additional geometric datum.  The missing standard results are Cartan's
   closed-subgroup theorem (to give `SpinGroup` and `GLor` smooth structures) and the
   corollary that a smooth homomorphism with discrete kernel is a smooth covering map;
   neither is in the pinned Mathlib.  No new primitive datum was introduced, and the
   intrinsic Spin group was **not** replaced by `SL(2,ℂ)` or a matrix model.

3. **Time orientation.**  `SpinNative.SmoothTangentSolderData.timeField_glue_iff` is the exact
   gluing criterion for the *distinguished representative* `A_i(𝟙_𝒮)`, and is **not** an
   obstruction to time orientability.  Task 36 isolates
   `Task36.TimeOrientationReduction` and proves
   `Task36.nonempty_timeOrientationReduction_of_solder`: a regular solder *always* yields a
   coherent smooth future-cone reduction.  The classification is

   ```text
   time-orientation reduction            : DERIVED
   global smooth timelike representative : ADDITIONAL THEOREM / INFRASTRUCTURE BLOCKER
   ```

Full details: `TASK36_AUDIT.md` §§1–3.
