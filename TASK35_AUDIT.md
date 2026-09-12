# TASK 35 — Pinned-Mathlib API audit (bundles, frames, smoothness)

Environment: Lean `v4.28.0`, Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
Toolchain, `lakefile.toml` and `lake-manifest.json` untouched.

This document records **exactly** which objects of the pinned Mathlib were available for the
Task-35 regularity/bundle layer, which were absent, and what was therefore built natively.
Nothing below was assumed: every "present" entry was `#check`ed in the pin, and every "absent"
entry was searched for by name *and* by statement shape before the native replacement was
written.

---

## 1. Present in the pin, and used

| object | form | where used in Task 35 |
|---|---|---|
| `VectorBundleCore ℝ X F ι` | structure with `baseSet`, `isOpen_baseSet`, `indexAt`, `mem_baseSet_at`, `coordChange`, `coordChange_self`, `continuousOn_coordChange`, `coordChange_comp` | `Solder/BundleEquivalence.lean` (general `SolderBundle` namespace) |
| `VectorBundleCore.TotalSpace`, `.Fiber`, `.proj`, `.localTriv`, `.localTriv_apply`, `.localTriv_symm_apply`, `.mem_localTriv_source` | defs/lemmas | construction and continuity of `coreTotalMap` |
| `Bundle.TotalSpace`, `Bundle.TotalSpace.mk'`, `.proj` | structure | total-space maps |
| `FiberBundleCore.continuous_proj`, `Trivialization.continuousOn`, `Trivialization.continuousOn_symm` | lemmas | `continuousOn_coreTotalMap`, `continuous_coreTotalMap` |
| `tangentBundleCore I M`, `tangentBundleCore_coordChange`, `tangentBundleCore_indexAt`, `achart` | defs/lemmas | `SpinNative.tangentCore`, and the identification of the genuine tangent transition |
| `TangentSpace I x` | a `def` that reduces to the model space `E` | used **only** where a genuine tangent vector is meant; explicitly *not* used as evidence of regularity (see §4) |
| `ContinuousLinearMap`, `ContinuousLinearEquiv`, `ContinuousLinearMap.inverse`, `ContinuousLinearMap.inverse_equiv` | | the comparison field `A i : LocalModel → (LocalModel ≃L[ℝ] LocalModel)` and its inverse |
| `contDiffAt_map_inverse` | smoothness of inversion on the units of `E →L[ℝ] E` | `contDiffOn_A_symm` |
| `ContDiffOn.fderivWithin`, `ContDiffOn.clm_comp`, `ContDiffOn.clm_apply`, `ContDiffOn.comp`, `isBoundedBilinearMap_apply` | | `contDiffOn_solderLorentzRep`, `contDiffOn_metricCoeff`, `contDiffOn_timeField` |
| `IsManifold`, `ChartedSpace`, `atlas`, `PartialHomeomorph` | | reuse of the Task-33 emergent atlas |
| `LinearMap.toContinuousLinearMap`, `LinearEquiv.toContinuousLinearEquiv` (finite dimensions) | | passage between the Task-34 fibrewise linear data and the regular continuous-linear data |
| `LinearMap.det` | | `frameChange_det` |
| `VectorBundleCore.IsContMDiff`, `ContMDiffVectorBundle` | mixin classes | inspected; **not** used, see §3 |

## 2. Absent from the pin

| searched for | result |
|---|---|
| a vector-bundle **morphism** or **equivalence** type (`VectorBundleEquiv`, `Bundle.Hom`, `ContinuousVectorBundleHom`, an isomorphism of `VectorBundleCore`s) | **absent**.  The pin has `Trivialization`, `Pretrivialization`, `VectorPrebundle`, `ContinuousLinearMap`-valued bundles and `VectorBundleCore`, but no type whose inhabitants are equivalences of two bundles over the same base |
| a smooth vector-bundle equivalence, or total-space diffeomorphism packaged for bundles | **absent** |
| a pseudo-Riemannian / Lorentzian metric structure (`LorentzianMetric`, `PseudoRiemannianMetric`, signature `(1,3)` predicate) | **absent**.  The pin's `RiemannianMetric` machinery is positive-definite and does not apply |
| a `SpinStructure` / smooth-`Spin(TM)` object | **absent** (as already recorded in Tasks 4–5) |
| `GeneralLinearGroup` as a **Lie group** with smooth inversion, in the form needed for a chart-valued frame | the algebraic `Units (E →L[ℝ] E)` and `contDiffAt_map_inverse` are present; a packaged smooth Lie-group structure specialised to a fixed finite-dimensional real model is not needed and was not used |

## 3. Consequences — what Task 35 built natively

1. **`SolderBundle.CoreBundleEquiv Z₁ Z₂`** (`Spine/Solder/BundleEquivalence.lean`).  Because the
   pin has no bundle-equivalence type, Task 35 defines one whose content is stated explicitly:
   a fibrewise `F ≃L[ℝ] F`-valued field `L`, together with continuity of the induced total-space
   map in *both* directions.  Its consequences are proved, not assumed:
   `toHomeomorph : Z₁.TotalSpace ≃ₜ Z₂.TotalSpace`, `toHomeomorph_proj` (it covers `id`), and
   `toHomeomorph_apply` (the fibrewise formula).  The local representatives in the two bundles'
   own trivializations are `coreRep`, and the exact coordinate-change square is
   `coreRep_symm_comp`.
2. **The metric predicate** (`Spine/Solder/SmoothMetric.lean`).  With no Lorentzian-metric
   structure in the pin, "smooth Lorentz metric" is given the explicit local-coefficient
   meaning: `metricCoeff i y u v`, with `metricCoeff_symm`, `metricCoeff_nondegenerate`,
   `contDiffOn_metricCoeff` (`C^∞` on `B.D i` for every `i, u, v`), the tensor law
   `metricCoeff_transform`, and the signature statement `metricCoeff_signature`.
3. **`VectorBundleCore.IsContMDiff` was deliberately not used.**  It is a mixin about the
   *coordinate changes of one core*.  Task 35 needs a statement about **two** cores and the
   comparison field between them, which the mixin cannot express; and the internal Lorentz core
   of the Spin seed carries only the seed's own **continuity**, so the mixin's hypothesis is not
   available for it.  Using it would have silently upgraded a topological datum.  This is the
   precise reason clause 5 of the principal certificate is a *topological* bundle equivalence
   while clauses 4, 6 and 7 are `C^∞` statements in the chart coordinates.

## 4. Deliberate non-use of a definitional equality

`TangentSpace localModelI x` reduces definitionally to `LocalModel`.  Task 34 used this to build
fibrewise data.  Task 35 treats it as **no evidence of regularity**: the negative control
`SpinNative.weak_solder_not_regular` (`Spine/Solder/WeakInsufficiency.lean`) exhibits a weak
Task-34 solder datum on a Task-33 emergent manifold whose representative in the *actual* chart
is not continuous, and whose fibrewise Task-34 "metric" coefficient is not continuous either.

## 5. Status vocabulary used in the Task-35 documents

| tag | meaning |
|---|---|
| FIBREWISE | true at each point, with no regularity in the base |
| TOPOLOGICAL | continuity proved, smoothness not claimed |
| SMOOTH | `ContDiffOn ℝ ⊤` proved in the actual Task-33 chart coordinates |
| DERIVED | proved from already-certified project data, no new hypothesis |
| ADDITIONAL DATUM | an input that must be supplied; not derivable from the data below it |
| ADDITIONAL THEOREM | true-or-false open statement, not proved here |
| BLOCKED BY INFRASTRUCTURE | the statement is formulable but a needed object is absent from the pin |
| NOT YET CLAIMED | intentionally outside the scope of this task |

---

# CORRECTION NOTICE (Task 36, §§1–4)

The Task-35 audit above is preserved verbatim.  Task 36 revised four of its entries; see
`TASK36_AUDIT.md` §§1–4 for the full argument and the exact missing library results.

| Task-35 entry | Task-36 correction |
| --- | --- |
| smooth bundle equivalence is blocked because the native Spin cocycle is only continuous | **wrong reason.**  The projected Lorentz representatives are already `C^∞` (`contDiffOn_solderLorentzRep`); the blocker is the absence of a vector-bundle morphism/equivalence type in the pinned Mathlib.  Classification: `smooth total-space packaging : BLOCKED BY INFRASTRUCTURE`.  Strongest correct result: `Task36.RegularBundleCertificate`, `Task36.nonempty_regularBundleCertificate_iff` |
| smoothness of the native Spin lift | **ADDITIONAL THEOREM / INFRASTRUCTURE BLOCKER**, not an additional geometric datum.  Missing: Cartan's closed-subgroup theorem, and the smooth-covering-map corollary for discrete-kernel smooth homomorphisms |
| `timeField_glue_iff` as the obstruction to a global timelike field | it is the gluing criterion of the **distinguished representative** only.  The time-orientation reduction itself is unconditionally derived: `Task36.nonempty_timeOrientationReduction_of_solder` |
| "the regular solder data form a torsor" with the group structure unpackaged | now packaged: `Group` + `MulAction` + `MulAction.IsPretransitive` + freeness in `RequestProject/Spine/Task36/GaugeGroup.lean`.  The pinned Mathlib has no multiplicative torsor class, so the wording used is "free and transitive regular gauge action" |
