# TASK 34 — Tangent/Solder coupling gate: provenance report

Environment: Lean `v4.28.0`, Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
(toolchain, manifest and Mathlib revision untouched).  No `sorry`, no `admit`, no new
`axiom`, no `native_decide`, no `unsafe`, no `partial`, no `implemented_by` in any new
production module.

**Outcome: B — one explicit solder coupling is additionally required, and with it the gate
closes completely.**  Secondary outcomes **C** and **E** are also recorded as theorems: the
model-space identification `LocalModel = TangentSpace localModelI x` is available but is
*not* a solder form (it carries no overlap law), and the compatible solder fields are a
torsor under pointwise tangent automorphism fields, so none of them is canonical.

Outcome **A** is refuted (`SpinNative.tangent_spin_base_data_do_not_force_transition_identification`),
outcome **D** does not arise (the negative control is already smooth and the symmetric sector
is not needed for it), and outcome **F** did not occur: no module of the bottom-up branch
imports the top-down tangent/frame machinery, and the mechanical firewall now checks this.

---

## 1. Source/DAG audit before new mathematics (§3)

### 1.1 The bottom-up branch, as it actually exists

| object | exact declaration | file |
|---|---|---|
| local model | `EmergentBase.LocalModel` (`abbrev` for `SpinCore.LorentzCarrier`) | `Spine/Emergent/LocalModel.lean` |
| base-gluing primitive | `EmergentBase.BaseGluingData` | `Spine/Emergent/BaseGluing.lean` |
| emergent base | `EmergentBase.BaseGluingData.Space` | `Spine/Emergent/Reconstruction.lean` |
| charts | `BaseGluingData.chartOfPoint`, `BaseGluingData.pieceChart` | `Reconstruction.lean`, `SmoothStructure.lean` |
| Task-33 manifold | `BaseGluingData.isManifold_of_smoothGluing` (+ instance `instChartedSpaceSpace`) | `Spine/Emergent/SmoothStructure.lean` |
| emergent cover | `EmergentBase.emergentCover` | `Spine/Emergent/CoverAdapter.lean` |
| emergent Spin seed | `SpinNative.emergentSeed` | `Spine/Comparison/EmergentSpinGate.lean` |
| projected cocycle | `SpinNative.CanonicalSpinSeed.projected` = `SpinNative.project SpinCore.internalSpinProjection` | `Spine/Comparison/CanonicalSpinSeed.lean`, `Spine/SpinNative/Projection.lean` |

### 1.2 The top-down control branch

`Spine/Geometry/FrameField.lean`, `Spine/Geometry/TangentInstance.lean`,
`Spine/Geometry/SpinStructure.lean`, `Spine/Geometry/Z2Class.lean`,
`Spine/GoodCover/W2Interface.lean`.  `LorentzFrames.LorentzTangentFrameData` *assumes*
tangent-frame data, so it is a certification target only.

### 1.3 The recorded dependency firewall

```text
Emergent.LocalModel → BaseGluing → Reconstruction → Symmetric → SmoothGate
                                → SmoothStructure → Emergent.TangentTransition      (base-free)
Emergent.CoverAdapter + E2.SpinProjection + SpinNative.Projection
                                → Solder.InternalLorentz → Solder.Independence
                                → Solder.Solder → Solder.LorentzBundle              (bottom-up)
Solder.Solder + Geometry.TangentInstance → Comparison.SolderTangentGate             (leaf)
```

`Spine/Audit/ArchitectureDAG.lean` check 9 now also covers `Emergent.TangentTransition`
(which may reach no `E2`, `Cech`, `Geometry`, `Nerve`, `GoodCover`, `Cohomology`,
`AlgebraicTopology`, `SpinNative`, `Comparison` or `Controls` module), and the new check 10
covers the four `Spine.Solder` modules (which may reach no `Geometry`, `Cech`, `Nerve`,
`GoodCover`, `Cohomology`, `AlgebraicTopology`, `Comparison`, `Controls` module and no
obstruction module of `E2.Cech`).  Positive controls make each check sensitive, and the
comparison module is required to reach *both* branches.

One pre-existing rule was widened, with its justification recorded in the source: the rule
"the standard branch must not depend on the Spin-native branch" previously exempted only
`Spine.Comparison`; it now also exempts `Spine.Solder`, whose entire subject is the coupling
of the projected Spin/Lorentz transition with the tangent geometry.  This is a widening of an
*exemption list*, not a weakening of any theorem, and the new check 10 constrains the exempt
layer much more tightly than the old rule did.

---

## 2. What was proved (§§5–15), question by question (§22)

**(1) What are the genuine tangent transition maps of the Task-33 emergent manifold?**

`EmergentBase.BaseGluingData.tangentTransitionMap B i j y = fderivWithin ℝ (B.φ i j) (B.W i j) y`,
and `EmergentBase.BaseGluingData.tangentTransition` packages it as a continuous linear
equivalence whose inverse is `D(φ_ji)(φ_ij y)` — invertibility is *derived* from the
primitive's inversion law by the chain rule.

The principal theorem is
`EmergentBase.BaseGluingData.tangentTransition_eq_derivative_baseTransition`: for two charts
of the *actual* Task-33 atlas, Mathlib's own
`(tangentBundleCore localModelI (Space B)).coordChange` at a point of the overlap equals
`D(φ_ij)`.  The proof goes through the Task-33 identification of the coordinate changes
(`transition_source`, `transition_apply`, `pieceChart_apply`, `pieceChart_symm_apply`); the
general Mathlib construction is *not* merely quoted.
`exists_tangentTransition_of_mem_atlas` states the same for arbitrary atlas members.

**(2) How do they compare with the projected internal Lorentz transitions?**

`SpinNative.projectedLorentzTransition S i j x : LocalModel ≃ₗ[ℝ] LocalModel` is the action
of the projected Spin cocycle on the local model — no external `SO(1,3)` representation, since
`SpinCore.GLor` is by construction a subgroup of `LocalModel ≃ₗ[ℝ] LocalModel`.  It inherits
preservation of `NS`, `BS`, `ConeS`, `IntFuture` and `det = 1`, together with the identity,
inverse and cocycle laws and continuity on double overlaps
(`SpinNative.internal_lorentz_transition_system`).

**(3) Is their coupling derivable from the previous data?  No.**

`SpinNative.tangent_spin_base_data_do_not_force_transition_identification`.  The witness is
`EmergentBase.rescaleGluing`: two pieces, both equal to the whole local model, with
`φ₀₁(v) = 2 • v` and `φ₁₀(v) = 2⁻¹ • v`.  All primitive laws hold, the datum is smooth, and
Task 33 makes its emergent base a `C^∞` manifold.  Paired with the pointwise trivial
Spin-native datum the projected Lorentz transition is the identity everywhere, while
`D(φ₀₁) = 2 • id`; the two differ already on the intrinsic unit.

This is a **non-derivability** statement.  It is *not* a non-existence statement, and the
distinction is itself proved: `SpinNative.nonempty_tangentSolderData_rescaleGluing` exhibits a
compatible solder field over that very base.

**(4) What exactly is additionally required?**

`SpinNative.TangentSolderData B S`: for each piece `i` a fibrewise real-linear equivalence
`frame i x : LocalModel ≃ₗ[ℝ] TangentSpace localModelI x` of the internal Lorentz model with
Mathlib's genuine tangent space, subject to the single overlap law

```text
frame j x v = frame i x (ρ(g̃_ij)(x) v)      for x ∈ U i ∩ U j
```

i.e. the commuting square of §9 with the orientation fixed by the project's own conventions
(`comparison = e_i⁻¹ ∘ e_j`, Čech law `g_ij·g_jk = g_ik`); the composition check is
`TangentSolderData.compatibility_comp`.  Invertibility is in the type; the domain condition is
the overlap quantifier; the regularity that the Lorentz side can see is *derived*
(`TangentSolderData.continuousOn_comparison`), so it is deliberately not a field.  No metric,
connection, curvature, torsion or dynamics is part of the datum.

**(5) Is the internal Lorentz structure then genuinely identified with `TM`?**

Fibrewise yes, with the exact overlap compatibility:
`TangentSolderData.tangentLinearEquiv`, and in bundle language
`SpinNative.internalLorentzBundleCore` (a genuine Mathlib `VectorBundleCore` over `Space B`
with fibre `LocalModel` and transition functions exactly the projected Lorentz action)
together with `TangentSolderData.toInternalLorentzFiberEquiv` and
`TangentSolderData.coordChange_intertwines`.  The derived tangent geometry is
`TangentSolderData.tangentMetric` with
`tangentMetric_wellDefined`, `tangentMetric_frame_isometry`, `tangentMetric_nondegenerate`,
`finrank_tangentSpace` and the package `tangentMetric_isLorentz`.

What is **not** packaged is an isomorphism of *topological* vector bundles; see §4 below.

**(6) Does the tangent Lorentz frame cocycle equal the projected native Lorentz cocycle?**

Yes: `SpinNative.TangentSolderData.projected_eq_tangentFrameTransition`, after
`TangentSolderData.toLorentzTangentFrameData` constructs genuine
`LorentzFrames.LorentzTangentFrameData` on the emergent manifold.

**(7) Is the native Spin structure a lift of the actual tangent Lorentz frame data?**

Yes: `SpinNative.TangentSolderData.nativeSpin_to_tangentSpinFrameStructure`, packaged in
`TangentSolderData.solder_tangent_certificate`.  No statement about `w₁`, `w₂`, connections
or curvature is made anywhere.

**(8) Documentation repair.**  See `TASK34_DOCUMENTATION_REPAIR.md` and §5 below.

---

## 3. Orientation and time orientation (§12)

| datum | classification | witness |
|---|---|---|
| orientation of the tangent fibres | **DERIVED** from the solder datum | `TangentSolderData.tangentVol`, `tangentVol_frame_pos`; uses `det ρ(g̃_ij) = 1` |
| time orientation | **DERIVED** from the solder datum | `TangentSolderData.tangentTimeField`, `tangentMetric_timeField`, `tangentMetric_timeField_frame`; uses that `GLor` preserves `SpinCore.IntFuture` |
| values in the native proper orthochronous group | **DERIVED** | the frame comparisons *are* `GLor`-elements by `TangentSolderData.comparison_eq`, and the resulting `LorentzTangentFrameData.transition` is `GLor`-valued by construction |
| continuity/smoothness of the metric field as a bundle section | **ADDITIONAL CHOICE (not derived, not claimed)** | see §4 |

So no extra orientation or time-orientation choice is required once the solder datum is
given: both are inherited from the internal Lorentz structure of the Clifford core.

---

## 4. Exactly what remains un-packaged

1. **Topological bundle isomorphism.**  `InternalLorentzBundle ≃ TangentBundle` as
   *topological* vector bundles is not constructed.  The reason is recorded and is
   mathematical, not technical: `TangentSolderData` imposes no continuity on the frames
   themselves, only the overlap law, whose regularity is automatic.  Strengthening the datum
   by a frame-regularity field would be a *different, stronger* primitive; Task 34 isolates
   the weakest one that closes the algebraic gate, and proves the fibrewise statement plus the
   exact intertwining of transition systems.
2. **Continuity of the tangent metric field.**  For the same reason.  In a solder frame the
   metric coefficients are *constant* (they are `BS`), so the obstruction is precisely the
   regularity of the frame field, not of the metric construction.
3. **Converse of the solder gate.**  It is not claimed that a compatible solder datum exists
   for every `(B, S)`; what is proved is existence for the trivial seed over an arbitrary
   emergent base (`SpinNative.nonempty_tangentSolderData`), which is what non-vacuity of every
   sufficiency theorem in this layer requires.
4. **Uniqueness.**  Deliberately not claimed; the exact residual freedom is proved instead
   (`TangentSolderData.exists_gauge`, `TangentSolderData.gauge`,
   `TangentSolderData.not_unique`).

---

## 5. Falsification conditions (§19), each explicitly rejected

| shortcut | status in this task |
|---|---|
| `TangentSpace` is implemented using `LocalModel` ⇒ internal Lorentz model = `TM` | rejected.  The definitional identification is isolated as `EmergentBase.tangentSpace_eq_localModel` and labelled an implementation artefact; it is used *only* to witness non-vacuity of `TangentSolderData` for the trivial seed, never as a proof of a coupling statement. |
| same dimension 4 ⇒ bundles globally equivalent | rejected; no such inference occurs.  `finrank_tangentSpace` is proved *through* the solder equivalence. |
| a Spin cocycle exists ⇒ it is the tangent-frame cocycle | rejected by the main independence theorem; the equality is proved only *after* a solder datum is assumed. |
| smooth emergent manifold ⇒ it carries the Lorentz metric | rejected; the metric is constructed from the solder datum and from `BS`. |
| local Lorentz metric ⇒ globally well defined | rejected; well-definedness is the theorem `tangentMetric_wellDefined`, and it is exactly where the Lorentz overlap law is consumed. |
| Spin structure on an abstract cocycle ⇒ conventional Spin structure of `TM` | rejected; the endpoint is a `SpinFrameStructure` for the solder-derived *tangent* frame data, and no `w₂` identification is claimed. |
| a solder field is chosen ⇒ it is canonical | rejected; `exists_gauge` and `not_unique`. |

---

## 6. Build and axiom audit (§20)

* `rm -rf .lake/build && lake build RequestProject` — green (see `TASK34_FAILBUILDS.md` for
  every intermediate failure).
* `#print axioms` is run inside each new module on every principal endpoint; all report
  exactly `[propext, Classical.choice, Quot.sound]`.  No `sorryAx`.
* `RequestProject.Spine.Audit.ArchitectureDAG` compiles, i.e. the extended firewall passes:
  `Task-34 tangent/solder firewall audited: 4 bottom-up modules + 1 comparison join; illegal
  edges: 0`.

---

# TASK-35 CORRECTION NOTICE (2026-09-12)

*Historical text above is preserved verbatim; the following annotation states the exact
content of the Task-34 results, as required by Task 35 §2.*

1. The phrase **"outcome B — … and with it the gate closes completely"** (opening paragraph)
   over-states what was proved.  The exact statements are:
   * **"direct/raw transition identification is not forced"**
     (`SpinNative.tangent_spin_base_data_do_not_force_transition_identification`): for one
     concrete smooth rescaling gluing the raw tangent transition differs from the raw projected
     Lorentz transition.  This is *not* a proof that no solder coupling can be derived by any
     construction, and the same control does admit solder data.
   * **"the fibrewise/algebraic solder gate closes; the topological/smooth solder gate remains
     open"** — Task 34 proved no regularity of the solder frames, no continuity/smoothness of
     the induced metric, no bundle equivalence and no smooth Lorentzian structure.
2. The **torsor** wording of Task 34 refers to arbitrary *pointwise* tangent automorphism
   fields.  For the regular structure the correct gauge group is the group of `C^∞` chartwise
   tangent-bundle automorphism fields (`SpinNative.RegularTangentGauge`), for which
   transitivity and freeness are proved in Task 35.
3. The topological/smooth gate left open here was closed by Task 35 at the level stated in
   `TASK35_PROVENANCE.md` §0: regular solder data are *equivalent* to a bundle equivalence
   `InternalLorentzBundle(S) ≃ TM` (total-space homeomorphism covering `id_M`, fibrewise
   linear, with `C^∞` local representatives); the transported Lorentz metric is smooth; the
   Spin endpoint remains a **topological** Spin lift.
4. Task 35 also showed that a weak Task-34 `TangentSolderData` need **not** be regular
   (`SpinNative.weak_solder_not_regular`), so the Task-34 object is strictly weaker than the
   Task-35 one.
