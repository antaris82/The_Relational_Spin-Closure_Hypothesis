# TASK 34 — audit: the tangent/solder coupling gate

Environment: Lean `v4.28.0`, Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

This document records what the Task-34 layer proves, what it deliberately does not prove, and
which shortcuts were rejected.  The provenance report is `TASK34_PROVENANCE.md`, the failed
builds are in `TASK34_FAILBUILDS.md`, the hygiene report is `TASK34_CODE_HYGIENE.md`, and the
terminology repair of Tasks 32/33 is in `TASK34_DOCUMENTATION_REPAIR.md`.

---

## 1. The arrow that was missing, and the arrow that now exists

Before Task 34:

```text
E1 Clifford/Spin/Lorentz core → internal Lorentz model V → base-gluing layer
                              → smooth emergent 4-manifold M           (Task 33)

internal Lorentz model / Lorentz cocycle   ——?——>   TM
```

After Task 34:

```text
internal Lorentz model
        ↓            (SpinNative.internalLorentzBundleCore)
internal Lorentz bundle over M
        ↓            (SpinNative.TangentSolderData — an explicit new datum, proved additional)
       TM            (fibrewise, with exact overlap compatibility)
        ↓
tangent Lorentz metric, orientation, time orientation, GLor-valued frame cocycle
        ↓
native Spin structure of the *actual* tangent Lorentz frame data
```

The middle arrow is **not** derivable from the certified Task-32/33 data.  That is the main
scientific content, and it is a theorem, not an observation.

## 2. Anti-shortcut record (§4)

Mathlib implements `TangentSpace I x` by the model vector space, so for this manifold
`TangentSpace localModelI x` and `LocalModel` are definitionally the same type.  This is
recorded once, as `EmergentBase.tangentSpace_eq_localModel`, and explicitly labelled an
implementation artefact.  It is used in exactly one place in the whole layer: to witness that
`TangentSolderData` is inhabited for the pointwise trivial Spin seed
(`SpinNative.modelSolder`), i.e. to keep the sufficiency theorems non-vacuous.  It is never
the proof of a coupling statement.

Why it is not a solder form, in the language of this project: the type-level identification
is chart-blind.  The tangent trivialization it corresponds to in `tangentBundleCore` is the
one attached to `achart` — the chart of the *representative that the quotient machinery
selects at each point* (`chartOfPoint_eq_pieceChart`, Task 33) — which varies from point to
point with no coherence.  What carries geometric content is the transition law between two
charts of the actual atlas, and that is exactly what
`tangentTransition_eq_derivative_baseTransition` computes.

No principal theorem of this layer is proved by `rfl`, `LinearEquiv.refl`, a tangent-space
cast, or a dimension count.

## 3. Outcome classification (§18)

* **Outcome A (solder derived): refuted.**
  `SpinNative.tangent_spin_base_data_do_not_force_transition_identification`.
* **Outcome B (one explicit solder coupling required): this is the result.**
  `SpinNative.TangentSolderData` plus
  `tangentMetric_isLorentz`, `projected_eq_tangentFrameTransition`,
  `nativeSpin_to_tangentSpinFrameStructure`, `solder_tangent_certificate`.
* **Outcome C (only the model-level identification is automatic): also recorded**, as the
  precise distinction of §2 above; the type-level identification is never called a solder
  form, and the missing law is named — it is the overlap law, the single field
  `TangentSolderData.compatibility`.
* **Outcome D (symmetric sector closes automatically): not claimed.**  The negative control
  is a *smooth* two-chart datum; no statement is generalized from the symmetric sector, and
  none is needed.
* **Outcome E (noncanonicity): proved.**  `TangentSolderData.gauge`,
  `TangentSolderData.exists_gauge` (the residual freedom is *exactly* a pointwise
  automorphism field of `TM`, independent of the index), `TangentSolderData.not_unique`.
* **Outcome F (architecture regression): did not occur.**  The mechanical firewall
  (`Spine/Audit/ArchitectureDAG.lean`, checks 9 and 10) fails to compile if the bottom-up
  branch reaches `Spine.Geometry` at all.

## 4. Regularity: exactly what is and is not available

`TangentSolderData` carries no regularity condition on the frames.  Three consequences, all
recorded as such:

1. **Derived and available.**  The frame comparisons are continuous on double overlaps,
   because by `TangentSolderData.comparison_eq` they *are* the projected Spin transitions
   (`TangentSolderData.continuousOn_comparison`).  This is what the top-down
   `LorentzFrameData.continuousOn_comparison` field requires, so the comparison module needs
   no extra hypothesis.
2. **Not available: continuity of the metric field as a section.**  In a solder frame the
   metric coefficients are constant (`tangentMetric_frame_isometry` gives `BS`), so the
   obstruction is the regularity of the frame field itself, not of the metric construction.
   Classification: **ADDITIONAL — not derived, not claimed.**
3. **Not available: a topological vector-bundle isomorphism
   `InternalLorentzBundle ≃ TangentBundle`.**  Same reason.  What is proved instead is the
   fibrewise equivalence together with the exact intertwining of the coordinate changes
   (`TangentSolderData.toInternalLorentzFiberEquiv`,
   `TangentSolderData.coordChange_intertwines`), which is the invariant content of the
   commuting square.  Classification: **UN-PACKAGED, with the missing ingredient named.**

Strengthening the datum with a frame-regularity field would give a different, strictly
stronger primitive.  Task 34 isolates the weakest datum that closes the algebraic gate; this
makes every sufficiency theorem in the layer correspondingly stronger.

## 5. Orientation and time orientation (§12)

| item | classification |
|---|---|
| fibrewise orientation of `TM` | **DERIVED** from the solder datum (uses `det ρ(g̃_ij) = 1`) |
| fibrewise time orientation of `TM` | **DERIVED** from the solder datum (uses preservation of `SpinCore.IntFuture` by `GLor`) |
| frame transitions land in the native proper orthochronous `GLor` | **DERIVED** |
| a *continuous* global orientation/time-orientation field | **NOT FORMALISED** (same regularity gap as §4) |

## 6. Non-goals, verified absent (§16)

No declaration of the Task-34 layer mentions or depends on `w₁`, `w₂`, Stiefel–Whitney
classes, connections, spin connections, Levi-Civita connections, parallel transport,
holonomy, curvature, torsion, Einstein/Palatini/Einstein–Cartan equations, dynamics or QFT.
The Spin endpoint is a lift of a *transition cocycle*; its relation to the conventional
`w₂(TM)` is untouched, as in Tasks 4 and 30–33.

## 7. Sensitivity of the negative control

The control is not vacuous in any of the usual ways:

* the base-gluing datum satisfies every field of `BaseGluingData` (checked by the elaborator);
* it is smooth, so Task 33 applies and `IsManifold localModelI ⊤ (Space rescaleGluing)` holds;
* the Spin datum is a genuine `NativeSpinTransitionData` on the emergent cover;
* the disagreement is exhibited on a concrete vector (the intrinsic unit `sOne`), not merely
  asserted;
* and the same base still carries a compatible solder field
  (`nonempty_tangentSolderData_rescaleGluing`), so the theorem cannot be misread as
  "no solder form exists".

## 8. Stop condition (§22)

All eight questions have theorem-level answers; they are listed with their witnesses in
`TASK34_PROVENANCE.md` §2 (questions 1–7) and in `TASK34_DOCUMENTATION_REPAIR.md`
(question 8).

---

# TASK-35 CORRECTION NOTICE (2026-09-12)

Wherever this document says or implies that the solder coupling is *proved non-derivable*, or
that the Task-34 gate *closes completely*, read instead the exact statements

* **"direct/raw transition identification is not forced"**, and
* **"the fibrewise/algebraic solder gate closes; the topological/smooth solder gate remains
  open"**.

The topological/smooth gate was subsequently closed by Task 35 at the exact level recorded in
`TASK35_PROVENANCE.md` §0 (bundle equivalence with `TM`, smooth transported Lorentz metric,
topological Spin lift).  Historical wording above is unchanged.
