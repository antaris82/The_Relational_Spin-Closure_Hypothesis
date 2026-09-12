# Task 30 — Failed builds and rejected routes

All compilations were run at the frozen pin (Lean 4.28.0, Mathlib `8f9d9cff…`).

## 1. Name collision with an inherited Stage-1.2 theorem

* **Command.** `lake build RequestProject.Spine.Comparison.SpinNativeVsSO`
* **Error.**

  ```
  error: RequestProject/Spine/Comparison/SpinNativeVsSO.lean:162:8:
  `SpinCore.spinCover_negOneSpin_mul` has already been declared
  ```

* **Diagnosis.**  The draft comparison module restated the information-loss fact
  `ρ(−u) = ρ(u)` in the `SpinCore` namespace.  That theorem already exists, proved in Stage
  1.2: `SpinCore.spinCover_negOneSpin_mul`, `RequestProject/Spine/E1/Topology/LocalSection.lean:506`.
  The failure is therefore a *useful* one: it enforced the task rule "do not reprove the
  kernel theory already certified in Stage 1.2".
* **Repair.**  The duplicate was deleted.  In its place,
  `SpinCore.proj_ker_mul_eq_spinCover_negOneSpin_mul` records, in one statement, that the new
  generic lemma `SpinNative.proj_ker_mul` specializes to the inherited theorem, and cites it.
* **Did a mathematical statement change?**  No.  The information-loss content is unchanged;
  only the location and name of one restatement.

No other compilation of the new modules failed.

## 2. Routes considered and rejected before coding (audit of §3 of the task)

These were rejected on the evidence of the source, not after a failed build; they are
recorded because rejecting them is part of the provenance result.

* **A new `structure NativeSpinTransitionData` with its own fields.**  Rejected: it would
  duplicate `CechSpinLift.VisibleCocycle`, which is already stated for an arbitrary
  topological group and never mentions the projection.  The task explicitly forbids
  duplicating an existing mathematical object under a new name.  An `abbrev` is used instead.
* **Reusing `LorentzFrames.SpinFrameStructure` as the Spin-native object.**  Rejected: its
  field `projects` refers to `Φ.transition`, i.e. it presupposes prior `SO`-transition data,
  which is exactly what the Spin-native branch must not require.  It is used instead as the
  *source* of the comparison arrow `SpinFrameStructure.toNative`, which forgets that field.
* **Reusing `NullSectorTask29.CompatibleContinuousInternalTransitions`.**  Rejected for the
  same reason (its field `proj_v` refers to the ordinary transition system `S.g`), and
  additionally because it lives above the descent layer, so importing it into a low-level
  Spin-native module would create precisely the downward dependency Outcome E warns about.
* **A global (not overlap-restricted) form of `project_twist`.**  Rejected as *false as
  stated*: `KerCocycle₁.isKer` constrains `ε` only on the double overlaps, so off the
  overlaps `ρ(ε_ij(x)·s_ij(x))` need not equal `ρ(s_ij(x))`, and the two projected cocycles
  need not be equal as functions.  The theorem is therefore stated pointwise on the overlaps
  — the strongest correct form in the current representation — and the docstring says so.
* **Extending Task 30 to an H¹-classification of Spin structures.**  Not attempted: it is an
  explicit non-goal (§6, §10), and nothing in the delivered statements claims it.
