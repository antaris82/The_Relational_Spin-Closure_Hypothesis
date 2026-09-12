# TASK 35 — failed-build provenance

Every failed build encountered during Task 35, in chronological order, recorded when it
happened and not rewritten afterwards.  Unless stated otherwise, in **every** entry:

* theorem statement changed: **no**;
* assumptions changed: **no**;
* architecture changed: **no**.

The build command is, in all entries, of the form

```
lake build RequestProject.Spine.<Module>
```

with the module named in the entry (the final verification used `lake build RequestProject`).

---

## F1 — `Spine/Solder/RegularSolder.lean`, `pieceChart_eq_pieceCoord`

* error: `congr`-style rewrite applied in the wrong direction; the two sides of the chart
  identity were exchanged, so `rw` reported "motive is not type correct".
* diagnosis: the helper produces `chart i (pieceCoord …) = x`, the goal wanted the converse.
* repair: added `.symm` at the use site.

## F2 — `Spine/Solder/RegularSolder.lean`, `contDiffOn_A_symm`

* error: `ContDiffAt.comp` left an uninstantiated metavariable for the intermediate function.
* diagnosis: the composite goes through `ContinuousLinearMap.inverse`, which elaboration cannot
  guess from the goal.
* repair: supplied the named arguments `(g := ContinuousLinearMap.inverse)` and `(f := …)`.

## F3 — `Spine/Solder/RegularSolder.lean`, `weakFrame`

* error: `failed to synthesize Decidable (x ∈ B.chartRange i)`.
* diagnosis: the forgetful map to the Task-34 weak datum needs a value off the patch, i.e. a
  `dite` on a non-decidable membership.
* repair: `open Classical in def weakFrame`, together with the on-patch computation rule
  `weakFrame_of_mem`.  This also removed a cascade of field-notation errors downstream, since
  the on-patch value is now a lemma rather than an unfolded `dite`.

## F4 — `Spine/Solder/RegularExamples.lean`, rescaling control

* error 1: `hid z hz` applied with its arguments in the wrong order.
* error 2: `contDiffOn_const` did not match the goal
  `ContDiffOn ℝ ⊤ (fun y => ↑(rescaleSolderA i y)) (B.D i)`, because the coercion is applied
  after the (constant) function.
* repair: reordered the arguments; inserted a `show` exhibiting the map as a literal constant
  function of `y` before applying `contDiffOn_const`.

## F5 — `Spine/Solder/BundleEquivalence.lean`, six occurrences of one idiom

* error: `rw [← B.chart_outCoord x]; exact ⟨_, rfl⟩` failed — the rewrite also replaced the `x`
  occurring inside `B.outIndex x`, so the remaining goal was no longer the membership wanted.
* diagnosis: `outIndex` and `outCoord` are both functions of `x`; rewriting `x` is not
  admissible here.
* repair: proved the dedicated lemma
  `EmergentBase.BaseGluingData.mem_chartRange_outIndex : x ∈ B.chartRange (B.outIndex x)`
  once, and used it at all six sites.

## F6 — `Spine/Solder/BundleEquivalence.lean`, typo

* error: unexpected token in `∥SpinGroup`.
* repair: the subtype coercion is `↥SpinGroup`.

## F7 — `Spine/Solder/SmoothMetric.lean`

* error 1: `⟨_, rfl⟩` no longer closed a membership goal after `set x := …`.
* error 2: the proof of the transformation law ended one `rfl` short after
  `rw [… projectedLorentzTransition_BS]`.
* error 3: `by assumption` inside a packaged statement's binder had no hypothesis to find.
* repair: explicit witnesses instead of `_`; added the missing final `rfl`; gave the binder a
  name, `(hx : x ∈ B.chartRange i)`, and used it.

## F8 — `Spine/Solder/OrientationTime.lean`

* error: anonymous hypothesis notation `‹y ∈ B.W i j›` failed inside a packaged statement.
* repair: named the binder `hy` in the statement and used it.

## F9 — `Spine/Solder/WeakInsufficiency.lean`

* error 1: unknown identifier `continuous_subtype_mk`.
* repair: `Continuous.subtype_mk continuous_id _`.
* error 2: `rw` into a `ContinuousAt` goal failed (the point appears in both the function and
  the filter).
* repair: rewrote the *limit value* instead and concluded with
  `(hcont.tendsto 0).mono_left nhdsWithin_le_nhds`.

## F10 — `Spine/Comparison/SmoothSolderGate.lean`

* error: unused-variable linter warnings on binders of the packaged certificate that the proof
  term does not mention.
* repair: replaced those binders by `_` in the proof term.  The statement is unchanged.

## F11 — `Spine/Solder/RegularSolder.lean`, hygiene pass (removal of `by simp`)

* command: `lake build RequestProject.Spine.Solder.RegularSolder`
* location: `RegularSolder.lean:391:57`
* error:
  `Application type mismatch: The argument le_top has type ?m ≤ ⊤ but is expected to have type
  ↑⊤ + 1 ≤ ↑⊤`
* diagnosis: the side condition of `ContDiffOn.fderivWithin` lives in `WithTop ℕ∞`, where the
  relevant element is the *coerced* `(⊤ : ℕ∞)`, not the top element of `WithTop ℕ∞`; so
  `le_top` is not the right term.
* repair: `le_of_eq ENat.coe_top_add_one`.
* note: this replaced a `by simp` and is the reason no `simp` tactic call remains in the
  Task-35 production modules.

## F12 — `Spine/Solder/Independence.lean`, hygiene pass

* command: `lake build RequestProject.Spine.Solder.Solder RequestProject.Spine.Solder.Independence`
* location: `Independence.lean:124:8`
* error: `Unknown identifier two_ne_one`.
* diagnosis: the name is not available for `ℝ` in the pin at that position.
* repair: `exact one_ne_zero (by linarith : (1 : ℝ) = 0)` from the rewritten hypothesis
  `(2 : ℝ) • (1 : ℝ) = 1`.

---

No failed build in Task 35 was repaired by weakening a theorem, by adding a hypothesis, or by
changing the module architecture.  The single architectural change of Task 35 (§1 of the task:
`Solder.InternalLorentz` no longer imports `Emergent.TangentTransition`) was made deliberately
*before* any new mathematics, not in response to a failure, and the firewall was extended to
forbid the edge mechanically.
