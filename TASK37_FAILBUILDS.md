# TASK 37 — fail-build ledger

Every failed build attempt of this task, in order, with command, location, error, diagnosis and
repair.  Nothing is overwritten after success.  Scratch-elaboration failures (single snippets
checked before being written into a module) are recorded too, marked *scratch*.

---

## F1 — *scratch* — `Basis` does not resolve

* **command**: scratch elaboration of the replacement determinant lemma against
  `import RequestProject.Spine.Solder.RegularSolder`
* **location**: candidate body of `Task36.continuous_det_localModel`
* **error**: `Unknown identifier 'Basis'`, `Unknown identifier 'Basis.ofEquivFun'`
* **diagnosis**: in the pinned Mathlib the bundled basis type is `Module.Basis`, not `Basis`.
* **repair**: use `Module.Basis` and `Module.Basis.ofEquivFun`.
* theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

## F2 — *scratch* — `smul_eq_mul` does not apply to an `ℝ`-action on `Cl3`

* **command**: scratch elaboration of the paravector product lemma
* **location**: `paravector_mul`, subproof `h4`
* **error**: `rewrite failed: did not find an occurrence of ?a • ?b` in `(b * b) • 1 = …`
* **diagnosis**: `smul_eq_mul` is for a monoid acting on itself; here the scalar action is the
  `ℝ`-module structure of the Clifford algebra.
* **repair**: close the goal with `(Algebra.algebraMap_eq_smul_one _).symm`.
* statement/assumptions/architecture changed? **NO / NO / NO**

## F3 — *scratch* — wrong orientation of a commuted product

* **command**: scratch elaboration of `paravector_mul`
* **error**: `did not find an occurrence of the pattern c * b`
* **diagnosis**: after `Algebra.commutes` the scalars appear in the other order.
* **repair**: drop the superfluous `mul_comm` rewrite; the normal form already matched.
* statement/assumptions/architecture changed? **NO / NO / NO**

## F4 — `lake build RequestProject.Spine.Deformation.SharedTransport` (three errors)

* **command**: `lake build RequestProject.Spine.Deformation.SharedTransport`
* **locations and errors**:
  1. `SharedTransport.lean:140` — `rewrite failed: did not find an occurrence of
     -sinh (l/2) * cosh (l/2) + cosh (l/2) * sinh (l/2)`;
  2. `SharedTransport.lean:172` — `No goals to be solved` inside `transportState_add`;
  3. `SharedTransport.lean:242` — `Dependent elimination failed: Failed to solve equation
     G.1 p = F.1 p`.
* **diagnosis**:
  1. the auxiliary identity `hcross'` was stated with the two summands in the wrong order for
     the goal produced by `paravector_mul`;
  2. `congr 1` had already discharged one of the two component goals, so the second bullet had
     no goal left;
  3. `cases` on an equality of *base gluing data* cannot be performed when the second field's
     type depends on it — the `HEq` formulation of the shared-origin congruence was not
     provable this way.
* **repair**:
  1. state `hcross'` in the order the goal presents;
  2. replace the `congr` block by explicit `mul_comm` / `add_comm` rewrites;
  3. replace the `HEq` congruence by two statements that are both exactly what §18 needs:
     `projectedLorentz_eq` (the projected datum *is* the projection of the Spin field, by
     definition) and `fixedBase_projectedLorentz_determined` (over a frozen base, equal Spin
     fields give equal projected data).
* theorem statement changed? **YES for item 3** — a *new* module of this task, not a frozen
  one: the unprovable `HEq` congruence was replaced, before it was ever built, by two provable
  statements of the same firewall content.  No Task-36 statement was touched.
* assumptions changed? **NO** — architecture changed? **NO**

## F5 — `lake build RequestProject.Spine.Deformation.NeutralRegression`

* **command**: `lake build RequestProject.Spine.Deformation.NeutralRegression`
* **location**: `NeutralRegression.lean:125`
* **error**: `Type mismatch: loopGluingOf_smoothGluing has type ∀ (κ) [DecidableEq κ] (t),
  (loopGluingOf κ t).SmoothGluing but is expected to have type
  ((loopTransportFamily κ).base 0).SmoothGluing`
* **diagnosis**: the frozen lemma takes the label type and the wrap involution explicitly;
  they cannot be inferred through the family projection.
* **repair**: supply them: `loopGluingOf_smoothGluing κ LoopTwist.id'`.
* statement/assumptions/architecture changed? **NO / NO / NO**

## F6 — no further failures

The refactored Task-36 tree (`lake build RequestProject.Spine.Task36.Firewall`), the deformed
loop cocycle module, the closure-admissibility module, the deformation firewall and the full
`lake build RequestProject` all compiled at the first attempt after the repairs above.

One *architecture* change was required and is recorded here explicitly:

* **A1** — `RequestProject/Spine/Task36/Firewall.lean`, check 1 ("Task 36 is a leaf") now
  excludes the prefix `RequestProject.Spine.Deformation`.  Reason: the Task-37 deformation
  branch is a *consumer* of the frozen Task-36 layer by design.  The exemption is not a
  weakening: the deformation branch is itself audited to be a leaf, with the same check, in
  `RequestProject/Spine/Deformation/Firewall.lean` (201 non-deformation Spine modules
  checked, 0 reach it).
  theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed?
  **YES**, as described.
