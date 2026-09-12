# TASK 38 — failed-build ledger (append-only)

Every failed build encountered while producing the Task-38 fixed-base smoke test, recorded at
the moment it happened.  Nothing is erased after success.

For each entry: exact command, exact source location, exact Lean error (abbreviated to its
first line where the error text is long), diagnosis, repair, and the three impact questions.

---

## F1

* **Command** `lake build RequestProject.Spine.Deformation.ProjectedParaAction`
* **Location** `RequestProject/Spine/Deformation/ProjectedParaAction.lean:105` (`cle_zero_anticomm`)
* **Error** `Tactic 'rewrite' failed: Did not find an occurrence of the pattern cle 2 * cle 0 in
  the target expression cle 0 * cle ((fun i => i) ⟨2, ⋯⟩) = -(cle ((fun i => i) ⟨2, ⋯⟩) * cle 0)`
* **Diagnosis** `fin_cases k` leaves the index in the unreduced form `(fun i => i) ⟨2, _⟩`, which
  does not match the frozen anticommutation lemmas `t10`, `t20` syntactically.
* **Repair** first derive `k = 0 ∨ k = 1 ∨ k = 2` (by `fin_cases k <;> decide`) and then
  `rcases`, so the index is a literal before the rewrite.
* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

## F2

* **Command** as F1
* **Location** `ProjectedParaAction.lean:130` (`transportElem_mul_cle`)
* **Error** `Tactic 'rewrite' failed: Did not find an occurrence of the pattern ?a - -?b`
* **Diagnosis** after `smul_neg` the goal is `A + -(s • B) = A - s • B`, an additive identity,
  not an instance of `sub_neg_eq_add`.
* **Repair** close with `abel`.
* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

## F3

* **Command** as F1
* **Location** `ProjectedParaAction.lean:172` (`projectedTransportState_apply`)
* **Error** `Tactic 'rewrite' failed: Did not find an occurrence of the pattern (?a + ?b) * ?c`
* **Diagnosis** the conjugated product `g * (X + Y) * g` needs `mul_add` *before* `add_mul`; the
  single rewrite chain distributed in the wrong order.
* **Repair** introduce a named intermediate computation `hR` for
  `transportElem l * spinToCl x * transportElem l`, distributing with explicit
  `show … from by rw [mul_add, add_mul]` steps, and rewrite with it at the end.
* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

## F4

* **Command** as F1
* **Location** `ProjectedParaAction.lean:225` (`paraEquiv_zero`)
* **Error** `Application type mismatch … but is expected to have type
  ⇑(paraEquiv 0) = ⇑(ContinuousLinearEquiv.refl ℝ LocalModel)`
* **Diagnosis** `ContinuousLinearEquiv.ext` consumes an equality of the coercions, not a
  pointwise family.
* **Repair** `ContinuousLinearEquiv.ext (funext fun x => …)`.
* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

## F5

* **Command** `lake build RequestProject.Spine.Deformation.FixedBaseSmokeTest`
* **Location** `FixedBaseSmokeTest.lean:177` (`mem_wrapSet_of_slab45`)
* **Error** `Type mismatch: hmem has type unwrap LoopTwist.id' y ∈ slab 0 1 but is expected to
  have type ⟨φ …, ⋯⟩ ∈ {y | ↑y ∈ slab 0 1}`
* **Diagnosis** the membership was being built by hand against the set-builder form of
  `Task36.wrapSet`, with the wrong subtype packaging.
* **Repair** reuse the already-proved `mem_wrapSet_of_slab01` at the transported coordinate.
* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

## F6

* **Command** as F5
* **Location** `FixedBaseSmokeTest.lean:192` (`notMem_wrapSet_of_slab23'`)
* **Error** `Tactic 'rewrite' failed: motive is not type correct`
* **Diagnosis** rewriting the coordinate inside a term whose *subtype proof* depends on it.
* **Repair** reuse `notMem_wrapSet_of_slab23` instead of rewriting under the dependency.
* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

## F7

* **Command** as F5
* **Location** `FixedBaseSmokeTest.lean:269` (`loopParaSolder`, `contDiffOn_A`, first patch)
* **Error** `typeclass instance problem is stuck: NormedSpace ?m ?m`
* **Diagnosis** the comparison field on the first patch is *definitionally* constant but not
  syntactically so, so `contDiffOn_const` could not determine its target space.
* **Repair** state the constant form with `show` before applying `contDiffOn_const` (and
  likewise the interpolated form on the second patch).
* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

## F8

* **Command** as F5
* **Location** `FixedBaseSmokeTest.lean:173–174` (`mem_wrapSet_of_slab45`)
* **Error** `Tactic 'rewrite' failed: Did not find an occurrence of the pattern (unwrap ?t ?y).1
  in the target expression 0 < (fun x => x.1) (unwrap LoopTwist.id' y)`
* **Diagnosis** `slab` membership unfolds through a preimage, presenting the coordinate as an
  applied lambda.
* **Repair** name the coordinate equation (`hfst`) and build the membership through
  `Task36.mem_slab`.
* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

## F9

* **Command** `lake build RequestProject.Spine.Deformation.CocycleGaugeOrbit`
* **Location** `CocycleGaugeOrbit.lean:106`
* **Error** `Function expected at InternalProjection but this term has type ?m`
* **Diagnosis** the namespace carrying `InternalProjection` was not opened in the new module.
* **Repair** add `NullSectorTask28` to the `open` list, matching the frozen source modules.
* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

## F10

* **Command** as F9
* **Location** `CocycleGaugeOrbit.lean:194` (`continuousOn_loopGaugeFun`)
* **Error** `typeclass instance problem is stuck: TopologicalSpace ?m`
* **Diagnosis** composing with `continuous_transportState` before the intermediate real-valued
  map was fixed left its type as a metavariable.
* **Repair** prove the real-valued `ContinuousOn` statement as a named `have`, then compose.
* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

## F11

* **Command** as F9
* **Location** `CocycleGaugeOrbit.lean:198`
* **Error** `typeclass instance problem is stuck: TopologicalSpace ?m`
* **Diagnosis** same cause as F7 on the first patch of the gauge field.
* **Repair** `show` the constant form before `continuousOn_const`.
* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed? **NO**

---

## Recorded configuration change (not a failure)

`RequestProject/Spine/Deformation/Firewall.lean` was extended: the audited module list now
contains the five Task-38 modules and the sensitivity threshold was raised from 4 to 9
deformation modules.  No check was weakened, no exemption was added, and the leaf, import,
field-list and token audits were all re-run and pass.

* Theorem statement changed? **NO** — assumptions changed? **NO** — architecture changed?
  **YES (audit configuration only: more modules are audited, no check relaxed)**
