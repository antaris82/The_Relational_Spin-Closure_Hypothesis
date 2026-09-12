# Refactoring audit: extraction of the spin-reconstruction proof spine

This is the record of the refactor.  It is mechanical where possible: every claim below is
either a build result, a `grep` over the tree, or a number computed from the `import`
graph.  No mathematical statement was strengthened; where a statement had to change at all,
the change is listed in §4.

## 1. What was done

1. **Experiment-1 intrinsic core extracted** into `RequestProject/Spine/E1/` (namespace
   `SpinCore`, carrier `SpinCore.LorentzCarrier`).  The legacy import coupling through
   `Task9Freeze` — and hence through the Hermitian Jordan-carrier layer — is gone: the
   carrier module imports `Mathlib` only.
2. **The Hermitian route became a comparison endpoint** (`RequestProject/Comparison/E1Hermitian.lean`).
   It imports the intrinsic core and the retained historical layer and proves the two agree;
   nothing in production imports it.
3. **The algebraic Clifford-module / Weyl-spinor material was extracted** from the upstream
   Task-15 spinor branch into `RequestProject/Spine/E1/WeylSpinorModule.lean`, whose closure
   is 3 modules and contains no Maxwell, gauge-field, quantization, mass-selection or
   positive-frequency material, and no historical verdict.
4. **Experiment-2 serial chain broken.**  The Task-26 varying-family core is separated from
   the Task-25 one-fibre comparison endpoint (which became
   `RequestProject/Comparison/E2OneFibreComparison.lean` and `…/E2Task26Endpoint.lean`); the
   topology layer imports the family core directly.
5. **Generic central double-cover / transition-lift layer extracted** into
   `RequestProject/Spine/E2/CentralDoubleCover.lean` (`Mathlib` only).  The concrete
   instantiation at the frame model was separated into `RequestProject/Spine/E2/Model/`.
6. **Good/bad atlas made a negative control** (`RequestProject/Control/E2/GoodBadAtlas.lean`,
   `…/FamilyDefectControl.lean`); production modules no longer import it, and the
   presentation-level versus family-level distinction is preserved (§4).
7. **Import firewalls made mechanical** (`RequestProject/Spine/Audit/Firewall.lean`).
8. **195 modules removed** from the active tree, each recorded in `PROVENANCE_LEDGER.md`.

## 2. Build results

| Build | Result |
| --- | --- |
| `lake build RequestProject.Spine.E1.SL2Comparison` | `Build completed successfully (8044 jobs)` |
| `lake build RequestProject.Spine.E1.Core` | `Build completed successfully (8045 jobs)` |
| `lake build RequestProject.Spine.Audit.Firewall` (dedicated firewall build) | `Build completed successfully (8340 jobs)`, audit reports `SPINE FIREWALL AUDIT: all checks passed` |
| `lake build` (whole tree, final) | **`Build completed successfully (8345 jobs)`, 0 errors** |

The final full build includes the two comparison endpoints and all three negative-control
modules, so the control builds are green as part of it.

### Axiom audit

The developments emit `#print axioms` on their endpoints: 678 axiom reports in the final
build, each reporting either `[propext, Classical.choice, Quot.sound]` or `[propext]`, and
nothing else.

### Prohibited constructs

`grep` over `RequestProject/**.lean` finds no `sorry`, no `admit`, no `axiom` declaration,
no `@[implemented_by]`, no `native_decide`, no `bv_decide`.  (The word "admit" occurs in
five English sentences inside doc comments.)

## 3. Failed builds, diagnosis and repair

Every build failure encountered during the refactor is recorded here.

| # | Failure | Diagnosis | Repair | Mathematical content affected |
| --- | --- | --- | --- | --- |
| 1 | `RequestProject/Spine/E1/MatrixModel.lean`: `Tactic 'simp' failed … maximum recursion depth` in `center_eq_complexScalars`, and `unsolved goals … ring failed` in `hMat_sq` | new, hand-written replacements for two facts the upstream took from the Hermitian Jordan layer.  In `hMat_sq` the full simp set rewrote `(↑X)^2` into `↑(X^2)` and left goals about `.re`/`.im`; in the centre proof the wrong matrix entries of the two commutators were extracted, so `simp` looped on the remaining goal | added `-Complex.ofReal_pow` to the simp set and closed the residual conjunctions with `refine ⟨?_, ?_⟩ <;> ring`; extracted entry `(0,1)` of both commutators, giving `C 0 0 = C 1 1`, `C 0 1 = 0`, `C 1 0 = 0` | none: both statements are new proofs of the same facts, and the audit shows the core no longer reaches the Hermitian layer |
| 2 | `RequestProject/Spine/E2/CentralDoubleCover.lean:97: unexpected token 'namespace'; expected 'lemma'` | a `/-- … -/` *doc* comment was placed before a `namespace` command in the newly split module | changed it to a `/-! … -/` section comment | none (comment only) |
| 3 | `RequestProject/Spine/E2/Model/CertifiedProjection.lean: unknown namespace 'NullSectorTask01' …` (and follow-on elaboration errors) | severing the Task-25 chain from the topology layer also removed, from this module's environment, the historical certified-projection data (`LiftG`, `GvisG`, `projCore`, `KerSign`, `Vset`, `sec`) that the *concrete instantiation* legitimately needs — it had been reaching them transitively | separated the model instantiation into `RequestProject/Spine/E2/Model/` and gave it an explicit import of `RequestProject.Experiment2.NullSectorTask23.Task23`; introduced the two-level firewall (generic modules: no historical layer at all; model-instantiated modules: the certified-projection chain only, never a comparison endpoint or control) | none: no statement changed; the dependency became explicit instead of transitive |
| 4 | `RequestProject/Spine/Audit/Firewall.lean:162: AUDIT NOT SENSITIVE: NullSectorTask32.task32_closure does not depend on GoodBad.badAtlas` | the audit's own positive control used the short name `GoodBad.badAtlas`; the declaration is `NullSectorTask32.GoodBad.badAtlas` | used fully qualified names in the control list and in the forbidden-constant list | none: this failure was the audit correctly refusing to certify itself as sensitive |

An additional weakness found by inspection rather than by a failure: `auditModelModule`
silently passed for `Spine.E2.Defect.Task31` because that module was not imported by the
audit, so its "import closure" was the singleton.  A `requireModule` guard was added — the
audit now fails if an audited module is absent from its own environment — and the missing
imports were added.

## 4. Statement-level changes

Only two statements in the whole tree differ from their upstream form, both because a
production module had to stop depending on the negative control:

| Production statement | Upstream statement | Relation |
| --- | --- | --- |
| `NullSectorTask32.task32_verdictC_classification` (in `Spine/E2/AtlasChange/FamilyExistenceClassification.lean`) | `NullSectorTask32.task32_verdictC_content` | the production version keeps the first conjunct (the exact family-level classification, for every bare family of the class) and drops the four good/bad atlas conjuncts.  The **full** upstream statement is preserved verbatim, under its original name, in `Control/E2/FamilyDefectControl.lean` |
| the Task-32 endpoint module no longer states `task32_closure` | `NullSectorTask32.task32_closure` | preserved verbatim in `Control/E2/FamilyDefectControl.lean` |

Everything else — including `familyLiftable_iff_familyKernelDefectNeutral`,
`badFamilyBase_familyKernelDefectNeutral` and
`presentationLevel_nonNeutral_with_familyLevel_neutral` — is unchanged; the last two simply
live in the control module now.  In the experiment-1 core the only change is the systematic
rename of the carrier (`Task9.Spin` → `SpinCore.LorentzCarrier`) and of the three task
namespaces into `SpinCore`; the Hermitian comparison sections of the upstream carrier module
were moved, not altered.

## 5. Firewall audit, as executed

`RequestProject/Spine/Audit/Firewall.lean` runs, in this order:

1. five **positive controls** — two comparison endpoints that do reach the historical layer,
   one control module that does reach the good/bad atlas, one comparison theorem whose proof
   closure does contain `Herm2.Herm`, and one control theorem whose proof closure does
   contain `NullSectorTask32.GoodBad.badAtlas`.  If any of them stopped firing, the audit
   fails as "not sensitive";
2. **level-1 import firewall** on twelve generic production modules (all of `Spine.E1`, and
   `Spine.E2.Family`, `Spine.E2.Topology`, `Spine.E2.CentralDoubleCover`, the generic
   `Spine.E2.Lift` modules): none may reach `Experiment1`, `Experiment2`, `Comparison` or
   `Control`;
3. **level-2 import firewall** on seven model-instantiated production modules: none may
   reach `Experiment1`, `Comparison`, `Control`, or the Task-24/Task-25 one-fibre chain;
4. **declaration-closure audit** on ten principal endpoints: the closure of statement *and*
   proof must avoid fifteen removed or comparison-only constants, among them `Task9.Spin`,
   `Task9.toHerm`, `Herm2.Herm`, `Task8.JordanConeAut`, `Task10.det_sq_of_GLorWide`,
   `Task15.diracOp`, `NullSectorTask32.GoodBad.badAtlas`.

All checks pass; the final message is `SPINE FIREWALL AUDIT: all checks passed`.

## 6. Stopping point

The extraction is complete and verified.  Nothing was attempted beyond it: there is no `w₁`,
no `w₂`, no Lorentzian spin structure, no spinor bundle over a manifold and no spin
connection in this tree, and no project defect is identified with a Stiefel–Whitney class.

## Refactoring task 02 (intrinsic Spin double-cover extraction)

The failed builds and repairs of the second refactoring pass are recorded in
`SPIN_CORE_EXTRACTION_AUDIT.md`, §8, together with the provenance mapping for the moved
declarations, the level-1b import firewall, the before/after dependency statistics, the
axiom audit and the `InternalProjection` interface table.


---

## Refactoring task 03 — complete legacy decoupling (this pass)

The concrete experiment-2 projection (`Spine/E2/Model/CertifiedProjection.lean`, importing
`Experiment2.NullSectorTask23.Task23`) was the last arrow from the new code into the
historical trees.  It has been removed, together with `ModelBridge.modelInternalProjection`
and every inherited specialization built on it; the E2 theory is now parameterized by an
internal projection `P`, non-vacuity is witnessed by a native circle double cover, the
controls were rebuilt under `Spine/Controls/**`, and the legacy-facing comparison modules
were deleted.

The record of that pass — provenance table, mechanical import audit, before/after
statistics, axiom audit, the failed builds with diagnosis and repair, and the isolated clean
build with both historical trees removed — is in `LEGACY_DECOUPLING_AUDIT.md`.
