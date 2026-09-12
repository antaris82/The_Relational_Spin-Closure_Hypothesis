# TASK 25 FAILBUILD PROVENANCE

Every failed compilation encountered while bringing the Task-25 refactor (chronological
`TaskNN` modules → content-based layout, plus import narrowing) to a green build, with the exact
Lean error, the diagnosis, the repair, and whether a theorem *statement* changed. No failed
route is silently discarded.

Both failures below are of the same kind: an `import` that the automatic narrowing removed
although the module genuinely needs it, because the needed name is not detected by the
name-mention heuristic of `scripts/min_imports.py`. In both cases Lean's symptom is the same and
is characteristic: the missing name is auto-bound as an implicit variable, so the first
diagnostic is *"invalid use of explicit universe parameters, `X` is a local variable"* rather
than *"unknown identifier"*.

**No theorem statement, proof term or tactic script was changed in this task.** The only edits
were `import` lines.

---

## F1 — the standard-cell excision module lost the definition of the standard pair

* **Module**: `RequestProject/Spine/Nerve/StandardCell/Excision.lean` (pre-refactor
  `Spine/Nerve/Task23StandardCellExcision.lean`).
* **Error** (from `lake build RequestProject`, 15 errors in this one file):
  ```
  error: RequestProject/Spine/Nerve/StandardCell/Excision.lean:78:4:
    invalid use of explicit universe parameters, `stdCellPair` is a local variable
  error: RequestProject/Spine/Nerve/StandardCell/Excision.lean:80:74: unsolved goals
  error: RequestProject/Spine/Nerve/StandardCell/Excision.lean:92:43:
    invalid use of explicit universe parameters, `stdPairMap` is a local variable
  error: RequestProject/Spine/Nerve/StandardCell/Excision.lean:93:62: Unknown identifier `r`
  error: RequestProject/Spine/Nerve/StandardCell/Excision.lean:101:11:
    Unknown identifier `isIso_homologyMap_stdPair`
  error: RequestProject/Spine/Nerve/StandardCell/Excision.lean:124:34:
    Unknown identifier `stdPairIso`
  ```
* **Diagnosis**: the file uses `SpineTask14.stdCellPair`, which the refactor split out into the
  new definition module `RequestProject.Spine.Nerve.StandardCell.Pair`. Its two imports
  (`Nerve.CellFamily.ExcisionCompatibility`, `Nerve.Geometry.OpenStandardCell`) do not reach
  that module, so `stdCellPair` was auto-bound as an implicit variable in `square_stdPair`;
  every later declaration that mentions `stdCellPair`, `stdPairMap` or `stdPairIso` then failed
  in cascade. The name-mention heuristic had proposed the edge, but it was lost when the
  cell-pair definition was moved to its own module after that computation.
* **Repair**: add `import RequestProject.Spine.Nerve.StandardCell.Pair`. This is the definition
  module only — it does not re-introduce any proof stack, and the mechanical check §3.4 of
  `TASK25_ARCHITECTURE_AUDIT.md` (which forbids `CellFamily.TargetMap` from reaching
  `StandardCell.Excision`) still passes.
* **Statement changed**: no. One import line; the file's Lean code is untouched.

---

## F2 — proposed narrowing rejected: `SingularHomotopy` really does need `SingularHomology`

* **Module**: `RequestProject/Spine/AlgebraicTopology/SingularHomotopy.lean`.
* **Route taken**: `scripts/min_imports.py --apply` proposed dropping
  `RequestProject.Spine.AlgebraicTopology.SingularHomology` from its imports. Applying it and
  rebuilding gives
  ```
  error: RequestProject/Spine/AlgebraicTopology/SingularHomotopy.lean:30:36:
    invalid use of explicit universe parameters, `Cx` is a local variable
  warning: RequestProject/Spine/AlgebraicTopology/SingularHomotopy.lean:33:8:
    declaration uses `sorry`
  error: RequestProject/Spine/AlgebraicTopology/SingularHomotopy.lean:59:60: unsolved goals
  X Y Z : TopCat
  f : X ⟶ Y
  g : Y ⟶ Z
  q : ℕ
  ⊢ HomologicalComplex.homologyMap sorry q =
      HomologicalComplex.homologyMap (singCxMap f) q ≫ HomologicalComplex.homologyMap (singCxMap g) q
  ```
* **Diagnosis**: the module needs the abbreviation `Cx` (`ChainComplex (ModuleCat (ZMod 2)) ℕ`,
  `AlgebraicTopology/SingularHomology.lean:34`), which is the codomain of its very first
  declaration `abbrev singCxFunctor : TopCat ⥤ Cx`. `scripts/min_imports.py`
  ignores identifiers whose last component is shorter than five characters (`MIN_LEN = 5`),
  because short suffixes are almost always Mathlib names; `Cx` falls below that cutoff, so the
  edge looked unjustified. With the import gone, `Cx` is auto-bound as an implicit variable in
  `abbrev singCxFunctor`, whose body then elaborates to `sorry` and poisons the two theorems
  below it.
* **Repair**: the proposed removal was reverted — the import is genuine mathematical dependency
  and stays. `scripts/min_imports.py` still reports this single difference; it is a known
  false positive of the heuristic, not an outstanding narrowing.
* **Statement changed**: no. The file is byte-identical to its pre-narrowing state.

---

## Outcome

After F1's repair and F2's reversion, `lake build RequestProject` from a deleted `.lake/build`
reports **"Build completed successfully (8275 jobs)"** with 0 errors, the legacy firewall and
the new `Spine/Audit/ArchitectureDAG.lean` audit both pass, and the axiom table is identical to
the pre-refactor baseline. No other compilation failure occurred in this task; the four import
removals listed in §4 of `TASK25_ARCHITECTURE_AUDIT.md` all built green on the first attempt.
