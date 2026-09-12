import RequestProject.Spine.Task36.SpinObstruction
import RequestProject.Spine.Task36.Certificate
import RequestProject.Spine.Task36.GaugeGroup
import RequestProject.Spine.Task36.SpinFoamControl
import RequestProject.Spine.Task36.SmoothBundlePackaging
import RequestProject.Spine.Task36.OrientationReversing
import RequestProject.Spine.Task36.LoopSpinFreedom
import RequestProject.Spine.Task36.LoopTimeOrientation
import RequestProject.Spine.Audit.Firewall

/-!
# Task 36 / §21 : the adversarial import firewall

This module **fails to compile** if the Task-36 architecture is violated.  It is the
mechanical counterpart of the §21 requirement.

The allowed architecture is

```
    frozen bottom-up branch  (Spine.SpinNative.**, Spine.Emergent.**, Spine.Solder.**)
              \
               →  Spine.Task36.**          (adversarial / comparison layer)
              /
    top-down obstruction branch (Spine.Geometry.**, Spine.Cech.**, Spine.E2.Cech.Obstruction,
                                 Spine.Comparison.**)
```

and the forbidden shape is any reverse dependency

```
    bottom-up production module  →  Spine.Task36.**  →  top-down w₁/w₂ branch.
```

Five independent mechanical checks are run, reusing the generic import-graph machinery of
`SpineAudit` (`RequestProject.Spine.Audit.Firewall`).

## 1. Task 36 is a leaf (mandatory)

No module of `RequestProject.Spine.**` outside `RequestProject.Spine.Task36` may import,
directly or transitively, any module of `RequestProject.Spine.Task36`.  In particular the
frozen bottom-up construction is completely independent of this adversarial battery, so no
adversarial example can have been used to prove a bottom-up theorem.

## 2. The bottom-up adversarial modules do not touch the top-down branch (mandatory)

Every Task-36 module *except* the explicitly declared comparison module
`Spine.Task36.SpinObstruction` (and this audit) must avoid the whole top-down obstruction
branch.  Hence the orientation gate, the loop/Möbius models, the loop Spin-freedom family,
the time-orientation reduction, the one-chart control and the smooth bundle-packaging
certificate are all proved using nothing but the frozen bottom-up construction.

## 3. The comparison module really is a comparison (sensitivity control)

`Spine.Task36.SpinObstruction` must reach **both** branches: the bottom-up solder
(`Spine.Solder.RegularSolder`) and the top-down Čech obstruction
(`Spine.E2.Cech.Obstruction`).  Without this positive control check 2 would be vacuous.

## 4. Curvature claim firewall (§15)

At this stage the project has **no** connection or curvature structure.  The audit therefore
requires that no module of `RequestProject.Spine.**` declares any object whose name asserts
curvature, holonomy, a connection or a Riemann tensor, so that no such property can be
inferred from base gluing data, noncontractible fundamental loops, Spin kernel signs or
regular soldering.  Curvature is deferred to the later connection stage.

## 5. Zero-legacy and zero-external audit for the Task-36 tree

The mandatory project-wide audit of `Spine.Audit.Firewall` is re-run on every Task-36
module: none of them may reach `RequestProject.Experiment1`, `RequestProject.Experiment2`
or any inspected external project.
-/

open Lean Elab Command

namespace Task36Audit

/-- The Task-36 tree. -/
def task36Prefix : Name := `RequestProject.Spine.Task36

/-- The top-down obstruction branch: the classical `w₁`/`w₂`-style Čech machinery, the
manifold/`Geometry` Spin-structure layer and the comparison layer built on them. -/
def topDownPrefixes : List Name :=
  [`RequestProject.Spine.E2.Cech.Obstruction, `RequestProject.Spine.Geometry,
   `RequestProject.Spine.Cech, `RequestProject.Spine.Cohomology,
   `RequestProject.Spine.GoodCover, `RequestProject.Spine.Comparison]

/-- The Task-36 modules that are **not** allowed to see the top-down branch: everything
except the declared comparison module and this audit. -/
def bottomUpTask36 : List Name :=
  [`RequestProject.Spine.Task36.LoopModel,
   `RequestProject.Spine.Task36.OrientationGate,
   `RequestProject.Spine.Task36.OrientationReversing,
   `RequestProject.Spine.Task36.LoopSolder,
   `RequestProject.Spine.Task36.LoopSpinFreedom,
   `RequestProject.Spine.Task36.TimeOrientation,
   `RequestProject.Spine.Task36.LoopTimeOrientation,
   `RequestProject.Spine.Task36.TrivialControl,
   `RequestProject.Spine.Task36.SmoothBundlePackaging,
   `RequestProject.Spine.Task36.GaugeGroup,
   `RequestProject.Spine.Task36.SpinNotLorentz,
   `RequestProject.Spine.Task36.SpinFoamControl]

end Task36Audit

set_option maxRecDepth 100000 in
open SpineAudit Task36Audit in
run_cmd do
  let env ← getEnv
  let idx := moduleIndex env
  -- ============ sensitivity: the whole Task-36 tree must be in scope ============
  for m in bottomUpTask36 do
    requireModule idx m
  requireModule idx `RequestProject.Spine.Task36.SpinObstruction
  requireModule idx `RequestProject.Spine.Task36.Certificate
  let spine := spineModules env
  if spine.length < 50 then
    throwError "AUDIT NOT SENSITIVE: only {spine.length} Spine modules are in scope"
  let task36 := spine.filter fun m => task36Prefix.isPrefixOf m
  if task36.length < 14 then
    throwError "AUDIT NOT SENSITIVE: only {task36.length} Task-36 modules are in scope"
  -- ============ 1. Task 36 is a leaf of the Spine ============
  -- The Task-37 deformation-preparation branch `Spine.Deformation` is a *consumer* of the
  -- frozen Task-36 layer by design, and is itself audited to be a leaf in
  -- `RequestProject.Spine.Deformation.Firewall`; it is therefore excluded here.
  let outside := spine.filter fun m =>
    !(task36Prefix.isPrefixOf m) && !((`RequestProject.Spine.Audit).isPrefixOf m) &&
      !((`RequestProject.Spine.Deformation).isPrefixOf m)
  for m in outside do
    for x in (importClosure env idx m).toList do
      if task36Prefix.isPrefixOf x then
        throwError "TASK-36 FIREWALL VIOLATION: production module {m} transitively \
          imports the adversarial module {x}"
  logInfo m!"Task-36 leaf audit: {outside.length} non-Task-36 Spine modules checked, \
    0 of them reach {task36Prefix}"
  -- ============ 2. bottom-up adversarial modules avoid the top-down branch ============
  for m in bottomUpTask36 do
    auditForbidden env idx "Task-36 bottom-up branch" m topDownPrefixes
  logInfo m!"Task-36 branch audit: {bottomUpTask36.length} bottom-up adversarial modules \
    reach none of the {topDownPrefixes.length} top-down obstruction prefixes"
  -- ============ 3. the comparison module reaches both branches ============
  auditModulePositive env idx `RequestProject.Spine.Task36.SpinObstruction
    `RequestProject.Spine.Solder.RegularSolder
  auditModulePositive env idx `RequestProject.Spine.Task36.SpinObstruction
    `RequestProject.Spine.E2.Cech.Obstruction
  -- ============ 5. §15 curvature claim firewall ============
  -- No module of the Spine may *declare* an object whose name asserts curvature, holonomy,
  -- a connection or a Riemann tensor: at this stage of the project there is no connection
  -- structure, so no such statement may be inferred from base gluing data, noncontractible
  -- loops, Spin holonomy signs or regular soldering.  Curvature is deferred to the later
  -- connection stage (see `TASK36_AUDIT.md` §15).
  let banned : List String :=
    ["curvature", "Curvature", "Riemann", "holonomy", "Holonomy", "connection", "Connection"]
  let mut declCount : Nat := 0
  for m in spine do
    match idx[m]? with
    | some i =>
      for c in (env.header.moduleData[i]!.constNames) do
        declCount := declCount + 1
        for b in banned do
          if (c.toString.splitOn b).length > 1 then
            throwError "CURVATURE CLAIM FIREWALL: module {m} declares {c}; no curvature, \
              holonomy or connection object may exist at this stage of the project"
    | none => pure ()
  logInfo m!"curvature claim firewall: {declCount} Spine declarations scanned, none names \
    curvature, holonomy, a connection or a Riemann tensor"
  -- ============ 4. zero-legacy / zero-external for the Task-36 tree ============
  for m in task36 do
    let _ ← auditNoLegacy env idx m
    auditNoExternal env idx m
  logInfo m!"Task-36 modules audited for legacy/external imports: {task36.length}; \
    Experiment1 = 0, Experiment2 = 0, external projects = 0"
