import RequestProject.Spine.Deformation.ClosureAdmissibility
import RequestProject.Spine.Deformation.SmokeTestCertificate
import RequestProject.Spine.Deformation.SolderTransport
import RequestProject.Spine.Closure.IntermediateMilestone
import RequestProject.Spine.Audit.Firewall

/-!
# Task 37 / §18 : the deformation-branch firewall

This module **fails to compile** if the Task-37 deformation-preparation architecture is
violated.  Six independent mechanical checks are run.

## 1. The deformation branch is a leaf (mandatory)

No module of `RequestProject.Spine.**` outside `RequestProject.Spine.Deformation` may import,
directly or transitively, any module of the deformation branch.  In particular the frozen
Task-36 battery and the whole bottom-up construction are completely independent of it, so no
deformation object can have been used to prove a frozen theorem.

**Task-39 amendment.**  Two branches are exempt from this check, and only these two: the audit
branch `RequestProject.Spine.Audit` (which must see everything in order to audit it) and the
closure branch `RequestProject.Spine.Closure`, whose single module aggregates already certified
endpoints into the intermediate-milestone certificate.  Check 7 below requires the closure
branch to be a leaf in turn, so no production or frozen module can reach the deformation branch
through it.

## 2. The deformation branch imports only certified frozen layers (mandatory)

Its import closure is checked to contain no historical experiment tree and no inspected
external project, exactly as for the rest of the Spine.

## 3. Shared-origin firewall (mandatory, §18)

`Task37.Deformation.SharedTransportFamily` must have **exactly two** fields, `base` and
`spin`.  A third field — in particular an independently supplied Lorentz transition system —
would break the rule that the projected Lorentz datum is obtained from the Spin-side
deformation through the native projection.  Likewise
`Task37.Deformation.RegularClosureSolution` must have exactly the two fields `smoothGluing`
and `solder`: the closure solution may not carry a supplied "compatibility" field.

## 4. Anti-target-leakage token audit (mandatory, §12)

No declaration of the deformation branch may name a curvature sign, a sectional curvature, a
`kappa`, a cosmological constant, a sphere, hyperbolic space, de Sitter, anti-de Sitter,
Einstein equations, a Riemann tensor, a transport form ("connection") or a loop-transport
("holonomy") object.  The deformation parameter is a transport-side parameter and nothing
else; no target geometry may enter as an input or a branch selector.

## 5. Sensitivity controls

The deformation branch really does reach the frozen bottom-up solder layer and the frozen
Task-36 comparison endpoint; otherwise checks 1–4 would be vacuous.

## 6. Non-vacuity of the closure predicate

Recorded here as a pointer, proved in `Spine.Deformation.ClosureAdmissibility`:
`Task37.Deformation.not_forall_regularClosureAdmissible` shows that no universal existence
theorem holds, so the Task-38 question has content.
-/

open Lean Elab Command

namespace Task37Audit

/-- The deformation-preparation tree. -/
def deformationPrefix : Name := `RequestProject.Spine.Deformation

/-- The modules of the deformation branch. -/
def deformationModules : List Name :=
  [`RequestProject.Spine.Deformation.SharedTransport,
   `RequestProject.Spine.Deformation.LoopSharedTransport,
   `RequestProject.Spine.Deformation.NeutralRegression,
   `RequestProject.Spine.Deformation.ClosureAdmissibility,
   -- Task 38: the fixed-base smoke test, inside the same leaf branch
   `RequestProject.Spine.Deformation.ProjectedParaAction,
   `RequestProject.Spine.Deformation.FixedBaseSmokeTest,
   `RequestProject.Spine.Deformation.CocycleGaugeOrbit,
   `RequestProject.Spine.Deformation.TangentMetricComparison,
   `RequestProject.Spine.Deformation.SmokeTestCertificate,
   -- Task 39: the two strengthening modules, inside the same leaf branch
   `RequestProject.Spine.Deformation.SmoothProjectedGauge,
   `RequestProject.Spine.Deformation.SolderTransport]

/-- The closure branch of Task 39. -/
def closurePrefix : Name := `RequestProject.Spine.Closure

/-- The modules of the closure branch. -/
def closureModules : List Name :=
  [`RequestProject.Spine.Closure.IntermediateMilestone]

/-- Declaration-name tokens that would signal target-geometry leakage or a transport layer
that the project has not built. -/
def bannedTokens : List String :=
  ["curvature", "Curvature", "kappa", "Kappa", "cosmological", "Cosmological",
   "deSitter", "DeSitter", "AntiDeSitter", "antiDeSitter", "sphere", "Sphere",
   "hyperbolic", "Hyperbolic", "einstein", "Einstein", "Riemann",
   "holonomy", "Holonomy", "connection", "Connection"]

end Task37Audit

set_option maxRecDepth 100000 in
open SpineAudit Task37Audit in
run_cmd do
  let env ← getEnv
  let idx := moduleIndex env
  -- ============ sensitivity: the whole branch must be in scope ============
  for m in deformationModules do
    requireModule idx m
  for m in closureModules do
    requireModule idx m
  let spine := spineModules env
  if spine.length < 50 then
    throwError "AUDIT NOT SENSITIVE: only {spine.length} Spine modules are in scope"
  let deformation := spine.filter fun m => deformationPrefix.isPrefixOf m
  if deformation.length < 11 then
    throwError "AUDIT NOT SENSITIVE: only {deformation.length} deformation modules in scope"
  -- ============ 1. the deformation branch is a leaf ============
  let outside := spine.filter fun m =>
    !(deformationPrefix.isPrefixOf m) && !((`RequestProject.Spine.Audit).isPrefixOf m)
      && !(closurePrefix.isPrefixOf m)
  for m in outside do
    for x in (importClosure env idx m).toList do
      if deformationPrefix.isPrefixOf x then
        throwError "DEFORMATION FIREWALL VIOLATION: module {m} transitively imports the \
          deformation-preparation module {x}"
  logInfo m!"deformation leaf audit: {outside.length} non-deformation Spine modules checked, \
    0 of them reach {deformationPrefix}"
  -- ============ 2. only certified frozen layers ============
  for m in deformation do
    let _ ← auditNoLegacy env idx m
    auditNoExternal env idx m
  logInfo m!"deformation modules audited for legacy/external imports: {deformation.length}; \
    Experiment1 = 0, Experiment2 = 0, external projects = 0"
  -- ============ 3. shared-origin firewall: the field lists ============
  let famFields := getStructureFields env `Task37.Deformation.SharedTransportFamily
  if famFields != #[`base, `spin] then
    throwError "SHARED-ORIGIN FIREWALL VIOLATION: SharedTransportFamily has fields \
      {famFields.toList}; exactly [base, spin] are allowed, so that the projected Lorentz \
      datum stays a function of the Spin-side deformation"
  let solFields := getStructureFields env `Task37.Deformation.RegularClosureSolution
  if solFields != #[`smoothGluing, `solder] then
    throwError "CLOSURE-SOLUTION FIREWALL VIOLATION: RegularClosureSolution has fields \
      {solFields.toList}; exactly [smoothGluing, solder] are allowed, so that compatibility \
      is never a supplied field"
  logInfo m!"shared-origin firewall: SharedTransportFamily {famFields.toList}, \
    RegularClosureSolution {solFields.toList}"
  -- ============ 4. anti-target-leakage token audit ============
  let mut declCount : Nat := 0
  for m in deformation do
    match idx[m]? with
    | some i =>
      for c in (env.header.moduleData[i]!.constNames) do
        declCount := declCount + 1
        for b in bannedTokens do
          if (c.toString.splitOn b).length > 1 then
            throwError "TARGET-LEAKAGE FIREWALL: deformation module {m} declares {c}; no \
              curvature, target-geometry, field-equation, transport-form or loop-transport \
              object may be named in the deformation-preparation branch"
    | none => pure ()
  logInfo m!"deformation target-leakage audit: {declCount} declarations scanned, none names \
    a curvature sign, a target geometry, a field equation, a transport form or a \
    loop-transport object"
  -- ============ 5. sensitivity controls ============
  auditModulePositive env idx `RequestProject.Spine.Deformation.ClosureAdmissibility
    `RequestProject.Spine.Solder.RegularSolder
  auditModulePositive env idx `RequestProject.Spine.Deformation.ClosureAdmissibility
    `RequestProject.Spine.Task36.SpinObstruction
  auditModulePositive env idx `RequestProject.Spine.Deformation.SharedTransport
    `RequestProject.Spine.E1.SpinCover
  -- ============ 7. the closure branch is a leaf as well (Task 39) ============
  let closure := spine.filter fun m => closurePrefix.isPrefixOf m
  if closure.length < 1 then
    throwError "AUDIT NOT SENSITIVE: no closure module in scope"
  let outsideClosure := spine.filter fun m =>
    !(closurePrefix.isPrefixOf m) && !((`RequestProject.Spine.Audit).isPrefixOf m)
      && m != `RequestProject.Spine.Deformation.Firewall
  for m in outsideClosure do
    for x in (importClosure env idx m).toList do
      if closurePrefix.isPrefixOf x then
        throwError "CLOSURE FIREWALL VIOLATION: module {m} transitively imports the \
          closure module {x}"
  for m in closure do
    let _ ← auditNoLegacy env idx m
    auditNoExternal env idx m
  auditModulePositive env idx `RequestProject.Spine.Closure.IntermediateMilestone
    `RequestProject.Spine.Deformation.SolderTransport
  auditModulePositive env idx `RequestProject.Spine.Closure.IntermediateMilestone
    `RequestProject.Spine.Task36.Certificate
  logInfo m!"closure leaf audit: {outsideClosure.length} non-closure Spine modules checked, \
    0 of them reach {closurePrefix}; {closure.length} closure module(s) audited for \
    legacy/external imports"
