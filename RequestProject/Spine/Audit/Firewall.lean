import Lean
import Mathlib
import RequestProject.Spine.Core
import RequestProject.Spine.E1.SL2Comparison
import RequestProject.Spine.E1.Topology.Core
import RequestProject.Spine.E2.Core
import RequestProject.Spine.E2.Topology.Task27
import RequestProject.Spine.E2.Descent.Task29
import RequestProject.Spine.E2.Global.Task30
import RequestProject.Spine.E2.Defect.Task31
import RequestProject.Spine.E2.AtlasChange.Task32
import RequestProject.Spine.E2.CentralDoubleCover
import RequestProject.Spine.E2.SpinProjection
import RequestProject.Spine.E2.SpinProjectionIntegration
import RequestProject.Spine.Controls.CircleDoubleCover
import RequestProject.Spine.Controls.E2.NativeLiftControl
import RequestProject.Spine.Controls.E2.GoodBadAtlas
import RequestProject.Spine.Controls.E2.FamilyDefectControl
import RequestProject.Spine.Controls.E2.DescentCounterexample
import RequestProject.Spine.E2.Cech.Core
import RequestProject.Spine.Controls.E2.CechObstructionControl
import RequestProject.Spine.Geometry.Core
import RequestProject.Spine.Controls.Geometry.FlatFrameControl
import RequestProject.Spine.Cohomology.Core
import RequestProject.Spine.Cech.Core
import RequestProject.Spine.GoodCover.Core

/-!
# Spine / Audit : the mechanical legacy firewall and the layering audit

This module **fails to compile** if the refactored architecture is violated.  It is the
mechanical counterpart of `ARCHITECTURE.md`:

```
   production core        RequestProject.Spine.**   (minus Controls, Audit)
   native controls        RequestProject.Spine.Controls.**
   historical provenance  RequestProject.Experiment1.**, RequestProject.Experiment2.**
```

Four independent checks are run.

## 1. Zero-legacy audit (mandatory)

Every module of `RequestProject.Spine.**` present in the environment of this audit is
scanned, both for its **direct** imports and for its full **transitive** import closure, and
is required to reach no module under `RequestProject.Experiment1` or
`RequestProject.Experiment2`.  The audit is run again, separately, for each principal
endpoint (`Spine.E1.Core`, `Spine.E1.SL2Comparison`, `Spine.E2.Core`, `Spine.Core`, the five
task endpoints and the controls) and reports the required summary.

Since this audit module imports every principal endpoint, its own environment contains the
whole Spine, so the enumeration is not vacuous; `requireModule` additionally guards each
individually named module.

## 2. Controls are downstream (mandatory)

No production module may import a module of `RequestProject.Spine.Controls`.  Conversely the
controls *do* import the production layer (positive control), so the check is sensitive.

## 3. Layer-order audit

* the intrinsic experiment-1 spin core (carrier → … → `SpinKernel`) may reach neither the
  `SL(2,ℂ)` comparison layer, nor the matrix model / Pauli representation built on it, nor
  the Weyl-spinor module, nor any experiment-2 module;
* the experiment-2 foundations (`Family`, `Topology`, `CentralDoubleCover`) may not reach the
  later `Lift`, `Descent`, `Defect`, `Global` or `AtlasChange` layers.

## 4. Declaration-closure audit

For each principal endpoint the dependency closure of statement **and** proof term is
computed, expanding project constants recursively, and is required to avoid removed or
control-only constants (the historical Hermitian carrier, the old `Task9.Spin` carrier name,
the good/bad atlas of the controls).  A positive control exhibits a control theorem whose
closure *does* contain the good/bad atlas.
-/

open Lean Elab Command

namespace SpineAudit

/-! ## Generic machinery

The import graph is read off the compiled environment.  For speed the module-name → index
map is built once: a naive recomputation would rescan the whole `Mathlib` header for every
module of the Spine. -/

/-- The module-name → index map of the compiled environment. -/
def moduleIndex (env : Environment) : Std.HashMap Name Nat :=
  env.header.moduleNames.zipIdx.foldl (fun m (n, i) => m.insert n i) {}

/-- The direct imports of a module. -/
def directImports (env : Environment) (idx : Std.HashMap Name Nat) (m : Name) : List Name :=
  match idx[m]? with
  | some i => ((env.header.moduleData[i]!).imports.map (·.module)).toList
  | none => []

/-- Transitive import closure, with an explicit accumulator. -/
partial def closureAux (env : Environment) (idx : Std.HashMap Name Nat) (m : Name)
    (acc : NameSet) : NameSet :=
  if acc.contains m then acc
  else
    (directImports env idx m).foldl (fun a x => closureAux env idx x a) (acc.insert m)

/-- Transitive import closure of a module. -/
def importClosure (env : Environment) (idx : Std.HashMap Name Nat) (m : Name) : NameSet :=
  closureAux env idx m {}

/-- Guard against a vacuous audit: the audited module must actually be part of the compiled
environment, otherwise its "import closure" is the module itself and every check passes for
free. -/
def requireModule (idx : Std.HashMap Name Nat) (m : Name) : CommandElabM Unit := do
  unless idx.contains m do
    throwError "AUDIT NOT SENSITIVE: {m} is not in the environment of this audit; add an \
      import for it"

/-- The two historical trees.  No module of the new Spine may reach either of them. -/
def legacyPrefixes : List Name :=
  [`RequestProject.Experiment1, `RequestProject.Experiment2]

/-- Root namespaces of the **external Lean projects** that were inspected as scholarly
references for Task 5 (`TASK05_EXTERNAL_SOURCES.md`).  No module of the Spine may reach any of
them: the external work is documentation/provenance only, never a dependency. -/
def externalProjectPrefixes : List Name :=
  [`SKEFTHawking, `SKEFT, `MathPhysics, `JanusFormal, `Janus, `GQ2, `Gq2]

/-- All modules of the new Spine present in this environment. -/
def spineModules (env : Environment) : List Name :=
  env.header.moduleNames.toList.filter (fun m => (`RequestProject.Spine).isPrefixOf m)

/-- Production modules: the Spine minus the controls and minus this audit. -/
def productionModules (env : Environment) : List Name :=
  (spineModules env).filter fun m =>
    !((`RequestProject.Spine.Controls).isPrefixOf m) &&
      !((`RequestProject.Spine.Audit).isPrefixOf m)

/-- Number of modules under the prefix `p` in a given closure. -/
def countUnder (cl : NameSet) (p : Name) : Nat :=
  (cl.toList.filter fun x => p.isPrefixOf x).length

/-- **Mandatory zero-legacy audit** for one module: neither a direct import nor any module of
the transitive closure may lie under a historical experiment tree.  Returns the pair
(direct legacy imports, transitive legacy imports), which is `(0, 0)` whenever it succeeds. -/
def auditNoLegacy (env : Environment) (idx : Std.HashMap Name Nat) (m : Name) :
    CommandElabM (Nat × Nat) := do
  requireModule idx m
  let cl := importClosure env idx m
  for p in legacyPrefixes do
    for x in directImports env idx m do
      if p.isPrefixOf x then
        throwError "LEGACY FIREWALL VIOLATION (direct): {m} imports {x}"
    for x in cl.toList do
      if p.isPrefixOf x then
        throwError "LEGACY FIREWALL VIOLATION (transitive): {m} transitively imports {x}"
  return (0, 0)

/-- **Mandatory external-isolation audit**: no module of the transitive closure may belong to
an inspected external project. -/
def auditNoExternal (env : Environment) (idx : Std.HashMap Name Nat) (m : Name) :
    CommandElabM Unit := do
  requireModule idx m
  for x in (importClosure env idx m).toList do
    for p in externalProjectPrefixes do
      if p.isPrefixOf x then
        throwError "EXTERNAL-PROJECT IMPORT: {m} transitively imports {x}"

/-- The report required of every principal endpoint. -/
def reportEndpoint (env : Environment) (idx : Std.HashMap Name Nat) (m : Name) :
    CommandElabM Unit := do
  let _ ← auditNoLegacy env idx m
  let cl := importClosure env idx m
  let proj := countUnder cl `RequestProject
  let direct := (directImports env idx m).filter fun x => (`RequestProject).isPrefixOf x
  logInfo m!"endpoint {m}: direct project-local imports {direct.length}, project-local \
    closure {proj}, direct legacy imports E1 = 0, E2 = 0, transitive legacy imports \
    E1 = {countUnder cl `RequestProject.Experiment1}, \
    E2 = {countUnder cl `RequestProject.Experiment2}"

/-- No production module may import a control. -/
def auditNoControls (env : Environment) (idx : Std.HashMap Name Nat) (m : Name) :
    CommandElabM Unit := do
  requireModule idx m
  for x in (importClosure env idx m).toList do
    if (`RequestProject.Spine.Controls).isPrefixOf x then
      throwError "DEPENDENCY-DIRECTION VIOLATION: production module {m} imports control {x}"

/-- A forbidden-prefix audit for one module. -/
def auditForbidden (env : Environment) (idx : Std.HashMap Name Nat) (label : String)
    (m : Name) (ps : List Name) : CommandElabM Unit := do
  requireModule idx m
  for x in (importClosure env idx m).toList do
    for p in ps do
      if p.isPrefixOf x then
        throwError "LAYERING VIOLATION ({label}): {m} transitively imports {x}"

/-- Positive control: the given module *must* reach the given one. -/
def auditModulePositive (env : Environment) (idx : Std.HashMap Name Nat) (m needed : Name) :
    CommandElabM Unit := do
  requireModule idx m
  if (importClosure env idx m).contains needed then
    logInfo m!"control OK: {m} does import {needed} (audit is sensitive)"
  else
    throwError "AUDIT NOT SENSITIVE: {m} does not import {needed}"

/-- Level 1b — the prefixes the **intrinsic experiment-1 spin core** must never reach. -/
def forbiddenIntrinsicSpin : List Name :=
  [`RequestProject.Experiment1, `RequestProject.Experiment2, `RequestProject.Spine.Controls,
   `RequestProject.Spine.E2, `RequestProject.Spine.E1.SL2Comparison,
   `RequestProject.Spine.E1.MatrixModel, `RequestProject.Spine.E1.PauliRepresentation,
   `RequestProject.Spine.E1.WeylSpinorModule]

/-- The prefixes the **experiment-2 foundations** must never reach: the whole later
lift/descent/defect/global/atlas machinery. -/
def forbiddenE2Foundations : List Name :=
  [`RequestProject.Experiment1, `RequestProject.Experiment2, `RequestProject.Spine.Controls,
   `RequestProject.Spine.E2.Lift, `RequestProject.Spine.E2.Descent,
   `RequestProject.Spine.E2.Defect, `RequestProject.Spine.E2.Global,
   `RequestProject.Spine.E2.AtlasChange]

/-! ## Declaration-closure audit -/

/-- Constants belonging to this project, expanded recursively by the closure audit. -/
def isProjectConst (c : Name) : Bool :=
  [`SpinCore, `CechSpinLift, `NullSectorTask26, `NullSectorTask27, `NullSectorTask28, `NullSectorTask29,
    `NullSectorTask30, `NullSectorTask31, `NullSectorTask32, `Task11, `Task10, `Task9,
    `Task8, `Task7, `Task6, `Carrier, `Herm2, `Mink4, `SpinLorentz, `Lorentz, `Task15,
    `MetricOrientedRankThreeFamily, `MetricOrientedFibreAtlas, `GoodBad, `LorentzFrames,
    `Examples, `Counterexample, `SpineControls, `SpineTop, `Mod2Cohomology,
    `CechZ2, `CechSpinZ2, `CechSingularSpec, `NerveZ2, `NerveGeom, `GoodCoverZ2, `GoodCoverSpec].any (fun p => p.isPrefixOf c)

/-- Project-transitive, Mathlib-shallow dependency closure of statement and proof. -/
partial def collectDeps (env : Environment) (n : Name) (acc : NameSet) : NameSet :=
  if acc.contains n then acc
  else
    let acc := acc.insert n
    match env.find? n with
    | some ci =>
        let cs := ci.type.getUsedConstants ++ (ci.value?.map Expr.getUsedConstants).getD #[]
        cs.foldl (fun a c => if isProjectConst c then collectDeps env c a else a.insert c) acc
    | none => acc

/-- Constants that must not occur in the closure of a production endpoint. -/
def forbiddenConsts : List Name :=
  [`Task9.Spin, `Task9.toHerm, `Task9.sJ, `Herm2.Herm, `Herm2.hermCoordEquiv,
   `Task8.Nintr, `Task8.ConeJ, `Task8.JordanConeAut, `Task8.reflY,
   `Task10.spinHermConj, `Task10.det_sq_of_GLorWide, `Task10.spatialRefl_det,
   `Task15.diracOp, `NullSectorTask32.GoodBad.badAtlas,
   `NullSectorTask32.GoodBad.trivialAtlas, `SpineControls.circleDoubleCover,
   `SpineControls.trivialDoubleCover]

def auditProof (env : Environment) (target : Name) : CommandElabM Unit := do
  let deps := collectDeps env target {}
  for b in forbiddenConsts do
    if deps.contains b then
      throwError "PROOF-CLOSURE LEAKAGE: {target} depends on {b}"
  logInfo m!"proof-closure OK: {target} (closure {deps.size}) avoids \
    {forbiddenConsts.length} removed/control-only constants"

def auditProofPositive (env : Environment) (target needed : Name) : CommandElabM Unit := do
  let deps := collectDeps env target {}
  if deps.contains needed then
    logInfo m!"control OK: {target} does depend on {needed} (audit is sensitive)"
  else
    throwError "AUDIT NOT SENSITIVE: {target} does not depend on {needed}"

end SpineAudit

set_option maxRecDepth 100000 in
open SpineAudit in
run_cmd do
  let env ← getEnv
  let idx := moduleIndex env
  -- ============ 1. the mandatory zero-legacy audit over the whole Spine ============
  let spine := spineModules env
  if spine.length < 50 then
    throwError "AUDIT NOT SENSITIVE: only {spine.length} Spine modules are in scope"
  for m in spine do
    let _ ← auditNoLegacy env idx m
    auditNoExternal env idx m
  logInfo m!"Spine external-project imports: 0 (prefixes checked: \
    {externalProjectPrefixes.length})"
  logInfo m!"Spine modules audited: {spine.length}\n\
    Spine direct legacy imports:\nExperiment1 = 0\nExperiment2 = 0\n\
    Spine transitive legacy imports:\nExperiment1 = 0\nExperiment2 = 0"
  -- ============ the same audit, endpoint by endpoint ============
  for m in [`RequestProject.Spine.Core, `RequestProject.Spine.E1.Core,
            `RequestProject.Spine.E1.SL2Comparison,
            `RequestProject.Spine.E1.Topology.Core, `RequestProject.Spine.E2.Core,
            `RequestProject.Spine.E2.SpinProjection,
            `RequestProject.Spine.E2.SpinProjectionIntegration,
            `RequestProject.Spine.E2.Topology.Task27,
            `RequestProject.Spine.E2.Descent.Task29, `RequestProject.Spine.E2.Global.Task30,
            `RequestProject.Spine.E2.Defect.Task31,
            `RequestProject.Spine.E2.AtlasChange.Task32,
            `RequestProject.Spine.E2.Cech.Core,
            `RequestProject.Spine.E2.Cech.SpinInstance,
            `RequestProject.Spine.Controls.CircleDoubleCover,
            `RequestProject.Spine.Controls.E2.CechObstructionControl,
            `RequestProject.Spine.Controls.E2.NativeLiftControl,
            `RequestProject.Spine.Controls.E2.GoodBadAtlas,
            `RequestProject.Spine.Controls.E2.FamilyDefectControl,
            `RequestProject.Spine.Controls.E2.DescentCounterexample,
            `RequestProject.Spine.Geometry.Core,
            `RequestProject.Spine.Geometry.FrameField,
            `RequestProject.Spine.Geometry.SpinStructure,
            `RequestProject.Spine.Geometry.TangentInstance,
            `RequestProject.Spine.Geometry.Z2Class,
            `RequestProject.Spine.Controls.Geometry.FlatFrameControl,
            `RequestProject.Spine.Cohomology.Core,
            `RequestProject.Spine.Cohomology.Cochain,
            `RequestProject.Spine.Cohomology.Coboundary,
            `RequestProject.Spine.Cohomology.Cohomology,
            `RequestProject.Spine.Cohomology.Functorial,
            `RequestProject.Spine.Cohomology.Cup,
            `RequestProject.Spine.Cohomology.CupDescent,
            `RequestProject.Spine.Cohomology.CechBridgeSpec,
            `RequestProject.Spine.Cech.Core,
            `RequestProject.Spine.Cech.Cochain,
            `RequestProject.Spine.Cech.Coboundary,
            `RequestProject.Spine.Cech.Cohomology,
            `RequestProject.Spine.Cech.Refinement,
            `RequestProject.Spine.Cech.CoverNerve,
            `RequestProject.Spine.Cech.KernelSign,
            `RequestProject.Spine.Cech.SpinKernelSign,
            `RequestProject.Spine.Cech.SpinCocycle,
            `RequestProject.Spine.Cech.Comparison,
            `RequestProject.Spine.Cech.SpinInstance,
            `RequestProject.Spine.Cech.SingularBridgeSpec,
            `RequestProject.Spine.GoodCover.Core,
            `RequestProject.Spine.GoodCover.Presimplicial,
            `RequestProject.Spine.GoodCover.NerveIdentification,
            `RequestProject.Spine.GoodCover.GoodCover,
            `RequestProject.Spine.GoodCover.PointCohomology,
            `RequestProject.Spine.GoodCover.AcyclicCover,
            `RequestProject.Spine.GoodCover.ManifoldCovers,
            `RequestProject.Spine.GoodCover.Constancy,
            `RequestProject.Spine.GoodCover.SingularComparisonSpec,
            `RequestProject.Spine.GoodCover.W2Interface,
            `RequestProject.Spine.Nerve.Core,
            `RequestProject.Spine.Nerve.Basic.Cover,
            `RequestProject.Spine.Nerve.Cochain.CochainComparison,
            `RequestProject.Spine.Nerve.Basic.Realization,
            `RequestProject.Spine.Nerve.Basic.ChainMap,
            `RequestProject.Spine.Nerve.Cochain.CochainMap,
            `RequestProject.Spine.Nerve.Cochain.ComparisonSpec] do
    reportEndpoint env idx m
  -- ============ 2. production never imports controls ============
  for m in productionModules env do
    auditNoControls env idx m
  auditModulePositive env idx `RequestProject.Spine.Controls.E2.NativeLiftControl
    `RequestProject.Spine.E2.Defect.DefectNeutrality
  auditModulePositive env idx `RequestProject.Spine.Controls.E2.FamilyDefectControl
    `RequestProject.Spine.Controls.E2.GoodBadAtlas
  auditModulePositive env idx `RequestProject.Spine.Controls.Geometry.FlatFrameControl
    `RequestProject.Spine.Geometry.TangentInstance
  -- ============ 3. layer order ============
  for m in [`RequestProject.Spine.E1.Carrier, `RequestProject.Spine.E1.Clifford,
            `RequestProject.Spine.E1.LorentzClifford,
            `RequestProject.Spine.E1.CliffordMonomial, `RequestProject.Spine.E1.SpinElement,
            `RequestProject.Spine.E1.SpinGroup, `RequestProject.Spine.E1.Paravector,
            `RequestProject.Spine.E1.SpinDeterminant, `RequestProject.Spine.E1.DoubleCover,
            `RequestProject.Spine.E1.SpinCover, `RequestProject.Spine.E1.SpinKernel,
            `RequestProject.Spine.E1.Topology.FiniteDimTools,
            `RequestProject.Spine.E1.Topology.CliffordTopology,
            `RequestProject.Spine.E1.Topology.LorentzTopology,
            `RequestProject.Spine.E1.Topology.SpinTopology,
            `RequestProject.Spine.E1.Topology.SpinCoverTopology,
            `RequestProject.Spine.E1.Topology.LocalSection,
            `RequestProject.Spine.E1.Topology.Core] do
    auditForbidden env idx "intrinsic spin core" m forbiddenIntrinsicSpin
  -- the native spin projection is downstream of the intrinsic core and of the generic
  -- interface, and reaches neither a control nor a historical experiment module
  auditModulePositive env idx `RequestProject.Spine.E2.SpinProjection
    `RequestProject.Spine.E1.Topology.LocalSection
  auditModulePositive env idx `RequestProject.Spine.E2.SpinProjection
    `RequestProject.Spine.E2.CentralDoubleCover
  auditForbidden env idx "native spin projection" `RequestProject.Spine.E2.SpinProjection
    [`RequestProject.Experiment1, `RequestProject.Experiment2,
     `RequestProject.Spine.Controls, `RequestProject.Spine.E1.SL2Comparison,
     `RequestProject.Spine.E1.MatrixModel, `RequestProject.Spine.E1.PauliRepresentation]
  auditModulePositive env idx `RequestProject.Spine.E1.SL2Comparison
    `RequestProject.Spine.E1.SpinKernel
  -- the Task-3 Čech layer: generic part free of the concrete projection, concrete part
  -- downstream of the native projection only
  auditForbidden env idx "Cech generic layer" `RequestProject.Spine.E2.Cech.Refinement
    [`RequestProject.Experiment1, `RequestProject.Experiment2,
     `RequestProject.Spine.Controls, `RequestProject.Spine.E1.SL2Comparison,
     `RequestProject.Spine.E1.MatrixModel, `RequestProject.Spine.E1.PauliRepresentation,
     `RequestProject.Spine.E2.SpinProjection]
  auditModulePositive env idx `RequestProject.Spine.E2.Cech.SpinInstance
    `RequestProject.Spine.E2.SpinProjection
  auditModulePositive env idx `RequestProject.Spine.E2.Cech.SpinInstance
    `RequestProject.Spine.E2.Cech.Refinement
  auditForbidden env idx "Cech spin instantiation" `RequestProject.Spine.E2.Cech.SpinInstance
    [`RequestProject.Experiment1, `RequestProject.Experiment2,
     `RequestProject.Spine.Controls, `RequestProject.Spine.E1.SL2Comparison,
     `RequestProject.Spine.E1.MatrixModel, `RequestProject.Spine.E1.PauliRepresentation]
  -- the Task-4 geometry layer: downstream of the Task-3 Čech layer and of the native spin
  -- projection, upstream of nothing, and free of every historical or control module
  auditModulePositive env idx `RequestProject.Spine.Geometry.SpinStructure
    `RequestProject.Spine.E2.Cech.SpinInstance
  auditModulePositive env idx `RequestProject.Spine.Geometry.FrameField
    `RequestProject.Spine.E2.Cech.Cover
  for m in [`RequestProject.Spine.Geometry.CausalAlgebra,
            `RequestProject.Spine.Geometry.FrameField,
            `RequestProject.Spine.Geometry.SpinStructure,
            `RequestProject.Spine.Geometry.TangentInstance,
            `RequestProject.Spine.Geometry.Z2Class,
            `RequestProject.Spine.Geometry.Core] do
    auditForbidden env idx "Task-4 geometry layer" m
      [`RequestProject.Experiment1, `RequestProject.Experiment2,
       `RequestProject.Spine.Controls, `RequestProject.Spine.E1.SL2Comparison,
       `RequestProject.Spine.E1.MatrixModel, `RequestProject.Spine.E1.PauliRepresentation]
  -- the Task-5 cohomology layer: built on Mathlib only.  Every module except the bridge
  -- specification is independent of the whole Čech/geometry machinery, and none of them
  -- reaches a historical experiment tree, a control, or an external project.
  for m in [`RequestProject.Spine.Cohomology.Cochain,
            `RequestProject.Spine.Cohomology.Coboundary,
            `RequestProject.Spine.Cohomology.Cohomology,
            `RequestProject.Spine.Cohomology.Functorial,
            `RequestProject.Spine.Cohomology.AlexanderWhitney,
            `RequestProject.Spine.Cohomology.Cup,
            `RequestProject.Spine.Cohomology.CupDescent] do
    auditForbidden env idx "Task-5 cohomology layer" m
      [`RequestProject.Experiment1, `RequestProject.Experiment2,
       `RequestProject.Spine.Controls, `RequestProject.Spine.E1,
       `RequestProject.Spine.E2, `RequestProject.Spine.Geometry]
  -- the Task-6 fixed-cover Čech layer.  Its Spin-independent half must not reach the Spin,
  -- lift, geometry or control layers at all: the Čech complex exists on its own.
  for m in [`RequestProject.Spine.Cech.Cochain,
            `RequestProject.Spine.Cech.Coboundary,
            `RequestProject.Spine.Cech.Cohomology,
            `RequestProject.Spine.Cech.Refinement] do
    auditForbidden env idx "Task-6 Cech layer (Spin-independent half)" m
      [`RequestProject.Experiment1, `RequestProject.Experiment2,
       `RequestProject.Spine.Controls, `RequestProject.Spine.E1, `RequestProject.Spine.E2,
       `RequestProject.Spine.Geometry, `RequestProject.Spine.Cohomology]
  auditModulePositive env idx `RequestProject.Spine.Cech.SpinCocycle
    `RequestProject.Spine.E2.Cech.Core
  auditModulePositive env idx `RequestProject.Spine.Cech.SpinCocycle
    `RequestProject.Spine.Cech.Cohomology
  auditModulePositive env idx `RequestProject.Spine.Cech.SpinInstance
    `RequestProject.Spine.Cech.SpinKernelSign
  auditModulePositive env idx `RequestProject.Spine.Cech.SingularBridgeSpec
    `RequestProject.Spine.Cohomology.Core
  for m in [`RequestProject.Spine.Cech.CoverNerve,
            `RequestProject.Spine.Cech.KernelSign,
            `RequestProject.Spine.Cech.SpinKernelSign,
            `RequestProject.Spine.Cech.SpinCocycle,
            `RequestProject.Spine.Cech.Comparison,
            `RequestProject.Spine.Cech.SpinInstance,
            `RequestProject.Spine.Cech.SingularBridgeSpec,
            `RequestProject.Spine.Cech.Core] do
    auditForbidden env idx "Task-6 Cech layer" m
      [`RequestProject.Experiment1, `RequestProject.Experiment2,
       `RequestProject.Spine.Controls]
  -- the Task-7 good-cover layer.  Its cover-side half is Spin-independent and geometry-free:
  -- the abstract presimplicial complex reaches nothing of the project at all, and the
  -- good-cover / nerve-identification modules reach only the Spin-independent Čech complex.
  auditForbidden env idx "Task-7 presimplicial layer"
    `RequestProject.Spine.GoodCover.Presimplicial
    [`RequestProject.Experiment1, `RequestProject.Experiment2,
     `RequestProject.Spine.Controls, `RequestProject.Spine.E1, `RequestProject.Spine.E2,
     `RequestProject.Spine.Geometry, `RequestProject.Spine.Cohomology,
     `RequestProject.Spine.Cech]
  for m in [`RequestProject.Spine.GoodCover.GoodCover,
            `RequestProject.Spine.GoodCover.NerveIdentification] do
    auditForbidden env idx "Task-7 cover layer (Spin-independent half)" m
      [`RequestProject.Experiment1, `RequestProject.Experiment2,
       `RequestProject.Spine.Controls, `RequestProject.Spine.E1, `RequestProject.Spine.E2,
       `RequestProject.Spine.Geometry, `RequestProject.Spine.Cohomology]
  auditForbidden env idx "Task-7 point-cohomology computation"
    `RequestProject.Spine.GoodCover.PointCohomology
    [`RequestProject.Experiment1, `RequestProject.Experiment2,
     `RequestProject.Spine.Controls, `RequestProject.Spine.E1, `RequestProject.Spine.E2,
     `RequestProject.Spine.Geometry, `RequestProject.Spine.Cech]
  auditModulePositive env idx `RequestProject.Spine.GoodCover.NerveIdentification
    `RequestProject.Spine.Cech.Cohomology
  auditModulePositive env idx `RequestProject.Spine.GoodCover.Constancy
    `RequestProject.Spine.Cech.SpinInstance
  auditModulePositive env idx `RequestProject.Spine.GoodCover.SingularComparisonSpec
    `RequestProject.Spine.Cohomology.Core
  for m in [`RequestProject.Spine.GoodCover.AcyclicCover,
            `RequestProject.Spine.GoodCover.ManifoldCovers,
            `RequestProject.Spine.GoodCover.Constancy,
            `RequestProject.Spine.GoodCover.SingularComparisonSpec,
            `RequestProject.Spine.GoodCover.W2Interface,
            `RequestProject.Spine.GoodCover.Core] do
    auditForbidden env idx "Task-7 good-cover layer" m
      [`RequestProject.Experiment1, `RequestProject.Experiment2,
       `RequestProject.Spine.Controls]
  -- the Task-9 nerve/realization layer.  Its purely simplicial half (the full simplicial
  -- cover nerve and the identification with the Task-6 cochain complex) must not reach the
  -- Spin, lift, geometry or singular-cohomology layers at all.
  for m in [`RequestProject.Spine.Nerve.Basic.Cover,
            `RequestProject.Spine.Nerve.Cochain.CochainComparison] do
    auditForbidden env idx "Task-9 simplicial nerve layer" m
      [`RequestProject.Experiment1, `RequestProject.Experiment2,
       `RequestProject.Spine.Controls, `RequestProject.Spine.E1, `RequestProject.Spine.E2,
       `RequestProject.Spine.Geometry, `RequestProject.Spine.Cohomology]
  auditModulePositive env idx `RequestProject.Spine.Nerve.Basic.Realization
    `RequestProject.Spine.Cohomology.Cohomology
  auditModulePositive env idx `RequestProject.Spine.Nerve.Cochain.CochainMap
    `RequestProject.Spine.Nerve.Basic.Realization
  auditModulePositive env idx `RequestProject.Spine.Nerve.Cochain.ComparisonSpec
    `RequestProject.Spine.GoodCover.HardenedSpec
  for m in [`RequestProject.Spine.Nerve.Basic.Realization,
            `RequestProject.Spine.Nerve.Basic.ChainMap,
            `RequestProject.Spine.Nerve.Cochain.CochainMap,
            `RequestProject.Spine.Nerve.Cochain.ComparisonSpec,
            `RequestProject.Spine.Nerve.Core] do
    auditForbidden env idx "Task-9 nerve layer" m
      [`RequestProject.Experiment1, `RequestProject.Experiment2,
       `RequestProject.Spine.Controls]
  auditModulePositive env idx `RequestProject.Spine.Cohomology.CechBridgeSpec
    `RequestProject.Spine.E2.Cech.Obstruction
  auditForbidden env idx "Task-5 bridge specification"
    `RequestProject.Spine.Cohomology.CechBridgeSpec
    [`RequestProject.Experiment1, `RequestProject.Experiment2,
     `RequestProject.Spine.Controls]
  for m in [`RequestProject.Spine.E2.Family.TransitionData,
            `RequestProject.Spine.E2.CentralDoubleCover,
            `RequestProject.Spine.E2.Topology.Task27] do
    auditForbidden env idx "E2 foundations" m forbiddenE2Foundations
  auditModulePositive env idx `RequestProject.Spine.E2.Lift.TransitionLiftBase
    `RequestProject.Spine.E2.Topology.Task27
  auditModulePositive env idx `RequestProject.Spine.E2.Defect.Task31
    `RequestProject.Spine.E2.Descent.Task29
  -- ============ 4. declaration closure of the principal endpoints ============
  auditProofPositive env `NullSectorTask32.task32_closure `NullSectorTask32.GoodBad.badAtlas
  auditProof env `SpinCore.lorentz_quadratic_form
  auditProof env `SpinCore.mem_lorentz_group_iff
  auditProof env `SpinCore.clifford_generator_square
  auditProof env `SpinCore.paravector_norm
  auditProof env `SpinCore.spin_double_cover_of_lorentz
  auditProof env `SpinCore.spin_double_cover_bundled
  auditProof env `SpinCore.spin_double_cover
  auditProof env `SpinCore.spin_double_cover_topological
  auditProof env `SpinCore.spin_double_cover_topological_endpoint
  auditProof env `SpinCore.spinCover_hasLocalSection
  auditProof env `SpinCore.intrinsic_spin_cover_local_two_sheets
  auditProof env `SpinCore.spin_double_cover_local_sections
  auditProof env `SpinCore.internalSpinProjection
  auditProof env `SpinCore.intrinsic_spin_internal_projection
  auditProof env `SpinCore.spin_levelB
  auditProof env `SpinCore.weyl_clifford_module
  auditProof env `SpinCore.sl2_comparison
  auditProof env `NullSectorTask31.internalLiftable_iff_globalKernelDefect_neutral
  auditProof env `NullSectorTask31.tautSystem_not_internalLiftable
  auditProof env `NullSectorTask32.familyLiftable_iff_familyKernelDefectNeutral
  auditProof env `NullSectorTask32.task32_verdictC_classification
  auditProof env `NullSectorTask28.InternalProjection
  auditProof env `CechSpinLift.SpinLiftFamily.spinLiftObstruction_defect
  auditProof env `CechSpinLift.SpinLiftFamily.defect_change_of_lift
  auditProof env `CechSpinLift.SpinLiftFamily.obstruction_lift_independent
  auditProof env `CechSpinLift.SpinLiftFamily.obstruction_eq_trivialClass_iff_exists_coherent
  auditProof env `CechSpinLift.SpinLiftFamily.obstruction_pullLift
  auditProof env `CechSpinLift.SpinLiftFamily.obstruction_pullLift_indep_of_map
  auditProof env `SpinCore.isGLor_of_isometry_of_future_of_det_pos
  auditProof env `LorentzFrames.LorentzFrameData.comparison_mem_GLor
  auditProof env `LorentzFrames.LorentzFrameData.frameCocycle
  auditProof env `LorentzFrames.LorentzFrameData.frameObstruction_eq_trivial_iff_spinStructure
  auditProof env `LorentzFrames.tangent_frame_cocycle
  auditProof env `LorentzFrames.tangent_frame_spin_lift_obstruction
  auditProof env `LorentzFrames.zdefect_isCoboundary_iff_spinStructure
  auditProof env `SpinCore.cech_defect_eq_pm_one
  auditProof env `SpinCore.spinLiftObstruction
  auditProof env `Mod2Cohomology.coboundary_coboundary
  auditProof env `Mod2Cohomology.d_comp_d
  auditProof env `Mod2Cohomology.coboundaries_le_cocycles
  auditProof env `Mod2Cohomology.Cohomology
  auditProof env `Mod2Cohomology.pullback_d
  auditProof env `Mod2Cohomology.Hmap_id
  auditProof env `Mod2Cohomology.Hmap_comp
  auditProof env `Mod2Cohomology.prismK_identity
  auditProof env `Mod2Cohomology.prismK_identity_zero
  auditProof env `Mod2Cohomology.Hmap_eq_of_homotopic
  auditProof env `Mod2Cohomology.homotopyEquivCohomology
  auditProof env `Mod2Cohomology.cohomology_succ_eq_zero_of_contractible
  auditProof env `GoodCoverZ2.isAcyclicCover_of_isGoodCover
  auditProof env `GoodCoverSpec.nativeHomotopyInvariance
  auditProof env `GoodCoverSpec.HardenedComparison.equiv
  auditProof env `Mod2Cohomology.coboundary_cup
  auditProof env `Mod2Cohomology.cup_cocycle
  auditProof env `Mod2Cohomology.cupH11
  auditProof env `Mod2Cohomology.cupH22
  auditProof env `Mod2Cohomology.comparison_vanishing_iff_exists_coherent
  auditProof env `CechZ2.coboundary_coboundary
  auditProof env `CechZ2.d_comp_d
  auditProof env `CechZ2.coboundaries_le_cocycles
  auditProof env `CechZ2.Cohomology
  auditProof env `CechZ2.Hmap
  auditProof env `CechZ2.Hmap_comp
  auditProof env `CechSpinZ2.spinKernelSign
  auditProof env `CechSpinZ2.d_zCochain
  auditProof env `CechSpinZ2.zCochain_change_of_lift
  auditProof env `CechSpinZ2.spinCechClass_lift_independent
  auditProof env `CechSpinZ2.spinCechClass_eq_zero_iff_exists_coherent
  auditProof env `CechSpinZ2.toObstruction_spinCechClass
  auditProof env `CechSpinZ2.toObstruction_injective
  auditProof env `CechSpinZ2.classOf_not_mem_range_toObstruction
  auditProof env `CechSpinZ2.Hmap_spinCechClass
  auditProof env `CechSpinZ2.spinCechClass_pull_indep_of_map
  auditProof env `CechSpinZ2.frameCechClass_eq_zero_iff_spinStructure
  auditProof env `NerveGeom.coverNerveSSet
  auditProof env `NerveGeom.face_face_comm
  auditProof env `NerveGeom.degen_degen_comm
  auditProof env `NerveGeom.underlyingPresimplicial_coverNerveSSet
  auditProof env `NerveGeom.isDegenerate_iff_exists_degen
  auditProof env `NerveGeom.coverNerveRealization
  auditProof env `NerveGeom.charSimplex
  auditProof env `NerveGeom.charSimplex_face
  auditProof env `NerveGeom.charSimplex_degen
  auditProof env `NerveGeom.charSimplex_universal
  auditProof env `NerveGeom.chainMap_comm
  auditProof env `NerveGeom.geometricCochainMap
  auditProof env `NerveGeom.geometricHmap
  auditProof env `NerveGeom.canonicalNervePresentation
  auditProof env `NerveGeom.spinLiftRealizedClass_eq_zero_iff
  auditProof env `NerveGeom.frameRealizedClass_eq_zero_iff_spinStructure
  logInfo "SPINE FIREWALL AUDIT: all checks passed"
