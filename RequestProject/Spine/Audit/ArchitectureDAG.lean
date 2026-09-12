import RequestProject.Spine.Audit.Firewall
import RequestProject.Spine.Nerve.Audit.Stage13Axioms
import RequestProject.Spine.Comparison.SpinNativeVsSO
import RequestProject.Spine.Comparison.KernelTwistCohomology
import RequestProject.Spine.Comparison.LorentzSpinUniqueness
import RequestProject.Spine.Comparison.CanonicalSpinSeed
import RequestProject.Spine.Controls.SpinNative.KernelTwistControl
import RequestProject.Spine.Comparison.EmergentSpinGate
import RequestProject.Spine.Emergent.SmoothGate
import RequestProject.Spine.Emergent.SymmetricSmooth
import RequestProject.Spine.Emergent.LocalPieceData
import RequestProject.Spine.Emergent.TangentTransition
import RequestProject.Spine.Solder.LorentzBundle
import RequestProject.Spine.Comparison.SolderTangentGate
import RequestProject.Spine.Comparison.SmoothSolderGate

/-!
# Spine / Audit : the mathematical-DAG firewall

This module **fails to compile** if the Stage-1.3 import graph reacquires a chronological
(rather than mathematical) shape.  It is the mechanical counterpart of
`TASK25_ARCHITECTURE_AUDIT.md` and encodes the architecture rule

> a production module may import another module only for a genuine mathematical definition or
> theorem dependency; historical task order is not an import dependency; generic results
> belong below domain-specific results; independent branches stay independent until their
> first necessary join; lightweight definitions must not require their heavy proof stacks.

Six checks are run, all of them on the *compiled* import graph (the generic machinery is
reused from `RequestProject.Spine.Audit.Firewall`).

1. **No historical modules.**  No production module of the Stage-1.3 area
   (`RequestProject.Spine.AlgebraicTopology`, `RequestProject.Spine.Nerve`) is a `TaskNN…`
   module: the chronological layer has been removed, not wrapped.  (The `E1`/`E2` halves of
   the Spine keep their own historical names; they are outside this refactor.)
2. **Generic results are below the Nerve.**  No module of
   `RequestProject.Spine.AlgebraicTopology` may reach a module of
   `RequestProject.Spine.Nerve`, `…Cech`, `…GoodCover`, `…Cohomology`, `…Geometry`,
   `…E1`, `…E2` or `…Controls`.
3. **Low-level geometry does not import high-level comparison.**  No module of
   `Nerve.Geometry`, `Nerve.Skeleton` or `Nerve.Basic` may reach `Nerve.Comparison`,
   `Nerve.CellFamily` or `Nerve.StandardCell`.
4. **Definitions do not import their proof stacks.**  `Nerve.CellFamily.TargetMap`, which
   defines `tgtDecomp`, must not reach the finite-family proof
   `Nerve.CellFamily.TargetDecomposition`, nor the standard-cell homology, generator or
   excision proofs, nor the cell geometry.  (It does import the *definition* of the standard
   cell pair, `Nerve.StandardCell.Pair`.)
5. **Independent branches.**  `AlgebraicTopology.DirectSumComplex` and its homology
   `AlgebraicTopology.DirectSumHomology` must reach neither the cell geometry nor Excision;
   `Nerve.Geometry.CellSeparation` must reach neither the standard-cell generator nor the
   `relJ` compatibility layer; `Nerve.CellFamily.SingularFactorization` must
   not reach the standard-cell Excision proof.
6. **The comparison layering.**  The mathematical dependency order is

   > lower `AlgebraicTopology` → lower Nerve geometry / cell machinery → `Comparison.RelJ`
   > → `Comparison.GlobalHomology` → `Comparison.GlobalCohomology`.

   Accordingly: the only production modules that may reach `Nerve.Comparison.RelJ` are the
   global comparison layer itself (`RelJ`, `GlobalHomology`, `GlobalCohomology`); no module
   may reach the endpoint `GlobalCohomology`; no cell-family, geometry, skeleton or basic
   module may reach `GlobalHomology`; and each step must genuinely reach the previous one
   (positive controls, so no check can pass vacuously).

7. **The Spin branch firewall (Task 30).**  The Stage-1.3 obstruction area is split into two
   branches that meet only in the comparison layer:

   > Branch A (standard control): `SO`-valued transition data → local Spin lifts → defect →
   > Čech obstruction → coherent Spin lift.
   > Branch B (Spin-native): Spin-valued gluing data → coherent Spin cocycle → projection
   > through `ρ` → `SO`-valued transition data.

   Accordingly: no module of `RequestProject.Spine.SpinNative` may reach the high-level
   obstruction machinery (`E2.Cech.Defect`, `E2.Cech.Coboundary`, `E2.Cech.Obstruction`,
   `E2.Cech.Refinement`, `E2.Cech.SpinInstance`), nor the frame/Spin-structure geometry
   (`Spine.Geometry`), nor `Spine.Cech`, `Spine.GoodCover`, `Spine.Cohomology`,
   `Spine.Nerve` or `Spine.Controls`; conversely no module of the standard branch may reach
   `Spine.SpinNative`; and `Spine.Comparison` is a leaf of the production DAG — no
   production module may import it, while it must itself reach both branches (positive
   controls).

8. **The uniqueness-layer firewall (Task 31).**  The Spin-native uniqueness layer

   > `SpinNative.KernelTwist` → `SpinNative.GaugeEquivalence` → `SpinNative.Canonical`
   > → `SpinNative.Rigidity`

   must reach neither the SO-first local-lift construction (`E2.Cech.LocalLifts`) nor any
   obstruction, Čech-cohomology, good-cover, Nerve or frame-geometry module; each of its four
   modules must genuinely reach the previous one (positive controls); and the two modules
   that see both directions — the cohomological gate
   `Comparison.KernelTwistCohomology` and the packaged handoff
   `Comparison.CanonicalSpinSeed`, together with the Lorentz-frame instance
   `Comparison.LorentzSpinUniqueness` — are comparison modules, hence leaves.

9. **The manifold-emergence firewall (Task 32).**  The emergence layer

   > `Emergent.LocalModel` → `Emergent.BaseGluing` → `Emergent.Reconstruction`
   > → `Emergent.Symmetric` → {`Emergent.NonDerivability`, `Emergent.SmoothGate`}

   is *base-free*: none of its modules may reach any cover-over-`X`, Čech, obstruction,
   frame-geometry, Nerve or Spin-native module — the local Clifford/Spin core
   (`Spine.E1`) and Mathlib are its only inputs.  The single exception is the explicit
   adapter `Emergent.CoverAdapter`, which may reach the cover interface
   `E2.Cech.Cover` (positive control) but still not the obstruction machinery, the frame
   geometry, the Spin-native branch or the comparison layer.  The join of the emergent base
   with the Task-31 twist/cohomology layer is the comparison module
   `Comparison.EmergentSpinGate`, hence a leaf, and it must genuinely reach both sides
   (positive controls).

10. **The smooth-manifold-closure firewall (Task 33).**  The new layer

    > `Emergent.SmoothGate` → `Emergent.SmoothStructure`
    > `Emergent.Symmetric` → `Emergent.SymmetricCanonical`
    > {`SmoothStructure`, `SymmetricCanonical`} → `Emergent.SymmetricSmooth`
    > `Emergent.NonDerivability` → `Emergent.LocalPieceData`

    stays inside the same base-free firewall: the smooth-manifold certification may use
    Mathlib's manifold machinery, but no module of it may reach the top-down tangent/frame
    geometry (`Spine.Geometry`), the Spin-obstruction machinery, the nerve-comparison
    machinery or the comparison layer.  In particular the smooth structure of the emergent
    base is *not* obtained by importing a pre-existing top-down manifold construction.

Every negative check is paired with an explicit `requireModule`, so a check can never pass
because the module it constrains is absent from the environment.
-/

open Lean Elab Command

namespace SpineAudit

/-- The production Spine: everything except the controls, the audits and the deliberately
aggregated `Core` modules. -/
def dagProductionModules (env : Environment) : List Name :=
  (spineModules env).filter fun m =>
    !((`RequestProject.Spine.Controls).isPrefixOf m) &&
      !((`RequestProject.Spine.Audit).isPrefixOf m) &&
      !((`RequestProject.Spine.Nerve.Audit).isPrefixOf m) &&
      !((`RequestProject.Spine.Nerve.Controls).isPrefixOf m)

/-- A module name is *chronological* if one of its components is `TaskNN…`. -/
def isChronological (m : Name) : Bool :=
  m.components.any fun c => "Task".isPrefixOf c.toString

/-- Negative check: `m` must not reach any module under one of the given prefixes. -/
def auditNoReach (env : Environment) (idx : Std.HashMap Name Nat) (label : String)
    (m : Name) (ps : List Name) : CommandElabM Unit := do
  requireModule idx m
  for x in (importClosure env idx m).toList do
    for p in ps do
      if p.isPrefixOf x && x != m then
        throwError "ARCHITECTURE VIOLATION ({label}): {m} transitively imports {x}"

/-- Positive control: `m` must reach `needed`, otherwise the corresponding negative checks
would be vacuous. -/
def auditReaches (env : Environment) (idx : Std.HashMap Name Nat) (m needed : Name) :
    CommandElabM Unit := do
  requireModule idx m
  requireModule idx needed
  unless (importClosure env idx m).contains needed do
    throwError "AUDIT NOT SENSITIVE: {m} does not import {needed}"

end SpineAudit

set_option maxRecDepth 10000 in
open SpineAudit in
run_cmd do
  let env ← getEnv
  let idx := moduleIndex env
  let prod := dagProductionModules env
  if prod.length < 60 then
    throwError "AUDIT NOT SENSITIVE: only {prod.length} production Spine modules are in scope"
  -- ===== 1. no chronological production modules in the Stage-1.3 area =====
  let stage13 := prod.filter fun m =>
    (`RequestProject.Spine.AlgebraicTopology).isPrefixOf m
      || (`RequestProject.Spine.Nerve).isPrefixOf m
  if stage13.length < 60 then
    throwError "AUDIT NOT SENSITIVE: only {stage13.length} Stage-1.3 modules are in scope"
  for m in stage13 do
    if isChronological m then
      throwError "CHRONOLOGICAL MODULE IN PRODUCTION: {m}"
  logInfo m!"Stage-1.3 production modules audited: {stage13.length} \
    (of {prod.length} production Spine modules); chronological TaskNN modules: 0"
  -- ===== 2. generic algebraic topology is below every domain-specific layer =====
  let genericForbidden : List Name :=
    [`RequestProject.Spine.Nerve, `RequestProject.Spine.Cech, `RequestProject.Spine.GoodCover,
     `RequestProject.Spine.Cohomology, `RequestProject.Spine.Geometry,
     `RequestProject.Spine.E1, `RequestProject.Spine.E2, `RequestProject.Spine.Controls,
     `RequestProject.Spine.SpinNative, `RequestProject.Spine.Comparison]
  let generic := prod.filter (`RequestProject.Spine.AlgebraicTopology).isPrefixOf
  if generic.length < 20 then
    throwError "AUDIT NOT SENSITIVE: only {generic.length} generic modules are in scope"
  for m in generic do
    auditNoReach env idx "generic results must not depend on Nerve-specific ones" m
      genericForbidden
  logInfo m!"generic AlgebraicTopology modules audited: {generic.length}, \
    domain-specific imports: 0"
  -- ===== 3. low-level geometry does not import high-level comparison =====
  let lowLevel := prod.filter fun m =>
    (`RequestProject.Spine.Nerve.Geometry).isPrefixOf m
      || (`RequestProject.Spine.Nerve.Skeleton).isPrefixOf m
      || (`RequestProject.Spine.Nerve.Basic).isPrefixOf m
  for m in lowLevel do
    auditNoReach env idx "geometry must not depend on the high-level comparison" m
      [`RequestProject.Spine.Nerve.Comparison, `RequestProject.Spine.Nerve.CellFamily,
       `RequestProject.Spine.Nerve.StandardCell]
  logInfo m!"low-level Nerve modules audited: {lowLevel.length}, high-level imports: 0"
  -- ===== 4. definitions do not drag in their proof stacks =====
  auditNoReach env idx "the definition of tgtDecomp must not import its finite-family proof"
    `RequestProject.Spine.Nerve.CellFamily.TargetMap
    [`RequestProject.Spine.Nerve.CellFamily.TargetDecomposition,
     `RequestProject.Spine.Nerve.CellFamily.RelativeChainDecomposition,
     `RequestProject.Spine.Nerve.CellFamily.SingularFactorization,
     `RequestProject.Spine.Nerve.CellFamily.ExcisionCompatibility,
     `RequestProject.Spine.Nerve.StandardCell.Homology,
     `RequestProject.Spine.Nerve.StandardCell.FundamentalClass,
     `RequestProject.Spine.Nerve.StandardCell.Generator,
     `RequestProject.Spine.Nerve.StandardCell.CanonicalGenerator,
     `RequestProject.Spine.Nerve.StandardCell.RelativeComparison,
     `RequestProject.Spine.Nerve.StandardCell.Excision,
     `RequestProject.Spine.Nerve.Geometry, `RequestProject.Spine.AlgebraicTopology.Excision]
  -- ===== 5. independent branches =====
  auditNoReach env idx "direct-sum homological algebra is independent of geometry"
    `RequestProject.Spine.AlgebraicTopology.DirectSumComplex
    [`RequestProject.Spine.Nerve, `RequestProject.Spine.AlgebraicTopology.Excision,
     `RequestProject.Spine.AlgebraicTopology.Subdivision]
  auditNoReach env idx "arbitrary direct-sum homology is independent of geometry"
    `RequestProject.Spine.AlgebraicTopology.DirectSumHomology
    [`RequestProject.Spine.Nerve, `RequestProject.Spine.AlgebraicTopology.Excision,
     `RequestProject.Spine.AlgebraicTopology.Subdivision]
  auditNoReach env idx "cell separation is point-set geometry"
    `RequestProject.Spine.Nerve.Geometry.CellSeparation
    [`RequestProject.Spine.Nerve.StandardCell, `RequestProject.Spine.Nerve.Comparison,
     `RequestProject.Spine.Nerve.CellFamily, `RequestProject.Spine.AlgebraicTopology.Excision]
  auditNoReach env idx "singular factorization needs cell geometry, not Excision proofs"
    `RequestProject.Spine.Nerve.CellFamily.SingularFactorization
    [`RequestProject.Spine.Nerve.StandardCell, `RequestProject.Spine.Nerve.Comparison]
  -- ===== 6. the comparison layering: RelJ → GlobalHomology → GlobalCohomology =====
  let globalLayer : List Name :=
    [`RequestProject.Spine.Nerve.Comparison.RelJ,
     `RequestProject.Spine.Nerve.Comparison.GlobalHomology,
     `RequestProject.Spine.Nerve.Comparison.GlobalCohomology]
  for m in globalLayer do
    requireModule idx m
  -- (a) `RelJ` is consumed only by the global comparison layer
  for m in prod do
    if !(globalLayer.contains m) then
      if (importClosure env idx m).contains `RequestProject.Spine.Nerve.Comparison.RelJ then
        throwError "ARCHITECTURE VIOLATION (RelJ is consumed only by the global comparison \
          layer): {m} imports it"
  -- (b) the cohomological endpoint is a leaf
  for m in prod do
    if m != `RequestProject.Spine.Nerve.Comparison.GlobalCohomology then
      if (importClosure env idx m).contains
          `RequestProject.Spine.Nerve.Comparison.GlobalCohomology then
        throwError "ARCHITECTURE VIOLATION (GlobalCohomology is the endpoint): {m} imports it"
  -- (c) nothing below the comparison layer may depend back on the global comparison
  let belowComparison := prod.filter fun m =>
    (`RequestProject.Spine.Nerve.Geometry).isPrefixOf m
      || (`RequestProject.Spine.Nerve.Skeleton).isPrefixOf m
      || (`RequestProject.Spine.Nerve.Basic).isPrefixOf m
      || (`RequestProject.Spine.Nerve.CellFamily).isPrefixOf m
      || (`RequestProject.Spine.Nerve.StandardCell).isPrefixOf m
      || (`RequestProject.Spine.AlgebraicTopology).isPrefixOf m
  for m in belowComparison do
    auditNoReach env idx "cell families and geometry must not depend on the global comparison"
      m [`RequestProject.Spine.Nerve.Comparison.GlobalHomology,
         `RequestProject.Spine.Nerve.Comparison.GlobalCohomology]
  -- (d) positive controls: each layer really joins the branches below it
  for needed in [`RequestProject.Spine.Nerve.Comparison.SourceDecomposition,
                 `RequestProject.Spine.Nerve.StandardCell.RelativeComparison,
                 `RequestProject.Spine.Nerve.CellFamily.TargetDecomposition,
                 `RequestProject.Spine.AlgebraicTopology.DirectSumComplex,
                 `RequestProject.Spine.AlgebraicTopology.DirectSumHomology] do
    auditReaches env idx `RequestProject.Spine.Nerve.Comparison.RelJ needed
  for needed in [`RequestProject.Spine.Nerve.Comparison.RelJ,
                 `RequestProject.Spine.Nerve.Comparison.SkeletalInduction,
                 `RequestProject.Spine.Nerve.Skeleton.SkeletalSupport,
                 `RequestProject.Spine.Nerve.Geometry.SkeletalFactorization,
                 `RequestProject.Spine.AlgebraicTopology.ExhaustiveHomology] do
    auditReaches env idx `RequestProject.Spine.Nerve.Comparison.GlobalHomology needed
  for needed in [`RequestProject.Spine.Nerve.Comparison.GlobalHomology,
                 `RequestProject.Spine.Nerve.Cochain.Dualization,
                 `RequestProject.Spine.AlgebraicTopology.DualCohomology,
                 `RequestProject.Spine.AlgebraicTopology.NaiveHomology] do
    auditReaches env idx `RequestProject.Spine.Nerve.Comparison.GlobalCohomology needed
  logInfo m!"comparison layering audited: RelJ → GlobalHomology → GlobalCohomology"
  -- ===== 7. the Spin branch firewall (Task 30) =====
  let spinNative := prod.filter (`RequestProject.Spine.SpinNative).isPrefixOf
  if spinNative.length < 2 then
    throwError "AUDIT NOT SENSITIVE: only {spinNative.length} Spin-native modules are in scope"
  let nativeForbidden : List Name :=
    [`RequestProject.Spine.E2.Cech.Defect, `RequestProject.Spine.E2.Cech.Coboundary,
     `RequestProject.Spine.E2.Cech.LocalLifts,
     `RequestProject.Spine.E2.Cech.Obstruction, `RequestProject.Spine.E2.Cech.Refinement,
     `RequestProject.Spine.E2.Cech.SpinInstance, `RequestProject.Spine.E2.Cech.Core,
     `RequestProject.Spine.Geometry, `RequestProject.Spine.Cech,
     `RequestProject.Spine.GoodCover, `RequestProject.Spine.Cohomology,
     `RequestProject.Spine.Nerve, `RequestProject.Spine.Controls,
     `RequestProject.Spine.Comparison]
  for m in spinNative do
    auditNoReach env idx "the Spin-native branch must not import the standard obstruction \
      machinery" m nativeForbidden
  -- The standard branch does not depend on the Spin-native branch either.  Two families of
  -- modules are legitimate *consumers* of the Spin-native branch and are therefore exempt:
  -- the comparison layer, and (Task 34) the tangent/solder layer `Spine.Solder`, whose whole
  -- subject is the coupling of the projected Spin/Lorentz transition with the tangent
  -- geometry.  The solder layer is itself firewalled in check 10 below.
  for m in prod do
    if !((`RequestProject.Spine.SpinNative).isPrefixOf m)
        && !((`RequestProject.Spine.Solder).isPrefixOf m)
        && !((`RequestProject.Spine.Comparison).isPrefixOf m) then
      if (importClosure env idx m).contains `RequestProject.Spine.SpinNative.TransitionData then
        throwError "ARCHITECTURE VIOLATION (the standard branch must not depend on the \
          Spin-native branch): {m} imports it"
  -- the comparison layer is a leaf of the production DAG
  let comparison := prod.filter (`RequestProject.Spine.Comparison).isPrefixOf
  if comparison.length < 1 then
    throwError "AUDIT NOT SENSITIVE: no comparison module is in scope"
  for m in prod do
    if !((`RequestProject.Spine.Comparison).isPrefixOf m) then
      for c in comparison do
        if (importClosure env idx m).contains c then
          throwError "ARCHITECTURE VIOLATION (the comparison layer is a leaf): {m} imports {c}"
  -- positive controls: the comparison layer really joins both branches
  for needed in [`RequestProject.Spine.SpinNative.TransitionData,
                 `RequestProject.Spine.SpinNative.Projection,
                 `RequestProject.Spine.E2.Cech.Obstruction,
                 `RequestProject.Spine.Geometry.SpinStructure] do
    auditReaches env idx `RequestProject.Spine.Comparison.SpinNativeVsSO needed
  logInfo m!"Spin branch firewall audited: {spinNative.length} Spin-native modules, \
    {comparison.length} comparison module(s); illegal edges: 0"
  -- ===== 8. the Task-31 uniqueness layer =====
  -- The uniqueness layer (kernel twist → gauge equivalence → canonical selection → rigidity)
  -- lives entirely inside the Spin-native branch, so it is already covered by the negative
  -- checks of §7; what is added here is that it depends on *nothing but* the minimal
  -- Spin-native machinery, that it is genuinely stacked in that order, and that the two
  -- modules which see the Čech/ℤ₂ cohomology or the standard obstruction are comparison
  -- modules.
  let uniquenessLayer : List Name :=
    [`RequestProject.Spine.SpinNative.KernelTwist,
     `RequestProject.Spine.SpinNative.GaugeEquivalence,
     `RequestProject.Spine.SpinNative.Canonical,
     `RequestProject.Spine.SpinNative.Rigidity]
  for m in uniquenessLayer do
    requireModule idx m
    auditNoReach env idx "the uniqueness layer must not import the SO-first lift construction \
      or any obstruction/cohomology machinery" m nativeForbidden
  -- the uniqueness layer really is a stack over the minimal Spin-native machinery
  for needed in [`RequestProject.Spine.SpinNative.TransitionData,
                 `RequestProject.Spine.SpinNative.Projection] do
    auditReaches env idx `RequestProject.Spine.SpinNative.KernelTwist needed
  auditReaches env idx `RequestProject.Spine.SpinNative.GaugeEquivalence
    `RequestProject.Spine.SpinNative.KernelTwist
  auditReaches env idx `RequestProject.Spine.SpinNative.Canonical
    `RequestProject.Spine.SpinNative.GaugeEquivalence
  auditReaches env idx `RequestProject.Spine.SpinNative.Rigidity
    `RequestProject.Spine.SpinNative.Canonical
  -- the cohomological gate and the packaged seed are comparison modules, and they really do
  -- join the branches they claim to join
  for needed in [`RequestProject.Spine.SpinNative.Rigidity,
                 `RequestProject.Spine.Cech.Cohomology] do
    auditReaches env idx `RequestProject.Spine.Comparison.KernelTwistCohomology needed
  for needed in [`RequestProject.Spine.SpinNative.Rigidity,
                 `RequestProject.Spine.E2.Cech.Obstruction] do
    auditReaches env idx `RequestProject.Spine.Comparison.CanonicalSpinSeed needed
  for needed in [`RequestProject.Spine.SpinNative.Rigidity,
                 `RequestProject.Spine.Geometry.SpinStructure] do
    auditReaches env idx `RequestProject.Spine.Comparison.LorentzSpinUniqueness needed
  -- no module of the uniqueness layer may reach the Nerve machinery or a manifold model
  for m in uniquenessLayer do
    auditNoReach env idx "the uniqueness layer must not import the Nerve or manifold \
      machinery" m [`RequestProject.Spine.Nerve, `RequestProject.Spine.GoodCover,
        `RequestProject.Spine.AlgebraicTopology, `RequestProject.Spine.Geometry]
  logInfo m!"Task-31 uniqueness layer audited: {uniquenessLayer.length} modules, \
    illegal edges: 0"
  -- ===== 9. the manifold-emergence firewall (Task 32) =====
  let emergentCore : List Name :=
    [`RequestProject.Spine.Emergent.LocalModel,
     `RequestProject.Spine.Emergent.BaseGluing,
     `RequestProject.Spine.Emergent.Reconstruction,
     `RequestProject.Spine.Emergent.Symmetric,
     `RequestProject.Spine.Emergent.NonDerivability,
     `RequestProject.Spine.Emergent.SmoothGate,
     `RequestProject.Spine.Emergent.SmoothStructure,
     `RequestProject.Spine.Emergent.SymmetricCanonical,
     `RequestProject.Spine.Emergent.SymmetricSmooth,
     `RequestProject.Spine.Emergent.LocalPieceData,
     `RequestProject.Spine.Emergent.TangentTransition]
  let emergentForbidden : List Name :=
    [`RequestProject.Spine.E2, `RequestProject.Spine.Cech, `RequestProject.Spine.Geometry,
     `RequestProject.Spine.Nerve, `RequestProject.Spine.GoodCover,
     `RequestProject.Spine.Cohomology, `RequestProject.Spine.AlgebraicTopology,
     `RequestProject.Spine.SpinNative, `RequestProject.Spine.Comparison,
     `RequestProject.Spine.Controls]
  for m in emergentCore do
    requireModule idx m
    auditNoReach env idx "the base-free emergence layer must not import cover-over-X, Čech, \
      obstruction, frame-geometry or Spin-native machinery" m emergentForbidden
  -- the layer really is stacked in the stated order (positive controls)
  auditReaches env idx `RequestProject.Spine.Emergent.BaseGluing
    `RequestProject.Spine.Emergent.LocalModel
  auditReaches env idx `RequestProject.Spine.Emergent.Reconstruction
    `RequestProject.Spine.Emergent.BaseGluing
  auditReaches env idx `RequestProject.Spine.Emergent.Symmetric
    `RequestProject.Spine.Emergent.Reconstruction
  auditReaches env idx `RequestProject.Spine.Emergent.NonDerivability
    `RequestProject.Spine.Emergent.Symmetric
  auditReaches env idx `RequestProject.Spine.Emergent.SmoothGate
    `RequestProject.Spine.Emergent.Symmetric
  -- Task 33: the smooth-closure and canonicity modules sit on top of the same base-free stack
  auditReaches env idx `RequestProject.Spine.Emergent.SmoothStructure
    `RequestProject.Spine.Emergent.SmoothGate
  auditReaches env idx `RequestProject.Spine.Emergent.SymmetricCanonical
    `RequestProject.Spine.Emergent.Symmetric
  auditReaches env idx `RequestProject.Spine.Emergent.SymmetricSmooth
    `RequestProject.Spine.Emergent.SmoothStructure
  auditReaches env idx `RequestProject.Spine.Emergent.SymmetricSmooth
    `RequestProject.Spine.Emergent.SymmetricCanonical
  auditReaches env idx `RequestProject.Spine.Emergent.LocalPieceData
    `RequestProject.Spine.Emergent.NonDerivability
  -- and it really does rest on the local Clifford/Spin core (so the checks are not vacuous)
  auditReaches env idx `RequestProject.Spine.Emergent.LocalModel
    `RequestProject.Spine.E1.SpinCover
  -- the adapter: allowed to see the cover interface, nothing above it
  auditReaches env idx `RequestProject.Spine.Emergent.CoverAdapter
    `RequestProject.Spine.E2.Cech.Cover
  auditReaches env idx `RequestProject.Spine.Emergent.CoverAdapter
    `RequestProject.Spine.Emergent.Symmetric
  auditNoReach env idx "the cover adapter must not import the obstruction machinery, the \
    frame geometry, the Spin-native branch or the comparison layer"
    `RequestProject.Spine.Emergent.CoverAdapter
    [`RequestProject.Spine.E2.Cech.Defect, `RequestProject.Spine.E2.Cech.Coboundary,
     `RequestProject.Spine.E2.Cech.LocalLifts, `RequestProject.Spine.E2.Cech.Obstruction,
     `RequestProject.Spine.E2.Cech.SpinInstance, `RequestProject.Spine.E2.Cech.Core,
     `RequestProject.Spine.Geometry, `RequestProject.Spine.Cech,
     `RequestProject.Spine.GoodCover, `RequestProject.Spine.Nerve,
     `RequestProject.Spine.SpinNative, `RequestProject.Spine.Comparison,
     `RequestProject.Spine.Controls]
  -- the emergence/Spin join is a comparison module and sees both sides
  for needed in [`RequestProject.Spine.Emergent.CoverAdapter,
                 `RequestProject.Spine.Emergent.NonDerivability,
                 `RequestProject.Spine.Cech.FullNerve,
                 `RequestProject.Spine.SpinNative.Rigidity,
                 `RequestProject.Spine.Comparison.KernelTwistCohomology] do
    auditReaches env idx `RequestProject.Spine.Comparison.EmergentSpinGate needed
  auditReaches env idx `RequestProject.Spine.Emergent.TangentTransition
    `RequestProject.Spine.Emergent.SmoothStructure
  logInfo m!"Task-32/33 manifold-emergence firewall audited: {emergentCore.length} base-free \
    modules (including the Task-33 smooth-manifold closure, symmetric canonicity and \
    local-piece-data layers) + 1 adapter + 1 comparison join; illegal edges: 0"
  -- ===== 10. the tangent/solder firewall (Task 34) =====
  -- The bottom-up solder branch may see the emergent base, the cover interface, the E2
  -- double-cover interface and the Spin-native projection, and nothing above them; in
  -- particular it must not reach the historical top-down tangent/frame/obstruction
  -- machinery, which is a certification target and never an input.
  let solderBranch : List Name :=
    [`RequestProject.Spine.Solder.InternalLorentz,
     `RequestProject.Spine.Solder.Independence,
     `RequestProject.Spine.Solder.Solder,
     `RequestProject.Spine.Solder.LorentzBundle,
     -- Task 35: the regularity layer
     `RequestProject.Spine.Solder.RegularSolder,
     `RequestProject.Spine.Solder.RegularExamples,
     `RequestProject.Spine.Solder.BundleEquivalence,
     `RequestProject.Spine.Solder.SmoothMetric,
     `RequestProject.Spine.Solder.OrientationTime,
     `RequestProject.Spine.Solder.RegularGauge,
     `RequestProject.Spine.Solder.WeakInsufficiency]
  let solderForbidden : List Name :=
    [`RequestProject.Spine.Geometry, `RequestProject.Spine.Cech,
     `RequestProject.Spine.Nerve, `RequestProject.Spine.GoodCover,
     `RequestProject.Spine.Cohomology, `RequestProject.Spine.AlgebraicTopology,
     `RequestProject.Spine.Comparison, `RequestProject.Spine.Controls,
     `RequestProject.Spine.E2.Cech.Obstruction, `RequestProject.Spine.E2.Cech.SpinInstance,
     `RequestProject.Spine.E2.Cech.Core]
  for m in solderBranch do
    requireModule idx m
    auditNoReach env idx "the bottom-up tangent/solder branch must not import the top-down \
      tangent/frame/obstruction machinery, the Čech/nerve layers or the comparison layer"
      m solderForbidden
  -- TASK-35 DAG REPAIR.  The internal-Lorentz branch must *not* depend on the tangent
  -- branch: the two transition systems are produced independently and only compared in
  -- `Solder.Independence` and above.
  auditNoReach env idx "the internal-Lorentz branch must be independent of the tangent \
    branch (Task-35 repair)" `RequestProject.Spine.Solder.InternalLorentz
    [`RequestProject.Spine.Emergent.TangentTransition]
  auditReaches env idx `RequestProject.Spine.Solder.InternalLorentz
    `RequestProject.Spine.E2.SpinProjection
  -- the comparison module sees *both* independent branches directly
  auditReaches env idx `RequestProject.Spine.Solder.Independence
    `RequestProject.Spine.Emergent.TangentTransition
  auditReaches env idx `RequestProject.Spine.Solder.Independence
    `RequestProject.Spine.Solder.InternalLorentz
  auditReaches env idx `RequestProject.Spine.Solder.Solder
    `RequestProject.Spine.Solder.Independence
  auditReaches env idx `RequestProject.Spine.Solder.LorentzBundle
    `RequestProject.Spine.Solder.Solder
  -- the comparison module is the *only* place where the two branches meet, and it sees both
  for needed in [`RequestProject.Spine.Solder.Solder,
                 `RequestProject.Spine.Geometry.TangentInstance,
                 `RequestProject.Spine.Geometry.FrameField] do
    auditReaches env idx `RequestProject.Spine.Comparison.SolderTangentGate needed
  -- ===== 11. the Task-35 regularity layer =====
  -- It is stacked on the Task-34 solder layer and on the tangent branch, and is still
  -- firewalled against the top-down machinery (checked above, as part of `solderBranch`).
  auditReaches env idx `RequestProject.Spine.Solder.RegularSolder
    `RequestProject.Spine.Solder.LorentzBundle
  auditReaches env idx `RequestProject.Spine.Solder.RegularSolder
    `RequestProject.Spine.Emergent.TangentTransition
  auditReaches env idx `RequestProject.Spine.Solder.BundleEquivalence
    `RequestProject.Spine.Solder.RegularSolder
  auditReaches env idx `RequestProject.Spine.Solder.SmoothMetric
    `RequestProject.Spine.Solder.BundleEquivalence
  auditReaches env idx `RequestProject.Spine.Solder.OrientationTime
    `RequestProject.Spine.Solder.SmoothMetric
  auditReaches env idx `RequestProject.Spine.Solder.RegularGauge
    `RequestProject.Spine.Solder.OrientationTime
  auditReaches env idx `RequestProject.Spine.Solder.RegularExamples
    `RequestProject.Spine.Solder.RegularSolder
  auditReaches env idx `RequestProject.Spine.Solder.WeakInsufficiency
    `RequestProject.Spine.Solder.RegularExamples
  -- the Task-35 comparison join sees the regularity layer and the top-down branch
  for needed in [`RequestProject.Spine.Solder.RegularGauge,
                 `RequestProject.Spine.Solder.WeakInsufficiency,
                 `RequestProject.Spine.Comparison.SolderTangentGate,
                 `RequestProject.Spine.Geometry.TangentInstance] do
    auditReaches env idx `RequestProject.Spine.Comparison.SmoothSolderGate needed
  logInfo m!"Task-34/35 tangent/solder firewall audited: {solderBranch.length} bottom-up \
    modules + 2 comparison joins; illegal edges: 0"
  logInfo m!"SPINE ARCHITECTURE AUDIT: all checks passed"
