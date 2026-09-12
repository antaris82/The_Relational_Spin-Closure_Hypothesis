# Dependency-DAG statistics, before and after the spine extraction

All numbers are computed mechanically from the `import` lines of the Lean sources, counting
project modules only (`Mathlib` is excluded).  "Before" is the merged tree as it stood at
the initial commit `5790111`; "after" is the current tree.

## Headline

| Endpoint | before | after | what left the closure |
| --- | --- | --- | --- |
| experiment-1 spin / `SL(2,ℂ)` chain | 48 (`Experiment1.Task11SL2`) | **19** (`Spine.E1.SL2Comparison`) | the whole Hermitian Jordan-carrier layer (`Herm2`, `Task6*`–`Task8*`, `Task9Freeze`, `Task9Wide`, `Task10Compare`, `SpinFinal`, `Minkowski4`, `SectorAlgebra`, …) |
| experiment-1 production core | — | **20** (`Spine.E1.Core`) | new principal endpoint: carrier, Clifford, spin double cover, Weyl module |
| experiment-1 carrier root | 41 (the `Task9SpinFactor` chain as consumed by `Task15Spinor`) | **1** (`Spine.E1.Carrier`) | the carrier module now imports `Mathlib` only |
| experiment-1 Clifford-module / Weyl material | 41 (`Experiment1.Task15Spinor`) | **3** (`Spine.E1.WeylSpinorModule`) | Maxwell, gauge-phase, quantization, mass-selection and positive-frequency branches |
| experiment-2 generic central double-cover interface | 221 (only reachable inside `NullSectorTask28.TransitionLiftBase`) | **1** (`Spine.E2.CentralDoubleCover`) | everything: the interface is now `Mathlib`-only and reusable |
| experiment-2 family core | 202 (`NullSectorTask26.Task26`) | **7** (`Spine.E2.Family.TransitionData`) | the Task-25 one-fibre endpoint and its Task-01…Task-24 chain |
| experiment-2 topological frame family | 212 (`NullSectorTask27.Task27`) | **17** (`Spine.E2.Topology.Task27`) | as above |
| experiment-2 generic lift layer | 221 (`NullSectorTask28` generic packages) | **23** (`Spine.E2.Lift.RepresentativeChange`) | as above |
| experiment-2 model instantiation | 221 (`NullSectorTask28.Task28`) | **207** (`Spine.E2.Model.Task28`) | the Task-24/Task-25 one-fibre comparison endpoint; the rest is the certified-projection chain the concrete model *is* |
| experiment-2 production endpoint | 263 (`NullSectorTask32.Task32`) | **248** (`Spine.E2.Core`) | the good/bad negative control and the one-fibre comparison endpoint |

Active source files: **488 → 319** (195 modules removed and ledgered, 26 modules added or
split off).

## Update after refactoring task 02 (intrinsic Spin core extraction)

The second refactoring pass split the experiment-1 spin material into a predicate layer, a
bundled group layer, the covering homomorphism and its kernel, and moved all of it *below*
the `SL(2,ℂ)` comparison.  Project-local closures, before and after that pass:

| Endpoint | direct before → after | transitive before → after | legacy E1 | legacy E2 |
| --- | --- | --- | --- | --- |
| `Spine.E1.Core` | 2 → 2 | 19 → 22 | 0 | 0 |
| `Spine.E1.SL2Comparison` | 2 → 2 | 18 → 22 | 0 | 0 |
| `Spine.E1.SpinKernel` (new intrinsic double-cover endpoint) | — → 1 | — → **19** | — → 0 | — → 0 |
| `Spine.E2.Core` | 1 → 1 | 247 → 247 | 0 | 180 |

The two small increases are module *splits* (four new files), not new mathematical
dependencies.  The point of the pass is the third row: the intrinsic double cover is now
reachable from a 19-module closure that contains none of `Spine.E1.MatrixModel`,
`Spine.E1.PauliRepresentation`, `Spine.E1.SL2Comparison` or `Spine.E1.WeylSpinorModule`;
before the pass the same theorems were only available from `SL2Comparison`, whose closure
contains all of them.  Figures are reproducible with `scripts/dep_stats.py`; the full
discussion, including build timings and the `InternalProjection` interface table, is in
`SPIN_CORE_EXTRACTION_AUDIT.md`.

## Update after refactoring task 03 (complete legacy decoupling)

The third pass removed the last arrow from the new code into the historical trees: the
concrete experiment-2 projection.  Project-local closures before and after that pass
(reproducible with `scripts/dep_stats.py` and `scripts/legacy_audit.py`):

| Endpoint | transitive before → after | legacy E1 | legacy E2 |
| --- | --- | --- | --- |
| `Spine.E1.Core` | 22 → 22 | 0 → 0 | 0 → 0 |
| `Spine.E1.SL2Comparison` | 22 → 22 | 0 → 0 | 0 → 0 |
| `Spine.E2.Topology.Task27` | 16 → 16 | 0 → 0 | 0 → 0 |
| `Spine.E2.Descent.Task29` | 216 → **34** | 0 → 0 | 180 → **0** |
| `Spine.E2.Global.Task30` | 228 → **46** | 0 → 0 | 180 → **0** |
| `Spine.E2.Defect.Task31` | 238 → **56** | 0 → 0 | 180 → **0** |
| `Spine.E2.AtlasChange.Task32` | 246 → **64** | 0 → 0 | 180 → **0** |
| `Spine.E2.Core` | 247 → **65** | 0 → 0 | 180 → **0** |
| `Spine.Audit.Firewall` | 320 → **98** | 26 → **0** | 193 → **0** |
| `Spine.Core` (new aggregate) | — → **91** | — → 0 | — → 0 |

Spine modules 96 → 100, Spine LOC 20 346 → 20 686.  The `Spine/E2/Model/` layer is gone:
two of its modules moved into `Spine/E2/Lift/` (`TransitionSystem`, `LiftLevels`) and two
were deleted with the legacy adapter.  `RequestProject/Comparison/**` (3 modules) was
removed, `RequestProject/Control/E2/**` (3 modules) became `Spine/Controls/E2/**`, and three
modules were added (`Spine/Core.lean`, `Spine/Controls/CircleDoubleCover.lean`,
`Spine/Controls/E2/NativeLiftControl.lean`).

The full report, including the migration provenance table, the mechanical audit output, the
axiom audit, the fail/repair ledger and the isolated build with both historical trees
removed, is `LEGACY_DECOUPLING_AUDIT.md`.

## Reading the experiment-2 numbers

The experiment-2 chain has two genuinely different regimes, and the refactor separates them:

* the **generic** layers — family, frames, transitions, topology, the central double-cover
  interface, local representatives, kernel ambiguity, the triple-overlap defect — are now
  1–23 modules deep and depend on `Mathlib` alone plus each other.  This is the part that a
  future Lorentzian tangent-frame family will re-instantiate;
* the **model-instantiated** layers no longer exist.  Up to refactoring task 02 they started
  at `Spine.E2.Model.CertifiedProjection`, which exhibited the concrete two-to-one projection
  of the frame model and therefore dragged the whole retained experiment-2 chain (171
  modules) into every later closure.  Task 03 deleted that adapter: the later layers are now
  generic in an internal projection `P`, and a native instance (the circle double cover)
  lives in the controls.  This is why the Descent/Global/Defect/AtlasChange closures drop
  from ≈ 220–250 to 34–65 modules.

## Full statistics

### Before (initial merged tree)
* modules in tree: **488**
* import edges: **661**
* closure of `RequestProject.Experiment1.Task11SL2` (E1 spin/SL2 endpoint): **48** modules
* closure of `RequestProject.Experiment1.Task15Spinor` (E1 Task-15 spinor branch): **41** modules
* closure of `RequestProject.Experiment1.SpinFinal` (E1 Hermitian endpoint): **11** modules
* closure of `RequestProject.Experiment2.NullSectorTask26.Task26` (E2 Task-26 endpoint): **202** modules
* closure of `RequestProject.Experiment2.NullSectorTask28.Task28` (E2 Task-28 lift endpoint): **221** modules
* closure of `RequestProject.Experiment2.NullSectorTask32.Task32` (E2 Task-32 endpoint): **263** modules
* closure of `RequestProject.CombinedDemo` (combined demo): **18** modules

### After (refactored tree)
* modules in tree: **319**
* import edges: **365**
* closure of `RequestProject.Spine.E1.Core` (E1 production endpoint): **20** modules
* closure of `RequestProject.Spine.E1.SL2Comparison` (E1 SL(2,C) comparison): **19** modules
* closure of `RequestProject.Spine.E1.WeylSpinorModule` (E1 Weyl module): **3** modules
* closure of `RequestProject.Spine.E1.Carrier` (E1 carrier root): **1** modules
* closure of `RequestProject.Spine.E2.CentralDoubleCover` (E2 generic lift layer): **1** modules
* closure of `RequestProject.Spine.E2.Family.TransitionData` (E2 family core): **7** modules
* closure of `RequestProject.Spine.E2.Topology.Task27` (E2 topology endpoint): **17** modules
* closure of `RequestProject.Spine.E2.Lift.RepresentativeChange` (E2 generic lift layer, top): **23** modules
* closure of `RequestProject.Spine.E2.Model.CertifiedProjection` (E2 model instantiation): **204** modules
* closure of `RequestProject.Spine.E2.Model.Task28` (E2 model lift endpoint): **207** modules
* closure of `RequestProject.Spine.E2.Descent.Task29` (E2 descent endpoint): **217** modules
* closure of `RequestProject.Spine.E2.Defect.Task31` (E2 defect endpoint): **239** modules
* closure of `RequestProject.Spine.E2.AtlasChange.Task32` (E2 atlas-change endpoint): **247** modules
* closure of `RequestProject.Spine.E2.Core` (E2 production endpoint): **248** modules
* closure of `RequestProject.Comparison.E1Hermitian` (E1 Hermitian comparison): **29** modules
* closure of `RequestProject.Comparison.E2Task26Endpoint` (E2 one-fibre comparison): **202** modules
* closure of `RequestProject.Control.E2.FamilyDefectControl` (good/bad control): **249** modules
* closure of `RequestProject.CombinedDemo` (combined demo): **269** modules

### Exact transitive closure of each new principal endpoint

#### `RequestProject.Spine.E1.Core` — experiment-1 production core (20 project modules)

* `RequestProject.Spine.E1.Bivector`
* `RequestProject.Spine.E1.Carrier`
* `RequestProject.Spine.E1.Clifford`
* `RequestProject.Spine.E1.CliffordHodgeBridge`
* `RequestProject.Spine.E1.Coords`
* `RequestProject.Spine.E1.Core`
* `RequestProject.Spine.E1.DoubleCover`
* `RequestProject.Spine.E1.Hodge`
* `RequestProject.Spine.E1.Hyperbolic`
* `RequestProject.Spine.E1.LieAlgebra`
* `RequestProject.Spine.E1.LorentzClifford`
* `RequestProject.Spine.E1.LorentzGroup`
* `RequestProject.Spine.E1.MatrixModel`
* `RequestProject.Spine.E1.Paravector`
* `RequestProject.Spine.E1.PauliRepresentation`
* `RequestProject.Spine.E1.Shell`
* `RequestProject.Spine.E1.ShellTransitivity`
* `RequestProject.Spine.E1.SpinDeterminant`
* `RequestProject.Spine.E1.SpinGroup`
* `RequestProject.Spine.E1.WeylSpinorModule`

#### `RequestProject.Spine.E1.SL2Comparison` — experiment-1 SL(2,ℂ) comparison (19 project modules)

* `RequestProject.Spine.E1.Bivector`
* `RequestProject.Spine.E1.Carrier`
* `RequestProject.Spine.E1.Clifford`
* `RequestProject.Spine.E1.CliffordHodgeBridge`
* `RequestProject.Spine.E1.Coords`
* `RequestProject.Spine.E1.DoubleCover`
* `RequestProject.Spine.E1.Hodge`
* `RequestProject.Spine.E1.Hyperbolic`
* `RequestProject.Spine.E1.LieAlgebra`
* `RequestProject.Spine.E1.LorentzClifford`
* `RequestProject.Spine.E1.LorentzGroup`
* `RequestProject.Spine.E1.MatrixModel`
* `RequestProject.Spine.E1.Paravector`
* `RequestProject.Spine.E1.PauliRepresentation`
* `RequestProject.Spine.E1.SL2Comparison`
* `RequestProject.Spine.E1.Shell`
* `RequestProject.Spine.E1.ShellTransitivity`
* `RequestProject.Spine.E1.SpinDeterminant`
* `RequestProject.Spine.E1.SpinGroup`

#### `RequestProject.Spine.E2.Core` — experiment-2 production core (248 project modules)

* `RequestProject.Experiment2.NullSectorTask01.Basic`
* `RequestProject.Experiment2.NullSectorTask02.CandidateProduct`
* `RequestProject.Experiment2.NullSectorTask02.FixedUnit`
* `RequestProject.Experiment2.NullSectorTask02.LorentzData`
* `RequestProject.Experiment2.NullSectorTask04.GlobalExtension`
* `RequestProject.Experiment2.NullSectorTask04.Lorentz4`
* `RequestProject.Experiment2.NullSectorTask04.RestSpace`
* `RequestProject.Experiment2.NullSectorTask04.Sectors`
* `RequestProject.Experiment2.NullSectorTask06.AssociativityObstruction`
* `RequestProject.Experiment2.NullSectorTask06.GenericExtension`
* `RequestProject.Experiment2.NullSectorTask06.SafeBase`
* `RequestProject.Experiment2.NullSectorTask07.AmbientExtension`
* `RequestProject.Experiment2.NullSectorTask07.ForcedRelations`
* `RequestProject.Experiment2.NullSectorTask07.GeneratedClosure`
* `RequestProject.Experiment2.NullSectorTask07.Minimality`
* `RequestProject.Experiment2.NullSectorTask07.MixedProduct`
* `RequestProject.Experiment2.NullSectorTask07.NewDirection`
* `RequestProject.Experiment2.NullSectorTask07.Polarization`
* `RequestProject.Experiment2.NullSectorTask07.SafeBase`
* `RequestProject.Experiment2.NullSectorTask07.TwoDirections`
* `RequestProject.Experiment2.NullSectorTask08.DirectWitness`
* `RequestProject.Experiment2.NullSectorTask08.ForcedRelations`
* `RequestProject.Experiment2.NullSectorTask08.FullVec4Embedding`
* `RequestProject.Experiment2.NullSectorTask08.GeneratedClosure`
* `RequestProject.Experiment2.NullSectorTask08.Independence`
* `RequestProject.Experiment2.NullSectorTask08.InheritedRelations`
* `RequestProject.Experiment2.NullSectorTask08.Membership`
* `RequestProject.Experiment2.NullSectorTask08.Minimality`
* `RequestProject.Experiment2.NullSectorTask08.NewMixedProducts`
* `RequestProject.Experiment2.NullSectorTask08.SafeBase`
* `RequestProject.Experiment2.NullSectorTask08.StructuralDiagnostic`
* `RequestProject.Experiment2.NullSectorTask08.ThirdDirection`
* `RequestProject.Experiment2.NullSectorTask09.CentralPlane`
* `RequestProject.Experiment2.NullSectorTask09.Existence`
* `RequestProject.Experiment2.NullSectorTask09.RealScalarNoGo`
* `RequestProject.Experiment2.NullSectorTask09.Rigidity`
* `RequestProject.Experiment2.NullSectorTask09.SafeBase`
* `RequestProject.Experiment2.NullSectorTask09.UnknownQuadraticMap`
* `RequestProject.Experiment2.NullSectorTask10.AlgebraExtension`
* `RequestProject.Experiment2.NullSectorTask10.AxialDerivation`
* `RequestProject.Experiment2.NullSectorTask10.AxisDecomposition`
* `RequestProject.Experiment2.NullSectorTask10.HalfAngleSectors`
* `RequestProject.Experiment2.NullSectorTask10.InternalLift`
* `RequestProject.Experiment2.NullSectorTask10.OldAxialRotation`
* `RequestProject.Experiment2.NullSectorTask10.SafeBase`
* `RequestProject.Experiment2.NullSectorTask10.StateAction`
* `RequestProject.Experiment2.NullSectorTask10.VectorChannels`
* `RequestProject.Experiment2.NullSectorTask11.CenterRigidity`
* `RequestProject.Experiment2.NullSectorTask11.ContinuousClassification`
* `RequestProject.Experiment2.NullSectorTask11.ExactLiftClassification`
* `RequestProject.Experiment2.NullSectorTask11.FullLift`
* `RequestProject.Experiment2.NullSectorTask11.GeneratorSeparation`
* `RequestProject.Experiment2.NullSectorTask11.InfinitesimalLift`
* `RequestProject.Experiment2.NullSectorTask11.PeriodicityAudit`
* `RequestProject.Experiment2.NullSectorTask11.QuadraticCompatibility`
* `RequestProject.Experiment2.NullSectorTask11.ReferenceExistence`
* `RequestProject.Experiment2.NullSectorTask11.RelativeLiftRigidity`
* `RequestProject.Experiment2.NullSectorTask11.SafeBase`
* `RequestProject.Experiment2.NullSectorTask12.AxisRelation`
* `RequestProject.Experiment2.NullSectorTask12.CarrierEndomorphisms`
* `RequestProject.Experiment2.NullSectorTask12.CarrierFamily`
* `RequestProject.Experiment2.NullSectorTask12.CentralAction`
* `RequestProject.Experiment2.NullSectorTask12.DimensionClassification`
* `RequestProject.Experiment2.NullSectorTask12.GeneratedCarrier`
* `RequestProject.Experiment2.NullSectorTask12.HalfAngleRelation`
* `RequestProject.Experiment2.NullSectorTask12.LeftCarrier`
* `RequestProject.Experiment2.NullSectorTask12.LiftStability`
* `RequestProject.Experiment2.NullSectorTask12.MinimalCarrier`
* `RequestProject.Experiment2.NullSectorTask12.SafeBase`
* `RequestProject.Experiment2.NullSectorTask13.AutomorphismCarrierAction`
* `RequestProject.Experiment2.NullSectorTask13.CarrierIntertwiners`
* `RequestProject.Experiment2.NullSectorTask13.CarrierSlices`
* `RequestProject.Experiment2.NullSectorTask13.FixedCarrierLocus`
* `RequestProject.Experiment2.NullSectorTask13.FullLiftRestriction`
* `RequestProject.Experiment2.NullSectorTask13.InfinitesimalRestriction`
* `RequestProject.Experiment2.NullSectorTask13.MinusSectorHardening`
* `RequestProject.Experiment2.NullSectorTask13.ReferenceRestriction`
* `RequestProject.Experiment2.NullSectorTask13.ReferenceSectorAction`
* `RequestProject.Experiment2.NullSectorTask13.RelativeSectorAction`
* `RequestProject.Experiment2.NullSectorTask13.SafeBase`
* `RequestProject.Experiment2.NullSectorTask13.SelectionAudit`
* `RequestProject.Experiment2.NullSectorTask13.SliceCentralStructure`
* `RequestProject.Experiment2.NullSectorTask14.AxisGeneratorMap`
* `RequestProject.Experiment2.NullSectorTask14.CarrierFamilyAction`
* `RequestProject.Experiment2.NullSectorTask14.CarrierIntertwiners`
* `RequestProject.Experiment2.NullSectorTask14.CoherenceAudit`
* `RequestProject.Experiment2.NullSectorTask14.CommonFixedLocus`
* `RequestProject.Experiment2.NullSectorTask14.FullLiftDefect`
* `RequestProject.Experiment2.NullSectorTask14.GenericAxis`
* `RequestProject.Experiment2.NullSectorTask14.GenericTwoAxisComposition`
* `RequestProject.Experiment2.NullSectorTask14.ImplementerClosure`
* `RequestProject.Experiment2.NullSectorTask14.MixedFiniteComposition`
* `RequestProject.Experiment2.NullSectorTask14.MixedInfinitesimalComposition`
* `RequestProject.Experiment2.NullSectorTask14.MixedProjectors`
* `RequestProject.Experiment2.NullSectorTask14.ReferenceWordDefect`
* `RequestProject.Experiment2.NullSectorTask14.SafeBase`
* `RequestProject.Experiment2.NullSectorTask14.SecondAxisAutomorphism`
* `RequestProject.Experiment2.NullSectorTask14.SecondAxisCarrierSlices`
* `RequestProject.Experiment2.NullSectorTask14.SecondAxisImplementation`
* `RequestProject.Experiment2.NullSectorTask14.SecondAxisOldStructure`
* `RequestProject.Experiment2.NullSectorTask14.SecondAxisSectorAction`
* `RequestProject.Experiment2.NullSectorTask14.SelectionAudit`
* `RequestProject.Experiment2.NullSectorTask14.TwoAxisSliceComparison`
* `RequestProject.Experiment2.NullSectorTask15.DifferentiableLift`
* `RequestProject.Experiment2.NullSectorTask15.Infinitesimal`
* `RequestProject.Experiment2.NullSectorTask15.MixedComposition`
* `RequestProject.Experiment2.NullSectorTask15.RegularLift`
* `RequestProject.Experiment2.NullSectorTask15.SafeBase`
* `RequestProject.Experiment2.NullSectorTask16.ExactCoincidences`
* `RequestProject.Experiment2.NullSectorTask16.JointRegularity`
* `RequestProject.Experiment2.NullSectorTask16.LocalRepair`
* `RequestProject.Experiment2.NullSectorTask16.RegularDefect`
* `RequestProject.Experiment2.NullSectorTask16.SafeBase`
* `RequestProject.Experiment2.NullSectorTask16.TransformationValuedClosure`
* `RequestProject.Experiment2.NullSectorTask17.AdmissibleDomains`
* `RequestProject.Experiment2.NullSectorTask17.DomainGeometry`
* `RequestProject.Experiment2.NullSectorTask17.LocalExhaustion`
* `RequestProject.Experiment2.NullSectorTask17.OverlapTransitions`
* `RequestProject.Experiment2.NullSectorTask17.RateRigidity`
* `RequestProject.Experiment2.NullSectorTask17.Reconstruction`
* `RequestProject.Experiment2.NullSectorTask17.RegularityAudit`
* `RequestProject.Experiment2.NullSectorTask17.SafeBase`
* `RequestProject.Experiment2.NullSectorTask18.BridgeFactors`
* `RequestProject.Experiment2.NullSectorTask18.BridgeReconstruction`
* `RequestProject.Experiment2.NullSectorTask18.ConnectedAdmissibility`
* `RequestProject.Experiment2.NullSectorTask18.DisconnectedDomains`
* `RequestProject.Experiment2.NullSectorTask18.GlobalBridgeObstruction`
* `RequestProject.Experiment2.NullSectorTask18.MaximalDomains`
* `RequestProject.Experiment2.NullSectorTask18.NegativeControls`
* `RequestProject.Experiment2.NullSectorTask18.ReconstructionPredicates`
* `RequestProject.Experiment2.NullSectorTask18.RegularityAudit`
* `RequestProject.Experiment2.NullSectorTask18.RelationCoverage`
* `RequestProject.Experiment2.NullSectorTask18.SafeBase`
* `RequestProject.Experiment2.NullSectorTask19.DisconnectedExtension`
* `RequestProject.Experiment2.NullSectorTask19.HigherRegularity`
* `RequestProject.Experiment2.NullSectorTask19.MaximalPreconnected`
* `RequestProject.Experiment2.NullSectorTask19.MinimalObstruction`
* `RequestProject.Experiment2.NullSectorTask19.NegativeControls`
* `RequestProject.Experiment2.NullSectorTask19.PlainMaximality`
* `RequestProject.Experiment2.NullSectorTask19.PrimitiveBridge`
* `RequestProject.Experiment2.NullSectorTask19.RelationBridge`
* `RequestProject.Experiment2.NullSectorTask19.RelationCompletion`
* `RequestProject.Experiment2.NullSectorTask19.SafeBase`
* `RequestProject.Experiment2.NullSectorTask20.BridgeTorsor`
* `RequestProject.Experiment2.NullSectorTask20.GlobalObstruction`
* `RequestProject.Experiment2.NullSectorTask20.Identification`
* `RequestProject.Experiment2.NullSectorTask20.InternalProjection`
* `RequestProject.Experiment2.NullSectorTask20.LiftCarrier`
* `RequestProject.Experiment2.NullSectorTask20.NegativeControls`
* `RequestProject.Experiment2.NullSectorTask20.ReversalQuotient`
* `RequestProject.Experiment2.NullSectorTask20.SafeBase`
* `RequestProject.Experiment2.NullSectorTask20.SectionObstruction`
* `RequestProject.Experiment2.NullSectorTask20.VisibleQuotient`
* `RequestProject.Experiment2.NullSectorTask21.CentralComplex`
* `RequestProject.Experiment2.NullSectorTask21.CentralProduct`
* `RequestProject.Experiment2.NullSectorTask21.CoreProjection`
* `RequestProject.Experiment2.NullSectorTask21.CoreQuaternionEquiv`
* `RequestProject.Experiment2.NullSectorTask21.GroupPackaging`
* `RequestProject.Experiment2.NullSectorTask21.NegativeControls`
* `RequestProject.Experiment2.NullSectorTask21.NormalizedCentralCarrier`
* `RequestProject.Experiment2.NullSectorTask21.SU2Model`
* `RequestProject.Experiment2.NullSectorTask21.SafeBase`
* `RequestProject.Experiment2.NullSectorTask21.SectionObstruction`
* `RequestProject.Experiment2.NullSectorTask21.SignStructures`
* `RequestProject.Experiment2.NullSectorTask21.Task21`
* `RequestProject.Experiment2.NullSectorTask21.Task22`
* `RequestProject.Experiment2.NullSectorTask21.TorsorPlacement`
* `RequestProject.Experiment2.NullSectorTask21.VisibleRotationCandidate`
* `RequestProject.Experiment2.NullSectorTask23.Comparison`
* `RequestProject.Experiment2.NullSectorTask23.Cover`
* `RequestProject.Experiment2.NullSectorTask23.GlobalSection`
* `RequestProject.Experiment2.NullSectorTask23.Hierarchy`
* `RequestProject.Experiment2.NullSectorTask23.LocalProduct`
* `RequestProject.Experiment2.NullSectorTask23.OldBridges`
* `RequestProject.Experiment2.NullSectorTask23.OldDomains`
* `RequestProject.Experiment2.NullSectorTask23.Reconstruction`
* `RequestProject.Experiment2.NullSectorTask23.SafeBase`
* `RequestProject.Experiment2.NullSectorTask23.Sections`
* `RequestProject.Experiment2.NullSectorTask23.Task23`
* `RequestProject.Experiment2.NullSectorTask23.Transitions`
* `RequestProject.Spine.E2.AtlasChange.AtlasChangeLiftability`
* `RequestProject.Spine.E2.AtlasChange.FamilyDefectNeutrality`
* `RequestProject.Spine.E2.AtlasChange.FamilyExistenceClassification`
* `RequestProject.Spine.E2.AtlasChange.FamilyLiftability`
* `RequestProject.Spine.E2.AtlasChange.OrdinaryAtlasChange`
* `RequestProject.Spine.E2.AtlasChange.OrdinaryAtlasEquivalence`
* `RequestProject.Spine.E2.AtlasChange.OrdinaryCoverRefinement`
* `RequestProject.Spine.E2.AtlasChange.Task32`
* `RequestProject.Spine.E2.AtlasChange.UnderlyingFrameGeometry`
* `RequestProject.Spine.E2.CentralDoubleCover`
* `RequestProject.Spine.E2.Core`
* `RequestProject.Spine.E2.Defect.DefectNeutrality`
* `RequestProject.Spine.E2.Defect.ExistenceClassification`
* `RequestProject.Spine.E2.Defect.FrameFamilyRealization`
* `RequestProject.Spine.E2.Defect.GlobalCoveringHardening`
* `RequestProject.Spine.E2.Defect.GlobalMapHardening`
* `RequestProject.Spine.E2.Defect.IntrinsicDefectState`
* `RequestProject.Spine.E2.Defect.LiftabilityPredicate`
* `RequestProject.Spine.E2.Defect.SpatialClosureInterface`
* `RequestProject.Spine.E2.Defect.UniversalExistenceAudit`
* `RequestProject.Spine.E2.Descent.ChoiceInvariance`
* `RequestProject.Spine.E2.Descent.CombinedCompatibility`
* `RequestProject.Spine.E2.Descent.CompatibleTransitions`
* `RequestProject.Spine.E2.Descent.DefectFreeHardening`
* `RequestProject.Spine.E2.Descent.Inherited`
* `RequestProject.Spine.E2.Descent.KernelAdjustment`
* `RequestProject.Spine.E2.Descent.PairwiseDescent`
* `RequestProject.Spine.E2.Descent.RefinementBehavior`
* `RequestProject.Spine.E2.Descent.SimultaneousTrivialisation`
* `RequestProject.Spine.E2.Descent.Task29`
* `RequestProject.Spine.E2.Family.FamilyBase`
* `RequestProject.Spine.E2.Family.FiberFrames`
* `RequestProject.Spine.E2.Family.FiberIsometryGroup`
* `RequestProject.Spine.E2.Family.FrameTotal`
* `RequestProject.Spine.E2.Family.FrameTrivialization`
* `RequestProject.Spine.E2.Family.LocalTrivialization`
* `RequestProject.Spine.E2.Family.TransitionData`
* `RequestProject.Spine.E2.Global.ConditionalGlobalInterface`
* `RequestProject.Spine.E2.Global.GlobalFrameProjection`
* `RequestProject.Spine.E2.Global.GlobalGlueBase`
* `RequestProject.Spine.E2.Global.InternalGlueRelation`
* `RequestProject.Spine.E2.Global.InternalGroupAction`
* `RequestProject.Spine.E2.Global.InternalQuotient`
* `RequestProject.Spine.E2.Global.InternalTopology`
* `RequestProject.Spine.E2.Global.KernelFibres`
* `RequestProject.Spine.E2.Global.LocalComparison`
* `RequestProject.Spine.E2.Global.OrdinaryFrameSideInstance`
* `RequestProject.Spine.E2.Global.PresentationIndependence`
* `RequestProject.Spine.E2.Global.Task30`
* `RequestProject.Spine.E2.Lift.KernelAmbiguity`
* `RequestProject.Spine.E2.Lift.LocalInternalRepresentatives`
* `RequestProject.Spine.E2.Lift.RepresentativeChange`
* `RequestProject.Spine.E2.Lift.TransitionLiftBase`
* `RequestProject.Spine.E2.Lift.TripleOverlapDefect`
* `RequestProject.Spine.E2.Model.CertifiedProjection`
* `RequestProject.Spine.E2.Model.InternalTransitionInterface`
* `RequestProject.Spine.E2.Model.ModelBridge`
* `RequestProject.Spine.E2.Model.Task28`
* `RequestProject.Spine.E2.Topology.AtlasExtension`
* `RequestProject.Spine.E2.Topology.AtlasTopology`
* `RequestProject.Spine.E2.Topology.ContinuousTransitions`
* `RequestProject.Spine.E2.Topology.FiberTopology`
* `RequestProject.Spine.E2.Topology.FrameRightAction`
* `RequestProject.Spine.E2.Topology.FrameTopology`
* `RequestProject.Spine.E2.Topology.ModelTopology`
* `RequestProject.Spine.E2.Topology.ReverseReconstruction`
* `RequestProject.Spine.E2.Topology.Task27`
* `RequestProject.Spine.E2.Topology.TopologicalFrameFamily`

#### `RequestProject.Spine.E2.CentralDoubleCover` — generic central double-cover layer (1 project modules)

* `RequestProject.Spine.E2.CentralDoubleCover`

#### `RequestProject.Spine.E2.Lift.RepresentativeChange` — experiment-2 generic family/topology/lift layers (23 project modules)

* `RequestProject.Spine.E2.CentralDoubleCover`
* `RequestProject.Spine.E2.Family.FamilyBase`
* `RequestProject.Spine.E2.Family.FiberFrames`
* `RequestProject.Spine.E2.Family.FiberIsometryGroup`
* `RequestProject.Spine.E2.Family.FrameTotal`
* `RequestProject.Spine.E2.Family.FrameTrivialization`
* `RequestProject.Spine.E2.Family.LocalTrivialization`
* `RequestProject.Spine.E2.Family.TransitionData`
* `RequestProject.Spine.E2.Lift.KernelAmbiguity`
* `RequestProject.Spine.E2.Lift.LocalInternalRepresentatives`
* `RequestProject.Spine.E2.Lift.RepresentativeChange`
* `RequestProject.Spine.E2.Lift.TransitionLiftBase`
* `RequestProject.Spine.E2.Lift.TripleOverlapDefect`
* `RequestProject.Spine.E2.Topology.AtlasExtension`
* `RequestProject.Spine.E2.Topology.AtlasTopology`
* `RequestProject.Spine.E2.Topology.ContinuousTransitions`
* `RequestProject.Spine.E2.Topology.FiberTopology`
* `RequestProject.Spine.E2.Topology.FrameRightAction`
* `RequestProject.Spine.E2.Topology.FrameTopology`
* `RequestProject.Spine.E2.Topology.ModelTopology`
* `RequestProject.Spine.E2.Topology.ReverseReconstruction`
* `RequestProject.Spine.E2.Topology.Task27`
* `RequestProject.Spine.E2.Topology.TopologicalFrameFamily`

#### `RequestProject.Spine.Audit.Firewall` — firewall audit (317 project modules)

* `RequestProject.Comparison.E1Hermitian`
* `RequestProject.Comparison.E2OneFibreComparison`
* `RequestProject.Comparison.E2Task26Endpoint`
* `RequestProject.Control.E2.DescentCounterexample`
* `RequestProject.Control.E2.FamilyDefectControl`
* `RequestProject.Control.E2.GoodBadAtlas`
* `RequestProject.Experiment1.CarrierEquivalence`
* `RequestProject.Experiment1.DetPreserving`
* `RequestProject.Experiment1.DetPreservingQuotient`
* `RequestProject.Experiment1.DetPreservingRep`
* `RequestProject.Experiment1.Herm2`
* `RequestProject.Experiment1.LorentzMatrix`
* `RequestProject.Experiment1.SectorAlgebra`
* `RequestProject.Experiment1.SectorLorentzGroup`
* `RequestProject.Experiment1.SpinFinal`
* `RequestProject.Experiment1.SpinLifts`
* `RequestProject.Experiment1.SpinLorentz`
* `RequestProject.Experiment1.SpinSurjectivity`
* `RequestProject.Experiment1.Task6Aut`
* `RequestProject.Experiment1.Task6Carrier`
* `RequestProject.Experiment1.Task6Cone`
* `RequestProject.Experiment1.Task6Jordan`
* `RequestProject.Experiment1.Task6Rigidity`
* `RequestProject.Experiment1.Task7Cone`
* `RequestProject.Experiment1.Task7Jordan`
* `RequestProject.Experiment1.Task7Polarization`
* `RequestProject.Experiment1.Task7Trace`
* `RequestProject.Experiment1.Task8Aut`
* `RequestProject.Experiment1.Task8Cone`
* `RequestProject.Experiment1.Task8Intrinsic`
* `RequestProject.Experiment1.Task9Freeze`
* `RequestProject.Experiment1.V3Restriction`
* `RequestProject.Experiment2.NullSectorTask01.Basic`
* `RequestProject.Experiment2.NullSectorTask02.CandidateProduct`
* `RequestProject.Experiment2.NullSectorTask02.FixedUnit`
* `RequestProject.Experiment2.NullSectorTask02.LorentzData`
* `RequestProject.Experiment2.NullSectorTask04.GlobalExtension`
* `RequestProject.Experiment2.NullSectorTask04.Lorentz4`
* `RequestProject.Experiment2.NullSectorTask04.RestSpace`
* `RequestProject.Experiment2.NullSectorTask04.Sectors`
* `RequestProject.Experiment2.NullSectorTask06.AssociativityObstruction`
* `RequestProject.Experiment2.NullSectorTask06.GenericExtension`
* `RequestProject.Experiment2.NullSectorTask06.SafeBase`
* `RequestProject.Experiment2.NullSectorTask07.AmbientExtension`
* `RequestProject.Experiment2.NullSectorTask07.ForcedRelations`
* `RequestProject.Experiment2.NullSectorTask07.GeneratedClosure`
* `RequestProject.Experiment2.NullSectorTask07.Minimality`
* `RequestProject.Experiment2.NullSectorTask07.MixedProduct`
* `RequestProject.Experiment2.NullSectorTask07.NewDirection`
* `RequestProject.Experiment2.NullSectorTask07.Polarization`
* `RequestProject.Experiment2.NullSectorTask07.SafeBase`
* `RequestProject.Experiment2.NullSectorTask07.TwoDirections`
* `RequestProject.Experiment2.NullSectorTask08.DirectWitness`
* `RequestProject.Experiment2.NullSectorTask08.ForcedRelations`
* `RequestProject.Experiment2.NullSectorTask08.FullVec4Embedding`
* `RequestProject.Experiment2.NullSectorTask08.GeneratedClosure`
* `RequestProject.Experiment2.NullSectorTask08.Independence`
* `RequestProject.Experiment2.NullSectorTask08.InheritedRelations`
* `RequestProject.Experiment2.NullSectorTask08.Membership`
* `RequestProject.Experiment2.NullSectorTask08.Minimality`
* `RequestProject.Experiment2.NullSectorTask08.NewMixedProducts`
* `RequestProject.Experiment2.NullSectorTask08.SafeBase`
* `RequestProject.Experiment2.NullSectorTask08.StructuralDiagnostic`
* `RequestProject.Experiment2.NullSectorTask08.ThirdDirection`
* `RequestProject.Experiment2.NullSectorTask09.CentralPlane`
* `RequestProject.Experiment2.NullSectorTask09.Existence`
* `RequestProject.Experiment2.NullSectorTask09.RealScalarNoGo`
* `RequestProject.Experiment2.NullSectorTask09.Rigidity`
* `RequestProject.Experiment2.NullSectorTask09.SafeBase`
* `RequestProject.Experiment2.NullSectorTask09.UnknownQuadraticMap`
* `RequestProject.Experiment2.NullSectorTask10.AlgebraExtension`
* `RequestProject.Experiment2.NullSectorTask10.AxialDerivation`
* `RequestProject.Experiment2.NullSectorTask10.AxisDecomposition`
* `RequestProject.Experiment2.NullSectorTask10.HalfAngleSectors`
* `RequestProject.Experiment2.NullSectorTask10.InternalLift`
* `RequestProject.Experiment2.NullSectorTask10.OldAxialRotation`
* `RequestProject.Experiment2.NullSectorTask10.SafeBase`
* `RequestProject.Experiment2.NullSectorTask10.StateAction`
* `RequestProject.Experiment2.NullSectorTask10.VectorChannels`
* `RequestProject.Experiment2.NullSectorTask11.CenterRigidity`
* `RequestProject.Experiment2.NullSectorTask11.ContinuousClassification`
* `RequestProject.Experiment2.NullSectorTask11.ExactLiftClassification`
* `RequestProject.Experiment2.NullSectorTask11.FullLift`
* `RequestProject.Experiment2.NullSectorTask11.GeneratorSeparation`
* `RequestProject.Experiment2.NullSectorTask11.InfinitesimalLift`
* `RequestProject.Experiment2.NullSectorTask11.PeriodicityAudit`
* `RequestProject.Experiment2.NullSectorTask11.QuadraticCompatibility`
* `RequestProject.Experiment2.NullSectorTask11.ReferenceExistence`
* `RequestProject.Experiment2.NullSectorTask11.RelativeLiftRigidity`
* `RequestProject.Experiment2.NullSectorTask11.SafeBase`
* `RequestProject.Experiment2.NullSectorTask12.AxisRelation`
* `RequestProject.Experiment2.NullSectorTask12.CarrierEndomorphisms`
* `RequestProject.Experiment2.NullSectorTask12.CarrierFamily`
* `RequestProject.Experiment2.NullSectorTask12.CentralAction`
* `RequestProject.Experiment2.NullSectorTask12.DimensionClassification`
* `RequestProject.Experiment2.NullSectorTask12.GeneratedCarrier`
* `RequestProject.Experiment2.NullSectorTask12.HalfAngleRelation`
* `RequestProject.Experiment2.NullSectorTask12.LeftCarrier`
* `RequestProject.Experiment2.NullSectorTask12.LiftStability`
* `RequestProject.Experiment2.NullSectorTask12.MinimalCarrier`
* `RequestProject.Experiment2.NullSectorTask12.SafeBase`
* `RequestProject.Experiment2.NullSectorTask13.AutomorphismCarrierAction`
* `RequestProject.Experiment2.NullSectorTask13.CarrierIntertwiners`
* `RequestProject.Experiment2.NullSectorTask13.CarrierSlices`
* `RequestProject.Experiment2.NullSectorTask13.FixedCarrierLocus`
* `RequestProject.Experiment2.NullSectorTask13.FullLiftRestriction`
* `RequestProject.Experiment2.NullSectorTask13.InfinitesimalRestriction`
* `RequestProject.Experiment2.NullSectorTask13.MinusSectorHardening`
* `RequestProject.Experiment2.NullSectorTask13.ReferenceRestriction`
* `RequestProject.Experiment2.NullSectorTask13.ReferenceSectorAction`
* `RequestProject.Experiment2.NullSectorTask13.RelativeSectorAction`
* `RequestProject.Experiment2.NullSectorTask13.SafeBase`
* `RequestProject.Experiment2.NullSectorTask13.SelectionAudit`
* `RequestProject.Experiment2.NullSectorTask13.SliceCentralStructure`
* `RequestProject.Experiment2.NullSectorTask14.AxisGeneratorMap`
* `RequestProject.Experiment2.NullSectorTask14.CarrierFamilyAction`
* `RequestProject.Experiment2.NullSectorTask14.CarrierIntertwiners`
* `RequestProject.Experiment2.NullSectorTask14.CoherenceAudit`
* `RequestProject.Experiment2.NullSectorTask14.CommonFixedLocus`
* `RequestProject.Experiment2.NullSectorTask14.FullLiftDefect`
* `RequestProject.Experiment2.NullSectorTask14.GenericAxis`
* `RequestProject.Experiment2.NullSectorTask14.GenericTwoAxisComposition`
* `RequestProject.Experiment2.NullSectorTask14.ImplementerClosure`
* `RequestProject.Experiment2.NullSectorTask14.MixedFiniteComposition`
* `RequestProject.Experiment2.NullSectorTask14.MixedInfinitesimalComposition`
* `RequestProject.Experiment2.NullSectorTask14.MixedProjectors`
* `RequestProject.Experiment2.NullSectorTask14.ReferenceWordDefect`
* `RequestProject.Experiment2.NullSectorTask14.SafeBase`
* `RequestProject.Experiment2.NullSectorTask14.SecondAxisAutomorphism`
* `RequestProject.Experiment2.NullSectorTask14.SecondAxisCarrierSlices`
* `RequestProject.Experiment2.NullSectorTask14.SecondAxisImplementation`
* `RequestProject.Experiment2.NullSectorTask14.SecondAxisOldStructure`
* `RequestProject.Experiment2.NullSectorTask14.SecondAxisSectorAction`
* `RequestProject.Experiment2.NullSectorTask14.SelectionAudit`
* `RequestProject.Experiment2.NullSectorTask14.TwoAxisSliceComparison`
* `RequestProject.Experiment2.NullSectorTask15.DifferentiableLift`
* `RequestProject.Experiment2.NullSectorTask15.Infinitesimal`
* `RequestProject.Experiment2.NullSectorTask15.MixedComposition`
* `RequestProject.Experiment2.NullSectorTask15.RegularLift`
* `RequestProject.Experiment2.NullSectorTask15.SafeBase`
* `RequestProject.Experiment2.NullSectorTask16.ExactCoincidences`
* `RequestProject.Experiment2.NullSectorTask16.JointRegularity`
* `RequestProject.Experiment2.NullSectorTask16.LocalRepair`
* `RequestProject.Experiment2.NullSectorTask16.RegularDefect`
* `RequestProject.Experiment2.NullSectorTask16.SafeBase`
* `RequestProject.Experiment2.NullSectorTask16.TransformationValuedClosure`
* `RequestProject.Experiment2.NullSectorTask17.AdmissibleDomains`
* `RequestProject.Experiment2.NullSectorTask17.DomainGeometry`
* `RequestProject.Experiment2.NullSectorTask17.LocalExhaustion`
* `RequestProject.Experiment2.NullSectorTask17.OverlapTransitions`
* `RequestProject.Experiment2.NullSectorTask17.RateRigidity`
* `RequestProject.Experiment2.NullSectorTask17.Reconstruction`
* `RequestProject.Experiment2.NullSectorTask17.RegularityAudit`
* `RequestProject.Experiment2.NullSectorTask17.SafeBase`
* `RequestProject.Experiment2.NullSectorTask18.BridgeFactors`
* `RequestProject.Experiment2.NullSectorTask18.BridgeReconstruction`
* `RequestProject.Experiment2.NullSectorTask18.ConnectedAdmissibility`
* `RequestProject.Experiment2.NullSectorTask18.DisconnectedDomains`
* `RequestProject.Experiment2.NullSectorTask18.GlobalBridgeObstruction`
* `RequestProject.Experiment2.NullSectorTask18.MaximalDomains`
* `RequestProject.Experiment2.NullSectorTask18.NegativeControls`
* `RequestProject.Experiment2.NullSectorTask18.ReconstructionPredicates`
* `RequestProject.Experiment2.NullSectorTask18.RegularityAudit`
* `RequestProject.Experiment2.NullSectorTask18.RelationCoverage`
* `RequestProject.Experiment2.NullSectorTask18.SafeBase`
* `RequestProject.Experiment2.NullSectorTask19.DisconnectedExtension`
* `RequestProject.Experiment2.NullSectorTask19.HigherRegularity`
* `RequestProject.Experiment2.NullSectorTask19.MaximalPreconnected`
* `RequestProject.Experiment2.NullSectorTask19.MinimalObstruction`
* `RequestProject.Experiment2.NullSectorTask19.NegativeControls`
* `RequestProject.Experiment2.NullSectorTask19.PlainMaximality`
* `RequestProject.Experiment2.NullSectorTask19.PrimitiveBridge`
* `RequestProject.Experiment2.NullSectorTask19.RelationBridge`
* `RequestProject.Experiment2.NullSectorTask19.RelationCompletion`
* `RequestProject.Experiment2.NullSectorTask19.SafeBase`
* `RequestProject.Experiment2.NullSectorTask20.BridgeTorsor`
* `RequestProject.Experiment2.NullSectorTask20.GlobalObstruction`
* `RequestProject.Experiment2.NullSectorTask20.Identification`
* `RequestProject.Experiment2.NullSectorTask20.InternalProjection`
* `RequestProject.Experiment2.NullSectorTask20.LiftCarrier`
* `RequestProject.Experiment2.NullSectorTask20.NegativeControls`
* `RequestProject.Experiment2.NullSectorTask20.ReversalQuotient`
* `RequestProject.Experiment2.NullSectorTask20.SafeBase`
* `RequestProject.Experiment2.NullSectorTask20.SectionObstruction`
* `RequestProject.Experiment2.NullSectorTask20.VisibleQuotient`
* `RequestProject.Experiment2.NullSectorTask21.CentralComplex`
* `RequestProject.Experiment2.NullSectorTask21.CentralProduct`
* `RequestProject.Experiment2.NullSectorTask21.CoreProjection`
* `RequestProject.Experiment2.NullSectorTask21.CoreQuaternionEquiv`
* `RequestProject.Experiment2.NullSectorTask21.GroupPackaging`
* `RequestProject.Experiment2.NullSectorTask21.NegativeControls`
* `RequestProject.Experiment2.NullSectorTask21.NormalizedCentralCarrier`
* `RequestProject.Experiment2.NullSectorTask21.SU2Model`
* `RequestProject.Experiment2.NullSectorTask21.SafeBase`
* `RequestProject.Experiment2.NullSectorTask21.SectionObstruction`
* `RequestProject.Experiment2.NullSectorTask21.SignStructures`
* `RequestProject.Experiment2.NullSectorTask21.Task21`
* `RequestProject.Experiment2.NullSectorTask21.Task22`
* `RequestProject.Experiment2.NullSectorTask21.TorsorPlacement`
* `RequestProject.Experiment2.NullSectorTask21.VisibleRotationCandidate`
* `RequestProject.Experiment2.NullSectorTask23.Comparison`
* `RequestProject.Experiment2.NullSectorTask23.Cover`
* `RequestProject.Experiment2.NullSectorTask23.GlobalSection`
* `RequestProject.Experiment2.NullSectorTask23.Hierarchy`
* `RequestProject.Experiment2.NullSectorTask23.LocalProduct`
* `RequestProject.Experiment2.NullSectorTask23.OldBridges`
* `RequestProject.Experiment2.NullSectorTask23.OldDomains`
* `RequestProject.Experiment2.NullSectorTask23.Reconstruction`
* `RequestProject.Experiment2.NullSectorTask23.SafeBase`
* `RequestProject.Experiment2.NullSectorTask23.Sections`
* `RequestProject.Experiment2.NullSectorTask23.Task23`
* `RequestProject.Experiment2.NullSectorTask23.Transitions`
* `RequestProject.Experiment2.NullSectorTask24.Comparison`
* `RequestProject.Experiment2.NullSectorTask24.FrameTorsor`
* `RequestProject.Experiment2.NullSectorTask24.IntrinsicFrames`
* `RequestProject.Experiment2.NullSectorTask24.LiftedFrames`
* `RequestProject.Experiment2.NullSectorTask24.ReferenceIndependence`
* `RequestProject.Experiment2.NullSectorTask24.SafeBase`
* `RequestProject.Experiment2.NullSectorTask24.Task24`
* `RequestProject.Experiment2.NullSectorTask24.VisibleFrameAction`
* `RequestProject.Experiment2.NullSectorTask25.LiftedFrameAction`
* `RequestProject.Experiment2.NullSectorTask25.LiftedFrameEquivariance`
* `RequestProject.Experiment2.NullSectorTask25.OneFiberInterface`
* `RequestProject.Experiment2.NullSectorTask25.ReferenceTransferHardening`
* `RequestProject.Experiment2.NullSectorTask25.Task25`
* `RequestProject.Spine.Audit.Firewall`
* `RequestProject.Spine.E1.Bivector`
* `RequestProject.Spine.E1.Carrier`
* `RequestProject.Spine.E1.Clifford`
* `RequestProject.Spine.E1.CliffordHodgeBridge`
* `RequestProject.Spine.E1.Coords`
* `RequestProject.Spine.E1.Core`
* `RequestProject.Spine.E1.DoubleCover`
* `RequestProject.Spine.E1.Hodge`
* `RequestProject.Spine.E1.Hyperbolic`
* `RequestProject.Spine.E1.LieAlgebra`
* `RequestProject.Spine.E1.LorentzClifford`
* `RequestProject.Spine.E1.LorentzGroup`
* `RequestProject.Spine.E1.MatrixModel`
* `RequestProject.Spine.E1.Paravector`
* `RequestProject.Spine.E1.PauliRepresentation`
* `RequestProject.Spine.E1.SL2Comparison`
* `RequestProject.Spine.E1.Shell`
* `RequestProject.Spine.E1.ShellTransitivity`
* `RequestProject.Spine.E1.SpinDeterminant`
* `RequestProject.Spine.E1.SpinGroup`
* `RequestProject.Spine.E1.WeylSpinorModule`
* `RequestProject.Spine.E2.AtlasChange.AtlasChangeLiftability`
* `RequestProject.Spine.E2.AtlasChange.FamilyDefectNeutrality`
* `RequestProject.Spine.E2.AtlasChange.FamilyExistenceClassification`
* `RequestProject.Spine.E2.AtlasChange.FamilyLiftability`
* `RequestProject.Spine.E2.AtlasChange.OrdinaryAtlasChange`
* `RequestProject.Spine.E2.AtlasChange.OrdinaryAtlasEquivalence`
* `RequestProject.Spine.E2.AtlasChange.OrdinaryCoverRefinement`
* `RequestProject.Spine.E2.AtlasChange.Task32`
* `RequestProject.Spine.E2.AtlasChange.UnderlyingFrameGeometry`
* `RequestProject.Spine.E2.CentralDoubleCover`
* `RequestProject.Spine.E2.Core`
* `RequestProject.Spine.E2.Defect.DefectNeutrality`
* `RequestProject.Spine.E2.Defect.ExistenceClassification`
* `RequestProject.Spine.E2.Defect.FrameFamilyRealization`
* `RequestProject.Spine.E2.Defect.GlobalCoveringHardening`
* `RequestProject.Spine.E2.Defect.GlobalMapHardening`
* `RequestProject.Spine.E2.Defect.IntrinsicDefectState`
* `RequestProject.Spine.E2.Defect.LiftabilityPredicate`
* `RequestProject.Spine.E2.Defect.SpatialClosureInterface`
* `RequestProject.Spine.E2.Defect.Task31`
* `RequestProject.Spine.E2.Defect.UniversalExistenceAudit`
* `RequestProject.Spine.E2.Descent.ChoiceInvariance`
* `RequestProject.Spine.E2.Descent.CombinedCompatibility`
* `RequestProject.Spine.E2.Descent.CompatibleTransitions`
* `RequestProject.Spine.E2.Descent.DefectFreeHardening`
* `RequestProject.Spine.E2.Descent.Inherited`
* `RequestProject.Spine.E2.Descent.KernelAdjustment`
* `RequestProject.Spine.E2.Descent.PairwiseDescent`
* `RequestProject.Spine.E2.Descent.RefinementBehavior`
* `RequestProject.Spine.E2.Descent.SimultaneousTrivialisation`
* `RequestProject.Spine.E2.Descent.Task29`
* `RequestProject.Spine.E2.Family.FamilyBase`
* `RequestProject.Spine.E2.Family.FiberFrames`
* `RequestProject.Spine.E2.Family.FiberIsometryGroup`
* `RequestProject.Spine.E2.Family.FrameTotal`
* `RequestProject.Spine.E2.Family.FrameTrivialization`
* `RequestProject.Spine.E2.Family.LocalTrivialization`
* `RequestProject.Spine.E2.Family.TransitionData`
* `RequestProject.Spine.E2.Global.ConditionalGlobalInterface`
* `RequestProject.Spine.E2.Global.GlobalFrameProjection`
* `RequestProject.Spine.E2.Global.GlobalGlueBase`
* `RequestProject.Spine.E2.Global.InternalGlueRelation`
* `RequestProject.Spine.E2.Global.InternalGroupAction`
* `RequestProject.Spine.E2.Global.InternalQuotient`
* `RequestProject.Spine.E2.Global.InternalTopology`
* `RequestProject.Spine.E2.Global.KernelFibres`
* `RequestProject.Spine.E2.Global.LocalComparison`
* `RequestProject.Spine.E2.Global.OrdinaryFrameSideInstance`
* `RequestProject.Spine.E2.Global.PresentationIndependence`
* `RequestProject.Spine.E2.Global.Task30`
* `RequestProject.Spine.E2.Lift.KernelAmbiguity`
* `RequestProject.Spine.E2.Lift.LocalInternalRepresentatives`
* `RequestProject.Spine.E2.Lift.RepresentativeChange`
* `RequestProject.Spine.E2.Lift.TransitionLiftBase`
* `RequestProject.Spine.E2.Lift.TripleOverlapDefect`
* `RequestProject.Spine.E2.Model.CertifiedProjection`
* `RequestProject.Spine.E2.Model.InternalTransitionInterface`
* `RequestProject.Spine.E2.Model.ModelBridge`
* `RequestProject.Spine.E2.Model.Task28`
* `RequestProject.Spine.E2.Topology.AtlasExtension`
* `RequestProject.Spine.E2.Topology.AtlasTopology`
* `RequestProject.Spine.E2.Topology.ContinuousTransitions`
* `RequestProject.Spine.E2.Topology.FiberTopology`
* `RequestProject.Spine.E2.Topology.FrameRightAction`
* `RequestProject.Spine.E2.Topology.FrameTopology`
* `RequestProject.Spine.E2.Topology.ModelTopology`
* `RequestProject.Spine.E2.Topology.ReverseReconstruction`
* `RequestProject.Spine.E2.Topology.Task27`
* `RequestProject.Spine.E2.Topology.TopologicalFrameFamily`
* `RequestProject.Spine.Foundation.MinkowskiMatrix`


## Update after task 01 (topological qualification of the intrinsic Spin cover)

A new layer `Spine.E1.Topology.**` (six modules) sits above the intrinsic spin core and
below `Spine.E1.Core`, which re-exports its endpoint.  Project-local closures after the
pass (`python3 scripts/legacy_audit.py`):

| Endpoint | direct | project-local closure | legacy E1 | legacy E2 |
| --- | --- | --- | --- | --- |
| `Spine.E1.Topology.Core` (new) | 1 | 25 | 0 | 0 |
| `Spine.E1.Core` | 3 | 28 | 0 | 0 |
| `Spine.E1.SL2Comparison` | 2 | 22 | 0 | 0 |
| `Spine.E2.Core` | 1 | 65 | 0 | 0 |
| `Spine.Core` | 3 | 97 | 0 | 0 |

The new endpoint's closure contains none of `Spine.E1.MatrixModel`,
`Spine.E1.PauliRepresentation`, `Spine.E1.SL2Comparison`, `Spine.E1.WeylSpinorModule`,
`Spine.E2.**`, `Spine.Controls.**`, `Experiment1/**` or `Experiment2/**`; the compile-time
firewall checks each of its six modules individually.  The full dependency DAG of the layer,
the canonicality table and the classification of every property are in `TASK01_AUDIT.md`.

## Update after task 02 (local continuous sections and the native `InternalProjection`)

Three modules are added: `Spine.E1.Topology.LocalSection` (inside the E1 topology layer,
above `SpinCoverTopology` and below `Topology.Core`), and, above the generic interface,
`Spine.E2.SpinProjection` and `Spine.E2.SpinProjectionIntegration`.  The direction E1 → E2 is
preserved: the local-section theorem is proved in E1 and only consumed in E2.  Project-local
closures after the pass (`python3 scripts/legacy_audit.py`):

| Endpoint | direct | project-local closure | legacy E1 | legacy E2 |
| --- | --- | --- | --- | --- |
| `Spine.E1.Topology.Core` | 2 | 26 | 0 | 0 |
| `Spine.E1.Core` | 3 | 29 | 0 | 0 |
| `Spine.E1.SL2Comparison` | 2 | 22 | 0 | 0 |
| `Spine.E2.Core` | 1 | 65 | 0 | 0 |
| `Spine.E2.SpinProjection` (new) | 2 | 27 | 0 | 0 |
| `Spine.E2.SpinProjectionIntegration` (new) | 2 | 52 | 0 | 0 |
| `Spine.Core` | 5 | 100 | 0 | 0 |
| `Spine.Audit.Firewall` | 17 | 107 | 0 | 0 |

`Spine.E1.Topology.LocalSection` reaches none of `Spine.E1.MatrixModel`,
`Spine.E1.PauliRepresentation`, `Spine.E1.SL2Comparison`, `Spine.E1.WeylSpinorModule`,
`Spine.E2.**`, `Spine.Controls.**`, `Experiment1/**`, `Experiment2/**`; `Spine.E2.SpinProjection`
reaches exactly the intrinsic E1 chain plus the generic interface.  Both facts are checked at
compile time by `Spine.Audit.Firewall`.  The full DAG, the canonicality table and the
classification of every result are in `TASK02_AUDIT.md`.

---

## Task 3 — the Čech Spin-lift obstruction layer (`Spine.E2.Cech.**`)

Linear chain, each module importing only its predecessor:

```
Spine.E2.Lift.RepresentativeChange
  └── Spine.E2.Cech.Cover         WP2  CechCover, VisibleCocycle, CoverRefinement, pullback
        └── Spine.E2.Cech.LocalLifts   WP3  section criterion, local liftability, SpinLiftFamily
              └── Spine.E2.Cech.Defect       WP4/WP5  defect, kernel-valuedness, 2-cocycle law
                    └── Spine.E2.Cech.Coboundary   WP6  δ, change of local representatives
                          └── Spine.E2.Cech.Obstruction  WP7/WP8  class, vanishing ⇔ coherent
                                └── Spine.E2.Cech.Refinement  WP9  pullback, naturality
                                      └── Spine.E2.Cech.SpinInstance  WP10  native instantiation
                                            └── Spine.E2.Cech.Core     endpoint
```

`Spine.E2.Cech.SpinInstance` additionally imports `Spine.E2.SpinProjection`; every module
below it in the chain is free of any concrete projection (checked by the firewall).
`Spine.Core` imports `Spine.E2.Cech.Core`.  The control
`Spine.Controls.E2.CechObstructionControl` is downstream of the endpoint and imported by no
production module.

| Endpoint | direct | project-local closure | legacy E1 | legacy E2 |
| --- | --- | --- | --- | --- |
| `Spine.E2.Cech.Core` | 1 | 57 | 0 | 0 |
| `Spine.E2.Cech.SpinInstance` | 2 | 56 | 0 | 0 |
| `Spine.Core` | 6 | 108 | 0 | 0 |
| `Spine.Controls.E2.CechObstructionControl` | 1 | 58 | 0 | 0 |

Full classification of every Task-3 result: `TASK03_AUDIT.md`.

## Task-4 layer: `RequestProject.Spine.Geometry.**`

```
Spine.E1.Coords / Spine.E1.ShellTransitivity
  └── Spine.Geometry.CausalAlgebra    WP2/WP9  causal sign lemmas, GLor reduction criterion,
        │                                     orientation/time-orientation negative controls
        ├── Spine.E1.Topology.LorentzTopology
        ├── Spine.E2.Cech.Cover
        └── Spine.Geometry.FrameField        WP2/WP3  LorentzFrameData, GLor-valued
              │                                       frame transition cocycle
              └── Spine.Geometry.SpinStructure   WP4/WP5/WP8  obstruction instance,
                    │                                        SpinFrameStructure, torsor
                    ├── Spine.Geometry.Z2Class       WP7  canonical {±1} ≅ ℤ/2, additive
                    │                                     Čech presentation
                    └── Spine.Geometry.TangentInstance  WP1/WP3  genuine tangent spaces of a
                          │                                      smooth four-manifold
                          └── Spine.Geometry.Core        endpoint, axiom audit
                                └── Spine.Controls.Geometry.FlatFrameControl   (control only)
```

| Endpoint | direct | project-local closure | legacy E1 | legacy E2 |
| --- | --- | --- | --- | --- |
| `Spine.Geometry.FrameField` | 3 | 36 | 0 | 0 |
| `Spine.Geometry.SpinStructure` | 2 | 60 | 0 | 0 |
| `Spine.Geometry.TangentInstance` | 1 | 61 | 0 | 0 |
| `Spine.Geometry.Z2Class` | 1 | 61 | 0 | 0 |
| `Spine.Geometry.Core` | 2 | 63 | 0 | 0 |
| `Spine.Controls.Geometry.FlatFrameControl` | 1 | 62 | 0 | 0 |

Full classification of every Task-4 result, including what is blocked and why:
`TASK04_AUDIT.md`.

`Spine.Core` imports `Spine.Geometry.Core`, so the aggregate production endpoint now covers
the Task-4 layer as well.

## Task-5: the native mod-2 singular cohomology layer

```
Mathlib (TopCat, TopCat.toSSet, SimplexCategory, ZMod 2, Submodule)
  └── Spine.Cohomology.Cochain           WP2  singular simplices, faces, Cⁿ(X;ℤ₂)
        └── Spine.Cohomology.Coboundary  WP3  δ, δ² = 0 (from SimplexCategory.δ_comp_δ)
              ├── Spine.Cohomology.Cohomology      WP4  Zⁿ, Bⁿ, Bⁿ ⊆ Zⁿ, Hⁿ = Zⁿ/Bⁿ
              │     ├── Spine.Cohomology.Functorial        WP5  f*, δf* = f*δ, Hmap, functor laws
              │     └── Spine.Cohomology.AlexanderWhitney  WP6  front/back inclusions
              │           └── Spine.Cohomology.Cup         WP6  cup product, Leibniz rule
              │                 └── Spine.Cohomology.CupDescent  WP6  H¹×H¹→H², H²×H²→H⁴
              └── Spine.Cohomology.CechBridgeSpec  WP8  specification of the missing
                    │                                   Čech-to-singular comparison
                    │                                   (imports Spine.E2.Cech.Obstruction)
                    └── Spine.Cohomology.Core      endpoint, axiom audit
```

| Endpoint | direct | project-local closure | legacy E1 | legacy E2 | external |
| --- | --- | --- | --- | --- | --- |
| `Spine.Cohomology.Cochain` | 0 | 1 | 0 | 0 | 0 |
| `Spine.Cohomology.Coboundary` | 1 | 2 | 0 | 0 | 0 |
| `Spine.Cohomology.Cohomology` | 1 | 3 | 0 | 0 | 0 |
| `Spine.Cohomology.Functorial` | 1 | 4 | 0 | 0 | 0 |
| `Spine.Cohomology.Cup` | 1 | 5 | 0 | 0 | 0 |
| `Spine.Cohomology.CupDescent` | 2 | 7 | 0 | 0 | 0 |
| `Spine.Cohomology.CechBridgeSpec` | 2 | 36 | 0 | 0 | 0 |
| `Spine.Cohomology.Core` | 8 | 37 | 0 | 0 | 0 |

`Spine.Core` imports `Spine.Cohomology.Core`, so the aggregate production endpoint now covers
the Task-5 layer as well.  Remaining dependencies of the `w₂` certification branch:
`TASK05_AUDIT.md`, WP8–WP10.

## Task-6 layer — fixed-cover Čech `ℤ₂`-cohomology and the Spin-lift class

```
Mathlib (ZMod 2, Fin.succAbove, Submodule)
  └── Spine.Cech.Cochain              WP2  nerve, faces, Čⁿ(𝓤;ℤ₂)
        └── Spine.Cech.Coboundary     WP3  δ_Č, alternating formula, δ_Č² = 0
              └── Spine.Cech.Cohomology     WP4  Žⁿ, B̌ⁿ, B̌ⁿ ⊆ Žⁿ, Ȟⁿ = Žⁿ/B̌ⁿ
                    └── Spine.Cech.Refinement   WP11 r*, functor laws

Spine.E2.Cech.Cover ──┐
Spine.Cech.Refinement ┴── Spine.Cech.CoverNerve      Task-3 overlaps = nerve overlaps

Spine.E2.Cech.Coboundary ─── Spine.Cech.KernelSign   WP5  ker ρ ≅ ℤ₂ (data + MulEquiv)
Spine.Geometry.Z2Class ───── Spine.Cech.SpinKernelSign    WP5  Spin instance (reuses spinSign)

Spine.E2.Cech.Core + CoverNerve + KernelSign
  └── Spine.Cech.SpinCocycle          WP6–WP8, WP10  z, δ_Č z = 0, z' = z + δ_Č a,
        │                                            [z], vanishing ⇔ coherent lifts
        └── Spine.Cech.Comparison     WP9, WP11  toObstruction, injectivity,
              │                                  non-surjectivity, r*[z_𝓤] = [z_𝓥]
              └── Spine.Cech.SpinInstance        intrinsic Spin and Lorentz-frame instances
                    └── Spine.Cech.SingularBridgeSpec   WP12 (imports Spine.Cohomology.Core)
                          └── Spine.Cech.Core            endpoint, axiom audit
```

| Endpoint | direct | project-local closure | legacy E1 | legacy E2 | external |
| --- | --- | --- | --- | --- | --- |
| `Spine.Cech.Cochain` | 0 | 0 | 0 | 0 | 0 |
| `Spine.Cech.Coboundary` | 1 | 1 | 0 | 0 | 0 |
| `Spine.Cech.Cohomology` | 1 | 2 | 0 | 0 | 0 |
| `Spine.Cech.Refinement` | 1 | 3 | 0 | 0 | 0 |
| `Spine.Cech.CoverNerve` | 2 | 28 | 0 | 0 | 0 |
| `Spine.Cech.KernelSign` | 2 | 30 | 0 | 0 | 0 |
| `Spine.Cech.SpinKernelSign` | 2 | 65 | 0 | 0 | 0 |
| `Spine.Cech.SpinCocycle` | 3 | 64 | 0 | 0 | 0 |
| `Spine.Cech.Comparison` | 1 | 65 | 0 | 0 | 0 |
| `Spine.Cech.SpinInstance` | 2 | 71 | 0 | 0 | 0 |
| `Spine.Cech.SingularBridgeSpec` | 2 | 81 | 0 | 0 | 0 |
| `Spine.Cech.Core` | 11 | 82 | 0 | 0 | 0 |

`Spine.Core` imports `Spine.Cech.Core`, so the aggregate production endpoint covers the Task-6
layer as well.  Remaining dependency of the certification branch: the comparison
`Ȟ²(𝓤;ℤ₂) → H²_sing(X;ℤ₂)` specified in `Spine.Cech.SingularBridgeSpec` (see `TASK06_AUDIT.md`,
§6 and §10).

## Task 7 — the good-cover layer

```
Mathlib only
  └── Spine.GoodCover.Presimplicial            abstract presimplicial ℤ₂ complex, δ² = 0

Spine.Cech.Cochain
  └── Spine.GoodCover.GoodCover                IsGoodCover, contractible ⇒ … ⇒ preconnected

Spine.GoodCover.Presimplicial + Spine.Cech.Cohomology
  └── Spine.GoodCover.NerveIdentification      Ȟⁿ(𝓤;ℤ₂) = Hⁿ_simp(N(𝓤);ℤ₂)   (identity)

Spine.Cohomology.Cohomology
  └── Spine.GoodCover.PointCohomology          Hⁿ⁺¹_sing(point;ℤ₂) = 0

Spine.GoodCover.GoodCover + Spine.GoodCover.PointCohomology
  └── Spine.GoodCover.AcyclicCover             IsAcyclicCover (kept apart from IsGoodCover)

Spine.GoodCover.GoodCover + Spine.Geometry.TangentInstance
  └── Spine.GoodCover.ManifoldCovers           SLC, contractible open covers, HasGoodCover

Spine.GoodCover.AcyclicCover + Spine.Cech.SpinInstance
  └── Spine.GoodCover.Constancy                good cover ⇒ ConstOn₂/ConstOn₃; WP13 injectivity

  └── Spine.GoodCover.SingularComparisonSpec   WP6/WP8/WP9 hypotheses ⇒ Φ_𝓤, spinLiftSingularClass,
        │                                      vanishing ⇔ Spin structure, refinement invariance
        └── Spine.GoodCover.W2Interface        WP14 interface (w₂ is *not* defined)
              └── Spine.GoodCover.Core         endpoint, axiom audit
```

`Spine.Core` imports `Spine.GoodCover.Core`.  Remaining dependencies of the certification
branch, all named and none assumed: homotopy invariance of the Task-5 theory, the nerve theorem,
the simplicial-to-singular comparison, good-cover existence, and common good refinements
(`TASK07_AUDIT.md`, §§6–12 and §15).

## Update after Task 08 (native homotopy invariance, comparison-interface hardening)

Six modules were added; none of them reaches a historical experiment tree or any external
project.  Project-local closures (`scripts/dep_stats.py`):

| Module | direct | transitive | legacy E1 | legacy E2 |
| --- | --- | --- | --- | --- |
| `Spine.Cohomology.CharTwo` | 1 | 2 | 0 | 0 |
| `Spine.Cohomology.PrismMaps` | 1 | 1 | 0 | 0 |
| `Spine.Cohomology.Prism` | 3 | 6 | 0 | 0 |
| `Spine.Cohomology.HomotopyInvariance` | 2 | 8 | 0 | 0 |
| `Spine.GoodCover.GoodCoverAcyclic` | 2 | 12 | 0 | 0 |
| `Spine.GoodCover.HardenedSpec` | 2 | 96 | 0 | 0 |
| `Spine.Core` (endpoint) | 10 | 151 | 0 | 0 |

### The certification DAG, Čech → singular, after Task 8

```
  native Spin cover → local lifts → Čech Spin-lift class → Ȟ²(𝓤;ℤ₂)        [PROVED, Task 6]
                                                              ‖
                                              (identity, Task 7 WP5)
                                                              ‖
                                                  H²_simp(N(𝓤);ℤ₂)
                                                              │
                                        BLOCKED: simplicial → singular comparison
                                        specification hardened in Task 8 (WP13)
                                                              ▼
                                                  H²_sing(|N(𝓤)|;ℤ₂)
                                                              │
                                        UNBLOCKED IN TASK 8: native homotopy invariance
                                        (given a nerve equivalence, which is the other
                                         blocked edge, hardened in Task 8 WP12)
                                                              ▼
                                                  H²_sing(M;ℤ₂)
```

Exactly one major blocked edge — homotopy invariance — was removed.  The remaining blocked
edges are the nerve theorem and the simplicial-to-singular comparison; existence of good covers
and of common good refinements remain open from Task 7.  Details in `TASK08_AUDIT.md`.

---

## Task 9 — the canonical simplicial cover nerve, its realization, and the geometric comparison

### New modules

| module | direct project imports | project-local closure | E1 imports | E2 imports |
| --- | --- | --- | --- | --- |
| `Spine.Nerve.CoverNerveSSet` | 1 | 6 | 0 | 0 |
| `Spine.Nerve.CochainComparison` | 1 | 7 | 0 | 0 |
| `Spine.Nerve.Realization` | 2 | 11 | 0 | 0 |
| `Spine.Nerve.ChainMap` | 1 | 12 | 0 | 0 |
| `Spine.Nerve.CochainMap` | 1 | 13 | 0 | 0 |
| `Spine.Nerve.ComparisonSpec` | 2 | 103 | 0 | 0 |
| `Spine.Nerve.Core` (endpoint) | 6 | 104 | 0 | 0 |

(These are the figures printed by `RequestProject.Spine.Audit.Firewall`, which now reports on
all seven modules.)

### Internal edges

```
Spine.GoodCover.NerveIdentification
        │
        ▼
Spine.Nerve.CoverNerveSSet        (full SSet: faces = CechZ2.face, degeneracies = vertex repetition)
        │
        ▼
Spine.Nerve.CochainComparison     (underlyingPresimplicial ∘ coverNerveSSet = NerveZ2.coverNerve, rfl)
        │
        ├── Spine.Cohomology.Cohomology
        ▼
Spine.Nerve.Realization           (|N(𝓤)| = SSet.toTop.obj …; charSimplex from the adjunction unit)
        │
        ▼
Spine.Nerve.ChainMap              (J, ∂J = J∂)
        │
        ▼
Spine.Nerve.CochainMap            (J*, J*δ = δJ*, geometricHmap)
        │
        ├── Spine.GoodCover.HardenedSpec
        ▼
Spine.Nerve.ComparisonSpec        (GeometricComparison [BLOCKED], NerveTheoremData [BLOCKED],
                                   canonicalNervePresentation [CONSTRUCTED], Spin-class transport)
        │
        ▼
Spine.Nerve.Core  ──►  Spine.Core
```

### The certification DAG, Čech → singular, after Task 9

```
  native Spin cover → local lifts → Čech Spin-lift class → Ȟ²(𝓤;ℤ₂)        [PROVED, Task 6]
                                                              ‖
                                          (identity, Task 7 WP5 = Task 9 WP3)
                                                              ‖
                                                  H²_simp(N(𝓤);ℤ₂)
                                                              ▲
                            CONSTRUCTED IN TASK 9: the canonical geometric comparison
                            |σ| (WP5) → J (WP6) → J* (WP7) → geometricHmap
                                                              │
                                        BLOCKED: geometricHmap is bijective (WP8/WP9)
                                                              ▼
                                                  H²_sing(|N(𝓤)|;ℤ₂)
                                                              │
                          BLOCKED: nerve theorem, now in the genuine shape |N(𝓤)| ≃ M
                          (NerveGeom.NerveTheoremData; hypotheses itemised in WP14)
                                                              │
                          then automatically: Task-8 homotopy invariance [PROVED]
                                                              ▼
                                                  H²_sing(M;ℤ₂)
```

The arrow between the simplicial and the singular cohomology of the realization was *absent*
before Task 9 (only a hypothesised isomorphism existed); it is now a constructed canonical map,
and only its bijectivity is open.  Existence of good covers and of common good refinements
remain open from Task 7.  Details in `TASK09_AUDIT.md`.

---

# Task 10 — updated certification DAG (2026-09-08)

## Correction to the recorded assumption status (WP0)

Any earlier statement in this file, in `TASK09_AUDIT.md`, or in
`RequestProject/Spine/Nerve/ComparisonSpec.lean` to the effect that the Task-4 manifold layer
supplies Hausdorffness, second countability, paracompactness, metrisability, numerability of an
arbitrary cover, or a good cover is **withdrawn**.  Task 4 assumes only

```
[TopologicalSpace M]  [ChartedSpace LorentzCarrier M]  (+ [IsManifold carrierModel ⊤ M])
```

and none of those properties follows.  The implication "charted on the four-dimensional
carrier ⟹ second countable" is refuted at theorem level by
`SpineTask10.not_secondCountable_of_charted`
(`RequestProject/Spine/Nerve/ManifoldAssumptionAudit.lean`).  Nothing was added to Task 4.

## The fixed-cover certification DAG after Task 10

```
  Spin-lift family on the fixed cover
            │  (Task 6, THEOREM)
            ▼
  [z] ∈ Ȟ²(𝓤;ℤ₂)
            ║  Task 9: EQUALITY of complexes
            ║  Ȟⁿ(𝓤;ℤ₂) = Hⁿ_simp(N(𝓤);ℤ₂)      (cechCohomologyEquivSSet)
            ▼
  Hⁿ_simp(N(𝓤);ℤ₂)
            ▲
            │  geometricHmap 𝓤 n                (Task 9, CONSTRUCTED canonical map)
            │      = descent of  J* = dualOf J   (Task 10, dualOf_chainMap)
            │      with  J = C_*(η_K)            (Task 10, chainMap_eq_unitChainMap)
            │
  Hⁿ_sing(|N(𝓤)|;ℤ₂)
            ▲
            ┊  ONE remaining edge:
            ┊  ChainComparisonStatement 𝓤  :=  Nonempty (ChainHomotopyEquivData 𝓤)
            ┊     "J is a chain-homotopy equivalence"                     BLOCKED
            ┊
            ┊  Task 10 THEOREM:
            ┊  ChainHomotopyEquivData 𝓤 ⟹ ∀ n, Bijective (geometricHmap 𝓤 n)
            ┊     (geometricHmap_bijective_of_chainHomotopyEquiv)
            ┊  ChainHomotopyEquivData 𝓤 ⟹ GeometricComparison 𝓤
            ┊     (ChainHomotopyEquivData.toGeometricComparison)
            ▼
  Hⁿ_sing(M;ℤ₂)
            ▲
            ┊  nerve theorem  |N(𝓤)| ≃ M        BLOCKED, SEPARATE PROBLEM (untouched)
            ┊  then Task 8 homotopy invariance   THEOREM
```

## What changed relative to the Task-9 DAG

* The edge `Hⁿ_sing(|N(𝓤)|;ℤ₂) → Hⁿ_simp(N(𝓤);ℤ₂)` is unchanged as a map — it is still the
  Task-9 `geometricHmap` — but its *justification requirement* has moved one level down: it is
  no longer a cohomology-level assumption but a consequence of a chain-level statement about the
  same canonical map.
* `NerveGeom.GeometricComparison` is now `SUPERSEDED_BY_TASK10_CHAIN_COMPARISON` **as an input**:
  it is derivable from `ChainHomotopyEquivData` and should no longer be assumed directly.  It is
  retained because the Task-9 Spin-transport declarations are phrased with it.
* The realised Spin-lift class `[z]_{|N|} ∈ H²_sing(|N(𝓤)|;ℤ₂)` remains **conditional**, now on
  `ChainComparisonStatement` alone
  (`spinLiftRealizedClassOfChain_eq_zero_iff_cech`, `spinLiftRealizedClassOfChain_eq_zero_iff`).
* The nerve theorem edge is untouched and remains independent of the comparison edge.

## Task-10 module DAG

```
RequestProject.Spine.Nerve.CochainMap
        └── UnitChainMap                  (WP2: J = C_*(η_K))
                └── Dualization           (explicit transpose; dualOf ∂ = δ, dualOf J = J*)
                        └── ChainHomotopyComparison
                                          (WP5/WP7/WP10: chain datum ⟹ geometricHmap bijective)
RequestProject.Spine.Geometry.TangentInstance
        └── ManifoldAssumptionAudit       (WP0: counterexample to second countability)
all four ─── RequestProject.Spine.Nerve.Core   (endpoint, axiom audit)
```

Details, route matrix and negative-result statement: `TASK10_AUDIT.md`.

---

## Task 11 (2026-09-09) — upstream delta audit, corrections and the proposed Task-12 DAG

Task 11 added no mathematics.  Module delta:

```
RequestProject.Spine.Nerve.UnitChainMap
        └── Task11Probe                   (WP14 compile probes; nothing consumes it)
                └── RequestProject.Spine.Nerve.Core   (axiom audit only)
```

### Corrected logical status of the comparison edge

```
ChainComparisonStatement 𝓤          -- preferred *stronger* sufficient endpoint
        ⟹ GeometricComparison 𝓤     -- Task-9 cohomology-level specification
        ⟹ ∀ n, Bijective (geometricHmap 𝓤 n)   -- route-independent target
```

No converse is proved.  `ChainHomotopyEquivData` is therefore a **stronger**, not a weaker,
sufficient condition, and the compact-support theorem is **route-specific** to the
Acyclic-Models route.

### Proposed Task-12 DAG (native; upstream Mathlib supplies none of it)

```
T12.1 colimit description of |S| over finite subcomplexes
   └── T12.2 compact supports: σ : Δⁿ_top → |S| factors through |L|, L finite   ← Task 12 scope
T12.3 natural ℤ₂-chain contraction of C_*^sing(|Δ[n]|)                          (later task)
T12.4 freeness of both functors on the models                                    (later task)
T12.5 acyclic-models comparison over SSet, mod 2                                 (later task)
T12.6 assembly ⟹ NerveGeom.ChainComparisonStatement 𝓤                            (later task)
T12.7 geometricHmap_bijective_of_chainHomotopyEquiv                              ALREADY PROVED
```

Details, provenance and the decision matrix: `TASK11_UPSTREAM_DELTA_AUDIT.md`.

# Task 12 addendum (2026-09-09) — the Acyclic-Models route is closed; Route C replaces it

Task 12 added one leaf module, `RequestProject/Spine/Nerve/Task12Probe.lean`, whose only
project-local imports are `Nerve.UnitChainMap` and `Cohomology.HomotopyInvariance`.  Nothing
consumes it; the production closure figures above are unchanged, and the firewall still reports
`Experiment1 = Experiment2 = external-project imports = 0` (direct and transitive).

```
RequestProject.Spine.Nerve.UnitChainMap
RequestProject.Spine.Cohomology.HomotopyInvariance
        └── Task12Probe          (route-gate probes; nothing consumes it)
```

## Status of the Task-11 "Proposed Task-12 DAG"

The proposal recorded at the end of the Task-11 section is now **superseded**, by proof:

| item | Task-11 proposal | Task-12 outcome |
| --- | --- | --- |
| `T12.1` colimit description of `\|S\|` | prerequisite | still absent at the pin; belongs to Route K/L5 |
| `T12.2` compact supports | Task-12 scope | `ROUTE_SPECIFIC_BLOCKER`; needed only as the *last* step of the selected route, not for acyclic models |
| `T12.3` chain contraction of `C_*^sing(\|Δ[n]\|)` | later task | still classical-only; the cohomological form is now **proved** (`singularCohomology_stdSimplex_vanishing`) |
| `T12.4` freeness of **both** functors on the models | later task | **refuted for `G`** (`singularGenerator_not_surjective`); proved for `F` (`freeOnStdSimplex_bijective`) |
| `T12.5` acyclic-models comparison over `SSet` | later task | **`ROUTE_REJECTED`** — the hypothesis of `T12.4` is false, and no model class repairs it |
| `T12.6` assembly ⟹ `ChainComparisonStatement 𝓤` | later task | unchanged target, now to be reached by Route C |
| `T12.7` `geometricHmap_bijective_of_chainHomotopyEquiv` | already proved | unchanged |

## Selected successor DAG (Route C — skeletal/cellular)

```
L0  owned: J = C_*(η_K), dualisation, geometricHmap                       [Task 10]
    owned: mod-2 singular cohomology + homotopy invariance                 [Task 8]
    owned: F free & acyclic on Δ[n], |Δ[n]| contractible, ∂Δ[2] not acyclic[Task 12]
    owned: SSet.skeleton / SSet.Subcomplex / SSet.Finite                   [pin]
L1a relative simplicial mod-2 chains of a pair (K, K'), K' a subcomplex
L1b relative singular mod-2 chains of a pair (X, A)
L2  long exact sequence of a pair, both theories        (pure homological algebra)
L3a H_*(Δ[r], ∂Δ[r]) and H_*(|Δ^r|, |∂Δ^r|), free on the r-simplices
L3b excision / good-pair identification of H_*(|K^(r)|, |K^(r-1)|)     (hardest input)
L4  five lemma + induction on r                     ⟹ J iso on each skeleton
L5  compact support ⟹ pass to the colimit           (the Route-K ingredient)
L6  assembly ⟹ ChainComparisonStatement 𝓤 ⟹ geometricHmap 𝓤 n bijective  [L6⇒ owned]
```

L1a, L1b and L2 are independent of new topology and can start immediately; L3b should be scoped
before L3a/L4.  Details, matrices and the decision gate: `TASK12_ACYCLIC_MODELS_APPLICABILITY.md`.

## Task-14 update — topology-side DAG after the specialized cell-attachment task

Status of the Route-C levels after Task 14 (details, route audit and the hard decision:
`TASK14_SPECIALIZED_CELL_ATTACHMENT.md`):

| level | Task-12 plan | Task-14 status |
| --- | --- | --- |
| `L1a` relative simplicial chains of a subcomplex pair | to build | **done** — `SpineTask14.relChainCx`, `relSimpSC_shortExact` |
| `L1b` relative singular chains of a topological pair | to build | **done** — `relSingChainCx`, `relSingSC_shortExact` (needs the pair map injective) |
| `L2` long exact sequence of a pair | pure algebra | **done** — `pairDelta`, `pair_exact₁/₂/₃`, `pairDelta_naturality` |
| *(new)* skeletal cell attachment `K^(r) = K^(r-1) ∪ cells` | not scoped | **done** — `skelPiece_bijective`, `attachExtend*` (upstream `TODO`) |
| *(new)* realization carries the pushout | not scoped | **done** — `realizationPreservesColimits`, `toTop_isPushout` |
| *(new)* middle five lemma `τ₂` | not scoped | **done** — `isIso_homologyMap_τ₂`, `quasiIso_τ₂` (upstream `TODO`) |
| *(new)* canonical relative comparison induced by `J` | not scoped | **done** — `relJ`, `relJ_tau₂`, `relJ_generator` |
| `L4` five lemma + one skeleton step | to build | **done as an implication** — `oneSkeletonStep` |
| `L3a` `H_*(\|Δ[r]\|, \|∂Δ[r]\|)` | to build | **BLOCKED** — blocker `B1` |
| `L3b` excision / good pair for `H_*(\|K^(r)\|, \|K^(r-1)\|)` | hardest input | **BLOCKED** — blocker `B3`; decision `B: FULL EXCISION IS REQUIRED` |
| *(new)* `\|A\| → \|X\|` injective for `A ⊆ X` | not scoped | **BLOCKED** — blocker `B2`, independent of excision |
| `L5` compact support / colimit | deferred | unchanged, deferred |
| `L6` assembly ⟹ `geometricHmap` bijective | owned | unchanged |

Critical path now:

```
small-simplices theorem (barycentric subdivision + Lebesgue number + chain homotopy)
      └─▶ excision ─▶ B1 ─▶ B3 ─┐
                                 ├─▶ oneSkeletonStep becomes unconditional ─▶ L5 ─▶ L6
   realization of a mono is injective (B2) ──────┘
```

---

## Task 15 addendum

New modules and their place in the DAG (full detail in `TASK15_AUDIT.md`, §11):

```
Task13Skeletal ─▶ Task14SkeletalAttachment ─┐
Task14RelativeChains ─▶ Task14RelativeLES ─▶ Task14Comparison ─▶ Task14Blocker
                                                                     │
                                     Task15Pushout ◀─────────────────┘
                                          │      (skeletalIsPushout, …_toTop, …_toTop_coprod)
                                          ▼
                                 Task15RealizationMono
                                          │      (StandardCellMono, realization_skInc_injective,
                                          │       oneSkeletonStep_of_standardCell,
                                          │       standardCellMono_zero)
                                          ▼
                                    Task15BaseCase
                                                 (baseCase, skeletalInduction,
                                                  finiteDimensional_homologyIso)
```

Open leaves after Task 15: `SpineTask15.StandardCellMono r` (for `r ≥ 1`) and
`SpineTask14.RelJIsIso`.  Everything else on the path from the skeletal attachment to
"finite-dimensional `J` is a quasi-isomorphism" is proved.

---

## Task 16 addendum

```
Task15Pushout ─▶ Task15RealizationMono ─▶ Task16PointModel ─▶ Task16Consequences
                                              │                     │
   (StandardCellMono, reduction)              │                     └─▶ Task16AxiomAudit
                                              │
      exists_representative (Level A)  ───────┤
      coord / coord_naturality (WP4)   ───────┤
      subNormalForm / normalForm (WP2/3) ─────┤
      subcomplexMono, standardCellMono (WP6/7)┘
```

Status change: the leaf `SpineTask15.StandardCellMono r` is **closed**
(`SpineTask16.standardCellMono`).  Therefore

* `|K^{(r-1)}| → |K^{(r)}|` injective — **PROVED** for every `K`, every `r`
  (`SpineTask16.realization_skInc_injective`), i.e. blocker `B2` is gone;
* the entry "`|A| → |X|` injective for `A ⊆ X`" is proved in the case `X = Δ[r]`
  (`SpineTask16.subcomplexMono`); for general `X` it remains open;
* `SpineTask16.skeletalInduction` and `SpineTask16.finiteDimensional_homologyIso` now carry
  exactly one hypothesis, `SpineTask14.RelJIsIso`.

Critical path after Task 16:

```
H_q^{sing}(|Δ[r]|, |∂Δ[r]|; ℤ₂)  (standard-cell homology + top generator)
      └─▶ RelJIsIso ─▶ skeletalInduction / finiteDimensional_homologyIso unconditional
                     ─▶ L5 ─▶ L6
```

Only open leaf on that path: `SpineTask14.RelJIsIso` (blocker `B1`/`B3`).  See
`TASK16_AUDIT.md` §16 for its three precise missing Lean-level inputs.

---

## Task 27 addendum — blocker `B3` closed for an arbitrary cell family

```
AlgebraicTopology.DirectSumComplex ─▶ AlgebraicTopology.DirectSumHomology
                                                 │
                                                 ▼
                            Nerve.CellFamily.RelativeChainDecomposition
                                                 │  (isIso_sumCellHomology, no Fintype)
                                                 ▼
                              Nerve.CellFamily.TargetDecomposition
                                                 │  (isIso_tgtDecomp, no Fintype)
                                                 ▼
                                   Nerve.Comparison.RelJ
                                        (relJIsIso : SpineTask14.RelJIsIso X r)
```

Status change: the leaf `SpineTask14.RelJIsIso` is **closed** for every simplicial set and
every `r` (`SpineTask24.relJIsIso`), with no finiteness hypothesis on `X.nonDegenerate r`.  The
new generic input is

```
SpineTask23.isIso_sumHomologyMap_finsuppCxι :
    H_q(⊕_{α} C) ≅ ⊕_{α} H_q(C)   for an arbitrary index type α,
```

proved from the finite support of the chains of the direct sum; see `TASK27_AUDIT.md`.

`Nerve.Comparison.FiniteRelJ` was renamed `Nerve.Comparison.RelJ`; the finite forms
(`isIso_tgtDecomp_finite`, `relJIsIso_finite`, …) are retained there as wrappers.

Next mathematical edge on this path: the global skeletal assembly / canonical
simplicial–singular comparison (`skeletalInduction`, `finiteDimensional_homologyIso`), which
still carries `SpineTask14.RelJIsIso` as an explicit hypothesis; discharging it is deliberately
*not* part of Task 27.

---

## Addendum (Task 29): the global comparison layer

The Stage-1.3 spine is now closed up to and including the canonical cohomological comparison.
The dependency order above `RelJ` is

```
Nerve.Comparison.RelJ                       (blocker B3, arbitrary cell family)
        ↓
Nerve.Comparison.GlobalHomology             globalHomologyIso : ∀ K q, IsIso H_q(C_*(η_K))
        ↓
Nerve.Comparison.GlobalCohomology           geometricHmap 𝓤 n bijective; GeometricComparison 𝓤
```

with two further inputs feeding `GlobalHomology`, both unconditional:

```
Nerve.Geometry.SkeletalFactorization        a compact domain factors through a finite skeleton
        ↓
Nerve.Skeleton.SkeletalSupport              skeletalSupport : ∀ K, SkeletalSupport K
```

and two new generic modules feeding `GlobalCohomology`, neither of which mentions simplicial
sets, nerves or geometry:

```
AlgebraicTopology.NaiveHomology             categorical ↔ elementary homology dictionary
AlgebraicTopology.DualCohomology            transpose of a ℤ₂-quasi-isomorphism is a
                                            cohomology isomorphism (also hosts `dualOf`,
                                            re-exported by Nerve.Cochain.Dualization)
```

Status change: `SpineTask14.RelJIsIso`, the global homology comparison and the canonical
cohomology comparison are all closed; `NerveGeom.GeometricComparison 𝓤` is available
unconditionally (`NerveGeom.geometricComparison`).  The remaining Stage-1.3 edge is the genuine
Nerve Theorem `|N(𝓤)| ≃ M` for the actual good cover, which is *not* part of Task 29.
See `TASK29_AUDIT.md`.

---

## Task 30 addendum — the Spin-native provenance branch

The Stage-1.3 obstruction area now has two explicitly separated branches meeting in a single
leaf comparison module.

```
                     Spin/Lorentz foundation
                   (E1 SpinGroup / spinCover,
                    E2 InternalProjection, E2.Cech.Cover)
                          /                \
                         /                  \
        Branch A: SO-control            Branch B: Spin-native
        E2.Cech.LocalLifts              SpinNative.TransitionData
        E2.Cech.Defect                  SpinNative.Projection
        E2.Cech.Coboundary
        E2.Cech.Obstruction
        Geometry.SpinStructure
                         \                  /
                          \                /
                     Comparison.SpinNativeVsSO   (leaf)
```

New import edges (six in total): `SpinNative.TransitionData → E2.Cech.Cover`;
`SpinNative.Projection → SpinNative.TransitionData`; `Comparison.SpinNativeVsSO →
{SpinNative.Projection, E2.Cech.Obstruction, Geometry.SpinStructure}`; and
`Audit.ArchitectureDAG → Comparison.SpinNativeVsSO` (audit only, not production).

Firewall: `Spine.SpinNative.*` reaches no defect/coboundary/obstruction/refinement/geometry/
nerve/controls module; no production module reaches `Spine.Comparison.*`; both directions are
checked mechanically in `Spine/Audit/ArchitectureDAG.lean` (check 7).  Maximum internal import
depth unchanged at 67.  Status: the projected-obstruction triviality
(`SpinNative.projected_obstruction_trivial_of_lifts`) is closed; the standard branch is
unchanged; the genuine Nerve Theorem and the `w₂(TM)` identification remain open.
See `TASK30_PROVENANCE.md` and `TASK30_AUDIT.md`.

## Tasks 32–34 addendum: the emergence and tangent/solder branches (2026-09-12)

```text
Spine.E1.SpinCover
   └── Spine.Emergent.LocalModel
        └── Spine.Emergent.BaseGluing
             └── Spine.Emergent.Reconstruction
                  └── Spine.Emergent.Symmetric
                       ├── Spine.Emergent.NonDerivability ── Spine.Emergent.LocalPieceData
                       ├── Spine.Emergent.SymmetricCanonical ─┐
                       ├── Spine.Emergent.CoverAdapter        │  (also ← Spine.E2.Cech.Cover)
                       └── Spine.Emergent.SmoothGate          │
                            └── Spine.Emergent.SmoothStructure┴── Spine.Emergent.SymmetricSmooth
                                 └── Spine.Emergent.TangentTransition        (Task 34)
                                      └── Spine.Solder.InternalLorentz       (also ← Spine.E2.SpinProjection,
                                           └── Spine.Solder.Independence      Spine.SpinNative.Projection,
                                                └── Spine.Solder.Solder       Spine.Emergent.CoverAdapter)
                                                     └── Spine.Solder.LorentzBundle

Spine.Solder.Solder + Spine.Geometry.TangentInstance
   └── Spine.Comparison.SolderTangentGate            (leaf; the only join of the two branches)
```

Endpoints of the Task-34 branch: `EmergentBase.BaseGluingData.tangentTransition_eq_derivative_baseTransition`,
`SpinNative.tangent_spin_base_data_do_not_force_transition_identification`,
`SpinNative.TangentSolderData` with `tangentMetric_isLorentz` and `exists_gauge`,
`SpinNative.internalLorentzBundleCore`, and
`SpinNative.TangentSolderData.solder_tangent_certificate`.

## Task 35 addendum: the regularity / bundle-equivalence layer (2026-09-12)

Task 35 first **repaired** the Task-34 edge shown above: `Spine.Solder.InternalLorentz` no
longer imports `Spine.Emergent.TangentTransition` (nothing in it needs tangent geometry), and
`Spine.Solder.Independence` imports the two branches directly.  The two branches are therefore
independent in the import graph, not only in prose, and the architecture audit forbids the old
edge mechanically.

```text
Spine.Emergent.SmoothStructure
   └── Spine.Emergent.TangentTransition ─────────────────┐   (actual atlas → tangent transition)
                                                         │
Spine.Emergent.CoverAdapter, Spine.SpinNative.Projection,│
Spine.E2.SpinProjection                                  │
   └── Spine.Solder.InternalLorentz ─────────────────────┤   (native Spin → projected Lorentz)
                                                         │
                       Spine.Solder.Independence ◀───────┘
                            └── Spine.Solder.Solder
                                 └── Spine.Solder.LorentzBundle
                                      └── Spine.Solder.RegularSolder           (Task 35)
                                           ├── Spine.Solder.RegularExamples
                                           │      └── Spine.Solder.WeakInsufficiency
                                           └── Spine.Solder.BundleEquivalence
                                                  └── Spine.Solder.SmoothMetric
                                                       └── Spine.Solder.OrientationTime
                                                            └── Spine.Solder.RegularGauge

Spine.Solder.RegularGauge + Spine.Solder.WeakInsufficiency + Spine.Comparison.SolderTangentGate
   └── Spine.Comparison.SmoothSolderGate                 (leaf; second join of the two branches)
```

Endpoints of the Task-35 layer:
`SpinNative.SmoothTangentSolderData`, `SolderBundle.CoreBundleEquiv`,
`SpinNative.smooth_solder_iff_regular_bundle_equivalence`,
`SpinNative.SmoothTangentSolderData.smooth_tangent_lorentz_metric`,
`SpinNative.weak_solder_not_regular`,
`SpinNative.SmoothTangentSolderData.orientation_time_orientation_status`,
`SpinNative.SmoothTangentSolderData.regular_solder_torsor`,
`SpinNative.SmoothTangentSolderData.spin_endpoint_topological`, and the principal certificate
`SpinNative.SmoothTangentSolderData.smooth_solder_tangent_certificate`.

Audit (`Spine/Audit/ArchitectureDAG.lean`): `Task-34/35 tangent/solder firewall audited:
11 bottom-up modules + 2 comparison joins; illegal edges: 0`.

## Update after Task 36 (adversarial global-topology battery)

Task 36 added 14 modules under `RequestProject/Spine/Task36/` and changed no existing import
line.  Project-local closures of the new endpoints, and the mechanical checks that constrain
them:

| Endpoint | direct project-local imports | reaches the top-down obstruction branch? |
| --- | --- | --- |
| `Spine.Task36.LoopModel` | 1 | no |
| `Spine.Task36.OrientationGate` | 1 | no |
| `Spine.Task36.OrientationReversing` | 1 | no |
| `Spine.Task36.LoopSolder` | 1 | no |
| `Spine.Task36.LoopSpinFreedom` | 2 | no |
| `Spine.Task36.TimeOrientation` | 2 | no |
| `Spine.Task36.TrivialControl` | 2 | no |
| `Spine.Task36.SmoothBundlePackaging` | 2 | no |
| `Spine.Task36.GaugeGroup` | 2 | no |
| `Spine.Task36.SpinNotLorentz` | 1 | no |
| `Spine.Task36.SpinFoamControl` | 2 | no |
| `Spine.Task36.SpinObstruction` | 2 | **yes — the single declared comparison module** |
| `Spine.Task36.Certificate` | 4 | yes (through `SpinObstruction`) |
| `Spine.Task36.Firewall` | 5 | audit module |

Mechanically checked at the final green build (`lake build RequestProject`, 8341 jobs):

```text
Task-36 leaf audit:   199 non-Task-36 Spine modules checked, 0 of them reach Spine.Task36
Task-36 branch audit: 11 bottom-up adversarial modules reach none of the 6 top-down prefixes
control OK:           Spine.Task36.SpinObstruction imports Spine.Solder.RegularSolder
control OK:           Spine.Task36.SpinObstruction imports Spine.E2.Cech.Obstruction
curvature firewall:   6119 Spine declarations scanned, none names curvature/holonomy/
                      connection/Riemann
legacy/external:      13 Task-36 modules, Experiment1 = 0, Experiment2 = 0, external = 0
```

---

# Task 37 — the frozen Task-36 DAG and the deformation branch

## 1. The frozen Task-36 DAG after the Task-37 parallelisation

The Task-36 chain was serial (depth 9 to the firewall).  Task 37 rewrote eleven import lists;
no theorem statement changed.  New shape:

```text
Solder.RegularSolder    ─→ Task36.OrientationGate ─┬─→ Task36.OrientationReversing
                                                   │        └→ Task36.SpinNotLorentz
                                                   │                 └→ Task36.SpinFoamControl
                                                   ├─→ Task36.TrivialControl ───────↗
                                                   └─→ Task36.SpinObstruction  (comparison join)
Solder.RegularExamples  ─→ Task36.LoopModel ─→ Task36.LoopSolder ─┬→ Task36.LoopSpinFreedom
                                                                  └→ Task36.LoopTimeOrientation
Solder.OrientationTime  ─→ Task36.TimeOrientation ────────────────↗
Solder.BundleEquivalence─→ Task36.SmoothBundlePackaging
Solder.RegularGauge     ─→ Task36.GaugeGroup
Task36.Certificate  aggregates the proved endpoints
Task36.Firewall     audits the layer
```

| module | depth inside Task 36 (before → after) | imports a loop model? |
|---|---|---|
| `Task36.LoopModel` | 1 → 1 | itself |
| `Task36.OrientationGate` | 2 → 1 | **no** (was yes) |
| `Task36.LoopSolder` | 3 → 2 | yes |
| `Task36.TimeOrientation` | 4 → 1 | **no** (was yes) |
| `Task36.LoopTimeOrientation` (new) | — → 3 | yes |
| `Task36.TrivialControl` | 5 → 2 | **no** (was yes) |
| `Task36.SpinObstruction` | 6 → 2 | **no** (was yes) |
| `Task36.SmoothBundlePackaging` | 3 → 1 | no |
| `Task36.GaugeGroup` | 4 → 1 | no |
| `Task36.OrientationReversing` | 3 → 2 | yes |
| `Task36.SpinNotLorentz` | 4 → 3 | yes (through the Möbius control) |
| `Task36.SpinFoamControl` | 6 → 4 | yes (through the above) |
| `Task36.Certificate` | 7 → 4 | yes |
| `Task36.Firewall` | 8 → 5 | audit module |

## 2. The Task-37 deformation-preparation branch

```text
Solder.RegularSolder ──→ Deformation.SharedTransport ─┬→ Deformation.LoopSharedTransport
Task36.LoopSpinFreedom ───────────────────────────────┘        │
Task36.SpinObstruction ──→ Deformation.NeutralRegression ←─────┘
Task36.OrientationReversing ─→ Deformation.ClosureAdmissibility ←─ Deformation.NeutralRegression
                                        └→ Deformation.Firewall (audit)
```

The branch is a **leaf**: nothing outside `Spine.Deformation` imports it.  Check 1 of
`Spine/Task36/Firewall.lean` therefore exempts the prefix `Spine.Deformation` (the deformation
branch is a declared consumer of the frozen layer), and the same leaf property is verified for
the deformation branch itself in `Spine/Deformation/Firewall.lean`.

Mechanically checked at the final green build (`lake build RequestProject`, 8 347 jobs):

```text
Task-36 leaf audit:      199 non-Task-36 Spine modules checked, 0 reach Spine.Task36
Task-36 branch audit:    12 bottom-up adversarial modules reach none of the 6 top-down prefixes
deformation leaf audit:  201 non-deformation Spine modules checked, 0 reach Spine.Deformation
shared-origin firewall:  SharedTransportFamily [base, spin],
                         RegularClosureSolution [smoothGluing, solder]
target-leakage audit:    116 declarations scanned, none names a curvature sign, a target
                         geometry, a field equation, a transport form or a loop-transport object
legacy/external:         14 Task-36 modules + 4 deformation modules, all zero
```

---

## Task 38 — the fixed-base smoke test (same leaf branch)

Five modules were added *inside* `Spine.Deformation`, so the leaf property is unchanged:

```text
Deformation.SharedTransport ──→ Deformation.ProjectedParaAction ─┐
Deformation.ClosureAdmissibility ────────────────────────────────┴→ Deformation.FixedBaseSmokeTest
                                                                        │
                                          Deformation.CocycleGaugeOrbit ←┘
                                                     │
                                Deformation.TangentMetricComparison
                                                     │
                                 Deformation.SmokeTestCertificate ──→ Deformation.Firewall (audit)
```

Mechanically checked at the Task-38 green build (`lake build RequestProject`, 8 352 jobs):

```text
Task-36 leaf audit:      199 non-Task-36 Spine modules checked, 0 reach Spine.Task36
deformation leaf audit:  201 non-deformation Spine modules checked, 0 reach Spine.Deformation
shared-origin firewall:  SharedTransportFamily [base, spin],
                         RegularClosureSolution [smoothGluing, solder]
target-leakage audit:    225 declarations scanned, none names a curvature sign, a target
                         geometry, a field equation, a transport form or a loop-transport object
legacy/external:         14 Task-36 modules + 9 deformation modules, all zero
```
