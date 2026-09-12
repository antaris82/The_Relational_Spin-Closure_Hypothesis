# TASK 01 — Topological qualification of the intrinsic Spin cover

**Scope.** Topologies for the already reconstructed *algebraic* objects `SpinCore.SpinGroup`,
`SpinCore.GLor`, `SpinCore.spinCover`, such that both groups are topological (in fact
Hausdorff) groups, the cover is continuous, and the already proved kernel `{±1}` is
discrete. **Local continuous sections are explicitly out of scope** and are not claimed
anywhere in the new layer.

**Result.** All four required properties are established, with no new axiom, no `sorry`,
and no use of the historical experiment trees or of the downstream `SL(2,ℂ)` comparison.
The final classification is in §8, the answer to the final scientific question in §9.

---

## 1. WP1 — audit of the algebraic carriers

Exact native definitions inherited by this task (all in `RequestProject/Spine/E1/`):

| object | definition | file |
|---|---|---|
| carrier | `abbrev LorentzCarrier : Type := ℝ × (Fin 3 → ℝ)` | `Carrier.lean` |
| Euclidean form | `q3 : QuadraticForm ℝ (Fin 3 → ℝ)`, `q3 v = ⟪v,v⟫` | `Clifford.lean` |
| Clifford algebra | `abbrev Cl3 : Type := CliffordAlgebra q3` | `Clifford.lean` |
| paravector embedding | `spinToCl x = algebraMap ℝ Cl3 x.1 + ι q3 x.2` | `Clifford.lean` |
| Clifford conjugation | `cconj x = involute (reverse x)` | `SpinElement.lean` |
| spin predicate | `IsSpinElem g ↔ g * cconj g = 1 ∧ cconj g * g = 1` | `SpinElement.lean` |
| twisted action | `spinAct g x = g * spinToCl x * reverse g` | `SpinElement.lean` |
| induced map | `spinLor g x := (spinAct_mem_para g x).choose`, characterised by `spinToCl (spinLor g x) = spinAct g x` | `Paravector.lean` |
| bundled spin group | `SpinGroup : Subgroup Cl3ˣ`, carrier `{u | IsSpinElem ↑u}` | `SpinGroup.lean` |
| Lorentz target | `GLor : Subgroup (LorentzCarrier ≃ₗ[ℝ] LorentzCarrier)`, `IsGLor F ↔ (N- and cone-preserving) ∧ det = 1` | `LorentzGroup.lean` |
| the cover | `spinCover : SpinGroup →* GLor`, `u ↦ ⟨spinLorEquiv u.2, _⟩` | `SpinCover.lean` |
| exact kernel | `mem_ker_spinCover_iff`, `spinCover_ker_card = 2`, `spinCover_ker_central` | `SpinKernel.lean` |
| monomial frame | `mono : Fin 8 → Cl3`, `monoSpan_eq_top`, `monoComb_coeffs_eq_zero` | `CliffordMonomial.lean` |

Classification of the inherited structure relevant to topology:

* **Already in Mathlib**: `CliffordAlgebra`, `ι`, `reverse`, `involute`, `Units`, `Subgroup`,
  `LinearEquiv`, `Module.End`, the module topology `moduleTopology` and its theory.
* **Project-defined algebraic structure**: everything in the table above.
* **Equivalences used only downstream**: `spinEquivSL2 : SpinGroup ≃* SL(2,ℂ)`
  (`SL2Comparison.lean`) — *not used here, not imported here*; the complex matrix model
  `MatrixModel.lean` and `PauliRepresentation.lean` — likewise not used or imported.
* **Not previously available and supplied by this task**: `Module.Finite ℝ Cl3`,
  a basis of `Cl₃(ℝ)`, all topologies, all continuity, kernel discreteness.

### Dependency DAG of the new topological layer

```
Mathlib
  │
  ├── Spine/E1/Topology/FiniteDimTools.lean          (generic; Mathlib only)
  │      SpineTop.eq_moduleTopology_of_t2
  │      SpineTop.t2Space_of_isModuleTopology
  │      SpineTop.continuous_into_linearMap
  │
  ├── Spine/E1/CliffordMonomial.lean  ──►  Spine/E1/Topology/CliffordTopology.lean
  │      (mono, monoSpan_eq_top,            monoBasis, Module.Finite ℝ Cl3, finrank = 8,
  │       monoComb_coeffs_eq_zero)          TopologicalSpace Cl3 := moduleTopology ℝ Cl3,
  │                                         IsModuleTopology, ContinuousAdd,
  │                                         IsTopologicalRing Cl3, T2Space Cl3,
  │                                         monoCoords / monoHomeomorph,
  │                                         continuous_reverse, continuous_involute,
  │                                         Cl3_topology_unique
  │
  ├── Spine/E1/LorentzGroup.lean  ──►  Spine/E1/Topology/LorentzTopology.lean
  │      (GLor)                        IsModuleTopology ℝ LorentzCarrier,
  │                                    EndLor := LorentzCarrier →ₗ[ℝ] LorentzCarrier,
  │                                    TopologicalSpace EndLor := moduleTopology ℝ EndLor,
  │                                    IsTopologicalRing EndLor, T2Space EndLor,
  │                                    EndLor_topology_unique,
  │                                    lorAutToUnits, TopologicalSpace (≃ₗ),
  │                                    IsTopologicalGroup/T2 of (≃ₗ) and of GLor
  │
  ├── Spine/E1/SpinGroup.lean + CliffordTopology  ──►  Spine/E1/Topology/SpinTopology.lean
  │                                    continuous_cconj, T2Space Cl3ˣ,
  │                                    IsTopologicalGroup/T2 of SpinGroup,
  │                                    continuous_spinGroup_val / _cconj
  │
  └── Spine/E1/SpinKernel.lean + SpinTopology + LorentzTopology
                     ──►  Spine/E1/Topology/SpinCoverTopology.lean
                            spinToClLin, paraRetract, spinLor_eq_paraRetract,
                            carrierBasis, continuous_spinLor_apply,
                            continuous_spinLorLin, continuous_spinCover,
                            Finite/DiscreteTopology of ker spinCover,
                            TopologicalCentralCover, topologicalSpinProjection,
                            intrinsic_spin_cover_topological
                     ──►  Spine/E1/Topology/Core.lean   (endpoint)
                            spin_double_cover_topological
                     ──►  Spine/E1/Core.lean            (re-export)
                            spin_double_cover_topological_endpoint
```

No node of this DAG reaches `Experiment1/**`, `Experiment2/**`, `Spine/Controls/**`,
`Spine/E2/**`, `SL2Comparison`, `MatrixModel` or `PauliRepresentation`; this is enforced
mechanically (§7).

---

## 2. WP2 — the Lorentz target

Routes compared:

1. **subspace of a finite-dimensional endomorphism space** — the route taken;
2. **matrix realisation** — would require choosing a basis of the carrier and identifying
   `GLor` with a matrix subgroup: an extra, avoidable choice, and it produces the same
   topology anyway (a linear isomorphism of finite-dimensional Hausdorff TVS is a
   homeomorphism);
3. **transport along an existing linear equivalence** (e.g. `spinToVec : 𝒮 ≃ₗ ℝ⁴`) — same
   objection: a transported topology needs a justification that it does not depend on the
   equivalence, which route 1 makes unnecessary.

Implemented chain (`LorentzTopology.lean`):

`LorentzCarrier` (product topology; `isModuleTopology_LorentzCarrier` proves it *is* the
module topology) → `EndLor := LorentzCarrier →ₗ[ℝ] LorentzCarrier` with
`moduleTopology ℝ EndLor` → `IsTopologicalRing EndLor` (Mathlib:
`IsModuleTopology.isTopologicalRing`, applicable because `EndLor` is an `ℝ`-algebra finite
as an `ℝ`-module) → `T2Space EndLor` → `EndLorˣ` with Mathlib's canonical unit-group
topology (induced by `u ↦ (u, u⁻¹)`), hence a topological group with continuous inversion →
`LorentzCarrier ≃ₗ[ℝ] LorentzCarrier` topologised through Mathlib's canonical `MulEquiv`
`LinearMap.GeneralLinearGroup.generalLinearEquiv` → `GLor` with the subgroup topology.

Continuity of multiplication and of inversion on `GLor` is therefore *inherited*, not
re-proved: it is `Topology.IsInducing.topologicalGroup` applied to the canonical
identification, plus Mathlib's subgroup instance.

**Hausdorffness follows automatically** at every stage: `T2Space EndLor` (finite-dimensional
module topology), hence `T2Space EndLorˣ` (embedding `u ↦ (u,u⁻¹)`), hence
`T2Space (≃ₗ)` (embedding), hence `T2Space GLor` (subspace).

No manifold structure is used or claimed.

---

## 3. WP3 — the Spin source

`SpinGroup` is *by definition* a `Subgroup Cl3ˣ`, so no new carrier is introduced. The chain
(`CliffordTopology.lean` + `SpinTopology.lean`) is exactly the one demanded:

finite-dimensional real Clifford algebra (`Module.Finite ℝ Cl3` from the monomial frame,
`finrank = 8`) → topological algebra (`moduleTopology ℝ Cl3`, `IsTopologicalRing Cl3`,
`T2Space Cl3`) → unit group `Cl3ˣ` (canonical unit topology; topological group; Hausdorff) →
subgroup topology on `SpinGroup` (topological group; Hausdorff).

No transport from `SL(2,ℂ)` is used; the intrinsic construction did not fail at any point,
so the escape clause of WP3 was never invoked.

`monoHomeomorph : Cl₃(ℝ) ≃ₜ ℝ⁸` records that the canonical topology is the ordinary
eight-dimensional real topology read in the intrinsic monomial frame (so it is neither
discrete nor indiscrete — the continuity statements below are not vacuous).

---

## 4. WP4 — continuity of the cover

The implementation of `spinCover` goes through `spinLor`, which is defined by a *choice*
(`Exists.choose` of the paravector-membership proof). Nothing was changed about that
definition; instead the intrinsic continuous map was exposed, as WP4 permits:

1. `spinToClLin : LorentzCarrier →ₗ[ℝ] Cl3` — the existing embedding `spinToCl` packaged as
   a linear map (its additivity and homogeneity are the existing lemmas `spinToCl_add`,
   `spinToCl_smul`; injectivity is the existing `spinToCl_injective`);
2. `paraRetract : Cl3 →ₗ[ℝ] LorentzCarrier` — a linear left inverse, which exists because an
   injective linear map of finite-dimensional real vector spaces splits
   (`LinearMap.exists_leftInverse_of_injective`);
3. `spinLor_eq_paraRetract : spinLor g x = paraRetract (g * spinToCl x * reverse g)` — the
   choice is eliminated: the action *is* the retraction of the twisted Clifford product;
4. `continuous_spinLor_apply` — hence continuity in `g` for fixed `x`, from: continuity of
   multiplication in `Cl₃(ℝ)` (`IsTopologicalRing Cl3`), continuity of `reverse` (an
   `ℝ`-linear map out of a module-topologised space) and continuity of `paraRetract`;
5. `continuous_spinLorLin : Continuous fun g : Cl3 => (spinLorLin g : EndLor)` — the whole
   Clifford action map into the endomorphism algebra is continuous, by the basis-evaluation
   criterion `SpineTop.continuous_into_linearMap` with `carrierBasis` (from the existing
   coordinate equivalence `spinToVec`);
6. `continuous_spinCover` — the target topology is induced from `EndLor × EndLorᵐᵒᵖ` by
   `F ↦ (F, F⁻¹)`, so continuity of the cover reduces to continuity of
   `u ↦ spinLorLin ↑u` and of `u ↦ spinLorLin (cconj ↑u)`; both are step 5 composed with
   the continuous maps `u ↦ ↑u` and `u ↦ cconj ↑u` on the spin group. The two identities
   `((spinCover u : GLor) : ≃ₗ).toLinearMap = spinLorLin ↑u` and
   `(… ).symm.toLinearMap = spinLorLin (cconj ↑u)` hold by `rfl`, i.e. the proof really does
   run through the definition of `spinCover`.

The primitive ingredients are exactly those anticipated in the task statement:
Clifford multiplication, reversion/Clifford conjugation (which supplies inversion in the
unit group), the twisted action, the restriction to the paravector carrier (here: its
linear retraction) and finite-dimensional linear maps. `SL2Comparison` is not imported.

---

## 5. WP5 — discreteness of the kernel

Not asserted from "two elements". The chain is:

* the source `SpinGroup` is **Hausdorff** — `instT2SpaceSpinGroup`, inherited from
  `T2Space Cl3` (finite-dimensional module topology) through the unit-group embedding and
  the subgroup topology;
* the kernel `spinCover.ker : Subgroup ↥SpinGroup` carries the **subgroup (subspace)
  topology** by Mathlib's `Subgroup` instance — this is the same topology as the one
  induced from `SpinGroup`, by construction of the instance;
* it is **finite**: `Nat.card (spinCover.ker) = 2` is the existing algebraic theorem
  `spinCover_ker_card` (re-used, not re-proved), and `Nat.finite_of_card_ne_zero` turns it
  into `Finite`;
* a **finite Hausdorff** space is discrete (Mathlib instance), giving
  `instDiscreteTopologySpinCoverKer : DiscreteTopology (spinCover.ker)` — exactly the form
  the downstream generic interface asks for (`ker_discrete` field shape).

Centrality is the existing `spinCover_ker_central`, re-used unchanged.

---

## 6. Canonicality / provenance table

| # | object | construction route | dependencies | status | transported from | inequivalent alternative possible? | downstream dependence on the choice |
|---|---|---|---|---|---|---|---|
| 1 | `Module.Finite ℝ Cl3`, `monoBasis` | packaging of `monoSpan_eq_top` + `monoComb_coeffs_eq_zero` | `CliffordMonomial` | **derived** (a *basis* is a choice, but the finiteness statement is not, and the basis occurs in no statement of the topology) | — | no (finiteness is a property) | no |
| 2 | `TopologicalSpace Cl3` | `moduleTopology ℝ Cl3` (`sInf` of the topologies making `+` and `•` continuous) | `Module ℝ Cl3` only | **definitional / inherited canonical** (choice-free) | — | **no** among Hausdorff TVS topologies: `Cl3_topology_unique` | — |
| 3 | `IsTopologicalRing Cl3` | Mathlib `IsModuleTopology.isTopologicalRing` (finite algebra + module topology) | 1, 2 | **derived** | — | — | no |
| 4 | `T2Space Cl3` | continuous injection `monoCoords` into `ℝ⁸` | 1, 2 | **derived** (basis used in the proof only) | — | — | no |
| 5 | `monoHomeomorph : Cl3 ≃ₜ ℝ⁸` | both directions linear, module topology | 1–4 | **derived** | — | — | no (informational) |
| 6 | `IsModuleTopology ℝ LorentzCarrier` | Mathlib `isModuleTopologyOfFiniteDimensional` | product topology of `ℝ × ℝ³` | **inherited canonical**: the pre-existing product topology *is* the module topology | — | no (Hausdorff TVS uniqueness) | no |
| 7 | `TopologicalSpace EndLor` | `moduleTopology ℝ EndLor` | `Module ℝ EndLor` | **definitional / inherited canonical** | — | **no**: `EndLor_topology_unique` | — |
| 8 | `IsTopologicalRing EndLor`, `T2Space EndLor` | as 3, 4 (generic lemma `SpineTop.t2Space_of_isModuleTopology`) | 7 | **derived** | — | — | no |
| 9 | `TopologicalSpace EndLorˣ` | Mathlib `Units` instance, induced by `u ↦ (u, u⁻¹)` | 7 | **inherited canonical** (Mathlib's canonical unit topology; the one that makes inversion continuous) | — | the coarser topology induced by `u ↦ u` alone is a conceivable alternative; it is *not* used, and it is a theorem of finite-dimensional analysis (not proved here) that the two agree | the topological-group structure uses this choice; nothing else does |
| 10 | `TopologicalSpace (𝒮 ≃ₗ[ℝ] 𝒮)` | induced along `lorAutToUnits`, Mathlib's canonical `MulEquiv` with `EndLorˣ` | 9 | **transported canonical** | from `EndLorˣ` through `LinearMap.GeneralLinearGroup.generalLinearEquiv` (a Mathlib-canonical isomorphism, not a chosen one) | no, given 9 | yes: this is the topology of the cover's target |
| 11 | `IsTopologicalGroup`, `T2Space` of `(𝒮 ≃ₗ 𝒮)` | `Topology.IsInducing.topologicalGroup`, `IsEmbedding.t2Space` | 10 | **derived** | — | — | no |
| 12 | topology / group / `T2` of `GLor` | Mathlib subgroup instances | 10, 11 | **inherited canonical** (subspace) | — | no | — |
| 13 | `T2Space Cl3ˣ`, topology of `Cl3ˣ` | Mathlib `Units` instances + embedding | 2–4 | **inherited canonical** | — | as in 9 | — |
| 14 | topology / group / `T2` of `SpinGroup` | Mathlib subgroup instances | 13 | **inherited canonical** (subspace) | — | no | — |
| 15 | `spinToClLin` | packaging of `spinToCl` as a linear map | existing lemmas | **derived** | — | — | no |
| 16 | `paraRetract` | `LinearMap.exists_leftInverse_of_injective` + `Exists.choose` | 15 | **chosen** (a linear complement of the paravector subspace is a genuine choice) | — | yes, many retractions exist | **no**: only `paraRetract ∘ spinToCl = id` is used, and every retraction gives the same value `spinLor g x`, which is determined by `spinToCl_spinLor` |
| 17 | `carrierBasis` | `Module.Basis.ofEquivFun spinToVec` | existing `spinToVec` | **chosen** (frame) | — | yes | **no**: used only inside the proof of `continuous_spinLorLin`; occurs in no statement |
| 18 | `continuous_spinCover` | §4 | 2–17 | **derived** | — | — | — |
| 19 | `DiscreteTopology (ker spinCover)` | §5 | 14 + `spinCover_ker_card` | **derived** | — | — | — |
| 20 | `TopologicalCentralCover`, `topologicalSpinProjection` | packaging | 12, 14, 18, 19 | **derived** | — | — | — |

Only rows 16 and 17 involve a genuine free choice, and in both cases the choice is
confined to a proof: it occurs in no statement of the layer, and the statements are
invariant under it.

---

## 7. Verification

### Build commands and outputs

```
$ lake build RequestProject.Spine.E1.Core
Build completed successfully (8054 jobs).

$ lake build RequestProject.Spine.E2.Core
Build completed successfully (8091 jobs).

$ lake build RequestProject.Spine.Core
Build completed successfully (8123 jobs).

$ lake build RequestProject.Spine.E1.Topology.Core          # the new focused target
Build completed successfully (8051 jobs).

$ lake build RequestProject.Spine.Audit.Firewall
info: SPINE FIREWALL AUDIT: all checks passed
Build completed successfully (8130 jobs).

$ lake build                                                # whole default target
Build completed successfully (8134 jobs).
```

### Legacy-dependency audit

`python3 scripts/legacy_audit.py` → `RESULT: PASS`, with

```
Spine direct legacy imports:     Experiment1 = 0   Experiment2 = 0
Spine transitive legacy imports: Experiment1 = 0   Experiment2 = 0

endpoint                                   direct  closure   E1   E2
RequestProject.Spine.Core                       3       97    0    0
RequestProject.Spine.E1.Core                    3       28    0    0
RequestProject.Spine.E1.Topology.Core           1       25    0    0
RequestProject.Spine.E1.SL2Comparison           2       22    0    0
RequestProject.Spine.E2.Core                    1       65    0    0
…                                                              0    0
```

The compile-time firewall was extended: the six new modules are added to the level-3
"intrinsic spin core" audit, so the build now *fails* if any of them ever reaches
`Experiment1/**`, `Experiment2/**`, `Spine.Controls/**`, `Spine.E2/**`, `SL2Comparison`,
`MatrixModel`, `PauliRepresentation` or `WeylSpinorModule`; `Spine.E1.Topology.Core` was
added to the per-endpoint zero-legacy report, and the proof-closure audit now also covers
`SpinCore.spin_double_cover_topological` and
`SpinCore.spin_double_cover_topological_endpoint`.

### Proof discipline

`rg` over `RequestProject/Spine/E1/Topology/**`: no `sorry`, no `admit`, no `axiom`
declaration, no `@[implemented_by]`, no `native_decide`, no `unsafe`, no `partial`.
No pre-existing theorem statement was altered; the only edits outside the new directory are
three additive ones (an import plus a re-export theorem in `Spine/E1/Core.lean`, the
firewall extension, one line in `scripts/legacy_audit.py`).

### Axiom audit

All of the following report exactly `[propext, Classical.choice, Quot.sound]`:

```
SpinCore.monoBasis                        SpinCore.instT2SpaceCl3Units
SpinCore.instTopologicalSpaceCl3          SpinCore.instIsTopologicalGroupSpinGroup
SpinCore.instIsModuleTopologyCl3          SpinCore.instT2SpaceSpinGroup
SpinCore.instIsTopologicalRingCl3         SpinCore.continuous_cconj
SpinCore.instT2SpaceCl3                   SpinCore.paraRetract
SpinCore.monoHomeomorph                   SpinCore.spinLor_eq_paraRetract
SpinCore.Cl3_topology_unique              SpinCore.continuous_spinLorLin
SpinCore.isModuleTopology_LorentzCarrier  SpinCore.continuous_spinCover
SpinCore.instTopologicalSpaceEndLor       SpinCore.instDiscreteTopologySpinCoverKer
SpinCore.instIsTopologicalRingEndLor      SpinCore.topologicalSpinProjection
SpinCore.instT2SpaceEndLor                SpinCore.intrinsic_spin_cover_topological
SpinCore.EndLor_topology_unique           SpinCore.spin_double_cover_topological
SpinCore.instTopologicalSpaceLorAut       SpinCore.spin_double_cover_topological_endpoint
SpinCore.instIsTopologicalGroupLorAut     SpineTop.eq_moduleTopology_of_t2
SpinCore.instT2SpaceLorAut                SpineTop.continuous_into_linearMap
SpinCore.instIsTopologicalGroupGLor
SpinCore.instT2SpaceGLor
```

### Failbuild ledger (append-only)

| # | module | error | diagnosis | repair | mathematical content changed |
|---|---|---|---|---|---|
| 1 | `Topology/FiniteDimTools.lean` | `Unknown constant IsModuleTopology.eq_moduleTopology` | the lemma is declared at root level, before `namespace IsModuleTopology` | use `eq_moduleTopology ℝ E` | no |
| 2 | `Topology/FiniteDimTools.lean` | `Type mismatch … Continuous ⇑e` | `LinearEquiv` coercion vs. `LinearMap` coercion | state `Continuous (⇑e)` and close with `simpa` from the linear-map version | no |
| 3 | `Topology/CliffordTopology.lean` | `Invalid field toLinearMap … LinearMap.toLinearMap` | `CliffordAlgebra.reverse` is already a `LinearMap` (unlike `involute`, an `AlgHom`) | drop `.toLinearMap` for `reverse` | no |
| 4 | `Topology/CliffordTopology.lean` | `typeclass instance problem is stuck`, then `Function expected at` | `cconj` is defined in `SpinElement.lean`, which this module does not import; the identifier was auto-bound as an implicit variable | moved `continuous_cconj` to `Topology/SpinTopology.lean`, which imports the spin layer | no |
| 5 | `Topology/LorentzTopology.lean` | `Unknown identifier IsInducing.topologicalGroup` | the lemma lives in namespace `Topology` | `Topology.IsInducing.topologicalGroup` | no |
| 6 | `Topology/SpinCoverTopology.lean` | `simpa` produced a component-wise `Prod` continuity goal | `simp` unfolded continuity into the two carrier components | replaced by an explicit `funext` + `rw` of the retraction identity | no |
| 7 | `Topology/SpinCoverTopology.lean` | `Type mismatch: fun u => spinLorLin ↑u has type Cl3ˣ → …` | the binder ascription `(SpinGroup : Subgroup Cl3ˣ)` was read as the coercion target of `u` | write the binder as `u : ↥SpinGroup` | no |
| 8 | `Topology/SpinCoverTopology.lean` | `spinCover has type ↥SpinGroup →* ↥GLor but is expected to have type Subgroup Cl3ˣ → ↥GLor` | ascription of a `MonoidHom` to a function type | use `⇑spinCover` | no |

No other build failed; every failure above was repaired before the documentation of the
relevant section was written.

---

## 8. Classification of the required properties

| required property | classification | justification |
|---|---|---|
| `SpinGroup` is a topological group | `INHERITED_CANONICAL` | subgroup of `Cl3ˣ`, whose topology is Mathlib's canonical unit topology over the module topology of `Cl₃(ℝ)`; uniqueness of the latter is `Cl3_topology_unique` |
| `SpinGroup` is Hausdorff | `DERIVED_NATIVE` | from `T2Space Cl3`, via embedding and subspace |
| `GLor` is a topological group | `INHERITED_CANONICAL` (with one `TRANSPORTED_CANONICAL` step) | subgroup of the linear automorphism group, topologised through Mathlib's canonical `MulEquiv` with `EndLorˣ`; the transport is along a canonical isomorphism, not a chosen one |
| `GLor` is Hausdorff | `DERIVED_NATIVE` | from `T2Space EndLor` |
| `spinCover` is continuous | `DERIVED_NATIVE` | §4: proved from the definition of the twisted Clifford action |
| `spinCover` is surjective | `DERIVED_NATIVE` (re-used) | existing `spinCover_surjective` |
| `ker spinCover` is central | `DERIVED_NATIVE` (re-used) | existing `spinCover_ker_central` |
| `ker spinCover` is discrete | `DERIVED_NATIVE` | §5: Hausdorff source + finite kernel |
| topology of `Cl₃(ℝ)` | `INHERITED_CANONICAL` | module topology of the underlying real vector space; unique Hausdorff TVS topology |
| finite dimensionality of `Cl₃(ℝ)` | `DERIVED_NATIVE` | from the project's own monomial frame |
| choice of a linear retraction `paraRetract` and of `carrierBasis` | `ADDITIONAL_CHOICE` (proof-internal only) | free choices that occur in no statement and change no value |
| local continuous sections | `NOT_REQUIRED` | explicitly deferred to a later task |
| manifold / bundle / covering-space structure | `NOT_REQUIRED` | out of scope |
| identification with the Lie group `Spin⁺(1,3)` | `NOT_REQUIRED` | not theorem-level in the native Spine, and not used |

Nothing in the required list is `BLOCKED`.

---

## 9. Final scientific question

> Does the intrinsic algebraic Spin double cover already reconstructed in `Spine/E1`
> canonically determine a continuous central two-fold projection of topological groups with
> discrete kernel, without using the historical experiments or the downstream `SL(2,ℂ)`
> comparison as foundational input?

**Yes.** Formally: `SpinCore.spin_double_cover_topological` (endpoint
`RequestProject.Spine.E1.Topology.Core`), bundled as
`SpinCore.topologicalSpinProjection : TopologicalCentralCover ↥SpinGroup ↥GLor`.

The qualification is canonical in the following precise sense. The only topological input
is that a finite-dimensional real vector space carries a unique Hausdorff
topological-vector-space topology, namely its module topology
(`SpineTop.eq_moduleTopology_of_t2`); this is applied to the two ambient algebras that the
existing construction already fixes — the Clifford algebra `Cl₃(ℝ)` (whose finite
dimensionality is proved from the project's own monomial frame) and the endomorphism
algebra of the carrier. Everything else is Mathlib's canonical unit-group and subgroup
topology. Consequently no alternative *inequivalent* Hausdorff topology on either ambient
object is possible (`Cl3_topology_unique`, `EndLor_topology_unique`), and the two group
topologies are not free parameters of the construction.

The single residual conventional element is the use of the unit-group topology (induced by
`u ↦ (u, u⁻¹)`) rather than the possibly coarser subspace topology induced by `u ↦ u`; this
is the standard convention that makes inversion continuous, it is the convention the
downstream interface expects, and the two are in fact known to coincide in finite
dimension — a fact this task does not need and does not prove.

The question of **continuous local sections** is deliberately left open here; it is the
subject of the next task, and nothing in this layer presupposes it.
