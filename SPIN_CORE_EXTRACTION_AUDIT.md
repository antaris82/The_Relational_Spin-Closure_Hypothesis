# Refactoring task 02 — extraction of the intrinsic Spin double-cover core

This document records the second refactoring pass: the complete algebraic Spin
double-cover object is now contained in the intrinsic experiment-1 core, independently of
`SL(2,ℂ)`, of the complex `2 × 2` matrix model, and of both historical experiment trees.

Everything below is mechanically checked: the module boundaries by
`RequestProject/Spine/Audit/Firewall.lean` (which fails to compile if they are violated),
the proofs by `lake build`, the axioms by the `#print axioms` lines quoted in §7.

---

## 1. The new layering

```
Spine.E1.Carrier                (Lorentz carrier, intrinsic quadratic form NS, cone, GLor)
        ↓
Spine.E1.Clifford               (Cl₃(ℝ) = CliffordAlgebra q3, paravector embedding)
        ↓
Spine.E1.LorentzClifford        (even Lorentz Clifford construction)
        ↓
Spine.E1.CliffordMonomial       (monomial frame, faithfulness, exact centre)        [new]
        ↓
Spine.E1.SpinElement            (predicate IsSpinElem, twisted action)      [renamed file]
        ↓
Spine.E1.SpinGroup              (bundled SpinGroup : Subgroup Cl3ˣ)                 [new]
        ↓
Spine.E1.Paravector / SpinDeterminant / Shell / DoubleCover   (action facts, surjectivity)
        ↓
Spine.E1.SpinCover              (spinCover : SpinGroup →* GLor, surjectivity)       [new]
        ↓
Spine.E1.SpinKernel             (ker spinCover = {±1}, central, of order 2)         [new]
        ↓
Spine.E1.SL2Comparison          (comparison only: SpinGroup ≃* SL(2,ℂ))         [rewritten]
```

There is no reverse edge.  `Spine.E1.SL2Comparison` imports `Spine.E1.SpinKernel`; no
module of the intrinsic core imports `SL2Comparison`, `MatrixModel`, `PauliRepresentation`
or `WeylSpinorModule`.

## 2. Deliverables

| # | Deliverable | Declaration | Module |
| --- | --- | --- | --- |
| 1 | cleaned intrinsic Spin group | `SpinCore.SpinGroup : Subgroup Cl3ˣ` | `Spine/E1/SpinGroup.lean` |
| 1b | predicate layer, kept separate | `SpinCore.IsSpinElem : Cl3 → Prop` | `Spine/E1/SpinElement.lean` |
| 2 | intrinsic Spin → Lorentz homomorphism | `SpinCore.spinCover : SpinGroup →* GLor` | `Spine/E1/SpinCover.lean` |
| 3 | intrinsic surjectivity | `SpinCore.spinCover_surjective` | `Spine/E1/SpinCover.lean` |
| 4 | intrinsic exact `{±1}` kernel | `SpinCore.mem_ker_spinCover_iff`, `SpinCore.spinCover_ker_eq_zpowers`, `SpinCore.spinCover_ker_card`, `SpinCore.spinCover_ker_central` | `Spine/E1/SpinKernel.lean` |
| 4b | bundled endpoint | `SpinCore.spin_double_cover`, `SpinCore.spin_double_cover_bundled` | `Spine/E1/SpinKernel.lean`, `Spine/E1/Core.lean` |
| 5 | comparison-only `SL(2,ℂ)` layer | `SpinCore.spinEquivSL2`, `SpinCore.sl2_comparison` | `Spine/E1/SL2Comparison.lean` |

The kernel is stated in the strongest clean forms available:

* elementwise: `u ∈ spinCover.ker ↔ u = 1 ∨ u = negOneSpin`;
* as a subgroup: `spinCover.ker = Subgroup.zpowers negOneSpin`;
* as a cardinality: `Nat.card spinCover.ker = 2` (using `negOneSpin ≠ 1`, itself reduced to
  the intrinsic linear independence of `1` and the pseudoscalar);
* as a centrality statement: `∀ z ∈ ker, ∀ u, z * u = u * z`.

## 3. Was `SL(2,ℂ)` needed for the proofs?  No.

The first pass proved the exact kernel through `SpinCore.center_Cl3` (the centre of
`Cl₃(ℝ)`), and that centre theorem was proved in `Spine.E1.PauliRepresentation` from the
centre of `M₂(ℂ)` — a Hermitian-pattern matrix model.  That was the only genuine
dependence of the intrinsic double cover on a matrix comparison, and it was a *proof
device*, not foundational data.

It has been removed.  `Spine.E1.CliffordMonomial` now proves, with no complex algebra:

* the eight monomials `1, e₀, e₁, e₂, e₀e₁, e₀e₂, e₁e₂, ω` span `Cl₃(ℝ)`
  (`monoSpan_eq_top`, moved unchanged);
* they are linearly independent (`monoComb_coeffs_eq_zero`), decided in the faithful
  **real** `4 × 4` frame `repCl` that the project already used for `iota_injective`;
* conjugation by a generator multiplies each monomial by an explicit sign
  (`cle0_conj_monoComb`, `cle1_conj_monoComb`), whence an element commuting with `e₀` and
  `e₁` is `a·1 + b·ω` (`eq_scalar_add_omega_of_comm_cle01`), whence the exact centre
  `center_Cl3`;
* `one_omega_indep`, previously proved via the Pauli representation.

Consequently the intrinsic chain up to and including `SpinKernel` no longer imports
`MatrixModel` or `PauliRepresentation` at all.  **No comparison theorem is required by the
intrinsic double cover, and none is used.**

## 4. Provenance mapping for moved declarations

| Old Spine declaration | Historical experiment-1 origin | New declaration | Proof |
| --- | --- | --- | --- |
| `SpinCore.SpinGrp` (`Spine/E1/SL2Comparison.lean`) | `Task11SpinSL2` / `SpinFinal` spin subgroup | `SpinCore.SpinGroup` (`Spine/E1/SpinGroup.lean`) | moved unchanged; only the name changed (`SpinGrp → SpinGroup`) |
| `SpinCore.spinUnit`, `mem_SpinGrp` (`SL2Comparison`) | same | `SpinCore.spinUnit`, `SpinCore.mem_SpinGroup` (`SpinGroup.lean`) | moved unchanged |
| — | — | `SpinCore.mkSpin`, `SpinCore.negOneSpin`, `negOneSpin_sq`, `negOneSpin_ne_one`, `spinGroup_neg_one_central` | new packaging (bundled constructor and the `-1` element) |
| `SpinCore.spinCover`, `spinCover_apply` (`SL2Comparison`) | `SpinFinal` covering map | `SpinCore.spinCover`, `spinCover_apply` (`Spine/E1/SpinCover.lean`) | moved unchanged (uses `mkSpin`); imports of `MatrixModel` / `PauliRepresentation` removed |
| `SpinCore.spinCover_surjective` (`SL2Comparison`) | `SpinFinal` | `SpinCore.spinCover_surjective` (`SpinCover.lean`) | moved unchanged |
| `SpinCore.spinCover_kernel` (`SL2Comparison`) | `SpinFinal` | `SpinCore.mem_ker_spinCover_iff'` (same statement) and `mem_ker_spinCover_iff` (phrased with `MonoidHom.ker` and `±1` read in `Cl3ˣ`) | moved unchanged, then repackaged; the underlying fact is still `SpinCore.kernel_exactly_pm_one` |
| `SpinCore.task11_V5` (`SL2Comparison`) | `SpinFinal` bundled verdict | `SpinCore.sl2_comparison` (`SL2Comparison.lean`) | restated with the moved names; same three conjuncts |
| `SpinCore.center_Cl3` (`Spine/E1/PauliRepresentation.lean`) | `Task9` centre theorem via `M₂(ℂ)` | `SpinCore.center_Cl3` (`Spine/E1/CliffordMonomial.lean`) | **reconstructed** intrinsically (see §3); statement identical |
| `SpinCore.one_omega_indep` (`Spine/E1/Paravector.lean`) | `Task9` | `SpinCore.one_omega_indep` (`CliffordMonomial.lean`) | **reconstructed** from the real frame; statement identical |
| `mono`, `monoSpan`, `monoComb`, `monoSpan_eq_top`, `exists_monoComb`, `monoComb_expand`, `adjoin_cle_top`, `cle*_mul_mono` (`PauliRepresentation`) | `Task9` | same names in `CliffordMonomial.lean` | **moved unchanged**; they never used the matrix model |
| `cconj_cconj`, `isSpinElem_cconj` (`Spine/E1/Paravector.lean`) | `Task11Spin` | same names in `Spine/E1/SpinElement.lean` | moved unchanged (they belong to the predicate layer) |
| module `Spine/E1/SpinGroup.lean` (predicate layer) | `Task11Spin` | module `Spine/E1/SpinElement.lean` | file renamed with `git mv`; contents unchanged apart from the header and the two lemmas above |

No statement was strengthened by the rearrangement.  The only *new* mathematical content
is: the intrinsic proofs of §3, the kernel repackaging (`zpowers`, `Nat.card = 2`,
centrality), and `SpinCore.spinEquivSL2_negOne` (compatibility of the two kernel
descriptions).

Historical trees `RequestProject/Experiment1/**` and `RequestProject/Experiment2/**` are
untouched and remain provenance.

## 5. Import firewall

`RequestProject/Spine/Audit/Firewall.lean` gains a **level-1b** check
(`auditIntrinsicSpinModule`).  For each module of the intrinsic spin core it recomputes the
transitive import closure from the compiled environment and rejects any module whose name
begins with

```
RequestProject.Experiment1        RequestProject.Spine.E1.SL2Comparison
RequestProject.Experiment2        RequestProject.Spine.E1.MatrixModel
RequestProject.Comparison         RequestProject.Spine.E1.PauliRepresentation
RequestProject.Control            RequestProject.Spine.E1.WeylSpinorModule
RequestProject.Spine.E2
```

Audited at level 1b: `Carrier`, `Clifford`, `LorentzClifford`, `CliffordMonomial`,
`SpinElement`, `SpinGroup`, `Paravector`, `SpinDeterminant`, `DoubleCover`, `SpinCover`,
`SpinKernel`.  All eleven pass.

Two positive controls keep the check sensitive and pin the direction of the comparison
edge: `Spine.E1.SL2Comparison` *must* import `Spine.E1.SpinKernel` and
`Spine.E1.PauliRepresentation`.  The pre-existing level-1 and level-2 checks, the
declaration-closure audit and its positive controls are unchanged; the closure audit now
also covers `SpinCore.spin_double_cover` and `SpinCore.spin_double_cover_bundled`.

Build output of the audit: `SPINE FIREWALL AUDIT: all checks passed`.

## 6. Before/after dependency statistics

Computed by `scripts/dep_stats.py` from the `import` lines, counting **project-local**
modules only (`Mathlib` excluded — a cold Lake job count is dominated by Mathlib and is not
used as a proxy for anything here).

| Endpoint | direct (before → after) | transitive (before → after) | legacy E1 | legacy E2 |
| --- | --- | --- | --- | --- |
| `Spine.E1.Core` | 2 → 2 | 19 → 22 | 0 → 0 | 0 → 0 |
| `Spine.E1.SL2Comparison` | 2 → 2 | 18 → 22 | 0 → 0 | 0 → 0 |
| `Spine.E1.SpinKernel` (new intrinsic endpoint) | — → 1 | — → **19** | — → 0 | — → 0 |
| `Spine.E2.Core` | 1 → 1 | 247 → 247 | 0 → 0 | 180 → 180 |

Reading these numbers:

* the counts of `E1.Core` and `SL2Comparison` rise by 3–4 because the refactor **splits**
  modules (three new files plus `CliffordMonomial`); no new mathematical dependency was
  added, and both remain free of the historical trees;
* the number that matters is the third row: the intrinsic double-cover endpoint
  `Spine.E1.SpinKernel` closes over 19 project modules and **none** of `MatrixModel`,
  `PauliRepresentation`, `SL2Comparison`, `WeylSpinorModule`.  Before this pass the same
  content was only available from `SL2Comparison`, whose closure necessarily contained all
  of them;
* `Spine.E2.Core` is deliberately unchanged: no experiment-2 rewrite was attempted (Part F).

Additional measurements, unchanged by this pass and quoted for the interface discussion:

| Module | direct | transitive | legacy E2 |
| --- | --- | --- | --- |
| `Spine.E2.CentralDoubleCover` (generic interface) | 0 | 0 | 0 |
| `Spine.E2.Lift.TransitionLiftBase` (generic lift layer) | 2 | 18 | 0 |
| `Spine.E2.Model.CertifiedProjection` (legacy instantiation) | 2 | 203 | 180 |

**Build behaviour.**  Cold build of the three endpoints (`E1.Core`, `E1.SL2Comparison`,
`E2.Core`) before the refactor: 8294 Lake jobs, 66 min wall (dominated by Mathlib and by the
180 legacy experiment-2 modules under `E2.Core`).  After the refactor, rebuilding the
affected experiment-1 chain (11 modules from `SpinElement` to `Core`) took 4 min 28 s.
Incremental behaviour of the new split: editing `Spine/E1/SpinCover.lean` in a way that does
not change its `.olean` (a comment) rebuilds that module alone, 15 s / 29 s wall; a real
change to it rebuilds only `SpinKernel`, `SL2Comparison` and `Core`.

## 7. Axiom audit

`#print axioms` lines are compiled into the modules themselves.  Every one of

```
SpinCore.spinCover                  SpinCore.spinCover_ker_central
SpinCore.spinCover_surjective       SpinCore.spinCover_ker_card
SpinCore.mem_ker_spinCover_iff      SpinCore.spin_double_cover
SpinCore.spinCover_ker_eq_zpowers   SpinCore.spin_double_cover_bundled
SpinCore.spinEquivSL2               SpinCore.sl2_comparison
SpinCore.lorentz_quadratic_form     SpinCore.mem_lorentz_group_iff
SpinCore.clifford_generator_square  SpinCore.paravector_norm
SpinCore.spin_double_cover_of_lorentz  SpinCore.weyl_clifford_module
```

reports exactly `[propext, Classical.choice, Quot.sound]`.  No `sorry`, no `admit`, no
`axiom` declaration, no `@[implemented_by]`, no `native_decide` was introduced.

## 8. Failed builds encountered in this pass

| # | Failing declaration / file | Error | Diagnosis | Repair | Final status |
| --- | --- | --- | --- | --- | --- |
| 1 | `SpinCore.cle0_conj_monoComb`, `cle1_conj_monoComb` (`CliffordMonomial.lean`) | linter: `This simp argument is unused: Matrix.cons_val_fin_one` | leftover simp lemma from the exploratory version of the coefficient bookkeeping | removed the argument | green |
| 2 | `SpinCore.eq_scalar_add_omega_of_comm_cle01` (`CliffordMonomial.lean`) | linter: `This simp argument is unused: Matrix.cons_val` | the `![…] i` projections were already reduced, so the normalisation step was a no-op | deleted the line | green |

No compilation *error* occurred in this pass: the extraction, the reconstructed intrinsic
centre theorem and the rewritten comparison layer all elaborated on the first build.  Only
the two linter warnings above were raised, and both were repaired rather than suppressed.
(The earlier refactoring pass's failures remain recorded in `REFACTOR_AUDIT.md`.)

## 9. Part E — the E1 → E2 `InternalProjection` interface table

The generic experiment-2 interface is
`NullSectorTask28.InternalProjection L G` (`Spine/E2/CentralDoubleCover.lean`), whose
fields are listed below against the cleaned experiment-1 cover
`spinCover : SpinGroup →* GLor`.

| `InternalProjection` requirement | Formal shape | E1 status |
| --- | --- | --- |
| source group | `[Group L]` | **proved / available** — `SpinCore.SpinGroup : Subgroup Cl3ˣ` is a `Subgroup`, so the coercion is a group |
| target group | `[Group G]` | **proved / available** — `SpinCore.GLor : Subgroup (LorentzCarrier ≃ₗ[ℝ] LorentzCarrier)` |
| group homomorphism | `proj : L →* G` | **proved / available** — `SpinCore.spinCover` |
| surjective | `Function.Surjective proj` | **proved** — `SpinCore.spinCover_surjective` |
| central kernel | `∀ z ∈ proj.ker, ∀ l, z * l = l * z` | **proved** — `SpinCore.spinCover_ker_central` (exactly this shape) |
| exact kernel `{±1}` | — (not a field; the interface only needs centrality + discreteness) | **proved** — `SpinCore.mem_ker_spinCover_iff`, `spinCover_ker_eq_zpowers`, `spinCover_ker_card = 2` |
| topology on source | `[TopologicalSpace L]` | **missing** — no topology is put on `Cl3ˣ`, on `Cl₃(ℝ)` or on `SpinGroup` anywhere in the project.  Mathlib has the pieces (`CliffordAlgebra` is a finite-dimensional real algebra, so `Module.finrank`-based `TopologicalSpace`/`IsTopologicalRing` instances exist for finite-dimensional real vector spaces, and `Units.instTopologicalSpace` topologises `Cl3ˣ`), but no instance is currently *declared* for `Cl3`, and the finite-dimensionality of `CliffordAlgebra q3` is itself not established in this project |
| source is a topological group | `[IsTopologicalGroup L]` | **missing** — follows from the above once the topology exists (`Units.instIsTopologicalGroup` for a topological ring with continuous inversion on units), but nothing of this is packaged here |
| topology on target | `[TopologicalSpace G]` | **missing** — `GLor` sits inside `LorentzCarrier ≃ₗ[ℝ] LorentzCarrier`; the carrier is `ℝ × (Fin 3 → ℝ)` and is finite-dimensional, so a topology is available from Mathlib in principle, but none is declared and no `IsTopologicalGroup` instance is packaged |
| continuity of `proj` | `Continuous proj` | **missing** — cannot even be stated before the two topologies exist.  Mathematically it is the restriction of the polynomial map `g ↦ (x ↦ g A(x) g̃)`, so it should be routine once the instances are in place; it is *not* proved |
| discrete kernel | `DiscreteTopology proj.ker` | **missing as a topological statement**; the algebraic input is complete (`Nat.card ker = 2`).  Mathlib supplies `DiscreteTopology` for any finite subsingleton-separated subspace of a T1 space, so this reduces to the source topology being T1 (or Hausdorff) — again available in principle, not packaged |
| local continuous sections | `∀ k, ∃ V open ∋ k, ∃ s, ContinuousOn s V ∧ ∀ y ∈ V, proj (s y) = y` | **genuinely missing mathematics** — this is a local-triviality statement for the covering `Spin → SO⁺(1,3)`.  It is *not* a packaging exercise: it needs either an explicit local section (e.g. the paravector square root already used for the boost part of surjectivity, `SpinCore.exists_spin_boost`, together with a rotation-side section) plus a continuity proof, or a general covering-space argument that Mathlib does not provide for this cover |

Classification of the gaps:

* **already proved:** source/target groups, homomorphism, surjectivity, kernel exactness,
  kernel centrality, kernel order two;
* **available from Mathlib, needs packaging only:** finite-dimensional real topology on
  `Cl₃(ℝ)` and hence on `Cl3ˣ` and `SpinGroup`; topology on the target group; the resulting
  `IsTopologicalGroup` instances; discreteness of a two-element subgroup of a T1 group;
* **needs a short new proof, but no new theory:** continuity of `spinCover`;
* **genuinely missing mathematical theorem:** existence of continuous local sections of
  `spinCover` around every element of `GLor`.

Per the task, no new topology was proved to fill this table.

### Exact list of still-missing facts required to instantiate the generic machinery

To construct a term `InternalProjection SpinGroup GLor` the following must be added:

1. `TopologicalSpace Cl3` together with `IsTopologicalRing Cl3` (via finite-dimensionality
   of `CliffordAlgebra q3` over `ℝ`, which must itself be established: Mathlib's
   `CliffordAlgebra` files prove no `FiniteDimensional`/`Module.Finite` instance.  The
   intrinsic core already contains what is needed — `SpinCore.monoSpan_eq_top` exhibits an
   eight-element spanning set and `SpinCore.monoComb_coeffs_eq_zero` its independence — so
   `finrank ℝ Cl3 = 8` is packaging, not new mathematics, and it does **not** have to go
   through the `M₂(ℂ)` isomorphism);
2. the induced `TopologicalSpace SpinGroup` and `IsTopologicalGroup SpinGroup`
   (through `Cl3ˣ`);
3. `TopologicalSpace GLor` and `IsTopologicalGroup GLor` (through
   `LorentzCarrier ≃ₗ[ℝ] LorentzCarrier`);
4. `Continuous spinCover`;
5. `DiscreteTopology (spinCover.ker)` — from 2 (T1) and `Nat.card ker = 2`;
6. `∀ F : GLor, ∃ V open ∋ F, ∃ s : GLor → SpinGroup, ContinuousOn s V ∧ ∀ G ∈ V,
   spinCover (s G) = G` — the local continuous section; the only item requiring genuinely
   new mathematics.

Items 1–3 and 5 are packaging; item 4 is a short proof; item 6 is the real bridge task.

## 10. Part F — the legacy Task-23 projection is temporary

`Spine/E2/Model/CertifiedProjection.lean` still imports
`RequestProject.Experiment2.NullSectorTask23.Task23` directly, and through it 180 legacy
experiment-2 modules.  This is the historical concrete two-to-one projection, retained only
so that the generic lift machinery has *some* instance to be exercised on.

**It is explicitly not intended to become the Spin projection of the merged architecture.**
The intended future shape is

```
E1 intrinsic SpinGroup --spinCover--> Lorentz group --> E2 generic lift machinery
```

rather than the current

```
historical E2 Task01 → … → Task23 → E2 generic lift machinery
```

No new production module introduces any dependency on the legacy Task-23 chain: the
level-1 firewall forbids `RequestProject.Experiment2` in every production module except the
model-instantiation layer, and the new experiment-1 modules of this pass are additionally
audited at level 1b, which forbids `RequestProject.Spine.E2` as well.  No experiment-2
rewrite was attempted in this task.

## 11. Non-goals respected

Nothing in this pass constructs or mentions a Lorentzian manifold, tangent or frame
bundles, orientability, time orientability, `w₁`, `w₂`, a global Spin structure, a spinor
bundle, a Levi-Civita or Spin connection, Dirac dynamics, or any new physical
interpretation.  No historical physics branch was reopened.
