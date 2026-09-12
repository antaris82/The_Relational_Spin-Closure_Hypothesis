# Task 02 — Local continuous sections of the intrinsic Spin projection, and the native `InternalProjection`

**Result: affirmative.**  The intrinsically reconstructed continuous central two-fold Spin
projection `SpinCore.spinCover : SpinGroup →* GLor` **does** admit continuous local sections
around every point of `GLor`, proved natively from the Clifford realisation, with no input
from `SL(2,ℂ)`, no matrix model, no manifold or Lie-group theorem, no postulated covering-map
or local-homeomorphism property, and no module of either historical experiment tree.  The
generic interface `NullSectorTask28.InternalProjection SpinGroup GLor` is therefore
instantiated natively as `SpinCore.internalSpinProjection`, and the generic E2 lift theory
consumes it.

Nothing from the hypothesis paper is used as a premise; no spacetime, manifold, metric,
vierbein, connection, curvature, synchronization variable, mass or matter is introduced.

---

## 1. WP1 — the exact remaining E1 → E2 gap, verified from source

Source inspected: `RequestProject/Spine/E2/CentralDoubleCover.lean` (definition of
`NullSectorTask28.InternalProjection`), `RequestProject/Spine/E1/Topology/SpinCoverTopology.lean`
(`SpinCore.TopologicalCentralCover`, `SpinCore.topologicalSpinProjection`),
`RequestProject/Spine/E1/SpinCover.lean`, `RequestProject/Spine/E1/SpinKernel.lean`.

`InternalProjection L G` has exactly six fields.  Against the intrinsic cover, as the tree
stood at the start of this task:

| `InternalProjection` field | status before Task 2 | witness in the source |
|---|---|---|
| `proj : L →* G` | CLOSED | `SpinCore.spinCover` (`E1/SpinCover.lean`) |
| `continuous_proj` | CLOSED | `SpinCore.continuous_spinCover` (`E1/Topology/SpinCoverTopology.lean`) |
| `surjective_proj` | CLOSED | `SpinCore.spinCover_surjective` (`E1/SpinCover.lean`) |
| `hasLocalSection` | **OPEN** | — none; `TopologicalCentralCover` deliberately has no such field |
| `ker_central` | CLOSED | `SpinCore.spinCover_ker_central` (`E1/SpinKernel.lean`) |
| `ker_discrete` | CLOSED | `SpinCore.instDiscreteTopologySpinCoverKer` (`E1/Topology/SpinCoverTopology.lean`) |

Additional inherited facts, not required by the interface but used below:
`SpinCore.spinCover_ker_card` (`Nat.card (ker) = 2`), `SpinCore.mem_ker_spinCover_iff`
(`u ∈ ker ↔ u = 1 ∨ u = -1`), `T2Space` for both groups.

So the expected situation of the task statement is confirmed **from source**: exactly one
substantive obligation was open, `hasLocalSection`.

---

## 2. WP2 — classification of the routes, and the one taken

* **Route A (direct local construction from the Clifford realisation) — TAKEN.**
  Feasible, and it exposes the intrinsic dependency chain; see §3.
* **Route B (prove a local-homeomorphism/covering property first) — NOT ASSUMED, OBTAINED AS
  A COROLLARY.**  No such property is postulated anywhere.  The local homeomorphism
  `SpinCore.sheetPlusHomeomorph : sheetPlus ≃ₜ LorNbhd` is *derived* from the constructed
  section (§6), not used to obtain it.
* **Route C (Lie-group theorem) — REJECTED.**  No smooth/analytic structure on `SpinGroup`
  or `GLor` exists in the native tree, so the hypotheses of such a theorem cannot be
  discharged without importing the desired conclusion.  Nothing of the sort is used.
* **Route D (transport from `SL(2,ℂ)`/matrix models) — REJECTED, not even as a diagnostic.**
  The mechanical firewall (`RequestProject/Spine/Audit/Firewall.lean`) now fails the build if
  `Spine.E1.Topology.LocalSection` or `Spine.E2.SpinProjection` ever reaches
  `Spine.E1.SL2Comparison`, `Spine.E1.MatrixModel`, `Spine.E1.PauliRepresentation`,
  `Spine.Controls.**`, `Experiment1/**` or `Experiment2/**`.

---

## 3. WP3 — the minimal local mechanism

Discreteness of a two-element kernel plus Hausdorffness of both groups is **not** sufficient
for local sections in general (remark, *not formalised in this project*: the identity
homomorphism from `ℝ` with the discrete topology onto `ℝ` with its usual topology is a
continuous surjective homomorphism of Hausdorff topological groups with trivial — hence
central and discrete — kernel and admits no continuous local section).  Something must
produce a *continuous two-valued inverse*.  In the intrinsic cover that something is
algebraic, and the chain is exactly:

1. **Contraction identity (algebraic).**  `SpinCore.fierz y = y + Σᵢ eᵢ y eᵢ` takes values in
   the centre `ℝ ⊕ ℝω` (`SpinCore.fierz_eq_central`, proved by evaluating the three
   conjugations in the intrinsic eight-monomial frame), and `fierz 1 = 4`.
2. **Reconstruction identity (algebraic).**  With `A` the paravector embedding and
   `b₀ = 1, bᵢ = eᵢ`,
   `SpinCore.recon F = Σ_μ A(F b_μ) · A(b_μ)` is **linear in `F`** and satisfies
   `recon (spinLorLin g) = g · fierz (reverse g)` (`SpinCore.recon_spinLorLin`).
   Hence the reconstruction of the action of a spin element returns that element up to a
   **central** factor.
3. **The centre is a field (algebraic).**  `SpinCore.cx : ℂ →ₐ[ℝ] Cl₃(ℝ)`, `i ↦ ω`
   (legitimate by `omega_sq : ω² = -1`), is injective, central-valued and fixed by Clifford
   conjugation.  Writing `recon (ρ u) = cx w · u`, the spin condition `u · cconj u = 1` gives
   `recon · cconj recon = cx (w²)`, so
   **`SpinCore.spinDisc F = w²` is a genuine function of `F` alone** — the `ℤ/2` ambiguity is
   exactly the ambiguity of a square root of the discriminant.
4. **A continuous branch of the square root (topological).**  This is the *only* analytic
   ingredient.  `spinDisc 1 = 16`, and on the open set
   `LorNbhd = {F | spinDisc F ∈ Complex.slitPlane}` the principal branch `z ↦ z^(1/2)` is
   continuous; dividing by it produces a continuous map whose value at each `F` is `±u`.
5. **Values land in the group (algebraic).**  Since the normalised value is `±u` for a
   genuine `u ∈ SpinGroup`, it *is* a spin element, and its inverse is its Clifford
   conjugate — which is what makes the section continuous as a map into the **unit group**.
6. **Transport (group-theoretic).**  Left translation by any chosen lift moves the identity
   neighbourhood anywhere; continuity of multiplication does the rest.

Ingredients from the possible list that are **not** needed: openness of `ρ`, local injectivity
as an input, separation of `+1` from `-1` as an input.  (Local injectivity and the separation
of the two sheets come out as *consequences*, §6.)  Hausdorffness of the source is used only
where it was already used in Task 1 (kernel discreteness) and, in §6, to see that the two
sheets are relatively closed.

---

## 4. WP4 — the identity-neighbourhood argument, explicitly

Let `U = LorNbhd`, an open neighbourhood of `1` in `GLor` (`SpinCore.isOpen_LorNbhd`,
`SpinCore.one_mem_LorNbhd`, the latter because `spinDisc 1 = 16 ∈ slitPlane`).

* `SpinCore.secCl F = cx ((csqrt (spinDisc F))⁻¹) · spinRecon F` is defined for all `F`, and
  is continuous on `U` (`SpinCore.continuousOn_secCl`).
* `SpinCore.secCl_spinCover`: if `spinDisc (ρ u) ≠ 0` then `secCl (ρ u) = u` or
  `secCl (ρ u) = -u`.  (Two-valued, never more, never fewer.)
* Consequently `secCl F` is a spin element whenever `spinDisc F ≠ 0`
  (`SpinCore.isSpinElem_secCl`), and `SpinCore.spinSection F : SpinGroup` satisfies
  `ρ (spinSection F) = F` (`SpinCore.spinCover_spinSection`) and `spinSection 1 = 1`
  (`SpinCore.spinSection_one`).
* `SpinCore.continuousOn_spinSection : ContinuousOn spinSection LorNbhd` — continuity into the
  unit group uses both `val` and `inv`, and `inv = cconj` on spin elements.

Set `W = sheetPlus = {u | ρ u ∈ U ∧ spinSection (ρ u) = u}` (§6).  Then, **proved**:

* `W` is open and `1 ∈ W`;
* `W ∩ (-W) = ∅`, where `-W = negOneSpin • W = sheetMinus`
  (`SpinCore.sheetPlus_disjoint_sheetMinus` + `SpinCore.sheetMinus_eq_image`);
* `ρ` is injective on `W` and `ρ '' W = U` (`SpinCore.bijOn_spinCover_sheetPlus`), so
  **`ρ (W)` is open**;
* `ρ|W : W → U` is a homeomorphism (`SpinCore.sheetPlusHomeomorph`), with inverse
  `spinSection`.

So all four questions of WP4 are answered affirmatively, and nothing is missing.

---

## 5. WP5 — transport, and the exact dependence on the chosen lift

`SpinCore.LorNbhdAt k = (k⁻¹ · ·) ⁻¹' LorNbhd` is open and contains `k`.  For a chosen lift
`ut` with `ρ ut = k`,

```
SpinCore.transportSection ut F = ut * spinSection ((ρ ut)⁻¹ * F)
```

is continuous on `LorNbhdAt k` (`SpinCore.continuousOn_transportSection`) and satisfies
`ρ (transportSection ut F) = F` there (`SpinCore.spinCover_transportSection`).  This yields
the endpoint `SpinCore.spinCover_hasLocalSection`.

Dependence on the choice, stated separately and never conflated:

| notion | status |
|---|---|
| **existence** of a local section around every `k` | **proved**, `SpinCore.spinCover_hasLocalSection` |
| **uniqueness** of a local section | **false / not claimed** — see the next two rows |
| **uniqueness modulo the kernel action** | **proved pointwise**: any two lifts of the same element satisfy `v = u ∨ v = (-1)·u` (`SpinCore.lift_ambiguity`); hence two sections on the same set agree up to a `{±1}`-valued function |
| **dependence on the chosen lift** | **proved exactly**: `transportSection ((-1)·ut) = (-1) · transportSection ut` (`SpinCore.transportSection_negOneSpin`) |
| **local uniqueness after fixing a sheet** | **proved**: on `LorNbhd`, `spinSection` is the unique section with values in `sheetPlus` (`SpinCore.invOn_spinSection_sheetPlus` + `SpinCore.bijOn_spinCover_sheetPlus`) |

---

## 6. WP6 — the exact local two-sheet statement (the strongest justified one)

Over `U = LorNbhd` (an explicit open neighbourhood of `1`, *not* over an arbitrary small open
set, and *not* over all of `GLor`):

```
sheetPlus  = {u | ρ u ∈ U ∧ spinSection (ρ u) = u}
sheetMinus = {u | ρ u ∈ U ∧ spinSection (ρ u) = (-1) * u}
```

Proved (`SpinCore.intrinsic_spin_cover_local_two_sheets`):

* `ρ⁻¹(U) = sheetPlus ∪ sheetMinus` and `Disjoint sheetPlus sheetMinus`;
* both sheets are **open** — not assumed: each is relatively closed in the open set `ρ⁻¹(U)`
  as the equaliser of two continuous maps into a Hausdorff group, and each is the relative
  complement of the other;
* `sheetMinus = (-1) · sheetPlus`;
* `1 ∈ sheetPlus`;
* `Set.BijOn ρ sheetPlus U`, `Set.InvOn spinSection ρ sheetPlus U`, and the bundled
  homeomorphism `SpinCore.sheetPlusHomeomorph : sheetPlus ≃ₜ U`.

By translation the same picture holds over `LorNbhdAt k` for every `k`; the *global* statement
"`ρ` is a covering map" is **not** claimed, because the two-sheet decomposition is proved only
over the explicitly constructed neighbourhoods.

---

## 7. WP7 — the native `InternalProjection`

`RequestProject/Spine/E2/SpinProjection.lean`:

```
SpinCore.internalSpinProjection : NullSectorTask28.InternalProjection ↥SpinGroup ↥GLor
```

with fields `spinCover`, `continuous_spinCover`, `spinCover_surjective`,
`spinCover_hasLocalSection`, `spinCover_ker_central`, `instDiscreteTopologySpinCoverKer`, and
the unbundled endpoint `SpinCore.intrinsic_spin_internal_projection` recording all five
required properties plus `Nat.card (ker) = 2`.

It is not an adapter or bridge to historical code: its import closure is `Mathlib`, the
intrinsic E1 chain with its topology layer, and the generic `Spine.E2.CentralDoubleCover`
(27 project-local modules, `Experiment1 = Experiment2 = 0`, direct and transitive).

---

## 8. WP8 — E2 integration smoke test

`RequestProject/Spine/E2/SpinProjectionIntegration.lean` exercises the *already generic* lift
theory on the native projection:

* `SpinCore.spin_local_internal_representative` — Package C: every continuous map into `GLor`
  has, locally, a continuous internal (spin) representative;
* `SpinCore.spin_internal_reps_differ_by_kernel` — the exact kernel ambiguity of two such
  representatives;
* `SpinCore.spinTautSystem` — a concrete one-chart transition system valued in `GLor`, so the
  statements below are not vacuous;
* `SpinCore.spin_levelB` / `SpinCore.spin_levelB_taut` — Level B: the frozen candidate
  interface `InternalTransitionCandidate` is inhabited;
* `SpinCore.spin_defect_isKerFunOn`, `SpinCore.spin_defect_isLocallyConstant` — the
  triple-overlap defect of such a candidate is kernel-valued, continuous and locally constant.

No tangent-frame bundle, no spacetime spin structure, no global lifting claim: Level C is
neither asserted nor refuted.

---

## 9. New dependency DAG

```
Mathlib
 │
 ├─ Spine/E1/Carrier → Clifford → LorentzClifford → CliffordHodgeBridge → CliffordMonomial
 │        → SpinElement → SpinGroup → Paravector → SpinDeterminant → DoubleCover
 │        → SpinCover → SpinKernel                                   (intrinsic algebra, Task 0/1)
 │
 ├─ Spine/E1/Topology/FiniteDimTools
 │        → CliffordTopology → SpinTopology
 │        → LorentzTopology
 │        → SpinCoverTopology                                        (Task 1)
 │        → **LocalSection**                                         (NEW, Task 2)
 │        → Topology/Core          (re-exports the local-section endpoint)
 │
 ├─ Spine/E2/CentralDoubleCover    (generic interface, Mathlib only)
 │
 ├─ **Spine/E2/SpinProjection**    (NEW: LocalSection + CentralDoubleCover → internalSpinProjection)
 │
 ├─ **Spine/E2/SpinProjectionIntegration** (NEW: SpinProjection + Lift/LiftLevels)
 │
 └─ Spine/Core  ⟵ E1.Core, E1.SL2Comparison, E2.Core, E2.SpinProjection,
                   E2.SpinProjectionIntegration
```

Direction: **E1 never imports E2.**  The local-section theorem lives in E1 and is only
consumed in E2.  Project-local closure sizes (from `scripts/legacy_audit.py`):
`Spine.E1.Topology.Core` 26, `Spine.E1.Core` 29, `Spine.E2.SpinProjection` 27,
`Spine.E2.SpinProjectionIntegration` 52, `Spine.Core` 100, `Spine.Audit.Firewall` 107 — all
with `Experiment1 = 0`, `Experiment2 = 0`, direct and transitive.

---

## 10. Canonicality table

`INTRINSIC` = determined by the algebraic/topological data with no choice;
`CHOICE_UP_TO_KERNEL` = determined up to the central `{±1}`;
`ADDITIONAL_CHOICE` = a genuine extra choice (recorded, and its effect stated).

| object | canonicality | remark |
|---|---|---|
| `spinCover`, its continuity, surjectivity, kernel | INTRINSIC (inherited) | Task 1 |
| `fierz` | INTRINSIC | canonical contraction; no frame in the statement (the monomial frame is used only in the proof) |
| `fierz_eq_central`, `fierz_one` | INTRINSIC | |
| `cx : ℂ →ₐ[ℝ] Cl₃(ℝ)` | ADDITIONAL_CHOICE (orientation) | the two algebra maps `i ↦ ±ω` are interchanged by reversing the orientation of the frame; both give valid sections |
| `cxRetract` | ADDITIONAL_CHOICE, value-irrelevant | only `cxRetract ∘ cx = id` is used, and every argument at which it is evaluated on `GLor` lies in the image of `cx`; so `spinDisc` is independent of the retraction |
| `recon`, `spinRecon` | INTRINSIC | linear in the endomorphism |
| `spinDisc` | INTRINSIC (given `cx`) | equals `w²`; the un-squared `w` is *not* a function of `F` — this is precisely the `ℤ/2` |
| `csqrt` (principal branch) | ADDITIONAL_CHOICE = sheet choice | equivalent to choosing one of the two sheets |
| `LorNbhd` | ADDITIONAL_CHOICE (a domain) | a *specific* open neighbourhood of `1`; existence of some such neighbourhood is intrinsic |
| `secCl`, `spinSection` | CHOICE_UP_TO_KERNEL | `spinSection 1 = 1` normalises it; any other continuous section on `LorNbhd` differs pointwise by an element of `{±1}` |
| `sheetPlus` / `sheetMinus` (as a *labelled pair*) | CHOICE_UP_TO_KERNEL | the *unordered* decomposition of `ρ⁻¹(LorNbhd)` is intrinsic; which one is "plus" is the branch choice |
| `transportSection ut` | CHOICE_UP_TO_KERNEL | changing `ut ↦ -ut` multiplies the section by `-1` |
| `spinCover_hasLocalSection` (the existential) | INTRINSIC | a `Prop`: no choice survives in the statement |
| `internalSpinProjection` | INTRINSIC | all fields but `proj` are `Prop`s; given `proj = spinCover` the instance is unique |

**The boundary the task asks to keep visible.**  The *intrinsic projection structure* —
`spinCover` together with the five proved properties, i.e. `internalSpinProjection` — carries
no choice at all.  Every choice made in this task lives in the *local representative*: the
branch/sheet and the lift used for transport, and both are choices exactly up to the central
`ℤ/2`.  No scalar parameter (`Σ`, `λ`, `v`, `M` or similar) is introduced anywhere, and the
full `Spin`/`ℤ₂` lifting structure is preserved rather than reduced.

---

## 11. Final classification of every result of this task

| result | classification |
|---|---|
| `fierz`, `fierz_monoComb`, `fierz_eq_central`, `fierz_one` | DERIVED_NATIVE |
| `cle2_conj_monoComb` | DERIVED_NATIVE |
| `cx`, `cx_apply`, `cx_injective`, `cx_central`, `cconj_cx`, `continuous_cx` | DERIVED_NATIVE |
| `cxRetract`, `cxRetract_cx`, `continuous_cxRetract` | ADDITIONAL_CHOICE (proof device; absent from the endpoint statements) |
| `recon`, `recon_spinLorLin`, `continuous_recon` | DERIVED_NATIVE |
| `spinRecon`, `spinRecon_spinCover`, `exists_cx_spinRecon` | DERIVED_NATIVE |
| `spinDisc`, `spinDisc_of_cx_spinRecon`, `spinDisc_one`, `continuous_spinDisc` | DERIVED_NATIVE |
| `csqrt`, `csqrt_mul_self`, `csqrt_ne_zero`, `continuousOn_csqrt`, `csqrt_sixteen` | ADDITIONAL_CHOICE (branch), Mathlib-only |
| `secCl`, `secCl_spinCover`, `secCl_one`, `continuousOn_secCl` | CHOICE_UP_TO_KERNEL |
| `spinSection`, `spinCover_spinSection`, `spinSection_one`, `continuousOn_spinSection` | CHOICE_UP_TO_KERNEL |
| `lift_ambiguity` | DERIVED_NATIVE |
| `LorNbhd`, `isOpen_LorNbhd`, `one_mem_LorNbhd`, `LorNbhdAt`, `isOpen_LorNbhdAt` | DERIVED_NATIVE (domain, dependent on the branch choice) |
| `transportSection`, `spinCover_transportSection`, `continuousOn_transportSection`, `transportSection_negOneSpin` | CHOICE_UP_TO_KERNEL |
| **`spinCover_hasLocalSection`**, `intrinsic_spin_cover_hasLocalSection` | **DERIVED_NATIVE** |
| `sheetPlus`, `sheetMinus`, `preimage_LorNbhd_eq`, `sheetPlus_disjoint_sheetMinus`, `sheetMinus_eq_image`, `isOpen_sheetPlus`, `isOpen_sheetMinus`, `bijOn_spinCover_sheetPlus`, `invOn_spinSection_sheetPlus`, `sheetPlusHomeomorph` | DERIVED_NATIVE (labelling CHOICE_UP_TO_KERNEL) |
| `intrinsic_spin_cover_local_two_sheets` | DERIVED_NATIVE |
| `spin_double_cover_local_sections`, `spin_double_cover_local_section_endpoint` | INHERITED_CANONICAL (re-exports) |
| **`internalSpinProjection`**, `intrinsic_spin_internal_projection` | **DERIVED_NATIVE** |
| `internalSpinProjection_Ker` | INHERITED_CANONICAL |
| integration test (`spin_local_internal_representative`, `spin_internal_reps_differ_by_kernel`, `spinTautSystem`, `spin_levelB`, `spin_levelB_taut`, `spin_defect_isKerFunOn`, `spin_defect_isLocallyConstant`) | INHERITED_CANONICAL (generic theory instantiated) |
| global section, covering map over all of `GLor`, manifold/frame-bundle/spin-structure material | NOT_REQUIRED (out of scope for this task) |
| — | nothing is BLOCKED |

---

## 12. Failbuild ledger (append-only)

Every failed build of this task, in order.  None of them changed a *statement*: all repairs
were tactic-level or naming-level.

| # | failing command | error | diagnosis | repair | statement change |
|---|---|---|---|---|---|
| 1 | `lake build …Topology.LocalSection` | `No goals to be solved` (`cx_surjective_onto_center`) | `rw [cx_apply]` already closed the goal; the trailing `rfl` had no goal | dropped `rfl`; renamed the lemma `cx_mk` | none |
| 2 | (scratch elaboration of `cx_apply`) | `rewrite failed: pattern ?r • ?x * ?y not found` | only the first `algebraMap` had been turned into a scalar action before `smul_mul_assoc` was applied | rewrote both `algebraMap` occurrences first | none |
| 3 | `lake build …Topology.LocalSection` | `Type mismatch: After simplification …` (`continuous_endLor_apply`) | `simpa` unfolded the product carrier of `LorentzCarrier` into components | replaced `simpa using h` by `exact h` | none |
| 4 | `lake build …Topology.LocalSection` | `rewrite failed: cx ?z * ?y not found` (`exists_cx_spinRecon`) | `rw [cx_mk]` had rewritten the right-hand side, so the `cx_central` pattern was gone | `rw [← cx_mk]` then `exact (cx_central _ _).symm` | none |
| 5 | `lake build …Topology.LocalSection` | `Unknown constant Complex.continuousAt_cpow_const` | the Mathlib lemma is in the root namespace, not in `Complex` | used `continuousAt_cpow_const` | none |
| 6 | `lake build …Topology.LocalSection` | `rewrite failed` + `failed to synthesize Inv Cl3` (`continuousOn_spinSection`) | the goal appears as `Units.val ∘ Subtype.val ∘ restrict …`, and the ascription `(u⁻¹ : Cl3)` forced inversion in the ring instead of in the unit group | used `show` to state the two goals as explicit lambdas and `(… : Cl3ˣ)⁻¹ |>.val` for the inverse | none |
| 7 | `lake build …Topology.LocalSection` | `unsolved goals` + two `rewrite failed: ?a * (?b * ?c)` (§10 sheet lemmas) | ad-hoc `mul_assoc`/`pow_two` rewriting inside the sheet proofs | factored out `negOneSpin_mul_self`, `negOneSpin_mul_mul`, `spinCover_negOneSpin_mul` and used them | none |
| 8 | `lake build …Topology.LocalSection` (linter) | `unused variable z` | unused binder in `continuousOn_csqrt` | renamed to `_` | none |
| 9 | `lake build …Topology.LocalSection` (linter) | `unused variable u`, `unused variable F` | unused binders in `invOn_spinSection_sheetPlus` | renamed to `_` | none |

`RequestProject/Spine/E2/SpinProjection.lean` and
`RequestProject/Spine/E2/SpinProjectionIntegration.lean` compiled at the first attempt; no
failure to record.

---

## 13. Build evidence (all re-run at the end, in this order)

```
lake build RequestProject.Spine.E1.Core                       Build completed successfully (8055 jobs).
lake build RequestProject.Spine.E1.Topology.Core              Build completed successfully (8052 jobs).
lake build RequestProject.Spine.E1.Topology.LocalSection      Build completed successfully (8051 jobs).   [new]
lake build RequestProject.Spine.E2.Core                       Build completed successfully (8091 jobs).
lake build RequestProject.Spine.E2.SpinProjection             Build completed successfully (8053 jobs).   [new]
lake build RequestProject.Spine.E2.SpinProjectionIntegration  Build completed successfully (8078 jobs).   [new]
lake build RequestProject.Spine.Core                          Build completed successfully (8126 jobs).
lake build RequestProject.Spine.Audit.Firewall                Build completed successfully (8133 jobs).
lake build                                                    Build completed successfully (8137 jobs).
```

`RequestProject.Spine.Audit.Firewall` prints `SPINE FIREWALL AUDIT: all checks passed`, now
including the two new checks that `Spine.E1.Topology.LocalSection` reaches no `Spine.E2`,
`SL(2,ℂ)`, matrix-model, control or historical module, and that `Spine.E2.SpinProjection`
does reach both `Spine.E1.Topology.LocalSection` and `Spine.E2.CentralDoubleCover` (positive
controls, so the audit is sensitive) while reaching no forbidden prefix.

`python3 scripts/legacy_audit.py` → `RESULT: PASS`, with the two new endpoints added to its
endpoint list:

```
Experiment1 direct imports    = 0      Experiment1 transitive imports = 0
Experiment2 direct imports    = 0      Experiment2 transitive imports = 0
```

for every module of `Spine/**`, including all three new ones.

Source discipline: no `sorry`, no `admit`, no project-local `axiom`, no `unsafe`, no
`partial` (outside the two pre-existing `partial def`s of the audit's import-graph walker),
no `@[implemented_by]`, no `native_decide` anywhere under `RequestProject/Spine/**`.

---

## 14. Axiom audit

`#print axioms` is emitted by the modules themselves at build time.  Every principal new
declaration reports exactly `[propext, Classical.choice, Quot.sound]`:

```
SpinCore.fierz_eq_central                      SpinCore.recon_spinLorLin
SpinCore.secCl_spinCover                       SpinCore.spinCover_spinSection
SpinCore.continuousOn_spinSection              SpinCore.spinSection_one
SpinCore.lift_ambiguity                        SpinCore.spinCover_hasLocalSection
SpinCore.intrinsic_spin_cover_local_two_sheets SpinCore.intrinsic_spin_cover_hasLocalSection
SpinCore.spin_double_cover_local_sections      SpinCore.spin_double_cover_local_section_endpoint
SpinCore.internalSpinProjection                SpinCore.intrinsic_spin_internal_projection
SpinCore.spin_local_internal_representative    SpinCore.spin_internal_reps_differ_by_kernel
SpinCore.spin_levelB                           SpinCore.spin_levelB_taut
SpinCore.spin_defect_isKerFunOn                SpinCore.spin_defect_isLocallyConstant
```

---

## 15. Final scientific question — answered

> Does the intrinsically reconstructed continuous central Spin double cover possess native
> local continuous sections, sufficient to instantiate the generic `InternalProjection`
> interface, and if so, which parts of those local lifts are intrinsic and which are choices
> only up to the central `ℤ₂` kernel?

**Yes.**  Local continuous sections exist around every point of `GLor` and are constructed
natively: the twisted Clifford action can be inverted algebraically up to a *central* factor,
that factor is visible only through its square (an intrinsic, continuous, `ℂ`-valued
discriminant), and a continuous branch of the complex square root on a neighbourhood of the
discriminant's value at the identity turns the two-valued inverse into a continuous section.
Transport by left translation extends this to every point.  The generic interface is
therefore instantiated natively as `SpinCore.internalSpinProjection`, and the generic E2 lift
theory consumes it.

What is intrinsic: the projection and all five interface properties (the instance itself is
unique once `proj = spinCover`, since every other field is a proposition); the contraction
identity; the reconstruction map; the discriminant; the *existence* of local sections; and
the *unordered* two-sheet decomposition over each constructed neighbourhood, with the
homeomorphism of each sheet onto the base neighbourhood.

What is a choice, and only up to the central `ℤ₂`: which square-root branch — equivalently
which sheet — is used, and which lift is used to transport the section.  Both change the
resulting local section exactly by multiplication by the kernel element `-1`, never by
anything else (`lift_ambiguity`, `transportSection_negOneSpin`), and the section around the
identity is normalised by `spinSection 1 = 1`.  A chosen local section is therefore a local
representative, not an intrinsic object; the intrinsic object is the projection structure.

No manifold Spin geometry was attempted.
