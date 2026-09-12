# TASK 03 AUDIT — Native Čech Coherence and the Global Spin-Lift Obstruction

Status: **full green build**, no `sorry`, no `admit`, no project-local `axiom`, no `unsafe`,
no `partial`, no `implemented_by`, no `native_decide`.
All Task-3 modules live under `RequestProject/Spine/E2/Cech/`; the control lives under
`RequestProject/Spine/Controls/E2/`.

---

## 0. Final scientific answer

> Does the native intrinsic Spin projection generate a well-defined ℤ₂-valued Čech lifting
> obstruction for Lorentz transition data, invariant under local Spin-representative
> changes and natural under cover refinement, whose vanishing is exactly equivalent to the
> existence of coherent Spin-valued transition data?

**Yes — on a fixed cover, and for transition data that admits local lifts on the double
overlaps.**  Precisely, all of the following are theorems (see §5):

* the triple-overlap defect exists canonically once the lifts are chosen, and is
  `{±1}`-valued (`SpinCore.cech_defect_eq_pm_one`);
* it is continuous and locally constant (discreteness of the kernel);
* it satisfies the exact multiplicative Čech 2-cocycle law
  `c_jkl · c_ikl⁻¹ · c_ijl · c_ijk⁻¹ = 1` (`defect_delta_eq_one`);
* changing the local lifts multiplies it by a 1-coboundary `δε` (`defect_change_of_lift`);
* its class on the fixed cover is independent of the lift choice
  (`obstruction_lift_independent`);
* the class is trivial **iff** coherent Spin-valued transition data exists
  (`obstruction_eq_trivialClass_iff_exists_coherent`), both directions;
* the class is natural under cover refinement (`obstruction_pullLift`).

Two qualifications, both proved-or-documented rather than hidden:

1. **Existence of the local lifts on full overlaps is a hypothesis, not a theorem.**  What is
   unconditional is *pointwise-local* liftability (`exists_lift_nhdsWithin`).  See §4 (WP3)
   and §7 (first exact obstruction).
2. **No cover-independent (direct-limit) class is constructed.**  Task 3 stops at exact
   refinement naturality, as the task permits.  See §7.

> Is this obstruction `w₂(TM)`?
> **Not proved, and not claimed — this question remains open in Task 3.**  The base space is
> an abstract topological space and the transition data is abstract; there is no manifold, no
> tangent bundle, no metric, no orientation, no time-orientation, no frame bundle and no
> frame transition cocycle anywhere in the project, so the identification cannot even be
> stated here.  The strongest admissible statement is: *the object constructed is an abstract
> ℤ₂-valued Spin-lift obstruction of the correct formal type for a later `w₂` comparison.*

---

## 1. WP1 — audit of the pre-existing generic E2 machinery

Inspected: `RequestProject/Spine/E2/CentralDoubleCover.lean`,
`RequestProject/Spine/E2/Lift/*.lean`, `Descent/*`, `Defect/*`, `Global/*`, `AtlasChange/*`,
`RequestProject/Spine/E2/SpinProjection.lean`.

| required ingredient | pre-existing? | verdict | used as |
|---|---|---|---|
| central projection interface with local sections | `NullSectorTask28.InternalProjection` | already generic and reusable | parameter of the whole Task-3 layer |
| local internal representatives | `InternalProjection.IsInternalRepOn` | already generic | `SpinLiftFamily.isRep` |
| kernel-valued differences of two lifts | `relFactor`, `relFactor_isKerFunOn` | already generic | `liftRatio` (WP6) |
| continuous kernel-valued functions, local constancy from a discrete kernel | `IsKerFunOn`, `toKerFun`, `isLocallyConstant_toKerFun` | already generic | WP4 continuity/local constancy |
| triple-overlap defect + kernel-valuedness | `tripleDefect`, `tripleDefect_mem_ker`, `tripleDefect_isKerFunOn` | already generic (opposite index convention) | `SpinLiftFamily.defect` is *defined* as `tripleDefect` with permuted arguments — **not duplicated** |
| quadruple-overlap consistency | `quadruple_defect_consistency` | already generic | the WP5 2-cocycle law is derived from it, not re-proved |
| change of representatives | `triple_defect_change_of_rep`, `central_rearrange` | already generic | WP6 coboundary law |
| exact compatibility ⇔ trivial defect | `exact_internal_transition_compatibility_iff_defect_trivial` | already generic | `isCoherent_iff_defect_one` |
| an **open cover of an abstract base as a standalone object** | only inside `NullSectorTask27.OrdinaryTransitionSystem`, bundled with transitions and a fixed model group | only partially present | new `CechCover` (needed to state refinement `𝓥 → 𝓤`) |
| indexed *family* of transition maps with the exact Čech 1-cocycle law over an abstract base | partially (Task-27 system, tied to the frame-family model group) | only partially present | new `VisibleCocycle` |
| an **indexed family of lifts** and its defect **as a 2-cochain** | missing | missing | new `SpinLiftFamily`, `defect` |
| Čech 2-cocycle law in `ijkl` indexing | missing (only the unindexed consistency identity) | missing | new `defect_cocycle₂`, `defect_delta_eq_one` |
| coboundary operator `δ` on kernel-valued 1-cochains | missing | missing | new `delta₁`, `delta₁_mul`, `delta₁_inv` |
| cohomologous relation / quotient class | missing (and deliberately avoided upstream: "no cohomological reading is introduced") | missing | new `Cohomologous`, `ObstructionClass` |
| vanishing ⇔ coherent transition data | missing at cover level | missing | new `obstruction_eq_trivialClass_iff_exists_coherent` |
| refinement of covers with pullback of all four levels | partially (`Descent/RefinementBehavior`, pairwise only) | only partially present | new `CoverRefinement`, `pullback`, `pullLift`, `restrictClass` |
| Task-23 / Experiment1 / Experiment2 material | present historically | **forbidden**, and mechanically excluded | not used (firewall) |

### Dependency DAG (Task 3)

```
Mathlib
  └── Spine.E2.CentralDoubleCover            (InternalProjection interface)
        └── Spine.E2.Lift.LocalInternalRepresentatives
              └── Spine.E2.Lift.KernelAmbiguity
                    └── Spine.E2.Lift.TripleOverlapDefect
                          └── Spine.E2.Lift.RepresentativeChange
                                └── Spine.E2.Cech.Cover        (WP2, WP9-pullback)
                                      └── Spine.E2.Cech.LocalLifts    (WP3)
                                            └── Spine.E2.Cech.Defect  (WP4, WP5)
                                                  └── Spine.E2.Cech.Coboundary   (WP6)
                                                        └── Spine.E2.Cech.Obstruction (WP7, WP8)
                                                              └── Spine.E2.Cech.Refinement (WP9)
                                                                    └── Spine.E2.Cech.SpinInstance (WP10)
                                                                          └── Spine.E2.Cech.Core
Spine.E1.* (intrinsic Clifford/Spin core)
  └── Spine.E1.Topology.LocalSection
        └── Spine.E2.SpinProjection  (SpinCore.internalSpinProjection)
              └── Spine.E2.Cech.SpinInstance
```

Everything from `Cech.Cover` through `Cech.Refinement` is proved for an arbitrary
`InternalProjection`; the concrete Spin projection enters only in `Cech.SpinInstance`.  This
is checked mechanically: the firewall asserts that `Spine.E2.Cech.Refinement` does **not**
import `Spine.E2.SpinProjection`, and that `Spine.E2.Cech.SpinInstance` does.

---

## 2. WP2 — cover and visible transition representation

* `CechSpinLift.CechCover X ι`: `U : ι → Set X`, openness, covering.  Overlaps
  `overlap₂ i j`, `overlap₃ i j k`, `overlap₄ i j k l`, with all inclusion lemmas.
* `CechSpinLift.VisibleCocycle G 𝓤`: `g : ι → ι → (X → G)`, `ContinuousOn (g i j)` on
  `overlap₂ i j`, and the **only** assumed law `g i j x * g j k x = g i k x` on `overlap₃`.
* Derived, not assumed: `g_self` (`g i i = 1` on `U i`), `g_symm`
  (`g j i = (g i j)⁻¹` on `overlap₂`).  Packaged as `visible_transition_laws`.
* No manifold, tangent bundle or frame bundle occurs; `X` carries only a topology.

## 3. WP9 representation of refinement (stated here because `Cover.lean` defines it)

`CoverRefinement 𝓥 𝓤` = an index map `r : ι' → ι` with `𝓥.U a ⊆ 𝓤.U (r a)`; the induced
inclusions on 2-, 3- and 4-fold overlaps are proved, and `R.pullback T` is the pulled-back
visible cocycle (continuity and the cocycle law inherited).

## 4. WP3 — local Spin lifts, honestly

Proved:

* `isInternalRepOn_of_mapsTo_section` — if `g` is continuous on `V` and `g '' V ⊆ W` where
  `W` carries a continuous section `s` of `ρ`, then `s ∘ g` is a continuous lift on `V`.
* `exists_lift_nhdsWithin` — **unconditional**: every point of `V` has a relative
  neighbourhood carrying a continuous lift.  This is what the inherited local-section
  property gives, and no more.
* `IsLiftAdmissible P T` — the hypothesis "every `g_ij` has a lift on the whole `U_ij`",
  equivalent to `Nonempty (SpinLiftFamily P T)`.
* `isLiftAdmissible_of_sectionDomains` — sufficient criterion (ADDITIONAL_ASSUMPTION).
* `isLiftAdmissible_of_const` — transition data constant on each overlap is always liftable
  (DERIVED_NATIVE; a non-vacuity witness using only surjectivity).
* `CoverRefinement.isLiftAdmissible_of_fine` — the refinement form: a refinement whose
  overlaps are mapped into section domains carries lifts of the pulled-back data.

**Not proved (and not assumed anywhere):** that every cover of every topological base has a
lift-admissible refinement.  See §7.

## 5. WP4–WP8, WP10 — the theorem chain

| step | theorem | consumes |
|---|---|---|
| defect defined | `SpinLiftFamily.defect`, `defect_apply` | inherited `tripleDefect` |
| defining identity | `lift_mul_lift` | `tripleDefect_mul` |
| `ρ(c)=1` | `proj_defect` | visible cocycle law + homomorphism property + `tripleDefect_mem_ker` |
| kernel-valued | `defect_mem_ker` | `mem_Ker_iff` (exact kernel), **not** postulated |
| continuous | `defect_isKerFunOn`, `defect_continuousOn` | continuity of the lifts |
| locally constant | `defect_isLocallyConstant` | **discreteness** of `ker ρ` |
| constant on connected overlaps | `defect_const_of_preconnected` | local constancy |
| 2-cocycle | `defect_cocycle₂` : `c_jkl · c_ijl = c_ijk · c_ikl` | associativity + **centrality** (`quadruple_defect_consistency`) |
| 2-cocycle, alternating | `defect_delta_eq_one` : `c_jkl c_ikl⁻¹ c_ijl c_ijk⁻¹ = 1` | centrality again |
| centrality audit | `defect_cocycle₂_uses_centrality` | states kernel-valuedness and centrality side by side |
| lifts differ by `ε` | `liftRatio_isKerCochain₁`, `lift_eq_liftRatio_mul` | `relFactor` theory |
| coboundary law | `defect_eq_delta₁_mul`, `defect_twist`, `defect_change_of_lift` | `central_rearrange` (**centrality**) |
| `δ` is a homomorphism / inverts | `delta₁_mul`, `delta₁_inv` | **centrality** |
| equivalence relation | `cohomologous_refl/symm/trans`, `cohomologous_equivalence` | `delta₁_mul`, `delta₁_inv` |
| class | `ObstructionClass`, `classOf`, `classOf_eq_iff`, `trivialClass` | `Quot` only |
| invariance | `obstruction_lift_independent` | coboundary law |
| coherence ⇔ trivial defect | `isCoherent_iff_defect_one` | inherited exact-compatibility criterion |
| vanishing ⇔ adjustable | `obstruction_eq_trivialClass_iff_kernel_adjustable` | `defect_twist` |
| **vanishing ⇔ coherent data exists** | `obstruction_eq_trivialClass_iff_exists_coherent` | both of the above |
| refinement | `pullLift`, `defect_pullLift`, `cohomologous_pull`, `restrictClass`, `obstruction_pullLift`, `obstruction_pullLift_eq_trivial`, `isCoherent_pullLift` | inclusion of overlaps |
| restriction is functorial | `restrictClass_id`, `restrictClass_comp` | `Quot.ind` |
| the restricted class does not depend on the refinement **map** | `conjLift`, `defect_conjLift`, `obstruction_pullLift_indep_of_map` | visible cocycle law + **centrality** (conjugating a kernel element by a lift is trivial) |
| **instantiation** | `SpinCore.cech_defect_eq_pm_one`, `SpinCore.cech_defect_kernel_card`, `SpinCore.spinLiftObstruction` | `SpinCore.internalSpinProjection`, `mem_ker_spinCover_iff`, `spinCover_ker_card` |

### Where centrality is genuinely needed

* **Not** needed for: `ρ(c)=1`, kernel-valuedness, continuity, local constancy,
  `isCoherent_iff_defect_one`.  These use only that `ker ρ` is a subgroup with the discrete
  topology.
* **Needed** for: the 2-cocycle law (moving a defect past a lift when re-bracketing
  `g̃_ij g̃_jk g̃_kl`), the coboundary law `c' = (δε) c`, `δ(ε'ε) = δε' · δε`,
  `δ(ε⁻¹) = (δε)⁻¹`, hence for transitivity and symmetry of `Cohomologous` and therefore for
  the very existence of the class.

### Canonicality table

| arrow / object | status |
|---|---|
| `g_ij` (visible transition data) | given data |
| `g_ii = 1`, `g_ji = g_ij⁻¹` | DERIVED_NATIVE from the cocycle law |
| `g_ij ⟶ g̃_ij` (a lift on a whole overlap) | **requires a choice, and requires liftability**: CHOICE_UP_TO_KERNEL + ADDITIONAL_ASSUMPTION (`IsLiftAdmissible`) |
| pointwise-local existence of a lift | DERIVED_NATIVE (unconditional) |
| `g̃ ⟶ c_ijk` | canonical *given the lifts*: DERIVED_NATIVE, no further choice |
| `c_ijk ∈ {±1}` | DERIVED_NATIVE (INHERITED_CANONICAL kernel theorem) |
| continuity / local constancy of `c` | DERIVED_NATIVE (kernel discrete) |
| `δc = 1` | DERIVED_NATIVE (needs central kernel) |
| dependence of `c` on the lifts | CHOICE_UP_TO_KERNEL, exactly `c' = (δε)c` |
| `[c]_𝓤` | DERIVED_NATIVE, **choice-invariant**; COVER_REFINEMENT_DEPENDENT as an object |
| `[c]_𝓤 = 1 ⇔ coherent data` | DERIVED_NATIVE, both directions |
| `[c_𝓥] = r*[c_𝓤]` | REFINEMENT_INVARIANT (naturality proved) |
| independence of the refinement index map `r` | REFINEMENT_INVARIANT (proved: `obstruction_pullLift_indep_of_map`) |
| functoriality `r* ∘ r'*`, `id* = id` | DERIVED_NATIVE |
| cover-independent class `Ȟ²` | BLOCKED / NOT_REQUIRED (explicitly out of scope) |
| existence of a lift-admissible refinement for an arbitrary base | BLOCKED (see §7) |
| identification with `w₂(TM)` | NOT_REQUIRED here, and **open** |

## 6. Non-vacuity control

`RequestProject/Spine/Controls/E2/CechObstructionControl.lean` (a control: no production
module imports it) builds an explicit instance over the one-point base with the one-patch
cover, the unit visible cocycle and the **native** Spin projection, and proves:

* `negLift_defect_ne_one` — a legitimate family of local lifts whose defect equals
  `negOneSpin ≠ 1`: the defect is genuinely choice-dependent, so the theorems above are not
  statements about a constant-`1` object;
* `obstruction_trivial_both` — the class of the same data nevertheless vanishes, and equals
  the class of the coherent family.

This separates the two layers exactly as claimed: `c` depends on the choice, `[c]` does not.

## 7. Negative results — the exact obstructions

**(a) Lift-admissibility on full overlaps.**

* *Missing statement*: for an arbitrary topological base `X`, an arbitrary cover `𝓤` and
  arbitrary continuous transition data, a refinement `𝓥 → 𝓤` such that every
  `g_{r a, r b}` lifts continuously on all of `V_a ∩ V_b`.
* *Why it fails here*: the inherited data gives a section only on a neighbourhood of each
  point of the visible group `G`.  Turning that into a lift on a whole overlap requires the
  overlap to be mapped into one section domain.  Shrinking the patches of `𝓤` so that this
  holds **simultaneously for all index pairs** is a shrinking/paracompactness argument: for a
  patch around `x` one must control `g_{i(x) j}` for indices `j` whose patches meet the new
  patch, including indices with `x ∉ U_j`, where continuity gives no control at `x`.
* *Minimal additional assumptions that suffice* (any one of):
  (i) each overlap is mapped into a section domain — this is exactly
  `isLiftAdmissible_of_sectionDomains` (proved); (ii) a fine refinement in the sense of
  `CoverRefinement.isLiftAdmissible_of_fine` (proved); (iii) a good cover / contractible
  overlaps together with a covering-space lifting criterion (not formalised, and would
  require covering-space theory for `ρ`, which is deliberately not claimed); (iv) a
  paracompact base plus the shrinking lemma.
* *Canonical?*  No: (i)–(iv) are genuine extra hypotheses, and the task forbids assuming a
  good cover silently.  They are therefore classified ADDITIONAL_ASSUMPTION and appear as
  explicit hypotheses, never as background assumptions.
* *Which stage fails*: **local lifting**, not the defect algebra.
* *Does the core algebra survive?*  **Yes.**  Everything from WP4 onwards is stated for a
  given `SpinLiftFamily`; none of it uses how that family was obtained.

**(b) Cover-independent class.**

* *Missing statement*: `[c] ∈ Ȟ²(X; ℤ₂)` as a colimit over refinements, plus the converse of
  `obstruction_pullLift_eq_trivial` (vanishing after refinement ⇒ vanishing before).
* *Why not built*: a direct-limit construction over the refinement preorder plus cofinality
  is a general Čech-cohomology library, which the task explicitly rules out.  Two of the
  ingredients a colimit would need are nevertheless proved here: functoriality of the
  restriction maps (`restrictClass_id`, `restrictClass_comp`) and independence of the
  restriction from the chosen index map (`obstruction_pullLift_indep_of_map`).  What is
  still missing is the injectivity/cofinality statement, i.e. the converse of
  `obstruction_pullLift_eq_trivial`.
* *Which stage*: **quotient construction / global topology**, not the defect algebra.
* *Does the core survive?*  Yes; exact naturality `[c_𝓥] = r*[c_𝓤]` is proved.

**(c) `w₂`.** Not attempted; the required structures (manifold, `TM`, metric, orientation,
time-orientation, frame bundle, frame cocycle) do not exist in this project.  Deliberate
non-goal.

## 8. Interpretation boundary (mandatory, repeated in the Lean sources)

* Topological layer: `[c] ≠ 1` means precisely that a globally coherent Spin-valued lift of
  the given transition data on the given cover is obstructed.
* Future dynamical layer: even when `[c] = 1`, a connection introduced later may have nonzero
  curvature or torsion, and any later relational/synchronization structure may be nontrivial.
* Therefore `[c] = 1` must **not** be read as flat spacetime, zero curvature, zero
  gravitational field, synchronization equilibrium or absolute rest.
* The defect is **not** curvature, torsion, holonomy, a synchronization imbalance, a field
  strength, a matter/antimatter sign or a preferred frame.  The kernel signs are the two
  elements of `ker ρ = {±1}` and carry no physical reading here.
* `topological ℤ₂ obstruction ≠ dynamical synchronization defect.`
* The uploaded hypothesis paper was used as background context only; no claim of it is used
  as a formal assumption anywhere in the Lean sources.

## 9. Anti-shortcut compliance

1. no `Experiment1/**` or `Experiment2/**` import — mechanically enforced (§10);
2. no historical Task-23 infrastructure used;
3. global lifts on full overlaps never assumed (hypothesis `IsLiftAdmissible`, §4);
4. no good cover assumed; fineness appears only as an explicit, classified hypothesis;
5. the Čech 2-cocycle law is **proved**, not assumed;
6. the class is defined only after the coboundary law and is then proved lift-independent;
7. no identification with `w₂`;
8. kernel signs are never given a matter/antimatter reading;
9. vanishing is never equated with geometric flatness;
10. no physical interpretation is used as a proof premise;
11. no cohomology library is imported: the quotient uses `Quot` only.

## 10. Build evidence

Commands run, all successful:

```
lake build RequestProject.Spine.E1.Core
lake build RequestProject.Spine.E1.Topology.Core
lake build RequestProject.Spine.E2.Core
lake build RequestProject.Spine.Core
lake build RequestProject.Spine.Audit.Firewall
lake build RequestProject.Spine.E2.Cech.Cover
lake build RequestProject.Spine.E2.Cech.LocalLifts
lake build RequestProject.Spine.E2.Cech.Defect
lake build RequestProject.Spine.E2.Cech.Coboundary
lake build RequestProject.Spine.E2.Cech.Obstruction
lake build RequestProject.Spine.E2.Cech.Refinement
lake build RequestProject.Spine.E2.Cech.SpinInstance
lake build RequestProject.Spine.E2.Cech.Core
lake build RequestProject.Spine.Controls.E2.CechObstructionControl
lake build
```

Firewall output (`RequestProject.Spine.Audit.Firewall`), extended in this task with the new
modules:

```
Spine direct legacy imports:    Experiment1 = 0, Experiment2 = 0
Spine transitive legacy imports: Experiment1 = 0, Experiment2 = 0
endpoint RequestProject.Spine.E2.Cech.Core:        E1 = 0, E2 = 0 (direct and transitive)
endpoint RequestProject.Spine.E2.Cech.SpinInstance: E1 = 0, E2 = 0 (direct and transitive)
endpoint RequestProject.Spine.Controls.E2.CechObstructionControl: E1 = 0, E2 = 0
control OK: Spine.E2.Cech.SpinInstance does import Spine.E2.SpinProjection
control OK: Spine.E2.Cech.SpinInstance does import Spine.E2.Cech.Refinement
LAYERING (Cech generic layer): Spine.E2.Cech.Refinement reaches no control, no legacy tree,
  no SL(2,ℂ)/matrix/Pauli module, and not Spine.E2.SpinProjection
SPINE FIREWALL AUDIT: all checks passed
```

## 11. Axiom audit

`#print axioms` is run inside `Spine/E2/Cech/Core.lean` and `Spine/E2/Cech/SpinInstance.lean`
(and for the control).  Every principal Task-3 declaration reports only

```
[propext, Classical.choice, Quot.sound]
```

(`CechSpinLift.CechCover` reports no axioms at all; `VisibleCocycle` reports
`[propext, Quot.sound]`).  No `sorryAx`, no project-local axiom, no `Lean.ofReduceBool`.

## 12. Fail-build ledger (append-only)

| # | command | failing source | diagnostic | cause | repair | statement changed? |
|---|---|---|---|---|---|---|
| 1 | `lake build RequestProject.Spine.E2.Cech.Cover` | `Cover.lean:139` | `Unknown identifier 'mul_right_eq_self'` | lemma name not available in this Mathlib | replaced by explicit `mul_right_cancel` step | no |
| 2 | `lake build RequestProject.Spine.E2.Cech.Defect` | `Defect.lean:146,165` | `Invalid field 'quadruple_defect_consistency' / 'ker_commute'` | `Cech.Cover` imported only `Lift.TripleOverlapDefect`, which is upstream of `Lift.RepresentativeChange` | import bumped to `Lift.RepresentativeChange` | no |
| 3 | `lake build RequestProject.Spine.E2.Cech.Coboundary` | `Coboundary.lean:103` | type mismatch after `simpa` in `delta₁_mul` | centrality was demanded of the wrong factor (`ε` instead of `ε'`) | hypothesis changed to `IsKerCochain₁ P 𝓤 ε'`, `delta₁_inv` adapted | hypothesis of an auxiliary lemma only |
| 4 | `lake build RequestProject.Spine.E2.Cech.Obstruction` | `Obstruction.lean:70,101,137,140` | `rewrite` pattern not found; invalid `▸`; invalid field notation | (a) implicit args of `delta₁_mul` after fix #3; (b) `▸` on an equality of `Prop`s; (c) `P` is not a parameter of the inherited compatibility criterion | (a) explicit `(ε := ) (ε' := )`; (b) `cast`; (c) fully qualified call | no |
| 5 | `lake build RequestProject.Spine.Controls.E2.CechObstructionControl` | control file `:55` | `Function expected at MonoidHom.mem_ker` | `mem_ker` is an `Iff`, not a function | `MonoidHom.mem_ker.1 …` | no |

Linter warnings (unused variables, unused section variables, `simpa`→`simp`) were fixed at
the root — by `omit`ing genuinely unused section variables and renaming unused binders to
`_` — not by disabling linters.  The final build of the Task-3 modules is warning-free.

## 13. Deliverables map

| deliverable | location |
|---|---|
| native Lean implementation | `RequestProject/Spine/E2/Cech/{Cover,LocalLifts,Defect,Coboundary,Obstruction,Refinement,SpinInstance,Core}.lean` |
| this audit | `TASK03_AUDIT.md` |
| dependency DAG | §1 |
| cover/refinement representation | §2, §3 |
| construction of `c_ijk` | `SpinLiftFamily.defect` (§5) |
| kernel-valuedness | `proj_defect`, `defect_mem_ker` |
| continuity / local constancy | `defect_isKerFunOn`, `defect_isLocallyConstant` |
| Čech 2-cocycle law | `defect_cocycle₂`, `defect_delta_eq_one` |
| change-of-lift / coboundary | `defect_eq_delta₁_mul`, `defect_twist`, `defect_change_of_lift` |
| fixed-cover class | `ObstructionClass`, `obstruction`, `obstruction_lift_independent` |
| vanishing ⇔ coherent lift | `obstruction_eq_trivialClass_iff_exists_coherent` |
| refinement naturality | `obstruction_pullLift`, `obstruction_pullLift_indep_of_map`, `restrictClass_id`, `restrictClass_comp` (+ documented gap, §7b) |
| concrete instantiation | `SpinCore.cech_defect_eq_pm_one`, `SpinCore.spinLiftObstruction` |
| canonicality table | §5 |
| fail-build ledger | §12 |
| build evidence | §10 |
| axiom audit | §11 |
