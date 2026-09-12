# TASK 36 — Adversarial result matrix

Every source-derived control case of the Task-36 brief, with its exact status.

**Reading rule.**  A *genuine mathematical FAIL* (the object exists in the formalism and the
property provably fails) is distinguished throughout from *missing library infrastructure*
(the object or the property cannot be expressed at all in the pin).  The two are never
conflated, and a blocked case is never counted as a pass.

Legend for the last column: **PROVED** = theorem in this tree; **BLOCKED** = mathematically
standard but not expressible/provable with Lean 4.28.0 + Mathlib v4.28.0 and the project's
current development; **OUT OF SCOPE** = deliberately not part of this stage of the project.

---

## A. Trivial one-chart control (§6)

| field | value |
| --- | --- |
| object / construction | `Task36.oneChartGluing` — one chart, whole local model, identity identifications |
| smooth manifold? | **YES** — `Task36.oneChartGluing_smoothGluing`, `Task36.oneChartGluing_isManifold` |
| orientable? | **YES** (project-native orientation compatibility, as a *consequence* of the solder) — field 4 of `Task36.oneChart_positive_control` |
| Spin-admissible? | **YES**, trivially: `Task36.oneChartSpin`, with `S.g i j x = 1` |
| Lorentz-admissible? | **YES** in the project's sense: the internal Lorentz bundle is soldered to `TM` |
| regular solder? | **EXISTS** — `Task36.oneChartSolder` |
| number/freedom of Spin structures | no residual freedom on this cover: every kernel 1-cocycle is pointwise trivial (`Task36.kerCocycle_pointwiseTrivial_of_subsingleton`).  **Not** claimed: uniqueness of the Spin structure on the manifold — no classification theorem is proved |
| smooth Spin bundle? | **BLOCKED** (see §§1–2 of `TASK36_AUDIT.md`) |
| connection available? | **OUT OF SCOPE** |
| Dirac operator? | **OUT OF SCOPE** |
| curvature statement? | **NOT YET DEFINED** |
| theorem names | `Task36.oneChart_positive_control`, `Task36.oneChart_no_overlap_obstruction` |
| blocker | — |

## B. One-loop control (§7)

| field | value |
| --- | --- |
| object / construction | `Task36.loopGluing = Task36.loopGluingOf Unit LoopTwist.id'` — two slabs of `ℝ ⊕ ℝ³` glued along two disjoint overlap components, one of them the wrap-around: one noncontractible loop |
| smooth manifold? | **YES** — `Task36.loopGluingOf_smoothGluing`, `Task36.loopGluingOf_isManifold` |
| orientable? | **YES** — tangent transitions are the identity (`Task36.tangentTransitionMap_loop_id`), and the orientation gate applies |
| Spin-admissible? | **YES** — `Task36.twistedSpin σ` for every `σ : Unit → Bool` |
| Lorentz-admissible? | **YES** in the project's sense |
| regular solder? | **EXISTS** — `Task36.loopRegularSolder`, `Task36.nonempty_solder_loopGluing`; and for every twisted seed, `Task36.loop_spin_lift_has_solder` |
| number/freedom of Spin structures | **2 gauge-inequivalent native Spin data over the same projected Lorentz transition system**, differing by the kernel sign around the loop — `Task36.one_loop_has_kernel_sign_freedom`.  These are inequivalent *lift classes at the implemented equivalence relation* (`SpinNative.GaugeEquiv`); **no physical distinction is claimed** |
| smooth Spin bundle? | **BLOCKED** |
| connection available? | **OUT OF SCOPE** |
| Dirac operator? | **OUT OF SCOPE** |
| curvature statement? | **NOT YET DEFINED** — the tangent transitions being the identity is *not* a flatness statement about a connection |
| theorem names | `Task36.one_loop_has_kernel_sign_freedom`, `Task36.loop_spin_lift_has_solder`, `Task36.loop_spin_lifts_inequivalent` |
| blocker | — |

## C. `N` independent loops — fixed-cover `H¹`-like multiplicity (§8)

| field | value |
| --- | --- |
| object / construction | `Task36.loopGluingOf κ LoopTwist.id'` for an arbitrary index type `κ`; instantiated at `κ = Fin 2` |
| smooth manifold? | **YES** |
| orientable? | **YES** |
| Spin-admissible? | **YES** — the family `Task36.twistedSpin σ`, `σ : κ → Bool` |
| Lorentz-admissible? | **YES** in the project's sense |
| regular solder? | **EXISTS** for every member of the family |
| number/freedom of Spin structures | `σ ↦ twistedSpin σ` is injective on gauge classes: `2^N` classes for `N` loops; `N = 2` instantiated with `2² = 4` |
| smooth Spin bundle? | **BLOCKED** |
| connection / Dirac / curvature | **OUT OF SCOPE** / **OUT OF SCOPE** / **NOT YET DEFINED** |
| theorem names | `Task36.fixed_cover_spin_choice_family`, `Task36.two_loop_spin_choice_family` |
| blocker for the *torus* reading | **THIS IS THE PROJECT'S FIXED-COVER `H¹`-LIKE CONTROL, NOT YET A THEOREM IDENTIFYING IT WITH GLOBAL `H¹(T^N; ℤ₂)`.**  The base is a disjoint family of loop models, not a literal `T^N`; missing are a smooth-quotient construction of `T^N` and the comparison of the project's fixed-cover Čech classes with singular `H¹` |

## D. Orientation-reversing / Möbius-type control (§9)

| field | value |
| --- | --- |
| object / construction | `Task36.moebiusGluing = Task36.loopGluingOf Unit LoopTwist.flip` — the wrap-around identification is an explicit linear map of determinant `-1` (`Task36.det_flipEquiv`) |
| smooth manifold? | **YES** — `Task36.moebiusGluing_smoothGluing`, `Task36.loopGluingOf_isManifold` |
| orientable? | **NO** (project-native sense): the determinant 1-cocycle of the tangent transitions is not a continuous nowhere-vanishing coboundary |
| Spin-admissible? | **YES** as *transition data*: native Spin transition data exist (e.g. the trivial cocycle) |
| Lorentz-admissible? | **NO** in the project's sense |
| regular solder? | **IMPOSSIBLE** — `Task36.orientation_reversing_gluing_no_solder`, for **every** native Spin datum |
| number/freedom of Spin structures | not applicable: the failure precedes any lift discussion |
| smooth Spin bundle? | not applicable |
| connection / Dirac / curvature | **OUT OF SCOPE** / **OUT OF SCOPE** / **NOT YET DEFINED** |
| theorem names | `Task36.orientation_reversing_gluing_no_solder`, `Task36.spin_does_not_imply_lorentz_moebius` |
| gate | the **ORIENTATION** gate, before any lifting discussion.  The proof uses only the determinant law and connectedness of a chart domain; no triple overlap, no lift family, no kernel cocycle.  **This obstruction is not described as `w₂`.** |

## E. Independent Spin-lifting / triple-overlap control (§10)

| field | value |
| --- | --- |
| object / construction | any visible Lorentz transition system `T` on the emergent cover with a lift family `D` whose project-native Čech obstruction class is nontrivial |
| smooth manifold? | **YES** (the base gluing is arbitrary and smooth) |
| orientable? | irrelevant: the statement is independent of the orientation gate |
| Spin-admissible? | **NO** — `Task36.spin_obstruction_nonzero_implies_no_native_lift`: no native Spin transition datum projects to `T` |
| Lorentz-admissible? | **NO** in the project's sense |
| regular solder? | **IMPOSSIBLE** — `Task36.spin_obstruction_nonzero_implies_no_solder` |
| smooth Spin bundle? | not applicable |
| connection / Dirac / curvature | **OUT OF SCOPE** / **OUT OF SCOPE** / **NOT YET DEFINED** |
| theorem names | `Task36.smooth_solder_implies_spin_obstruction_trivial`, `Task36.spin_obstruction_nonzero_implies_no_native_lift`, `Task36.spin_obstruction_nonzero_implies_no_solder` |
| blocker | the class used is the **project-native** `CechSpinLift.SpinLiftFamily.obstruction`.  Its identification with `w₂(TM)` is **NOT FORMALIZED**; see `TASK36_AUDIT.md` §11 for the exact missing comparison theorem |

## F. `S⁴` — Spin but no Lorentz metric (§12)

| field | value |
| --- | --- |
| object / construction | the 4-sphere |
| smooth manifold? | **NOT FORMALIZED** in this project (Mathlib has `Metric.sphere`, but not the smooth-manifold + tangent-bundle development needed here) |
| orientable? | **UNKNOWN** in the formal sense: no orientation predicate for manifolds is available |
| Spin-admissible? | **UNKNOWN** formally (true mathematically) |
| Lorentz-admissible? | **UNKNOWN** formally (false mathematically, because `χ(S⁴) = 2 ≠ 0`) |
| regular solder? | **NOT FORMALIZED** |
| number/freedom of Spin structures | **NOT FORMALIZED** |
| smooth Spin bundle? | **NOT FORMALIZED** |
| connection / Dirac / curvature | **OUT OF SCOPE** |
| theorem names | conditional substitutes only: `Task36.spin_does_not_imply_lorentz_conditional`, `Task36.spin_does_not_imply_lorentz_moebius` |
| exact blocker | pinned Mathlib has **no** Euler characteristic of a manifold, **no** Poincaré–Hopf / nowhere-zero-vector-field criterion, **no** Lorentzian metrics, **no** manifold Spin structures and **no** Stiefel–Whitney classes.  §12 forbids reimplementing that library here. **BLOCKED BY INFRASTRUCTURE — NOT counted as a theorem-level pass.** |
| note | the concrete separation that *is* proved (row D, last line) fails at the **orientation** gate, not at the Euler-characteristic gate; it is a different theorem and is reported as such |

## G. `E8`-type topological 4-manifold (§13)

| field | value |
| --- | --- |
| object / construction | Freedman's closed simply connected topological 4-manifold with intersection form `E8` |
| smooth manifold? | **NO** (mathematically, by Rokhlin) — **NOT FORMALIZED** |
| orientable? | **UNKNOWN** formally |
| Spin-admissible? | **CATEGORY-DIFFERENT**: "Spin" here means the even unimodular intersection form in the *topological* category, not a `Spin` structure on a smooth `TM` |
| Lorentz-admissible? | **UNKNOWN** formally |
| regular solder? | **NOT FORMALIZED** (there is no smooth structure for a solder to exist on) |
| number/freedom of Spin structures | **NOT FORMALIZED** |
| smooth Spin bundle? | **NO** mathematically — **NOT FORMALIZED** |
| connection / Dirac operator | **NO** mathematically (no smooth structure) — **NOT FORMALIZED** |
| curvature statement | **NOT YET DEFINED** |
| theorem names | none |
| exact blocker | **EXTERNAL ROBUSTNESS CASE — NOT FORMALIZED.**  Requires Freedman's classification of simply connected topological 4-manifolds, Rokhlin's theorem, Casson's non-triangulability result and a topological-category notion of Spin structure; none is in the pin or in this project.  No easier object was substituted |
| lesson preserved | Spin/topological lift data alone must not imply smooth geometry, a connection or a Dirac operator — enforced here by the curvature claim firewall (§15) and by the absence of any connection/Dirac construction in the tree |

## H. Spin-foam-type combinatorial data (§14)

| field | value |
| --- | --- |
| object / construction | `Task36.SpinFoamLabels V` — vertices, a symmetric adjacency relation, a `SpinGroup`-valued label on each ordered pair.  No topology, no cover, no local model, no continuity, no cocycle law |
| smooth manifold? | **NO** — the type carries no manifold data at all |
| orientable? | not applicable (category-different) |
| Spin-admissible? | **CATEGORY-DIFFERENT**: the object carries spin *labels*, which is not a Spin structure on the tangent bundle of a manifold |
| Lorentz-admissible? | not applicable |
| regular solder? | **NOT FORMALIZED** — and proved *not determined* by the labels: `Task36.spin_foam_labels_do_not_determine_solder` exhibits, independently of any spin foam, both a smooth emergent four-manifold with a regular solder and one with none |
| number/freedom of Spin structures | not applicable |
| smooth Spin bundle / connection / Dirac / curvature | not applicable / **OUT OF SCOPE** / **OUT OF SCOPE** / **NOT YET DEFINED** |
| theorem names | `Task36.spinFoamLabels_unconstrained`, `Task36.spin_foam_labels_do_not_determine_solder` |
| explicitly not claimed | that no object called a spin foam can ever underlie or encode a manifold.  Only the §14 robustness target is proved |

## I. Flat-topology control (§15)

| field | value |
| --- | --- |
| object / construction | `Task36.loopGluing`: noncontractible global topology, identity tangent transitions, regular solder |
| smooth manifold? | **YES** |
| orientable? | **YES** |
| Spin-admissible? | **YES** |
| Lorentz-admissible? | **YES** in the project's sense |
| regular solder? | **EXISTS** |
| curvature statement? | **NOT YET DEFINED.**  The project has no connection or curvature structure at this stage, so no zero-curvature theorem is added and none is faked.  A mechanical **claim firewall** (`Spine/Task36/Firewall.lean`, check 4) scans all 6119 Spine declarations and fails the build if any object named `curvature`/`Riemann`/`holonomy`/`connection` is declared |
| theorem names | `Task36.tangentTransitionMap_loop_id`, `Task36.nonempty_solder_loopGluing`; firewall in `Spine/Task36/Firewall.lean` |
| exact blocker | no connection/curvature stage exists yet; curvature is explicitly deferred |

## J. Globally hyperbolic / product `ℝ × Σ` positive class (§16)

| field | value |
| --- | --- |
| object / construction | `ℝ × Σ` for `Σ` a closed oriented 3-manifold |
| smooth manifold? | **NOT FORMALIZED** |
| orientable? | **UNKNOWN** formally |
| Spin-admissible? | **UNKNOWN** formally (true mathematically: closed oriented 3-manifolds are parallelizable) |
| Lorentz-admissible? | **UNKNOWN** formally |
| regular solder? | **NOT FORMALIZED** |
| number/freedom of Spin structures | **NOT FORMALIZED** |
| smooth Spin bundle / connection / Dirac / curvature | **NOT FORMALIZED** / **OUT OF SCOPE** / **OUT OF SCOPE** / **NOT YET DEFINED** |
| theorem names | none |
| exact blocker | **EXTERNAL ROBUSTNESS CASE — NOT FORMALIZED.**  Missing: a parallelizability predicate for manifolds, the Stiefel theorem for oriented 3-manifolds, Stiefel–Whitney classes and their product behaviour, Lorentzian metrics, global hyperbolicity and Cauchy surfaces.  The recollection in the source discussion was audited (it is mathematically correct) but could not be used |
| explicitly not inferred | global hyperbolicity from a product topology; a Lorentz metric from Spin |

---

## Summary

| case | outcome |
| --- | --- |
| A one-chart | **PASS** (positive control) |
| B one loop | **PASS** (positive control + expected `ℤ/2` freedom) |
| C `N` loops | **PASS** at the fixed-cover level; torus/`H¹` identification blocked |
| D orientation-reversing | **PASS** (rejected at the orientation gate) |
| E Spin-lifting obstruction | **PASS** (rejected at the triple-overlap gate) |
| F `S⁴` | **BLOCKED BY INFRASTRUCTURE** — conditional substitute proved |
| G `E8` | **EXTERNAL ROBUSTNESS CASE — NOT FORMALIZED** |
| H spin foam | **PASS** at the robustness-target level |
| I flat topology | **PASS** as a claim firewall; curvature deferred |
| J `ℝ × Σ` | **EXTERNAL ROBUSTNESS CASE — NOT FORMALIZED** |

No case produced a FAIL-STRUCTURAL or FAIL-CANONICITY outcome.  Overall stop condition:
**PASS-B — PROJECT-NATIVE RECONVERGENCE** (see `TASK36_AUDIT.md` §25).
