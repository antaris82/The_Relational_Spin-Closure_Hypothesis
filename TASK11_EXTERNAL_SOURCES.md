# TASK 11 — external source ledger (upstream delta audit)

Scope of the permitted search (WP4–WP11): current upstream Mathlib; upstream Git history, merged
PRs and open issues; and serious external Lean formalizations of
`H_*^simp(K) ≅ H_*^sing(|K|)`, acyclic carriers, acyclic models, geometric-realization homology,
simplicial approximation, barycentric subdivision, compact support in realizations, and
finite-subcomplex containment.

**Nothing was imported.**  `lakefile.toml` still declares exactly one dependency, `mathlib` at
tag `v4.28.0`, and `lake-manifest.json` still resolves it to
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.  The mechanical firewall
(`RequestProject/Spine/Audit/Firewall.lean`) reports `Spine external-project imports: 0` on the
full build.  No proof block, no definition and no file from any source below was copied into
the project.

Access date for every entry: **2026-09-09**.

---

## 1. Production dependency (the pin), inspected as the baseline

| field | value |
| --- | --- |
| author/owner | the mathlib community |
| repository | `leanprover-community/mathlib4` |
| exact commit | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`, 2026-02-16) |
| licence | Apache 2.0 |
| Lean version | `leanprover/lean4:v4.28.0` |
| files re-inspected in Task 11 | `Mathlib/AlgebraicTopology/SingularSet.lean`; `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`; `Mathlib/AlgebraicTopology/SimplicialSet/**`; `Mathlib/AlgebraicTopology/DoldKan/**`; `Mathlib/Algebra/Homology/QuasiIso.lean` |
| declarations used in Task 11 | `AlgebraicTopology.SSet.singularChainComplexFunctor`, `AlgebraicTopology.singularChainComplexFunctor`, `sSetTopAdj`, `SSet.toTop`, `TopCat.toSSet`, `QuasiIso` (all in `RequestProject/Spine/Nerve/Task11Probe.lean`) |
| declarations confirmed **absent** | `SSet.homology`, `SSet.homologyMap`, `SSetPair`, `TopPair`, `TopPair.HomologyPretheory`, `SSet.sd`, `SSet.normalizedChainComplex`, `SSet.Homotopy`, `SimplicialObject.Homotopy`, `TopCat.Homotopy.singularChainComplexFunctorObjMap` |
| influence category | `MATHLIB_API_REFERENCE` (for what the probe uses); `NEGATIVE_CONTROL` (for the confirmed-absent list) |

`SingularSet.lean` lines 34–37 of the pin record, in the pinned tree itself, the open TODOs
"Show that the singular simplicial set is a Kan complex" and "Show the adjunction `sSetTopAdj`
is a Quillen equivalence".

---

## 2. Current upstream Mathlib — external research source, **not** a dependency

| field | value |
| --- | --- |
| author/owner | the mathlib community |
| repository | `https://github.com/leanprover-community/mathlib4`, branch `master` |
| exact commit inspected | `076c9da2981330e0d1ba84a10afa6544faafa612` (2026-09-09T03:44:13Z) |
| licence | Apache 2.0 |
| Lean version required | `leanprover/lean4:v4.34.0-rc2` |
| Mathlib version | post-`v4.33`, 6002 commits after the pin |
| files inspected | `AlgebraicTopology/SingularSet.lean`; `AlgebraicTopology/SimplicialSet/TopAdj.lean`; `AlgebraicTopology/SimplicialSet/Homology/{Basic,HomologyZero,HomotopyInvariance,MapHomologicalComplex,Nondegenerate,Relative}.lean`; `AlgebraicTopology/SimplicialSet/{SSetPair,Subdivision,Skeleton,Subcomplex,CategoryWithFibrations,KanComplex}.lean`; `AlgebraicTopology/SimplicialSet/AnodyneExtensions/**`; `AlgebraicTopology/SingularHomology/{Basic,HomologyZero,HomotopyInvariance}.lean`; `AlgebraicTopology/EilenbergSteenrod.lean`; `AlgebraicTopology/{AlternatingFaceMapComplex,MooreComplex,ExtraDegeneracy}.lean`; `AlgebraicTopology/DoldKan/**`; `AlgebraicTopology/SimplicialObject/{ChainHomotopy,Homotopy}.lean`; `Topology/Category/TopPair.lean`; `Topology/Homotopy/TopCat/{ToSSet,ZerothHomotopy}.lean` |
| theorems inspected | `SSet.homology(Map)`, `SSet.Homotopy.congr_homologyMap`, `TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor`, `SSet.homology₀Iso`, `TopCat.singularHomology₀Iso`, `SSet.isZero_homology_of_hasDimensionLT`, `QuasiIso (X.toNormalizedChainComplex R)`, `SSetPair.homology_exact₁/₂/₃`, `SSetPair.homologyδ`, `TopPair.HomologyPretheory.IsHomotopyInvariant`, `SSet.sdExAdjunction`, `sSetTopAdj_unit_app_app_down` |
| is its proof architecture reusable? | partly, as a **design** reference for how one would organise a simplicial/relative homology layer; not reusable as code (new Lean module system, `Category*`, `cat_disch`, `lia`, `dsimp%`, `set_option backward.*` — none of which exists at `v4.28.0`) |
| influence category | `NEGATIVE_CONTROL` for the comparison theorem (it does not exist there); `DESIGN_REFERENCE` for the naming/shape of the canonical map; `BACKGROUND_ONLY` for the rest |
| how inspected | blobless `git clone`, `git checkout 076c9da…`, `git diff --stat` against the pin, `rg`, plus a scratch `lake exe cache get` checkout used only for the WP14 class-B compile probes (outside the Lake project) |

---

## 3. `joelriou/excision` — out-of-tree excision development

| field | value |
| --- | --- |
| author/owner | Joël Riou |
| repository | `https://github.com/joelriou/excision` |
| exact commit | `7d6441e263568075b0228ca503b6976b4269906f` (2026-09-06T21:36:47+02:00, message "wip") |
| licence | Apache 2.0 (per file headers; no top-level `LICENSE` file at that commit) |
| Lean version | `leanprover/lean4:v4.34.0-rc2` |
| Mathlib version | fork `joelriou/mathlib4` @ `810b3888d0aa94294b18587c453466bc86c1f0fc` |
| exact files inspected | `Excision/Excision.lean`; `Excision/SmallSimplices.lean`; `Excision/SimplicialSet/{Devissage,RelativeHomology,Homology,ChainComplexAb}.lean`; `Excision/SingularHomology/{Basic,NatTrans,Subdivision,ULift}.lean`; `Excision/ConvexSpace/{Top,ToSSet,AffineChains,StdSimplex,Diameter}.lean`; `Excision/Topology/LebesgueNumber.lean`; `Excision/HomotopyCategory/HomotopyEquivalences.lean` |
| theorems inspected | `TopPair.toSSetPair`, `TopPair.homotopyEquivalences_of_excision`, `ExcisionCondition.topPairHom`, `SmallSimplicesCondition`, `SSetPair` dévissage (`homotopyEquivalences_chainComplexMap_homOfSubcomplexes`, `homotopyEquivalence_chainComplexMap_iff_of_mono`), barycentric subdivision of singular chains, Lebesgue-number lemma |
| `sorry`-free? | yes (no occurrence of `sorry` in the tree at that commit) |
| does it contain the comparison we need? | **no** — the string `SSet.toTop` does not occur anywhere in it; geometric realization plays no role |
| is its proof architecture reusable? | its *decomposition* is instructive for a future excision/Mayer–Vietoris layer (small simplices ⟹ subdivision ⟹ dévissage ⟹ excision), but it is written against a post-`v4.34` Mathlib fork and cannot be transplanted to the pin |
| influence category | `THEOREM_DECOMPOSITION_REFERENCE` (and `NEGATIVE_CONTROL` for the comparison question) |

Related open Mathlib PRs from the same development: #43524, #43528 (explicitly "From
https://github.com/joelriou/excision"), and #41318, whose text states that it is paused "until
I upstream the excision theorem for topological spaces".

---

## 4. `Shamrock-Frost/BrouwerFixedPoint` — Lean 3 singular homology and acyclic models

| field | value |
| --- | --- |
| author/owner | Brendan Seamus Murphy (`Shamrock-Frost`) |
| repository | `https://github.com/Shamrock-Frost/BrouwerFixedPoint` |
| exact commit | `2883ceb0f5d461155fa1689266a7af40ff8ae671` (2026-01-22) |
| licence | **none declared** (no `LICENSE` file, GitHub reports no licence) — therefore *no* code may be copied; consulted for mathematical decomposition only |
| Lean version | `leanprover-community/lean:3.51.1` |
| Mathlib version | mathlib3 @ `13361559d66b84f80b6d5a1c4a26aa5054766725` |
| exact files inspected | `src/acyclic_models_theorem.lean` (505 lines); file list of `src/` (`barycentric_subdivision.lean`, `homotopy_invariance.lean`, `homology_of_spheres.lean`, `reduced_homology.lean`, `singular_homology_definitions.lean`, `simplices.lean`, `LTE_port/**`) |
| theorems inspected | `functor_basis`, `functor_basis.get_basis`, `functor_basis.map_out`, `complex_functor_basis`, `acyclic`, `lift_nat_trans`, `lift_nat_trans_spec`, `lift_nat_trans_unique`, `lifts_of_nat_trans_H0_give_same_map_in_homology` |
| does it contain the comparison we need? | **no** — it formalizes singular homology, homotopy invariance, subdivision, excision-adjacent machinery and Brouwer; it does not formalize `H_*^simp(K) ≅ H_*^sing(\|K\|)` |
| is its proof architecture reusable? | the *architecture* is exactly the one Task 12 would need for step T12.5 (free functor on models + acyclicity ⟹ lifts unique up to natural chain homotopy); the code is Lean 3, mathlib3, and unlicensed, so only the decomposition may be reused |
| influence category | `DESIGN_REFERENCE` + `THEOREM_DECOMPOSITION_REFERENCE` |

This repository is the project referred to in the upstream docstring of
`Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean`: *"This result was first
formalized in Lean 3 in 2022 by Brendan Seamus Murphy (with a different proof)."*

---

## 5. Searches that returned nothing usable

| search | result | category |
| --- | --- | --- |
| GitHub repository search: acyclic models in Lean 4 | no serious formalization found | `NOT_USED` |
| GitHub repository search: simplicial homology in Lean | only unrelated or toy repositories (`Raylern/Simplicial-Complexes`, `smorel394/AbstractSimplicialComplex`, TDA lists) | `NOT_USED` |
| upstream PR search: "simplicial approximation" | no algebraic-topology PR | `NOT_USED` |
| upstream PR search: "geometric realization" | 0 open PRs | `NEGATIVE_CONTROL` |
| upstream PR search: "Quillen" | 1 open PR, unrelated (`Over`-category adjoints) | `NEGATIVE_CONTROL` |
| upstream tree search: `excision`, `acyclic model`, `nerve theorem`, Mayer–Vietoris for singular homology | 0 occurrences at `076c9da` | `NEGATIVE_CONTROL` |

---

## 6. Statement of independence

Task 11 added five Lean declarations, all in `RequestProject/Spine/Nerve/Task11Probe.lean`
(`SpineTask11.unitChainComplexMap`, `unitChainComplexMap_target`,
`unitChainComplexMap_naturality`, `UnitQuasiIsoStatement`,
`taskNine_and_mathlib_share_the_unit`).  Each is a two-to-five-line statement written directly
against the **pinned** Mathlib API; none reproduces, ports or paraphrases a proof from any
source in this ledger.  The axiom audit of all five is
`[propext, Classical.choice, Quot.sound]`.
