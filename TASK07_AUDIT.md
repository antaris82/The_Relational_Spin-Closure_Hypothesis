# TASK 07 — Good-cover qualification and the Čech-to-singular (H²) comparison

**Status summary.**  The *cover-side* half of Task 7 closes natively and unconditionally.  The
*comparison* half does **not** close in the pinned library, and this audit names the exact
missing theorems instead of assuming them.

| Work package | Result | Classification |
| --- | --- | --- |
| WP1 infrastructure audit | done, §1 | — |
| WP2 Task-4 manifold hypotheses | done, §2; SLC + arbitrarily fine contractible open covers **proved** | DERIVED_NATIVE |
| WP3 good-cover notion + constancy | `IsGoodCover`, implication chain, **good ⇒ Task-6 ConstOn automatic** | GOOD_COVER, DERIVED_NATIVE |
| WP3(b) acyclic covers | `IsAcyclicCover` defined separately; `good ⇒ acyclic` only conditionally | DERIVED_NATIVE (conditional edge) |
| WP4 existence of good covers | **Outcome C**: not proved, parametrised under `IsGoodCover`; contractible-member covers proved to exist | BLOCKED (existence) / DERIVED_NATIVE (weaker cover) |
| WP5 nerve identification | Čech complex **is** the simplicial complex of the nerve (identity) | NERVE_IDENTIFICATION, DERIVED_NATIVE |
| WP6 nerve theorem | absent from Mathlib; stated as hypothesis `NerveRealization` | NERVE_THEOREM_BLOCKED |
| WP7 no artificial cochain map | respected: no invented `Č² → C²_sing` map exists in the project | — |
| WP8 simplicial vs singular | absent; hypothesis `SimplicialSingularComparison` | BLOCKED |
| WP9 homotopy invariance | absent; hypothesis `HomotopyInvariance`; the point computation is **proved** | BLOCKED (partial native result) |
| WP10 `Φ_𝓤` | constructed *from* WP6+WP8+WP9, as a linear isomorphism | COHOMOLOGY_ISOMORPHISM (conditional) |
| WP11 `spinLiftSingularClass` | defined, lift-independent, vanishing ⇔ Spin structure | REPRESENTATION_BRIDGE (conditional) |
| WP12 cover independence | refinement invariance proved conditionally; common good refinement missing | BLOCKED (named) |
| WP13 old Task-3 carrier | injective on good covers; extra classes are carrier artefacts | DERIVED_NATIVE |
| WP14 `w₂` interface | interface + comparison statement only; `w₂` **not** defined | DEFERRED |

New Lean layer: `RequestProject/Spine/GoodCover/**` (9 modules + endpoint).  Full `lake build`
is green (8184 jobs), the mechanical firewall passes, and there is no `sorry`, `admit`,
project-local `axiom`, `unsafe`, `partial` or `implemented_by` anywhere in the new layer.

---

## 1. WP1 — infrastructure audit (pinned Mathlib + this Spine)

| Item | Status | Where |
| --- | --- | --- |
| charted spaces, models with corners, smooth manifolds | MATHLIB_NATIVE | `Mathlib.Geometry.Manifold.*` |
| tangent spaces / tangent bundle | MATHLIB_NATIVE | used by Task 4 |
| paracompactness, locally finite refinements, shrinking lemmas | MATHLIB_NATIVE (general topology) | `Mathlib.Topology.Compactness.Paracompact`, `ShrinkingLemma` — **not** used here, since Task 4 assumes no paracompactness |
| second countability | MATHLIB_NATIVE as a typeclass; **not** assumed by Task 4 | — |
| local Euclidean structure | MATHLIB_NATIVE via `ChartedSpace` | — |
| convexity ⇒ contractible; contractible balls | MATHLIB_NATIVE | `Convex.contractibleSpace`, `Metric.contractibleSpace_ball` |
| strong local contractibility (`StronglyLocallyContractibleSpace`) | MATHLIB_NATIVE (class + transfer along open embeddings) | `Mathlib.Topology.Homotopy.LocallyContractible` |
| SLC of a normed space / of a charted space | **MISSING in Mathlib** (explicit TODO there); **SPINE_NATIVE** now | `Spine.GoodCover.ManifoldCovers` |
| good covers | MISSING (no definition, no existence) | defined natively: `GoodCoverZ2.IsGoodCover` |
| nerve of a cover (as a combinatorial object) | MATHLIB_PARTIAL (`CategoryTheory.Nerve` is the nerve of a *category*; `AlgebraicTopology.CechNerve` is the Čech nerve of a *morphism*, not of an open cover) | built natively in Task 6, exhibited as a presimplicial set here |
| simplicial sets, geometric realization `SSet.toTop` | MATHLIB_NATIVE | `Mathlib.AlgebraicTopology.SingularSet` |
| singular chain complex / homology functor | MATHLIB_NATIVE (categorical, `AlgebraicTopology.SingularHomology.Basic`) | not used: Task 5 built an explicit `ℤ₂`-cochain theory |
| homotopy equivalence of spaces | MATHLIB_NATIVE | `ContinuousMap.HomotopyEquiv` |
| **homotopy invariance of singular (co)homology** | **MISSING** (no prism operator, no chain homotopy; a search of the pinned tree finds no such statement) | hypothesis `GoodCoverSpec.HomotopyInvariance` |
| **nerve theorem** | **MISSING** | hypothesis `GoodCoverSpec.NerveRealization` |
| **simplicial vs singular cohomology** | **MISSING** | hypothesis `GoodCoverSpec.SimplicialSingularComparison` |
| Mayer–Vietoris, acyclic-cover / Leray theorems | MISSING for this setting | — |
| Task-5 singular `ℤ₂` cohomology, cup products | SPINE_NATIVE | `Spine.Cohomology.**` |
| Task-6 fixed-cover Čech `ℤ₂` cohomology, refinement pullback | SPINE_NATIVE | `Spine.Cech.**` |

---

## 2. WP2 — the Task-4 manifold hypotheses, exactly

Task 4 assumes, and nothing more:

```
  [TopologicalSpace M] [ChartedSpace LorentzCarrier M]   (+ [IsManifold carrierModel ⊤ M])
```

with `LorentzCarrier = ℝ × (Fin 3 → ℝ)` a four-dimensional real normed space.

| Property | Classification | Justification |
| --- | --- | --- |
| Hausdorff | **NEW_EXPLICIT_HYPOTHESIS** if ever needed | a `ChartedSpace` need not be `T2`; Task 7 does not need it and does not add it |
| second countable | NEW_EXPLICIT_HYPOTHESIS if ever needed | not implied; not added |
| paracompact | NEW_EXPLICIT_HYPOTHESIS if ever needed | needs `T2` + second countability (or an assumption); not added |
| locally contractible | **STANDARD_CONSEQUENCE, now proved** | `SpineTop.stronglyLocallyContractibleSpace_of_chartedSpace` |
| arbitrarily fine covers by *contractible open* coordinate neighbourhoods | **STANDARD_CONSEQUENCE, now proved** | `SpineTop.exists_contractible_open_nhds`, `SpineTop.exists_contractible_refinement`, `LorentzFrames.contractibleCover` |
| arbitrarily fine **good** covers | **BLOCKED_IN_PINNED_MATHLIB** | see §4 |

No manifold assumption was silently strengthened: the new theorems are stated for a
`ChartedSpace` over a normed space and are applied to the Task-4 class unchanged.

---

## 3. WP3 — the exact good-cover notion, and the constancy implication

`GoodCoverZ2.IsGoodCover U` (module `GoodCover.lean`): every `U i` open, the family covers, and
**every nonempty finite intersection `U i₀ ∩ ⋯ ∩ U i_k` is contractible**, with the
intersections taken in exactly the nerve form `CechZ2.inter` used by the Task-6 complex.  The
index tuples have length `k + 1`; the empty tuple is excluded on purpose, since its
intersection is the whole space and requiring that to be contractible would be a condition on
`X` rather than on the cover.

Distinctions kept apart, with the implications actually proved:

```
  ContractibleSpace s ⇒ IsPathConnected s ⇒ IsConnected s ⇒ IsPreconnected s
```

(`isPathConnected_of_contractible`, `isConnected_of_contractible`,
`isPreconnected_of_contractible`), and the strictness control
`contractible_ne_preconnected` (the empty set is preconnected and not contractible).  Acyclicity
is a *separate* predicate, §3(b).

**The WP3 endpoint** (`Constancy.lean`):

```
  IsGoodCover 𝓤.U  ⟹  ConstOn₃ 𝓤 D.defect   and   ConstOn₂ 𝓤 e        (GoodCoverZ2.goodCover_constOn)
```

so the Task-6 hypotheses become automatic and the whole Task-6 Spin package is unconditional on
a good cover: `spinLiftCechClassGood`, `spinLiftCechClassGood_lift_independent`,
`spinLiftCechClassGood_eq_zero_iff`, and for the Task-4 frame data
`frameCechClassGood_eq_zero_iff_spinStructure`.

### 3(b) acyclic covers

`GoodCoverZ2.IsAcyclicCover U` (module `AcyclicCover.lean`) asks that finite overlaps be
preconnected and that `Hᵏ⁺¹_sing(overlap;ℤ₂) = 0` for all `k`, in the **native Task-5 theory**,
for the nonempty overlaps (the only ones the nerve sees).  It is satisfiable
(`isAcyclicCover_of_subsingleton`) and it also yields the Task-6 constancy data
(`constOn₃_ofAcyclicCover`, `constOn₂_ofAcyclicCover`).

`good ⇒ acyclic` is **not** proved unconditionally: the missing step is homotopy invariance.
The coefficient half *is* proved — `Mod2Cohomology.cohomology_succ_eq_zero_of_subsingleton`, the
mod-2 cohomology of a point vanishes above degree zero, computed directly from the fact that a
subsingleton space has exactly one singular simplex per degree and the coboundary multiplies its
value by `n + 2` — and the conditional implication
`GoodCoverSpec.isAcyclicCover_of_isGoodCover` shows homotopy invariance is the *only* remaining
input.

---

## 4. WP4 — do suitable covers exist?  (Outcome C)

Proved: every Task-4 manifold admits covers by **contractible open** sets, refining any given
open cover (§2).  This is the strongest cover statement its hypotheses support.

Not proved, and not assumed: that the *intersections* can be made contractible.  The classical
construction is Riemannian — a metric, geodesically convex balls (Whitehead), and the fact that
intersections of geodesically convex sets are geodesically convex.  Pinned Mathlib has **no**
Riemannian metric on a manifold, no exponential map, no injectivity or convexity radius, so
that route is unavailable; nothing else in the library produces good covers.

Consequently Task 7 adopts **Outcome C**: the downstream theory is parametric in
`IsGoodCover 𝓤.U`.  The existence question is *recorded* as the predicate
`SpineTop.HasGoodCover`, left unproved for manifolds, and shown non-vacuous for contractible
spaces (`SpineTop.hasGoodCover_of_contractible`, `hasGoodCover_carrier`).

---

## 5. WP5 — the nerve, explicitly, and the Čech/nerve identification

`NerveZ2.Presimplicial` (module `Presimplicial.lean`) is an abstract presimplicial
(semi-simplicial) set: simplices in each degree, face operators, and the presimplicial identity
`dᵢ ∘ d_{j+1} = dⱼ ∘ dᵢ` for `i ≤ j`.  Its `ℤ₂` cochain complex is built from scratch, including
its own `δ² = 0` (`Presimplicial.coboundary_coboundary`), the agreement with the conventional
alternating formula, and the quotient `Hⁿ_simp(S;ℤ₂)`.

`NerveZ2.coverNerve U` is the nerve of a cover as such an object: a `k`-simplex is a
`(k+1)`-tuple of indices with nonempty overlap, faces delete an index, and the presimplicial
identity is the `Fin.succAbove` commutation already proved in Task 6.

Identification (module `NerveIdentification.lean`), all by `rfl` or a case split:

```
  Cochain, coboundary, cocycles, coboundaries, cohomology  —  identical
  NerveZ2.coverNerve_cohomology :  Hⁿ_simp(N(𝓤);ℤ₂) = Ȟⁿ(𝓤;ℤ₂)
  NerveZ2.cechCohomologyEquiv   :  the identity isomorphism (degree two: cechCohomologyEquiv₂)
```

So WP5 is settled in the strongest form: Task 6 *was* nerve cohomology, and this is now a
theorem rather than a naming convention.  In particular `Ȟ²(𝓤;ℤ₂)` stores one `ℤ₂` per nonempty
overlap and carries no component information — which is exactly why the good-cover hypothesis of
§3 is needed.

---

## 6. WP6 — nerve-theorem audit

Available in pinned Mathlib: geometric realization `SSet.toTop` (left adjoint of
`TopCat.toSSet`), the adjunction, simplicial sets, homotopies and `ContinuousMap.HomotopyEquiv`.

Missing: the nerve theorem itself; the two comparison maps `M → |N(𝓤)|` (partition of unity) and
`|N(𝓤)| → M`; the homotopies exhibiting them as inverse; any acyclic-cover/Leray statement.
There is no partition-of-unity construction against an arbitrary open cover in a form usable
here, and the manifold would need paracompactness for one.

**Classification: NERVE_THEOREM_BLOCKED.**  Recorded as the hypothesis
`GoodCoverSpec.NerveRealization` (a realization plus a homotopy equivalence).  Scope of the
missing work: *major*.

---

## 7. WP7 — no artificial cochain-level comparison

No map `Č²(𝓤;ℤ₂) → C²_sing(X;ℤ₂)` is defined anywhere in this project.  The only comparison is
the composite of §5 (proved), §8 and §9 (hypotheses).  The Task-6 specification
`CechSingularSpec.Comparison` remains in place, untouched, and is still not constructed.

---

## 8. WP8 — simplicial-to-singular comparison audit

Missing entirely in pinned Mathlib for the relevant direction: there is no comparison of the
simplicial cochain complex of a simplicial set with the singular cochain complex of its
realization, and no `ℤ₂`-coefficient version of either.  Building it needs the CW/skeletal
filtration of `|K|` or an acyclic-models argument.

**Classification: BLOCKED**, recorded as `GoodCoverSpec.SimplicialSingularComparison` in degree
two only (as WP8 requests, no more generality than needed).  Scope: *moderate to major*.

---

## 9. WP9 — homotopy invariance of the Task-5 singular cohomology

Searched in pinned Mathlib: there is no homotopy invariance statement for singular homology or
cohomology, no prism operator and no chain homotopy machinery for the singular complex.  The
Task-5 theory has functorial pullback (`Mod2Cohomology.Hmap`, `Hmap_id`, `Hmap_comp`) but
nothing that identifies the pullbacks of homotopic maps.

Proved natively here instead (the coefficient input): **the mod-2 cohomology of a one-point
space vanishes above degree zero** —
`Mod2Cohomology.cohomology_succ_eq_zero_of_subsingleton` — from
`Mod2Cohomology.simplexSubsingleton`/`simplexNonempty` and the explicit coboundary computation
`coboundary_subsingleton`.

**Classification: BLOCKED (partial native result).**  Missing theorem, stated exactly:

> for `f, g : X ⟶ Y` homotopic, `Mod2Cohomology.Hmap f n = Mod2Cohomology.Hmap g n`; hence a
> homotopy equivalence induces an isomorphism `Hⁿ_sing(Y;ℤ₂) ≅ Hⁿ_sing(X;ℤ₂)`.

Source object: singular `ℤ₂` cochain complex of `X`.  Target object: the same for `Y`.
Mathematical theorem needed: the prism/chain-homotopy operator for singular chains.  Available
primitives: `TopCat.toSSet`, `SimplexCategory.toTop`, the face maps, `ContinuousMap.Homotopy`.
Missing infrastructure: the affine subdivision of `Δⁿ × I` and its face identities.  Scope:
*major*.  Recorded as the hypothesis `GoodCoverSpec.HomotopyInvariance`.

---

## 10. WP10 — the assembled comparison `Φ_𝓤`

```
  Φ_𝓤 = (cechCohomologyEquiv₂ 𝓤).symm  ≫  simplicial.compare  ≫  homotopy.transport nerve.equiv
       : Ȟ²(𝓤;ℤ₂)  ≅  H²_sing(X;ℤ₂)                       (GoodCoverSpec.Comparison.equiv)
```

Noncanonical choices, recorded: the realization of the nerve, the nerve-theorem homotopy
equivalence, the simplicial-singular comparison map.  The first factor *is* canonical (it is the
identity).  Therefore the correct classification of `Φ_𝓤` is **dependent on a chosen nerve
equivalence** — not canonical, and not merely existentially available once the data is given.
The word "canonical" is deliberately not used for it anywhere in the Lean sources.

Consequence proved: `Comparison.equiv_eq_zero_iff`, so vanishing transfers in both directions.

---

## 11. WP11 — the transported Spin-lift class

```
  spinLiftSingularClass C h D = Φ_𝓤 [z]        ∈ H²_sing(X;ℤ₂)
```

with `h : IsGoodCover 𝓤.U` and `C` the comparison datum.  Proved:

* `spinLiftSingularClass_lift_independent` — independent of the chosen local Spin lifts;
* `spinLiftSingularClass_eq_zero_iff` — `[z]_sing = 0 ⟺ coherent Spin transition data exist`;
* `frameSingularClass_eq_zero_iff_spinStructure` — for the Task-4 Lorentz frame data,
  `[z]_sing = 0 ⟺ a Spin structure exists`.

All three are theorems *given* `C`; none of them assumes `C` exists.

---

## 12. WP12 — cover and refinement independence

Proved (conditionally on a refinement-compatible comparison family
`GoodCoverSpec.ComparisonFamily`, whose compatibility field is the naturality of the nerve
theorem in refinements): `spinLiftSingularClass_refinement`, i.e. refining a good cover by
another good cover does not change the singular class.  This uses the Task-6 refinement theorem
`Hmap_spinCechClass` and the value-independence `spinCechClass_indep_of_values`.

Missing for *full* independence of the chosen good cover: a **common good refinement** of two
good covers.  Exactly stated as `GoodCoverSpec.CommonGoodRefinement`
(with the packaging structure `GoodRefinementData`), and the conditional conclusion is
`spinLiftSingularClass_common_refinement`.  This missing theorem has the same Riemannian
character as good-cover existence itself (§4); scope: *major*, and strictly downstream of it.

**Cover independence is therefore not asserted.**

---

## 13. WP13 — reassessment of the old Task-3 obstruction carrier

1. *Does every physically relevant Spin-lift defect lie in the image of genuine Čech `H²`?*
   Yes on a good cover: the defect is constant on triple overlaps (§3), hence *is* a Čech
   2-cochain, and its Task-3 class is the image of its Čech class
   (`toObstruction_spinCechClass`).
2. *Are the extra Task-3 representatives artefacts?*  Yes.  The Task-3 carrier admits arbitrary
   group-valued cochains with no cocycle condition; Task 6 already proved the comparison map is
   not surjective, and Task 7 adds that on a good cover it is **injective**
   (`GoodCoverZ2.toObstruction_injective_of_goodCover`).  So the Čech group embeds and the
   surplus carries no Spin-lift information.
3. *Can the old `ObstructionClass` be deprecated for future certification work?*  For
   certification, yes: on good covers the Čech class determines it and is strictly better
   behaved.  It should not be *deleted*.
4. *Retain for provenance?*  Yes — every Task-3 declaration is left untouched, and the
   comparison theorems are what make the deprecation statement meaningful.

---

## 14. WP14 — the `w₂` interface, and the next dependency DAG

`w₂(TM)` is **not** defined, and `w₂(TM) := [z]_sing` is explicitly rejected as circular.
`GoodCoverSpec.W2Interface` fixes what an independent construction must deliver (a degree-two
mod-2 singular class attached to the Lorentz frame data), and
`GoodCoverSpec.AgreesWithSpinObstruction` is the statement a future task must *prove*.  The
payoff is recorded: `GoodCoverSpec.spinStructure_iff_of_agrees` shows that once the agreement is
proved, the Stiefel–Whitney side inherits the Spin criterion.

Route audit:

* **Route A (conventional).**  Real bundles → Thom space / classifying space → Steenrod squares
  → `wᵢ`.  Missing: Steenrod squares, Thom spaces, Thom isomorphism, `BO(n)`, characteristic
  classes.  Scope *major*.
* **Route B (Wu, dimension four).**  `[M]` → Poincaré duality → `v₂` → `w₂ = v₂ + v₁²`.
  Missing: fundamental classes, Poincaré duality, Wu classes, the Wu formula; additionally needs
  compactness/orientability hypotheses Task 4 does not carry.  The cup product it needs *is*
  available natively (Task 5).  Scope *major*.
* **Route C.**  Defining `w₂` as the Spin obstruction is the forbidden circular route; no other
  independent standard construction is shorter in the pinned library.

Next dependency DAG (every edge below is currently missing):

```
 native singular H* (done) ┐
 native cup product (done) ┤
                           ├─► homotopy invariance (WP9) ─┬─► Steenrod squares ─► Thom iso ─► w₂   (A)
                           │                              └─► nerve theorem (WP6) ─► Φ_𝓤
                           └─────────────────────────────────► fundamental class ─► PD ─► v₂ ─► w₂ (B)
```

The first node needed by every branch, and the only one whose inputs already exist natively,
is **homotopy invariance (WP9)**.

---

## 15. Negative-result table (blocked edges, in the required format)

| # | Source object | Target object | Theorem needed | Available primitives | Missing infrastructure | Scope |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | Task-5 `Cⁿ_sing(X;ℤ₂)` | Task-5 `Cⁿ_sing(Y;ℤ₂)` | homotopic maps induce equal maps on `Hⁿ` | `Hmap`, faces, `ContinuousMap.Homotopy` | prism operator, chain homotopies | major |
| 2 | good cover `𝓤` of `M` | `\|N(𝓤)\| ≃ M` | nerve theorem | `SSet.toTop`, adjunction | partition of unity vs a cover, both comparison maps, the homotopies | major |
| 3 | `H²_simp(K;ℤ₂)` | `H²_sing(\|K\|;ℤ₂)` | simplicial = singular | realization, native simplicial complex | skeletal filtration or acyclic models | moderate–major |
| 4 | Task-4 manifold | a good cover of it | existence of good covers | charts, contractible balls, SLC (proved here) | Riemannian metric, geodesic convexity, convexity radius | major |
| 5 | two good covers | a common good refinement | common good refinement | `CoverRefinement`, refinement pullback | same Riemannian input as #4 | major |
| 6 | good cover | acyclic cover | contractible ⇒ acyclic | point computation (proved here) | #1 | major (equals #1) |

---

## 16. Failbuild ledger (every failure of this task, with cause and repair)

| # | Command | Diagnostic | Cause | Repair | Statement change |
| --- | --- | --- | --- | --- | --- |
| 1 | `lake build …GoodCover.Presimplicial` | `NerveZ2.Presimplicial.mk has already been declared` | clash with the structure constructor | renamed the class map to `cohomologyClass` | STATEMENT_UNCHANGED |
| 2 | `lake build …GoodCover.GoodCover` | unused section variable `[TopologicalSpace X]` | `inter_pair'`/`inter_triple'` are purely set-theoretic | `omit [TopologicalSpace X] in` | STATEMENT_UNCHANGED |
| 3 | `lake build …NerveIdentification` | type mismatch in the quotient carriers | `coboundaries` only reduces after a case split on the degree | `cases n <;> rfl`; the equiv defined by cases | STATEMENT_UNCHANGED |
| 4 | `lake build …NerveIdentification` | ill-typed pointwise `apply` lemmas in generic degree | the two carriers are only propositionally equal for symbolic `n` | pointwise lemmas restricted to degree two | STATEMENT_NARROWED (auxiliary lemmas only; the identification itself is degree-generic) |
| 5 | `lake build …ManifoldCovers` | instance not found for `IsOpen.stronglyLocallyContractibleSpace` | that lemma needs the *ambient* space to be SLC — circular | SLC of a chart source obtained from `isOpenEmbedding_restrict` into the model | STATEMENT_UNCHANGED |
| 6 | `lake env lean …ManifoldCovers` | `Unknown identifier E` | the model space appeared only in the proof, so the section variable was not included | model space made an explicit argument | STATEMENT_UNCHANGED |
| 7 | `lake env lean …ManifoldCovers` | `rw` pattern not found (`↑e z`) | membership in a preimage is not syntactically an application | replaced by `show e z ∈ ball …` | STATEMENT_UNCHANGED |
| 8 | (design) `contractibleCover` | spec not recoverable from a `choose`-built definition | tactic-built definition | rebuilt with `Classical.choose` + `contractibleNhd_spec` | STATEMENT_UNCHANGED |
| 9 | `lake build …SingularComparisonSpec` | `elaboration function for subscriptTerm has not been implemented` | the `≃ₕ` notation is not in scope in that file | wrote `ContinuousMap.HomotopyEquiv` explicitly | STATEMENT_UNCHANGED |
| 10 | idem | `rw [h, map_zero]` looped to `0 = 0` | wrong idiom for injectivity of a `LinearEquiv` | `LinearEquiv.map_eq_zero_iff` | STATEMENT_UNCHANGED |
| 11 | idem | acyclicity unprovable for *empty* overlaps | emptiness of the simplex type was not available | acyclicity restricted to nonempty overlaps (the standard convention; the nerve sees no others) | STATEMENT_NARROWED (`IsAcyclicCover`) |
| 12 | idem | `Fib` elaborated as `Type u → Type u` | binder name shadowed the base space | `{Fib : ↥X → Type u}` | STATEMENT_UNCHANGED |
| 13 | idem | `rw` pattern not found in the refinement theorem | used the lift-independence lemma where the value-independence lemma was needed | `spinCechClass_indep_of_values` | STATEMENT_UNCHANGED |
| 14 | idem | `Prod` applied to a `Prop` | `Σ'`-packaging of data + proof | introduced the structure `GoodRefinementData` | STATEMENT_UNCHANGED (same content) |
| 15 | idem | `unexpected token '/--'` | two consecutive docstrings | docstrings reattached to their declarations | STATEMENT_UNCHANGED |
| 16 | `lake build …Audit.Firewall` | `LAYERING VIOLATION … PointCohomology transitively imports Spine.E2.Topology.ModelTopology` | it imported `Cohomology.Core`, which reaches the Task-6 bridge spec | import narrowed to `Cohomology.Cohomology` | STATEMENT_UNCHANGED |

---

## 17. Build evidence

```
lake build RequestProject.Spine.E1.Core                  ✔
lake build RequestProject.Spine.E1.Topology.Core         ✔
lake build RequestProject.Spine.E2.Core                  ✔
lake build RequestProject.Spine.Cohomology.Core          ✔
lake build RequestProject.Spine.Cech.Core                ✔
lake build RequestProject.Spine.Geometry.Core            ✔
lake build RequestProject.Spine.Core                     ✔
lake build RequestProject.Spine.Audit.Firewall           ✔  "SPINE FIREWALL AUDIT: all checks passed"
lake build                                               ✔  Build completed successfully (8184 jobs)

new Task-7 targets, each built explicitly:
  RequestProject.Spine.GoodCover.Presimplicial           ✔
  RequestProject.Spine.GoodCover.NerveIdentification     ✔
  RequestProject.Spine.GoodCover.GoodCover               ✔
  RequestProject.Spine.GoodCover.PointCohomology         ✔
  RequestProject.Spine.GoodCover.AcyclicCover            ✔
  RequestProject.Spine.GoodCover.ManifoldCovers          ✔
  RequestProject.Spine.GoodCover.Constancy               ✔
  RequestProject.Spine.GoodCover.SingularComparisonSpec  ✔
  RequestProject.Spine.GoodCover.W2Interface             ✔
  RequestProject.Spine.GoodCover.Core                    ✔
```

Isolation, reported by the firewall over the 154 Spine modules present in its environment
(156 modules exist in the archive; the two-module gap is the one documented in
`TASK05_AUDIT.md`, and concerns modules that the audit environment does not import):

```
Experiment1 direct imports    = 0        Experiment1 transitive imports = 0
Experiment2 direct imports    = 0        Experiment2 transitive imports = 0
external-project imports      = 0
```

Additional mechanical layer checks added for Task 7: `GoodCover.Presimplicial` reaches **no**
project module at all; `GoodCover.GoodCover` and `GoodCover.NerveIdentification` reach no
`E1`/`E2`/`Geometry`/`Cohomology`/`Controls` module; `GoodCover.PointCohomology` reaches no
`E1`/`E2`/`Geometry`/`Čech`/`Controls` module; with the positive controls that
`NerveIdentification` *does* reach `Cech.Cohomology`, `Constancy` *does* reach
`Cech.SpinInstance`, and `SingularComparisonSpec` *does* reach `Cohomology.Core`.

## 18. Axiom audit

`RequestProject/Spine/GoodCover/Core.lean` runs `#print axioms` on all 36 principal Task-7
declarations.  Every one reports only

```
[propext, Classical.choice, Quot.sound]      (or a subset)
```

No `sorry`, no `admit`, no project-local `axiom`, no `unsafe`, no `partial`, no
`implemented_by`, and no equivalent proof bypass occurs in the new layer.

---

## 19. Answers to the final scientific questions

1. **Do suitable good covers exist for the manifold class used by the current Lorentz-frame
   formalization?**  Not natively, and not derivably in the pinned library.  What *is* proved is
   strictly weaker and genuinely useful: those manifolds are strongly locally contractible and
   admit arbitrarily fine covers by **contractible open** sets.  Good covers additionally require
   contractible *intersections*, whose only standard construction is Riemannian (geodesic
   convexity), and the pinned library has no Riemannian geometry on manifolds.  Good-cover
   existence is therefore **an explicit hypothesis** (`IsGoodCover`, `HasGoodCover`), Outcome C.
2. **Is the Task-6 Spin-lift class canonically represented in `H²_sing(M;ℤ₂)`?**  Not yet, and
   not canonically even conditionally.  Given a good cover, the class is represented in
   `Ȟ²(𝓤;ℤ₂) = H²_simp(N(𝓤);ℤ₂)` canonically (that identification is the identity, proved).  The
   step into singular cohomology exists only relative to three named missing theorems, and the
   resulting isomorphism depends on the chosen nerve realization: it is *dependent on a chosen
   nerve equivalence*, not canonical.
3. **Is the singular class independent of the chosen good cover?**  Refinement invariance is
   proved conditionally on a refinement-natural comparison family.  Full independence needs a
   common good refinement of two good covers, which is not available; the dependency is stated
   exactly (`CommonGoodRefinement`) and is not asserted.
4. **What is the minimal mathematically independent construction required before comparing with
   `w₂(TM)`?**  Homotopy invariance of the native singular mod-2 theory (WP9).  It is the unique
   first node shared by the comparison route, the good ⇒ acyclic implication, and both routes to
   an independent `w₂`; its inputs (the singular complex, the cup product, the point
   computation) already exist natively.

**Interpretation boundary (unchanged).**  `[z]` and `[z]_sing` are purely topological Spin-lift
obstructions.  They are not curvature, torsion, a spin connection, a gauge field strength, a
synchronization mismatch, gravity, matter, mass, dynamics, confinement or QCD structure, and
they are not claimed to be `w₂(TM)`.

---

## 20. Post-hoc correction (self-review, not a build failure)

`GoodCoverZ2.IsGoodCover` and `GoodCoverZ2.IsAcyclicCover` were first written quantifying over
index tuples `Fin n → ι` for *all* `n`, including `n = 0`.  The empty tuple has intersection
`Set.univ`, so that version silently demanded that the whole space be contractible (resp.
acyclic) — a condition on `X`, not on the cover, and strictly stronger than the conventional
good-cover condition.  Both predicates were corrected to quantify over `Fin (n + 1) → ι`, i.e.
over intersections of at least one cover member, which is the standard notion and is exactly
what the nerve sees.  Classification: **STATEMENT_WEAKENED (corrected to the intended,
conventional definition)**; all downstream theorems were rebuilt unchanged.
