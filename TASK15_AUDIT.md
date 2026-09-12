# Task 15 — Standard-cell pair, realization monomorphisms, relative comparison

**Environment (frozen, unchanged):** Lean `v4.28.0`, Mathlib pinned at
`8f9d9cff6bd728b17a24e163c9402775d9e6a365` (`lake-manifest.json`, `lean-toolchain` and
`lakefile.toml` are byte-identical to their Task-14 state).

**Outcome classification: `F — precise remaining blocker`,** with substantially more proved
than in Task 14 and with the blocker isolated to a *single* statement about one fixed pair of
simplicial sets.

Concretely, Task 15 closes **WP1 in full**, closes **WP3 up to a single standard-cell
statement**, closes the **base case** and the **skeletal induction** of WP12 conditionally, and
proves the finite-dimensional comparison theorem *conditionally on exactly two explicitly
carried hypotheses*.  It does **not** prove the standard-cell homology theorem (WP5/WP7), the
excision-strength decomposition (WP9), the relative comparison isomorphism (WP11), or the
cohomology bridge (WP13).

Nothing below is assumed: there is no `sorry`, no `admit`, no project-local `axiom`, no
`native_decide`, and every principal declaration reports exactly
`[propext, Classical.choice, Quot.sound]`.

---

## 0. Inherited interfaces (frozen, not redefined)

`SSet.skeleton` / `SpineTask13.Sk` / `SpineTask13.skInc`; `X.nonDegenerate r`;
`SpineTask14.AttachData` / `attachExtend` / `attachExtend_comp_skInc` / `attachExtend_cell` /
`attachExtend_unique`; `SpineTask14.relChainCx` and the relative complex; the pair long exact
sequence; the canonical `J = C_*(η_K)` (`sSetChainComplexFunctor.map (sSetTopAdj.unit.app _)`);
`SpineTask14.relJ` and `relJ_generator`; `SpineTask14.oneSkeletonStep`.

**No comparison map was replaced.**  Every new theorem is stated for the frozen
`J = C_*(η_K)` and for `relJ`.  `SpineTask15.oneSkeletonStep_of_standardCell` and
`SpineTask15.skeletalInduction` are literal consumers of `SpineTask14.oneSkeletonStep`.

---

## 1. WP1 — the concrete pushout gap, closed

New module: `RequestProject/Spine/Nerve/Task15Pushout.lean`.

The Task-14 gap was that the concrete skeletal attachment theorem existed only as a bespoke
universal property (`AttachData`/`attachExtend`), while the transport theorem
`SpineTask14.toTop_isPushout` needed a `CategoryTheory.IsPushout`.  The two were never joined.

Proved here:

| declaration | statement |
|---|---|
| `charTot`, `cellChar`, `cellAttach` | the canonical characteristic map `Δ[r] ⟶ K^{(r)}` of a nondegenerate `r`-simplex, and the canonical attaching map `∂Δ[r] ⟶ K^{(r-1)}`; both are `σ · (−)`, nothing is chosen |
| `attachSrc`, `attachTgt`, `attachMap`, `bdryMap`, `cellMap` | the four objects and three maps of the square |
| `attach_commSq` | the square commutes |
| `coconeAttachData`, `pushoutDesc`, `pushoutDesc_left/right/uniq` | translation of a cocone under the square into Task-14 `AttachData`, and back |
| **`skeletalIsPushout`** | **`IsPushout (attachMap) (bdryMap) (skInc) (cellMap)`** — the concrete simplicial square *is* a categorical pushout |
| **`skeletalIsPushout_toTop`** | its image under `SSet.toTop` is a pushout in `TopCat` (this is the theorem-level composition Task 14 lacked) |
| **`skeletalIsPushout_toTop_coprod`** | the same square written with the honest coproducts `∐_σ |∂Δ[r]| → |K^{(r-1)}|`, `∐_σ |Δ[r]| → |K^{(r)}|`, transported along `PreservesCoproduct.iso` |

WP1 is therefore **complete**, in the required non-generic sense.

---

## 2. WP2 — inventory for realization of monomorphisms

Method: a full-text search of the pinned Mathlib source for `SSet.toTop`, `sSetTopAdj`,
`toTopSimplex`, and for the words *embedding*, *cofibration*, *injective* in conjunction with
geometric realization.

**Result: `SSet.toTop` occurs in exactly one file of the pinned library,
`Mathlib/AlgebraicTopology/SingularSet.lean`.**  Everything the pin knows about geometric
realization is:

| available theorem | form |
|---|---|
| `SSet.toTop` | *definition*: `stdSimplex.leftKanExtension SimplexCategory.toTop` |
| `sSetTopAdj` | `SSet.toTop ⊣ TopCat.toSSet` |
| `SSet.toTopSimplex` | `stdSimplex ⋙ toTop ≅ SimplexCategory.toTop` (representables only) |
| `SSet.toTop.IsLeftKanExtension` | the Kan-extension property |
| (derived, project) | `SpineTask14.realizationPreservesColimits`, `toTop_isPushout` |

| missing theorem | status in the pin |
|---|---|
| `Mono f → Function.Injective |f|` | **absent** |
| `|f|` is a topological embedding | **absent** |
| `|f|` is a closed embedding | **absent** |
| `|f|` is a cofibration | **absent** (no cofibration notion for `TopCat` at all) |
| realization preserves monomorphisms | **absent** |
| realization of a subcomplex is a subspace | **absent** |
| realization preserves finite limits / finite intersections | **absent** |
| pointwise (coend / quotient) model of `|X|` | **absent** — the Kan extension is never evaluated |
| `|X|` is a CW complex | **absent** |

| provable from the current API | how |
|---|---|
| realization preserves all colimits | left adjoint (already in the project) |
| realization preserves the initial object | special case; used below for `r = 0` |
| `|∐ A_i| ≅ ∐ |A_i|` | `PreservesCoproduct.iso` (used in WP1) |
| **injectivity of `|K^{(r-1)}| → |K^{(r)}|` from injectivity of `|∂Δ[r]| → |Δ[r]|`** | proved in WP3 below |

The decisive negative fact is the last "missing" row: because the pin never evaluates the left
Kan extension, there is **no handle at all** on the points of `|X|` for a non-representable
`X`.  This single API gap is what blocks both blocker `B2` and the *identification* step of
every route to blocker `B1` (see §5).

---

## 3. WP3 — the skeletal realization inclusion

New module: `RequestProject/Spine/Nerve/Task15RealizationMono.lean`.

We did **not** assume injectivity, and we did **not** encode it as a structure field.  What is
proved is a reduction, and the `r = 0` case outright.

* `sigmaMap_injective` — a coproduct of injections in `Type` is injective (via
  `Types.coproductIso`).
* `Real := SSet.toTop ⋙ forget TopCat`, with `PreservesColimitsOfSize` (both factors are left
  adjoints; `forget TopCat` is a left adjoint by `TopCat.adj₂`).
* `Real_sigmaMap_injective` — `Real` of a coproduct of maps is injective as soon as each factor
  is, via the comparison isomorphism `sigmaComparison Real`.
* `StandardCellMono r : Prop` — `Function.Injective (Real.map ∂Δ[r].ι)`, i.e. **`|∂Δ[r]| → |Δ[r]|`
  is injective**.  A statement about one fixed pair of simplicial sets.
* **`realization_skInc_injective`** — *if* `StandardCellMono r`, *then*
  `|K^{(r-1)}| → |K^{(r)}|` is injective, **for every simplicial set `K`**.
  Proof: the WP1 square is carried into `Type` by the colimit-preserving `Real`; the left
  vertical map is a coproduct of copies of `|∂Δ[r]| → |Δ[r]|`, hence a monomorphism; `Type` is
  adhesive, so `Adhesive.mono_of_isPushout_of_mono_right` gives that the pushout leg is a
  monomorphism.
* **`realizationInjective_of_standardCellMono`** — the same statement in the exact shape
  Task 14 consumes (`SpineTask14.RealizationInjective`).
* **`oneSkeletonStep_of_standardCell`** — Task-14's step with `B2` replaced by
  `StandardCellMono`.
* `boundaryZero_isEmpty`, `boundaryZero_isInitial`, **`standardCellMono_zero`** — `∂Δ[0]` is the
  initial simplicial set, so `|∂Δ[0]| = ∅` and `StandardCellMono 0` holds unconditionally;
  hence `realizationInjective_zero` is unconditional.

**Net effect on blocker `B2`.**  Task 14 carried "geometric realization of *the* skeletal
monomorphism of an *arbitrary* simplicial set is injective".  Task 15 replaces it by
"`|∂Δ[r]| → |Δ[r]|` is injective", one statement per `r`, with `r = 0` proved.  Nothing weaker
suffices for the argument as it stands, and nothing stronger is needed.

Stronger conclusions (topological embedding, closed embedding) were **not** attempted: they are
strictly harder in the pin than injectivity, because they require the topology of `|X|`, which
the pin never exposes, whereas injectivity was reachable through the set-level pushout.

---

## 4. WP4 — the singular relative pair interface

No new work was needed and none was done: Task 14 already proves, for any degreewise injective
map of simplicial sets, the short exact sequence
`0 → C_*(S) → C_*(T) → C_*(T,S) → 0` (`SpineTask14.relSC_shortExact`) and its long exact
sequence, and `SpineTask14.oneSkeletonStep` already consumes exactly that.  The vertical maps of
the comparison are `SpineTask14.relJSC`, whose `τ₂` is *definitionally* the frozen
`J = C_*(η)` (`relJ_tau₂` is `rfl`) and whose `τ₃` is `relJ` (`relJ_tau₃` is `rfl`).  No
substitute map exists anywhere in the Task-15 layer.

With WP3, the hypothesis of that interface is now supplied by `StandardCellMono`.

---

## 5. WP5–WP7 — the standard-cell theorem: **not proved**, with the exact first missing theorem

Target (unchanged, and *not* weakened): `H_q^{sing}(|Δ[r]|,|∂Δ[r]|;ℤ₂) = 0` for `q ≠ r`,
`≅ ℤ₂` for `q = r`, **together with** the statement that the identity/characteristic singular
`r`-simplex represents the nonzero class.  This is `SpineTask14.StandardCellPairAcyclic` /
`StandardCellPairTop`, strengthened by the generator clause.

### WP6 — topology audit of the pin

| ingredient | status in the pin |
|---|---|
| `|Δ[r]|` identified with the topological simplex | **available** (`SSet.toTopSimplex`) |
| `|Δ[r]|` contractible | **available in the project** (Task 12, `realization_stdSimplex_contractible`) |
| topology of `|∂Δ[r]|` | **absent** — nothing identifies `|∂Δ[r]|` with anything |
| `|∂Δ[r]| ≃ S^{r-1}` | **absent** |
| reduced homology of spheres | **absent** (no `H_*(Sⁿ)` anywhere) |
| relative homology of a disk/boundary pair | **absent** |
| `|Δ[r]|/|∂Δ[r]| ≅ S^r` | **absent** |
| cone / suspension of a space | **absent** (`Suspension`, `MappingCone` for spaces: 0 hits) |
| relative-to-reduced homology comparison | **absent** |
| relative singular homology at all | **absent**; the pin's `AlgebraicTopology/SingularHomology/Basic.lean` is 95 lines and contains only the definition plus the totally-disconnected computation |
| good pairs / neighbourhood deformation retracts | **absent** |

Consequently **Routes A, B and C all fail at the same first step**, and it is *not* excision:

> **First missing theorem for `B1`:** an identification of the space `|∂Δ[r]|`.  Every route
> (disk/sphere pair, quotient `X/A ≃ S^r`, contractible-total-space plus LES) needs to know
> what `|∂Δ[r]|` *is*, and the pin provides no evaluation of the left Kan extension defining
> `SSet.toTop` outside the representables.  This is the *same* API gap that blocks `B2`.

Only *after* that identification does the classical argument need excision-strength input
(Route C additionally needs `H_*(S^{r-1})`, which in turn needs Mayer–Vietoris or excision).

### WP7

Not attempted beyond the audit, for the reason just given: with `|∂Δ[r]|` unidentified there is
no route whose first step can be taken.  The generator clause was therefore not reached; it is
recorded as *not formally identified*.

---

## 6. WP8 — small-simplices / subdivision audit

| ingredient | status in the pin |
|---|---|
| barycentric subdivision of singular chains | **absent** (0 hits) |
| iterated subdivision | **absent** |
| chain homotopy between subdivision and the identity | **absent** |
| Lebesgue-number lemma | present for (pseudo-)emetric spaces (`Mathlib/Topology/EMetricSpace/Basic.lean`), *not* connected to singular chains |
| small singular simplices subordinate to a cover | **absent** |
| excision for singular homology | **absent** (0 hits for `excision`/`Excision`) |
| Mayer–Vietoris for singular homology | **absent** (the three `MayerVietoris` files are about sheaves/sites, not singular homology) |
| relative excision | **absent** |
| subdivision respecting pairs | **absent** |
| simplicial-set subdivision `sd ⊣ Ex` | **absent at the pin** (present only in current upstream, per the Task-11 audit) |

### Required documentation correction (inherited from Task 14)

The Task-14 formulation *"`B — FULL EXCISION IS GENUINELY REQUIRED`"* is **withdrawn** and
replaced by the justified statement:

> **No audited specialized route bypasses excision-strength small-simplices infrastructure in
> the pinned environment.**

Task 15 establishes no impossibility theorem, and in fact sharpens the diagnosis in the
opposite direction: the *first* obstruction on every audited route is not excision but the
absence of a pointwise model of geometric realization (§5).

Likewise the Task-14 status is recorded accurately as:

* WP3 concrete simplicial attachment: **proved** (Task 14);
* generic realization of categorical pushouts: **proved** (Task 14);
* their concrete theorem-level composition: **proved in Task 15, WP1**.

---

## 7. WP9–WP11 — not proved

* **WP9** (decomposition of `H_*(|K^{(r)}|,|K^{(r-1)}|)` into the cells) was not attempted; it
  needs an excision-strength statement, and it is downstream of `B1`, which is blocked earlier.
  We explicitly did **not** assume the decomposition from the pushout alone.
* **WP10** (comparison of relative generators) was not reached.  Task 14's
  `relJ_generator` — `J^rel[σ]` is the class of the characteristic singular simplex `η(σ)` —
  remains the only generator-level statement available, and it is untouched.  The
  corresponding *singular* summand generator does not exist yet, because WP5 is open.
* **WP11** (`H_q(J_r^{rel})` iso) remains open.  It is carried, unchanged, as the explicit
  hypothesis `SpineTask14.RelJIsIso`.

---

## 8. WP12 — base case and induction: proved, conditionally

New module: `RequestProject/Spine/Nerve/Task15BaseCase.lean`.

| declaration | statement | conditional? |
|---|---|---|
| `skZero_isEmpty`, `skZero_isInitial` | `Sk K 0` is the initial (empty) simplicial set | no |
| `realSkZero_isEmpty`, `singSkZero_isEmpty` | `|Sk K 0|` is empty and so is its singular simplicial set | no |
| `isZero_chain_of_isEmpty` | the mod-2 chain complex of an empty simplicial set is degreewise zero | no |
| **`baseCase`** | **`J` is a homology isomorphism on `Sk K 0`** | **no** |
| **`skeletalInduction`** | `J` is a homology isomorphism on `Sk K r` for every `r` | yes: `∀ r, StandardCellMono r` and `∀ r, RelJIsIso K r` |
| `skeleton_eq_top`, `skTopIso` | `K^{(d)} = K` and `Sk K d ≅ K` when `K.HasDimensionLT d` | no |
| **`finiteDimensional_homologyIso`** | **`H_q(J_K)` is an isomorphism for every finite-dimensional `K` and every `q`** | yes: the same two hypotheses |

So the *global* shape of WP12 is now a theorem; only its two topological inputs are open.  The
statement is genuinely about the frozen `J`: it is
`HomologicalComplex.homologyMap (sSetChainComplexFunctor.map (sSetTopAdj.unit.app X)) q`.

---

## 9. WP13 — cohomology bridge: audited, not formalized

The project already owns (Task 10) the implication

> chain-homotopy-equivalence data for `J` ⟹ `GeometricComparison` ⟹ `geometricHmap` bijective,

and it is *not* duplicated here.  What is still missing is the algebraic half

> `H(J)` iso over `ℤ₂` ⟹ `J` is a chain-homotopy equivalence.

Audit of the pin: there is no such statement for `ChainComplex (ModuleCat (ZMod 2)) ℕ`.  The
route sketched in the task (complexes of vector spaces split; an acyclic complex of vector
spaces is contractible; hence a quasi-isomorphism has contractible mapping cone) is not present
either — the pin has `HomologicalComplex.mappingCone`-style machinery in the cochain setting and
K-projective/derived-category machinery, but no "quasi-iso ⟹ homotopy equivalence over a field"
theorem.  (`QuasiIso`/`QuasiIsoAt` themselves *are* present, and are by definition degreewise
`IsIso` on homology, so `finiteDimensional_homologyIso` is exactly a `QuasiIso` statement in the
pin's own vocabulary; what is absent is the passage from there to a homotopy equivalence.)

Since WP11 is open, this bridge is not on the critical path yet, and it was deliberately not
formalized: `finiteDimensional_homologyIso` is a homology statement, and no claim is made — here
or anywhere in the project — that `geometricHmap` is bijective.  **`geometricHmap` is still not
proved bijective.**

---

## 10. WP14

Not invoked.  Nothing in the Task-15 layer mentions the nerve theorem, `|N(𝒰)| ≃ M`, or `w₂(TM)`.

---

## 11. New theorem dependency DAG (Task 15 only)

```
SpineTask14.AttachData / attachExtend / attachExtend_comp_skInc
        / attachExtend_cell / attachExtend_unique        [Task 14, frozen]
                    │
                    ▼
 coconeAttachData ─▶ pushoutDesc ─▶ pushoutDesc_left
                                 ─▶ pushoutDesc_right ─▶ cellChar_yonedaEquiv
                                 ─▶ pushoutDesc_uniq
                    │
                    ▼
            skeletalIsPushout          (WP1.1)
                    │
     ┌──────────────┴───────────────┐
     ▼                              ▼
skeletalIsPushout_toTop     (IsPushout.map Real)
   (WP1.2, via SpineTask14.toTop_isPushout)
     │                              │
     ▼                              ▼
skeletalIsPushout_toTop_coprod   realization_skInc_injective   (WP3)
   (WP1.3)                          ▲            ▲
                                    │            │
              Real_sigmaMap_injective            Adhesive (Type)
                       ▲
              sigmaMap_injective  (Types.coproductIso)

realization_skInc_injective ─▶ realizationInjective_of_standardCellMono
                              ─▶ oneSkeletonStep_of_standardCell
                                        │   (consumes SpineTask14.oneSkeletonStep)
                                        ▼
 skZero_isEmpty ─▶ skZero_isInitial ─▶ realSkZero_isEmpty ─▶ singSkZero_isEmpty
                                        │
                     isZero_chain_of_isEmpty
                                        ▼
                                    baseCase
                                        │
                                        ▼
                                skeletalInduction
                                        │
             skeleton_eq_top ─▶ skTopIso ─▶ finiteDimensional_homologyIso

boundaryZero_isEmpty ─▶ boundaryZero_isInitial ─▶ standardCellMono_zero
                                                  ─▶ realizationInjective_zero
```

## 12. Source modules reused

`RequestProject/Spine/Nerve/Task13Skeletal.lean` (`Sk`, `skInc`),
`Task14SkeletalAttachment.lean` (the whole universal property, `mem_skeleton_of_not_epi`,
`nonDeg_mem_of_mem`, `cellSimplex`), `Task14RelativeChains.lean`
(`sSetChainComplexFunctor`, `relSC_shortExact`), `Task14RelativeLES.lean`,
`Task14Comparison.lean` (`toTop_isPushout`, `relJ`, `RealizationInjective`, `oneSkeletonStep`),
`Task14Blocker.lean` (`RelJIsIso`).  Pinned Mathlib: `SimplicialSet/{StdSimplex, Boundary,
Subcomplex, Skeleton, Dimension}`, `SingularSet`, `CategoryTheory/Adhesive/Basic`,
`CategoryTheory/Limits/Types/Coproducts`, `CategoryTheory/Limits/Preserves/Shapes/Products`,
`Topology/Category/TopCat/{Adjunctions, EpiMono}`.

## 13. Newly added modules

* `RequestProject/Spine/Nerve/Task15Pushout.lean`
* `RequestProject/Spine/Nerve/Task15RealizationMono.lean`
* `RequestProject/Spine/Nerve/Task15BaseCase.lean`

## 14. Build status and axiom/sorry audit

`lake build` is green for the whole default target, including the three new modules and the
firewall audit (`SPINE FIREWALL AUDIT: all checks passed`; Experiment1/Experiment2 direct and
transitive imports = 0).  `rg` over the Task-15 layer finds no `sorry`, `admit`, `axiom`,
`unsafe`, `partial`, `implemented_by` or `native_decide`.  `#print axioms` on
`skeletalIsPushout`, `skeletalIsPushout_toTop_coprod`, `realization_skInc_injective`,
`realizationInjective_of_standardCellMono`, `oneSkeletonStep_of_standardCell`,
`standardCellMono_zero`, `baseCase`, `skeletalInduction` and `finiteDimensional_homologyIso`
returns exactly `[propext, Classical.choice, Quot.sound]`.

## 15. Failed proof routes

See `TASK15_FAILBUILDS.md` for the append-only ledger with provenance, diagnosis and repair.
Mathematically distinct dead ends:

1. **Proving `StandardCellMono r` for general `r` by self-application of
   `realization_skInc_injective`.**  Since `∂Δ[r] = Sk Δ[r] r` and `Δ[r] = Sk Δ[r] (r+1)`, the
   reduction applied to `X = Δ[r]` returns exactly its own hypothesis.  Circular; abandoned.
2. **Deriving `Mono |f|` from `Mono f` by a purely categorical argument.**  Realization is only
   known to be a *left* adjoint, so it preserves colimits, not monomorphisms; `TopCat` is not
   registered as adhesive in the pin, and even if it were, that would give preservation of
   pushouts of monos, not creation of monos.  The set-level route through `Type` (which *is*
   adhesive) is the one that worked, and only for the pushout leg.
3. **Building `|∂Δ[r]| ↪ |Δ[r]|` from `boundary_eq_iSup` and the pin's bicartesian squares.**
   The pin does provide `SSet.Subcomplex.BicartSq.isPushout`: for subcomplexes with
   `A₁ = A₂ ⊓ A₃` and `A₄ = A₂ ⊔ A₃`, the square of subcomplexes is a pushout, so its
   realization is a pushout of spaces, and the union of the faces of `Δ[r]` can be assembled by
   iterating it.  This route still fails, and the failure is instructive: to conclude that
   `|A₂ ⊔ A₃| → |Δ[r]|` is injective one needs the *images* of `|A₂|` and `|A₃|` in `|Δ[r]|` to
   meet exactly in the image of `|A₂ ⊓ A₃|`, i.e. one needs realization to preserve that
   intersection (a finite limit).  Adhesiveness of `Type` gives the pushout square back as a
   pullback over `|A₄|`, which is not the same statement.  Preservation of the intersection is
   precisely one of the "missing" rows of the WP2 inventory.

## 16. Answers to the required final questions

1. **Exact new theorem dependency DAG** — §11.
2. **Exact source modules reused** — §12.
3. **Every newly added module** — §13.
4. **Build status** — green; §14.
5. **Axiom/sorry audit** — clean; §14.
6. **All failed proof routes** — §15 and `TASK15_FAILBUILDS.md`.
7. **Exact status of B1, B2, B3** —
   * `B1` (standard cell pair, with generator): **open**, and its first missing theorem is now
     identified as the *identification of the space* `|∂Δ[r]|`, upstream of excision.
   * `B2` (realization injectivity): **reduced to `StandardCellMono r`** and **proved for
     `r = 0`**; the general skeletal statement is a theorem conditional on it.
   * `B3` (`RelJIsIso`): **open**, unchanged, carried explicitly.
8. **Is the characteristic-simplex generator formally identified?** On the *simplicial* side
   yes, by the inherited `SpineTask14.relJ_generator`.  On the *singular* side **no**: the
   nonvanishing of `[id_{|Δ[r]|}]` in `H_r(|Δ[r]|,|∂Δ[r]|;ℤ₂)` is **not** proved, and no
   equivalence `H_r ≅ ℤ₂` was constructed.
9. **Is the concrete realized skeletal pushout formally obtained?** **Yes** —
   `skeletalIsPushout_toTop` and `skeletalIsPushout_toTop_coprod`.
10. **Is `J_r^{rel}` now a homology isomorphism?** **No.**  It remains the explicit hypothesis
    `RelJIsIso`.
11. **Is finite-dimensional `J` now a quasi-isomorphism?** **Conditionally.**
    `finiteDimensional_homologyIso` proves it from `∀ r, StandardCellMono r` and
    `∀ r, RelJIsIso X r`; both are open.  Unconditionally, only the base case `Sk K 0` and the
    `r = 0` injectivity are proved.
12. **Is `geometricHmap` now proved bijective?** **No**, and no step towards it was taken beyond
    the audit in §9.
13. **Exact first remaining blocker.**
    > There is no theorem in the pinned environment that evaluates the left Kan extension
    > defining `SSet.toTop` at a non-representable simplicial set.  Concretely, the first
    > missing theorem is a description of the points of `|X|` (Milnor's normal form: every point
    > is `[x, t]` for a unique nondegenerate simplex `x` and interior point `t`), or any
    > substitute sufficient to (i) prove `StandardCellMono r`, and (ii) identify `|∂Δ[r]|`.
    > Excision-strength small-simplices infrastructure is the *second* blocker, needed after
    > that identification for WP7/WP9; it too is entirely absent.
