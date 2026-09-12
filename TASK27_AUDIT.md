# Task 27 — arbitrary direct-sum homology and the closure of blocker B3

**Principal outcome: Outcome A — arbitrary B3 closed.**

---

## 1. Pin

Unchanged from the frozen environment:

```
lean-toolchain      : leanprover/lean4:v4.28.0
Mathlib revision    : 8f9d9cff6bd728b17a24e163c9402775d9e6a365   (lake-manifest.json)
```

`lean-toolchain`, `lake-manifest.json` and the Mathlib revision were not modified.

## 2. The arbitrary direct-sum homology theorem

`RequestProject/Spine/AlgebraicTopology/DirectSumHomology.lean`:

```lean
theorem SpineTask23.isIso_sumHomologyMap_finsuppCxι
    {α : Type u} {C : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ} (q : ℕ) :
    IsIso (sumHomologyMap (finsuppCxι α C) q)
```

`sumHomologyMap (finsuppCxι α C) q : (α →₀ H_q(C)) ⟶ H_q(⊕_α C)` is the map sending
`Finsupp.single s m` to `H_q(ι_s) m`; the theorem says it is an isomorphism, i.e.

  H_q( ⊕_{α} C )  ≅  ⊕_{α} H_q(C),

with the *project's own* `Finsupp`-based direct sum `finsuppCx α C` and its own comparison map
— no representation was replaced and no downstream API changed shape.

Two further public forms:

```lean
theorem SpineTask23.isIso_sumHomologyMap_of_splitting (Ι : α → (C ⟶ K)) (P : α → (K ⟶ C))
    (h1 : ∀ s, Ι s ≫ P s = 𝟙 C) (h2 : ∀ s t, s ≠ t → Ι s ≫ P t = 0)
    (h3 : ∀ (q : ℕ) (x : K.X q), ∃ S : Finset α, ∑ s ∈ S, ((P s ≫ Ι s).f q).hom x = x)
    (q : ℕ) : IsIso (sumHomologyMap Ι q)

theorem SpineTask23.isIso_sumHomologyMap_of_iso {K} (Θ : finsuppCx α C ⟶ K) [IsIso Θ] (q : ℕ) :
    IsIso (sumHomologyMap (fun s => finsuppCxι α C s ≫ Θ) q)
```

## 3. Proof strategy

**Route A/B hybrid, in the form of an explicit local-finiteness argument** (not Route C: the
pinned Mathlib has no ready statement that homology commutes with coproducts of complexes, and
no exactness package for the functor `M ↦ (α →₀ M)`).

* *Injectivity* is formal and index-free: applying `H_q(P t)` to the image of
  `c : α →₀ H_q(C)` returns `c t`, because `Ι s ≫ P t` is `𝟙` for `s = t` and `0` otherwise and
  the homology functor is additive (`homologyMap_retraction_sumHomologyMap`).
* *Surjectivity* is where finite support is used. A class `y ∈ H_q(K)` is `π z` for some cycle
  `z` (`Epi (K.homologyπ q)`); its underlying chain `i z` is, by local finiteness, fixed by the
  partial idempotent `e_S = ∑_{s ∈ S} P s ≫ Ι s` for a **finite** `S`. Since `K.iCycles q` is a
  monomorphism, `e_S` fixes `z`, hence `H_q(e_S) y = y` (`homologyMap_finset_idem`); additivity
  of the homology functor then rewrites this as
  `y = ∑_{s ∈ S} H_q(Ι s)(H_q(P s) y)`, which exhibits `y` as the image of the finitely
  supported family `∑_{s ∈ S} single s (H_q(P s) y)`.
* For the direct sum itself the local-finiteness input is
  `finsuppCx_sum_support_single : ∑_{s ∈ x.support} single s (x s) = x`, i.e. exactly the
  finite-support property of `Finsupp`. This is the single place where finiteness of anything
  occurs, and it is a property of each individual chain, not of the index type.

## 4. The index type is genuinely arbitrary

`#check` on the compiled declarations (run with `lake env lean`):

```
@SpineTask23.isIso_sumHomologyMap_finsuppCxι :
  ∀ {α : Type u_1} {C : ChainComplex (ModuleCat (ZMod 2)) ℕ} (q : ℕ),
    IsIso (SpineTask23.sumHomologyMap (SpineTask23.finsuppCxι α C) q)

@SpineTask23.isIso_sumHomologyMap_of_iso :
  ∀ {α : Type u_1} {C K : ChainComplex (ModuleCat (ZMod 2)) ℕ}
    (Θ : SpineTask23.finsuppCx α C ⟶ K) [IsIso Θ] (q : ℕ), IsIso (…)

SpineTask24.isIso_tgtDecomp : ∀ (X : SSet) (r q : ℕ), IsIso (SpineTask22.tgtDecomp X r q)
SpineTask24.relJIsIso      : ∀ (X : SSet) (r : ℕ), SpineTask14.RelJIsIso X r
```

No `[Fintype α]`, no `Finite α`, no `Fintype.ofFinite`, no `DecidableEq α` binder occurs in any
of them. `classical` is used inside three proofs only to obtain decidable equality for
`Finset.induction` and for `Finsupp.support` manipulation; it carries no cardinality
information and appears in no statement.

## 5. The arbitrary target decomposition

`RequestProject/Spine/Nerve/CellFamily/TargetDecomposition.lean`:

```lean
theorem SpineTask24.isIso_tgtDecomp (X : SSet.{u}) (r q : ℕ) : IsIso (tgtDecomp X r q)
```

It is obtained exactly as prescribed: the already existing arbitrary-family relative chain
isomorphism `Θ_rel` (`SpineTask24.thetaRel`, `isIso_thetaRel`) plus the new direct-sum homology
theorem give `isIso_sumCellHomology` for an arbitrary cell family in
`Nerve/CellFamily/RelativeChainDecomposition.lean`; the already existing standard-cell /
open-cell comparison `stdCellIso`, the excision compatibility `cellPairIso` and the frozen
identification `mapRangeStd_tgtDecomp` were reused unchanged. No geometry was rebuilt.

The name `isIso_tgtDecomp` was free (the finite theorem was called `isIso_tgtDecomp_finite`),
so no `_arbitrary` suffix was needed; `isIso_tgtDecomp_finite` is retained, with its original
statement, as a wrapper.

## 6. The arbitrary `RelJIsIso`

`RequestProject/Spine/Nerve/Comparison/RelJ.lean` (renamed from `FiniteRelJ.lean`):

```lean
theorem SpineTask24.singularCellFamilyAdditivity (X : SSet.{u}) (r : ℕ) :
    SingularCellFamilyAdditivity X r

theorem SpineTask24.relJIsIso (X : SSet.{u}) (r : ℕ) : SpineTask14.RelJIsIso X r
```

using the already proved comparison square `srcDecomp ≫ H(relJ) = sumCellRelJ ≫ tgtDecomp`
(`relJIsIso_of_singularCellFamilyAdditivity`), whose other two ingredients were already
isomorphisms. Nothing beyond B3 was attempted.

## 7. Finite regression

Both required finite endpoints still exist, with unchanged statements, and compile:

* `SpineTask24.isIso_tgtDecomp_finite [Fintype ↑(X.nonDegenerate r)] : IsIso (tgtDecomp X r q)`
* `SpineTask24.relJIsIso_finite [Fintype ↑(X.nonDegenerate r)] : SpineTask14.RelJIsIso X r`

as do `singularCellFamilyAdditivity_finite`, `finiteSingularCellFamilyAdditivity_finite`,
`SpineTask23.relJIsIso_of_finite`, `SpineTask23.isIso_sumHomologyMap` (finite splitting
criterion, now a corollary of the general one) and
`SpineTask23.isIso_sumHomologyMap_of_iso` (same name and conclusion, two instance hypotheses
dropped — a strict weakening of hypotheses, so no call site changed).

## 8. Full build

```
$ lake build RequestProject
Build completed successfully (8276 jobs).
```

0 errors; no `sorry`, `admit`, `native_decide`, `unsafe`, `@[implemented_by]` or project-local
`axiom` anywhere in the tree. The build emits 74 linter warnings, all of them pre-existing and
all of them in `Spine/E1`, `Spine/E2`, `Spine/Foundation` and other areas untouched by this
task; none of the modules created or edited here produces a warning.

## 9. ArchitectureDAG

`Spine/Audit/ArchitectureDAG.lean` compiles (it is part of the default target) and reports:

```
Stage-1.3 production modules audited: 79 (of 232 production Spine modules);
    chronological TaskNN modules: 0
generic AlgebraicTopology modules audited: 29, domain-specific imports: 0
low-level Nerve modules audited: 18, high-level imports: 0
SPINE ARCHITECTURE AUDIT: all checks passed
```

The audit was **strengthened**, not relaxed: check 5 gained an explicit `auditNoReach` for
`AlgebraicTopology.DirectSumHomology`, and the positive control of check 6 now also requires
the endpoint to reach `AlgebraicTopology.DirectSumHomology`. Check 6 was retargeted from
`Nerve.Comparison.FiniteRelJ` to its new name `Nerve.Comparison.RelJ`; the endpoint is still a
leaf (no production module imports it). The legacy firewall (`Spine/Audit/Firewall.lean`) is
unchanged and still passes.

## 10. Axioms

Every declaration of the project is `#print axioms`-audited in
`Spine/Nerve/Audit/Stage13Axioms.lean` and in the per-module audit modules; the extracted table
is `scripts/task27_axioms_post.txt` (1010 declarations). Distribution:

```
1007  [Classical.choice, Quot.sound, propext]
   2  [Quot.sound, propext]
   1  [propext]
```

No `sorryAx`, no `native_decide` axiom, no project-local axiom. The diff against the Task-25
baseline table (`scripts/task25_axioms_post.txt`) consists of exactly the seven new
declarations, each with the baseline axiom set:

```
SpineTask23.finsuppCx_sum_support_single
SpineTask23.homologyMap_finset_idem
SpineTask23.isIso_sumHomologyMap_finsuppCxι
SpineTask23.isIso_sumHomologyMap_of_splitting
SpineTask24.isIso_tgtDecomp
SpineTask24.relJIsIso
SpineTask24.singularCellFamilyAdditivity
```

Explicitly, for the three required endpoints:

```
'SpineTask23.isIso_sumHomologyMap_finsuppCxι' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpineTask24.isIso_tgtDecomp'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'SpineTask24.relJIsIso'                       depends on axioms: [propext, Classical.choice, Quot.sound]
```

and for the helper carrying the infinite-family argument,

```
'SpineTask23.isIso_sumHomologyMap_of_splitting' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 11. Dependency metrics

Measured with `scripts/arch_metrics.py` over
`RequestProject.Spine.AlgebraicTopology` + `RequestProject.Spine.Nerve`
(`scripts/task27_metrics_pre.txt`, `scripts/task27_metrics_post.txt`):

| metric | before | after |
|---|---|---|
| production modules | 84 | 85 |
| Lean LOC | 17575 | 17724 |
| internal import edges | 143 | 145 |
| all project import edges | 150 | 152 |
| max internal import depth | 24 | **24** |
| longest internal chain | Stage13Axioms → FiniteRelJ → … → SimplicialChains | Stage13Axioms → RelJ → … → SimplicialChains (same chain, renamed head) |

Transitive project-local closures:

| endpoint | closure |
|---|---|
| `AlgebraicTopology.DirectSumHomology` | 4 modules: `DirectSumComplex`, `RelativeChains`, `SimplicialChains`, `Normalization` |
| `Nerve.CellFamily.TargetDecomposition` | 40 (was 39) |
| arbitrary `RelJ` endpoint | 62 (was 61 for `FiniteRelJ`) |

The critical path did **not** grow: the new module was attached as a sibling one level above
`DirectSumComplex`, whose own depth is far below the maximum, so the two new edges add one
module to each downstream closure and nothing to the depth.

## 12. Code hygiene

See `TASK27_CODE_HYGIENE.md`. Summary: one new content-named generic module below `Nerve`; one
module renamed to match its (now more general) content; two new import edges, both mathematically
forced; no duplicated finite/arbitrary proof logic (the finite splitting criterion is now a
corollary); two obsolete finite-only helpers deleted; no task-number namespaces or chronological
comments introduced.

## 13. Failbuilds

See `TASK27_FAILBUILDS.md`. Two compilation failures, both in the new generic module, both API
plumbing (an elementwise naturality square that needed its type written out, and an `IsIso`
instance for `homologyMap` of an isomorphism). Neither changed a statement, neither changed the
import DAG, and no failure was patched by reintroducing a finiteness hypothesis.

## 14. Remaining Stage-1.3 frontier

```
B1: CLOSED
B2: CLOSED
B3 finite: CLOSED
B3 arbitrary: CLOSED
Next mathematical edge:
global skeletal assembly / canonical simplicial-singular comparison.
```

Nothing beyond B3 was attempted: no global skeletal induction, no global homology equivalence,
no Nerve theorem, no Čech-to-manifold comparison, no `w₂(TM)`.
