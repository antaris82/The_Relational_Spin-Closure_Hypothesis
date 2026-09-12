# Task 27 — failed build attempts

Two compilation failures occurred, both in the new generic module, both purely a matter of Lean
API plumbing. No theorem statement was weakened, no finiteness hypothesis was reintroduced, and
the import DAG was not touched by either repair.

---

## 1. `AlgebraicTopology/DirectSumHomology.lean` — `homologyMap_finset_idem`

**Error**

```
error: RequestProject/Spine/AlgebraicTopology/DirectSumHomology.lean:120:24:
Application type mismatch: The argument
  congrArg (⇑(ModuleCat.Hom.hom (HomologicalComplex.homologyπ K q))) hcy
has type
  (homologyπ K q).hom ((cyclesMap (∑ s ∈ S, P s ≫ Ι s) q).hom z) = (homologyπ K q).hom z
but is expected to have type
  (fun g => g.hom z) (homologyπ K q ≫ homologyMap (∑ s ∈ S, P s ≫ Ι s) q) = ?m.321
```

**Diagnosis.** The naturality square `homologyπ_naturality` was turned into an elementwise
statement by `congrArg (fun g => g.hom z)`, which leaves the composite `f ≫ g` *unapplied*
inside the equation. `Eq.trans` then had to unify `(f ≫ g).hom z` with `g.hom (f.hom z)`; these
are definitionally equal but not syntactically, so elaboration of the `.trans` chain failed on
the metavariable.

**Repair.** State the elementwise naturality as a `have` **with its type written out** in the
applied form, so the `congrArg` result is checked against the intended statement, and finish
with `rw [hnat, hcy]` instead of a `Eq.trans` chain.

* theorem statement changed: no (only the proof).
* import DAG changed: no.

---

## 2. `AlgebraicTopology/DirectSumHomology.lean` — `isIso_sumHomologyMap_of_iso`

**Error**

```
error: RequestProject/Spine/AlgebraicTopology/DirectSumHomology.lean:211:2:
failed to synthesize instance of type class
  IsIso (sumHomologyMap (finsuppCxι α C) q ≫ HomologicalComplex.homologyMap Θ q)
```

**Diagnosis.** After rewriting the comparison as a composite, `IsIso` of the composite needs
`IsIso` of both factors. The first factor is the new theorem (supplied by `haveI`), but Lean has
no instance saying that `HomologicalComplex.homologyMap Θ q` is invertible when `Θ` is: that
fact is `Functor.map_isIso` for the homology functor, and `homologyMap` is not syntactically a
functor application.

**Repair.** Insert
`haveI : IsIso (HomologicalComplex.homologyMap Θ q) := by change IsIso ((HomologicalComplex.homologyFunctor _ _ q).map Θ); infer_instance`
before the rewrite.

* theorem statement changed: no.
* import DAG changed: no.

---

## Notes on the failure classes flagged in the task

* **`Finsupp` support** — no failure. `finsuppCx_sum_support_single` reduces to
  `Finsupp.sum_single` after two `show`s that unfold `finsuppCxπ ≫ finsuppCxι` to
  `Finsupp.single s (x s)`.
* **Quotient homology representatives** — no failure. Representatives are obtained from
  `Epi (K.homologyπ q)` via `ModuleCat.epi_iff_surjective`, and identified through
  `Mono (K.iCycles q)` via `ModuleCat.mono_iff_injective`; both instances exist in the pinned
  Mathlib, so no explicit quotient calculus was needed.
* **Infinite index types / implicit `Fintype`** — no hidden `Fintype` was found. The only
  `classical` invocations are for `DecidableEq` in `Finset` induction and `Finsupp.support`
  manipulation; `#check` on the four principal statements confirms that no `Fintype`, `Finite`
  or `DecidableEq` binder survives (recorded in `TASK27_AUDIT.md`, §4).
* **`HomologicalComplex.homologyMap` / `IsIso` inference** — the failure above (2) is exactly
  this class; the repair is local.

Two interim full-project builds were also aborted mid-flight because sources were edited while
`lake` was running (`lake build RequestProject` then reported a failure in
`Spine/Audit/ArchitectureDAG` against a stale environment). These are not source defects; the
final build was run on a quiescent tree.
