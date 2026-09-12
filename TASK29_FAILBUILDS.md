# Task 29 — failed builds and abandoned routes

Every failure below materially affected imports, statements, proof architecture, assumptions
or the choice of duality route.  Nothing is erased after the green build.

---

## F1. Inherited Task-28 point-set module does not compile

* **File / declaration**: `RequestProject/Spine/Nerve/Geometry/SkeletalFactorization.lean`,
  `NerveTopology.isClosedMap_realization_subcomplex`.
* **Exact errors** (first full build of the inherited tree):

  ```
  error: …/SkeletalFactorization.lean:77:12: Tactic `rewrite` failed: Did not find an
    occurrence of the pattern
      Rz.map ?g (cellPoint ?a ?w)
    in the target expression
      realMap A.ι (cellPoint ⟨K.map i.snd.op a, hcond⟩ v) =
        cellPoint a (stdSimplex.map (⇑(SimplexCategory.Hom.toOrderHom i.snd)) v)

  error: …/SkeletalFactorization.lean:90:6: Type mismatch
    IsClosed.preimage (continuous_cellPoint ?m.689) hS
  has type
    IsClosed (cellMap ?m.689 ⁻¹' S)
  but is expected to have type
    IsClosed {v | cellPoint ⟨K.map i.snd.op a, hcond⟩ v ∈ S}
  ```

* **Diagnosis**: (i) `NerveTopology.realMap` is a `def`, so `rw [cellPoint_naturality]`, whose
  left-hand side is `Rz.map _ (cellPoint _ _)`, does not match syntactically; (ii) the simplex
  argument of `continuous_cellPoint` sits under `cellMap` and was not inferred.
* **Repair**: proof-only.  A `show Rz.map A.ι (cellPoint …) = _` before the rewrite, and
  explicit `(X := ⦋(i.1 : ℕ)⦌)` plus the explicit simplex for `continuous_cellPoint`.
* **Theorem statement changed?**  No.
* **Assumption added?**  No.
* **Import DAG changed?**  No.

Note (a strengthening, not a repair): `exists_skeletal_factorization` was generalized from
`{Z : Type u}` to `{Z : Type v}`, because the domain of a singular simplex,
`stdSimplex ℝ (Fin (q+1))`, lives in `Type 0` while `K : SSet.{u}`.  The conclusion is
unchanged; the hypothesis is strictly weaker.

---

## F2. Higher-order unification against a graded family of modules

* **File / declarations**: `RequestProject/Spine/AlgebraicTopology/NaiveHomology.lean`
  (`cycles_eq_ker_dFrom`, `zeta`, …), later also
  `RequestProject/Spine/AlgebraicTopology/DualCohomology.lean`.
* **Exact error** (representative):

  ```
  error: Type mismatch
    ModuleCat.Hom.hom (K.d (m + 1) m)
  has type
    ↑(K.X (m + 1)) →ₗ[R] ↑(K.X m)
  but is expected to have type
    ?m.114 (m + 1) →ₗ[?m.112] ?m.114 m
  ```

  and, in `DualCohomology`, the same pattern degenerated into

  ```
  error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000)
  ```

* **Diagnosis**: the generic theory is indexed by a family `M : ℕ → Type u`; unifying
  `?M (n+1)` with `↑(K.X (n+1))` or with `α (n+1) →₀ ZMod 2` is not a Miller pattern, so Lean
  either fails or takes a very expensive path.
* **Repair**: reducible abbreviations whose head is a constant applied to the family —
  `SpineNaiveHomology.cxMod`, `SpineNaiveHomology.cxD` and `SpineDualCohomology.FreeMod` — so
  that first-order unification applies.  All uses of the generic theory are now stated through
  them.
* **Theorem statement changed?**  Only for the new generic theorems, whose binders were
  rewritten with the abbreviations; the abbreviations are reducible, so the propositions are
  the same.
* **Assumption added?**  No.
* **Import DAG changed?**  No.
* Residual cost: `SpineDualCohomology.bijective_Hmap` still needs
  `set_option maxHeartbeats 1000000`.

---

## F3. `moduleCatCyclesIso` carrier is not syntactically a kernel

* **File / declaration**: `NaiveHomology.lean`, `zeta_surjective`.
* **Exact error**:

  ```
  error: Type mismatch
    k
  has type
    ↑(HomologicalComplex.sc K n).moduleCatLeftHomologyData.K
  but is expected to have type
    ↑(K.X n)
  ```

* **Diagnosis**: an element of the Mathlib left-homology datum cannot be coerced to a chain by
  `↑`; the datum's carrier is a structure projection.
* **Repair**: the surjectivity proof now goes through `iCycles`
  (`mem_cycles_iCycles`, `zeta_iCycles`) instead of through the datum's carrier.
* **Statement / assumption / DAG**: unchanged.

---

## F4. `rw` and `exact` on composites of `ModuleCat` morphisms

* **File / declarations**: `NaiveHomology.lean`, `zeta_surjective`, `zeta_naturality`.
* **Exact errors**:

  ```
  error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
    (ModuleCat.Hom.hom (HomologicalComplex.sc K n).moduleCatCyclesIso.inv) ((Submodule.inclusion ⋯) ⟨…⟩)
  ```

  ```
  error: Type mismatch
    Eq.symm hnat'
  has type
    (ModuleCat.Hom.hom (cyclesMap F n ≫ homologyπ L n)) cK = …
  but is expected to have type
    (ModuleCat.Hom.hom (homologyMap F n)) ((ModuleCat.Hom.hom (homologyπ K n)) cK) = …
  ```

* **Diagnosis**: keyed matching fails on subterms containing anonymous constructor proofs; and
  `(a ≫ b).hom x` is definitionally but not syntactically `b.hom (a.hom x)`, while
  `simp [ModuleCat.hom_comp, LinearMap.comp_apply]` did not fire in this configuration.
* **Repair**: `congrArg` instead of `rw`; and a local `hcomp : (a ≫ b).hom x = b.hom (a.hom x)`
  proved by `rfl`, used as a rewrite rule.
* **Statement / assumption / DAG**: unchanged.

---

## F5. Duality route: missing lemmas and missing field structure

* **File / declaration**: `DualCohomology.lean`,
  `SpineDualCohomology.mem_coboundaries_iff`.
* **Exact errors**:

  ```
  error: Invalid field `exists_extend`: The environment does not contain
    `LinearMap.exists_extend`
  ```

  ```
  error: failed to synthesize instance of type class
    DivisionRing (ZMod 2)
  ```

  ```
  error: unknown tactic            -- `linear_combination` / `abel`
  ```

* **Diagnosis**: the module's import closure (inherited from `HomologyElements`, which imports
  only three Mathlib homology files) contained neither the algebraic Hahn–Banach extension
  lemma, nor the `Field (ZMod p)` instance, nor the tactic library.
* **Repair**: added `Mathlib.LinearAlgebra.Basis.VectorSpace`, `Mathlib.LinearAlgebra.Isomorphisms`,
  `Mathlib.LinearAlgebra.Dual.Lemmas`, `Mathlib.Data.Finsupp.Basic`, `Mathlib.Data.ZMod.Basic`,
  `Mathlib.Algebra.Field.ZMod` and `Mathlib.Tactic`, and a local
  `haveI : Fact (Nat.Prime 2)` where the field structure of `ℤ₂` is used.
* **Theorem statement changed?**  No.
* **Assumption added?**  No (the `Fact` instance is a proved fact, `Nat.prime_two`).
* **Import DAG changed?**  Yes, but only by *Mathlib* imports; no project-local edge.

---

## F6. Abandoned route: pattern-matched coboundaries in the generic layer

* **File / declaration**: `DualCohomology.lean`, first version of
  `SpineDualCohomology.coboundaries` / `Cohomology` / `Hmap`.
* **Diagnosis**: the generic theory originally *defined*
  `coboundaries δ 0 = ⊥`, `coboundaries δ (n+1) = range (δ n)` by pattern matching.  The
  project's own `Mod2Cohomology.coboundaries` and `NerveZ2.Presimplicial.coboundaries` are
  defined by the *same* pattern match but as different constants, so for a variable degree `n`
  the two are stuck `casesOn` applications of different auxiliary matchers; the quotient types
  `SpineDualCohomology.Cohomology` and `Mod2Cohomology.Cohomology` are then **not**
  definitionally equal, and transporting bijectivity across them would have required an ad-hoc
  chain of `Submodule.quotEquivOfEq`s — precisely the kind of "convenient replacement map" the
  task forbids.
* **Repair (design change)**: the coboundaries became *parameters* `BdA`, `BdB` of the generic
  theory, tied to `δ`, `ε` by the equations `BdA 0 = ⊥`, `BdA (n+1) = range (δ n)`.  Instantiated
  at the project's own coboundaries these equations hold by `rfl`, and
  `SpineDualCohomology.Hmap … = (NerveGeom.geometricCochainMap U).Hmap n` holds definitionally.
* **Theorem statement changed?**  Yes — of the *new* generic theorems only (they gained the
  four equations as hypotheses).  No pre-existing statement changed.
* **Assumption added?**  No: the equations are discharged by `rfl` at the point of use.
* **Import DAG changed?**  No.

The same device (parameters plus identifying equations) is used for the differentials in
`SpineNaiveHomology.bijective_homologyMap_of_isIso`, where
`sSetChainComplexFunctor_d` is only a propositional equality.

---

## F7. `export` after a doc comment

* **File**: `RequestProject/Spine/Nerve/Cochain/Dualization.lean`.
* **Exact error**:

  ```
  error: …/Dualization.lean:47:54: unexpected token 'export'; expected 'lemma'
  ```

* **Diagnosis**: a `/-- … -/` doc comment must be attached to a declaration; `export` is not one.
* **Repair**: the explanatory comment became a plain `/- … -/` block comment.
* **Statement / assumption / DAG**: unchanged.

---

## F8. The Task-27 architecture firewall rejects the new consumer

* **File**: `RequestProject/Spine/Audit/ArchitectureDAG.lean`, check 6.
* **Diagnosis**: check 6 asserted that *no* production module imports
  `Nerve.Comparison.RelJ`.  `Nerve.Comparison.GlobalHomology` legitimately consumes it, so the
  check had to fail (it did so for the Task-28 tree as delivered, which is why that tree could
  not have passed the audit unchanged).
* **Repair**: the check was **replaced, not weakened**, by the layering rule
  `lower AlgebraicTopology → lower Nerve geometry / cell machinery → RelJ → GlobalHomology →
  GlobalCohomology`, with four sub-checks: (a) only the three modules of the global comparison
  layer may reach `RelJ`; (b) nothing may reach the endpoint `GlobalCohomology`; (c) no
  geometry, skeleton, basic, cell-family, standard-cell or generic module may reach
  `GlobalHomology` or `GlobalCohomology`; (d) positive controls that each layer really reaches
  the layer below (so the negative checks cannot pass vacuously).
* **Statement / assumption**: unchanged.
* **Import DAG changed?**  The audited rule changed; the graph itself gained only the
  mathematically forced edges listed in `TASK29_AUDIT.md`.
