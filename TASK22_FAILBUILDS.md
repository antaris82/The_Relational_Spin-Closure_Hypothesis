# TASK 22 FAILBUILDS — every failed elaboration, its diagnosis and its repair

Every entry below is a genuine failed `lake build` of a Task-22 module.  **No mathematical
statement was weakened and no hypothesis was strengthened to make a build pass**; in particular
no finiteness hypothesis was added anywhere (see `TASK22_AUDIT.md` §1), and none of the
negative controls of the task specification was ever silently used.

---

## `Task22FiniteCellAdditivity.lean`

### F1 — `mem_Zc_top`, instance search through `ModuleCat` coercion

* **Failing elaboration**: `exact Subsingleton.elim _ _` after
  `haveI := subsingleton_relChain_of_lt X (m + 1) (Nat.lt_succ_self m)`.
* **Error**: `failed to synthesize instance of type class
  Subsingleton ↑((relChainCx (skInc X (m + 1))).X m)`.
* **Diagnosis**: purely an instance-resolution issue.  `(relChainCx f).X m` is
  `ModuleCat.of (ZMod 2) (RelChainMod f m)`, and typeclass search does not unfold the `ModuleCat`
  coercion to find the `Subsingleton` instance placed on `RelChainMod f m`.
* **Repair**: use the `Subsingleton` *term* directly as a projection,
  `(subsingleton_relChain_of_lt X (m + 1) (Nat.lt_succ_self m)).elim _ _`, which unifies up to
  definitional unfolding.
* **Mathematical statement changed**: no.

### F2 — `cellChainMap_single`, `simp` cannot see through `Finsupp.lmapDomain`

* **Failing elaboration**: `simp [cellChainMap, Finsupp.mapDomain_single]`.
* **Error**: unsolved goal
  `((Finsupp.lmapDomain (ZMod 2) (ZMod 2) fun σ => cellSimplex σ) fun₀ | σ => c) = fun₀ | cellSimplex σ => c`.
* **Diagnosis**: `Finsupp.lmapDomain` is definitionally `Finsupp.mapDomain` but `simp` did not
  rewrite the application; the statement is literally `Finsupp.mapDomain_single`.
* **Repair**: replace the tactic proof by the term `Finsupp.mapDomain_single`.
* **Mathematical statement changed**: no.

### F3 — `phi_injective`, `rw` with a `LinearMap.comp` equation

* **Failing elaboration**:
  `rw [congrFun (congrArg DFunLike.coe (normProj_comm (Sk X (r+1)) r)) W, ...]` (and the
  analogous `normProj_natural` step).
* **Error**: `Did not find an occurrence of the pattern (normProj … ∘ₗ sSetBoundary …) W`.
* **Diagnosis**: `normProj_comm` / `normProj_natural` are equalities of *composite* linear maps;
  `congrFun (congrArg DFunLike.coe …)` produces a statement about `(f ∘ₗ g) W`, which is
  definitionally but not syntactically the applied form in the goal.
* **Repair**: introduce the equation as a `have` and normalise it first with
  `simp only [LinearMap.comp_apply]`, then `rw`.
* **Mathematical statement changed**: no.

### F4 — `phi_injective`, wrong rewrite direction

* **Failing elaboration**: `rw [← hv, map_sub, h1, zero_sub, neg_eq_zero] at h2`.
* **Error**: `Did not find an occurrence of the pattern (sSetBoundary …) W - (cellChainMap X r) c`.
* **Diagnosis**: `hv : sSetChainMap (skInc X r) r v = ∂W - cellChainMap X r c`; the hypothesis
  `h2` contains the left-hand side, so the rewrite must be forwards, not backwards.
* **Repair**: `rw [hv, …] at h2`.
* **Mathematical statement changed**: no.

### F5 — `phi_injective`, orientation of the final `simpa`

* **Failing elaboration**: `simpa using h4`.
* **Error**: `After simplification, term h4 has type 0 = c σ but is expected to have type c σ = 0`.
* **Repair**: `simpa using h4.symm`.
* **Mathematical statement changed**: no.

### F6 — `phi_surjective`, residual `normChainEquiv_apply` goal

* **Failing elaboration**: the `rw [normChainEquiv_apply, normChainEquiv_apply, …]` chain left
  the goal `((normChainEquiv (Sk X (r+1)) r) ((normProj …) x)) a = x ↑a`.
* **Diagnosis**: after the earlier rewrites the pattern `normChainEquiv (normProj x) a`
  reappeared on the left-hand side, so one further application of the same lemma is required.
* **Repair**: close with `exact normChainEquiv_apply (Sk X (r + 1)) r x a`.
* **Mathematical statement changed**: no.

### F7 — `srcDecomp_single`, `rw` with `Finsupp.sum_single_index`

* **Failing elaboration**: `rw [Finsupp.sum_single_index (map_zero _)]`.
* **Error**: `Did not find an occurrence of the pattern (fun₀ | ?m => ?m).sum DFunLike.coe`.
* **Diagnosis**: the metavariable for the summand function was solved as `DFunLike.coe` rather
  than the intended `fun σ m => …`, so the pattern no longer matched.
* **Repair**: `exact Finsupp.sum_single_index (map_zero _)`.
* **Mathematical statement changed**: no.

### F8 — `lineSumEquiv_single`, unfolding `Finsupp.mapRange.linearEquiv`

* **Failing elaboration**:
  `simp [lineSumEquiv, Finsupp.mapRange.linearEquiv, Finsupp.mapRange.addEquiv, Finsupp.mapRange_single]`.
* **Error**: unsolved goal displaying the anonymous-constructor form of the `LinearEquiv`
  applied to `fun₀ | σ => 1`.
* **Diagnosis**: `simp` unfolded the structure but did not reduce the application of its
  `toFun` field.
* **Repair**: convert with an explicit
  `show Finsupp.mapRange (lineEquiv r) (map_zero _) (Finsupp.single σ 1) = _`, then
  `rw [Finsupp.mapRange_single]` and `congrArg (Finsupp.single σ) (one_smul _ _)`.
* **Mathematical statement changed**: no.

### F9 — `subsingleton_srcSumMod_of_ne`, `ext` on a `ModuleCat` object

* **Failing elaboration**: `ext σ` inside `Subsingleton (srcSumMod X r q)`.
* **Error**: `No applicable extensionality theorem found for type ↑(srcSumMod X r q)`.
* **Diagnosis**: `srcSumMod` is a `def` wrapping `ModuleCat.of`, so `ext` cannot see the
  underlying `Finsupp`.
* **Repair**: precede by
  `show Subsingleton (↑(X.nonDegenerate r) →₀ ((simpRel r).homology q))` and use
  `Finsupp.ext`.
* **Mathematical statement changed**: no.

---

## `Task22RelJCompatibility.lean`

### F10 — `relJ_decomposition_square`, instance mismatch in `Finsupp.single`

* **Failing elaboration**: `rw [srcDecomp_single, …]` after
  `refine ModuleCat.hom_ext (Finsupp.lhom_ext fun σ m => ?_)`.
* **Error**: `Did not find an occurrence of the pattern (ModuleCat.Hom.hom (srcDecomp ?X ?r ?q)) fun₀ | ?σ => ?m`,
  although the displayed goal is syntactically that expression.
* **Diagnosis**: the `Zero` instance argument of `Finsupp.single` produced by `Finsupp.lhom_ext`
  (through the `ModuleCat` coercion of `srcSumMod`) is definitionally but not syntactically the
  one in `srcDecomp_single`.
* **Repair**: insert an explicit `show` restating the goal, which re-elaborates
  `Finsupp.single σ m` with the canonical instances; the rewrites then match.
* **Mathematical statement changed**: no.

---

## `Task22CellSeparation.lean`

### F11 — spurious `congrArg` around cocone/iso identities

* **Failing elaborations**: `congrFun (congrArg _ (cellPushoutIso X r).hom_inv_id) z`,
  `congrFun (congrArg _ (realIsPushout X r).flip.w) w`.
* **Error**: application type mismatch — the metavariable introduced by `congrArg _` was never
  solved, so the term had type `?m (f ≫ g) z = ?m h z`.
* **Diagnosis**: in `Type u` a morphism *is* a function, so `congrFun` applies directly to an
  equation of morphisms; the `congrArg DFunLike.coe` idiom used for `ModuleCat` is not needed
  and actively harmful here.
* **Repair**: drop `congrArg _`.
* **Mathematical statement changed**: no.

### F12 — `real_cellMap_eq_cellMap_iff`, `∃ (_ : P), Q` versus `∃ …, P ∧ Q`

* **Failing elaboration**: `exact h''` after `rw [Types.Pushout.inl_rel'_inl_iff] at h''`.
* **Error**: type mismatch between
  `∃ x₀ y₀, ∃ (_ : g x₀ = g y₀), …` (Mathlib's shape) and the `∧`-shape used in the statement.
* **Diagnosis**: purely a shape difference in the existential.
* **Repair**: `rcases` and re-assemble.
* **Mathematical statement changed**: no.

### F13 — `real_cellMap_eq_cellMap_iff`, unapplied cocone identity

* **Failing elaboration**: `rw [hw, hw', hww']` where
  `hw := congrFun (realIsPushout X r).flip.w w`.
* **Error**: `Did not find an occurrence of the pattern (Real.map (bdryMap X r) ≫ Real.map (cellMap X r)) w`.
* **Diagnosis**: `congrFun` on an equation of composites yields the `≫`-form, not the applied
  form appearing in the goal.
* **Repair**: give `hw` and `hw'` explicit applied types, so that elaboration inserts the
  definitional unfolding once.
* **Mathematical statement changed**: no.

---

## Attempts that would have required a forbidden strengthening

Two routes were considered and **abandoned before being written**, precisely because they would
have required something the task forbids:

* **Arbitrary-coproduct preservation.**  Building `srcDecomp` as a `Limits.Sigma.desc` in
  `ModuleCat` and proving it an isomorphism through "homology preserves coproducts" would have
  needed an arbitrary-coproduct-preservation statement for the homology functor.  This was
  avoided entirely: the decomposition map is `Finsupp.lsum` of the canonical cell components and
  bijectivity is proved by hand from the Task-13 free-basis computation.  No coproduct
  preservation theorem, finite or infinite, is used.
* **Excision on the realized skeleton.**  The WP3 attempt stopped at the point where an *open*
  excisive family in `|Sk X (r+1)|` is required.  Producing one would have needed either local
  finiteness of geometric realization, or a CW closure-finiteness theorem, or an infinite wedge
  theorem — all explicitly excluded.  Rather than strengthening the hypotheses (for instance by
  assuming `X` itself finite, or finite-dimensional), the gap is reported: the underlying-set
  separation statement was proved instead (`Task22CellSeparation.lean`), and the remaining
  topological input is stated exactly in `TASK22_AUDIT.md` §14.  `SingularCellFamilyAdditivity`
  is left as an unproved, unassumed `Prop`.
