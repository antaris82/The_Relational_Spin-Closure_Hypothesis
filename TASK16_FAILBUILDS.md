# Task 16 — failed builds and failed proof routes

Every failure below was observed in the pinned environment and is recorded with its diagnosis
and the repair that was applied.  The final state of the tree builds green.

## F1. `Real` collides with `_root_.Real`

*Provenance:* first draft of `Task16PointModel.lean`, statements written as `Real.{u}.obj …`
with `SpineTask15.Real` in scope via `open SpineTask15 in`.

*Error:* `too many explicit universe levels for 'Real'`, then
`AddConstAsyncResult.commitConst: constant has level params [u, u_1, u_2] but expected [u_1, u_2]`.

*Diagnosis:* `open … in` applies to one declaration only, and inside a statement `Real` resolves
to `_root_.Real` (the real numbers), which has no universe parameters.

*Repair:* introduced the local reducible abbreviation `SpineTask16.Rz := SpineTask15.Real` and
used it uniformly.  (This is the standard "avoid Mathlib name collisions" repair; no
mathematical content is affected — `Rz` is *definitionally* the Task-15 functor, as the final
`standardCellMono : SpineTask15.StandardCellMono r` shows.)

## F2. Colimit preservation at the wrong universe level

*Provenance:* first attempt at `exists_representative`.

*Error:* `failed to synthesize PreservesColimit (CostructuredArrow.proj uliftYoneda A ⋙ uliftYoneda) Rz`.

*Diagnosis:* the Task-15 instance is `PreservesColimitsOfSize.{u, u}`, whereas the index
category `CostructuredArrow uliftYoneda A` has objects in `Type u` and morphisms in `Type 0`.

*Repair:* declared the universe-polymorphic instances
`PreservesColimitsOfSize.{v, w}` for `forget TopCat`, `SSet.toTop` and `Rz`, all obtained from
`Adjunction.leftAdjoint_preservesColimits`.

## F3. `stdSimplex.map` coordinate formula not reachable by `simp`

*Provenance:* the `map_apply` lemma.

*Error:* `simp [stdSimplex.map, FunOnFinite.linearMap_apply_apply]` left
`⟨(FunOnFinite.linearMap ℝ ℝ g) ⇑u, _⟩ y = ∑ x with g x = y, u x`.

*Diagnosis:* the `FunLike` coercion of the subtype `stdSimplex ℝ X` blocks `simp` from seeing
the underlying linear map.

*Repair:* replaced the `simp` by an explicit `show (FunOnFinite.linearMap ℝ ℝ g) (u : X → ℝ) y = _`
followed by `rw [FunOnFinite.linearMap_apply_apply]`.

## F4. `∑ x, u x` versus `∑ x, ↑u x`

*Provenance:* `supp_nonempty`.

*Error:* `rewrite failed: did not find ∑ x, ↑u x` when using `u.2.2`.

*Diagnosis:* `u.2.2` is stated for the `Subtype.val` coercion, the goal for the `FunLike` one.

*Repair:* used the library lemmas `stdSimplex.sum_eq_one` and `stdSimplex.zero_le`, which are
stated for the `FunLike` coercion.

## F5. `Finset.filter` rewriting under a mismatched `Decidable` instance

*Provenance:* `range_bdCoord` and the `r = 1` smoke test.

*Error:* `rewrite failed: did not find an occurrence of the pattern …filter (fun a => e a = i)…`,
and a leftover goal `(toOrderHom e) 0 = i` after `simp`.

*Diagnosis:* the `DecidableEq (Fin (⦋r⦌.len+1))` instance in the goal (coming from `map_apply`)
is not syntactically the one elaborated in the `show`/`rw` term.

*Repair:* avoided rewriting the filter altogether: the vanishing case is now
`Finset.sum_eq_zero fun a ha => absurd (Finset.mem_filter.1 ha).2 (hi a)`, and the `r = 1` case
was rewritten to use `stdSimplex.map_vertex` on the unique point of `stdSimplex ℝ (Fin 1)`,
which removes the coordinate computation entirely.

## F6. `omega` on `⦋k⦌.len`

*Provenance:* the `r = 1` smoke test.

*Error:* `omega could not prove the goal … a := ↑⦋1⦌.len, b := ↑⦋k⦌.len, c := ↑k`.

*Diagnosis:* `omega` treats `⦋k⦌.len` as an opaque atom.

*Repair:* `simp only [SimplexCategory.len_mk] at hcard` before `omega`.

## F7. `Subsingleton (stdSimplex ℝ (Fin (0+1)))` not found

*Provenance:* the `r = 1` smoke test, first attempt (`Subsingleton.elim`).

*Diagnosis:* instance search does not reduce `Fin (0+1)` to `Fin 1` for the
`Subsingleton`/`Unique` instances.

*Repair:* proved `v = stdSimplex.vertex 0` by hand from `stdSimplex.sum_eq_one` and
`Fin.sum_univ_one`.

## F8. Implicit subcomplex left as a metavariable

*Provenance:* the generalization of the normal form to arbitrary subcomplexes; the boundary
corollaries `faceMap_comp_ι`, `bdCoord_faceMap` were stated as `subFaceMap_comp_ι _ e hns`.

*Error:* `Application type mismatch: hns has type ¬Surjective … but is expected to have type
faceSimplex e ∈ Subfunctor.obj ?m (op ⦋k⦌)`.

*Diagnosis:* the membership proof `hns` is definitionally correct only once the subcomplex is
known to be `∂Δ[r]`; with a metavariable in that position unification cannot see it.

*Repair:* made the subcomplex explicit in the two corollaries.

## F9. Namespace of `sSetChainComplexFunctor`

*Provenance:* `Task16Consequences.lean`, WP8 block.

*Error:* `Unknown identifier 'SpineTask13.sSetChainComplexFunctor.map'`, then
`Unknown identifier 'SpineTask15.skeletalInduction'`.

*Diagnosis:* the chain-complex functor lives in `SpineTask14` (`Task14RelativeChains.lean`), and
`Task15BaseCase` was not imported.

*Repair:* corrected the namespace and added the missing import.

---

## Routes considered and rejected (no build attempted)

* **Coend / quotient presentation of `|A|`** (WP13 Route C).  Rejected once it became clear that
  only the *surjectivity* half of the colimit presentation is needed: the identifications used
  in the normal form are all instances of functoriality of the realization, so no equality
  criterion for the quotient is required.  This is why the pin's lack of a quotient model was
  not, in the end, a blocker.
* **A junk-valued retraction `|Δ[r]| → |∂Δ[r]|`** (an alternative to the uniqueness argument).
  Rejected: it requires a dependent definition over the cardinality of the support and a
  base-point for the interior case, which fails at `r = 0`; the existential normal form plus
  `Finset.orderEmbOfFin_unique` is shorter and uniform in `r`.
* **A new Euclidean model of geometric realization.**  Explicitly forbidden by the task, and
  unnecessary: `coord` is derived from the pin's `SSet.toTopSimplex`.
