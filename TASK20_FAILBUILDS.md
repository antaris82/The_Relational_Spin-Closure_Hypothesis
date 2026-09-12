# TASK 20 FAILBUILDS

Every failed build encountered while producing the Task-20 modules, in the order in
which they occurred.  **No mathematical statement changed in any of the repairs**: all
failures were elaboration/API issues, and the final statements are exactly the ones
targeted from the start.  Routes A/B never failed, so Route C (a new local excision
pair) was never entered.

---

## 1. `SpineTask20.bdFaceSimp_eq` (`Task20FaceMaps.lean`)

* **Error**: `rfl` / `show` failed — "The left-hand side is not definitionally equal to
  the right-hand side" when identifying the singular simplex `bdFaceSimp m i` with the
  image of the top simplex under the adjunction unit composed with the realized face
  map.
* **Diagnosis**: the two sides differ by the unrolled naturality square of
  `sSetTopAdj.unit`; the components are propositionally but not syntactically equal
  because `Subcomplex.toPresheaf` objects elaborate to an anonymous structure literal.
* **Repair**: prove the identification by rewriting with the naturality of the unit
  applied to the explicit face inclusion, instead of `rfl`.
* **Statement changed**: no.

## 2. `SpineTask20.bdCoord_bdFaceTop_succ` (`Task20FaceMaps.lean`)

* **Error**: `Finset.sum_filter`-based rewriting failed with a decidability instance
  mismatch (`Classical.propDecidable` vs the inferred `DecidableEq (Fin _)` instance).
* **Diagnosis**: `Finset.filter` carries its `Decidable` instance in the term; the
  instance produced by `simp` differed from the one in the goal.
* **Repair**: avoid `filter` entirely and evaluate the sum with
  `Finset.sum_eq_single_of_mem`.
* **Statement changed**: no.

## 3. `SpineTask20.bdFaceChain_add_single_zero` (`Task20CanonicalGenerator.lean`)

* **Error**: `motive is not type correct` when rewriting the definition of
  `bdFaceChain (n+1)` inside the goal.
* **Diagnosis**: the rewrite occurred under a dependent occurrence of the index `n+1`.
* **Repair**: isolate the purely algebraic content as the abstract lemma
  `add_add_self_cancel` over a `ZMod 2`-module and apply it, so no rewrite under a
  dependent motive is needed.
* **Statement changed**: no.

## 4. Support computation in `exists_chainU` / `exists_chainV`

* **Error**: `Finsupp.support_sum` application failed (argument/implicit-name
  mismatch at the pin), and the subsequent membership goal could not be discharged.
* **Diagnosis**: the pinned signature of `Finsupp.support_sum` does not fit the
  submodule-membership goal being produced.
* **Repair**: replace the support computation by `Submodule.sum_mem` applied
  termwise, using `carrier_bdFaceSimp_subset_Uset` / `..._Vset`.
* **Statement changed**: no.

## 5. `Functor.map_id` ambiguity (`Task20Cover.lean`)

* **Error**: `unknown identifier 'Functor.map_id'` / ambiguous resolution inside the
  opened namespaces.
* **Diagnosis**: `Functor.map_id` resolves to the `_root_` monadic lemma under the
  open namespaces of the file.
* **Repair**: use the fully qualified `CategoryTheory.Functor.map_id`.
* **Statement changed**: no.

## 6. `Subtype.val` versus coercion (`Task20Coords.lean`)

* **Error**: `rw`/`exact` failures with "pattern not found" between `x.val i` and
  `(x : Fin _ → ℝ) i` in `stdSimplex`.
* **Diagnosis**: `stdSimplex` membership uses a coercion that is reducible but not
  syntactically `Subtype.val` in every occurrence.
* **Repair**: add the extensionality helper `stdSimplex_ext` and route all pointwise
  arguments through it.
* **Statement changed**: no.

## 7. Implicitness of `n` in `coordRetr`

* **Error**: after making the dimension argument of `coordRetr` implicit,
  `Task20Cover.lean` failed with "function expected"/too many arguments.
* **Diagnosis**: call sites still supplied the explicit `n`.
* **Repair**: drop the explicit argument at the call sites.
* **Statement changed**: no.

## 8. `SpineTask20.cellRelJ` (optional §6 corollary)

* **Error**:
  ```
  Application type mismatch: the argument
    Eq.symm (sSetTopAdj.unit.naturality ?m)
  has type
    unit.app ?X ≫ (toTop ⋙ TopCat.toSSet).map ?f = (𝟭 SSet).map ?f ≫ unit.app ?Y
  but is expected to have type
    ∂Δ[r].ι ≫ unit.app (yoneda ^⦋r⦌ …) = unit.app { obj := … } ≫ stdCellPair r
  ```
* **Diagnosis**: two problems at once — the commuting square required by
  `relChainCxMap` is the naturality square in the *unsymmetrised* direction, and with
  the map argument left as `_` the unifier could not solve for it against the
  anonymous `Subcomplex.toPresheaf` structure literal.
* **Repair**: drop the `.symm` and pass the boundary inclusion
  `(∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι` explicitly to
  `sSetTopAdj.unit.naturality`.
* **Statement changed**: no.

---

## Route changes

None.  Route A/B (compare the explicit face-sum cycle with `bdFundClass`, using only
the already existing Task-18 excision isomorphism and Task-19 one-dimensionality) went
through, so Route C was never required and no new local excision pair was introduced.
