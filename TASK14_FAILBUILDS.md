# TASK14_FAILBUILDS.md — append-only failbuild ledger for Task 14

Every failed build during Task 14, in order. Command in all cases is
`lake build <module>` (or `lake build`) from the project root, in the pinned environment
(Lean v4.28.0, Mathlib pinned in `lake-manifest.json`).

Classification of "mathematical-statement change":

* `NONE` — proof-script repair only, statement unchanged;
* `PRESENTATION` — the statement was rephrased with the same mathematical content;
* `WEAKENED` / `STRENGTHENED` — real change of content.

---

## F1 — `RequestProject.Spine.Nerve.Task14RelativeChains`

* **Diagnostic (representative).**
  `relProj` : `'show' tactic failed, pattern` at the naturality square;
  `relSC` and `relChainCxMap_relProj` : `HomologicalComplex.hom_ext … funext …` application
  type mismatch (`∀ i, …` expected, `_ = _` given);
  `relSC_shortExact` : `ModuleCat.mono_iff_injective` — argument `hinj` has the wrong
  `ConcreteCategory.hom` form; the three `ShortExact` fields were produced by `refine` in an
  order the bullets did not match;
  `relChainCxMap` : `simpa … using this.symm` produced the transposed equation;
  `subcomplex_homOfLE_injective` : `congrArg Subtype.val hst` elaborated at the wrong type.
* **Cause.** (i) the `comm'` field of a `HomologicalComplex.Hom` is oriented
  `f.f i ≫ d = d ≫ f.f j`, the opposite of what the `show` assumed; (ii) `hom_ext` takes a
  pointwise family, not a `funext`; (iii) `ModuleCat` morphisms carry a `ConcreteCategory.hom`
  wrapper that blocks unification with a bare `LinearMap`; (iv) `Finsupp.mapDomain_comp`
  orientation.
* **Repair.** Swapped the `show`; replaced `funext fun q => _` by `fun q => _`; introduced the
  `Mono`/`Epi` witnesses as separate `have`s with their full expected types; replaced the
  `simpa` by an explicit `show` + `Finsupp.mapDomain_comp` rewrite; annotated the coercion
  function in `congrArg`.
* **Statement change.** `NONE`.
* **Source theorem involved.** None (pure API friction).

## F2 — `RequestProject.Spine.Nerve.Task14RelativeChains` (second pass)

* **Diagnostic.** `typeclass instance problem is stuck — Module ?m (SSetChain T' j)` inside
  `relChainCxMap.comm'`.
* **Cause.** `Submodule.Quotient.mk` in a `show` with the submodule left implicit.
* **Repair.** Replaced the `show`+`rw` by
  `refine congrArg (Submodule.Quotient.mk (p := LinearMap.range (sSetChainMap f' j))) ?_`.
* **Statement change.** `NONE`.

## F3 — `RequestProject.Spine.Nerve.Task14RelativeLES`

* **Diagnostic.** `relSCMap.comm₁₂` : `rewrite failed … sSetChainComplexFunctor.map ?f ≫ …`;
  `epi_homologyMap_τ₂` : `simpa using hi` gave `i = 0` instead of `∀ j, ¬ j+1 = i`, and the
  `▸` used to coerce a `mapShortComplex` morphism was not an equality.
* **Cause.** the `ShortComplex` field `f` is not syntactically the functor image; and the
  short-complex four lemma needed the `ComposableArrows`-valued form, not the
  `mapShortComplex` form.
* **Repair.** Added an explicit `show` for `comm₁₂`; replaced the `▸` by the pinned
  `Abelian.epi_of_epi_of_epi_of_epi` applied to
  `HomologicalComplex.HomologySequence.mapComposableArrows₂`, with
  `composableArrows₂_exact` as the exactness input; replaced `simpa using hi` by
  `fun j hij => hi ⟨j, hij⟩`.
* **Statement change.** `NONE`.
* **Source theorem involved.** `CategoryTheory.Abelian.epi_of_epi_of_epi_of_epi`
  (`Mathlib/CategoryTheory/Abelian/DiagramLemmas/Four.lean`).

## F4 — `RequestProject.Spine.Nerve.Task14SkeletalAttachment` (universal property)

* **Diagnostic.** `Unknown constant 'Opposite.rec''` (twice); unsolved goal
  `↑(cellSimplex σ) = ↑σ` in `attachExtend_cell`.
* **Cause.** the pinned `Opposite` API does not expose `rec'` under that name; and `rw` did not
  close the residual `Subtype` coercion goal.
* **Repair.** `obtain ⟨Δ⟩ := m` instead of the eliminator; `simp [cellSimplex]` for the
  coercion goal.
* **Statement change.** `NONE`.

## F5 — `RequestProject.Spine.Nerve.Task14SkeletalAttachment` (uniqueness)

* **Diagnostic.** `rewrite failed … attachFun D n x` not found in
  `ψ.app (op ⦋n⦌) x = (attachExtend D).app (op ⦋n⦌) x`.
* **Cause.** `(attachExtend D).app` is definitionally but not syntactically `attachFun`.
* **Repair.** Inserted `show ψ.app (op ⦋n⦌) x = attachFun D n x`.
* **Statement change.** `NONE`.

## F6 — `RequestProject.Spine.Nerve.Task14Controls`

* **Diagnostic.** `Subtype.ext (SimplexCategory.eq_id_of_epi f)` — application type mismatch in
  `cellIndexTopEquiv.left_inv`.
* **Cause.** the `Sigma`/`Subtype` pair had to be destructed before the identity substitution.
* **Repair.** `have hfid : f = 𝟙 _ := SimplexCategory.eq_id_of_epi f; subst hfid; rfl`.
* **Statement change.** `NONE`.

## F7 — `RequestProject.Spine.Nerve.Task14Blocker`

* **Diagnostic.** `ModuleCat.of (ZMod 2) (ZMod 2)` — universe mismatch (`Type` vs `Type u`);
  `Function expected at Sk` (unknown identifier).
* **Cause.** the relative complex lives in `ModuleCat.{u}`, so the one-dimensional comparison
  object must be `ULift.{u} (ZMod 2)`; and `SpineTask13` was not opened.
* **Repair.** `ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))`; added `SpineTask13` to the `open`.
* **Statement change.** `PRESENTATION` — `StandardCellPairTop` compares with `ULift (ZMod 2)`
  rather than `ZMod 2`; the mathematical content (one-dimensional over `ℤ₂`) is unchanged.

---

**Final state.** `lake build` for every module listed in WP21 succeeds; see
`ARISTOTLE_SUMMARY.md` / the Task-14 section of `TASK14_SPECIALIZED_CELL_ATTACHMENT.md` for the
build and axiom evidence.
