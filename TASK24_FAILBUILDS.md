# TASK 24 FAILBUILD PROVENANCE

Every failed compilation encountered in Task 24, with the exact Lean error, the diagnosis, the
repair, and whether a theorem *statement* changed.  No failed route is silently discarded.

---

## F1 — inherited post-audit Task-23 module does not compile

* **Declaration/module**: `SpineTask23.exists_cellIncl`, `Spine/Nerve/Task23CellSum.lean:282`.
* **Error**
  ```
  error: don't know how to synthesize implicit argument `σ`
    @mem_openStdCell_of_cellPt X r ?m.127 x ?m.129
  ⊢ ↑(X.nonDegenerate r)
  ```
* **Diagnosis**: `mem_openStdCell_of_cellPt` has `{σ}` implicit, and the goal
  `x ∈ openStdCell r` does not mention `σ`; with `refine … ?_` the metavariable is not solved
  before the remaining goal is created.
* **Repair**: `refine mem_openStdCell_of_cellPt (σ := σ) X r ?_`.
* **Statement changed**: no.  Proof-only, one token.  This is the sole edit to inherited
  Task-23 material (recorded in `TASK24_AUDIT.md` §1.5).

---

## F2 — lifting the simplex bijection to free modules: `Finsupp.sum_single_index` unification

* **Declaration**: `SpineTask24.finsuppCxDesc` (field `comm'`).
* **Error**
  ```
  error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
    (fun₀ | ?m => ?m).sum DFunLike.coe
  ```
* **Diagnosis**: elaborating `rw [Finsupp.sum_single_index (map_zero _)]` fixes the implicit
  summand function `h` from `map_zero _` before the goal is inspected, producing the wrong
  pattern (`DFunLike.coe` instead of `fun a c => ((F a).f q).hom c`).
* **Repair**: the degreewise component was factored out as a separate definition
  `finsuppCxDescMap` with its own `exact`-provable generator lemma
  `finsuppCxDescMap_single := Finsupp.sum_single_index (map_zero _)`, which is then used by
  `rw`.  Same technique for `Finsupp.mapRange_single` (see F5).
* **Statement changed**: no (an auxiliary definition was added).

---

## F3 — chain differential compatibility: `Finsupp.mapRange_single` applied to an argument

* **Declarations**: `finsuppCxDesc.comm'`, `SpineTask24.mapRangeMk_single`,
  `SpineTask24.mapRangeStd_tgtDecomp`.
* **Error**
  ```
  error: Function expected at
    Finsupp.mapRange_single
  but this term has type
    (Finsupp.mapRange ?f ?hf fun₀ | ?a => ?b) = fun₀ | ?a => ?f ?b
  ```
* **Diagnosis**: in the pinned Mathlib `Finsupp.mapRange_single` takes *all* arguments
  implicitly (including `hf`), so `Finsupp.mapRange_single (map_zero _)` is an application of a
  proof to a term.  In addition, `Finsupp.mapRange.linearMap f` is not syntactically
  `Finsupp.mapRange f _`, so `rw` alone does not fire.
* **Repair**: precede the rewrite with
  `show Finsupp.mapRange _ (map_zero _) (Finsupp.single s c) = _` (the two are definitionally
  equal), then `rw [Finsupp.mapRange_single]`, closing with `rfl` where `Submodule.mkQ` has to
  be unfolded to `Submodule.Quotient.mk`.
* **Statement changed**: no.

---

## F4 — quotient descent / coordinate formula: `ModuleCat` carrier coercions block application

* **Declarations**: `famChainMap_apply` (first version), `injective_famChainMap_f`,
  `surjective_famChainMap_f`, `famRelChainMap_mapRange` (all first versions).
* **Errors**
  ```
  error: Function expected at
    (ModuleCat.Hom.hom ((famChainMap φ).f q)) d
  but this term has type
    ↑((sSetChainComplexFunctor.obj T).X q)
  ```
  and
  ```
  error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
    (d s) x
  in the target expression
    (d s) x = (d' s) x
  ```
* **Diagnosis**: `((F).f q).hom d` has type `↑(K.X q)`, which is only *definitionally* a
  `Finsupp`; it cannot be applied as a function, and a type ascription does not change the
  recorded type of the application.  The second error is the same phenomenon one level down:
  the `FunLike` instance path differs between `d : α →₀ SSetChain S q` and
  `d : ↑((finsuppCx α _).X q)`, so the two occurrences of `d s x` are not syntactically equal
  and `rw` fails.
* **Repair**: every degreewise statement was restated for an explicitly typed linear map
  (`famChainMapDeg`, `famRelChainMapDeg`, `mapRangeMk`), with the bridging equalities
  `famChainMap_f_hom : ⇑((famChainMap φ).f q).hom = ⇑(famChainMapDeg φ q) := rfl` and
  `famRelChainMap_f_hom` (both `rfl`), transferring bijectivity by `rw [famChainMap_f_hom]`.
  This is the pattern already used in `Task22RelJCompatibility.isIso_sumCellRelJ`.
* **Statement changed**: yes for the *auxiliary* lemmas — they are now stated for the
  degreewise linear maps rather than for the `ModuleCat` morphisms.  No principal statement
  (Θ_abs, Θ_rel, WP4, WP6, WP7, WP8) changed.

---

## F5 — `Finsupp` extensionality/induction: implicit index type not inferable

* **Declaration**: `SpineTask24.mapRangeMk_surjective`.
* **Error**
  ```
  error: don't know how to synthesize implicit argument `β`
    @Function.Surjective (?m q →₀ SSetChain S q) (?m q →₀ RelChainMod f q) ⇑(mapRangeMk f q)
  ```
* **Diagnosis**: `mapRangeMk` carries the index type `α` as a section-variable implicit that
  occurs only inside the `Finsupp` types of the statement, so it cannot be solved.
* **Repair**: state the theorem as `Function.Surjective (mapRangeMk (α := α) f q)`.
* **Statement changed**: no (only the elaboration annotation).

---

## F6 — coordinate formula: invalid `▸`

* **Declaration**: `SpineTask24.famChainMapDeg_apply`.
* **Error**
  ```
  error: invalid `▸` notation, expected result type of cast is
    s ∈ d.support
  however, the equality
    congrArg Prod.fst (hinj q hy)
  of type
    (a, y).1 = (s, x).1
  does not contain the expected result type on either the left or the right hand side
  ```
* **Diagnosis**: the equality `(a, y).1 = (s, x).1` is not reduced to `a = s`, so `▸` cannot
  locate the motive.
* **Repair**: `have has : a = s := congrArg Prod.fst (hinj q hy)` (which forces the reduction),
  then `exact hs (has ▸ ha)`.
* **Statement changed**: no.

---

## F7 — identifying the constructed map with `tgtDecomp`

* **Declaration**: `SpineTask24.mapRangeStd_tgtDecomp`.
* **Error**: unsolved goal after the failed `rw [show … from Finsupp.mapRange_single (map_zero _)]`
  (same root cause as F3):
  ```
  ⊢ (tgtDecomp X r q).hom ((mapRangeStd X r q).hom fun₀ | σ => m)
      = (cellPairIso X r q).hom.hom ((sumCellHomology X r q).hom fun₀ | σ => m)
  ```
* **Diagnosis**: only the `mapRangeStd`-on-a-generator step was missing; the identification
  itself (`cell_decomposition_square`) was already available.
* **Repair**: the generator computation was isolated as a `have hmr : … := by show …; rw […]`
  and the proof then closes with `tgtDecomp_single`, `sumCellHomology_single` and
  `cell_decomposition_square`.
* **Statement changed**: no.

---

## Routes considered and *not* taken (no failure, recorded for completeness)

* Building Θ_abs as a composite of `finsuppProdLEquiv` and `Finsupp.domLCongr` and *then*
  proving it is a chain map: rejected because the boundary compatibility would have to be
  proved by hand, whereas assembling the map from the functorially induced components
  (`sSetChainComplexFunctor.map`) makes it a chain map by construction.  Only the coordinate
  formula is then needed, and it is proved directly.
* Introducing a second finite direct-sum framework: explicitly avoided; `SpineTask23.finsuppCx`
  and `isIso_sumHomologyMap_of_iso` are used as they stand.
