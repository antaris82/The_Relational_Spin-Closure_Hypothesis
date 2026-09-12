# Task 15 — failbuild ledger (append-only)

Format: *provenance* (what produced the failing build) / *diagnosis* (why it failed) /
*repair* (what fixed it) / *classification* — `NONE` = proof-only defect, no change to any
statement; `PRESENTATION` = tooling/typography defect; `STATEMENT` = a statement had to change.

No entry in this ledger required a statement change.  In particular no theorem was weakened,
no hypothesis was added to a target statement, and no definition was altered to make a proof go
through.

---

### F15-01 — `Task15Pushout.range_charTot_le`
* **Provenance.** First compile of `Task15Pushout.lean`.
* **Diagnosis.** After `rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff]` the goal
  was `SSet.yonedaEquiv (charTot X r σ) ∈ (X.skeleton (r+1)).obj _`, and the supplied term
  proved `σ.1 ∈ …`.  `yonedaEquiv (yonedaEquiv.symm σ.1) = σ.1` holds, but the elaborator will
  not see it through `∈` without a rewrite (a bare `show … ∈ _` left the `Membership` instance
  stuck on a metavariable).
* **Repair.** Extended the rewrite chain by `charTot, Equiv.apply_symm_apply`.
* **Classification.** `NONE`.

### F15-02 — unknown identifiers `mem_skeleton_of_not_epi`, `cellSimplex`
* **Provenance.** Same compile.
* **Diagnosis.** `Task15Pushout.lean` imported `Task14Blocker`, which reaches
  `Task14Comparison → Task14RelativeLES → Task14RelativeChains` but **not**
  `Task14SkeletalAttachment`; the Task-14 attachment layer is a sibling, not an ancestor.
* **Repair.** Added `import RequestProject.Spine.Nerve.Task14SkeletalAttachment`.
* **Classification.** `NONE`.

### F15-03 — `Sigma.map` resolves to the wrong constant
* **Provenance.** Same compile, definition `bdryMap`.
* **Diagnosis.** With `Simplicial`/`SSet` open, the bare name `Sigma.map` resolves to the
  dependent-pair function `Sigma.map`, not to `CategoryTheory.Limits.Sigma.map`.
* **Repair.** Wrote `Limits.Sigma.map`.
* **Classification.** `NONE`.

### F15-04 — `cellChar_yonedaEquiv` is not `rfl`
* **Provenance.** Same compile.
* **Diagnosis.** `yonedaEquiv (Subcomplex.lift f h)` unfolds to
  `⟨X.map (𝟙).op σ.1, _⟩`, which is only propositionally equal to `⟨σ.1, _⟩`
  (`FunctorToTypes.map_id_apply` is needed).
* **Repair.** `Subtype.ext` followed by an explicit `show` of the underlying value and `simp`.
* **Classification.** `NONE`.

### F15-05 — corrupted simplex-object brackets
* **Provenance.** A line-based edit of `Task15Pushout.lean` writing `op ⦋r⦌`.
* **Diagnosis.** The characters arrived in the file as U+2989/U+298A instead of the
  simplex-object brackets U+298B/U+298C, so the term parsed as an unknown identifier.
* **Repair.** Rewrote the term as `op (SimplexCategory.mk r)`, which is the same object without
  notation; subsequent edits containing the notation were made by whole-file rewrites.
* **Classification.** `PRESENTATION`.

### F15-06 — stuck metavariable in `FunctorToTypes.naturality`
* **Provenance.** `Task15Pushout.coconeAttachData`, `compat` field.
* **Diagnosis.** `(FunctorToTypes.naturality _ _ _ h.op (ULift.up (𝟙 _))).symm` left both the
  source functor and the universe of the `ULift` undetermined, producing
  `Application type mismatch: { down := 𝟙 ?m }`.
* **Repair.** Supplied the two functors, the natural transformation and the element explicitly,
  and rewrote with the separately proved `hx : Δ[r].map h.op (ULift.up (𝟙 ⦋r⦌)) = ULift.up h`.
* **Classification.** `NONE`.

### F15-07 — misassociated rewrite in `sigmaMap_injective`
* **Provenance.** `Task15RealizationMono.lean`, first compile.
* **Diagnosis.** After rewriting the left-hand side, the remaining right-hand side was
  `Sigma.ι f j ≫ ((coproductIso f).hom ≫ F)`, so the pattern
  `Sigma.ι _ _ ≫ (coproductIso _).hom` was not present.
* **Repair.** Inserted `← Category.assoc` before the second
  `Types.coproductIso_ι_comp_hom`.
* **Classification.** `NONE`.

### F15-08 — three defects in the first compile of `Task15BaseCase.lean`
* **Provenance.** `singSkZero_isEmpty`, `isZero_chain_of_isEmpty`, `baseCase`.
* **Diagnosis.**
  1. `g.down` is a `TopCat` morphism (bundled `TopCat.Hom`), not a function, so `g.down p` was
     rejected;
  2. `ModuleCat.isZero_of_subsingleton` takes the `Subsingleton` instance as an instance
     argument, so it cannot be discharged by a goal produced *after* `refine`;
  3. the constant is `HomologicalComplex.Hom.isIso_of_components`, not
     `HomologicalComplex.isIso_of_components`, and it takes the componentwise isomorphisms as an
     instance argument.
* **Repair.** `(forget TopCat).map g.down p`; a `haveI : Subsingleton …` established before the
  call, via `Finsupp.ext`; `haveI hcomp : ∀ i, IsIso …` before
  `HomologicalComplex.Hom.isIso_of_components`, with the final `IsIso` on homology obtained from
  `HomologicalComplex.homologyMapIso (asIso …)`.
* **Classification.** `NONE`.
