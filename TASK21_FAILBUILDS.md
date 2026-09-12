# TASK 21 FAILBUILDS

Every failed elaboration/proof attempt of Task 21, with error, diagnosis and repair.
**No mathematical statement was weakened at any point**; in particular the all-degree theorem
was never replaced by a top-degree-only result, and the frozen `cellRelJ` was never replaced.

---

### F1 — `Task21Normalization.homotopyPToId_hom_naturality` (scratch)

* **Error.** `rewrite failed: Did not find an occurrence of the pattern
  f.app (op ⦋n⦌) ≫ (homotopyPToId Y q).hom n (n + 1)` after the unfolding `simp only`.
* **Diagnosis.** The unfolded successor case leaves `f.app _ ≫ 0 + f.app _ ≫ (… + …)`;
  the induction hypothesis only matches after the zero summands and the composition
  distribution have been simplified away.
* **Repair.** Added `dif_pos, zero_add, comp_add, add_comp` to the `simp only` set, so the goal
  is already distributed when `rw [ih]` fires.
* **Statement changed?** No.

### F2 — same declaration, `comp_zero` / `zero_comp` unknown

* **Error.** `Unknown identifier 'comp_zero'`, `Unknown identifier 'zero_comp'`.
* **Diagnosis.** These live in `CategoryTheory.Limits`, which was not opened in the scratch
  snippet.
* **Repair.** Opened `CategoryTheory.Limits` (they then turned out to be unnecessary and were
  dropped from the simp set).
* **Statement changed?** No.

### F3 — `single_mem_degen_of_surjective`, degree `0` case

* **Error.** `omega could not prove the goal` — the hypotheses still mentioned `⦋m + 1⦌.len`
  and `⦋r⦌.len`.
* **Diagnosis.** `Fintype.card_le_of_surjective` produces cardinalities of
  `Fin (⦋q⦌.len + 1)`; `Fintype.card_fin` alone does not reduce `⦋q⦌.len`.
* **Repair.** Added `SimplexCategory.len_mk` to the `simp only` set before `omega`.
* **Statement changed?** No.

### F4 — `single_mem_degen_of_surjective`, degeneracy rewrite

* **Error.** `rewrite failed: Did not find an occurrence of the pattern
  SimplexCategory.σ i ≫ θ'` in `s = objEquiv.symm ((SimplexCategory.σ i).op.unop ≫ θ')`.
* **Diagnosis.** `stdSimplex.map_apply` leaves the morphism in the form `f.op.unop`.
* **Repair.** Inserted `simp only [Quiver.Hom.unop_op]` before the rewrite.
* **Statement changed?** No.

### F5 — `isZero_simpRel_homology`, positive degree

* **Error.** `rewrite failed: Did not find an occurrence of the pattern
  (normHtpy Δ[r] m) ((sSetBoundary Δ[r] m) x)` — after `rw [hhw]` the term had already been
  replaced, so the second rewrite had nothing left to act on.
* **Diagnosis.** The intended computation is a characteristic-two identity
  (`∂h x = x + (P∞ x + h ∂x)`), not a sequence of rewrites: the homotopy identity has to be
  moved across the equation with `a + a = 0` before matching.
* **Repair.** Replaced the rewrite chain by an explicit `calc` deriving
  `∂ (h x) = x + (P∞ x + h (∂ x))` from `normHtpy_succ` and `SpineTask13.z2_add_self_gen`, then
  a single `rw [map_add, hy, ← hhw, key]; abel`.
* **Statement changed?** No.

### F6 — `exists_smul_relTop`, identification of the surjective top simplex

* **Error.** `rewrite failed: Did not find an occurrence of the pattern (Equiv.symm ?e) (?e ?x)`
  in a goal that visibly contained it (implicit-argument mismatch in
  `stdSimplex.objEquiv`).
* **Diagnosis.** `congrArg` on the `Equiv` produced a term whose implicit `m`/`n` arguments did
  not unify syntactically with the `Equiv.symm_apply_apply` lemma instance.
* **Repair.** Used `stdSimplex.objEquiv.injective` directly:
  `objEquiv.injective ((SimplexCategory.eq_id_of_epi (objEquiv s)).trans rfl)`.
* **Statement changed?** No.

### F7 — `bijective_homologyMap_cellRelJ_top`, case split on `c : ZMod 2`

* **Error.** `Expected type must not contain free variables: c = 0 ∨ c = 1` (from
  `rcases (by decide : c = 0 ∨ c = 1)`).
* **Diagnosis.** `decide` cannot elaborate a proposition containing the local `c`.
* **Repair.** Proved `∀ a : ZMod 2, a = 0 ∨ a = 1` by `decide` and specialised it to `c`.
* **Statement changed?** No.

### F8 — quasi-isomorphism packaging

* **Error.** `Unknown constant 'ChainComplex.quasiIsoAt_iff_isIso_homologyMap'`.
* **Diagnosis.** In the pin the lemma is the unnamespaced `quasiIsoAt_iff_isIso_homologyMap`.
* **Repair.** Used the correct name.
* **Statement changed?** No.

### F9 — linter

* **Warning.** `try 'simp' instead of 'simpa'` in the zero case of `proj_mem_range`.
* **Repair.** Replaced by `rw [map_zero]; exact Submodule.zero_mem _`.
* **Statement changed?** No.
