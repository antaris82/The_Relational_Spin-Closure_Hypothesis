# Task 17 — failbuilds, with provenance, diagnosis and repair

Every failed elaboration encountered while building the Task-17 modules is recorded here.  All
of them were repaired; the final state of the project builds green
(`lake build RequestProject`, 8222 jobs) with no `sorry`, no `admit` and no new axiom.

| # | provenance | error | diagnosis | repair |
|---|---|---|---|---|
| F1 | scratch, before `Task17StandardCellTopology.lean` | `failed to synthesize TopologicalSpace (SpineTask16.Rz.obj A)` | `Rz.obj A` is `(forget TopCat).obj (SSet.toTop.obj A)`; it is *definitionally* the carrier `↥(SSet.toTop.obj A)` (checked by `rfl`) but instance search does not unfold it | state every topological claim with the carrier spelling `↥(SSet.toTop.obj A)`, coercing the Task-16 map with `show … from`; the two spellings are interchangeable by `rfl` |
| F2 | `contractibleSpace_realized_simplex` | `Unknown constant 'stdSimplex.vertex_mem'` | guessed name; in the pin `stdSimplex.vertex i` is already an element of the subtype | use `(stdSimplex.vertex (0 : Fin (n+1))).2` for the `Set.Nonempty` witness |
| F3 | `contractibleSpace_realized_simplex` | `failed to synthesize ContractibleSpace ↑(stdSimplex ℝ (Fin (⦋n⦌.len + 1)))` | `simplexHomeo ⦋n⦌` produces the index `⦋n⦌.len + 1`, not `n + 1`; the two are equal but not syntactically | prove the `have` at the `⦋n⦌.len` index after `simp only [len_mk]` |
| F4 | `continuous_subCover` | `failed to synthesize TopologicalSpace ((_ : topIdx A) × SpineTask16.Rz.obj Δ[r])` | same cause as F1, inside the sigma type occurring in the *type* of `subCover` | give `subCover` itself the carrier spelling in domain and codomain |
| F5 | scratch (`collapse`) | `omega could not prove the goal … ⦋k⦌.len` | `SimplexCategory.len ⦋k⦌` is not reduced by `omega` | insert `simp only [SimplexCategory.len_mk]` before `omega`, and bound the `Fin` value with `lt_of_le_of_lt (min_le_right _ _) (by simp)` |
| F6 | scratch (`collapse`, monotonicity) | `Type mismatch … a ≤ b ∨ ?m ≤ ↑b` | `simpa using min_le_min …` rewrote the goal into a disjunction before the term was checked | replace by `simp only [Fin.mk_le_mk]` followed by an explicit `exact min_le_min …` |
| F7 | scratch (`simplexGauge_smul`) | `Type mismatch: Eq.symm (mul_max_of_nonneg …)` and later `Tactic 'rfl' failed … Function.comp` | wrong orientation for `Finset.comp_sup'_eq_sup'_comp`, and the composed function is not syntactically the pointwise one | drop the `Eq.symm`; close the residual equality with `congrArg _ (funext …)` and `simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, mul_neg]` |
| F8 | scratch (`neg_le_sup'`) | `Function expected at le_sup' (fun i => -y i) ?m` | `Finset.le_sup'` takes the function explicitly and the membership proof next; an extra `_` was supplied | `Finset.le_sup' (fun i => -y i) (Finset.mem_univ i)` |
| F9 | `Task17BoundarySphere.lean` (`sumL_surjective`) | `failed to synthesize Fintype ℕ` / `'show' tactic failed` | the `show` re-elaborated `∑ i, …` with an unconstrained index type | give the witness in term mode and discharge with `simp [sumL]` |
| F10 | `Task17BoundarySphere.lean` (`finrank_hyper`) | `omega could not prove the goal` with `finrank ↥(hyper r)` and `finrank (Fin (r+1) → ℝ)` as separate atoms | `hyper r` and `LinearMap.ker (sumL r)` are distinct atoms for `omega`, and the pi-rank was not rewritten | rewrite with `finrank_top`, `Module.finrank_self`, `Module.finrank_pi`, then `show Module.finrank ℝ (LinearMap.ker (sumL r)) = r` before `omega` |
| F11 | `Task17BoundarySphere.lean` (`toHyper`) | `unsolved goals ⊢ 1 - 1 = 0` after `field_simp` | `field_simp` normalised the coefficient but left the trivial residue | append `norm_num` |
| F12 | `Task17BoundarySphere.lean` (`toHyper_ne_zero`) | `No goals to be solved` | `simp [simplexGauge]` already derived the contradiction; the following `linarith` was redundant | delete the redundant tactic |
| F13 | API search | `Function.Surjective.compactSpace` does not exist | guessed name | build the instance directly: `⟨by rw [← (surj).range_eq, ← Set.image_univ]; exact isCompact_univ.image cont⟩` |

No failbuild was worked around by weakening a statement, by adding a hypothesis, or by
introducing an axiom.
