# TASK 10 — failbuild ledger (append-only)

Every failing build of a Task-10 module, in order.  "Statement change" records whether the
repair altered a *statement* (as opposed to a proof); a `YES` there would require a separate
justification.

---

## F1

* **command** — `lake build RequestProject.Spine.Nerve.UnitChainMap`
* **diagnostic** —
  `RequestProject/Spine/Nerve/UnitChainMap.lean:83:6: Application type mismatch: The argument
  Eq.symm (congrFun (φ.naturality (δ i).op) σ) has type
  (φ.app _ ≫ T.map (δ i).op) σ = (S.map (δ i).op ≫ φ.app _) σ
  but is expected to have type
  φ.app _ (SimplicialObject.δ S i σ) = SimplicialObject.δ T i (φ.app _ σ)`
* **cause** — composition in `Type` reverses the reading order, so the naturality square
  already had the orientation needed; the extra `.symm` inverted it.
* **repair** — dropped `.symm` and introduced the naturality equation as a `have` before
  applying `congrArg`.
* **statement change** — NO (proof only).

## F2

* **command** — `lake build RequestProject.Spine.Nerve.Dualization`
* **diagnostic** — three issues in one run:
  1. `Dualization.lean:80:34: Tactic 'rewrite' failed: Did not find an occurrence of the
     pattern (Finsupp.linearCombination ?R ?v) fun₀ | ?a => ?c` in the `single` case of
     `linearCombination_dualOf`;
  2. `Dualization.lean:140:2: No goals to be solved` (a trailing `rfl` in
     `dualOf_singBoundary`);
  3. deprecation warning: `LinearMap.coeFn_sum` → `LinearMap.coe_sum`.
* **cause** — (1) the chained `rw [hs, map_smul, map_smul, …]` consumed the two `map_smul`
  rewrites on the left-hand side only, leaving `c • …` on the right unmatched; (2) `simp only`
  had already closed the goal; (3) upstream rename in the pinned Mathlib.
* **repair** — (1) split into `rw [hs]; simp only [map_smul]; congr 1; rw [...]`; (2) removed
  the trailing `rfl`; (3) switched to `LinearMap.coe_sum`.
* **statement change** — NO (proofs and one lemma name only).

## F3

* **command** — `lake build RequestProject.Spine.Nerve.ChainHomotopyComparison`
* **diagnostic** — three errors:
  1. `:62:2: Type mismatch — Eq.symm h has type 0 = x + x but is expected to have type
     x + x = 0` (in `z2_add_self`);
  2. `:257:14: rewrite failed: Did not find an occurrence of the pattern
     ↑c + (geometricCochainMap U).map (m+1) ((D.cochainInv (m+1)) ↑c)` (surjectivity, `succ`
     case);
  3. `:289:34: rewrite failed: Did not find an occurrence of the pattern
     ((underlyingPresimplicial (coverNerveSSet U)).d m) b` (injectivity, `succ` case).
* **cause** — (1) `two_smul` gave the equation in the already-correct orientation; (2) and (3)
  the rewrite direction (`h` versus `← h`) was inverted relative to the hypothesis actually
  produced by the dualised homotopy identity.
* **repair** — (1) `exact h`; (2) `rw [h, …]` instead of `rw [← h, …]`; (3) `rw […, ← hb] at h`
  and then `rw [map_add, h, add_assoc, z2_add_self, add_zero]`.
* **statement change** — NO (proofs only).

## F4

* **command** — `lake build RequestProject.Spine.Nerve.ChainHomotopyComparison`
* **diagnostic** — `:261:32: Tactic 'rewrite' failed: motive is not type correct` when
  rewriting with `z2_neg_eq_self` inside a cochain expression indexed by `m + 1`.
* **cause** — the rewritten subterm sits under a coercion from a degree-indexed subtype, so
  abstracting it produces an ill-typed motive.
* **repair** — introduced the top-level helper
  `z2_sub_eq_add : x - y = x + y` (proved once, abstractly) and rewrote with that instead.
* **statement change** — NO (a new abstract helper lemma; no existing statement altered).

## F5

* **command** — `lake build RequestProject.Spine.Nerve.ChainHomotopyComparison`
* **diagnostic** — `:261:33: Tactic 'rewrite' failed: motive is not type correct` for
  `add_comm`, which tried to unify the degree index `m + 1`.
* **cause** — `rw [add_comm]` abstracts over *all* occurrences, including the degree argument.
* **repair** — replaced by `exact add_comm _ _`.
* **statement change** — NO (proof only).

## F6

* **command** — `lake build RequestProject.Spine.Nerve.ManifoldAssumptionAudit`
* **diagnostic** — `:141:33: unused variable 'h'` (linter warning; build succeeded).
* **cause** — the discarded `Countable ℝ` hypothesis was bound to a name.
* **repair** — renamed to `_`.  The linter was not disabled and no `nolint` was added.
* **statement change** — NO.

---

No other Task-10 build failed.  The final state builds green:
`lake build` → `Build completed successfully (8201 jobs)`, firewall
`SPINE FIREWALL AUDIT: all checks passed`.
