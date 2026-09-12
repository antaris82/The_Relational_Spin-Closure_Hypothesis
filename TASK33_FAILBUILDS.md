# TASK 33 — failed-build ledger

Every failed build during Task 33 is recorded.  None of them weakened a theorem statement,
none strengthened an assumption, and none changed the architecture.  (Task-32 and earlier
ledgers are untouched.)

---

## F1 — `Spine/Emergent/SmoothStructure.lean`: type ascription parsed as a binder

* **Command** `lake build RequestProject.Spine.Emergent.SmoothStructure`
* **Error** `RequestProject/Spine/Emergent/SmoothStructure.lean:105:25: invalid binder name
  `B.D`, it must be atomic` (and the same at 116:22, plus a follow-on
  `Invalid ⟨...⟩ notation: The expected type of this term could not be determined`).
* **Diagnosis** in `change (Subtype.val : (B.D i : Set V) → V) …` the parser reads
  `(B.D i : Set V) → V` as a *dependent function binder*, not as an ascribed type followed by
  an arrow.
* **Repair** wrote the subtype directly: `(Subtype.val : ↥(B.D i) → V)`, and ascribed the
  anonymous constructor `(⟨y, hy⟩ : ↥(B.D i))`.
* statement changed? no · assumptions changed? no · architecture changed? no.

## F2 — same file: `if`-defined transition maps are not definitionally reducible

* **Error** `302:0: Not a definitional equality: the left-hand side
  nonSmoothGluing.φ false true is not definitionally equal to the right-hand side absShift`,
  and the corresponding `Type mismatch: rfl`.
* **Diagnosis** the negative-control datum defined `φ i j := if i = j then id else …`; the
  `rfl` lemma for a concrete index pair then requires unfolding a `def` plus two
  `Decidable` instances, which `rfl` does not do here.
* **Repair** introduced the named pattern-matching function
  `EmergentBase.nonSmoothTransition : Bool → Bool → LocalModel → LocalModel` and used it as
  the `φ` field; the concrete-index lemmas are then `rfl`, and the coherence fields are
  proved by `cases i <;> cases j <;> …`.
* statement changed? no (the datum is new in Task 33) · assumptions changed? no ·
  architecture changed? no.

## F3 — same file: higher-order unification in `DifferentiableAt.comp`

* **Error** `Application type mismatch: the argument hline has type
  DifferentiableAt ℝ (fun t => (t, 0)) 0 but is expected to have type
  DifferentiableAt ℝ (Prod.mk 0) 0`.
* **Diagnosis** the base point `(fun t => (t,0)) 0` was beta-reduced before unification, and
  the elaborator solved `?f 0 ≡ (0,0)` with the wrong higher-order solution `?f := Prod.mk 0`.
* **Repair** supplied the composition data explicitly:
  `DifferentiableAt.comp (𝕜 := ℝ) (g := …) (f := …) 0 hg hf`.
* statement changed? no · assumptions changed? no · architecture changed? no.

## F4 — same file: wrong side condition for `ContDiffOn.differentiableOn`

* **Error** `mod_cast has type ?m ≤ ⊤ but is expected to have type ¬⊤ = 0`.
* **Diagnosis** in this Mathlib revision the hypothesis of `ContDiffOn.differentiableOn` is
  `n ≠ 0`, not `1 ≤ n`.
* **Repair** replaced `by exact_mod_cast le_top` with `by simp`.
* statement changed? no · assumptions changed? no · architecture changed? no.

## F5 — same file: `Space` not in scope in a section outside `namespace BaseGluingData`

* **Error** `Function expected at Space … The identifier `Space` is unknown` (with the
  `autoImplicit` hint).
* **Diagnosis** `Space` is `EmergentBase.BaseGluingData.Space`; the negative-control section
  sits outside that namespace.
* **Repair** added `open BaseGluingData` in that section.
* statement changed? no · assumptions changed? no · architecture changed? no.

## F6 — `Spine/Emergent/SymmetricCanonical.lean`: `simp` recursion in a coherence law

* **Error** `150:4: Tactic `simp` failed with a nested error: maximum recursion depth has
  been reached` (in `symmetricCanonicalHomeomorph_symm`).
* **Diagnosis** unfolding `Homeomorph.trans`/`Homeomorph.symm` with `simp` loops through the
  quotient coercions; the identity is in fact definitional.
* **Repair** replaced the `simp` proofs by `Homeomorph.ext fun _ => rfl` (inverse law) and by
  an explicit `congrArg … (Homeomorph.apply_symm_apply …)` (composition law).
* statement changed? no · assumptions changed? no · architecture changed? no.

## F7 — `Spine/Emergent/SymmetricSmooth.lean`: residual `D i = D` goal

* **Error** `78:41: unsolved goals ⊢ (symmetricGluing ι hD).D (Quotient.out x).fst = D`.
* **Diagnosis** `pieceChart_target` gives the target as `B.D i`; for the symmetric datum
  this is `D` definitionally but not syntactically.
* **Repair** appended `rfl`.
* statement changed? no · assumptions changed? no · architecture changed? no.

## F8 — linter-only failures

* `unusedSimpArgs` in `pieceChart_source`/`pieceChart_target`
  (`OpenPartialHomeomorph.trans_source/target` were already simp lemmas), `unnecessarySimpa`
  and one `unusedVariables` in the coherence laws.
* **Repair** removed the redundant simp arguments, replaced `simpa` by `simp only … ; exact`,
  renamed the unused binder to `_`.  No `set_option linter… false` was used anywhere.
* statement changed? no · assumptions changed? no · architecture changed? no.

---

## Non-build failure recorded for the record: the abandoned converse lemma

A first draft of `Spine/Emergent/SmoothStructure.lean` contained a planned converse

```
smoothGluing_of_isManifold : IsManifold … (Space B) → B.SmoothGluing
```

with `sorry` placeholders.  It was **removed before any build was accepted**, because the
statement is not provable as stated: the reconstructed atlas consists of the charts of the
indices that `Quotient.out` happens to select, so it can be smooth even when some `φ_ij`
between unselected indices is not.  Instead of weakening or forcing it, Task 33 records the
non-claim in the module docstring and supplies the honest negative control
`EmergentBase.not_smoothGluing_nonSmoothGluing`: an explicit datum over the local model whose
identification maps are homeomorphisms but not smooth, so `SmoothGluing` is a genuine extra
hypothesis and is never silently available.
