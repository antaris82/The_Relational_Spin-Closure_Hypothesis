# TASK 31 — Failbuild ledger

Every failed or aborted build of this task, in order.  Nothing is erased.

---

## F0 — aborted whole-project build (tooling, not a code failure)

* **Command:** `lake build` (all default targets), issued immediately after creating
  `RequestProject/Spine/SpinNative/KernelTwist.lean`.
* **Symptom:** the invocation exceeded the 30-minute wrapper timeout while
  `RequestProject/Spine/Audit/Firewall.lean` was still elaborating (that single audit module
  takes ≈ 140 s and several GB on its own, after the 8000-job project replay).
* **Diagnostic cause:** not a compilation error — the target module had in fact already been
  built successfully (`.lake/build/lib/lean/RequestProject/Spine/SpinNative/KernelTwist.olean`
  present).  The whole-project target was simply the wrong granularity for iteration.
* **Repair:** build the specific module under work
  (`lake build RequestProject.Spine.SpinNative.Rigidity`, etc.), and run the whole-project
  target only for the final validation.
* Theorem statement changed: **no**.  Assumption strengthened: **no**.  Architecture changed:
  **no**.

---

## F1 — `RequestProject.Spine.Comparison.KernelTwistCohomology`, first attempt

* **Command:** `lake build RequestProject.Spine.Comparison.KernelTwistCohomology`
* **Errors:** three, all in the same file.

  1. **`d_kerCocycleCochain`, the `hsum` step.**  After
     `rw [Fin.sum_univ_three, hσ, face_nerve₂_zero …]` the rewrite of
     `hσ : σ = nerve₂ 𝓤 (σ.idx 0) (σ.idx 1) (σ.idx 2) ⟨x, hx⟩` also rewrote the *indices*
     `σ.idx 0/1/2` occurring on the right-hand side of the `have`, producing the unusable
     goal `… S.sgn (ε.e ((nerve₂ 𝓤 (σ.idx 0) …).idx 0) …)`.
     *Cause:* the statement being rewritten mentioned `σ` both as a nerve simplex and through
     its index tuple, so the rewrite was not confined to the simplex occurrence.
     *Repair:* replace the `have hσ … ; rw [hσ]` pattern by an `obtain` that introduces the
     three indices as *fresh variables* and substitutes `σ` outright:
     `obtain ⟨i, j, k, h₃, rfl⟩ : ∃ i j k, ∃ h : (𝓤.overlap₃ i j k).Nonempty,
      σ = nerve₂ 𝓤 i j k h`, then `obtain ⟨x, hx⟩ := h₃` (legitimate: the goal is a `Prop`).

  2. **line 136, `Unknown identifier hx`.**  The auxiliary statement had been written as
     `∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, d 𝓤.U 0 b (nerve₁ 𝓤 i j ⟨x, hx⟩) = …`; the binder
     notation `∀ x ∈ s, …` does not name the membership proof, which the term
     `nerve₁ 𝓤 i j ⟨x, hx⟩` needs.
     *Repair:* spell the binder out: `∀ (i j : ι) (x : X) (hx : x ∈ 𝓤.overlap₂ i j), …`.

  3. **the kernel-valuedness goal of the constructed 0-cochain.**  `rw [dif_pos ⟨x, hx⟩]`
     failed with *"Did not find an occurrence of the pattern `dite …`"*: the goal was the
     un-beta-reduced application `(fun i x => if h : … then … else 1) i x ∈ P.Ker`.
     *Repair:* precede the rewrite with an explicit `show` of the beta-reduced statement (and
     likewise for the main equation, where the anonymous constructor could then not infer its
     expected type).
* **Repair verified:** rebuilt successfully (18 s).
* Theorem statement changed: **no** (only proof scripts and one binder spelling).  Assumption
  strengthened: **no**.  Architecture changed: **no**.

---

## F2 — stale audit artifact after the final `#print axioms` additions

* **Command:** `lake --rehash --no-build build RequestProject` (freshness check after the
  clean build).
* **Symptom:** `✖ Building RequestProject.Spine.Audit.ArchitectureDAG — target is
  out-of-date and needs to be rebuilt`.
* **Diagnostic cause:** not a code error.  The `#print axioms` blocks were appended to
  `Comparison/LorentzSpinUniqueness.lean` and `Controls/SpinNative/KernelTwistControl.lean`
  *after* the clean whole-project build; `ArchitectureDAG` imports both, so its artifact was
  stale.
* **Repair:** re-run `lake build RequestProject`; it completed successfully (8300 jobs, all
  audits passing) and the freshness check then reported `All targets up-to-date`.
* Theorem statement changed: **no**.  Assumption strengthened: **no**.  Architecture changed:
  **no**.

---

## Warnings fixed (no build failure)

* `RequestProject/Spine/SpinNative/KernelTwist.lean:75,134` — unused binders `i j` / `i` in
  the two `isKer` fields of the trivial cocycle/cochain; replaced by `_`.
* `RequestProject/Spine/SpinNative/Canonical.lean:80` — unused binder `x` in
  `SpinStructureOver.exists_twist`; replaced by `_`.
* `RequestProject/Spine/Controls/SpinNative/KernelTwistControl.lean:77` — the section
  variable `[IsTopologicalGroup L]` was unused in `nullGluing_g`; `omit … in` added.
* `RequestProject/Spine/Cech/CoverNerve.lean:180,186` — `fin_cases u <;> rfl` on a `Fin 1`
  index flagged by the `unnecessarySeqFocus` linter; split into `fin_cases u` / `rfl`.

No linter was disabled anywhere; every warning was fixed at its root.

---

## Summary

Three build incidents in total: one tooling-granularity abort (F0), one genuine compilation
failure (F1) with three diagnostics, and one stale-artifact freshness failure (F2); all of them proof-script issues (rewrite scope, binder
naming, beta reduction).  **No theorem statement was weakened, no assumption strengthened and
no architectural boundary moved as a result of a build failure.**
