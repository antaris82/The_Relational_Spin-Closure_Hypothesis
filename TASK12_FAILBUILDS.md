# Task 12 — failbuild ledger (append-only)

Every compilation failure encountered while producing
`RequestProject/Spine/Nerve/Task12Probe.lean`, in the order in which it occurred, with the
diagnostic, the cause, the repair, and whether the repair changed a *statement* or only a
*proof*. **No statement was ever weakened**: every repair below is a proof-term or
formulation-of-scaffolding change, and the four decisive statements (freeness of `F`,
non-freeness of `G`, acyclicity of `F` on `Δ[n]`, non-acyclicity of `∂Δ[2]`) are the ones
originally planned.

Entries 1–7 occurred in scratch elaboration probes; entry 8 is the one failure of
`lake build` on the project file.

---

### 1. Instance synthesis for `Finite (Δ[1] ⟶ Δ[1])`

* Command: scratch elaboration, `example : Finite (Δ[1] ⟶ Δ[1]) := by infer_instance`.
* Diagnostic: `failed to synthesize instance of type class Finite (Δ[1] ⟶ Δ[1])`.
* Cause: there is no instance on the hom-type of simplicial sets; finiteness has to be
  transported along Yoneda.
* Repair: `Finite.of_equiv _ SSet.yonedaEquiv.symm`, used inside
  `singularGenerator_not_surjective`.
* Classification: proof-only.

### 2. Deprecated `SimplexCategory.toTopObj`

* Command: scratch `#check @SimplexCategory.toTopObj`.
* Diagnostic: `` `SimplexCategory.toTopObj` has been deprecated: Use `SimplexCategory.toTop₀`
  instead ``.
* Cause: upstream rename inside the pin.
* Repair: use `SimplexCategory.toTop` / `toTop₀` and `SSet.toTopSimplex`.
* Classification: proof-only (API rename applied as instructed by the deprecation).

### 3. Universe inference for `SSet.toTopSimplex.app`

* Command: scratch `have := SSet.toTopSimplex.app ⦋1⦌`.
* Diagnostic: `failed to infer universe levels in 'have' declaration type`.
* Cause: `SSet.toTop`, `SSet.stdSimplex` and `SimplexCategory.toTop` are universe-polymorphic and
  the universe is not determined by the statement.
* Repair: pin every statement of the module to universe `0` (`SSet.{0}`, `toTop.{0}`); the
  counterexample is a failure already at universe `0`, so no generality is lost.
* Classification: scaffolding; the affected statements are counterexamples, which are *weaker*
  when stated at a fixed universe, i.e. the change is conservative.

### 4. Degree bookkeeping in the cone face identity

* Command: scratch elaboration of `cone_face_succ`.
* Diagnostic: `Application type mismatch: f has type ⦋q⦌ ⟶ ⦋n⦌ but is expected to have type
  ⦋q + 1⦌ ⟶ ⦋?m⦌`.
* Cause: the identity `d_{i+1}(h σ) = h(d_i σ)` only makes sense for `q ≥ 1`; the statement had
  been written with the wrong degree offsets.
* Repair: state it for `f : ⦋p+1⦌ ⟶ ⦋n⦌` and `i : Fin (p+2)`.
* Classification: statement corrected before it was ever proved (the wrong version was
  ill-typed, not false).

### 5. Unknown constant `Fin.succAbove_succ_succ`

* Command: scratch elaboration of `cone_face_succ`.
* Diagnostic: `Unknown constant 'Fin.succAbove_succ_succ'`.
* Cause: guessed lemma name.
* Repair: the pinned names are `Fin.succ_succAbove_zero` and `Fin.succ_succAbove_succ`.
* Classification: proof-only.

### 6. `rw` pattern mismatch after inlining a rewrite

* Command: scratch elaboration of `cone_face_succ` with
  `rw [Fin.succ_succAbove_zero i, ...]`.
* Diagnostic: `Tactic 'rewrite' failed: Did not find an occurrence of the pattern
  i.succ.succAbove 0`.
* Cause: the goal displays `(δ i.succ).toOrderHom 0`, which is only *definitionally* the
  `succAbove` term.
* Repair: introduce the equation as a `have` with the goal's own spelling, then rewrite.
* Classification: proof-only.

### 7. `norm_num` leaves `2 = 0` in `ZMod 2`; `Submodule.mem_top` elaboration

* Commands: scratch elaboration of `boundary_fundamentalCycle` and of
  `surjective_of_span_singles`.
* Diagnostics: `unsolved goals ⊢ 2 = 0`; and
  `Type mismatch: hker Submodule.mem_top has type ?m ∈ (Finsupp.lapply s).ker but is expected to
  have type (fun₀ | s => 1) s = 0`.
* Causes: `norm_num` normalises `1 + 1` to `2` in `ZMod 2` and then stops; and the membership
  `x ∈ ker` needs to be unfolded with `LinearMap.mem_ker` before it can be used as an equation.
* Repairs: `rw [show (1 : ZMod 2) + 1 = 0 by decide, Finsupp.single_zero]`; and an explicit
  `have h2 : … ∈ LinearMap.ker … := hker Submodule.mem_top` followed by
  `rw [LinearMap.mem_ker] at h2`.
* Classification: proof-only.

### 8. `lake build` — contractibility of `|Δ[n]|`

* Command: `lake build` (project file `RequestProject/Spine/Nerve/Task12Probe.lean`).
* Diagnostics:
  * `RequestProject/Spine/Nerve/Task12Probe.lean:370:10: Unknown constant
    'stdSimplex.single_mem'`;
  * `RequestProject/Spine/Nerve/Task12Probe.lean:367:71: unsolved goals ⊢ ContractibleSpace
    ↑(SSet.toTop.obj Δ[n])`.
* Causes: the nonemptiness witness for the geometric simplex was guessed under a wrong name, and
  the two `ContractibleSpace` facts were introduced with `have` instead of `haveI`, so instance
  resolution could not use them when transporting along the homeomorphism.
* Repair: `Set.nonempty_coe_sort.mp inferInstance` for nonemptiness; `haveI` for both
  intermediate instances; transport with `(realizationHomeo n).symm.contractibleSpace`.
* Classification: proof-only; the statement of `realization_stdSimplex_contractible` is unchanged.

---

After entry 8 the full `lake build` is green (8203 jobs), the firewall reports
`SPINE FIREWALL AUDIT: all checks passed`, and every declaration of the module reports axioms
`[propext, Classical.choice, Quot.sound]`.
