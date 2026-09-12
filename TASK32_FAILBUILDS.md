# TASK 32 — failed-build ledger

Every failed build during Task 32 is recorded.  None of them changed a theorem statement in a
mathematically weakening way, none changed an assumption, and none exposed a missing
mathematical datum beyond the one Task 32 set out to find (the base-gluing primitive, which
was identified before any code was written and is proved to be irreducible in
`Emergent/NonDerivability.lean`).

---

## F1 — `Spine/Emergent/Reconstruction.lean`: name clash with the structure constructor

* **Command** `lake build RequestProject.Spine.Emergent.Reconstruction`
* **Error** `error: … `EmergentBase.BaseGluingData.mk` has already been declared`, followed by
  ~20 cascading `Invalid field notation: Function `mk` does not have a usable parameter of
  type `BaseGluingData …``
* **Diagnosis** the quotient map was called `BaseGluingData.mk`, which is the name Lean
  generates for the structure constructor of `BaseGluingData`.
* **Repair** renamed the quotient map to `BaseGluingData.quotMk` (the derived lemma names
  `mk_eq_mk_iff`, `mk_surjective`, `continuous_mk`, `isOpenMap_mk` were kept).
* statement changed? no · assumptions changed? no · architecture changed? no · missing
  mathematical datum? no.

## F2 — same file: unresolved namespace and computability

* **Errors** `Unknown constant `TopologicalSpace.SecondCountableTopology``;
  `failed to compile definition … depends on `Topology.IsEmbedding.toHomeomorph`, which is
  `noncomputable``; `… depends on `Quotient.out`, which has no executable code`.
* **Diagnosis** `SecondCountableTopology` lives in the root namespace in this Mathlib
  revision, and the chart homeomorphism / charted-space construction uses choice.
* **Repair** dropped the `TopologicalSpace.` prefix; wrapped the module in
  `noncomputable section`.
* statement changed? no · assumptions changed? no · architecture changed? no.

## F3 — same file: rewriting under `Set.mem_preimage`

* **Error** `Tactic `rewrite` failed: Did not find an occurrence of the pattern` at
  `rw [Set.mem_preimage, hφ]` inside the proof of `isOpenMap_mk`.
* **Diagnosis** the goal had already been reduced to a plain membership by the preceding
  `simp only`, so `Set.mem_preimage` had nothing to rewrite.
* **Repair** `rw [hφ]`.
* statement changed? no · assumptions changed? no · architecture changed? no.

## F4 — `Spine/Cech/FullNerve.lean`: orientation of the characteristic-two identity

* **Error** `Application type mismatch … has type `↑z σ + ↑z ⟨![i₀, b]⟩ + ↑z ⟨![i₀, a]⟩ = 0`
  but is expected to have type `↑z σ + ↑z ⟨![i₀, a]⟩ + ↑z ⟨![i₀, b]⟩ = 0``
* **Diagnosis** the auxiliary `decide`-proved `ZMod 2` identity was stated with the summands
  in the wrong order relative to the Čech face ordering.
* **Repair** restated the auxiliary identity as `∀ A B C : ZMod 2, A + B + C = 0 → B + C = A`.
* statement changed? no (the theorem `cohomology_one_eq_zero_of_fullNerve` is unchanged) ·
  assumptions changed? no · architecture changed? no.

## F5 — `Spine/Emergent/Symmetric.lean`: three Mathlib API names

* **Errors** `Invalid field `isOpenMap_iff_continuous_symm``; two `Type mismatch` errors in a
  hand-built continuity proof; `Invalid field `Topology.IsInducing.preconnectedSpace``.
* **Diagnosis** guessed names: the equivalence-to-homeomorphism constructor is
  `Equiv.toHomeomorphOfContinuousOpen`; the continuity of `p ↦ (p.2 : V)` on a sigma type is
  `continuous_sigma`; there is no `IsInducing.preconnectedSpace` in this revision.
* **Repair** used `Equiv.toHomeomorphOfContinuousOpen`, `continuous_sigma`, and transported
  preconnectedness explicitly via `IsPreconnected.image` of `Set.univ`.
* statement changed? no · assumptions changed? no · architecture changed? no.

## F6 — `Spine/Emergent/CoverAdapter.lean`: stuck instance from binder order

* **Error** `typeclass instance problem is stuck: Nonempty ?m.20` (twice: once in a theorem
  signature, once in a `haveI :=` without an expected type).
* **Diagnosis** the section variable `ι` was not yet included when the `[Nonempty ι]` binder
  was elaborated; and `symmetricGluing.preconnectedSpace` determines `ι` only from its
  conclusion, so a bare `haveI :=` leaves it a metavariable.
* **Repair** gave the theorem its own explicit binders and annotated the `haveI` with its
  type.
* statement changed? no · assumptions changed? no · architecture changed? no.

## F7 — `Spine/Emergent/NonDerivability.lean`: three small proof-engineering errors

* **Errors** `unsolved goals … ⊢ Set.MapsTo (fun x => x) D D` and
  `⊢ Set.MapsTo (fun x => x) ∅ (if j = i then D else ∅)` (a `simp` that closed neither branch
  of the `if`); `Invalid argument name `i` for function `Set.mem_biUnion``;
  `Unknown constant `IsClopen.eq_empty_or_univ``; `Unknown constant `Set.not_mem_empty``.
* **Diagnosis** guessed lemma names and an over-optimistic `simp` in the `disjointGluing`
  construction.
* **Repair** discharged both `MapsTo` branches by hand, used `Set.mem_iUnion₂.2` and
  `isClopen_iff.1`.
* statement changed? no · assumptions changed? no · architecture changed? no.

## F8 — `Spine/Comparison/EmergentSpinGate.lean`: an unincluded section variable

* **Errors** `Application type mismatch … ∀ (i j : ?m.54) [Nonempty ?m.54], …` (consequence of
  F6's binder order in the adapter) and five `Unknown identifier `hD`` errors in the
  non-derivability endpoint.
* **Diagnosis** `hD : IsOpen D` was a section variable mentioned only in the *proof* of the
  endpoint (the statement quantified the two gluing data existentially), so Lean did not
  include it.
* **Repair** the adapter lemma was given explicit binders (F6), and the endpoint
  `spin_data_do_not_determine_base` was restated with the two witnesses **named explicitly**
  (`symmetricGluing Bool hD`, `disjointGluing Bool hD`) instead of existentially quantified.
* statement changed? **yes, and strengthened**: the existential
  `∃ A B, … ¬ Nonempty (Space A ≃ₜ Space B)` was replaced by the explicit instance naming the
  two data and additionally asserting that their local pieces coincide.  No assumption was
  added or removed · architecture changed? no · missing mathematical datum? no.

## F9 — abandoned refactor: removing `Classical.choose` from `isOpenMap_mk`

* **Command** `lake build RequestProject.Spine.Emergent.Reconstruction` (five attempts)
* **Errors** in sequence: `Application type mismatch … IsOpen (Sigma.mk ?m ⁻¹' T) … expected
  IsOpen (?m ⁻¹' T)`; `Type mismatch … IsOpen (Subtype.val '' (?m.70 ⁻¹' T)) … expected
  IsOpen (Subtype.val '' (?m.45 ⁻¹' T))`; `invalid binder name `B.D`, it must be atomic`;
  `Sigma.mk i has type ?m i → Sigma ?m but is expected to have type ↑(B.D i) → B.Total`;
  `typeclass instance problem is stuck`.
* **Diagnosis** the proof of `isOpenMap_mk` extracts, for each index `i`, an open set of the
  local model whose trace on the piece is the `i`-slice of the given open set; that extraction
  is `Classical.choose` applied to `isOpen_induced_iff`.  The intended replacement — pushing
  the slice forward along the open embedding `Subtype.val` instead of pulling an ambient open
  set back — is mathematically equivalent and choice-free, but the statement of the auxiliary
  `have` needs the sigma family of `BaseGluingData.Total` to be inferred, and Lean does not
  solve `Sigma ?m =?= B.Total` in that position; every combination of type ascriptions tried
  (ascribing `Sigma.mk i`, ascribing `Subtype.val`, replacing `Sigma.mk i` by an explicit
  lambda, and making `Total` an `abbrev`) failed on one of the errors above.
* **Repair** the refactor was abandoned and the original, building proof was restored
  (`git checkout`).  The remaining use of choice is *inside a proof of a `Prop`* and is
  recorded in `TASK32_AUDIT.md` §4; no definition of the layer depends on it.
* statement changed? no · assumptions changed? no · architecture changed? no · missing
  mathematical datum? no.
