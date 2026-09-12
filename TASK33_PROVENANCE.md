# TASK 33 — Smooth-manifold closure and canonicity hardening: provenance report

> ### Task-34 correction notice (added by Task 34; the Task-33 text below is preserved verbatim)
>
> Task 33 is mathematically passed and its statements stand.  Two forward-looking remarks are
> now out of date:
>
> 1. Task 33 recorded that nothing about `TM`, solder forms or frames was introduced.  That is
>    correct for Task 33; Task 34 has since built the tangent/solder layer
>    (`Emergent/TangentTransition.lean`, `Spine/Solder/**`,
>    `Comparison/SolderTangentGate.lean`), so the *current* state of the project is described
>    in `TASK34_PROVENANCE.md`.
> 2. The architecture firewall now has one more layer: `Spine.Audit.ArchitectureDAG` check 9
>    additionally covers `Emergent.TangentTransition`, and a new check 10 covers the
>    `Spine.Solder` branch and its single comparison join.
>
> Every `Ȟ¹` statement in this document remains a **fixed-cover Čech `Ȟ¹`** statement about
> the **specific symmetric full-overlap emergent cover**; it is not `H¹(M;ℤ₂) = 0`.


Environment: Lean `v4.28.0`, Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
(toolchain, manifest and Mathlib revision untouched).  No `sorry`, no `admit`, no new
`axiom`, no `native_decide`, no `unsafe`, no `partial`, no `implemented_by`.

**Outcome: A (full hardening), with two explicitly recorded non-claims.**

* `BaseGluingData.SmoothGluing` **is** sufficient: it implies Mathlib's `IsManifold` for the
  *actual* Task-32 reconstructed atlas (no substitute atlas, no second charted structure).
* The Task-32 topological candidate therefore crosses the smooth gate: under the already
  explicit conditions (closed gluing graph, countable index type) the emergent base is a
  Hausdorff, second-countable, smooth 4-manifold over the canonical Clifford/Lorentz local
  model.
* The symmetric sector now has a *genuine* canonicity statement: an intrinsic quotient
  coordinate, a distinguished homeomorphism, a named comparison map between presentations,
  and the identity/inverse/composition coherence laws — upgraded to the smooth category as a
  `Diffeomorph`.
* The Task-32 phrase "minimal missing primitive" is repaired: what is proved is that the
  *local-piece data* do not determine the base, i.e. the cross-piece incidence layer is
  irreducibly additional.  Nothing stronger is claimed.

The two recorded non-claims (Outcome-E components, see §5 below) are: the *converse* of the
smooth gate, and the separate necessity of each individual field of `BaseGluingData`.

---

## 1. Source/API audit (§3), answered from the code

**Q1 — what is `BaseGluingData.chartOfPoint` actually?**
`RequestProject/Spine/Emergent/Reconstruction.lean` defines it as

```
((B.isOpenEmbedding_chart i).toOpenPartialHomeomorph _).symm.trans
  (((B.isOpen_D i).isOpenEmbedding_subtypeVal).toOpenPartialHomeomorph _)
```

with `i = (Quotient.out p).1` and the `Nonempty` instance `⟨(Quotient.out p).2⟩`.  So the
chart at a point is the chart of the piece carried by the *representative chosen by the
quotient machinery*.

**Q2 — what is `atlas LocalModel (Space B)` for `B.chartedSpace`?**
`Set.range B.chartOfPoint`.  Hence a member of the atlas is *not* indexed by an index of the
primitive but by a point; the index is recovered through `Quotient.out`.

**Q3 — what must be proved for two atlas members `e, e'`?**
With `I = modelWithCornersSelf ℝ LocalModel` (so `I = id`, `range I = univ`),
`isManifold_of_contDiffOn` reduces the requirement to

```
ContDiffOn ℝ ⊤ ↑(e.symm ≫ₕ e') (e.symm ≫ₕ e').source .
```

**Q4 — what *is* `e.symm ≫ₕ e'` for the generated atlas?**
Proved in `RequestProject/Spine/Emergent/SmoothStructure.lean`:

* `BaseGluingData.chartOfPoint_eq_pieceChart` — every atlas member is `pieceChart i hne`
  for the index `i` of the selected representative (definitional equality, so the
  representative selection is fully accounted for, not assumed away);
* `BaseGluingData.pieceChart_source/target/apply/symm_apply` — `source = chartRange i`,
  `target = D i`, `pieceChart i (chart i x) = x`, `(pieceChart i).symm y = chart i ⟨y,·⟩`;
* `BaseGluingData.transition_source` — the source of `e.symm ≫ₕ e'` is **exactly** the
  incidence domain `W i j`;
* `BaseGluingData.transition_apply` — on that source the map is **exactly** `φ i j`.

So the coordinate changes of the actual generated atlas are the primitive maps `φ_ij`
restricted to the correct overlap — this is the bridge Task 32 lacked.

---

## 2. The smooth gate (§4)

`RequestProject/Spine/Emergent/SmoothStructure.lean`:

| declaration | content |
|---|---|
| `BaseGluingData.instChartedSpaceSpace` | the Task-32 `B.chartedSpace`, registered for instance resolution (same atlas, nothing new) |
| `BaseGluingData.contDiffOn_transition` | every coordinate change of the reconstructed atlas is `C^∞` |
| `BaseGluingData.isManifold_of_smoothGluing` | `B.SmoothGluing → IsManifold 𝓘(ℝ, LocalModel) ⊤ (Space B)` |
| `BaseGluingData.hasGroupoid_of_smoothGluing` | the `HasGroupoid` form of the same fact |

The route used is `isManifold_of_contDiffOn`; the `HasGroupoid` statement is derived from it
(`IsManifold` extends `HasGroupoid` in this Mathlib revision).

No new atlas is introduced anywhere: `pieceChart` is *definitionally* the Task-32
`chartOfPoint` with the index made explicit.

---

## 3. The full smooth certificate (§5)

`BaseGluingData.smoothEmergentManifoldCertificate` packages, for
`B : BaseGluingData LocalModel ι` with `[Countable ι]`, `B.ClosedGluingGraph`,
`B.SmoothGluing`:

```
T2Space (Space B) ∧ SecondCountableTopology (Space B) ∧
IsManifold 𝓘(ℝ, LocalModel) ⊤ (Space B) ∧
Module.finrank ℝ LocalModel = 4 ∧
(∀ i, IsOpen (B.chartRange i)) ∧ (⋃ i, B.chartRange i) = Set.univ
```

Hausdorffness and second countability are kept *outside* `IsManifold`, as Mathlib does.  The
Task-32 proofs (`t2Space_of_closedGluingGraph`, `secondCountableTopology_space`,
`finrank_localModel`) are reused, not reproved.

---

## 4. Canonicity of the symmetric sector (§6, §7)

`RequestProject/Spine/Emergent/SymmetricCanonical.lean`:

* `symmetricGluing.coordinate` — the intrinsic quotient coordinate `Space → D`, defined by
  descent along the gluing relation (`Quotient.lift`), **not** by choosing an index;
* `symmetricGluing.coordinate_chart`, `symmetricGluing.chart_coordinate` — two-sided inverse
  of every chart insertion;
* `symmetricGluing.chart_independent_of_index` — `chart i x = chart j x` for all `i, j`;
* `symmetricGluing.baseHomeomorph` — the distinguished homeomorphism `Space ≃ₜ D` whose
  forward map is the intrinsic coordinate.  Classical choice is used only to package the
  inverse, and `baseHomeomorph_symm_apply` proves the packaged inverse equals the chart of
  *every* index, so the result is choice-independent;
* `symmetricCanonicalHomeomorph` with `_refl`, `_symm`, `_trans` — the comparison of two
  presentations and its coherence laws;
* `symmetric_emergent_base_canonical` — the packaged statement.

`RequestProject/Spine/Emergent/SymmetricSmooth.lean` upgrades this to the smooth category
with no new assumption (the symmetric datum satisfies `SmoothGluing` by Task 32):

* `symmetricGluing.chartAt_apply` — in the symmetric sector *every* chart produced by the
  reconstruction is the intrinsic coordinate, whatever representative is selected;
* `contMDiff_symmetricCanonicalHomeomorph`, `symmetricCanonicalDiffeomorph` with the three
  coherence laws, and `symmetric_emergent_base_canonical_smooth`.

The Task-32 `symmetric_emergent_base_unique` (a `Nonempty` statement) is retained, with its
docstring corrected to say that it is *existence*, and with a pointer to the canonical
version.

---

## 5. Exactly what is *not* claimed

1. **No converse of the smooth gate.**  `SmoothGluing → IsManifold` is proved; the converse
   is not, and it is not true in the naive form: the reconstructed atlas is indexed by the
   representatives `Quotient.out` selects, so it need not contain the chart of every index.
   A datum with non-smooth `φ_ij` may therefore still have a smooth reconstructed atlas.
   This is stated in the module docstring.
2. **No field-by-field minimality of `BaseGluingData`.**  Proved (in
   `RequestProject/Spine/Emergent/LocalPieceData.lean`) is only that the reconstruction does
   not factor through the local-piece data.  The irreducibility of `φ` *given* `D` and `W`,
   and any universal/minimal property of the primitive, remain unproved and unclaimed.
3. **No `Space ≃ₘ D` statement.**  The smooth canonicity proved is the comparison of two
   presentations; identifying the emergent base with the subtype `D` in the smooth category
   would require fixing a charted structure on `D`, which is a conventional choice and is not
   needed for the canonicity question.
4. **No tangent/frame content.**  Nothing about `TM`, solder forms, frames, `w₁`, `w₂`,
   connections, curvature or field equations appears; the architecture audit mechanically
   forbids the emergence layer from importing the frame-geometry or Spin-obstruction
   branches.

---

## 6. Answers to the four stop-condition questions (§16)

1. **Does `SmoothGluing` imply Mathlib `IsManifold` for the Task-32 base?**  Yes —
   `BaseGluingData.isManifold_of_smoothGluing`, for the Task-32 charted space, via the
   proved identification of the coordinate changes with the `φ_ij`.
2. **Strongest correct canonicity for the symmetric base?**  A named, choice-independent
   intrinsic coordinate; a distinguished homeomorphism to `D`; a named comparison map
   between any two presentations satisfying `refl`/`symm`/`trans`; and the same comparison
   as a `Diffeomorph`.  Literal equality of the quotient carriers is false and is not
   claimed.
3. **What exactly is irreducibly additional?**  The cross-piece incidence/identification
   layer: `base_incidence_not_determined_by_local_piece_data` and
   `no_reconstruction_from_local_piece_data`.  Stronger minimality claims remain unproved and
   have been removed from the documentation.
4. **Are the H¹ and Spin non-derivability statements worded at theorem strength?**  Now yes:
   the `Ȟ¹ = 0` result is documented as a fixed-cover statement for the symmetric
   full-overlap emergent cover only, and the Spin statement is documented as *both transition
   laws are pointwise trivial* rather than "literally identical typed data".

---

## 7. Axiom audit

`#print axioms` is run on every new principal endpoint at the end of
`Spine/Emergent/SymmetricSmooth.lean` and `Spine/Emergent/LocalPieceData.lean`.  Every one
reports a subset of

```
propext, Classical.choice, Quot.sound
```

and no `sorryAx`.
