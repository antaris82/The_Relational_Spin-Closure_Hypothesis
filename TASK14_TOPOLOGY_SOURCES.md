# TASK14_TOPOLOGY_SOURCES.md — source ledger for Task 14

Access date for every item below: **2026-09-09**.
Pinned environment: Lean **v4.28.0**, Mathlib at the revision recorded in `lake-manifest.json`
(`rev = "v4.28.0"` in `lakefile.toml`).

Classification tags used: `NAKAHARA_PRIMARY_REFERENCE`, `OTHER_TEXTBOOK_REFERENCE`,
`MATHLIB_SOURCE`, `UPSTREAM_MATHLIB_REFERENCE`, `NATIVE_PROOF_ARCHITECTURE`,
`CONSISTENCY_CHECK_ONLY`, `NOT_USED`.

No proof text is copied from any source. Where a Lean proof follows a source's architecture,
that is stated explicitly; where it does not, that is stated too.

---

## 1. NAKAHARA_PRIMARY_REFERENCE

**M. Nakahara, *Geometry, Topology and Physics*, 2nd edition, Institute of Physics
Publishing, 2003.** Supplied with this project as `GTP.pdf`. PDF page numbers below are
positions in the supplied file (they coincide with the printed page numbers of Chapter 3).

| § | PDF page | item | role in Task 14 | used as |
| --- | --- | --- | --- | --- |
| 3.2 | 117 | opening of "Simplexes and simplicial complexes" | orientation only | `GEOMETRIC_GUIDE` |
| 3.2.1 | 117 | definition of an `r`-simplex `σ^r = ⟨p_0 … p_r⟩` as the convex hull (3.11), barycentric coordinates, `q`-faces | the geometric meaning of `Δ[r]` and of its boundary faces; the mental model behind `stdCellPair` | `DEFINITION_REFERENCE`, `GEOMETRIC_GUIDE` |
| 3.2.2 | 118–119 | simplicial complex; **polyhedron `\|K\|`**; triangulation; Example 3.4 (the faces of a 3-simplex); Example 3.5 (a triangulation of the cylinder) | fixes what "realization" means informally; used to sanity-check that `SSet.toTop` is the right object and that `∂Δ[r]` is "the faces of `Δ[r]`" | `DEFINITION_REFERENCE`, `GEOMETRIC_GUIDE` |
| 3.3.1 | 119–121 | oriented simplexes | not used: the project works over `ℤ₂`, where orientation is invisible (`-1 = 1`) | `NOT_USED` |
| 3.3.2 | 121–125 | chain group `C_r(K)`, boundary `∂_r`, cycles `Z_r`, boundaries `B_r`, `∂∘∂ = 0` | the informal counterpart of the project's `SSetChain`/`sSetBoundary`; consistency only — the Lean complex is the pinned `alternatingFaceMapComplex` of the free `ℤ₂`-simplicial module, proved equal to the project's boundary in Task 13 (`afmc_d_hom`) | `CONSISTENCY_CHECK` |
| 3.3.3 | 125–126 | Definition 3.5 (`H_r(K) = Z_r/B_r`, and `H_r(K;ℤ₂)`); Theorem 3.4 (topological invariance, stated *without proof* in the book) | Definition 3.5 licenses the `ℤ₂` coefficients used throughout; Theorem 3.4 is **not** used — the project never appeals to an unproved invariance statement | `DEFINITION_REFERENCE` (Def. 3.5); `NOT_USED` (Thm 3.4) |
| 3.3.3 | 127 | Example 3.8: `K = {p₀,p₁,p₂,(p₀p₁),(p₁p₂),(p₂p₀)}`, a triangulation of `S¹`, `H₁ ≅ ℤ` | consistency control for `SpineTask14.nakahara_circle_nontrivial` | `CONSISTENCY_CHECK` |
| 3.3.3 | 128 | Example 3.9: the *filled* triangle, `H₁ = 0` | consistency control for `SpineTask14.nakahara_filled_triangle` | `CONSISTENCY_CHECK` |
| 3.3.3 | 129 | Exercise 3.3: boundary of a tetrahedron, `H₂(S²) ≅ ℤ`, `H₁ = 0` | requested WP17 control; **not performed** (see §5) | `NOT_USED` |
| 3.3.5 | 130–136 | Möbius strip, `ℝP²`, torus | not on the Task-14 path | `NOT_USED` |
| 3.4 | 136–140 | connectedness, structure of `H_r`, Betti numbers, Euler–Poincaré | not on the Task-14 path | `NOT_USED` |

### What Nakahara does **not** contain

Verified by a full-text search of `GTP.pdf` for `excision`, `relative homology`, `CW complex`,
`Mayer` — **zero hits**. Concretely, the book contains **no**:

* relative homology `H_*(X,A)`;
* long exact sequence of a pair;
* excision theorem;
* cellular homology or CW-complex attachment theory;
* homology of `S^n` for general `n` (only the `S¹` example and the `S²` exercise);
* simplicial sets, degeneracies, or geometric realization in the simplicial-set sense.

Consequently **every** relative/excision ingredient of Task 14 required another source, and
the general `H_*(S^n)` result is *not* inferred from the book's `S¹`/`S²` cases (WP16 C, WP20
item 9 respected).

---

## 2. OTHER_TEXTBOOK_REFERENCE

Used only to fix statements and to check that the native constructions have the standard
shape. No proof text is reproduced.

| source | item | role |
| --- | --- | --- |
| A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002 (§2.1 "Simplicial and Singular Homology", §2.1 "Relative Homology Groups", Theorem 2.20 "Excision", §2.2 "Cellular Homology", Appendix "Topology of Cell Complexes") | the definition of the relative singular chain complex `C_*(X,A) = C_*(X)/C_*(A)`, its short exact sequence and the resulting long exact sequence; the classical route "cell attachment + excision ⇒ `H_*(X^n,X^{n-1})` free on the `n`-cells"; `H_q(D^n,∂D^n) = ℤ` concentrated in degree `n` | `OTHER_TEXTBOOK_REFERENCE` for the *statements* of WP7, WP8, and of the blockers B1/B3. The Lean proofs of WP7/WP8 do **not** follow Hatcher's proof architecture: they are obtained from the pinned abelian-category machinery (`ShortComplex.ShortExact`, `HomologicalComplex.HomologySequence`), which is a different (categorical) route to the same statements. |
| P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Progress in Mathematics 174, Birkhäuser, 1999 (Ch. I §2, the Eilenberg–Zilber lemma; Ch. I §2 "skeleta" and the skeletal pushout) | the statement that `sk_n X` is obtained from `sk_{n-1} X` by attaching `∂Δ^n ⟶ Δ^n` along the nondegenerate `n`-simplices, and the Eilenberg–Zilber unique-decomposition lemma that proves it | `NATIVE_PROOF_ARCHITECTURE` for WP3: the Lean proof follows this architecture (unique decomposition `x = σ · f` with `σ` nondegenerate and `f` a surjection ⇒ degreewise disjoint-union decomposition ⇒ universal property), but the Eilenberg–Zilber input itself is taken from the **pinned Mathlib** (`SSet.unique_nonDegenerate_simplex`, `SSet.unique_nonDegenerate_map`), not reproved. |
| S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed., Springer, 1998 (Ch. V §5, left adjoints preserve colimits) | WP4 | the Lean statement is the pinned `Adjunction.leftAdjoint_preservesColimits` instantiated at `sSetTopAdj`; the source is cited for the statement only |

---

## 3. MATHLIB_SOURCE (pinned; reused, not reproved)

Read from the pinned source tree, not from generated documentation.

| declaration | file | use |
| --- | --- | --- |
| `SSet.toTop`, `TopCat.toSSet`, `sSetTopAdj`, `SSet.toTopSimplex` | `Mathlib/AlgebraicTopology/SingularSet.lean` | realization, singular simplicial set, the frozen canonical unit `η`, and `\|Δ[r]\| ≅ Δ^r_top` |
| `Adjunction.leftAdjoint_preservesColimits`, `IsPushout.map` | `Mathlib/CategoryTheory/...` | WP4 |
| `SSet.skeleton`, `SSet.mem_skeleton`, `SSet.skeleton_obj_eq_top`, `SSet.mem_skeleton_obj_iff_of_nonDegenerate` | `Mathlib/AlgebraicTopology/SimplicialSet/Skeleton.lean` | the skeletal filtration |
| `SSet.exists_nonDegenerate`, `SSet.unique_nonDegenerate_dim/simplex/map`, `SSet.isIso_of_nonDegenerate` | `Mathlib/AlgebraicTopology/SimplicialSet/Degenerate.lean` | Eilenberg–Zilber input to WP3 |
| `SSet.boundary` (`∂Δ[n]`), `SSet.Subcomplex.ι`, `SSet.Subcomplex.homOfLE` | `Mathlib/AlgebraicTopology/SimplicialSet/Boundary.lean`, `.../Subcomplex.lean` | statement of the standard cell pair |
| `AlgebraicTopology.alternatingFaceMapComplex` | `Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean` | the chain complex functor of WP7 |
| `HomologicalComplex.shortExact_of_degreewise_shortExact` | `Mathlib/Algebra/Homology/HomologicalComplexAbelian.lean` | WP7.5 |
| `ShortComplex.ShortExact.δ`, `.homology_exact₁/₂/₃`, `HomologicalComplex.HomologySequence.δ_naturality` | `Mathlib/Algebra/Homology/HomologySequence.lean`, `HomologySequenceLemmas.lean` | WP8 |
| `HomologicalComplex.HomologySequence.composableArrows₅`, `mapComposableArrows₅`, `composableArrows₂`, `epi_homologyMap_of_epi_of_not_rel` | `Mathlib/Algebra/Homology/HomologySequenceLemmas.lean` | WP13 |
| `CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono`, `epi_of_epi_of_epi_of_mono`, `epi_of_epi_of_epi_of_epi` | `Mathlib/CategoryTheory/Abelian/DiagramLemmas/Four.lean` | WP13 |
| `ShortComplex.moduleCat_exact_iff_range_eq_ker`, `ModuleCat.mono_iff_injective`, `ModuleCat.epi_iff_surjective` | `Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean`, `Mathlib/Algebra/Category/ModuleCat/EpiMono.lean` | WP7.5 |
| `TopCat.disk` `𝔻 n`, `TopCat.sphere` `𝕊 n`, `diskBoundaryInclusion` | `Mathlib/Topology/Category/TopCat/Sphere.lean` | audited; **not used** — no comparison with `\|Δ[r]\|` exists in the pin |
| `HomotopicalAlgebra.RelativeCellComplex`, `CWComplex` | `Mathlib/AlgebraicTopology/RelativeCellComplex/*`, `Mathlib/Topology/CWComplex/Abstract/Basic.lean` | audited; **not used** — these are *definitions* of cell complexes; the pin contains no theorem attaching a CW structure to `\|K\|`, and no cellular-homology theorem |

---

## 4. UPSTREAM_MATHLIB_REFERENCE

* `Mathlib/AlgebraicTopology/SimplicialSet/Skeleton.lean`, module `TODO` block: *"show that
  `X.skeleton (n + 1)` is obtained from `X.skeleton n` by attaching `∂Δ[n] ⟶ Δ[n]` cells (this
  also holds for `skeletonOfMono i`) (@joelriou)"*. This is precisely WP3 and is **open
  upstream**; `SpineTask14.skelPiece_bijective` + `attachExtend*` supply it in the form of the
  degreewise decomposition and the universal property.
* `Mathlib/Algebra/Homology/HomologySequenceLemmas.lean`, module header: *"So far, we state
  only four lemmas for `φ.τ₃`. Eight more similar lemmas for `φ.τ₁` and `φ.τ₂` shall also be
  obtained (TODO)."* `SpineTask14.isIso_homologyMap_τ₂` / `quasiIso_τ₂` supply the `τ₂`
  five-lemma for `ℕ`-indexed chain complexes.
* `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` is the **entire** singular-homology
  development in the pin: the singular chain complex functor, the homology functor, and the
  computation for totally disconnected spaces. There is no relative theory and no excision.

---

## 5. CONSISTENCY_CHECK_ONLY

* `SpineTask14.nakahara_filled_triangle` — Nakahara Example 3.9 (PDF p. 128).
* `SpineTask14.nakahara_circle_nontrivial` — Nakahara Example 3.8 (PDF p. 127); over `ℤ₂` only
  non-vanishing of `H₁` is claimed, not `H₁ ≅ ℤ₂`.
* `SpineTask14.relChain_self_subsingleton`, `SpineTask14.cellIndexTopEquiv` — smoke tests of
  the Task-14 constructions themselves.
* **Boundary of a tetrahedron (Nakahara Exercise 3.3, PDF p. 129): NOT PERFORMED.** The book
  gives it only as an exercise, and the project has no machinery for the homology of `∂Δ[3]`
  as a simplicial set. It is recorded as missing rather than silently dropped.

---

## 6. NOT_USED

Explicitly audited and deliberately not used:

* Nakahara §3.3.1 (orientations), §3.3.4, §3.3.5, §3.4 — see the table in §1.
* Nakahara Theorem 3.4 (topological invariance of simplicial homology) — stated without proof
  in the book; the project never relies on it.
* Mathlib `𝔻 n` / `𝕊 n` / `CWComplex` / `RelativeCellComplex` — audited, unusable here for lack
  of any comparison theorem with `\|Δ[r]\|` (see `TASK14_SPECIALIZED_CELL_ATTACHMENT.md`, WP5).
* Mathlib `SSet.toTop` Kan-extension internals — not needed beyond the adjunction.
