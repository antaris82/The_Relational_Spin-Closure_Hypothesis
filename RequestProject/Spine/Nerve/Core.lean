import RequestProject.Spine.Nerve.Audit.ManifoldAssumptions
import RequestProject.Spine.Nerve.Cochain.ChainHomotopyComparison
import RequestProject.Spine.Nerve.Controls.UnitProbe

/-!
# Spine / Nerve / Core : the Task-9 endpoint

Task 9 asks for the canonical full simplicial model of the cover nerve, its geometric
realization, and the standard geometric comparison between simplicial cohomology of the nerve
and singular cohomology of the realization.

## What is proved, unconditionally

* **WP2 `FULL_SIMPLICIAL_NERVE`** — `NerveGeom.coverNerveSSet 𝓤 : SSet` is a genuine simplicial
  set: an actual functor `Δᵒᵖ ⥤ Set`.  `n`-simplices are the ordered `(n+1)`-tuples of cover
  indices with nonempty total intersection (repetitions allowed), faces delete a vertex
  (`coverNerveSSet_delta`, definitionally the Task-6 `CechZ2.face`) and degeneracies repeat a
  vertex (`coverNerveSSet_sigma`, `degen_idx_castSucc`, `degen_idx_succ`).  All simplicial
  identities come from the functorial structure and are restated concretely
  (`face_face_comm`, `degen_degen_comm`, `face_castSucc_degen`, `face_succ_degen`,
  `face_degen_of_le`, `face_degen_of_gt`).
* **WP3 `DERIVED_NATIVE`** — Task 6 used *all ordered tuples*, i.e. the **unnormalized**
  simplicial cochain complex.  `underlyingPresimplicial_coverNerveSSet` proves that forgetting
  the degeneracies of the new simplicial set gives back *exactly* the Task-7 presimplicial
  nerve, so the cochains, coboundary, cocycles, coboundaries and cohomology are the Task-6
  ones on the nose (`cochain_eq`, `d_eq`, `cocycles_eq`, `coboundaries_eq`,
  `cechCohomologyEquivSSet`).  No normalization bridge is needed; the normalized subcomplex is
  defined (`normalizedCochains`) only to record that it is *not* what Task 6 used.
  `isDegenerate_iff_exists_degen` proves the combinatorial and the simplicial notion of
  degeneracy agree for the cover nerve.
* **WP4 `GEOMETRIC_REALIZATION`** — Mathlib's realization functor is reused:
  `NerveGeom.coverNerveRealization 𝓤 = SSet.toTop.obj (coverNerveSSet 𝓤)`.
* **WP5 `GEOMETRIC_REALIZATION`** — `NerveGeom.charSimplex` is the canonical characteristic
  singular simplex of a nerve simplex, taken from the **unit of the adjunction**
  `SSet.toTop ⊣ TopCat.toSSet`; `charMap` presents it as a continuous map
  `Δⁿ_top → |N(𝓤)|`.  Face compatibility (`charSimplex_face`) and degeneracy compatibility
  (`charSimplex_degen`) are theorems, both instances of `charSimplex_reindex`, and
  `charSimplex_universal` proves the family is the universal one, so nothing is chosen.
* **WP6 `CHAIN_MAP`** — `NerveGeom.chainMap` and the theorem
  `NerveGeom.chainMap_comm : ∂_sing ∘ J = J ∘ ∂_simp`, whose proof consumes `charSimplex_face`.
* **WP7 `COCHAIN_MAP`** — `NerveGeom.geometricCochainMap`, a genuine map of cochain complexes
  with `J*δ_sing = δ_simp J*`; its transposition relation to the chain map is
  `geometricCochainMap_dual_chainMap`; it descends to
  `NerveGeom.geometricHmap 𝓤 n : Hⁿ_sing(|N(𝓤)|;ℤ₂) → Ȟⁿ(𝓤;ℤ₂)`.
* **WP12 `SPECIFICATION_HARDENED`** — `NerveGeom.canonicalNervePresentation` *constructs* the
  Task-8 `GoodCoverSpec.NervePresentation`, and `NerveGeom.NerveTheoremData` fixes the
  realization to the canonical one, so the remaining nerve-theorem edge has the mandated shape
  `|N(𝓤)| ≃ X` and cannot be satisfied by an unrelated space.

## What is **not** proved

* **WP8/WP9 `BLOCKED`** — that `geometricHmap` is an isomorphism.  This is the standard
  simplicial-to-singular comparison theorem; the audit of the possible routes and of what the
  pinned library provides is in `RequestProject.Spine.Nerve.Cochain.ComparisonSpec`.  It is recorded as
  the explicitly conditional specification `NerveGeom.GeometricComparison`, whose only field
  asserts bijectivity of the *canonical* map constructed here.  A degree-two-only variant
  `GeometricComparison₂` is recorded, but is not materially smaller mathematically.
* **WP10 `SPIN_CLASS_TRANSPORT`, conditional** — `NerveGeom.spinLiftRealizedClass` and
  `NerveGeom.spinLiftRealizedClass_eq_zero_iff_cech` /
  `NerveGeom.frameRealizedClass_eq_zero_iff_spinStructure` are proved *given* a
  `GeometricComparison`.  Unconditional transport of `[z]` to `H²_sing(|N(𝓤)|;ℤ₂)` is therefore
  **not** available.
* **WP14 `BLOCKED`** — the nerve theorem, with its exact hypotheses written out in
  `NerveGeom.NerveTheoremStatement`.

## The three layers stay distinct

`coverNerveSSet 𝓤` (combinatorial), `coverNerveRealization 𝓤` (topological) and the base space
are three different objects; the relations between them are theorems or, where they are not
available, named conditional specifications.
-/

/-! ## Axiom audit of the Task-9 principal declarations

Each of the following must report only `[propext, Classical.choice, Quot.sound]`. -/

#print axioms NerveGeom.coverNerveSSet
#print axioms NerveGeom.coverNerveSSet_delta
#print axioms NerveGeom.coverNerveSSet_sigma
#print axioms NerveGeom.degen_repeats_vertex
#print axioms NerveGeom.face_face_comm
#print axioms NerveGeom.degen_degen_comm
#print axioms NerveGeom.face_castSucc_degen
#print axioms NerveGeom.face_succ_degen
#print axioms NerveGeom.face_degen_of_le
#print axioms NerveGeom.face_degen_of_gt
#print axioms NerveGeom.underlyingPresimplicial_coverNerveSSet
#print axioms NerveGeom.d_eq
#print axioms NerveGeom.cechCohomologyEquivSSet
#print axioms NerveGeom.isDegenerate_iff_exists_degen
#print axioms NerveGeom.normalizedCochains
#print axioms NerveGeom.coverNerveRealization
#print axioms NerveGeom.charSimplex
#print axioms NerveGeom.charMap
#print axioms NerveGeom.charSimplex_reindex
#print axioms NerveGeom.charSimplex_face
#print axioms NerveGeom.charSimplex_degen
#print axioms NerveGeom.charSimplex_universal
#print axioms NerveGeom.chainMap
#print axioms NerveGeom.chainMap_comm
#print axioms NerveGeom.geometricCochainMap
#print axioms NerveGeom.geometricCochainMap_dual_chainMap
#print axioms NerveGeom.SingularToSimplicialCochainMap.Hmap
#print axioms NerveGeom.geometricHmap
#print axioms NerveGeom.canonicalNervePresentation
#print axioms NerveGeom.NerveTheoremData.toNerveRealizationSpec
#print axioms NerveGeom.GeometricComparison.equiv
#print axioms NerveGeom.spinLiftRealizedClass
#print axioms NerveGeom.spinLiftRealizedClass_lift_independent
#print axioms NerveGeom.spinLiftRealizedClass_eq_zero_iff_cech
#print axioms NerveGeom.spinLiftRealizedClass_eq_zero_iff
#print axioms NerveGeom.frameRealizedClass_eq_zero_iff_spinStructure
#print axioms NerveGeom.fullComparison
#print axioms NerveGeom.NerveTheoremStatement

/-! ## Task 10

Task 10 adds four modules to this layer.  See `TASK10_AUDIT.md` for the full route matrix.

* **WP0 `DERIVED_NATIVE`** — `RequestProject.Spine.Nerve.Audit.ManifoldAssumptions` corrects the
  Task-9 claim that the Task-4 manifold layer supplies second countability / paracompactness.
  `SpineTask10.chartedNotSecondCountable` exhibits a space charted on the Task-4 carrier, and a
  `C^∞` manifold for `carrierModel`, that is **not** second countable, so
  `SpineTask10.not_secondCountable_of_charted` refutes the implication outright.  Nothing is
  added to Task 4.
* **WP2 `CHAIN_IDENTIFICATION`** — `RequestProject.Spine.Nerve.Basic.UnitChainMap` proves
  `NerveGeom.chainMap_eq_unitChainMap`: the Task-9 chain map `J` **is** the free
  `ℤ₂`-linearisation of the adjunction unit `η : N(𝓤) ⟶ Sing|N(𝓤)|`.  Both boundaries are the
  linearised boundaries of the two simplicial sets (`simpBoundary_eq`, `singBoundary_eq`), and
  `chainMap_comm` is the naturality of `η` (`sSetBoundary_naturality`).
* **WP10 `COHOMOLOGY_ISOMORPHISM`, conditional on one chain-level statement** —
  `RequestProject.Spine.Nerve.Cochain.Dualization` builds the explicit transpose `dualOf` and proves
  `dualOf ∂ = δ`, `dualOf J = J*`; `RequestProject.Spine.Nerve.Cochain.ChainHomotopyComparison` then
  proves `NerveGeom.geometricHmap_bijective_of_chainHomotopyEquiv`: a chain-homotopy inverse
  for the canonical `chainMap` makes the *existing* `geometricHmap 𝓤 n` bijective in every
  degree.  No universal coefficient theorem is used.
* **`BLOCKED`** — `NerveGeom.ChainComparisonStatement`, i.e. the existence of that
  chain-homotopy inverse, is the single remaining blocker of the geometric comparison.  Pinned
  Mathlib v4.28.0 has no singular excision, no Mayer–Vietoris, no CW/cellular structure on
  `SSet.toTop.obj S`, no acyclic-models theorem and no Quillen equivalence for `sSetTopAdj`.
-/

#print axioms NerveGeom.SSetChain
#print axioms NerveGeom.sSetBoundary
#print axioms NerveGeom.sSetChainMap
#print axioms NerveGeom.sSetBoundary_naturality
#print axioms NerveGeom.simpBoundary_eq
#print axioms NerveGeom.singBoundary_eq
#print axioms NerveGeom.chainMap_eq_unitChainMap
#print axioms NerveGeom.chainMap_comm_of_unit
#print axioms NerveGeom.dualOf
#print axioms NerveGeom.linearCombination_dualOf
#print axioms NerveGeom.dualOf_comp
#print axioms NerveGeom.dualOf_simpBoundary
#print axioms NerveGeom.dualOf_singBoundary
#print axioms NerveGeom.dualOf_chainMap
#print axioms NerveGeom.ChainHomotopyEquivData
#print axioms NerveGeom.ChainComparisonStatement
#print axioms NerveGeom.ChainHomotopyEquivData.cochainInv_comm
#print axioms NerveGeom.ChainHomotopyEquivData.cochainHtpySimp_zero
#print axioms NerveGeom.ChainHomotopyEquivData.cochainHtpySimp_succ
#print axioms NerveGeom.ChainHomotopyEquivData.cochainHtpySing_zero
#print axioms NerveGeom.ChainHomotopyEquivData.cochainHtpySing_succ
#print axioms NerveGeom.Hmap_surjective
#print axioms NerveGeom.Hmap_injective
#print axioms NerveGeom.geometricHmap_bijective_of_chainHomotopyEquiv
#print axioms NerveGeom.ChainHomotopyEquivData.toGeometricComparison
#print axioms NerveGeom.spinLiftRealizedClassOfChain_eq_zero_iff_cech
#print axioms NerveGeom.spinLiftRealizedClassOfChain_eq_zero_iff
#print axioms SpineTask10.not_secondCountable_sigma
#print axioms SpineTask10.chartedNotSecondCountable
#print axioms SpineTask10.not_secondCountable_of_charted

/-! ### Task 11 (WP14/WP23) : axiom audit of the upstream-delta compile probes -/

#print axioms SpineTask11.unitChainComplexMap
#print axioms SpineTask11.unitChainComplexMap_target
#print axioms SpineTask11.unitChainComplexMap_naturality
#print axioms SpineTask11.UnitQuasiIsoStatement
#print axioms SpineTask11.taskNine_and_mathlib_share_the_unit
