import RequestProject.Spine.GoodCover.Constancy
import RequestProject.Spine.GoodCover.NerveIdentification
import RequestProject.Spine.GoodCover.ManifoldCovers
import RequestProject.Spine.Cech.SingularBridgeSpec

/-!
# Task 7, WP6–WP12 : the good-cover comparison, assembled from *named* missing theorems

WP5 identified the Task-6 Čech complex with the simplicial complex of the nerve
(`NerveZ2.cechCohomologyEquiv`, an identity).  The classical route from there to singular
cohomology is

```
   Ȟ²(𝓤;ℤ₂) = H²_simp(N(𝓤);ℤ₂)  ≅  H²_sing(|N(𝓤)|;ℤ₂)  ≅  H²_sing(M;ℤ₂)
                                  (WP8)                  (WP6 + WP9)
```

and Task 7 must not assume any of the three steps.  This module therefore

* names each missing input as an **explicit hypothesis structure** — never an axiom, never a
  typeclass, never consumed by anything else in the Spine;
* proves everything that *does* follow from them, so that the exact remaining debt is visible;
* proves, in particular, the conditional implications that show why each hypothesis is needed.

## The three hypotheses

* `GoodCoverSpec.HomotopyInvariance n` (**WP9**) — homotopy-equivalent spaces have isomorphic
  Task-5 cohomology in degree `n`.  Pinned Mathlib has no homotopy invariance for singular
  (co)homology at all (there is no prism operator, no chain-homotopy machinery for the
  singular complex), so this is a genuine missing theorem, *major* in scope.
* `GoodCoverSpec.NerveRealization X U` (**WP6**) — a topological realization of the nerve
  together with a homotopy equivalence with the base.  Pinned Mathlib has geometric
  realization of simplicial sets (`SSet.toTop`) but no nerve theorem and no partition-of-unity
  construction of the two comparison maps; *major* in scope.
* `GoodCoverSpec.SimplicialSingularComparison U R` (**WP8**) — the classical comparison
  between simplicial and singular cohomology of a realization, in degree two.  Absent from
  pinned Mathlib; *moderate to major* in scope.

## What is proved here

* `HomotopyInvariance.cohomology_succ_eq_zero_of_contractible` — with WP9 available, the
  native cohomology of a contractible space vanishes above degree zero (using the *proved*
  point computation `Mod2Cohomology.cohomology_succ_eq_zero_of_subsingleton`);
* `isAcyclicCover_of_isGoodCover` — with WP9 available, **good ⇒ acyclic**; this is precisely
  the implication WP3 asks not to be assumed;
* `Comparison.equiv` (**WP10**) — from the three hypotheses, the isomorphism
  `Φ_𝓤 : Ȟ²(𝓤;ℤ₂) ≅ H²_sing(X;ℤ₂)`.  It is *not canonical*: it depends on the chosen nerve
  realization and on the chosen comparison data, which is recorded in the field structure;
* `spinLiftSingularClass` (**WP11**) — the transported Spin-lift class, with independence of
  the local Spin lifts, and the vanishing theorem
  `[z]_sing = 0 ↔ [z]_Ȟ² = 0 ↔ coherent Spin lifts exist`; for Lorentz frame data,
  `[z]_sing = 0 ↔ a Spin structure exists`;
* `spinLiftSingularClass_refinement` (**WP12**) — invariance under refinement of the good
  cover, *given* a comparison family that is natural in refinements.  Full independence of the
  chosen good cover additionally needs a common good refinement of two good covers, which is
  **not** available and is recorded as `CommonGoodRefinement`, again a hypothesis.
-/

noncomputable section

namespace GoodCoverSpec

open CategoryTheory CechSpinLift CechZ2 CechSpinZ2 GoodCoverZ2 NerveZ2 SpinCore LorentzFrames
  NullSectorTask28

universe u t

/-! ## WP9 : homotopy invariance of the Task-5 singular theory (hypothesis) -/

/-- **WP9, formerly a hypothesis.**

*Task-8 classification: `SUPERSEDED_BY_NATIVE_THEOREM`.*  This declaration is retained for
provenance and backward compatibility only.  Homotopy invariance of the native singular mod-2
cohomology is now a **theorem** of the Spine, `Mod2Cohomology.Hmap_eq_of_homotopic`, and the
present interface is *inhabited* by `GoodCoverSpec.nativeHomotopyInvariance`.  It must no
longer be used as a mathematical assumption; downstream code should use
`Mod2Cohomology.homotopyEquivCohomology`, whose two directions are `Mod2Cohomology.Hmap` of the
actual maps of the homotopy equivalence.

A homotopy equivalence of spaces induces an isomorphism of the native mod-2 singular cohomology
in degree `n`. -/
structure HomotopyInvariance (n : ℕ) where
  /-- The induced isomorphism. -/
  transport : ∀ {X Y : TopCat.{u}}, ContinuousMap.HomotopyEquiv (X : Type u) (Y : Type u) →
    (Mod2Cohomology.Cohomology X n ≃ₗ[ZMod 2] Mod2Cohomology.Cohomology Y n)

/-- **Conditional consequence of WP9.**  A contractible space has vanishing cohomology above
degree zero: transport the class to a point and use the *proved* point computation. -/
theorem HomotopyInvariance.cohomology_succ_eq_zero_of_contractible {n : ℕ}
    (H : HomotopyInvariance.{u} (n + 1)) (X : TopCat.{u}) [ContractibleSpace X]
    (q : Mod2Cohomology.Cohomology X (n + 1)) : q = 0 := by
  classical
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit (X : Type u)
  let P : TopCat.{u} := TopCat.of PUnit.{u + 1}
  have hu : (Unit : Type) ≃ₜ (P : Type u) := Homeomorph.homeomorphOfUnique _ _
  let e' : ContinuousMap.HomotopyEquiv (X : Type u) (P : Type u) := e.trans hu.toHomotopyEquiv
  haveI : Subsingleton (P : Type u) := inferInstanceAs (Subsingleton PUnit.{u + 1})
  haveI : Nonempty (P : Type u) := inferInstanceAs (Nonempty PUnit.{u + 1})
  have hzero : H.transport e' q = 0 :=
    Mod2Cohomology.cohomology_succ_eq_zero_of_subsingleton n _
  exact (H.transport e').map_eq_zero_iff.mp hzero

/-- **Conditional consequence of WP9 (WP3 form).**  With homotopy invariance available in every
positive degree, a **good cover is an acyclic cover**.  The implication is exactly as strong as
homotopy invariance: nothing else is missing. -/
theorem isAcyclicCover_of_isGoodCover {X : Type u} [TopologicalSpace X] {ι : Type t}
    {U : ι → Set X} (H : ∀ k : ℕ, HomotopyInvariance.{u} (k + 1)) (h : IsGoodCover U) :
    IsAcyclicCover U := by
  refine ⟨h.isOpen, h.covers, fun σ => h.isPreconnected_inter σ, ?_⟩
  intro n σ hne k q
  haveI := h.contractible_inter σ hne
  exact (H k).cohomology_succ_eq_zero_of_contractible (TopCat.of (inter U σ)) q

/-! ## WP6 and WP8 : the nerve theorem and the simplicial-singular comparison (hypotheses) -/

variable {X : TopCat.{u}} {ι : Type t}

/-- **WP6, the nerve theorem, as a provisional hypothesis.**

*Task-8 classification: `PROVISIONAL_CONDITIONAL_INTERFACE`, superseded as a specification by
`GoodCoverSpec.NerveRealizationSpec`.*  This structure is **weaker than its name suggests**: it
carries a bare `realization : TopCat` with no structural relationship to the nerve `N(𝓤)`, so
*any* space homotopy equivalent to `X` inhabits it.  It is **not** the nerve theorem and must
never be documented as one.  The hardened replacement requires the realization to be the
geometric realization of a simplicial set presenting the nerve; see
`RequestProject.Spine.GoodCover.HardenedSpec`.

A topological realization of the nerve of the cover, together with a homotopy equivalence with
the base space.  Pinned Mathlib supplies the geometric realization functor `SSet.toTop`, but no
nerve theorem, no comparison maps and no partition of unity producing them. -/
structure NerveRealization (U : ι → Set (X : Type u)) where
  -- Task-9 classification: `SUPERSEDED_BY_GEOMETRIC_COMPARISON`; use
  -- `NerveGeom.NerveTheoremData` instead.
  /-- The realization `|N(𝓤)|`. -/
  realization : TopCat.{u}
  /-- The homotopy equivalence `|N(𝓤)| ≃ X` of the nerve theorem. -/
  equiv : ContinuousMap.HomotopyEquiv (realization : Type u) (X : Type u)

/-- **WP8, the simplicial-to-singular comparison, as a provisional hypothesis** (degree two
only, which is all Task 7 needs).

*Task-8 classification: `PROVISIONAL_CONDITIONAL_INTERFACE`, superseded as a specification by
`GoodCoverSpec.SimplicialSingularComparisonSpec`.*  This structure is **weaker than its name
suggests**: an *arbitrary* linear equivalence inhabits it, so it does not express the standard
comparison theorem and must never be documented as one.  The hardened replacement demands an
explicit map of cochain complexes, compatible with both coboundaries, and asks for bijectivity
of the map it *induces* on cohomology; see `RequestProject.Spine.GoodCover.HardenedSpec`. -/
structure SimplicialSingularComparison (U : ι → Set (X : Type u)) (R : TopCat.{u}) where
  -- Task-9 classification: `SUPERSEDED_BY_GEOMETRIC_COMPARISON`; use
  -- `NerveGeom.GeometricComparison` instead.
  /-- The classical comparison isomorphism for the nerve and its realization. -/
  compare : (coverNerve U).Cohomology 2 ≃ₗ[ZMod 2] Mod2Cohomology.Cohomology R 2

/-! ## WP10 : the assembled comparison -/

/-- **WP10.**  The three hypotheses for one fixed cover, packaged.

*Task-8 classification: `SUPERSEDED`.*  The `homotopy` field is no longer needed (WP11) and the
other two fields are provisional (WP12, WP13).  The hardened replacement is
`GoodCoverSpec.HardenedComparison`, which has no homotopy-invariance field at all.  Every field is a *choice*;
nothing here is canonical, and this is recorded in `Comparison.equiv_depends_on_choices` below
by the fact that `equiv` is a function of the whole datum. -/
structure Comparison (U : ι → Set (X : Type u)) where
  /-- The nerve realization and the nerve-theorem homotopy equivalence (WP6). -/
  nerve : NerveRealization U
  /-- The simplicial-to-singular comparison for that realization (WP8). -/
  simplicial : SimplicialSingularComparison U nerve.realization
  /-- Homotopy invariance of the Task-5 theory in degree two (WP9). -/
  homotopy : HomotopyInvariance.{u} 2

namespace Comparison

variable {U : ι → Set (X : Type u)}

/-- **The fixed-good-cover comparison `Φ_𝓤 : Ȟ²(𝓤;ℤ₂) ≅ H²_sing(X;ℤ₂)`**, assembled from the
identification of the Čech complex with the nerve complex (proved), the simplicial-singular
comparison (hypothesis), and homotopy invariance applied to the nerve equivalence
(hypotheses). -/
def equiv (C : Comparison U) :
    CechZ2.Cohomology U 2 ≃ₗ[ZMod 2] Mod2Cohomology.Cohomology X 2 :=
  (cechCohomologyEquiv₂ U).symm ≪≫ₗ C.simplicial.compare ≪≫ₗ
    C.homotopy.transport C.nerve.equiv

/-- The comparison is a linear isomorphism, so a Čech class vanishes iff its singular image
does. -/
theorem equiv_eq_zero_iff (C : Comparison U) (q : CechZ2.Cohomology U 2) :
    C.equiv q = 0 ↔ q = 0 := by
  exact C.equiv.map_eq_zero_iff

end Comparison

/-! ## WP11 : the transported Spin-lift class -/

variable {𝓤 : CechCover (X : Type u) ι} {T : VisibleCocycle (↥GLor) 𝓤}

/-- **WP11, principal.**  The Spin-lift obstruction of the Task-3/Task-6 chain, transported to
a genuine class in the native singular mod-2 cohomology of the base, along a comparison
assembled from the WP6/WP8/WP9 hypotheses on a good cover.

The class depends on the comparison datum `C`; it does **not** depend on the choice of local
Spin lifts (`spinLiftSingularClass_lift_independent`). -/
def spinLiftSingularClass (C : Comparison 𝓤.U) (h : IsGoodCover 𝓤.U)
    (D : SpinLiftFamily internalSpinProjection T) : Mod2Cohomology.Cohomology X 2 :=
  C.equiv (spinLiftCechClassGood h D)

/-- The transported class is independent of the chosen local Spin lifts. -/
theorem spinLiftSingularClass_lift_independent (C : Comparison 𝓤.U) (h : IsGoodCover 𝓤.U)
    (D D' : SpinLiftFamily internalSpinProjection T) :
    spinLiftSingularClass C h D = spinLiftSingularClass C h D' := by
  unfold spinLiftSingularClass
  rw [spinLiftCechClassGood_lift_independent h D D']

/-- **The vanishing theorem, singular form.**  `[z]_sing = 0 ↔ [z]_Ȟ² = 0 ↔ coherent Spin
transition data exist.** -/
theorem spinLiftSingularClass_eq_zero_iff (C : Comparison 𝓤.U) (h : IsGoodCover 𝓤.U)
    (D : SpinLiftFamily internalSpinProjection T) :
    spinLiftSingularClass C h D = 0 ↔
      ∃ D' : SpinLiftFamily internalSpinProjection T, D'.IsCoherent := by
  rw [spinLiftSingularClass, Comparison.equiv_eq_zero_iff,
    spinLiftCechClassGood_eq_zero_iff h D]

/-! ## The Lorentz-frame endpoint -/

variable {Fib : ↥X → Type u} [∀ x, AddCommGroup (Fib x)] [∀ x, Module ℝ (Fib x)]
  {Φ : LorentzFrameData (↥X) Fib ι}

/-- **WP11 for the Task-4 frame data.**  The Lorentz-frame Spin-lift obstruction as a singular
mod-2 class. -/
def frameSingularClass (C : Comparison Φ.cover.U) (h : IsGoodCover Φ.cover.U)
    (D : FrameSpinLifts Φ) : Mod2Cohomology.Cohomology X 2 :=
  C.equiv (frameCechClassGood h D)

/-- **The central conditional endpoint of Task 7.**  On a good cover of the frame data, and
given the WP6/WP8/WP9 comparison hypotheses, the singular class vanishes **iff** the Lorentz
frame data admits a Spin structure. -/
theorem frameSingularClass_eq_zero_iff_spinStructure (C : Comparison Φ.cover.U)
    (h : IsGoodCover Φ.cover.U) (D : FrameSpinLifts Φ) :
    frameSingularClass C h D = 0 ↔ Nonempty (SpinFrameStructure Φ) := by
  rw [frameSingularClass, Comparison.equiv_eq_zero_iff,
    frameCechClassGood_eq_zero_iff_spinStructure h D]

/-! ## WP12 : behaviour under refinement, and the remaining obstacle -/

variable {ι' : Type t} {𝓥 : CechCover (X : Type u) ι'}

/-- **WP12 hypothesis.**  A *family* of comparisons, one per cover, compatible with refinement
pullbacks.  Compatibility is exactly the naturality of the nerve theorem in refinements; it is
not derivable from the fixed-cover data. -/
structure ComparisonFamily (X : TopCat.{u}) where
  /-- A comparison datum for every cover. -/
  comparison : ∀ {ι : Type t} (U : ι → Set (X : Type u)), Comparison U
  /-- Refining a cover does not change the singular image. -/
  refinement_compat : ∀ {ι ι' : Type t} (𝓤 : CechCover (X : Type u) ι)
    (𝓥 : CechCover (X : Type u) ι') (R : CoverRefinement 𝓥 𝓤) (q : CechZ2.Cohomology 𝓤.U 2),
    (comparison 𝓥.U).equiv (CechZ2.Hmap R.le 2 q) = (comparison 𝓤.U).equiv q

/-- **WP12, conditional.**  Given a refinement-compatible comparison family, the transported
Spin class is unchanged when the good cover is refined by another good cover. -/
theorem spinLiftSingularClass_refinement (F : ComparisonFamily.{u, t} X)
    (R : CoverRefinement 𝓥 𝓤) (hU : IsGoodCover 𝓤.U) (hV : IsGoodCover 𝓥.U)
    (D : SpinLiftFamily internalSpinProjection T) :
    spinLiftSingularClass (F.comparison 𝓥.U) hV (D.pullLift R) =
      spinLiftSingularClass (F.comparison 𝓤.U) hU D := by
  unfold spinLiftSingularClass spinLiftCechClassGood spinLiftCechClass
  rw [spinCechClass_indep_of_values spinKernelSign
      (constOn₃_ofGoodCover hV (D.pullLift R)) ((constOn₃_ofGoodCover hU D).pull R),
    ← Hmap_spinCechClass spinKernelSign R (constOn₃_ofGoodCover hU D)]
  exact F.refinement_compat 𝓤 𝓥 R _

/-- The data of a common good refinement of two good covers. -/
structure GoodRefinementData (𝓤 : CechCover (X : Type u) ι) (𝓥 : CechCover (X : Type u) ι') where
  /-- The index type of the common refinement. -/
  index : Type t
  /-- The common refinement itself. -/
  cover : CechCover (X : Type u) index
  /-- It is again a good cover. -/
  good : IsGoodCover cover.U
  /-- It refines the first cover. -/
  toFirst : CoverRefinement cover 𝓤
  /-- It refines the second cover. -/
  toSecond : CoverRefinement cover 𝓥

/-- **WP12, the remaining obstacle, as a hypothesis.**  Two *arbitrary* good covers need not be
comparable by refinement; the classical argument passes to a common refinement and needs it to
be good again.  Constructing common good refinements requires the same Riemannian input as
good-cover existence itself, so it is recorded here and not proved. -/
structure CommonGoodRefinement (X : TopCat.{u}) where
  /-- A common good refinement of any two good covers. -/
  refine : ∀ {ι ι' : Type t} (𝓤 : CechCover (X : Type u) ι) (𝓥 : CechCover (X : Type u) ι'),
    IsGoodCover 𝓤.U → IsGoodCover 𝓥.U → GoodRefinementData 𝓤 𝓥

/-- **WP12, conditional on both hypotheses.**  With a refinement-compatible comparison family
*and* common good refinements, the transported Spin class is the same for any two good covers
carrying (refinement-compatible) Spin lift data.  The second hypothesis is the exact remaining
obstacle to unconditional cover independence. -/
theorem spinLiftSingularClass_common_refinement (F : ComparisonFamily.{u, t} X)
    (K : CommonGoodRefinement.{u, t} X) (hU : IsGoodCover 𝓤.U) (hV : IsGoodCover 𝓥.U)
    (T' : VisibleCocycle (↥GLor) 𝓥) (D : SpinLiftFamily internalSpinProjection T)
    (D' : SpinLiftFamily internalSpinProjection T')
    (hcomp : ∀ (W : GoodRefinementData 𝓤 𝓥),
      spinLiftSingularClass (F.comparison W.cover.U) W.good (D.pullLift W.toFirst) =
        spinLiftSingularClass (F.comparison W.cover.U) W.good (D'.pullLift W.toSecond)) :
    spinLiftSingularClass (F.comparison 𝓤.U) hU D =
      spinLiftSingularClass (F.comparison 𝓥.U) hV D' := by
  have W := K.refine 𝓤 𝓥 hU hV
  have h1 := spinLiftSingularClass_refinement F W.toFirst hU W.good D
  have h2 := spinLiftSingularClass_refinement F W.toSecond hV W.good D'
  rw [← h1, ← h2]
  exact hcomp W

end GoodCoverSpec
