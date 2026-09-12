import RequestProject.Spine.GoodCover.SingularComparisonSpec
import RequestProject.Spine.GoodCover.GoodCoverAcyclic

/-!
# Task 8, WP11–WP13 : hardening the Task-7 conditional comparison layer

Task 7 recorded three missing theorems as *provisional* hypothesis structures.  Two of them
were, as stated, weaker than their names suggested:

* `GoodCoverSpec.NerveRealization` carried a bare `realization : TopCat` with **no structural
  relationship to the nerve** — any space homotopy equivalent to `X` satisfied it;
* `GoodCoverSpec.SimplicialSingularComparison` carried a bare linear equivalence
  `Ȟ²_simp ≃ₗ H²_sing` — **any** linear isomorphism satisfied it.

The third, `GoodCoverSpec.HomotopyInvariance`, is now a theorem of the Spine.

This module does three things and deletes nothing.

## WP11 — supersession of the homotopy-invariance interface

`GoodCoverSpec.nativeHomotopyInvariance` *constructs* the Task-7 interface from the Task-8
theorem `Mod2Cohomology.Hmap_eq_of_homotopic`.  It is therefore no longer an assumption, and
the hardened comparison below carries no homotopy-invariance field at all.

Classification of `GoodCoverSpec.HomotopyInvariance`: `SUPERSEDED_BY_NATIVE_THEOREM`.

## WP12 — a nerve realization that is actually a nerve realization

`GoodCoverSpec.NervePresentation` requires a *simplicial set* whose simplices and face maps are
those of the Task-7 combinatorial nerve `NerveZ2.coverNerve U`, and
`GoodCoverSpec.NerveRealizationSpec` requires the realization to be **equal to**
`SSet.toTop.obj` of that simplicial set, before asking for a homotopy equivalence with the base.
The four layers the task asks to distinguish are separate fields:

1. the combinatorial nerve — `NerveZ2.coverNerve U`, fixed, not chosen;
2. a simplicial set presenting it — `NervePresentation.sset` with `simplexEquiv`/`face_compat`;
3. its geometric realization and the underlying space — `realization` with `realization_eq`;
4. the comparison with the base — `equiv`.

Nothing is constructed: no nerve realization is produced here, and the nerve theorem is not
proved.  Classification: `BLOCKED_PENDING_GEOMETRIC_REALIZATION`, `SPECIFICATION_HARDENED`.

## WP13 — a simplicial-to-singular comparison that is actually a comparison

`GoodCoverSpec.SimplicialSingularCochainMap` is a genuine map of **cochain complexes**: a
degree-wise linear map together with the commutation with the two coboundaries.  It is shown
here to descend to cocycles, to coboundaries and hence to cohomology
(`SimplicialSingularCochainMap.Hmap`), and only then may a comparison be asserted, as
*bijectivity of that induced map* (`SimplicialSingularComparisonSpec`).  An arbitrary linear
isomorphism of cohomology no longer satisfies the specification.
Classification: `SPECIFICATION_HARDENED`, `BLOCKED`.
-/

noncomputable section

namespace GoodCoverSpec

open CategoryTheory Opposite Mod2Cohomology NerveZ2 CechZ2

universe u

/-! ## WP11 : the homotopy-invariance interface is now a theorem -/

/-- **WP11.**  The Task-7 conditional interface `GoodCoverSpec.HomotopyInvariance`, *constructed*
from the Task-8 theorem.  Its existence is the formal statement that the interface has ceased to
be an assumption: it is now inhabited natively, in every degree.

Downstream code should use `Mod2Cohomology.homotopyEquivCohomology` (or `Mod2Cohomology.Hmap`)
directly; this definition exists for backward compatibility with the Task-7 declarations. -/
def nativeHomotopyInvariance (n : ℕ) : HomotopyInvariance.{u} n where
  transport {_ _} e := (Mod2Cohomology.homotopyEquivCohomology e n).symm

/-- The native transport is not an arbitrary choice: it is `Hmap` of the forward map of the
homotopy equivalence, in the inverse direction. -/
@[simp] theorem nativeHomotopyInvariance_transport_symm {X Y : TopCat.{u}} (n : ℕ)
    (e : ContinuousMap.HomotopyEquiv (X : Type u) (Y : Type u))
    (q : Mod2Cohomology.Cohomology Y n) :
    ((nativeHomotopyInvariance n).transport e).symm q
      = Mod2Cohomology.Hmap (Mod2Cohomology.hequivFwd e) n q := rfl

variable {X : TopCat.{u}} {ι : Type u}

/-! ## WP12 : the hardened nerve-realization specification -/

/-- **A simplicial set presenting the nerve of a cover.**  The simplices in each degree are in
bijection with the simplices of the Task-7 combinatorial nerve `NerveZ2.coverNerve U`, and the
bijections intertwine the simplicial face maps with the nerve's face maps.

This is what makes "the nerve" of a `NerveRealizationSpec` genuinely the nerve of `U`. -/
structure NervePresentation (U : ι → Set (X : Type u)) where
  /-- The presenting simplicial set. -/
  sset : SSet.{u}
  /-- Its `n`-simplices are the `n`-simplices of the nerve. -/
  simplexEquiv : ∀ n : ℕ,
    sset.obj (op (SimplexCategory.mk n)) ≃ (coverNerve U).obj n
  /-- The presentation intertwines faces with the nerve's face operators. -/
  face_compat : ∀ (n : ℕ) (t : Fin (n + 2)) (x : sset.obj (op (SimplexCategory.mk (n + 1)))),
    simplexEquiv n (sset.map (SimplexCategory.δ t).op x)
      = (coverNerve U).face t (simplexEquiv (n + 1) x)

/-- **WP12, the hardened nerve-theorem interface.**

*Task-9 classification: `SUPERSEDED_BY_GEOMETRIC_COMPARISON` (realization half).*  Task 9
constructs the canonical nerve presentation `NerveGeom.canonicalNervePresentation` and fixes
the realization to `NerveGeom.coverNerveRealization 𝓤`, so the remaining edge is exactly a
homotopy equivalence `|N(𝓤)| ≃ X` (`NerveGeom.NerveTheoremData`).  This structure is retained
for provenance; new work should use `NerveGeom.NerveTheoremData`, which has no free
`realization` field at all.

A realization *of the nerve*: the space is
required to be the geometric realization `|N(𝓤)| = SSet.toTop.obj` of a simplicial set
presenting the nerve, and only then is a homotopy equivalence with the base asked for.

Compare `GoodCoverSpec.NerveRealization`, which permitted an arbitrary space; the map
`toNerveRealization` below shows that this specification is strictly stronger. -/
structure NerveRealizationSpec (U : ι → Set (X : Type u)) where
  /-- A simplicial set presenting the combinatorial nerve. -/
  presentation : NervePresentation U
  /-- The realization, as a space. -/
  realization : TopCat.{u}
  /-- …which must be the geometric realization of the presenting simplicial set. -/
  realization_eq : realization = SSet.toTop.obj presentation.sset
  /-- The nerve-theorem homotopy equivalence with the base. -/
  equiv : ContinuousMap.HomotopyEquiv (realization : Type u) (X : Type u)

namespace NerveRealizationSpec

variable {U : ι → Set (X : Type u)} (R : NerveRealizationSpec U)

/-- The realization of a hardened nerve realization *is* the geometric realization of a
simplicial set presenting the nerve of the cover.  (This is a field; it is restated as a
theorem so that downstream documentation can cite it.) -/
theorem realization_is_geometric_realization :
    R.realization = SSet.toTop.obj R.presentation.sset := R.realization_eq

/-- Every hardened nerve realization is in particular a Task-7 `NerveRealization`; the converse
fails, which is exactly the point of the hardening. -/
def toNerveRealization : NerveRealization U where
  realization := R.realization
  equiv := R.equiv

end NerveRealizationSpec

/-! ## WP13 : the hardened simplicial-to-singular specification -/

/-- **A map of cochain complexes** from the simplicial `ℤ₂`-cochain complex of a presimplicial
set to the native singular `ℤ₂`-cochain complex of a space.  The commutation with the two
coboundaries is part of the data and is imposed *before* any descent to cohomology. -/
structure SimplicialSingularCochainMap (S : Presimplicial.{u}) (R : TopCat.{u}) where
  /-- The degreewise linear comparison of cochains. -/
  map : ∀ n : ℕ, S.Cochain n →ₗ[ZMod 2] Mod2Cohomology.Cochain R n
  /-- Compatibility with the coboundaries. -/
  comm : ∀ (n : ℕ) (c : S.Cochain n),
    map (n + 1) (S.d n c) = Mod2Cohomology.d R n (map n c)

namespace SimplicialSingularCochainMap

variable {S : Presimplicial.{u}} {R : TopCat.{u}} (Φ : SimplicialSingularCochainMap S R)

theorem map_mem_cocycles (n : ℕ) {c : S.Cochain n} (hc : c ∈ S.cocycles n) :
    Φ.map n c ∈ Mod2Cohomology.cocycles R n := by
  have hc' : S.d n c = 0 := hc
  show Mod2Cohomology.d R n (Φ.map n c) = 0
  rw [← Φ.comm n c, hc', map_zero]

/-- The induced map on cocycles. -/
def cocyclesMap (n : ℕ) : S.cocycles n →ₗ[ZMod 2] Mod2Cohomology.cocycles R n :=
  (Φ.map n).restrict (fun _ hc => Φ.map_mem_cocycles n hc)

theorem map_mem_coboundaries (n : ℕ) {c : S.Cochain n} (hc : c ∈ S.coboundaries n) :
    Φ.map n c ∈ Mod2Cohomology.coboundaries R n := by
  cases n with
  | zero =>
      rw [Presimplicial.coboundaries, Submodule.mem_bot] at hc
      rw [Mod2Cohomology.coboundaries_zero, Submodule.mem_bot, hc, map_zero]
  | succ m =>
      obtain ⟨b, rfl⟩ := hc
      exact ⟨Φ.map m b, (Φ.comm m b).symm⟩

/-- **The induced map on cohomology**, obtained by descent from the cochain comparison.  Any
comparison isomorphism worth the name has to be *this* map. -/
def Hmap (n : ℕ) : S.Cohomology n →ₗ[ZMod 2] Mod2Cohomology.Cohomology R n :=
  Submodule.mapQ (S.coboundariesIn n) (Mod2Cohomology.coboundariesIn R n) (Φ.cocyclesMap n)
    (fun _ hz => Φ.map_mem_coboundaries n hz)

@[simp] theorem Hmap_class (n : ℕ) (z : S.cocycles n) :
    Φ.Hmap n (S.cohomologyClass z) = Mod2Cohomology.mk (Φ.cocyclesMap n z) := rfl

end SimplicialSingularCochainMap

/-- **WP13, the hardened simplicial-to-singular comparison interface.**

*Task-9 classification: `SUPERSEDED_BY_GEOMETRIC_COMPARISON`.*  This structure is retained for
provenance and backward compatibility only.  It still allows an *arbitrary* cochain map, with
no relation to the geometric realization of the nerve.  Task 9 constructs the canonical
geometric comparison — the characteristic simplices of `SSet.toTop.obj (coverNerveSSet 𝓤)`,
the induced chain map, its transpose cochain map and the induced map on cohomology — and
`NerveGeom.GeometricComparison` asserts bijectivity of *that* map and of no other.  Downstream
certification must use `NerveGeom.GeometricComparison`; see
`RequestProject.Spine.Nerve.Cochain.ComparisonSpec`.

A comparison consists
of an explicit cochain-complex map together with the assertion that the map it *induces* on
cohomology is bijective.  An arbitrary linear equivalence of cohomology no longer satisfies the
specification: it must come from a cochain map compatible with the coboundaries. -/
structure SimplicialSingularComparisonSpec (S : Presimplicial.{u}) (R : TopCat.{u}) where
  /-- The cochain-level comparison. -/
  cochain : SimplicialSingularCochainMap S R
  /-- The induced map on cohomology is bijective in every degree. -/
  bijective : ∀ n : ℕ, Function.Bijective (cochain.Hmap n)

namespace SimplicialSingularComparisonSpec

variable {S : Presimplicial.{u}} {R : TopCat.{u}} (C : SimplicialSingularComparisonSpec S R)

/-- The comparison isomorphism, *induced by* the cochain comparison. -/
def equiv (n : ℕ) : S.Cohomology n ≃ₗ[ZMod 2] Mod2Cohomology.Cohomology R n :=
  LinearEquiv.ofBijective (C.cochain.Hmap n) (C.bijective n)

@[simp] theorem equiv_apply (n : ℕ) (q : S.Cohomology n) :
    C.equiv n q = C.cochain.Hmap n q := rfl

/-- Every hardened comparison yields, in degree two, the Task-7 `SimplicialSingularComparison`
datum; the converse fails. -/
def toSimplicialSingularComparison {U : ι → Set (X : Type u)}
    (C : SimplicialSingularComparisonSpec (coverNerve U) R) :
    SimplicialSingularComparison U R where
  compare := C.equiv 2

end SimplicialSingularComparisonSpec

/-! ## The hardened comparison, with no homotopy-invariance assumption -/

/-- **WP14.**

*Task-9 classification: `SUPERSEDED_BY_GEOMETRIC_COMPARISON`.*  The Task-9 replacement is
`NerveGeom.fullComparison`, built from `NerveGeom.GeometricComparison` (bijectivity of the
canonical geometric map) and `NerveGeom.NerveTheoremData` (`|N(𝓤)| ≃ X`).

The hardened fixed-cover comparison datum.  Compared with Task 7's
`GoodCoverSpec.Comparison` it has

* a nerve realization genuinely tied to `N(𝓤)` (WP12),
* a simplicial-to-singular comparison genuinely induced by a cochain map (WP13),
* and **no homotopy-invariance field at all**, because that edge is now a theorem (WP11).

Two blocked edges remain, and they are exactly the two fields. -/
structure HardenedComparison (U : ι → Set (X : Type u)) where
  /-- The nerve realization (WP12; still blocked, but now honestly specified). -/
  nerve : NerveRealizationSpec U
  /-- The simplicial-to-singular comparison (WP13; still blocked, but now honestly specified). -/
  simplicial : SimplicialSingularComparisonSpec (coverNerve U) nerve.realization

namespace HardenedComparison

variable {U : ι → Set (X : Type u)} (C : HardenedComparison U)

/-- **The hardened comparison `Φ_𝓤 : Ȟⁿ(𝓤;ℤ₂) ≅ Hⁿ_sing(X;ℤ₂)`**, in every degree.

The last arrow is the *native* homotopy invariance of Task 8, applied to the nerve-theorem
equivalence — no free-standing transport datum occurs. -/
def equiv (n : ℕ) : CechZ2.Cohomology U n ≃ₗ[ZMod 2] Mod2Cohomology.Cohomology X n :=
  (cechCohomologyEquiv U n).symm ≪≫ₗ C.simplicial.equiv n ≪≫ₗ
    (Mod2Cohomology.homotopyEquivCohomology C.nerve.equiv n).symm

theorem equiv_eq_zero_iff (n : ℕ) (q : CechZ2.Cohomology U n) :
    C.equiv n q = 0 ↔ q = 0 :=
  (C.equiv n).map_eq_zero_iff

end HardenedComparison

/-! ## The Spin-lift class transported along the hardened comparison -/

section SpinTransport

open CechSpinLift CechSpinZ2 GoodCoverZ2 SpinCore LorentzFrames NullSectorTask28

variable {𝓤 : CechCover (X : Type u) ι} {T : VisibleCocycle (↥GLor) 𝓤}

/-- **The Task-6 Spin-lift class transported into `H²_sing(X;ℤ₂)` along a hardened
comparison.**  Compared with `GoodCoverSpec.spinLiftSingularClass` this consumes no
homotopy-invariance datum: the last arrow of the comparison is the Task-8 theorem. -/
def spinLiftSingularClassHardened (C : HardenedComparison 𝓤.U) (h : IsGoodCover 𝓤.U)
    (D : SpinLiftFamily internalSpinProjection T) : Mod2Cohomology.Cohomology X 2 :=
  C.equiv 2 (spinLiftCechClassGood h D)

/-- The transported class does not depend on the chosen local Spin lifts. -/
theorem spinLiftSingularClassHardened_lift_independent (C : HardenedComparison 𝓤.U)
    (h : IsGoodCover 𝓤.U) (D D' : SpinLiftFamily internalSpinProjection T) :
    spinLiftSingularClassHardened C h D = spinLiftSingularClassHardened C h D' := by
  unfold spinLiftSingularClassHardened
  rw [spinLiftCechClassGood_lift_independent h D D']

/-- **The vanishing theorem, hardened singular form.** -/
theorem spinLiftSingularClassHardened_eq_zero_iff (C : HardenedComparison 𝓤.U)
    (h : IsGoodCover 𝓤.U) (D : SpinLiftFamily internalSpinProjection T) :
    spinLiftSingularClassHardened C h D = 0 ↔
      ∃ D' : SpinLiftFamily internalSpinProjection T, D'.IsCoherent := by
  rw [spinLiftSingularClassHardened, HardenedComparison.equiv_eq_zero_iff,
    spinLiftCechClassGood_eq_zero_iff h D]

variable {Fib : ↥X → Type u} [∀ x, AddCommGroup (Fib x)] [∀ x, Module ℝ (Fib x)]
  {Φ : LorentzFrameData (↥X) Fib ι}

/-- The Lorentz-frame Spin-lift obstruction as a singular mod-2 class, along a hardened
comparison. -/
def frameSingularClassHardened (C : HardenedComparison Φ.cover.U) (h : IsGoodCover Φ.cover.U)
    (D : FrameSpinLifts Φ) : Mod2Cohomology.Cohomology X 2 :=
  C.equiv 2 (frameCechClassGood h D)

/-- **The hardened conditional endpoint.**  On a good cover, and given the two remaining
comparison inputs (nerve realization and simplicial-to-singular comparison, both now honestly
specified), the singular class vanishes **iff** the Lorentz frame data admits a Spin
structure. -/
theorem frameSingularClassHardened_eq_zero_iff_spinStructure (C : HardenedComparison Φ.cover.U)
    (h : IsGoodCover Φ.cover.U) (D : FrameSpinLifts Φ) :
    frameSingularClassHardened C h D = 0 ↔ Nonempty (SpinFrameStructure Φ) := by
  rw [frameSingularClassHardened, HardenedComparison.equiv_eq_zero_iff,
    frameCechClassGood_eq_zero_iff_spinStructure h D]

end SpinTransport

end GoodCoverSpec
