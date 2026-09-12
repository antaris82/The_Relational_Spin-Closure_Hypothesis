import RequestProject.Spine.Nerve.Cochain.CochainMap
import RequestProject.Spine.GoodCover.HardenedSpec

/-!
# Task 9, WP8–WP14 : what the geometric comparison still needs, and everything downstream of it

## WP8 — which standard theorem is required, and what the pinned library provides

The construction is complete up to and including the induced map

`NerveGeom.geometricHmap 𝓤 n : Hⁿ_sing(|N(𝓤)|;ℤ₂) → Ȟⁿ(𝓤;ℤ₂) = Hⁿ_simp(N(𝓤);ℤ₂)`,

which is the descent of the genuine cochain map `J*` of WP7 (itself the transpose of the chain
map `J` of WP6, itself built from the canonical characteristic simplices of WP5).  What remains
is the classical statement

> `J*` induces an isomorphism on cohomology in every degree,

equivalently that `J : C_*^simp(S) → C_*^sing(|S|)` is a quasi-isomorphism for every simplicial
set `S`.  The standard routes are

1. **skeletal induction** on `S`: `|S|` is a CW complex whose `n`-skeleton is obtained from the
   `(n-1)`-skeleton by attaching one `n`-cell per nondegenerate `n`-simplex, and the cellular
   chain complex of that CW structure *is* the normalized chain complex of `S`;
2. **acyclic models**, comparing `J` with the identity on the models `Δ[n]` (which requires
   knowing that `|Δ[n]|` is contractible and that both functors are free/acyclic on models);
3. **Dold–Kan plus the normalization theorem**, reducing the unnormalized complex to the
   normalized one, then route 1 or 2.

Every one of these needs machinery that pinned Mathlib does **not** have: a CW/cellular
structure on `SSet.toTop.obj S`, excision or Mayer–Vietoris for singular homology, homotopy
invariance *of the singular chain functor at chain level*, or the acyclic-model theorem.  What
the pinned library does supply is listed in the WP4 table of
`RequestProject.Spine.Nerve.Basic.Realization`, plus `AlgebraicTopology.SSet.singularChainComplexFunctor`
(definitions only; the only computation available is for totally disconnected spaces).

Classification of the comparison theorem: **`BLOCKED`**.  A degree-2-only route is *not*
materially smaller: all three standard proofs are global in the degree, and the degree-2
statement already needs the `2`-skeleton, the `3`-skeleton and excision.

## WP9 — status

`NerveGeom.GeometricComparison` below is an **explicitly conditional specification**, not a
theorem, and it is *not* a `Prop`-valued field hiding a gap: it asserts bijectivity of the
concrete map `geometricHmap`, which is fully constructed here.  It is consumed only by
declarations whose names and docstrings make the conditionality explicit.  Nothing in the
production Spine consumes it as if proved.

## WP11/WP12 — supersession and hardening

* `NerveGeom.canonicalNervePresentation` **constructs** the Task-8 `NervePresentation` — the
  simplicial-set half of the hardened nerve-realization interface is no longer blocked.
* `NerveGeom.NerveTheoremData` is the remaining edge, in the mandated shape `|N(𝓤)| ≃ X`, with
  `|N(𝓤)|` *fixed* to `NerveGeom.coverNerveRealization 𝓤`; no free `realization : TopCat`
  field exists.  `NerveTheoremData.toNerveRealizationSpec` shows it inhabits the Task-8
  hardened interface.
* The Task-7/Task-8 comparison interfaces `GoodCoverSpec.SimplicialSingularComparison` and
  `GoodCoverSpec.SimplicialSingularComparisonSpec` are hereby classified
  `SUPERSEDED_BY_GEOMETRIC_COMPARISON`: downstream certification must use
  `NerveGeom.GeometricComparison`, whose only degree of freedom is the *truth* of a statement
  about the canonical map.
-/

noncomputable section

namespace NerveGeom

open CategoryTheory Opposite CechZ2 SimplexCategory

universe u

variable {X : TopCat.{u}} {ι : Type u}

/-! ## WP12 : the canonical nerve presentation and the genuine shape of the nerve theorem -/

/-- **WP12, constructed.**  The canonical simplicial set of WP2 presents the Task-7
combinatorial nerve, on the nose: same simplices, same faces.  This *inhabits* the Task-8
hardened `NervePresentation` interface, so that half of the hardened nerve-realization
specification is no longer a hypothesis. -/
def canonicalNervePresentation (U : ι → Set (X : Type u)) : GoodCoverSpec.NervePresentation U where
  sset := coverNerveSSet U
  simplexEquiv _ := Equiv.refl _
  face_compat _ _ _ := rfl

/-- **WP12, the remaining nerve-theorem edge, in the mandated shape.**

`BLOCKED`.  The only datum is a homotopy equivalence between the **actual geometric
realization of the actual simplicial cover nerve** and the base space.  There is no
`realization : TopCat` field: an unrelated space `R` cannot inhabit this structure. -/
structure NerveTheoremData (U : ι → Set (X : Type u)) where
  /-- The nerve-theorem homotopy equivalence `|N(𝓤)| ≃ X`. -/
  equiv : ContinuousMap.HomotopyEquiv (coverNerveRealization U : Type u) (X : Type u)

/-- Every `NerveTheoremData` inhabits the Task-8 hardened nerve-realization interface, with
the canonical presentation and with `realization_eq` holding by `rfl`. -/
def NerveTheoremData.toNerveRealizationSpec {U : ι → Set (X : Type u)}
    (D : NerveTheoremData U) : GoodCoverSpec.NerveRealizationSpec U where
  presentation := canonicalNervePresentation U
  realization := coverNerveRealization U
  realization_eq := rfl
  equiv := D.equiv

/-! ## WP9 : the comparison isomorphism, as an explicitly conditional specification -/

/-- **WP9, `BLOCKED`.  A conditional specification, never a theorem.**

The single field asserts that the *canonical geometric map* `NerveGeom.geometricHmap`, built in
WP5–WP7 from the characteristic simplices of the realization, is bijective in every degree.
It is therefore **not** an arbitrary linear equivalence and **not** a free-standing
cohomology-level datum: an inhabitant of this structure is precisely a proof of the standard
simplicial-to-singular comparison theorem for the cover nerve.

No declaration of the production Spine consumes it, and every declaration below that does
consume it says so in its name or docstring.

**TASK 10 STATUS: `SUPERSEDED_BY_TASK10_CHAIN_COMPARISON` as an *input*.**  Task 10 proves
`NerveGeom.ChainHomotopyEquivData.toGeometricComparison`, which *constructs* this structure
from the purely chain-level datum `NerveGeom.ChainHomotopyEquivData` (a chain-homotopy inverse
for the canonical Task-9 `chainMap`).  The structure is retained for provenance and because
the downstream Spin-transport declarations below are phrased in terms of it; new work should
supply the chain-level datum instead, which is strictly closer to the classical theorem.

**TASK 11 CORRECTION (WP3).**  An earlier version of this docstring described
`NerveGeom.ChainHomotopyEquivData` as "strictly weaker to assume" than `GeometricComparison`.
That is wrong and is withdrawn.  The implication proved in Task 10 runs
`ChainHomotopyEquivData U → GeometricComparison U`
(`NerveGeom.ChainHomotopyEquivData.toGeometricComparison`), and no implication in the reverse
direction is proved anywhere in this project.  `ChainHomotopyEquivData` is therefore a
*stronger*, more structured **sufficient** condition: Task 10 replaced an abstract
cohomological comparison assumption by a stronger but structurally deeper sufficient condition
tied to the canonical chain map `J = C_*(η_K)`.  The route-independent target of the whole
line of work remains bijectivity of `NerveGeom.geometricHmap`. -/
structure GeometricComparison {X : Type u} {ι : Type u} (U : ι → Set X) where
  /-- The canonical geometric comparison map is bijective in every degree. -/
  bijective : ∀ n : ℕ, Function.Bijective (geometricHmap U n)

/-- The degree-two fragment of the same specification, recorded separately so that the
engineering scope of a degree-two-only route can be discussed honestly.  It is *not* smaller
mathematically (see the WP8 discussion above). -/
structure GeometricComparison₂ {X : Type u} {ι : Type u} (U : ι → Set X) where
  /-- The canonical geometric comparison map is bijective in degree two. -/
  bijective₂ : Function.Bijective (geometricHmap U 2)

/-- The full specification implies its degree-two fragment. -/
def GeometricComparison.toDegreeTwo {X : Type u} {ι : Type u} {U : ι → Set X}
    (C : GeometricComparison U) : GeometricComparison₂ U :=
  ⟨C.bijective 2⟩

namespace GeometricComparison

variable {Y : Type u} {κ : Type u} {U : κ → Set Y} (C : GeometricComparison U)

/-- The comparison isomorphism `Hⁿ_sing(|N(𝓤)|;ℤ₂) ≅ Ȟⁿ(𝓤;ℤ₂)`, **induced by** the canonical
cochain map of WP7 and by nothing else. -/
def equiv (n : ℕ) :
    Mod2Cohomology.Cohomology (coverNerveRealization U) n ≃ₗ[ZMod 2] CechZ2.Cohomology U n :=
  LinearEquiv.ofBijective (geometricHmap U n) (C.bijective n)

@[simp] theorem equiv_apply (n : ℕ)
    (q : Mod2Cohomology.Cohomology (coverNerveRealization U) n) :
    C.equiv n q = geometricHmap U n q := rfl

/-- The comparison in the Čech-to-singular direction. -/
def equivSymm (n : ℕ) :
    CechZ2.Cohomology U n ≃ₗ[ZMod 2] Mod2Cohomology.Cohomology (coverNerveRealization U) n :=
  (C.equiv n).symm

@[simp] theorem equiv_equivSymm (n : ℕ) (q : CechZ2.Cohomology U n) :
    C.equiv n (C.equivSymm n q) = q := (C.equiv n).apply_symm_apply q

end GeometricComparison

/-! ## WP10 : the Spin-lift class on the realized nerve -/

section SpinTransport

open CechSpinLift CechSpinZ2 GoodCoverZ2 SpinCore LorentzFrames NullSectorTask28

variable {𝓤 : CechCover (X : Type u) ι} {T : VisibleCocycle (↥GLor) 𝓤}

/-- **WP10 (conditional on `GeometricComparison`).**  The genuine Task-6 Spin-lift class
`[z] ∈ Ȟ²(𝓤;ℤ₂)`, transported into the singular mod-2 cohomology of the **realized nerve**
`|N(𝓤)|` along the canonical geometric comparison.  This is *not* a class on the manifold `M`:
transporting it there needs the nerve theorem, which is not available. -/
def spinLiftRealizedClass (C : GeometricComparison 𝓤.U) (h : IsGoodCover 𝓤.U)
    (D : SpinLiftFamily internalSpinProjection T) :
    Mod2Cohomology.Cohomology (coverNerveRealization 𝓤.U) 2 :=
  C.equivSymm 2 (spinLiftCechClassGood h D)

/-- The realized class does not depend on the chosen local Spin lifts. -/
theorem spinLiftRealizedClass_lift_independent (C : GeometricComparison 𝓤.U)
    (h : IsGoodCover 𝓤.U) (D D' : SpinLiftFamily internalSpinProjection T) :
    spinLiftRealizedClass C h D = spinLiftRealizedClass C h D' := by
  unfold spinLiftRealizedClass
  rw [spinLiftCechClassGood_lift_independent h D D']

/-- **WP10, principal.**  `[z]_{|N|} = 0 ⟺ [z]_{Ȟ²} = 0`. -/
theorem spinLiftRealizedClass_eq_zero_iff_cech (C : GeometricComparison 𝓤.U)
    (h : IsGoodCover 𝓤.U) (D : SpinLiftFamily internalSpinProjection T) :
    spinLiftRealizedClass C h D = 0 ↔ spinLiftCechClassGood h D = 0 :=
  (C.equivSymm 2).map_eq_zero_iff

/-- **WP10, second form.**  `[z]_{|N|} = 0 ⟺ coherent Spin transition data exist on the fixed
cover.** -/
theorem spinLiftRealizedClass_eq_zero_iff (C : GeometricComparison 𝓤.U)
    (h : IsGoodCover 𝓤.U) (D : SpinLiftFamily internalSpinProjection T) :
    spinLiftRealizedClass C h D = 0 ↔
      ∃ D' : SpinLiftFamily internalSpinProjection T, D'.IsCoherent := by
  rw [spinLiftRealizedClass_eq_zero_iff_cech, spinLiftCechClassGood_eq_zero_iff h D]

variable {Fib : ↥X → Type u} [∀ x, AddCommGroup (Fib x)] [∀ x, Module ℝ (Fib x)]
  {Φ : LorentzFrameData (↥X) Fib ι}

/-- The Lorentz-frame Spin-lift obstruction as a class on the realized nerve. -/
def frameRealizedClass (C : GeometricComparison Φ.cover.U) (h : IsGoodCover Φ.cover.U)
    (D : FrameSpinLifts Φ) :
    Mod2Cohomology.Cohomology (coverNerveRealization Φ.cover.U) 2 :=
  C.equivSymm 2 (frameCechClassGood h D)

/-- **WP10, frame form.**  The class on the realized nerve vanishes **iff** the Lorentz frame
data admits a Spin structure. -/
theorem frameRealizedClass_eq_zero_iff_spinStructure (C : GeometricComparison Φ.cover.U)
    (h : IsGoodCover Φ.cover.U) (D : FrameSpinLifts Φ) :
    frameRealizedClass C h D = 0 ↔ Nonempty (SpinFrameStructure Φ) := by
  rw [frameRealizedClass, (C.equivSymm 2).map_eq_zero_iff,
    frameCechClassGood_eq_zero_iff_spinStructure h D]

/-! ## WP13 : the reconstructed certification DAG -/

/-- **WP13.**  With the geometric comparison *and* the nerve theorem, the full fixed-good-cover
bridge `Ȟ²(𝓤;ℤ₂) ≅ H²_sing(X;ℤ₂)`.  The last arrow is the **theorem** of Task 8 (homotopy
invariance), applied to the nerve-theorem equivalence; the middle arrow is the canonical
geometric comparison.  Exactly one edge — the nerve theorem — is still an assumption, and it
now has the mandated shape `|N(𝓤)| ≃ X`. -/
def fullComparison (C : GeometricComparison (𝓤.U)) (N : NerveTheoremData 𝓤.U) (n : ℕ) :
    CechZ2.Cohomology 𝓤.U n ≃ₗ[ZMod 2] Mod2Cohomology.Cohomology X n :=
  (C.equiv n).symm ≪≫ₗ (Mod2Cohomology.homotopyEquivCohomology N.equiv n).symm

theorem fullComparison_eq_zero_iff (C : GeometricComparison 𝓤.U) (N : NerveTheoremData 𝓤.U)
    (n : ℕ) (q : CechZ2.Cohomology 𝓤.U n) : fullComparison C N n q = 0 ↔ q = 0 :=
  (fullComparison C N n).map_eq_zero_iff

end SpinTransport

/-! ## WP14 : the exact remaining blocker -/

/-- **WP14.**  The exact formal hypotheses of the nerve theorem that would produce a
`NerveGeom.NerveTheoremData`.  This is a *statement*, packaged as a `Prop`, not an assumption:
nothing consumes it.  It is the target of a future task.

The hypotheses are spelled out individually rather than bundled as "good cover":

* `hopen` — every member of the cover is open;
* `hcover` — the members cover the space;
* `hcontr` — every **nonempty finite** intersection of members is contractible.  (This is
  exactly `GoodCoverZ2.IsGoodCover`, stated on the nerve tuples the Čech complex uses; empty
  intersections are excluded, and no condition is imposed on them.)
* `hparacompact` — the base is paracompact.  Together with `hopen`/`hcover` this yields a
  subordinate partition of unity, i.e. the cover is **numerable**, which is what the classical
  proof (Weil / Segal / Borsuk) actually consumes: the map `|N(𝓤)| → X` is built from a
  partition of unity, and the homotopy inverse uses local finiteness of its support family.

Hausdorffness is **not** needed for the statement.  Local finiteness of the cover is implied
by paracompactness *after* refinement, and is not assumed separately.

**CORRECTED BY TASK 10, WP0.**  An earlier version of this docstring claimed that `hopen`,
`hcover` and `hparacompact` are "available in the Task-4 manifold model", because a manifold
charted on a finite-dimensional normed space would be second countable and hence paracompact.
That claim was **false** and is withdrawn.  Task 4 assumes only `[TopologicalSpace M]`,
`[ChartedSpace LorentzCarrier M]` and (where used) `[IsManifold carrierModel ⊤ M]`, and the
project derives *none* of Hausdorffness, second countability, paracompactness, metrisability,
numerability of an arbitrary cover, or existence of a good cover.  The implication "charted on
the four-dimensional carrier ⟹ second countable" is refuted at theorem level by
`SpineTask10.chartedNotSecondCountable` in
`RequestProject.Spine.Nerve.Audit.ManifoldAssumptions`.

Corrected status of the individual hypotheses of the nerve theorem:

| hypothesis | required by the theorem | currently derived in the project |
| --- | --- | --- |
| `hopen`, `hcover` | yes | only for a cover that is *given* as open and covering |
| `hparacompact` | yes (numerability) | **no** |
| `hcontr` (good cover) | yes | **no** (Task 7: the Riemannian convexity input is absent) |
| Hausdorffness | no | no |

The Task-7 module `RequestProject.Spine.GoodCover.ManifoldCovers` supplies contractible
*refinements*, but not contractibility of the finite intersections. -/
def NerveTheoremStatement (X : TopCat.{u}) (ι : Type u) : Prop :=
  ∀ (U : ι → Set (X : Type u)), (∀ i, IsOpen (U i)) → (⋃ i, U i) = Set.univ →
    ParacompactSpace (X : Type u) → GoodCoverZ2.IsGoodCover U →
    Nonempty (NerveTheoremData (X := X) U)

/-- **WP14, the second remaining blocker**, stated for the record: the comparison theorem
itself.  Again a `Prop`, consumed by nothing. -/
def GeometricComparisonStatement {Y : Type u} {κ : Type u} (U : κ → Set Y) : Prop :=
  Nonempty (GeometricComparison U)

end NerveGeom
