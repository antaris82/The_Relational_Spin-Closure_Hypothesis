import RequestProject.Spine.Nerve.Cochain.Dualization
import RequestProject.Spine.Nerve.Cochain.ComparisonSpec

/-!
# Task 10, WP5/WP7/WP10 : the comparison theorem reduced to one chain-level statement

Task 9 left the geometric comparison

`NerveGeom.geometricHmap 𝓤 n : Hⁿ_sing(|N(𝓤)|;ℤ₂) → Ȟⁿ(𝓤;ℤ₂)`

as a conditional specification.  This module removes every *cohomological* and every
*dualisation* step from that condition, leaving exactly one chain-level statement.

## The reduction

`NerveGeom.ChainHomotopyEquivData 𝓤` packages precisely the classical content

`J : C_*^simp(N(𝓤);ℤ₂) ⇄ C_*^sing(|N(𝓤)|;ℤ₂) : R`,   `R J ≃ id`,  `J R ≃ id`,

with **`J` the Task-9 `NerveGeom.chainMap`** — i.e. by `NerveGeom.chainMap_eq_unitChainMap`
the free `ℤ₂`-linearisation of the adjunction unit `η : N(𝓤) ⟶ Sing|N(𝓤)|`.  No abstract
quasi-isomorphism may be substituted for it: the forward map is *not* a field of the
structure, and there is no field asserting that anything is bijective or a
quasi-isomorphism.

The principal theorem

`NerveGeom.geometricHmap_bijective_of_chainHomotopyEquiv`

proves that the **existing** `geometricHmap 𝓤 n` is bijective in every degree.  The proof is
elementary and completely explicit:

* the chain homotopies are transposed with `NerveGeom.dualOf`, an exact contravariant
  operation defined by a formula (`RequestProject.Spine.Nerve.Cochain.Dualization`).  **No universal
  coefficient theorem is used and exactness of dualisation is proved, not assumed** — over
  `ℤ₂` the Spine cochain module `(σ ↦ ℤ₂)` is literally the dual of the free chain module;
* `dualOf ∂ = δ` and `dualOf J = J*` on the nose, so the dualised homotopies are homotopies
  for the *existing* Task-5/6/7 cochain complexes and for the *existing* cochain map;
* the usual diagram chase then gives surjectivity and injectivity of the induced map on
  cohomology in every degree, including degree `0` where `B⁰ = 0`.

Consequently the remaining blocker is `NerveGeom.ChainComparisonStatement`, a purely
chain-level statement.  Task 10 does **not** prove it; see `TASK10_AUDIT.md` for the route
audit and for why pinned Mathlib v4.28.0 supplies none of the required machinery.

## Task 11 status corrections

1. `ChainHomotopyEquivData` is a **stronger** sufficient condition than the Task-9
   `GeometricComparison`, not a weaker one: only
   `ChainHomotopyEquivData U → GeometricComparison U` is proved.  Task 10 replaced an abstract
   cohomological comparison assumption by a stronger but structurally deeper sufficient
   condition tied to the canonical chain map `J = C_*(η_K)`.
2. The route-independent target is `∀ n, Function.Bijective (NerveGeom.geometricHmap 𝓤 n)`.
   `ChainComparisonStatement` is the *preferred stronger* sufficient endpoint; a weaker
   sufficient route (for example a bare quasi-isomorphism statement plus a coefficient
   argument) is not excluded.
3. The compact-support / finite-subcomplex theorem is **route-specific**: it is the first
   missing prerequisite of the proposed Acyclic-Models route, and not the unique logical
   blocker.

See `TASK11_UPSTREAM_DELTA_AUDIT.md` for the audit of current upstream Mathlib against the
pinned commit, which found no upstream theorem closing this gap.
-/

noncomputable section

namespace NerveGeom

open CategoryTheory Opposite CechZ2 SimplexCategory

universe w u

/-! ## Characteristic two -/

/-- In a `ℤ₂`-module every element is its own negative; equivalently `x + x = 0`. -/
theorem z2_add_self {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) : x + x = 0 := by
  have h := (two_smul (ZMod 2) x).symm
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_smul] at h
  exact h

theorem z2_neg_eq_self {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) : -x = x := by
  have h := z2_add_self x
  have := congrArg (fun y => -x + y) h
  simpa [← add_assoc] using this.symm

theorem z2_sub_eq_add {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x y : M) :
    x - y = x + y := by
  rw [sub_eq_add_neg, z2_neg_eq_self]

/-! ## Cohomology-class lemmas for presimplicial cochain complexes -/

theorem presimplicialClass_eq_zero_iff (S : NerveZ2.Presimplicial.{u}) {n : ℕ}
    (z : S.cocycles n) :
    S.cohomologyClass z = 0 ↔ (z : S.Cochain n) ∈ S.coboundaries n := by
  rw [NerveZ2.Presimplicial.cohomologyClass, Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

theorem presimplicialClass_surjective (S : NerveZ2.Presimplicial.{u}) (n : ℕ) :
    Function.Surjective (S.cohomologyClass : S.cocycles n → S.Cohomology n) :=
  Submodule.Quotient.mk_surjective _

theorem presimplicialClass_eq_iff (S : NerveZ2.Presimplicial.{u}) {n : ℕ}
    (z w : S.cocycles n) :
    S.cohomologyClass z = S.cohomologyClass w ↔
      ((z : S.Cochain n) - (w : S.Cochain n)) ∈ S.coboundaries n := by
  rw [NerveZ2.Presimplicial.cohomologyClass, NerveZ2.Presimplicial.cohomologyClass,
    Submodule.Quotient.eq]
  exact Iff.rfl

/-! ## The chain-level comparison datum -/

variable {X : Type w} {ι : Type u}

/-- **WP7.  The exact chain-level datum the geometric comparison still needs.**

A chain-homotopy inverse for the Task-9 chain map `J = NerveGeom.chainMap 𝓤`, together with
the two homotopies.  All identities are written additively: over `ℤ₂` the classical
`∂h + h∂ = id - RJ` reads `∂h + h∂ = id + RJ`.

The forward map is *not* a field: it is fixed to be the canonical `chainMap`, hence (by
`chainMap_eq_unitChainMap`) the linearisation of the adjunction unit. -/
structure ChainHomotopyEquivData (U : ι → Set X) where
  /-- The chain-homotopy inverse `R : C_*^sing(|N(𝓤)|) → C_*^simp(N(𝓤))`. -/
  inv : ∀ n : ℕ,
    SingChain (coverNerveRealization U) n →ₗ[ZMod 2] SimpChain U n
  /-- `R` is a chain map. -/
  inv_comm : ∀ n : ℕ,
    (inv n).comp (singBoundary (coverNerveRealization U) n)
      = (simpBoundary U n).comp (inv (n + 1))
  /-- The homotopy `h` witnessing `R J ≃ id` on simplicial chains. -/
  htpySimp : ∀ n : ℕ, SimpChain U n →ₗ[ZMod 2] SimpChain U (n + 1)
  /-- `∂h = id + RJ` in degree `0` (there is no `h₋₁`). -/
  htpySimp_zero :
    (simpBoundary U 0).comp (htpySimp 0)
      = LinearMap.id + (inv 0).comp (chainMap U 0)
  /-- `∂h + h∂ = id + RJ` in positive degree. -/
  htpySimp_succ : ∀ n : ℕ,
    (simpBoundary U (n + 1)).comp (htpySimp (n + 1))
        + (htpySimp n).comp (simpBoundary U n)
      = LinearMap.id + (inv (n + 1)).comp (chainMap U (n + 1))
  /-- The homotopy `g` witnessing `J R ≃ id` on singular chains. -/
  htpySing : ∀ n : ℕ,
    SingChain (coverNerveRealization U) n →ₗ[ZMod 2]
      SingChain (coverNerveRealization U) (n + 1)
  /-- `∂g = id + JR` in degree `0`. -/
  htpySing_zero :
    (singBoundary (coverNerveRealization U) 0).comp (htpySing 0)
      = LinearMap.id + (chainMap U 0).comp (inv 0)
  /-- `∂g + g∂ = id + JR` in positive degree. -/
  htpySing_succ : ∀ n : ℕ,
    (singBoundary (coverNerveRealization U) (n + 1)).comp (htpySing (n + 1))
        + (htpySing n).comp (singBoundary (coverNerveRealization U) n)
      = LinearMap.id + (chainMap U (n + 1)).comp (inv (n + 1))

/-- **The remaining blocker of Task 10**, as a `Prop`: the Task-9 chain map is a
chain-homotopy equivalence.  Nothing in the Spine assumes it. -/
def ChainComparisonStatement (U : ι → Set X) : Prop :=
  Nonempty (ChainHomotopyEquivData U)

namespace ChainHomotopyEquivData

variable {U : ι → Set X} (D : ChainHomotopyEquivData U)

/-- The dualised comparison `Ψ = R* : Cⁿ_simp(N(𝓤);ℤ₂) → Cⁿ_sing(|N(𝓤)|;ℤ₂)`. -/
def cochainInv (n : ℕ) :
    (underlyingPresimplicial (coverNerveSSet U)).Cochain n →ₗ[ZMod 2]
      Mod2Cohomology.Cochain (coverNerveRealization U) n :=
  dualOf (D.inv n)

/-- The dualised simplicial homotopy, of cohomological degree `-1`. -/
def cochainHtpySimp (n : ℕ) :
    (underlyingPresimplicial (coverNerveSSet U)).Cochain (n + 1) →ₗ[ZMod 2]
      (underlyingPresimplicial (coverNerveSSet U)).Cochain n :=
  dualOf (D.htpySimp n)

/-- The dualised singular homotopy, of cohomological degree `-1`. -/
def cochainHtpySing (n : ℕ) :
    Mod2Cohomology.Cochain (coverNerveRealization U) (n + 1) →ₗ[ZMod 2]
      Mod2Cohomology.Cochain (coverNerveRealization U) n :=
  dualOf (D.htpySing n)

/-- `Ψ` is a map of cochain complexes: `Ψ δ_simp = δ_sing Ψ`. -/
theorem cochainInv_comm (n : ℕ) :
    (D.cochainInv (n + 1)).comp ((underlyingPresimplicial (coverNerveSSet U)).d n)
      = (Mod2Cohomology.d (coverNerveRealization U) n).comp (D.cochainInv n) := by
  have h := congrArg dualOf (D.inv_comm n)
  rw [dualOf_comp, dualOf_comp, dualOf_simpBoundary, dualOf_singBoundary] at h
  exact h.symm

/-- The dualised degree-zero simplicial homotopy identity `k δ = id + J* Ψ`. -/
theorem cochainHtpySimp_zero :
    (D.cochainHtpySimp 0).comp ((underlyingPresimplicial (coverNerveSSet U)).d 0)
      = LinearMap.id + ((geometricCochainMap U).map 0).comp (D.cochainInv 0) := by
  have h := congrArg dualOf D.htpySimp_zero
  rw [dualOf_comp, dualOf_simpBoundary, dualOf_add, dualOf_id, dualOf_comp,
    dualOf_chainMap] at h
  exact h

/-- The dualised positive-degree simplicial homotopy identity. -/
theorem cochainHtpySimp_succ (n : ℕ) :
    (D.cochainHtpySimp (n + 1)).comp
        ((underlyingPresimplicial (coverNerveSSet U)).d (n + 1))
      + ((underlyingPresimplicial (coverNerveSSet U)).d n).comp (D.cochainHtpySimp n)
      = LinearMap.id + ((geometricCochainMap U).map (n + 1)).comp (D.cochainInv (n + 1)) := by
  have h := congrArg dualOf (D.htpySimp_succ n)
  rw [dualOf_add, dualOf_comp, dualOf_comp, dualOf_simpBoundary, dualOf_simpBoundary,
    dualOf_add, dualOf_id, dualOf_comp, dualOf_chainMap] at h
  exact h

/-- The dualised degree-zero singular homotopy identity `k δ = id + Ψ J*`. -/
theorem cochainHtpySing_zero :
    (D.cochainHtpySing 0).comp (Mod2Cohomology.d (coverNerveRealization U) 0)
      = LinearMap.id + (D.cochainInv 0).comp ((geometricCochainMap U).map 0) := by
  have h := congrArg dualOf D.htpySing_zero
  rw [dualOf_comp, dualOf_singBoundary, dualOf_add, dualOf_id, dualOf_comp,
    dualOf_chainMap] at h
  exact h

/-- The dualised positive-degree singular homotopy identity. -/
theorem cochainHtpySing_succ (n : ℕ) :
    (D.cochainHtpySing (n + 1)).comp (Mod2Cohomology.d (coverNerveRealization U) (n + 1))
      + (Mod2Cohomology.d (coverNerveRealization U) n).comp (D.cochainHtpySing n)
      = LinearMap.id + (D.cochainInv (n + 1)).comp ((geometricCochainMap U).map (n + 1)) := by
  have h := congrArg dualOf (D.htpySing_succ n)
  rw [dualOf_add, dualOf_comp, dualOf_comp, dualOf_singBoundary, dualOf_singBoundary,
    dualOf_add, dualOf_id, dualOf_comp, dualOf_chainMap] at h
  exact h

end ChainHomotopyEquivData

/-! ## The comparison map is bijective, given the chain datum -/

/-- Surjectivity of the induced map on cohomology. -/
theorem Hmap_surjective {U : ι → Set X} (D : ChainHomotopyEquivData U) (n : ℕ) :
    Function.Surjective ((geometricCochainMap U).Hmap n) := by
  intro q
  obtain ⟨c, rfl⟩ :=
    presimplicialClass_surjective (underlyingPresimplicial (coverNerveSSet U)) n q
  have hc : (underlyingPresimplicial (coverNerveSSet U)).d n
      (c : (underlyingPresimplicial (coverNerveSSet U)).Cochain n) = 0 := c.2
  have hcm := congrFun (congrArg DFunLike.coe (D.cochainInv_comm n))
    (c : (underlyingPresimplicial (coverNerveSSet U)).Cochain n)
  simp only [LinearMap.comp_apply] at hcm
  have hdf : Mod2Cohomology.d (coverNerveRealization U) n
      (D.cochainInv n (c : (underlyingPresimplicial (coverNerveSSet U)).Cochain n)) = 0 := by
    rw [← hcm, hc, map_zero]
  refine ⟨Mod2Cohomology.mk ⟨_, hdf⟩, ?_⟩
  rw [SingularToSimplicialCochainMap.Hmap_class, presimplicialClass_eq_iff]
  have key : ((geometricCochainMap U).map n
        (D.cochainInv n (c : (underlyingPresimplicial (coverNerveSSet U)).Cochain n)))
      - (c : (underlyingPresimplicial (coverNerveSSet U)).Cochain n)
      ∈ (underlyingPresimplicial (coverNerveSSet U)).coboundaries n := by
    cases n with
    | zero =>
        have h := congrFun (congrArg DFunLike.coe D.cochainHtpySimp_zero)
          (c : (underlyingPresimplicial (coverNerveSSet U)).Cochain 0)
        simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_coe, id_eq] at h
        rw [hc, map_zero] at h
        have h0 : (c : (underlyingPresimplicial (coverNerveSSet U)).Cochain 0)
            + (geometricCochainMap U).map 0 (D.cochainInv 0
                (c : (underlyingPresimplicial (coverNerveSSet U)).Cochain 0)) = 0 := h.symm
        have h1 := eq_neg_of_add_eq_zero_right h0
        rw [z2_neg_eq_self] at h1
        rw [h1, sub_self]
        exact Submodule.zero_mem _
    | succ m =>
        have h := congrFun (congrArg DFunLike.coe (D.cochainHtpySimp_succ m))
          (c : (underlyingPresimplicial (coverNerveSSet U)).Cochain (m + 1))
        simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_coe, id_eq] at h
        rw [hc, map_zero, zero_add] at h
        have hval : ((geometricCochainMap U).map (m + 1)
              (D.cochainInv (m + 1)
                (c : (underlyingPresimplicial (coverNerveSSet U)).Cochain (m + 1))))
            - (c : (underlyingPresimplicial (coverNerveSSet U)).Cochain (m + 1))
            = (underlyingPresimplicial (coverNerveSSet U)).d m
                (D.cochainHtpySimp m
                  (c : (underlyingPresimplicial (coverNerveSSet U)).Cochain (m + 1))) := by
          rw [h, z2_sub_eq_add]
          exact add_comm _ _
        rw [hval]
        exact ⟨_, rfl⟩
  exact key

/-- Injectivity of the induced map on cohomology. -/
theorem Hmap_injective {U : ι → Set X} (D : ChainHomotopyEquivData U) (n : ℕ) :
    Function.Injective ((geometricCochainMap U).Hmap n) := by
  apply (injective_iff_map_eq_zero ((geometricCochainMap U).Hmap n)).mpr
  intro q hq
  obtain ⟨z, rfl⟩ := Mod2Cohomology.mk_surjective q
  rw [SingularToSimplicialCochainMap.Hmap_class, presimplicialClass_eq_zero_iff] at hq
  have hz : Mod2Cohomology.d (coverNerveRealization U) n
      (z : Mod2Cohomology.Cochain (coverNerveRealization U) n) = 0 := z.2
  have hzq : (geometricCochainMap U).map n
      (z : Mod2Cohomology.Cochain (coverNerveRealization U) n)
      ∈ (underlyingPresimplicial (coverNerveSSet U)).coboundaries n := hq
  rw [Mod2Cohomology.mk_eq_zero_iff]
  cases n with
  | zero =>
      rw [NerveZ2.Presimplicial.coboundaries, Submodule.mem_bot] at hzq
      have h := congrFun (congrArg DFunLike.coe D.cochainHtpySing_zero)
        (z : Mod2Cohomology.Cochain (coverNerveRealization U) 0)
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_coe, id_eq] at h
      rw [hz, map_zero, hzq, map_zero, add_zero] at h
      rw [Mod2Cohomology.coboundaries_zero, Submodule.mem_bot]
      exact h.symm
  | succ m =>
      obtain ⟨b, hb⟩ := hzq
      have h := congrFun (congrArg DFunLike.coe (D.cochainHtpySing_succ m))
        (z : Mod2Cohomology.Cochain (coverNerveRealization U) (m + 1))
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_coe, id_eq] at h
      rw [hz, map_zero, zero_add, ← hb] at h
      have hcomm := congrFun (congrArg DFunLike.coe (D.cochainInv_comm m)) b
      simp only [LinearMap.comp_apply] at hcomm
      rw [hcomm] at h
      refine ⟨D.cochainHtpySing m
        (z : Mod2Cohomology.Cochain (coverNerveRealization U) (m + 1)) + D.cochainInv m b, ?_⟩
      rw [map_add, h, add_assoc, z2_add_self, add_zero]

/-- **WP10, principal (conditional on the chain-level datum, and on nothing else).**

Given a chain-homotopy inverse for the *canonical Task-9 chain map*, the *existing* canonical
geometric comparison

`NerveGeom.geometricHmap 𝓤 n : Hⁿ_sing(|N(𝓤)|;ℤ₂) → Ȟⁿ(𝓤;ℤ₂)`

is bijective in **every** degree.  No universal coefficient theorem, no finiteness assumption
and no unproved exactness of dualisation enters the proof. -/
theorem geometricHmap_bijective_of_chainHomotopyEquiv {U : ι → Set X}
    (D : ChainHomotopyEquivData U) (n : ℕ) :
    Function.Bijective (geometricHmap U n) := by
  have h : Function.Bijective ((geometricCochainMap U).Hmap n) :=
    ⟨Hmap_injective D n, Hmap_surjective D n⟩
  refine ⟨fun a b hab => h.1 ((cechCohomologyEquivSSet U n).injective hab), fun y => ?_⟩
  obtain ⟨x, hx⟩ := h.2 ((cechCohomologyEquivSSet U n).symm y)
  refine ⟨x, ?_⟩
  show cechCohomologyEquivSSet U n ((geometricCochainMap U).Hmap n x) = y
  rw [hx]
  exact (cechCohomologyEquivSSet U n).apply_symm_apply y

/-- **WP11 (conditional).**  The chain-level datum *constructs* the Task-9
`GeometricComparison` structure, so no separate cohomological assumption is ever needed: the
only remaining input to the whole certification DAG is `ChainComparisonStatement`. -/
def ChainHomotopyEquivData.toGeometricComparison {Y : Type u} {κ : Type u} {V : κ → Set Y}
    (D : ChainHomotopyEquivData V) : GeometricComparison V where
  bijective n := geometricHmap_bijective_of_chainHomotopyEquiv D n

/-! ## WP11 : the Spin-lift class on the realised nerve, from the chain-level datum only -/

section SpinFromChainData

open CechSpinLift CechSpinZ2 GoodCoverZ2 SpinCore LorentzFrames NullSectorTask28

variable {Y : TopCat.{u}} {κ : Type u} {𝒤 : CechCover (Y : Type u) κ}
  {T : VisibleCocycle (↥GLor) 𝒤}

/-- The Task-6 Spin-lift class transported to `H²_sing(|N(𝒤)|;ℤ₂)`, now depending only on the
**chain-level** comparison datum. -/
def spinLiftRealizedClassOfChain (D : ChainHomotopyEquivData 𝒤.U) (h : IsGoodCover 𝒤.U)
    (L : SpinLiftFamily internalSpinProjection T) :
    Mod2Cohomology.Cohomology (coverNerveRealization 𝒤.U) 2 :=
  spinLiftRealizedClass D.toGeometricComparison h L

/-- `[z]_{|N|} = 0 ⟺ [z]_{Č²} = 0`, from the chain-level datum. -/
theorem spinLiftRealizedClassOfChain_eq_zero_iff_cech (D : ChainHomotopyEquivData 𝒤.U)
    (h : IsGoodCover 𝒤.U) (L : SpinLiftFamily internalSpinProjection T) :
    spinLiftRealizedClassOfChain D h L = 0 ↔ spinLiftCechClassGood h L = 0 :=
  spinLiftRealizedClass_eq_zero_iff_cech D.toGeometricComparison h L

/-- `[z]_{|N|} = 0 ⟺` a coherent Spin lift exists on the fixed cover, from the chain-level
datum. -/
theorem spinLiftRealizedClassOfChain_eq_zero_iff (D : ChainHomotopyEquivData 𝒤.U)
    (h : IsGoodCover 𝒤.U) (L : SpinLiftFamily internalSpinProjection T) :
    spinLiftRealizedClassOfChain D h L = 0 ↔
      ∃ L' : SpinLiftFamily internalSpinProjection T, L'.IsCoherent :=
  spinLiftRealizedClass_eq_zero_iff D.toGeometricComparison h L

end SpinFromChainData

end NerveGeom
