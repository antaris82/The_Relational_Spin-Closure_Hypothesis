import RequestProject.Spine.Nerve.Basic.ChainMap
import RequestProject.Spine.Nerve.Cochain.CochainComparison

/-!
# Task 9, WP7 : the dual **cochain** map and the induced map on cohomology

The chain map of WP6 goes `C_*^simp(N(𝓤)) → C_*^sing(|N(𝓤)|)`.  Dually, and this is the
direction the cochain-level Spine actually uses, the canonical characteristic simplex induces

`J* : Cⁿ_sing(|N(𝓤)|;ℤ₂) → Cⁿ_simp(N(𝓤);ℤ₂)`,   `(J*f)(σ) = f(|σ|)`,

which is precomposition with `σ ↦ |σ|`.  WP7 asks for `J*δ_sing = δ_simp J*`; this is
`NerveGeom.geometricCochainMap`'s `comm` field, proved from the WP5 face compatibility.

`SingularToSimplicialCochainMap` is the general interface (a degreewise linear map commuting
with the two coboundaries); it is shown to descend to cocycles, to coboundaries and hence to
cohomology, so that the induced map `Hⁿ_sing(|N(𝓤)|;ℤ₂) → Hⁿ_simp(N(𝓤);ℤ₂)` is **induced by
an actual cochain map** and is never introduced standalone.

`geometricCochainMap_dual_chainMap` records that `J*` is genuinely the transpose of the WP6
chain map `J`, so the two constructions are one construction.
-/

noncomputable section

namespace NerveGeom

open CategoryTheory Opposite CechZ2 SimplexCategory

universe w u

/-! ## The general interface : a singular-to-simplicial map of cochain complexes -/

/-- A map of cochain complexes from the native singular `ℤ₂`-cochain complex of a space to
the simplicial `ℤ₂`-cochain complex of a presimplicial set.  Commutation with the two
coboundaries is part of the data and is imposed before any descent to cohomology. -/
structure SingularToSimplicialCochainMap (R : TopCat.{u}) (S : NerveZ2.Presimplicial.{u}) where
  /-- The degreewise linear comparison of cochains. -/
  map : ∀ n : ℕ, Mod2Cohomology.Cochain R n →ₗ[ZMod 2] S.Cochain n
  /-- Compatibility with the coboundaries: `J*δ_sing = δ_simp J*`. -/
  comm : ∀ (n : ℕ) (f : Mod2Cohomology.Cochain R n),
    map (n + 1) (Mod2Cohomology.d R n f) = S.d n (map n f)

namespace SingularToSimplicialCochainMap

variable {R : TopCat.{u}} {S : NerveZ2.Presimplicial.{u}} (Φ : SingularToSimplicialCochainMap R S)

theorem map_mem_cocycles (n : ℕ) {f : Mod2Cohomology.Cochain R n}
    (hf : f ∈ Mod2Cohomology.cocycles R n) : Φ.map n f ∈ S.cocycles n := by
  have hf' : Mod2Cohomology.d R n f = 0 := hf
  show S.d n (Φ.map n f) = 0
  rw [← Φ.comm n f, hf', map_zero]

/-- The induced map on cocycles. -/
def cocyclesMap (n : ℕ) : Mod2Cohomology.cocycles R n →ₗ[ZMod 2] S.cocycles n :=
  (Φ.map n).restrict (fun _ hf => Φ.map_mem_cocycles n hf)

theorem map_mem_coboundaries (n : ℕ) {f : Mod2Cohomology.Cochain R n}
    (hf : f ∈ Mod2Cohomology.coboundaries R n) : Φ.map n f ∈ S.coboundaries n := by
  cases n with
  | zero =>
      rw [Mod2Cohomology.coboundaries_zero, Submodule.mem_bot] at hf
      rw [NerveZ2.Presimplicial.coboundaries, Submodule.mem_bot, hf, map_zero]
  | succ m =>
      obtain ⟨g, rfl⟩ := hf
      exact ⟨Φ.map m g, (Φ.comm m g).symm⟩

/-- **The induced map on cohomology**, obtained by descent from the cochain comparison. -/
def Hmap (n : ℕ) : Mod2Cohomology.Cohomology R n →ₗ[ZMod 2] S.Cohomology n :=
  Submodule.mapQ (Mod2Cohomology.coboundariesIn R n) (S.coboundariesIn n) (Φ.cocyclesMap n)
    (fun _ hz => Φ.map_mem_coboundaries n hz)

@[simp] theorem Hmap_class (n : ℕ) (z : Mod2Cohomology.cocycles R n) :
    Φ.Hmap n (Mod2Cohomology.mk z) = S.cohomologyClass (Φ.cocyclesMap n z) := rfl

end SingularToSimplicialCochainMap

/-! ## The canonical geometric comparison for the cover nerve -/

variable {X : Type w} {ι : Type u}

/-- **WP7, principal.**  The canonical cochain comparison
`J* : Cⁿ_sing(|N(𝓤)|;ℤ₂) → Cⁿ_simp(N(𝓤);ℤ₂)`, given by evaluation on the characteristic
simplices of WP5, together with the **theorem** `J*δ_sing = δ_simp J*`. -/
def geometricCochainMap (U : ι → Set X) :
    SingularToSimplicialCochainMap (coverNerveRealization U)
      (underlyingPresimplicial (coverNerveSSet U)) where
  map n := LinearMap.funLeft (ZMod 2) (ZMod 2) (charSimplex U n)
  comm n f := by
    funext σ
    show (∑ i : Fin (n + 2), f (Mod2Cohomology.face i (charSimplex U (n + 1) σ)))
      = ∑ t : Fin (n + 2), f (charSimplex U n (CechZ2.face t σ))
    exact Finset.sum_congr rfl fun t _ => by rw [charSimplex_face]

@[simp] theorem geometricCochainMap_apply (U : ι → Set X) (n : ℕ)
    (f : Mod2Cohomology.Cochain (coverNerveRealization U) n) (σ : Nerve U n) :
    (geometricCochainMap U).map n f σ = f (charSimplex U n σ) := rfl

/-- `J*` really is the transpose of the WP6 chain map `J`: the two constructions are one. -/
theorem geometricCochainMap_dual_chainMap (U : ι → Set X) (n : ℕ)
    (f : Mod2Cohomology.Cochain (coverNerveRealization U) n) (x : SimpChain U n) :
    (chainMap U n x).sum (fun s c => c * f s)
      = x.sum (fun σ c => c * (geometricCochainMap U).map n f σ) := by
  refine Finsupp.sum_mapDomain_index (h := fun s c => c * f s) ?_ ?_
  · intro s; simp
  · intro s c d; ring

/-! ## The induced map on cohomology, in the Task-6 formulation -/

/-- **The canonical geometric comparison on cohomology**,
`Hⁿ_sing(|N(𝓤)|;ℤ₂) → Ȟⁿ(𝓤;ℤ₂) = Hⁿ_simp(N(𝓤);ℤ₂)`.

It is the descent of the cochain map `J*`, composed with the Task-7 *identity* identification
of the simplicial cohomology of the nerve with the Task-6 Čech cohomology.  No cohomology-level
map is introduced independently of `J*`. -/
def geometricHmap (U : ι → Set X) (n : ℕ) :
    Mod2Cohomology.Cohomology (coverNerveRealization U) n →ₗ[ZMod 2] CechZ2.Cohomology U n :=
  (cechCohomologyEquivSSet U n).toLinearMap.comp ((geometricCochainMap U).Hmap n)

@[simp] theorem geometricHmap_apply (U : ι → Set X) (n : ℕ)
    (q : Mod2Cohomology.Cohomology (coverNerveRealization U) n) :
    geometricHmap U n q
      = cechCohomologyEquivSSet U n ((geometricCochainMap U).Hmap n q) := rfl

end NerveGeom
