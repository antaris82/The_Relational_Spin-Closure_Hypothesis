import RequestProject.Spine.AlgebraicTopology.LinearSubdivision

/-!
# Task 18, WP4/WP5 : barycentric subdivision of *singular* chains

The linear-chain engine of `Task18LinearSubdivision` is transported to the project's singular
chains `NerveGeom.SSetChain (TopCat.toSSet.obj X)` by the tautological formula

`sd(σ) = σ_# (sd ι_n)`,

where `ι_n` is the tautological affine `n`-simplex of `Δs n`.  Proved here:

* `SpineTask18.sdS` is linear in every degree, and `singBd ∘ sdS = sdS ∘ singBd`
  (`sdS_chain_map`);
* `SpineTask18.sdTS` satisfies `∂T + T∂ = id + sd` (`sdTS_homotopy`);
* naturality under postcomposition with a continuous map (`sdS_natural`);
* **locality**: every simplex occurring in `sdS σ` or in `sdTS σ` has image contained in the
  image of `σ` (`carrier_sdS`, `carrier_sdTS`).
-/

noncomputable section

open CategoryTheory Opposite Simplicial NerveGeom

universe u v

namespace SpineTask18

variable {X Y : TopCat.{u}}

/-! ## The two operators -/

/-- **WP4.**  Barycentric subdivision of singular chains. -/
def sdS (X : TopCat.{u}) (k : ℕ) :
    SSetChain (TopCat.toSSet.obj X) k →ₗ[ZMod 2] SSetChain (TopCat.toSSet.obj X) k :=
  Finsupp.linearCombination (ZMod 2)
    (fun σ : Sing X k => realizeChain σ k (sd k k (Finsupp.single (taut k) 1)))

/-- **WP5.**  The subdivision homotopy on singular chains. -/
def sdTS (X : TopCat.{u}) (k : ℕ) :
    SSetChain (TopCat.toSSet.obj X) k →ₗ[ZMod 2] SSetChain (TopCat.toSSet.obj X) (k + 1) :=
  Finsupp.linearCombination (ZMod 2)
    (fun σ : Sing X k => realizeChain σ (k + 1) (sdT k k (Finsupp.single (taut k) 1)))

theorem sdS_single {k : ℕ} (σ : Sing X k) :
    sdS X k (Finsupp.single σ 1) = realizeChain σ k (sd k k (Finsupp.single (taut k) 1)) := by
  show Finsupp.linearCombination _ _ _ = _
  rw [Finsupp.linearCombination_single, one_smul]

theorem sdTS_single {k : ℕ} (σ : Sing X k) :
    sdTS X k (Finsupp.single σ 1)
      = realizeChain σ (k + 1) (sdT k k (Finsupp.single (taut k) 1)) := by
  show Finsupp.linearCombination _ _ _ = _
  rw [Finsupp.linearCombination_single, one_smul]

/-! ## The master naturality lemmas -/

/-- Subdivision of an affine reparametrisation of `σ` is the realisation of the corresponding
linear subdivision. -/
theorem sdS_realize {n k : ℕ} (σ : Sing X n) (p : Fin (k + 1) → Δs n) :
    sdS X k (Finsupp.single (pre (combo p) σ) 1)
      = realizeChain σ k (sd n k (Finsupp.single p 1)) := by
  rw [sdS_single,
    show realizeChain (pre (combo p) σ) k (sd k k (Finsupp.single (taut k) 1))
      = realizeChain σ k (lmap (combo p) k (sd k k (Finsupp.single (taut k) 1))) from
      (congrFun (congrArg DFunLike.coe (realizeChain_lmap σ p k)) _).symm,
    lmap_sd, lmap_combo_taut]

theorem sdTS_realize {n k : ℕ} (σ : Sing X n) (p : Fin (k + 1) → Δs n) :
    sdTS X k (Finsupp.single (pre (combo p) σ) 1)
      = realizeChain σ (k + 1) (sdT n k (Finsupp.single p 1)) := by
  rw [sdTS_single,
    show realizeChain (pre (combo p) σ) (k + 1) (sdT k k (Finsupp.single (taut k) 1))
      = realizeChain σ (k + 1) (lmap (combo p) (k + 1) (sdT k k (Finsupp.single (taut k) 1)))
      from (congrFun (congrArg DFunLike.coe (realizeChain_lmap σ p (k + 1))) _).symm,
    lmap_sdT, lmap_combo_taut]

/-- The `i`-th face of `σ` is the affine reparametrisation of `σ` along the `i`-th vertex face. -/
theorem face_eq_pre_combo {n : ℕ} (σ : Sing X (n + 1)) (i : Fin (n + 2)) :
    pre (stdC (Fin.succAbove i)) σ = pre (combo (taut (n + 1) ∘ Fin.succAbove i)) σ := by
  rw [show (combo (taut (n + 1) ∘ Fin.succAbove i)) = stdC (Fin.succAbove i) from
    combo_vertex (Fin.succAbove i)]

theorem realizeChain_lbd_apply {n : ℕ} (σ : Sing X n) (k : ℕ) (c : LChain (Δs n) (k + 1)) :
    realizeChain σ k (lbd (Δs n) k c) = singBd X k (realizeChain σ (k + 1) c) :=
  congrFun (congrArg DFunLike.coe (realizeChain_lbd σ k)) c

/-! ## Subdivision is a chain map -/

/-- **WP4.2.**  `∂ ∘ sd = sd ∘ ∂` on singular chains. -/
theorem sdS_chain_map (X : TopCat.{u}) (k : ℕ) :
    (singBd X k).comp (sdS X (k + 1)) = (sdS X k).comp (singBd X k) := by
  refine Finsupp.lhom_ext' fun σ => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [sdS_single, ← realizeChain_lbd_apply, lbd_sd, lbd_single, map_sum, map_sum, singBd_single,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [face_eq_pre_combo, sdS_realize]

/-! ## The homotopy -/

theorem sdS_zero_deg (σ : Sing X 0) : sdS X 0 (Finsupp.single σ 1) = Finsupp.single σ 1 := by
  rw [sdS_single, sd_zero, realizeChain_taut]

theorem sdTS_zero_deg (c : SSetChain (TopCat.toSSet.obj X) 0) : sdTS X 0 c = 0 := by
  induction c using lchain_induction with
  | h0 => simp
  | hadd f g hf hg => simp only [map_add, hf, hg, add_zero]
  | hsingle σ => rw [sdTS_single, sdT_zero, map_zero]

/-- **WP5.**  `∂T + T∂ = id + sd` on singular chains, in positive degrees. -/
theorem sdTS_homotopy (X : TopCat.{u}) (k : ℕ)
    (c : SSetChain (TopCat.toSSet.obj X) (k + 1)) :
    singBd X (k + 1) (sdTS X (k + 1) c) + sdTS X k (singBd X k c) = c + sdS X (k + 1) c := by
  induction c using lchain_induction with
  | h0 => simp
  | hadd f g hf hg =>
    simp only [map_add]
    rw [add_add_add_comm, hf, hg, add_add_add_comm]
  | hsingle σ =>
    have h := sdT_homotopy (k + 1) k (Finsupp.single (taut (k + 1)) (1 : ZMod 2))
    have hh : lbd (Δs (k + 1)) (k + 1) (sdT (k + 1) (k + 1) (Finsupp.single (taut (k + 1)) 1))
        = (Finsupp.single (taut (k + 1)) 1
            + sd (k + 1) (k + 1) (Finsupp.single (taut (k + 1)) 1))
          + sdT (k + 1) k (lbd (Δs (k + 1)) k (Finsupp.single (taut (k + 1)) 1)) := by
      have h2 : (lbd (Δs (k + 1)) (k + 1) (sdT (k + 1) (k + 1) (Finsupp.single (taut (k + 1)) 1))
            + sdT (k + 1) k (lbd (Δs (k + 1)) k (Finsupp.single (taut (k + 1)) 1)))
            + sdT (k + 1) k (lbd (Δs (k + 1)) k (Finsupp.single (taut (k + 1)) 1))
          = (Finsupp.single (taut (k + 1)) 1
              + sd (k + 1) (k + 1) (Finsupp.single (taut (k + 1)) 1))
            + sdT (k + 1) k (lbd (Δs (k + 1)) k (Finsupp.single (taut (k + 1)) 1)) := by
        rw [h]
      rwa [add_assoc, mod2_add_self, add_zero] at h2
    have hfaces : sdTS X k (singBd X k (Finsupp.single σ 1))
        = realizeChain σ (k + 1)
            (sdT (k + 1) k (lbd (Δs (k + 1)) k (Finsupp.single (taut (k + 1)) 1))) := by
      rw [singBd_single, map_sum, lbd_single, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [face_eq_pre_combo, sdTS_realize]
    rw [sdTS_single, ← realizeChain_lbd_apply, hh, map_add, map_add, hfaces, realizeChain_taut,
      ← sdS_single, add_assoc, mod2_add_self, add_zero]

/-! ## Locality : the carrier of a subdivided simplex -/

/-- The image of a singular simplex. -/
def carrier {n : ℕ} (σ : Sing X n) : Set X := Set.range (sMap σ)

theorem carrier_pre {m n : ℕ} (φ : C(Δs m, Δs n)) (σ : Sing X n) :
    carrier (pre φ σ) ⊆ carrier σ := by
  rintro _ ⟨x, rfl⟩
  exact ⟨φ x, rfl⟩

/-- Chains supported on simplices whose image lies in `W`. -/
def carriedIn (W : Set X) (k : ℕ) : Submodule (ZMod 2) (SSetChain (TopCat.toSSet.obj X) k) :=
  Finsupp.supported (ZMod 2) (ZMod 2) {σ : Sing X k | carrier σ ⊆ W}

theorem mem_carriedIn {W : Set X} {k : ℕ} {c : SSetChain (TopCat.toSSet.obj X) k} :
    c ∈ carriedIn W k ↔ ∀ σ ∈ c.support, carrier σ ⊆ W := by
  constructor
  · intro h σ hσ; exact h hσ
  · intro h σ hσ; exact h σ hσ

theorem single_mem_carriedIn {W : Set X} {k : ℕ} {σ : Sing X k} (h : carrier σ ⊆ W)
    (a : ZMod 2) : Finsupp.single σ a ∈ carriedIn W k := by
  refine mem_carriedIn.2 fun τ hτ => ?_
  rcases Finset.mem_singleton.1 (Finsupp.support_single_subset hτ) with rfl
  exact h

/-- **Locality of realisation.**  Every simplex occurring in the realisation of a linear chain
along `σ` is carried by the image of `σ`. -/
theorem realizeChain_carried {n k : ℕ} (σ : Sing X n) (c : LChain (Δs n) k) {W : Set X}
    (h : carrier σ ⊆ W) : realizeChain σ k c ∈ carriedIn W k := by
  refine mem_carriedIn.2 fun τ hτ => ?_
  classical
  have hτ' : τ ∈ c.support.image (fun p : Fin (k + 1) → Δs n => pre (combo p) σ) :=
    Finsupp.mapDomain_support hτ
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hτ'
  exact (carrier_pre (combo p) σ).trans h

/-- **WP4.5 / WP5 locality.**  Subdivision does not enlarge the carrier. -/
theorem carrier_sdS {k : ℕ} (σ : Sing X k) {W : Set X} (h : carrier σ ⊆ W) :
    sdS X k (Finsupp.single σ 1) ∈ carriedIn W k := by
  rw [sdS_single]
  exact realizeChain_carried σ _ h

theorem carrier_sdTS {k : ℕ} (σ : Sing X k) {W : Set X} (h : carrier σ ⊆ W) :
    sdTS X k (Finsupp.single σ 1) ∈ carriedIn W (k + 1) := by
  rw [sdTS_single]
  exact realizeChain_carried σ _ h

/-! ## Naturality under continuous maps -/

/-- The chain map induced by a continuous map, in the project's model. -/
abbrev singMap (g : X ⟶ Y) (k : ℕ) :
    SSetChain (TopCat.toSSet.obj X) k →ₗ[ZMod 2] SSetChain (TopCat.toSSet.obj Y) k :=
  sSetChainMap (TopCat.toSSet.map g) k

theorem singMap_single (g : X ⟶ Y) {k : ℕ} (σ : Sing X k) (a : ZMod 2) :
    singMap g k (Finsupp.single σ a)
      = Finsupp.single (sOf ((ConcreteCategory.hom g).comp (sMap σ))) a := by
  rw [sSetChainMap_single]
  rfl

theorem pre_comp_map (g : X ⟶ Y) {m n : ℕ} (φ : C(Δs m, Δs n)) (σ : Sing X n) :
    sOf ((ConcreteCategory.hom g).comp (sMap (pre φ σ)))
      = pre φ (sOf ((ConcreteCategory.hom g).comp (sMap σ))) := by
  rw [pre, sMap_sOf, pre, sMap_sOf]
  rfl

/-- **WP4.4.**  Subdivision is natural for postcomposition by a continuous map. -/
theorem sdS_natural (g : X ⟶ Y) (k : ℕ) :
    (singMap g k).comp (sdS X k) = (sdS Y k).comp (singMap g k) := by
  refine Finsupp.lhom_ext' fun σ => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [sdS_single, singMap_single, sdS_single, realizeChain, realizeChain]
  show Finsupp.mapDomain _ (Finsupp.mapDomain _ _) = Finsupp.mapDomain _ _
  rw [← Finsupp.mapDomain_comp]
  refine congrFun (congrArg Finsupp.mapDomain (funext fun p => ?_)) _
  exact (pre_comp_map g (combo p) σ).symm

end SpineTask18
