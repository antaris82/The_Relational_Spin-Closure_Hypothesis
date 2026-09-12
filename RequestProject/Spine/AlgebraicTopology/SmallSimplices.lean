import RequestProject.Spine.AlgebraicTopology.Mesh
import RequestProject.Spine.AlgebraicTopology.Subdivision

/-!
# Task 18, WP6/WP7 : the small-simplices subcomplex and eventual smallness

For a pair of subsets `U V ⊆ X`, a singular simplex is *`(U,V)`-small* when its image is
contained in `U` or in `V`.  Smallness is stable under all the simplicial operators, so the
small simplices form a *simplicial subset* `SpineTask18.smallSSet X U V` of the singular
simplicial set, and its `ℤ₂`-chains form a subcomplex of the singular chains (WP6).

The geometric input (WP7) is `SpineTask18.exists_iterate_small`: if `U` and `V` are open and
cover `X`, then for every singular simplex `σ` some iterate `sd^N σ` consists of small
simplices; `SpineTask18.exists_iterate_small_chain` upgrades this to a finite chain with a
single `N`.
-/

noncomputable section

open CategoryTheory Opposite Simplicial NerveGeom

universe u v

namespace SpineTask18

variable {X : TopCat.{u}}

/-! ## Carriers in all simplicial degrees -/

/-- The image of a singular simplex, in any simplicial degree. -/
def carrierAt {n : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj X).obj n) : Set X :=
  Set.range (TopCat.toSSetObjEquiv X n σ)

theorem carrierAt_eq_carrier {k : ℕ} (σ : Sing X k) :
    carrierAt σ = carrier σ := rfl

theorem toSSetObjEquiv_map {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (σ : (TopCat.toSSet.obj X).obj n) :
    TopCat.toSSetObjEquiv X m ((TopCat.toSSet.obj X).map f σ)
      = (TopCat.toSSetObjEquiv X n σ).comp (stdC (m := m.unop.len) (n := n.unop.len) f.unop.toOrderHom) := rfl

theorem carrierAt_map {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (σ : (TopCat.toSSet.obj X).obj n) :
    carrierAt ((TopCat.toSSet.obj X).map f σ) ⊆ carrierAt σ := by
  rintro _ ⟨x, rfl⟩
  rw [carrierAt, toSSetObjEquiv_map]
  exact ⟨_, rfl⟩

/-! ## Small simplices -/

variable (U V : Set X)

/-- A simplex is `(U,V)`-small when its image lies entirely in `U` or entirely in `V`. -/
def IsSmallAt {n : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj X).obj n) : Prop :=
  carrierAt σ ⊆ U ∨ carrierAt σ ⊆ V

theorem IsSmallAt.map {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) {σ : (TopCat.toSSet.obj X).obj n}
    (h : IsSmallAt U V σ) : IsSmallAt U V ((TopCat.toSSet.obj X).map f σ) :=
  h.imp (fun hu => (carrierAt_map f σ).trans hu) (fun hv => (carrierAt_map f σ).trans hv)

/-- **WP6.**  The simplicial subset of `(U,V)`-small singular simplices. -/
def smallSSet : SSet.{u} where
  obj n := {σ : (TopCat.toSSet.obj X).obj n // IsSmallAt U V σ}
  map f σ := ⟨(TopCat.toSSet.obj X).map f σ, σ.2.map U V f⟩
  map_id n := by
    funext σ
    exact Subtype.ext (congrFun ((TopCat.toSSet.obj X).map_id n) σ.1)
  map_comp f g := by
    funext σ
    exact Subtype.ext (congrFun ((TopCat.toSSet.obj X).map_comp f g) σ.1)

/-- The inclusion of the small subcomplex. -/
def smallInc : smallSSet U V ⟶ TopCat.toSSet.obj X where
  app _ σ := σ.1
  naturality _ _ _ := rfl

theorem smallInc_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((smallInc U V).app n) := fun _ _ h => Subtype.ext h

/-! ## Chains supported on small simplices -/

/-- The submodule of chains supported on small simplices. -/
def smallChains (k : ℕ) : Submodule (ZMod 2) (SSetChain (TopCat.toSSet.obj X) k) :=
  Finsupp.supported (ZMod 2) (ZMod 2) {σ : Sing X k | IsSmallAt U V σ}

theorem mem_smallChains {k : ℕ} {c : SSetChain (TopCat.toSSet.obj X) k} :
    c ∈ smallChains U V k ↔ ∀ σ ∈ c.support, IsSmallAt U V σ :=
  ⟨fun h _ hσ => h hσ, fun h _ hσ => h _ hσ⟩

theorem single_mem_smallChains {k : ℕ} {σ : Sing X k} (h : IsSmallAt U V σ) (a : ZMod 2) :
    Finsupp.single σ a ∈ smallChains U V k := by
  refine (mem_smallChains U V).2 fun τ hτ => ?_
  rcases Finset.mem_singleton.1 (Finsupp.support_single_subset hτ) with rfl
  exact h

/-- The small chains are exactly the image of the chains of the small subcomplex. -/
theorem range_smallInc_chainMap (k : ℕ) :
    LinearMap.range (sSetChainMap (smallInc U V) k) = smallChains U V k := by
  classical
  refine le_antisymm ?_ ?_
  · rintro _ ⟨c, rfl⟩
    refine (mem_smallChains U V).2 fun σ hσ => ?_
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hσ)
    exact τ.2
  · intro c hc
    refine ⟨Finsupp.comapDomain Subtype.val c (Subtype.val_injective.injOn), ?_⟩
    show Finsupp.mapDomain Subtype.val (Finsupp.comapDomain Subtype.val c _) = c
    refine Finsupp.ext fun σ => ?_
    by_cases hσ : IsSmallAt U V σ
    · have hval := Finsupp.mapDomain_apply
        (f := (Subtype.val : {σ : Sing X k // IsSmallAt U V σ} → Sing X k))
        Subtype.val_injective (Finsupp.comapDomain Subtype.val c Subtype.val_injective.injOn)
        ⟨σ, hσ⟩
      simpa using hval
    · have h0 : c σ = 0 := by
        by_contra h
        exact hσ ((mem_smallChains U V).1 hc σ (Finsupp.mem_support_iff.2 h))
      rw [h0]
      by_contra hne
      obtain ⟨τ, -, hτ⟩ := Finset.mem_image.1
        (Finsupp.mapDomain_support (Finsupp.mem_support_iff.2 hne))
      exact hσ (hτ ▸ τ.2)

/-! ## Smallness is preserved by the subdivision operators -/

/-- To prove that a linear map sends a chain into a submodule it suffices to check generators
in the support. -/
theorem mem_of_single {α : Type*} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (F : (α →₀ ZMod 2) →ₗ[ZMod 2] M) (N : Submodule (ZMod 2) M) (c : α →₀ ZMod 2)
    (h : ∀ σ ∈ c.support, F (Finsupp.single σ 1) ∈ N) : F c ∈ N := by
  classical
  have hc : c = ∑ σ ∈ c.support, Finsupp.single σ (c σ) := (Finsupp.sum_single c).symm
  rw [hc, map_sum]
  refine Submodule.sum_mem _ fun σ hσ => ?_
  have hsm : Finsupp.single σ (c σ) = (c σ) • Finsupp.single σ (1 : ZMod 2) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hsm, map_smul]
  exact Submodule.smul_mem _ _ (h σ hσ)

theorem carriedIn_le_smallChains {W : Set X} (k : ℕ) (h : W ⊆ U ∨ W ⊆ V) :
    carriedIn W k ≤ smallChains U V k := by
  intro c hc
  refine (mem_smallChains U V).2 fun σ hσ => ?_
  have hcar := mem_carriedIn.1 hc σ hσ
  exact h.imp (fun hu => hcar.trans hu) (fun hv => hcar.trans hv)

/-- **WP6.3.**  Subdivision preserves smallness. -/
theorem sdS_smallChains {k : ℕ} {c : SSetChain (TopCat.toSSet.obj X) k}
    (hc : c ∈ smallChains U V k) : sdS X k c ∈ smallChains U V k :=
  mem_of_single _ _ c fun σ hσ =>
    carriedIn_le_smallChains U V k ((mem_smallChains U V).1 hc σ hσ)
      (carrier_sdS σ (le_refl _))

/-- **WP6.4.**  The subdivision homotopy preserves smallness. -/
theorem sdTS_smallChains {k : ℕ} {c : SSetChain (TopCat.toSSet.obj X) k}
    (hc : c ∈ smallChains U V k) : sdTS X k c ∈ smallChains U V (k + 1) :=
  mem_of_single _ _ c fun σ hσ =>
    carriedIn_le_smallChains U V (k + 1) ((mem_smallChains U V).1 hc σ hσ)
      (carrier_sdTS σ (le_refl _))

/-- **WP6.1/6.2.**  Faces of small simplices are small, so small chains form a subcomplex. -/
theorem singBd_smallChains {k : ℕ} {c : SSetChain (TopCat.toSSet.obj X) (k + 1)}
    (hc : c ∈ smallChains U V (k + 1)) : singBd X k c ∈ smallChains U V k := by
  refine mem_of_single _ _ c fun σ hσ => ?_
  have hsm : IsSmallAt U V σ := (mem_smallChains U V).1 hc σ hσ
  rw [singBd_single]
  refine Submodule.sum_mem _ fun i _ => ?_
  refine single_mem_smallChains U V ?_ _
  exact hsm.imp (fun hu => (carrier_pre _ σ).trans hu) (fun hv => (carrier_pre _ σ).trans hv)

/-! ## Iterated subdivision of singular chains -/

/-- Iterated barycentric subdivision of singular chains. -/
def sdSIter (X : TopCat.{u}) (k : ℕ) :
    ℕ → (SSetChain (TopCat.toSSet.obj X) k →ₗ[ZMod 2] SSetChain (TopCat.toSSet.obj X) k)
  | 0 => LinearMap.id
  | N + 1 => (sdS X k).comp (sdSIter X k N)

@[simp] theorem sdSIter_zero (k : ℕ) (c : SSetChain (TopCat.toSSet.obj X) k) :
    sdSIter X k 0 c = c := rfl

theorem sdSIter_succ (k N : ℕ) (c : SSetChain (TopCat.toSSet.obj X) k) :
    sdSIter X k (N + 1) c = sdS X k (sdSIter X k N c) := rfl

theorem sdSIter_add (k N : ℕ) : ∀ (M : ℕ) (c : SSetChain (TopCat.toSSet.obj X) k),
    sdSIter X k (N + M) c = sdSIter X k M (sdSIter X k N c)
  | 0, c => rfl
  | M + 1, c => by
    rw [show N + (M + 1) = (N + M) + 1 from rfl, sdSIter_succ, sdSIter_add k N M, sdSIter_succ]

theorem sdS_realizeChain {n k : ℕ} (σ : Sing X n) (c : LChain (Δs n) k) :
    sdS X k (realizeChain σ k c) = realizeChain σ k (sd n k c) := by
  induction c using lchain_induction with
  | h0 => simp
  | hadd f g hf hg => simp only [map_add, hf, hg]
  | hsingle p => rw [realizeChain_single, sdS_realize]

theorem sdSIter_single {n : ℕ} (σ : Sing X n) : ∀ N : ℕ,
    sdSIter X n N (Finsupp.single σ 1)
      = realizeChain σ n (sdIter n n N (Finsupp.single (taut n) 1))
  | 0 => by rw [sdSIter_zero, sdIter_zero, realizeChain_taut]
  | N + 1 => by
    rw [sdSIter_succ, sdSIter_single σ N, sdS_realizeChain, sdIter_succ]

/-! ## WP7 : eventual smallness -/

/-- **WP7, one simplex.**  For an open cover `X = U ∪ V`, some iterated subdivision of any
singular simplex consists entirely of `(U,V)`-small simplices. -/
theorem exists_iterate_small (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    {n : ℕ} (σ : Sing X n) :
    ∃ N : ℕ, sdSIter X n N (Finsupp.single σ 1) ∈ smallChains U V n := by
  classical
  set f : C(Δs n, X) := sMap σ with hf
  obtain ⟨δ, hδ, hlb⟩ := lebesgue_number_lemma_of_metric (s := (Set.univ : Set (Δs n)))
    (c := fun b : Bool => if b then f ⁻¹' U else f ⁻¹' V) isCompact_univ
    (fun b => by
      cases b
      · exact hV.preimage f.continuous
      · exact hU.preimage f.continuous)
    (fun x _ => by
      have : f x ∈ U ∪ V := hUV ▸ Set.mem_univ _
      rcases this with h | h
      · exact Set.mem_iUnion.2 ⟨true, by simpa using h⟩
      · exact Set.mem_iUnion.2 ⟨false, by simpa using h⟩)
  obtain ⟨N, hN⟩ := exists_pow_mesh_lt n hδ
  refine ⟨N, (mem_smallChains U V).2 fun τ hτ => ?_⟩
  rw [sdSIter_single] at hτ
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hτ)
  have hmesh : MeshLE p ((((n : ℝ) / (n + 1)) ^ N) * 1) :=
    chainMesh_sdIter (c := Finsupp.single (taut n) 1) (fun q _ => meshLE_one q) N p hp
  have hlt : ∀ x y : Δs n, dist (combo p x) (combo p y) < δ := fun x y =>
    lt_of_le_of_lt (dist_combo_le p hmesh x y) hN
  obtain ⟨b, hb⟩ := hlb (combo p (stdSimplex.vertex 0)) (Set.mem_univ _)
  have hrange : ∀ y : Δs n, combo p y ∈ (if b then f ⁻¹' U else f ⁻¹' V) := fun y =>
    hb (by
      simp only [Metric.mem_ball]
      rw [dist_comm]
      exact hlt (stdSimplex.vertex 0) y)
  have hcar : carrier (pre (combo p) σ) ⊆ (if b then U else V) := by
    rintro _ ⟨y, rfl⟩
    have := hrange y
    cases b
    · simpa using this
    · simpa using this
  cases b
  · exact Or.inr (by simpa using hcar)
  · exact Or.inl (by simpa using hcar)

theorem sdSIter_smallChains {k : ℕ} {c : SSetChain (TopCat.toSSet.obj X) k}
    (hc : c ∈ smallChains U V k) : ∀ M, sdSIter X k M c ∈ smallChains U V k
  | 0 => hc
  | M + 1 => by
    rw [sdSIter_succ]
    exact sdS_smallChains U V (sdSIter_smallChains hc M)

/-- **WP7, a finite chain.**  A *single* number of subdivisions makes an arbitrary finite
singular chain small. -/
theorem exists_iterate_small_chain (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    {k : ℕ} (c : SSetChain (TopCat.toSSet.obj X) k) :
    ∃ N : ℕ, sdSIter X k N c ∈ smallChains U V k := by
  classical
  choose g hg using fun σ : Sing X k => exists_iterate_small U V hU hV hUV σ
  refine ⟨c.support.sup g, mem_of_single _ _ c fun σ hσ => ?_⟩
  have hle : g σ ≤ c.support.sup g := Finset.le_sup hσ
  obtain ⟨M, hM⟩ := Nat.exists_eq_add_of_le hle
  rw [hM, sdSIter_add]
  exact sdSIter_smallChains U V (hg σ) M

end SpineTask18
