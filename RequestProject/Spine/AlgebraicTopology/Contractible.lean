import Mathlib.Topology.Homotopy.Contractible
import RequestProject.Spine.AlgebraicTopology.ChainHomotopy

/-!
# Task 18, WP3 : the contractibility smoke test

Using the chain prism of WP2 we show that a contractible space has vanishing singular
`ℤ₂`-homology in every positive degree, and instantiate this at Task 17's realized standard
simplex `|Δ[r]|`.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial NerveGeom

universe u

namespace SpineTask18

/-! ## From a Mathlib homotopy to a prism homotopy -/

theorem toI_mem (s : Δs 1) : (s : Fin 2 → ℝ) 1 ∈ unitInterval := by
  have hsum : (s : Fin 2 → ℝ) 0 + (s : Fin 2 → ℝ) 1 = 1 := by
    have h := s.2.2
    rwa [Fin.sum_univ_two] at h
  have h0 : 0 ≤ (s : Fin 2 → ℝ) 0 := s.2.1 0
  have h1 : 0 ≤ (s : Fin 2 → ℝ) 1 := s.2.1 1
  exact Set.mem_Icc.2 ⟨h1, by linarith⟩

/-- The interval factor `Δ^1` of the prism, mapped onto the unit interval. -/
def toI : C(Δs 1, unitInterval) :=
  ⟨fun s => ⟨(s : Fin 2 → ℝ) 1, toI_mem s⟩,
    Continuous.subtype_mk ((continuous_apply 1).comp continuous_subtype_val) _⟩

theorem toI_e0 : toI e0 = 0 := by
  refine Subtype.ext ?_
  show ((stdSimplex.vertex 0 : Δs 1) : Fin 2 → ℝ) 1 = 0
  rw [stdSimplex.vertex]
  simp

theorem toI_e1 : toI e1 = 1 := by
  refine Subtype.ext ?_
  show ((stdSimplex.vertex 1 : Δs 1) : Fin 2 → ℝ) 1 = 1
  rw [stdSimplex.vertex]
  simp

variable {X Y : TopCat.{u}}

/-- The homotopy `H : X × Δ^1 → Y` attached to a Mathlib homotopy. -/
def ofHomotopy {f g : C(↥X, ↥Y)} (h : f.Homotopy g) : C(↥X × Δs 1, ↥Y) :=
  h.toContinuousMap.comp ⟨fun z => (toI z.2, z.1),
    (toI.continuous.comp continuous_snd).prodMk continuous_fst⟩

theorem endMapC_ofHomotopy_e0 {f g : C(↥X, ↥Y)} (h : f.Homotopy g) :
    endMapC (ofHomotopy h) e0 = f := by
  refine ContinuousMap.ext fun x => ?_
  show h (toI e0, x) = f x
  rw [toI_e0, h.apply_zero]

theorem endMapC_ofHomotopy_e1 {f g : C(↥X, ↥Y)} (h : f.Homotopy g) :
    endMapC (ofHomotopy h) e1 = g := by
  refine ContinuousMap.ext fun x => ?_
  show h (toI e1, x) = g x
  rw [toI_e1, h.apply_one]

/-! ## Constant singular simplices -/

variable (y : ↥X)

/-- The constant singular simplex at `y`. -/
def constSimp (q : ℕ) : Sing X q := sOf (ContinuousMap.const _ y)

/-- The augmentation of singular chains. -/
def augS (X : TopCat.{u}) (q : ℕ) :
    SSetChain (TopCat.toSSet.obj X) q →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.linearCombination (ZMod 2) (fun _ => (1 : ZMod 2))

@[simp] theorem augS_single {q : ℕ} (σ : Sing X q) (a : ZMod 2) :
    augS X q (Finsupp.single σ a) = a := by
  rw [augS, Finsupp.linearCombination_single, smul_eq_mul, mul_one]

theorem singMap_const (q : ℕ) (c : SSetChain (TopCat.toSSet.obj X) q) :
    singMap (TopCat.ofHom (ContinuousMap.const ↥X y)) q c
      = Finsupp.single (constSimp y q) (augS X q c) := by
  induction c using lchain_induction with
  | h0 => simp
  | hadd u v hu hv => rw [map_add, hu, hv, map_add, Finsupp.single_add]
  | hsingle σ =>
    rw [singMap_single, augS_single]
    rfl

theorem singMap_id_apply (q : ℕ) (c : SSetChain (TopCat.toSSet.obj X) q) :
    singMap (𝟙 X) q c = c := by
  show sSetChainMap (TopCat.toSSet.map (𝟙 X)) q c = c
  rw [show TopCat.toSSet.map (𝟙 X) = 𝟙 _ from TopCat.toSSet.map_id X]
  show Finsupp.mapDomain _ c = c
  exact Finsupp.mapDomain_id

theorem pre_constSimp {m q : ℕ} (φ : C(Δs m, Δs q)) :
    pre φ (constSimp y q) = constSimp y m := by
  rw [constSimp, pre, sMap_sOf]
  rfl

theorem singBd_constSimp (q : ℕ) (a : ZMod 2) :
    singBd X q (Finsupp.single (constSimp y (q + 1)) a)
      = Finsupp.single (constSimp y q) ((q : ZMod 2) * a) := by
  rw [singBd_single]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    show Finsupp.single (pre (stdC (Fin.succAbove i)) (constSimp y (q + 1))) a
      = Finsupp.single (constSimp y q) a from by rw [pre_constSimp])]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finsupp.smul_single]
  refine congrArg (fun b => Finsupp.single (constSimp y q) b) ?_
  rw [nsmul_eq_mul]
  refine congrArg (fun b : ZMod 2 => b * a) ?_
  push_cast
  rw [add_assoc, show (1 + 1 : ZMod 2) = 0 from by decide, add_zero]

/-! ## Positive-degree homology of a contractible space vanishes -/

theorem exists_boundary_of_cycle [ContractibleSpace ↥X] (m : ℕ)
    (z : SSetChain (TopCat.toSSet.obj X) (m + 1)) (hz : singBd X m z = 0) :
    ∃ w : SSetChain (TopCat.toSSet.obj X) (m + 2), singBd X (m + 1) w = z := by
  obtain ⟨y, hy⟩ := id_nullhomotopic ↥X
  obtain ⟨h⟩ := hy
  set H : C(↥X × Δs 1, ↥X) := ofHomotopy h with hH
  have h0 : endMap H e0 = 𝟙 X := by
    rw [endMap, endMapC_ofHomotopy_e0]
    rfl
  have h1 : endMap H e1 = TopCat.ofHom (ContinuousMap.const ↥X y) := by
    rw [endMap, endMapC_ofHomotopy_e1]
  -- the prism identity for the cycle `z`
  have hid := prism_identity_succ H m z
  rw [hz, map_zero, add_zero, h0, h1, singMap_id_apply, singMap_const] at hid
  -- `hid : ∂ P z = z + (constant chain)`
  rcases Nat.even_or_odd m with hm | hm
  · -- `m` even, so `m + 1` is odd and the constant chain is itself a boundary
    refine ⟨prismOp H (m + 1) z
      + Finsupp.single (constSimp y (m + 2)) (augS X (m + 1) z), ?_⟩
    rw [map_add, singBd_constSimp, hid]
    have hone : ((m + 1 : ℕ) : ZMod 2) = 1 := by
      obtain ⟨k, rfl⟩ := hm
      push_cast
      rw [mod2_add_self, zero_add]
    rw [hone, one_mul, add_assoc, mod2_add_self, add_zero]
  · -- `m` odd, so the augmentation of the cycle vanishes
    have hb : singBd X m (Finsupp.single (constSimp y (m + 1)) (augS X (m + 1) z)) = 0 := by
      have h2 := congrArg (singBd X m) hid
      rw [show singBd X m (singBd X (m + 1) (prismOp H (m + 1) z)) = 0 from
        congrFun (congrArg DFunLike.coe
          (SpineTask13.sSetBoundary_comp_sSetBoundary (TopCat.toSSet.obj X) m)) _,
        map_add, hz, zero_add] at h2
      exact h2.symm
    rw [singBd_constSimp] at hb
    have hone : ((m : ℕ) : ZMod 2) = 1 := by
      obtain ⟨k, rfl⟩ := hm
      push_cast
      rw [show (2 : ZMod 2) = 0 from by decide, zero_mul, zero_add]
    rw [hone, one_mul, Finsupp.single_eq_zero] at hb
    refine ⟨prismOp H (m + 1) z, ?_⟩
    rw [hid, hb, Finsupp.single_zero, add_zero]

/-- **WP3.**  A contractible space has vanishing singular `ℤ₂`-homology in positive degrees. -/
theorem exactAt_singCx_of_contractible [ContractibleSpace ↥X] (m : ℕ) :
    (singCx X).ExactAt (m + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m
    (ComplexShape.prev_eq' _ (by simp)) (ComplexShape.next_eq' _ (by simp))]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, rfl⟩
    have hdd := (singCx X).d_comp_d (m + 2) (m + 1) m
    exact congrFun (congrArg DFunLike.coe (congrArg ModuleCat.Hom.hom hdd)) w
  · intro z hz
    have hz' : singBd X m z = 0 := by
      have h := LinearMap.mem_ker.1 hz
      rw [show (HomologicalComplex.sc' (singCx X) (m + 2) (m + 1) m).g
        = (singCx X).d (m + 1) m from rfl, SpineTask14.sSetChainComplexFunctor_d] at h
      exact h
    obtain ⟨w, hw⟩ := exists_boundary_of_cycle m z hz'
    refine ⟨w, ?_⟩
    rw [show (HomologicalComplex.sc' (singCx X) (m + 2) (m + 1) m).f
      = (singCx X).d (m + 2) (m + 1) from rfl, SpineTask14.sSetChainComplexFunctor_d]
    exact hw

/-- **WP3.**  The singular `ℤ₂`-homology of a contractible space vanishes in positive
degrees. -/
theorem isZero_homology_of_contractible [ContractibleSpace ↥X] (m : ℕ) :
    IsZero ((singCx X).homology (m + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (exactAt_singCx_of_contractible m)

/-! The corollary for the *realized standard simplex* needs the contractibility of `|Δ[r]|`,
which is Nerve-side geometry; it is
`SpineTask18.isZero_homology_realized_simplex` in
`RequestProject.Spine.Nerve.StandardCell.RealizedSimplexHomology`. -/

end SpineTask18
