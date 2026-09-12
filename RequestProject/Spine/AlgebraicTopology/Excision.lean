import RequestProject.Spine.AlgebraicTopology.SmallSimplices
import RequestProject.Spine.AlgebraicTopology.RelativeLES

/-!
# Task 18, WP8/WP9 : the small-simplices theorem and singular excision

The iterated subdivision homotopy `homN` satisfies `∂ D_N + D_N ∂ = id + sd^N`.  Combined with
eventual smallness this shows that the quotient complex `C_*(X)/C_*^{small}` is acyclic, hence
(via the project's relative short exact sequence and the long exact homology sequence) that the
inclusion of the small subcomplex is a quasi-isomorphism (WP8), and finally the excision
theorem (WP9).
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial NerveGeom SpineTask14

universe u v

namespace SpineTask18

variable {X : TopCat.{u}} (U V : Set X)

/-! ## The iterated subdivision homotopy -/

theorem singBd_sdSIter (k : ℕ) : ∀ (N : ℕ) (c : SSetChain (TopCat.toSSet.obj X) (k + 1)),
    singBd X k (sdSIter X (k + 1) N c) = sdSIter X k N (singBd X k c)
  | 0, c => rfl
  | N + 1, c => by
    rw [sdSIter_succ, sdSIter_succ,
      show singBd X k (sdS X (k + 1) (sdSIter X (k + 1) N c))
        = sdS X k (singBd X k (sdSIter X (k + 1) N c)) from
        congrFun (congrArg DFunLike.coe (sdS_chain_map X k)) _,
      singBd_sdSIter k N c]

/-- The `N`-fold subdivision homotopy `D_N = ∑_{i<N} T ∘ sd^i`. -/
def homN (X : TopCat.{u}) (k : ℕ) :
    ℕ → (SSetChain (TopCat.toSSet.obj X) k →ₗ[ZMod 2] SSetChain (TopCat.toSSet.obj X) (k + 1))
  | 0 => 0
  | N + 1 => homN X k N + (sdTS X k).comp (sdSIter X k N)

@[simp] theorem homN_zero (k : ℕ) (c : SSetChain (TopCat.toSSet.obj X) k) :
    homN X k 0 c = 0 := rfl

theorem homN_succ (k N : ℕ) (c : SSetChain (TopCat.toSSet.obj X) k) :
    homN X k (N + 1) c = homN X k N c + sdTS X k (sdSIter X k N c) := rfl

/-- **The iterated homotopy identity** `∂ D_N + D_N ∂ = id + sd^N`. -/
theorem homN_homotopy (k : ℕ) : ∀ (N : ℕ) (c : SSetChain (TopCat.toSSet.obj X) (k + 1)),
    singBd X (k + 1) (homN X (k + 1) N c) + homN X k N (singBd X k c)
      = c + sdSIter X (k + 1) N c
  | 0, c => by simp [mod2_add_self]
  | N + 1, c => by
    rw [homN_succ, homN_succ, map_add]
    have hIH := homN_homotopy k N c
    have hsd := sdTS_homotopy X k (sdSIter X (k + 1) N c)
    rw [singBd_sdSIter] at hsd
    calc singBd X (k + 1) (homN X (k + 1) N c)
            + singBd X (k + 1) (sdTS X (k + 1) (sdSIter X (k + 1) N c))
          + (homN X k N (singBd X k c) + sdTS X k (sdSIter X k N (singBd X k c)))
        = (singBd X (k + 1) (homN X (k + 1) N c) + homN X k N (singBd X k c))
          + (singBd X (k + 1) (sdTS X (k + 1) (sdSIter X (k + 1) N c))
            + sdTS X k (sdSIter X k N (singBd X k c))) := by abel
      _ = (c + sdSIter X (k + 1) N c)
          + (sdSIter X (k + 1) N c + sdS X (k + 1) (sdSIter X (k + 1) N c)) := by
            rw [hIH, hsd]
      _ = c + sdSIter X (k + 1) (N + 1) c := by
            rw [sdSIter_succ]
            rw [show ∀ A B C : SSetChain (TopCat.toSSet.obj X) (k + 1),
              (A + B) + (B + C) = A + C + (B + B) from fun A B C => by abel,
              mod2_add_self, add_zero]

theorem homN_smallChains {k : ℕ} {c : SSetChain (TopCat.toSSet.obj X) k}
    (hc : c ∈ smallChains U V k) (N : ℕ) : homN X k N c ∈ smallChains U V (k + 1) := by
  induction N with
  | zero => simp only [homN_zero]; exact (smallChains U V (k + 1)).zero_mem
  | succ N ih =>
    rw [homN_succ]
    exact Submodule.add_mem _ ih
      (sdTS_smallChains U V (sdSIter_smallChains U V hc N))

/-! ## Degree zero : every `0`-simplex is small -/

theorem smallChains_zero_eq_top (hUV : U ∪ V = Set.univ) : smallChains U V 0 = ⊤ := by
  refine eq_top_iff.2 fun c _ => (mem_smallChains U V).2 fun σ _ => ?_
  have hsub : ∀ x y : Δs 0, x = y := by
    intro x y
    refine Subtype.ext (funext fun i => ?_)
    have hx := x.2.2
    have hy := y.2.2
    rw [Fin.sum_univ_one] at hx hy
    have hi : i = 0 := Fin.ext (by omega)
    subst hi
    rw [hx, hy]
  set x₀ : Δs 0 := stdSimplex.vertex 0 with hx₀
  have hmem : sMap σ x₀ ∈ U ∪ V := hUV ▸ Set.mem_univ _
  rcases hmem with h | h
  · refine Or.inl ?_
    show Set.range (sMap σ) ⊆ U
    exact Set.range_subset_iff.2 fun x => by rw [hsub x x₀]; exact h
  · refine Or.inr ?_
    show Set.range (sMap σ) ⊆ V
    exact Set.range_subset_iff.2 fun x => by rw [hsub x x₀]; exact h

/-! ## Acyclicity of `C_*(X)/C_*^{small}` -/

theorem isZero_relSmall_zero (hUV : U ∪ V = Set.univ) :
    IsZero ((relChainCx (smallInc U V)).X 0) := by
  haveI hsub : Subsingleton (RelChainMod (smallInc U V) 0) := by
    constructor
    intro a b
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    have hx : x - y ∈ LinearMap.range (sSetChainMap (smallInc U V) 0) := by
      rw [range_smallInc_chainMap, smallChains_zero_eq_top U V hUV]
      trivial
    exact (Submodule.Quotient.eq _).2 hx
  rw [show (relChainCx (smallInc U V)).X 0
      = ModuleCat.of (ZMod 2) (RelChainMod (smallInc U V) 0) from rfl]
  exact ModuleCat.isZero_of_subsingleton _

/-- **The key acyclicity statement.**  Every relative cycle modulo small chains is a relative
boundary : the quotient complex `C_*(X)/C_*^{small}(X;U,V)` is exact everywhere. -/
theorem relSmall_exactAt (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    ∀ q : ℕ, (relChainCx (smallInc U V)).ExactAt q
  | 0 => ShortComplex.exact_of_isZero_X₂ _ (isZero_relSmall_zero U V hUV)
  | m + 1 => by
    rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m
      (ComplexShape.prev_eq' _ (by simp)) (ComplexShape.next_eq' _ (by simp))]
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, rfl⟩
      have hdd := (relChainCx (smallInc U V)).d_comp_d (m + 2) (m + 1) m
      exact congrFun (congrArg DFunLike.coe (congrArg ModuleCat.Hom.hom hdd)) y
    · intro x hx
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      -- the boundary of `c` is small
      have hbd : singBd X m c ∈ smallChains U V m := by
        have hx' : (relChainCx (smallInc U V)).d (m + 1) m
            (Submodule.Quotient.mk c) = 0 := hx
        rw [relChainCx_d] at hx'
        have h0 : Submodule.Quotient.mk (p := LinearMap.range (sSetChainMap (smallInc U V) m))
            (sSetBoundary (TopCat.toSSet.obj X) m c) = 0 := hx'
        rw [← range_smallInc_chainMap]
        exact (Submodule.Quotient.mk_eq_zero _).1 h0
      obtain ⟨N, hN⟩ := exists_iterate_small_chain U V hU hV hUV c
      have hc : singBd X (m + 1) (homN X (m + 1) N c) + homN X m N (singBd X m c)
          + sdSIter X (m + 1) N c = c := by
        rw [homN_homotopy, add_assoc, mod2_add_self, add_zero]
      refine ⟨Submodule.Quotient.mk (homN X (m + 1) N c), ?_⟩
      have hzero1 : Submodule.Quotient.mk
          (p := LinearMap.range (sSetChainMap (smallInc U V) (m + 1)))
          (homN X m N (singBd X m c)) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2
          (by rw [range_smallInc_chainMap]; exact homN_smallChains U V hbd N)
      have hzero2 : Submodule.Quotient.mk
          (p := LinearMap.range (sSetChainMap (smallInc U V) (m + 1)))
          (sdSIter X (m + 1) N c) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 (by rw [range_smallInc_chainMap]; exact hN)
      show ((relChainCx (smallInc U V)).d (m + 2) (m + 1)).hom
        (Submodule.Quotient.mk (homN X (m + 1) N c)) = Submodule.Quotient.mk c
      rw [relChainCx_d]
      show Submodule.Quotient.mk
        (sSetBoundary (TopCat.toSSet.obj X) (m + 1) (homN X (m + 1) N c))
          = Submodule.Quotient.mk c
      symm
      conv_lhs => rw [← hc]
      rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, hzero1, hzero2, add_zero, add_zero]

theorem isZero_relSmall_homology (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (q : ℕ) : IsZero ((relChainCx (smallInc U V)).homology q) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ q).1 (relSmall_exactAt U V hU hV hUV q)

/-! ## WP9 : subspaces, and the range of an induced chain map -/

/-- Chains in the image of `C_*(f)` are exactly the chains supported on the image of `f`. -/
theorem mem_range_sSetChainMap {S T : SSet.{u}} (f : S ⟶ T) (k : ℕ)
    (hf : Function.Injective (f.app (op (SimplexCategory.mk k)))) (c : SSetChain T k) :
    c ∈ LinearMap.range (sSetChainMap f k)
      ↔ ∀ σ ∈ c.support, σ ∈ Set.range (f.app (op (SimplexCategory.mk k))) := by
  classical
  constructor
  · rintro ⟨x, rfl⟩ σ hσ
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hσ)
    exact ⟨τ, rfl⟩
  · intro h
    refine ⟨Finsupp.comapDomain _ c hf.injOn, ?_⟩
    exact Finsupp.mapDomain_comapDomain _ hf c (fun σ hσ => h σ hσ)

/-- The subspace of `X` determined by a subset, as an object of `TopCat`. -/
abbrev subTop (W : Set X) : TopCat.{u} := TopCat.of W

/-- The inclusion of a subspace. -/
def subInc (W : Set X) : subTop W ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem subInc_injective (W : Set X) : Function.Injective (subInc W) :=
  fun _ _ h => Subtype.ext h

theorem carrierAt_toSSet_map {n : SimplexCategoryᵒᵖ} {Y : TopCat.{u}} (g : X ⟶ Y)
    (σ : (TopCat.toSSet.obj X).obj n) :
    carrierAt ((TopCat.toSSet.map g).app n σ) = (ConcreteCategory.hom g) '' carrierAt σ := by
  show Set.range (⇑(ConcreteCategory.hom g) ∘ ⇑(TopCat.toSSetObjEquiv X n σ)) = _
  exact Set.range_comp _ _

theorem carrierAt_subInc {n : SimplexCategoryᵒᵖ} (W : Set X)
    (σ : (TopCat.toSSet.obj (subTop W)).obj n) :
    carrierAt ((TopCat.toSSet.map (subInc W)).app n σ) ⊆ W := by
  rw [carrierAt_toSSet_map]
  rintro _ ⟨x, -, rfl⟩
  exact x.2

/-- A singular simplex of `X` factors through a subspace exactly when its image lies in it. -/
theorem range_toSSet_subInc (W : Set X) (k : ℕ) :
    Set.range ((TopCat.toSSet.map (subInc W)).app (op (SimplexCategory.mk k)))
      = {σ : Sing X k | carrier σ ⊆ W} := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro _ ⟨τ, rfl⟩
    exact carrierAt_subInc W τ
  · intro σ hσ
    refine ⟨sOf ⟨fun x => ⟨sMap σ x, hσ ⟨x, rfl⟩⟩, (sMap σ).continuous.subtype_mk _⟩, ?_⟩
    rw [toSSet_map_app, sMap_sOf]
    refine Eq.trans (congrArg sOf (?_ : _ = sMap σ)) (sOf_sMap σ)
    exact ContinuousMap.ext fun x => rfl


/-! ## WP9 : the three simplicial sets of the excision square -/

/-- A singular simplex of the subspace `U`, regarded as a `(U,V)`-small simplex of `X`. -/
def toSmallU : TopCat.toSSet.obj (subTop U) ⟶ smallSSet U V where
  app n σ := ⟨(TopCat.toSSet.map (subInc U)).app n σ, Or.inl (carrierAt_subInc U σ)⟩
  naturality _ _ f := by
    funext σ
    exact Subtype.ext (congrFun ((TopCat.toSSet.map (subInc U)).naturality f) σ)

/-- A singular simplex of the subspace `V`, regarded as a `(U,V)`-small simplex of `X`. -/
def toSmallV : TopCat.toSSet.obj (subTop V) ⟶ smallSSet U V where
  app n σ := ⟨(TopCat.toSSet.map (subInc V)).app n σ, Or.inr (carrierAt_subInc V σ)⟩
  naturality _ _ f := by
    funext σ
    exact Subtype.ext (congrFun ((TopCat.toSSet.map (subInc V)).naturality f) σ)

theorem toSmallU_smallInc : toSmallU U V ≫ smallInc U V = TopCat.toSSet.map (subInc U) := rfl

theorem toSmallV_smallInc : toSmallV U V ≫ smallInc U V = TopCat.toSSet.map (subInc V) := rfl

theorem toSmallU_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((toSmallU U V).app n) := fun _ _ h =>
  toSSet_map_injective (subInc U) (subInc_injective U) n (congrArg Subtype.val h)

theorem toSmallV_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((toSmallV U V).app n) := fun _ _ h =>
  toSSet_map_injective (subInc V) (subInc_injective V) n (congrArg Subtype.val h)

theorem range_toSmallV (k : ℕ) :
    Set.range ((toSmallV U V).app (op (SimplexCategory.mk k)))
      = {τ : (smallSSet U V).obj (op (SimplexCategory.mk k)) | carrier τ.1 ⊆ V} := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro _ ⟨τ, rfl⟩
    exact carrierAt_subInc V τ
  · intro τ hτ
    obtain ⟨σ, hσ⟩ : τ.1 ∈ Set.range ((TopCat.toSSet.map (subInc V)).app _) := by
      rw [range_toSSet_subInc]; exact hτ
    exact ⟨σ, Subtype.ext hσ⟩

theorem range_toSmallU (k : ℕ) :
    Set.range ((toSmallU U V).app (op (SimplexCategory.mk k)))
      = {τ : (smallSSet U V).obj (op (SimplexCategory.mk k)) | carrier τ.1 ⊆ U} := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro _ ⟨τ, rfl⟩
    exact carrierAt_subInc U τ
  · intro τ hτ
    obtain ⟨σ, hσ⟩ : τ.1 ∈ Set.range ((TopCat.toSSet.map (subInc U)).app _) := by
      rw [range_toSSet_subInc]; exact hτ
    exact ⟨σ, Subtype.ext hσ⟩

/-- The inclusion of `U ∩ V` into `U`. -/
def incInterU : subTop (U ∩ V) ⟶ subTop U :=
  TopCat.ofHom ⟨fun x => ⟨x.1, x.2.1⟩, Continuous.subtype_mk continuous_subtype_val _⟩

/-- The inclusion of `U ∩ V` into `V`. -/
def incInterV : subTop (U ∩ V) ⟶ subTop V :=
  TopCat.ofHom ⟨fun x => ⟨x.1, x.2.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩

theorem incInterU_injective : Function.Injective (incInterU U V) := fun _ _ h =>
  Subtype.ext (congrArg (fun z : U => (z : X)) h)

theorem incInter_square : incInterU U V ≫ subInc U = incInterV U V ≫ subInc V := rfl


theorem sMap_subInc {W : Set X} {k : ℕ} (σ : Sing (subTop W) k) :
    sMap ((TopCat.toSSet.map (subInc W)).app (op (SimplexCategory.mk k)) σ)
      = ⟨fun x => ((sMap σ x : W) : X), continuous_subtype_val.comp (sMap σ).continuous⟩ := by
  rw [toSSet_map_app, sMap_sOf]
  exact ContinuousMap.ext fun x => rfl

/-- A singular simplex of `U` factors through `U ∩ V` exactly when it also lands in `V`. -/
theorem mem_range_incInterU {k : ℕ} (σ : Sing (subTop U) k)
    (h : carrier ((TopCat.toSSet.map (subInc U)).app (op (SimplexCategory.mk k)) σ) ⊆ V) :
    σ ∈ Set.range ((TopCat.toSSet.map (incInterU U V)).app (op (SimplexCategory.mk k))) := by
  have hV : ∀ x, ((sMap σ x : U) : X) ∈ V := by
    intro x
    refine h ?_
    rw [carrier, sMap_subInc]
    exact ⟨x, rfl⟩
  refine ⟨sOf ⟨fun x => ⟨((sMap σ x : U) : X), ⟨(sMap σ x).2, hV x⟩⟩,
    (continuous_subtype_val.comp (sMap σ).continuous).subtype_mk _⟩, ?_⟩
  rw [toSSet_map_app, sMap_sOf]
  refine Eq.trans (congrArg sOf (?_ : _ = sMap σ)) (sOf_sMap σ)
  exact ContinuousMap.ext fun x => Subtype.ext rfl

/-! ## WP9 : the three comparison maps -/

theorem excSquare_small :
    TopCat.toSSet.map (incInterU U V) ≫ toSmallU U V
      = TopCat.toSSet.map (incInterV U V) ≫ toSmallV U V := by
  refine NatTrans.ext (funext fun n => funext fun σ => Subtype.ext ?_)
  show ((TopCat.toSSet.map (incInterU U V)) ≫ (TopCat.toSSet.map (subInc U))).app n σ
    = ((TopCat.toSSet.map (incInterV U V)) ≫ (TopCat.toSSet.map (subInc V))).app n σ
  rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp, incInter_square]

/-- The comparison `C_*(U)/C_*(U ∩ V) ⟶ C_*^{small}/C_*(V)`. -/
def excPsi : relSingChainCx (incInterU U V) ⟶ relChainCx (toSmallV U V) :=
  relChainCxMap (TopCat.toSSet.map (incInterU U V)) (toSmallV U V)
    (TopCat.toSSet.map (incInterV U V)) (toSmallU U V) (excSquare_small U V)

/-- The comparison `C_*^{small}/C_*(V) ⟶ C_*(X)/C_*(V)`. -/
def excAlpha : relChainCx (toSmallV U V) ⟶ relSingChainCx (subInc V) :=
  relChainCxMap (toSmallV U V) (TopCat.toSSet.map (subInc V)) (𝟙 _) (smallInc U V)
    ((toSmallV_smallInc U V).trans (Category.id_comp _).symm)

/-- The comparison `C_*(X)/C_*(V) ⟶ C_*(X)/C_*^{small}`. -/
def excBeta : relSingChainCx (subInc V) ⟶ relChainCx (smallInc U V) :=
  relChainCxMap (TopCat.toSSet.map (subInc V)) (smallInc U V) (toSmallV U V) (𝟙 _)
    ((Category.comp_id _).trans (toSmallV_smallInc U V).symm)

/-- **The excision map of pairs** `(U, U ∩ V) → (X, V)` on relative singular chains. -/
def excisionMap : relSingChainCx (incInterU U V) ⟶ relSingChainCx (subInc V) :=
  relChainCxMap (TopCat.toSSet.map (incInterU U V)) (TopCat.toSSet.map (subInc V))
    (TopCat.toSSet.map (incInterV U V)) (TopCat.toSSet.map (subInc U))
    (by rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp, incInter_square])

theorem excisionMap_factor : excisionMap U V = excPsi U V ≫ excAlpha U V := by
  refine HomologicalComplex.hom_ext _ _ fun q => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Submodule.Quotient.mk (sSetChainMap (TopCat.toSSet.map (subInc U)) q c)
    = Submodule.Quotient.mk (sSetChainMap (smallInc U V) q (sSetChainMap (toSmallU U V) q c))
  refine congrArg _ ?_
  show Finsupp.mapDomain ((TopCat.toSSet.map (subInc U)).app _) c
    = Finsupp.mapDomain ((smallInc U V).app _) (Finsupp.mapDomain ((toSmallU U V).app _) c)
  rw [← Finsupp.mapDomain_comp]
  rfl


/-! ## WP9 : `C_*(U)/C_*(U ∩ V) ≅ C_*^{small}/C_*(V)` -/

theorem excPsi_f_mk (q : ℕ) (c : SSetChain (TopCat.toSSet.obj (subTop U)) q) :
    ((excPsi U V).f q).hom (Submodule.Quotient.mk c)
      = Submodule.Quotient.mk (sSetChainMap (toSmallU U V) q c) := rfl

theorem excPsi_injective (q : ℕ) : Function.Injective ((excPsi U V).f q).hom := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [excPsi_f_mk] at hx
  have hmemV := (mem_range_sSetChainMap (toSmallV U V) q (toSmallV_injective U V _) _).1
    ((Submodule.Quotient.mk_eq_zero _).1 hx)
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  refine (mem_range_sSetChainMap (TopCat.toSSet.map (incInterU U V)) q
    (toSSet_map_injective _ (incInterU_injective U V) _) c).2 fun σ hσ => ?_
  have hsupp : (toSmallU U V).app _ σ ∈ (sSetChainMap (toSmallU U V) q c).support := by
    refine Finsupp.mem_support_iff.2 ?_
    rw [show sSetChainMap (toSmallU U V) q c
      = Finsupp.mapDomain ((toSmallU U V).app _) c from rfl,
      Finsupp.mapDomain_apply (toSmallU_injective U V _)]
    exact Finsupp.mem_support_iff.1 hσ
  have hV : carrier ((toSmallU U V).app (op (SimplexCategory.mk q)) σ).1 ⊆ V := by
    have := hmemV _ hsupp
    rw [range_toSmallV] at this
    exact this
  exact mem_range_incInterU U V σ hV

theorem excPsi_surjective (q : ℕ) : Function.Surjective ((excPsi U V).f q).hom := by
  classical
  intro y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine mem_of_single (Submodule.mkQ _) (LinearMap.range ((excPsi U V).f q).hom) z
    fun τ hτ => ?_
  rcases τ.2 with hU' | hV'
  · obtain ⟨σ, hσ⟩ : τ ∈ Set.range ((toSmallU U V).app (op (SimplexCategory.mk q))) := by
      rw [range_toSmallU]; exact hU'
    refine ⟨Submodule.Quotient.mk (Finsupp.single σ 1), ?_⟩
    show Submodule.Quotient.mk (sSetChainMap (toSmallU U V) q (Finsupp.single σ 1))
      = Submodule.Quotient.mk (Finsupp.single τ 1)
    rw [sSetChainMap_single, hσ]
  · refine ⟨0, ?_⟩
    rw [map_zero]
    symm
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    refine (mem_range_sSetChainMap (toSmallV U V) q (toSmallV_injective U V _) _).2 fun ρ hρ => ?_
    rcases Finset.mem_singleton.1 (Finsupp.support_single_subset hρ) with rfl
    rw [range_toSmallV]
    exact hV'

instance excPsi_isIso_f (q : ℕ) : IsIso ((excPsi U V).f q) :=
  (ConcreteCategory.isIso_iff_bijective _).2 ⟨excPsi_injective U V q, excPsi_surjective U V q⟩

/-- **The excision comparison is a degreewise isomorphism of relative chain complexes.** -/
instance excPsi_isIso : IsIso (excPsi U V) :=
  HomologicalComplex.Hom.isIso_of_components _


/-! ## WP9 : the short exact sequence `0 → C^{small}/C(V) → C(X)/C(V) → C(X)/C^{small} → 0` -/

theorem sSetChainMap_id (S : SSet.{u}) (q : ℕ) (c : SSetChain S q) :
    sSetChainMap (𝟙 S) q c = c := Finsupp.mapDomain_id

theorem excSC_zero : excAlpha U V ≫ excBeta U V = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun q => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Submodule.Quotient.mk (p := LinearMap.range (sSetChainMap (smallInc U V) q))
    (sSetChainMap (𝟙 (TopCat.toSSet.obj X)) q (sSetChainMap (smallInc U V) q c)) = 0
  rw [sSetChainMap_id]
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨c, rfl⟩

/-- The short complex `C_*^{small}/C_*(V) → C_*(X)/C_*(V) → C_*(X)/C_*^{small}`. -/
def excSC : ShortComplex (ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ) :=
  ShortComplex.mk (excAlpha U V) (excBeta U V) (excSC_zero U V)

theorem excAlpha_injective (q : ℕ) : Function.Injective ((excAlpha U V).f q).hom := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx' : Submodule.Quotient.mk
      (p := LinearMap.range (sSetChainMap (TopCat.toSSet.map (subInc V)) q))
      (sSetChainMap (smallInc U V) q c) = 0 := hx
  have hmem := (mem_range_sSetChainMap (TopCat.toSSet.map (subInc V)) q
    (toSSet_map_injective _ (subInc_injective V) _) _).1
    ((Submodule.Quotient.mk_eq_zero _).1 hx')
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  refine (mem_range_sSetChainMap (toSmallV U V) q (toSmallV_injective U V _) c).2 fun σ hσ => ?_
  have hsupp : (smallInc U V).app _ σ ∈ (sSetChainMap (smallInc U V) q c).support := by
    refine Finsupp.mem_support_iff.2 ?_
    rw [show sSetChainMap (smallInc U V) q c
      = Finsupp.mapDomain ((smallInc U V).app _) c from rfl,
      Finsupp.mapDomain_apply (smallInc_injective U V _)]
    exact Finsupp.mem_support_iff.1 hσ
  have hV : carrier σ.1 ⊆ V := by
    have := hmem _ hsupp
    rw [range_toSSet_subInc] at this
    exact this
  rw [range_toSmallV]
  exact hV

theorem excBeta_surjective (q : ℕ) : Function.Surjective ((excBeta U V).f q).hom := by
  intro y
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine ⟨Submodule.Quotient.mk c, ?_⟩
  show Submodule.Quotient.mk (sSetChainMap (𝟙 (TopCat.toSSet.obj X)) q c)
    = Submodule.Quotient.mk c
  rw [sSetChainMap_id]

/-- **The third-isomorphism short exact sequence.** -/
theorem excSC_shortExact : (excSC U V).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun q => ?_
  have hmono : Mono ((excSC U V).map
      (HomologicalComplex.eval (ModuleCat.{u} (ZMod 2)) (ComplexShape.down ℕ) q)).f :=
    (ModuleCat.mono_iff_injective _).2 (excAlpha_injective U V q)
  have hepi : Epi ((excSC U V).map
      (HomologicalComplex.eval (ModuleCat.{u} (ZMod 2)) (ComplexShape.down ℕ) q)).g :=
    (ModuleCat.epi_iff_surjective _).2 (excBeta_surjective U V q)
  refine { mono_f := hmono, epi_g := hepi, exact := ?_ }
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine LinearMap.mem_ker.2 ?_
    show Submodule.Quotient.mk (p := LinearMap.range (sSetChainMap (smallInc U V) q))
      (sSetChainMap (𝟙 (TopCat.toSSet.obj X)) q (sSetChainMap (smallInc U V) q c)) = 0
    rw [sSetChainMap_id]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨c, rfl⟩
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hbeta : ((excSC U V).map
        (HomologicalComplex.eval (ModuleCat.{u} (ZMod 2)) (ComplexShape.down ℕ) q)).g.hom
        (Submodule.Quotient.mk c)
        = Submodule.Quotient.mk (p := LinearMap.range (sSetChainMap (smallInc U V) q)) c := by
      show Submodule.Quotient.mk (sSetChainMap (𝟙 (TopCat.toSSet.obj X)) q c) = _
      rw [sSetChainMap_id]
    rw [LinearMap.mem_ker, hbeta] at hx
    obtain ⟨c', hc'⟩ := (Submodule.Quotient.mk_eq_zero _).1 hx
    exact ⟨Submodule.Quotient.mk c', by
      show Submodule.Quotient.mk (sSetChainMap (smallInc U V) q c') = Submodule.Quotient.mk c
      rw [hc']⟩


/-! ## WP8 : the small-simplices quasi-isomorphism -/

section WP8

variable (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

include hU hV hUV

theorem mono_homologyMap_smallInc (q : ℕ) :
    Mono (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (smallInc U V)) q) := by
  have hex := pair_exact₁ (smallInc U V) (smallInc_injective U V) q
  rw [ShortComplex.exact_iff_mono _
    ((isZero_relSmall_homology U V hU hV hUV (q + 1)).eq_of_src _ 0)] at hex
  exact hex

theorem epi_homologyMap_smallInc (q : ℕ) :
    Epi (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (smallInc U V)) q) := by
  have hex := pair_exact₂ (smallInc U V) (smallInc_injective U V) q
  rw [ShortComplex.exact_iff_epi _
    ((isZero_relSmall_homology U V hU hV hUV q).eq_of_tgt _ 0)] at hex
  exact hex

/-- **WP8, the Small-Simplices theorem.**  For an open cover `X = U ∪ V`, the inclusion of the
subcomplex of `(U,V)`-small singular chains induces an isomorphism on homology in every
degree. -/
theorem isIso_homologyMap_smallInc (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (sSetChainComplexFunctor.map (smallInc U V)) q) :=
  haveI := mono_homologyMap_smallInc U V hU hV hUV q
  haveI := epi_homologyMap_smallInc U V hU hV hUV q
  isIso_of_mono_of_epi _

/-- **WP8, packaged.**  The small-chain inclusion is a quasi-isomorphism. -/
theorem quasiIso_smallInc :
    QuasiIso (sSetChainComplexFunctor.map (smallInc U V)) where
  quasiIsoAt q := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact isIso_homologyMap_smallInc U V hU hV hUV q

end WP8


/-! ## WP9 : the excision theorem -/

section WP9

variable (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

include hU hV hUV

theorem mono_homologyMap_excAlpha (q : ℕ) :
    Mono (HomologicalComplex.homologyMap (excAlpha U V) q) := by
  have hex := (excSC_shortExact U V).homology_exact₁ (q + 1) q (by simp)
  rw [ShortComplex.exact_iff_mono _
    ((isZero_relSmall_homology U V hU hV hUV (q + 1)).eq_of_src _ 0)] at hex
  exact hex

theorem epi_homologyMap_excAlpha (q : ℕ) :
    Epi (HomologicalComplex.homologyMap (excAlpha U V) q) := by
  have hex := (excSC_shortExact U V).homology_exact₂ q
  rw [ShortComplex.exact_iff_epi _
    ((isZero_relSmall_homology U V hU hV hUV q).eq_of_tgt _ 0)] at hex
  exact hex

theorem isIso_homologyMap_excAlpha (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (excAlpha U V) q) :=
  haveI := mono_homologyMap_excAlpha U V hU hV hUV q
  haveI := epi_homologyMap_excAlpha U V hU hV hUV q
  isIso_of_mono_of_epi _

/-- **WP9, singular excision over `ZMod 2`.**  If `U` and `V` are open subsets of `X` with
`U ∪ V = X`, then the inclusion of pairs `(U, U ∩ V) → (X, V)` induces an isomorphism on
relative singular homology with `ℤ₂`-coefficients in every degree. -/
theorem isIso_homologyMap_excisionMap (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (excisionMap U V) q) := by
  haveI := isIso_homologyMap_excAlpha U V hU hV hUV q
  rw [excisionMap_factor, HomologicalComplex.homologyMap_comp]
  infer_instance

/-- **WP9, singular excision over `ZMod 2`, as an isomorphism.**
`H_q(U, U ∩ V; ℤ₂) ≅ H_q(X, V; ℤ₂)`. -/
noncomputable def excisionIso (q : ℕ) :
    (relSingChainCx (incInterU U V)).homology q ≅ (relSingChainCx (subInc V)).homology q :=
  haveI := isIso_homologyMap_excisionMap U V hU hV hUV q
  asIso (HomologicalComplex.homologyMap (excisionMap U V) q)

end WP9


end SpineTask18
