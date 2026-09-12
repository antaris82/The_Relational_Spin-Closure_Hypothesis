import RequestProject.Spine.Nerve.StandardCell.RelativeComparison

/-!
# Task 22, WP1/WP2 : the finite cell-family decomposition of the *simplicial* skeletal pair

This module passes from the single standard cell of Task 21 to the family of `r`-cells
attached to `K^{(r-1)} = Sk X r` in order to build `K^{(r)} = Sk X (r+1)`.

The mathematical content is entirely on the **source** (simplicial) side; the topological
counterpart is treated — and reported as a blocker — in the companion audit.

## What is proved here

* `isZero_skelRel_homology` — `H_q^{simp}(Sk X (r+1), Sk X r; ℤ₂) = 0` for `q ≠ r`.
  Proof: Task 13 already shows that the *normalized* relative chains of the skeletal pair
  vanish in every degree `q ≠ r` (`relNormChain_subsingleton_of_lt`,
  `relNormChain_subsingleton_of_gt`), hence `P∞` lands in the chains of the subcomplex; the
  Task-13 homotopy `∂h + h∂ = id + P∞`, natural by Task 21's `normHtpy_natural`, then exhibits
  every relative cycle as a relative boundary.
* `phi` and `bijective_phi` — in the critical degree `r` the map

  `(X.nonDegenerate r →₀ ℤ₂) → H_r^{simp}(Sk X (r+1), Sk X r; ℤ₂)`,
  `σ ↦ [σ]`,

  is bijective.  Again the input is the Task-13 computation
  (`relNormChainEquiv`, `nonDegenerateSkeletonEquiv`): the relative normalized chains are free
  on `X.nonDegenerate r` and vanish elsewhere.
* `srcDecomp` and `isIso_srcDecomp` — **the source finite-family decomposition**

  `⊕_{σ ∈ X.nonDegenerate r} H_q^{simp}(Δ[r], ∂Δ[r]; ℤ₂) ≅ H_q^{simp}(Sk X (r+1), Sk X r; ℤ₂)`,

  realised by the *canonical* cell maps: the `σ`-component is the map of relative complexes
  induced by the Task-15 characteristic map `cellChar X r σ` and attaching map
  `cellAttach X r σ`.  No noncanonical isomorphism is chosen.

The direct sum is taken as `Finsupp`, i.e. `⊕_σ M = (X.nonDegenerate r →₀ M)`; for a *finite*
family this is the finite biproduct (`finiteBiproduct_of_fintype`).  The source decomposition
turns out **not** to need any finiteness hypothesis; see `TASK22_AUDIT.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet NerveGeom SpineTask13
  SpineTask14 SpineTask15 SpineTask19 SpineTask20 SpineTask21

universe u

namespace SpineTask22

/-! ## WP1 : the finite direct sum we use

For a family of modules indexed by `α` and constantly equal to `M`, the coproduct is
`α →₀ M`.  If `α` is finite this is the finite biproduct `∀ a, M`. -/

/-- **WP1.**  For a *finite* index type the `Finsupp` direct sum used below is the finite
biproduct (the product of the summands). -/
def finiteBiproduct_of_fintype (α : Type u) [Finite α] (M : Type u) [AddCommGroup M]
    [Module (ZMod 2) M] : (α →₀ M) ≃ₗ[ZMod 2] (α → M) :=
  Finsupp.linearEquivFunOnFinite (ZMod 2) M α

/-! ## General relative-chain lemmas -/

section General

variable {S T : SSet.{u}}

/-- **The general vanishing criterion.**  If the Dold–Kan projector `P∞` carries a relative
cycle into the chains of the subobject, then its relative homology class vanishes.  This is
the argument of Task 21's `isZero_simpRel_homology`, isolated. -/
theorem hcls_rel_eq_zero_of_proj_mem_range (f : S ⟶ T) (q : ℕ) (x : SSetChain T q)
    (hz : (Submodule.Quotient.mk x : RelChainMod f q) ∈ Zc (relChainCx f) q)
    (hx : proj T q x ∈ LinearMap.range (sSetChainMap f q)) :
    hcls (K := relChainCx f) (Submodule.Quotient.mk x) hz = 0 := by
  rw [hcls_eq_zero_iff]
  refine ⟨Submodule.Quotient.mk (normHtpy T q x), ?_⟩
  rw [relChainCx_d]
  show Submodule.Quotient.mk (sSetBoundary T q (normHtpy T q x)) = _
  refine (Submodule.Quotient.eq _).2 ?_
  match q with
  | 0 =>
      have h := congrFun (congrArg DFunLike.coe (normHtpy_zero T)) x
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply] at h
      rw [h]
      obtain ⟨y, hy⟩ := hx
      refine ⟨y, ?_⟩
      rw [hy]
      abel
  | (m + 1) =>
      have h := congrFun (congrArg DFunLike.coe (normHtpy_succ T m)) x
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply] at h
      have hbd : sSetBoundary T m x ∈ LinearMap.range (sSetChainMap f m) := by
        have hz' : relBoundary f m (Submodule.Quotient.mk x) = 0 := by
          have := hz
          rw [mem_Zc_succ, relChainCx_d] at this
          exact this
        rw [relBoundary_mk] at hz'
        exact (Submodule.Quotient.mk_eq_zero _).1 hz'
      obtain ⟨w, hw⟩ := hbd
      obtain ⟨y, hy⟩ := hx
      refine ⟨y + normHtpy _ m w, ?_⟩
      have hhw : normHtpy T m (sSetBoundary T m x)
          = sSetChainMap f (m + 1) (normHtpy _ m w) := by
        rw [← hw, normHtpy_natural]
      have key : sSetBoundary T (m + 1) (normHtpy T (m + 1) x)
          = x + (proj T (m + 1) x + normHtpy T m (sSetBoundary T m x)) :=
        calc sSetBoundary T (m + 1) (normHtpy T (m + 1) x)
            = sSetBoundary T (m + 1) (normHtpy T (m + 1) x)
              + (normHtpy T m (sSetBoundary T m x)
                + normHtpy T m (sSetBoundary T m x)) := by
              rw [z2_add_self_gen, add_zero]
          _ = (sSetBoundary T (m + 1) (normHtpy T (m + 1) x)
                + normHtpy T m (sSetBoundary T m x))
              + normHtpy T m (sSetBoundary T m x) := by abel
          _ = (x + proj T (m + 1) x) + normHtpy T m (sSetBoundary T m x) := by rw [h]
          _ = _ := by abel
      rw [map_add, hy, ← hhw, key]
      abel

/-- If every normalized chain of `T` in degree `q` comes from `S`, then `P∞` of every chain of
`T` comes from `S`. -/
theorem proj_mem_range_of_normMap_surj (f : S ⟶ T) (q : ℕ)
    (h : ∀ z : NormChain T q, z ∈ LinearMap.range (normMap f q))
    (x : SSetChain T q) :
    proj T q x ∈ LinearMap.range (sSetChainMap f q) := by
  obtain ⟨y, hy⟩ := h (normProj T q x)
  obtain ⟨v, rfl⟩ := normProj_surjective S q y
  have hnat : normProj T q (sSetChainMap f q v) = normMap f q (normProj S q v) :=
    congrFun (congrArg DFunLike.coe (normProj_natural f q)) v
  have hd : x - sSetChainMap f q v ∈ degenSubmodule T q := by
    rw [← Submodule.Quotient.eq]
    show normProj T q x = normProj T q (sSetChainMap f q v)
    rw [hnat, hy]
  have h0 : proj T q (x - sSetChainMap f q v) = 0 := proj_degen_zero T q hd
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, SpineTask21.proj_natural f q v]
  exact ⟨proj S q v, rfl⟩

/-- In a `ℤ₂`-module subtraction is addition. -/
theorem z2_sub_eq_add {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (a b : M) :
    a - b = a + b := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (z2_add_self_gen b)]

/-- If every chain in degree `q` of a chain complex is a cycle, then taking homology classes
is a linear map. -/
def clsAll {K : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ} (q : ℕ)
    (hall : ∀ z : K.X q, z ∈ Zc K q) : (K.X q) →ₗ[ZMod 2] (K.homology q) :=
  ((hIso K q).inv.hom).comp
    (((LinearMap.range ((scN K q).moduleCatToCycles)).mkQ).comp
      (LinearMap.codRestrict (Zc K q) LinearMap.id hall))

theorem clsAll_apply {K : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ} (q : ℕ)
    (hall : ∀ z : K.X q, z ∈ Zc K q) (z : K.X q) :
    clsAll q hall z = hcls z (hall z) := rfl

end General

/-! ## The skeletal pair : vanishing away from the critical degree -/

section Skeletal

variable (X : SSet.{u}) (r : ℕ)

/-- Away from degree `r` every normalized chain of `K^{(r)}` comes from `K^{(r-1)}`.  This is
exactly the Task-13 computation of the relative normalized chains. -/
theorem normChain_mem_range_of_ne {q : ℕ} (hqr : q ≠ r) (z : NormChain (Sk X (r + 1)) q) :
    z ∈ LinearMap.range (normMap (skInc X r) q) := by
  have hsub : Subsingleton (RelNormChain X r q) := by
    rcases lt_or_gt_of_ne hqr with h | h
    · exact relNormChain_subsingleton_of_lt h
    · exact relNormChain_subsingleton_of_gt h
  have hz : (Submodule.Quotient.mk z : RelNormChain X r q) = 0 := Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero _).1 hz

theorem proj_skel_mem_range {q : ℕ} (hqr : q ≠ r) (x : SSetChain (Sk X (r + 1)) q) :
    proj (Sk X (r + 1)) q x ∈ LinearMap.range (sSetChainMap (skInc X r) q) :=
  proj_mem_range_of_normMap_surj _ q (normChain_mem_range_of_ne X r hqr) x

/-- **The skeletal relative simplicial homology vanishes away from degree `r`.** -/
theorem isZero_skelRel_homology {q : ℕ} (hqr : q ≠ r) :
    IsZero ((relChainCx (skInc X r)).homology q) := by
  refine ModuleCat.isZero_iff_subsingleton.2 (subsingleton_of_forall_eq 0 fun t => ?_)
  obtain ⟨z, hz, rfl⟩ := hcls_surjective t
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact hcls_rel_eq_zero_of_proj_mem_range _ q x hz (proj_skel_mem_range X r hqr x)

/-- Below the critical degree the skeletal inclusion is bijective on simplices, so the
relative chains vanish. -/
theorem subsingleton_relChain_of_lt {q : ℕ} (hq : q < r) :
    Subsingleton (RelChainMod (skInc X r) q) := by
  have hsimp : Function.Surjective ((skInc X r).app (op (SimplexCategory.mk q))) := by
    rintro ⟨y, hy⟩
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [X.skeleton_obj_eq_top hq]
    trivial
  have hchain : Function.Surjective (sSetChainMap (skInc X r) q) := by
    intro c
    refine ⟨Finsupp.mapDomain (Function.surjInv hsimp) c, ?_⟩
    show Finsupp.mapDomain _ (Finsupp.mapDomain _ c) = c
    rw [← Finsupp.mapDomain_comp,
      show ((skInc X r).app (op (SimplexCategory.mk q))) ∘ Function.surjInv hsimp = id from
        funext fun y => Function.surjInv_eq hsimp y, Finsupp.mapDomain_id]
  have htop : LinearMap.range (sSetChainMap (skInc X r) q) = ⊤ :=
    LinearMap.range_eq_top.2 hchain
  rw [show RelChainMod (skInc X r) q
      = (SSetChain (Sk X (r + 1)) q ⧸ LinearMap.range (sSetChainMap (skInc X r) q)) from rfl,
    htop]
  infer_instance

/-- In the critical degree *every* relative chain of the skeletal pair is a cycle: the
relative chains one degree below vanish. -/
theorem mem_Zc_top (z : (relChainCx (skInc X r)).X r) :
    z ∈ Zc (relChainCx (skInc X r)) r := by
  match r with
  | 0 => exact mem_Zc_zero _
  | (m + 1) =>
      rw [mem_Zc_succ]
      exact (subsingleton_relChain_of_lt X (m + 1) (Nat.lt_succ_self m)).elim _ _

/-- The relative class of a chain in the critical degree, as a linear map. -/
def topCls : SSetChain (Sk X (r + 1)) r →ₗ[ZMod 2] ((relChainCx (skInc X r)).homology r) :=
  (clsAll r (mem_Zc_top X r)).comp
    ((LinearMap.range (sSetChainMap (skInc X r) r)).mkQ)

theorem topCls_apply (x : SSetChain (Sk X (r + 1)) r) :
    topCls X r x = hcls (K := relChainCx (skInc X r))
      (Submodule.Quotient.mk x) (mem_Zc_top X r _) := rfl

theorem topCls_surjective : Function.Surjective (topCls X r) := by
  intro t
  obtain ⟨z, _, rfl⟩ := hcls_surjective t
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨x, rfl⟩

/-- `P∞` of a chain of `K^{(r)}` in degree `r + 1` vanishes: every `(r+1)`-simplex of the
`r`-skeleton is degenerate. -/
theorem normProj_succ_eq_zero (W : SSetChain (Sk X (r + 1)) (r + 1)) :
    normProj (Sk X (r + 1)) (r + 1) W = 0 :=
  haveI : Subsingleton (NormChain (Sk X (r + 1)) (r + 1)) :=
    normChain_skeleton_subsingleton (le_refl (r + 1))
  Subsingleton.elim _ _

/-- In the critical degree the normalized chains of the subskeleton vanish. -/
theorem range_normMap_top_eq_bot : LinearMap.range (normMap (skInc X r) r) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro _ ⟨z, rfl⟩
  haveI : Subsingleton (NormChain (Sk X r) r) := normChain_skeleton_subsingleton (le_refl r)
  rw [Subsingleton.elim z 0, map_zero]
  exact Submodule.zero_mem _

/-- **The relative class in the critical degree only depends on the normalization.** -/
theorem topCls_eq_of_normProj_eq (x y : SSetChain (Sk X (r + 1)) r)
    (h : normProj (Sk X (r + 1)) r x = normProj (Sk X (r + 1)) r y) :
    topCls X r x = topCls X r y := by
  have hd : x - y ∈ degenSubmodule (Sk X (r + 1)) r := (Submodule.Quotient.eq _).1 h
  have hzero : topCls X r (x - y) = 0 := by
    rw [topCls_apply]
    refine hcls_rel_eq_zero_of_proj_mem_range _ r (x - y) _ ?_
    rw [proj_degen_zero _ _ hd]
    exact Submodule.zero_mem _
  rw [map_sub] at hzero
  exact sub_eq_zero.1 hzero

/-! ## The critical degree : a free basis indexed by the nondegenerate `r`-simplices -/

theorem cellSimplex_injective :
    Function.Injective (fun σ : X.nonDegenerate r => (cellSimplex σ : (Sk X (r + 1)) _⦋r⦌)) := by
  intro a b h
  exact Subtype.ext (congrArg (fun z : (Sk X (r + 1)) _⦋r⦌ => (z : X _⦋r⦌)) h)

/-- The chain attached to a `ℤ₂`-combination of nondegenerate `r`-simplices. -/
def cellChainMap : (↑(X.nonDegenerate r) →₀ ZMod 2) →ₗ[ZMod 2] SSetChain (Sk X (r + 1)) r :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (fun σ : X.nonDegenerate r => cellSimplex σ)

theorem cellChainMap_single (σ : X.nonDegenerate r) (c : ZMod 2) :
    cellChainMap X r (Finsupp.single σ c) = Finsupp.single (cellSimplex σ) c :=
  Finsupp.mapDomain_single

theorem cellChainMap_apply_nonDeg (c : ↑(X.nonDegenerate r) →₀ ZMod 2)
    (a : ↑((Sk X (r + 1)).nonDegenerate r)) :
    cellChainMap X r c a.1 = c (nonDegenerateSkeletonEquiv X r a) := by
  have ha : (a.1 : (Sk X (r + 1)) _⦋r⦌)
      = cellSimplex (nonDegenerateSkeletonEquiv X r a) := rfl
  rw [ha]
  exact Finsupp.mapDomain_apply (cellSimplex_injective X r) c _

/-- **The critical-degree comparison** `(X.nonDegenerate r →₀ ℤ₂) → H_r^{simp}(K^{(r)},K^{(r-1)})`,
`σ ↦ [σ]`. -/
def phi : (↑(X.nonDegenerate r) →₀ ZMod 2) →ₗ[ZMod 2]
    ((relChainCx (skInc X r)).homology r) :=
  (topCls X r).comp (cellChainMap X r)

theorem phi_apply (c : ↑(X.nonDegenerate r) →₀ ZMod 2) :
    phi X r c = topCls X r (cellChainMap X r c) := rfl

theorem phi_injective : Function.Injective (phi X r) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  rw [phi_apply, topCls_apply, hcls_eq_zero_iff] at hc
  obtain ⟨w, hw⟩ := hc
  obtain ⟨W, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  simp only [relChainCx_d, ModuleCat.hom_ofHom] at hw
  obtain ⟨v, hv⟩ := (Submodule.Quotient.eq _).1 hw
  have hcomm := congrFun (congrArg DFunLike.coe (normProj_comm (Sk X (r + 1)) r)) W
  simp only [LinearMap.comp_apply] at hcomm
  have h1 : normProj (Sk X (r + 1)) r (sSetBoundary (Sk X (r + 1)) r W) = 0 := by
    rw [hcomm, normProj_succ_eq_zero, map_zero]
  have hnat := congrFun (congrArg DFunLike.coe (normProj_natural (skInc X r) r)) v
  simp only [LinearMap.comp_apply] at hnat
  have h2 : normProj (Sk X (r + 1)) r (sSetChainMap (skInc X r) r v) = 0 := by
    rw [hnat]
    have hmem : normMap (skInc X r) r (normProj (Sk X r) r v)
        ∈ LinearMap.range (normMap (skInc X r) r) := ⟨_, rfl⟩
    rw [range_normMap_top_eq_bot] at hmem
    exact hmem
  have h3 : normProj (Sk X (r + 1)) r (cellChainMap X r c) = 0 := by
    rw [hv, map_sub, h1, zero_sub, neg_eq_zero] at h2
    exact h2
  ext σ
  have h4 := normChainEquiv_apply (Sk X (r + 1)) r (cellChainMap X r c)
    ((nonDegenerateSkeletonEquiv X r).symm σ)
  rw [h3, cellChainMap_apply_nonDeg, Equiv.apply_symm_apply] at h4
  simpa using h4.symm

theorem phi_surjective : Function.Surjective (phi X r) := by
  intro t
  obtain ⟨x, rfl⟩ := topCls_surjective X r t
  refine ⟨Finsupp.equivMapDomain (nonDegenerateSkeletonEquiv X r)
    (normChainEquiv (Sk X (r + 1)) r (normProj (Sk X (r + 1)) r x)), ?_⟩
  refine topCls_eq_of_normProj_eq X r _ x ?_
  refine (normChainEquiv (Sk X (r + 1)) r).injective ?_
  ext a
  rw [normChainEquiv_apply, normChainEquiv_apply, cellChainMap_apply_nonDeg,
    Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]
  exact normChainEquiv_apply (Sk X (r + 1)) r x a

theorem bijective_phi : Function.Bijective (phi X r) :=
  ⟨phi_injective X r, phi_surjective X r⟩

/-! ## The canonical cell maps -/

/-- **The canonical `σ`-component.**  The map of relative simplicial complexes induced by the
Task-15 characteristic map `cellChar X r σ : Δ[r] ⟶ K^{(r)}` and attaching map
`cellAttach X r σ : ∂Δ[r] ⟶ K^{(r-1)}`.  Nothing is chosen: these are the Yoneda transposes of
the nondegenerate simplex `σ` itself. -/
def cellPairMap (σ : X.nonDegenerate r) : simpRel.{u} r ⟶ relChainCx (skInc X r) :=
  relChainCxMap (bdIncl.{u} r) (skInc X r) (cellAttach X r σ) (cellChar X r σ)
    (cellAttach_comm X r σ).symm

theorem cellChar_app_topSimp (σ : X.nonDegenerate r) :
    (cellChar X r σ).app (op (SimplexCategory.mk r)) (topSimp.{u} r) = cellSimplex σ := by
  refine Subtype.ext ?_
  show X.map (𝟙 (SimplexCategory.mk r)).op σ.1 = σ.1
  rw [op_id, FunctorToTypes.map_id_apply]

theorem cellPairMap_relTop (σ : X.nonDegenerate r) :
    ((cellPairMap X r σ).f r).hom (relTopChain.{u} r)
      = Submodule.Quotient.mk (Finsupp.single (cellSimplex σ) (1 : ZMod 2)) := by
  show Submodule.Quotient.mk
    (sSetChainMap (cellChar X r σ) r (Finsupp.single (topSimp.{u} r) (1 : ZMod 2))) = _
  rw [sSetChainMap_single, cellChar_app_topSimp]

/-- **The generator statement, source side.**  The `σ`-component carries the standard-cell
generator `e_r` to the class of `σ`. -/
theorem homologyMap_cellPairMap_simpTopClass (σ : X.nonDegenerate r) :
    (HomologicalComplex.homologyMap (cellPairMap X r σ) r).hom (simpTopClass.{u} r)
      = topCls X r (Finsupp.single (cellSimplex σ) (1 : ZMod 2)) := by
  rw [simpTopClass, homologyMap_hcls]
  exact hcls_congr _ _ (cellPairMap_relTop X r σ)

end Skeletal

/-! ## The standard-cell summand is a line -/

/-- `H_r^{simp}(Δ[r], ∂Δ[r]; ℤ₂) ≅ ℤ₂`, generated by the frozen class `e_r`. -/
def lineEquiv (r : ℕ) : ZMod 2 ≃ₗ[ZMod 2] ((simpRel.{u} r).homology r) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton (ZMod 2) _ (simpTopClass.{u} r)) <| by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro c hc
      have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      rcases hcases c with rfl | rfl
      · rfl
      · rw [LinearMap.toSpanSingleton_apply, one_smul] at hc
        exact absurd hc (simpTopClass_ne_zero.{u} r)
    · intro t
      obtain ⟨c, rfl⟩ := exists_smul_simpTopClass.{u} r t
      exact ⟨c, rfl⟩

@[simp] theorem lineEquiv_apply (r : ℕ) (c : ZMod 2) :
    lineEquiv.{u} r c = c • simpTopClass.{u} r := rfl

/-! ## WP2 : the source finite-family decomposition -/

section Decomposition

variable (X : SSet.{u}) (r q : ℕ)

/-- `⊕_{σ ∈ X.nonDegenerate r} H_q^{simp}(Δ[r], ∂Δ[r]; ℤ₂)`, as a `ℤ₂`-module.  The direct sum
of a family of modules indexed by `α` and constantly equal to `M` is `α →₀ M`. -/
def srcSumMod : ModuleCat.{u} (ZMod 2) :=
  ModuleCat.of (ZMod 2) (↑(X.nonDegenerate r) →₀ ((simpRel.{u} r).homology q))

/-- **The source decomposition map.**  On the `σ`-summand it is the map induced by the
canonical characteristic map of the cell of `σ`. -/
def srcDecomp : srcSumMod X r q ⟶ (relChainCx (skInc X r)).homology q :=
  ModuleCat.ofHom (Finsupp.lsum (ZMod 2)
    fun σ => (HomologicalComplex.homologyMap (cellPairMap X r σ) q).hom)

theorem srcDecomp_single (σ : X.nonDegenerate r) (m : (simpRel.{u} r).homology q) :
    (srcDecomp X r q).hom (Finsupp.single σ m)
      = (HomologicalComplex.homologyMap (cellPairMap X r σ) q).hom m := by
  show Finsupp.sum (Finsupp.single σ m)
    (fun σ m => (HomologicalComplex.homologyMap (cellPairMap X r σ) q).hom m) = _
  exact Finsupp.sum_single_index (map_zero _)

/-- The critical-degree source direct sum, written with `ℤ₂`-coefficients through the
identification `H_r^{simp}(Δ[r],∂Δ[r];ℤ₂) ≅ ℤ₂` of `lineEquiv`. -/
def lineSumEquiv : (↑(X.nonDegenerate r) →₀ ZMod 2) ≃ₗ[ZMod 2] srcSumMod X r r :=
  Finsupp.mapRange.linearEquiv (lineEquiv.{u} r)

theorem lineSumEquiv_single (σ : X.nonDegenerate r) :
    lineSumEquiv X r (Finsupp.single σ (1 : ZMod 2))
      = Finsupp.single σ (simpTopClass.{u} r) := by
  show Finsupp.mapRange (lineEquiv.{u} r) (map_zero _) (Finsupp.single σ (1 : ZMod 2)) = _
  rw [Finsupp.mapRange_single]
  exact congrArg (Finsupp.single σ) (one_smul _ _)

theorem srcDecomp_lineSumEquiv :
    ((srcDecomp X r r).hom).comp (lineSumEquiv X r).toLinearMap = phi X r := by
  refine Finsupp.lhom_ext' fun σ => LinearMap.ext_ring ?_
  show (srcDecomp X r r).hom (lineSumEquiv X r (Finsupp.single σ (1 : ZMod 2)))
    = phi X r (Finsupp.single σ (1 : ZMod 2))
  rw [lineSumEquiv_single, srcDecomp_single, homologyMap_cellPairMap_simpTopClass,
    phi_apply, cellChainMap_single]

theorem bijective_srcDecomp_top : Function.Bijective ((srcDecomp X r r).hom) := by
  have hb : Function.Bijective
      (((srcDecomp X r r).hom).comp (lineSumEquiv X r).toLinearMap) := by
    rw [srcDecomp_lineSumEquiv]
    exact bijective_phi X r
  constructor
  · intro a b hab
    obtain ⟨a', rfl⟩ := (lineSumEquiv X r).surjective a
    obtain ⟨b', rfl⟩ := (lineSumEquiv X r).surjective b
    exact congrArg _ (hb.1 hab)
  · intro t
    obtain ⟨c, hc⟩ := hb.2 t
    exact ⟨_, hc⟩

theorem subsingleton_srcSumMod_of_ne (hqr : q ≠ r) : Subsingleton (srcSumMod X r q) := by
  haveI : Subsingleton ((simpRel.{u} r).homology q) :=
    ModuleCat.isZero_iff_subsingleton.1 (isZero_simpRel_homology.{u} r q hqr)
  show Subsingleton (↑(X.nonDegenerate r) →₀ ((simpRel.{u} r).homology q))
  exact ⟨fun a b => Finsupp.ext fun σ => Subsingleton.elim _ _⟩

/-- **WP2, the source finite-family decomposition, as an isomorphism statement.**

`⊕_{σ ∈ X.nonDegenerate r} H_q^{simp}(Δ[r], ∂Δ[r]; ℤ₂) ≅ H_q^{simp}(Sk X (r+1), Sk X r; ℤ₂)`,

realised by the canonical characteristic maps of the cells. -/
theorem isIso_srcDecomp : IsIso (srcDecomp X r q) := by
  by_cases hqr : q = r
  · subst hqr
    exact (ConcreteCategory.isIso_iff_bijective _).2 (bijective_srcDecomp_top X q)
  · haveI := subsingleton_srcSumMod_of_ne X r q hqr
    haveI : Subsingleton ((relChainCx (skInc X r)).homology q) :=
      ModuleCat.isZero_iff_subsingleton.1 (isZero_skelRel_homology X r hqr)
    exact (ConcreteCategory.isIso_iff_bijective _).2
      ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- **WP2, packaged.**  The source finite-family decomposition isomorphism. -/
def srcDecompIso : srcSumMod X r q ≅ (relChainCx (skInc X r)).homology q :=
  haveI := isIso_srcDecomp X r q
  asIso (srcDecomp X r q)

end Decomposition

end SpineTask22
