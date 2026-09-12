import RequestProject.Spine.AlgebraicTopology.RelativeChains
import RequestProject.Spine.AlgebraicTopology.Subdivision

/-!
# Task 18, WP2 : the singular chain prism

This module builds the mod-2 *chain* prism operator on the project's singular chains, directly
(no cochain duality).  The construction is the classical acyclic-models one, carried out in the
explicit model

`PrismPt n = Δs n × Δs 1`,

the prism over the geometric standard `n`-simplex.  The universal prism chain
`SpineTask18.prismChain n` is defined by a cone recursion, and its boundary is computed in
`SpineTask18.lbd_prismChain`.  The only nontrivial input is that the *coface* operator `cobd`
of the model squares to zero; this is inherited from the pinned Mathlib
`AlternatingCofaceMapComplex` applied to an honest cosimplicial `ℤ₂`-module (`prismCosimp`).
-/

noncomputable section

open CategoryTheory Opposite Simplicial NerveGeom AlgebraicTopology

universe u v

namespace SpineTask18

/-! ## Elementary complements on affine simplices -/

theorem stdC_vertex {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (i : Fin (m + 1)) :
    stdC f (stdSimplex.vertex i) = stdSimplex.vertex (f i) := by
  rw [← combo_vertex, combo_apply_vertex]

theorem stdC_id (n : ℕ) : stdC (fun i : Fin (n + 1) => i) = ContinuousMap.id _ := by
  rw [← combo_id n, combo_vertex]

theorem stdC_comp {l m n : ℕ} (g : Fin (m + 1) → Fin (n + 1)) (f : Fin (l + 1) → Fin (m + 1)) :
    (stdC g).comp (stdC f) = stdC (g ∘ f) := by
  rw [← combo_vertex g, ← combo_vertex f, combo_comp, ← combo_vertex (g ∘ f)]
  exact congrArg combo (funext fun i => by rw [combo_apply_vertex]; rfl)

theorem combo_const {m n : ℕ} (b : Δs n) : combo (fun _ : Fin (m + 1) => b) = ContinuousMap.const _ b := by
  ext x j
  rw [combo_coe]
  show ∑ i, (x : Fin (m+1) → ℝ) i * (b : Fin (n+1) → ℝ) j = (b : Fin (n+1) → ℝ) j
  rw [← Finset.sum_mul, show ∑ i, (x : Fin (m+1) → ℝ) i = 1 from x.2.2, one_mul]

/-- Functoriality of linear chains, in the vertex map. -/
theorem lmap_comp {V W Z : Type*} (h₂ : W → Z) (h₁ : V → W) (k : ℕ) (c : LChain V k) :
    lmap h₂ k (lmap h₁ k c) = lmap (h₂ ∘ h₁) k c := by
  show Finsupp.mapDomain _ (Finsupp.mapDomain _ c) = Finsupp.mapDomain _ c
  rw [← Finsupp.mapDomain_comp]
  rfl

/-! ## The prism over the standard simplex -/

/-- The prism over the geometric standard `n`-simplex, `Δ^n × Δ^1`. -/
abbrev PrismPt (n : ℕ) : Type := Δs n × Δs 1

/-- The bottom endpoint of the interval factor. -/
def e0 : Δs 1 := stdSimplex.vertex 0

/-- The top endpoint of the interval factor. -/
def e1 : Δs 1 := stdSimplex.vertex 1

/-- The affine simplex of the prism spanned by a tuple of points. -/
def pcombo {m n : ℕ} (p : Fin (m + 1) → PrismPt n) : C(Δs m, PrismPt n) :=
  (combo (fun i => (p i).1)).prodMk (combo (fun i => (p i).2))

@[simp] theorem pcombo_apply {m n : ℕ} (p : Fin (m + 1) → PrismPt n) (x : Δs m) :
    pcombo p x = (combo (fun i => (p i).1) x, combo (fun i => (p i).2) x) := rfl

theorem pcombo_stdC {l m n : ℕ} (p : Fin (m + 1) → PrismPt n) (f : Fin (l + 1) → Fin (m + 1)) :
    (pcombo p).comp (stdC f) = pcombo (p ∘ f) := by
  refine ContinuousMap.ext fun x => ?_
  show (combo (fun i => (p i).1) (stdC f x), combo (fun i => (p i).2) (stdC f x))
    = (combo (fun i => (p (f i)).1) x, combo (fun i => (p (f i)).2) x)
  rw [show combo (fun i => (p i).1) (stdC f x)
        = ((combo (fun i => (p i).1)).comp (stdC f)) x from rfl,
    show combo (fun i => (p i).2) (stdC f x)
        = ((combo (fun i => (p i).2)).comp (stdC f)) x from rfl,
    combo_stdC, combo_stdC]
  rfl

/-- The affine map of prisms induced by a reindexing of the simplex factor. -/
def prismPtMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) : PrismPt m → PrismPt n :=
  fun z => (stdC f z.1, z.2)

/-- The affine map of prisms, as a continuous map. -/
def prismPtMapC {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) : C(PrismPt m, PrismPt n) :=
  (stdC f).prodMap (ContinuousMap.id _)

@[simp] theorem prismPtMapC_apply {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (z : PrismPt m) :
    prismPtMapC f z = prismPtMap f z := rfl

theorem pcombo_prismPtMap {k m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (p : Fin (k + 1) → PrismPt m) :
    pcombo (prismPtMap f ∘ p) = (prismPtMapC f).comp (pcombo p) := by
  refine ContinuousMap.ext fun x => ?_
  show (combo (fun i => stdC f (p i).1) x, combo (fun i => (p i).2) x)
    = (stdC f (combo (fun i => (p i).1) x), combo (fun i => (p i).2) x)
  refine Prod.ext ?_ rfl
  show combo (fun i => stdC f (p i).1) x = ((stdC f).comp (combo (fun i => (p i).1))) x
  rw [← combo_vertex f, combo_comp]

theorem prismPtMap_id (n : ℕ) : prismPtMap (fun i : Fin (n + 1) => i) = id := by
  funext z
  rw [prismPtMap, stdC_id]
  rfl

theorem prismPtMap_comp {l m n : ℕ} (g : Fin (m + 1) → Fin (n + 1)) (f : Fin (l + 1) → Fin (m + 1)) :
    prismPtMap g ∘ prismPtMap f = prismPtMap (g ∘ f) := by
  funext z
  show (stdC g (stdC f z.1), z.2) = (stdC (g ∘ f) z.1, z.2)
  rw [show stdC g (stdC f z.1) = ((stdC g).comp (stdC f)) z.1 from rfl, stdC_comp]

/-! ## The coface operator of the model, and `∂ ∘ ∂ = 0` for it -/

/-- The cosimplicial `ℤ₂`-module of linear `k`-chains on the prisms `Δ^n × Δ^1`. -/
def prismCosimp (k : ℕ) : CosimplicialObject (ModuleCat.{0} (ZMod 2)) where
  obj x := ModuleCat.of (ZMod 2) (LChain (PrismPt x.len) k)
  map f := ModuleCat.ofHom (lmap (prismPtMap (⇑f.toOrderHom)) k)
  map_id x := by
    refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
    show lmap (prismPtMap (⇑(SimplexCategory.Hom.id x).toOrderHom)) k c = c
    rw [show (⇑(SimplexCategory.Hom.id x).toOrderHom) = (fun i : Fin (x.len + 1) => i) from rfl,
      prismPtMap_id]
    show Finsupp.mapDomain (fun p => id ∘ p) c = c
    rw [show (fun p : Fin (k+1) → PrismPt x.len => id ∘ p) = id from rfl, Finsupp.mapDomain_id]
  map_comp {x y z} f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
    show lmap (prismPtMap (⇑(f ≫ g).toOrderHom)) k c
      = lmap (prismPtMap (⇑g.toOrderHom)) k (lmap (prismPtMap (⇑f.toOrderHom)) k c)
    rw [lmap_comp, prismPtMap_comp]
    rfl

/-- The coface (model) boundary operator on linear chains of prisms. -/
def cobd (n k : ℕ) : LChain (PrismPt n) k →ₗ[ZMod 2] LChain (PrismPt (n + 1)) k :=
  ∑ i : Fin (n + 2), lmap (prismPtMap (Fin.succAbove i)) k

theorem cobd_objD (n k : ℕ) :
    (AlternatingCofaceMapComplex.objD (prismCosimp k) n).hom = cobd n k := by
  rw [AlternatingCofaceMapComplex.objD]
  simp only [SpineTask13.modCat_hom_zsmul_neg_one_pow]
  rw [cobd, ModuleCat.hom_sum]
  rfl

/-- **`∂ ∘ ∂ = 0` for the model coface operator**, inherited from the pinned alternating
coface map complex. -/
theorem cobd_cobd (n k : ℕ) (c : LChain (PrismPt n) k) :
    cobd (n + 1) k (cobd n k c) = 0 := by
  have h := congrArg ModuleCat.Hom.hom (AlternatingCofaceMapComplex.d_squared (prismCosimp k) n)
  rw [ModuleCat.hom_comp, cobd_objD, cobd_objD] at h
  exact congrFun (congrArg DFunLike.coe h) c

theorem cobd_lbd (n k : ℕ) (c : LChain (PrismPt n) (k + 1)) :
    lbd (PrismPt (n + 1)) k (cobd n (k + 1) c) = cobd n k (lbd (PrismPt n) k c) := by
  rw [cobd, cobd, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (congrFun (congrArg DFunLike.coe (lmap_lbd (prismPtMap (Fin.succAbove i)) k)) c).symm

/-! ## The universal prism chain -/

/-- The bottom face of the prism, as a linear chain. -/
def botP (n : ℕ) : LChain (PrismPt n) n :=
  Finsupp.single (fun i => (stdSimplex.vertex i, e0)) 1

/-- The top face of the prism, as a linear chain. -/
def topP (n : ℕ) : LChain (PrismPt n) n :=
  Finsupp.single (fun i => (stdSimplex.vertex i, e1)) 1

theorem lbd_botP (n : ℕ) :
    lbd (PrismPt (n + 1)) n (botP (n + 1)) = cobd n n (botP n) := by
  rw [botP, lbd_single, cobd, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [botP, lmap_single]
  refine congrArg (fun p => Finsupp.single p (1 : ZMod 2)) (funext fun j => ?_)
  show ((stdSimplex.vertex (Fin.succAbove i j) : Δs (n+1)), e0)
    = (stdC (Fin.succAbove i) (stdSimplex.vertex j), e0)
  rw [stdC_vertex]

theorem lbd_topP (n : ℕ) :
    lbd (PrismPt (n + 1)) n (topP (n + 1)) = cobd n n (topP n) := by
  rw [topP, lbd_single, cobd, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [topP, lmap_single]
  refine congrArg (fun p => Finsupp.single p (1 : ZMod 2)) (funext fun j => ?_)
  show ((stdSimplex.vertex (Fin.succAbove i j) : Δs (n+1)), e1)
    = (stdC (Fin.succAbove i) (stdSimplex.vertex j), e1)
  rw [stdC_vertex]

/-- The apex used for the cone recursion. -/
def apexP (n : ℕ) : PrismPt n := (stdSimplex.vertex 0, e0)

/-- The universal prism chain, and the cycle it bounds, defined by mutual recursion. -/
def prismChain : ∀ n : ℕ, LChain (PrismPt n) (n + 1)
  | 0 => lcone (apexP 0) 0 (botP 0 + topP 0)
  | n + 1 => lcone (apexP (n + 1)) (n + 1)
      (botP (n + 1) + topP (n + 1) + cobd n (n + 1) (prismChain n))

/-- The cycle bounded by the universal prism chain. -/
def prismCyc : ∀ n : ℕ, LChain (PrismPt n) n
  | 0 => botP 0 + topP 0
  | n + 1 => botP (n + 1) + topP (n + 1) + cobd n (n + 1) (prismChain n)

theorem prismChain_eq (n : ℕ) : prismChain n = lcone (apexP n) n (prismCyc n) := by
  cases n with
  | zero => rfl
  | succ n => rfl

theorem cobd_prismCyc (n : ℕ) :
    cobd n n (prismCyc n) = cobd n n (botP n) + cobd n n (topP n) := by
  cases n with
  | zero => rw [prismCyc, map_add]
  | succ n =>
    rw [prismCyc, map_add, map_add, cobd_cobd, add_zero]

/-- **The boundary of the universal prism chain.** -/
theorem lbd_prismChain : ∀ n : ℕ, lbd (PrismPt n) n (prismChain n) = prismCyc n
  | 0 => by
      rw [prismChain_eq, lbd_lcone_zero, prismCyc]
      rw [show laug (PrismPt 0) (botP 0 + topP 0) = 0 from by
        rw [map_add, botP, topP, laug_single, laug_single]; decide]
      rw [Finsupp.single_zero, add_zero]
  | n + 1 => by
      rw [prismChain_eq, lbd_lcone]
      have hcyc : lbd (PrismPt (n + 1)) n (prismCyc (n + 1)) = 0 := by
        rw [prismCyc, map_add, map_add, lbd_botP, lbd_topP, cobd_lbd, lbd_prismChain n,
          cobd_prismCyc]
        rw [show ∀ A B : LChain (PrismPt (n+1)) n, A + B + (A + B) = 0 from
          fun A B => mod2_add_self _]
      rw [hcyc, map_zero, add_zero]

/-! ## Realizing prism chains in a space -/

variable {X Y : TopCat.{u}}

/-- The realization of a linear chain of the prism along a continuous map `F`. -/
def realizeP {n : ℕ} (F : C(PrismPt n, Y)) (k : ℕ) :
    LChain (PrismPt n) k →ₗ[ZMod 2] SSetChain (TopCat.toSSet.obj Y) k :=
  Finsupp.lmapDomain _ _ (fun p => sOf (F.comp (pcombo p)))

@[simp] theorem realizeP_single {n k : ℕ} (F : C(PrismPt n, Y)) (p : Fin (k + 1) → PrismPt n)
    (a : ZMod 2) : realizeP F k (Finsupp.single p a)
      = Finsupp.single (sOf (F.comp (pcombo p))) a :=
  Finsupp.mapDomain_single

/-- Realization of prism chains is a chain map. -/
theorem realizeP_lbd {n : ℕ} (F : C(PrismPt n, Y)) (k : ℕ) (c : LChain (PrismPt n) (k + 1)) :
    realizeP F k (lbd (PrismPt n) k c) = singBd Y k (realizeP F (k + 1) c) := by
  induction c using lchain_induction with
  | h0 => simp
  | hadd f g hf hg => simp only [map_add, hf, hg]
  | hsingle p =>
    rw [lbd_single, map_sum, realizeP_single, singBd_single]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [realizeP_single]
    refine congrArg (fun s => Finsupp.single s (1 : ZMod 2)) ?_
    rw [pre, sMap_sOf, ContinuousMap.comp_assoc, pcombo_stdC]

/-- Realization is natural for affine reparametrisation of the prism. -/
theorem realizeP_prismPtMap {m n k : ℕ} (F : C(PrismPt n, Y)) (f : Fin (m + 1) → Fin (n + 1))
    (c : LChain (PrismPt m) k) :
    realizeP F k (lmap (prismPtMap f) k c) = realizeP (F.comp (prismPtMapC f)) k c := by
  induction c using lchain_induction with
  | h0 => simp
  | hadd u v hu hv => simp only [map_add, hu, hv]
  | hsingle p =>
    rw [lmap_single, realizeP_single, realizeP_single]
    refine congrArg (fun s => Finsupp.single s (1 : ZMod 2)) ?_
    rw [pcombo_prismPtMap, ContinuousMap.comp_assoc]

/-! ## The prism operator of a homotopy -/

variable (H : C(↥X × Δs 1, ↥Y))

/-- The map `x ↦ H (x, b)`, for a point `b` of the interval factor. -/
def endMapC (b : Δs 1) : C(↥X, ↥Y) :=
  H.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ b))

/-- The map `x ↦ H (x, b)`, as a morphism of `TopCat`. -/
def endMap (b : Δs 1) : X ⟶ Y := TopCat.ofHom (endMapC H b)

/-- The prism over a single singular simplex. -/
def prismSimp {n : ℕ} (σ : Sing X n) : SSetChain (TopCat.toSSet.obj Y) (n + 1) :=
  realizeP (H.comp ((sMap σ).prodMap (ContinuousMap.id (Δs 1)))) (n + 1) (prismChain n)

/-- **WP2, the chain prism operator** `P_n : C_n(X) → C_{n+1}(Y)`. -/
def prismOp (n : ℕ) :
    SSetChain (TopCat.toSSet.obj X) n →ₗ[ZMod 2] SSetChain (TopCat.toSSet.obj Y) (n + 1) :=
  Finsupp.linearCombination (ZMod 2) (fun σ => prismSimp H σ)

@[simp] theorem prismOp_single {n : ℕ} (σ : Sing X n) :
    prismOp H n (Finsupp.single σ (1 : ZMod 2)) = prismSimp H σ := by
  rw [prismOp, Finsupp.linearCombination_single, one_smul]

theorem realizeP_botP {n : ℕ} (σ : Sing X n) :
    realizeP (H.comp ((sMap σ).prodMap (ContinuousMap.id (Δs 1)))) n (botP n)
      = singMap (endMap H e0) n (Finsupp.single σ 1) := by
  rw [botP, realizeP_single, singMap_single]
  refine congrArg (fun s => Finsupp.single s (1 : ZMod 2))
    (congrArg sOf (ContinuousMap.ext fun x => ?_))
  show H (sMap σ (combo (fun i => stdSimplex.vertex i) x), combo (fun _ => e0) x)
    = H (sMap σ x, e0)
  rw [combo_id, combo_const]
  rfl

theorem realizeP_topP {n : ℕ} (σ : Sing X n) :
    realizeP (H.comp ((sMap σ).prodMap (ContinuousMap.id (Δs 1)))) n (topP n)
      = singMap (endMap H e1) n (Finsupp.single σ 1) := by
  rw [topP, realizeP_single, singMap_single]
  refine congrArg (fun s => Finsupp.single s (1 : ZMod 2))
    (congrArg sOf (ContinuousMap.ext fun x => ?_))
  show H (sMap σ (combo (fun i => stdSimplex.vertex i) x), combo (fun _ => e1) x)
    = H (sMap σ x, e1)
  rw [combo_id, combo_const]
  rfl

theorem prismSimp_face {n : ℕ} (σ : Sing X (n + 1)) (i : Fin (n + 2)) :
    realizeP ((H.comp ((sMap σ).prodMap (ContinuousMap.id (Δs 1)))).comp
        (prismPtMapC (Fin.succAbove i))) (n + 1) (prismChain n)
      = prismSimp H (pre (stdC (Fin.succAbove i)) σ) := by
  rw [prismSimp]
  refine congrFun (congrArg DFunLike.coe (congrArg (fun F => realizeP F (n + 1)) ?_)) _
  refine ContinuousMap.ext fun z => ?_
  show H (sMap σ (stdC (Fin.succAbove i) z.1), z.2)
    = H (sMap (pre (stdC (Fin.succAbove i)) σ) z.1, z.2)
  rw [sMap_pre]
  rfl

/-- **WP2, the chain prism identity in positive degree.** -/
theorem singBd_prismSimp_succ {n : ℕ} (σ : Sing X (n + 1)) :
    singBd Y (n + 1) (prismSimp H σ)
      = singMap (endMap H e0) (n + 1) (Finsupp.single σ 1)
        + singMap (endMap H e1) (n + 1) (Finsupp.single σ 1)
        + prismOp H n (singBd X n (Finsupp.single σ 1)) := by
  rw [prismSimp, ← realizeP_lbd, lbd_prismChain, prismCyc, map_add, map_add,
    realizeP_botP, realizeP_topP]
  refine congrArg (fun z => singMap (endMap H e0) (n + 1) (Finsupp.single σ 1)
    + singMap (endMap H e1) (n + 1) (Finsupp.single σ 1) + z) ?_
  rw [cobd, LinearMap.sum_apply, map_sum, singBd_single, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [realizeP_prismPtMap, prismSimp_face, prismOp_single]

/-- **WP2, the chain prism identity in degree zero.** -/
theorem singBd_prismSimp_zero (σ : Sing X 0) :
    singBd Y 0 (prismSimp H σ)
      = singMap (endMap H e0) 0 (Finsupp.single σ 1)
        + singMap (endMap H e1) 0 (Finsupp.single σ 1) := by
  rw [prismSimp, ← realizeP_lbd, lbd_prismChain, prismCyc, map_add,
    realizeP_botP, realizeP_topP]


/-! ## The prism identity for arbitrary chains -/

theorem prism_identity_succ (n : ℕ) (c : SSetChain (TopCat.toSSet.obj X) (n + 1)) :
    singBd Y (n + 1) (prismOp H (n + 1) c) + prismOp H n (singBd X n c)
      = singMap (endMap H e0) (n + 1) c + singMap (endMap H e1) (n + 1) c := by
  induction c using lchain_induction with
  | h0 => simp
  | hadd u v hu hv =>
    simp only [map_add]
    rw [show ∀ A B C D : SSetChain (TopCat.toSSet.obj Y) (n + 1),
      A + B + (C + D) = (A + C) + (B + D) from fun A B C D => by abel, hu, hv]
    abel
  | hsingle σ =>
    rw [prismOp_single, singBd_prismSimp_succ, add_assoc, mod2_add_self, add_zero]

theorem prism_identity_zero (c : SSetChain (TopCat.toSSet.obj X) 0) :
    singBd Y 0 (prismOp H 0 c)
      = singMap (endMap H e0) 0 c + singMap (endMap H e1) 0 c := by
  induction c using lchain_induction with
  | h0 => simp
  | hadd u v hu hv =>
    simp only [map_add, hu, hv]
    abel
  | hsingle σ => rw [prismOp_single, singBd_prismSimp_zero]

/-! ## Packaging as a chain homotopy -/

/-- The project's singular chain complex of a space. -/
abbrev singCx (X : TopCat.{u}) : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ :=
  SpineTask14.sSetChainComplexFunctor.obj (TopCat.toSSet.obj X)

/-- The chain map induced by a continuous map. -/
abbrev singCxMap (g : X ⟶ Y) : singCx X ⟶ singCx Y :=
  SpineTask14.sSetChainComplexFunctor.map (TopCat.toSSet.map g)

/-- The degreewise components of the chain homotopy. -/
def prismHom (i j : ℕ) : (singCx X).X i ⟶ (singCx Y).X j :=
  if h : j = i + 1 then
    (ModuleCat.ofHom (prismOp H i) : (singCx X).X i ⟶ (singCx Y).X (i + 1))
      ≫ eqToHom (congrArg (singCx Y).X h.symm)
  else 0

theorem prismHom_succ (i : ℕ) : prismHom H i (i + 1) = ModuleCat.ofHom (prismOp H i) := by
  rw [prismHom, dif_pos rfl, eqToHom_refl, Category.comp_id]

/-- **WP2, the chain homotopy.**  The prism operator is a chain homotopy between the singular
chain maps induced by the two ends of the homotopy `H`. -/
def prismHomotopy : Homotopy (singCxMap (endMap H e0)) (singCxMap (endMap H e1)) where
  hom := prismHom H
  zero i j hij := dif_neg fun h => hij (by rw [h]; exact rfl)
  comm i := by
    have hprev : (prevD i) (prismHom H) =
        ModuleCat.ofHom (prismOp H i) ≫ (singCx Y).d (i + 1) i := by
      rw [prevD_eq (prismHom H) (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl),
        prismHom_succ]
    cases i with
    | zero =>
      have hnext : (dNext 0) (prismHom (X := X) (Y := Y) H) = 0 := by
        refine dNext_eq_zero _ _ ?_
        rw [ChainComplex.next_nat_zero]
        exact fun h => by simp at h
      rw [hnext, hprev, zero_add]
      refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
      simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
        LinearMap.comp_apply, ModuleCat.hom_ofHom, SpineTask14.sSetChainComplexFunctor_d,
        SpineTask14.sSetChainComplexFunctor_map_f]
      have hid : (sSetBoundary (TopCat.toSSet.obj Y) 0) ((prismOp H 0) c)
          = (sSetChainMap (TopCat.toSSet.map (endMap H e0)) 0) c
            + (sSetChainMap (TopCat.toSSet.map (endMap H e1)) 0) c :=
        prism_identity_zero H c
      show (sSetChainMap (TopCat.toSSet.map (endMap H e0)) 0) c
        = (sSetBoundary (TopCat.toSSet.obj Y) 0) ((prismOp H 0) c)
          + (sSetChainMap (TopCat.toSSet.map (endMap H e1)) 0) c
      rw [hid, add_assoc, mod2_add_self, add_zero]
    | succ m =>
      have hnext : (dNext (m + 1)) (prismHom (X := X) (Y := Y) H)
          = (singCx X).d (m + 1) m ≫ ModuleCat.ofHom (prismOp H m) := by
        rw [dNext_eq (prismHom H) (show (ComplexShape.down ℕ).Rel (m + 1) m from rfl),
          prismHom_succ]
      rw [hnext, hprev]
      refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
      simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
        LinearMap.comp_apply, ModuleCat.hom_ofHom, SpineTask14.sSetChainComplexFunctor_d,
        SpineTask14.sSetChainComplexFunctor_map_f]
      have hid : (sSetBoundary (TopCat.toSSet.obj Y) (m + 1)) ((prismOp H (m + 1)) c)
            + (prismOp H m) ((sSetBoundary (TopCat.toSSet.obj X) m) c)
          = (sSetChainMap (TopCat.toSSet.map (endMap H e0)) (m + 1)) c
            + (sSetChainMap (TopCat.toSSet.map (endMap H e1)) (m + 1)) c :=
        prism_identity_succ H m c
      show (sSetChainMap (TopCat.toSSet.map (endMap H e0)) (m + 1)) c
        = (prismOp H m) ((sSetBoundary (TopCat.toSSet.obj X) m) c)
            + (sSetBoundary (TopCat.toSSet.obj Y) (m + 1)) ((prismOp H (m + 1)) c)
          + (sSetChainMap (TopCat.toSSet.map (endMap H e1)) (m + 1)) c
      rw [add_comm ((prismOp H m) ((sSetBoundary (TopCat.toSSet.obj X) m) c))
          ((sSetBoundary (TopCat.toSSet.obj Y) (m + 1)) ((prismOp H (m + 1)) c)),
        hid, add_assoc, mod2_add_self, add_zero]

/-- **WP2, homotopy invariance.**  Homotopic maps induce the same map on singular homology. -/
theorem homologyMap_eq_of_prism (q : ℕ) :
    HomologicalComplex.homologyMap (singCxMap (endMap H e0)) q
      = HomologicalComplex.homologyMap (singCxMap (endMap H e1)) q :=
  (prismHomotopy H).homologyMap_eq q


end SpineTask18
