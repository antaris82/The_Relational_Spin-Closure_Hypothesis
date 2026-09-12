import RequestProject.Spine.AlgebraicTopology.SingularHomology
import RequestProject.Spine.AlgebraicTopology.Contractible

/-!
# Task 19, WP2 : degree-zero singular homology

The Task-18 contractibility theorem only covers *positive* degrees, so the standard-cell pair
in low dimensions needs an independent `H₀` calculus.  This module supplies it, for the
project's own singular chain complex `SpineTask18.singCx`:

* `SpineTask19.ptCls X x` — the class of a point, and its naturality `homologyMap_ptCls`;
* `SpineTask19.augH X` — the augmentation `H₀(X;ℤ₂) → ℤ₂`, with `augH_ptCls`;
* `SpineTask19.ptCls_eq_of_joined` — path-connected points have equal classes;
* `SpineTask19.hcls_zero_eq_augS_smul` — every `0`-class of a path-connected space is a
  multiple of a point class;
* `SpineTask19.h0Equiv` — `H₀(X;ℤ₂) ≃ ℤ₂` for a nonempty path-connected `X`.

Nothing here assumes `H₀(X) = ℤ₂` from nonemptiness: path-connectedness is used, and used
explicitly.
-/

noncomputable section

open CategoryTheory Opposite Simplicial NerveGeom SpineTask18

universe u

namespace SpineTask19

variable {X Y : TopCat.{u}}

/-! ## The singular chain complex in the language of `Task19Homology` -/

theorem singCx_d (X : TopCat.{u}) (q : ℕ) : ((singCx X).d (q + 1) q).hom = singBd X q :=
  SpineTask14.sSetChainComplexFunctor_d _ q

theorem singCxMap_f (g : X ⟶ Y) (q : ℕ) : ((singCxMap g).f q).hom = singMap g q := rfl

theorem mem_Zc_sing {q : ℕ} {z : SSetChain (TopCat.toSSet.obj X) (q + 1)} :
    z ∈ Zc (singCx X) (q + 1) ↔ singBd X q z = 0 := by
  show ((singCx X).d (q + 1) q).hom z = 0 ↔ _
  rw [singCx_d]
  exact Iff.rfl

theorem hcls_sing_eq_zero_iff {q : ℕ} (z : SSetChain (TopCat.toSSet.obj X) q)
    (hz : z ∈ Zc (singCx X) q) :
    hcls (K := singCx X) z hz = 0
      ↔ ∃ w : SSetChain (TopCat.toSSet.obj X) (q + 1), singBd X q w = z := by
  rw [hcls_eq_zero_iff]
  simp only [singCx_d]
  exact Iff.rfl

/-! ## Zero-simplices are constant -/

/-- The geometric `0`-simplex is a single point. -/
theorem Δs0_eq (x y : Δs 0) : x = y := by
  refine Subtype.ext (funext fun i => ?_)
  have hx := x.2.2
  have hy := y.2.2
  rw [Fin.sum_univ_one] at hx hy
  have hi : i = 0 := by fin_cases i; rfl
  subst hi
  rw [hx, hy]

/-- The base point of the geometric `0`-simplex. -/
def pt0 : Δs 0 := stdSimplex.vertex 0

/-- The value of a singular `0`-simplex. -/
def val0 (σ : Sing X 0) : X := sMap σ pt0

theorem sing0_eq_const (σ : Sing X 0) : σ = constSimp (val0 σ) 0 :=
  Eq.trans (sOf_sMap σ).symm (congrArg sOf (ContinuousMap.ext fun x =>
    congrArg (sMap σ) (Δs0_eq x pt0)))

@[simp] theorem val0_constSimp (x : X) : val0 (constSimp x 0) = x := by
  rw [val0, constSimp, sMap_sOf]
  rfl

/-! ## The class of a point -/

/-- The homology class of a point. -/
def ptCls (X : TopCat.{u}) (x : X) : (singCx X).homology 0 :=
  hcls (K := singCx X) (Finsupp.single (constSimp x 0) 1) (mem_Zc_zero _)

theorem singMap_constSimp (g : X ⟶ Y) (x : X) (q : ℕ) (a : ZMod 2) :
    singMap g q (Finsupp.single (constSimp x q) a)
      = Finsupp.single (constSimp ((ConcreteCategory.hom g) x) q) a := by
  show sSetChainMap (TopCat.toSSet.map g) q (Finsupp.single (constSimp x q) a) = _
  rw [sSetChainMap_single]
  refine congrArg (fun s => Finsupp.single s a) ?_
  show sOf ((ConcreteCategory.hom g).comp (sMap (constSimp x q))) = constSimp _ q
  refine congrArg sOf (ContinuousMap.ext fun t => ?_)
  show (ConcreteCategory.hom g) (sMap (constSimp x q) t) = _
  rw [constSimp, sMap_sOf]
  rfl

theorem homologyMap_ptCls (g : X ⟶ Y) (x : X) :
    (HomologicalComplex.homologyMap (singCxMap g) 0).hom (ptCls X x)
      = ptCls Y ((ConcreteCategory.hom g) x) := by
  rw [ptCls, homologyMap_hcls]
  refine hcls_congr _ _ ?_
  show singMap g 0 (Finsupp.single (constSimp x 0) 1)
    = Finsupp.single (constSimp ((ConcreteCategory.hom g) x) 0) 1
  exact singMap_constSimp g x 0 1

/-! ## The augmentation on `H₀` -/

theorem augS_singBd (X : TopCat.{u}) (w : SSetChain (TopCat.toSSet.obj X) 1) :
    augS X 0 (singBd X 0 w) = 0 := by
  induction w using lchain_induction with
  | h0 => simp
  | hadd f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | hsingle σ =>
    rw [singBd_single, map_sum]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => augS_single (X := X)
      (pre (stdC (Fin.succAbove i)) σ) 1)]
    decide

/-- **The augmentation** `H₀(X;ℤ₂) → ℤ₂`. -/
def augH (X : TopCat.{u}) : (singCx X).homology 0 →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.comp
    (Submodule.liftQ _ ((augS X 0).comp (Zc (singCx X) 0).subtype) (by
      rintro _ ⟨w, rfl⟩
      show augS X 0 (((singCx X).d 1 0).hom w) = 0
      rw [singCx_d]
      exact augS_singBd X w))
    ((hIso (singCx X) 0).hom.hom)

theorem augH_hcls (z : SSetChain (TopCat.toSSet.obj X) 0) (hz : z ∈ Zc (singCx X) 0) :
    augH X (hcls z hz) = augS X 0 z := by
  rw [augH, LinearMap.comp_apply, hIso_hom_hcls]
  rfl

@[simp] theorem augH_ptCls (x : X) : augH X (ptCls X x) = 1 := by
  rw [ptCls, augH_hcls, augS_single]

/-! ## Points joined by a path have the same class -/

theorem stdC_pt0 {n : ℕ} (f : Fin 1 → Fin (n + 1)) :
    stdC f pt0 = stdSimplex.vertex (f 0) := by
  rw [← combo_vertex f, pt0]
  exact combo_apply_vertex (fun i => stdSimplex.vertex (f i)) 0

theorem val0_pre_stdC {n : ℕ} (f : Fin 1 → Fin (n + 1)) (σ : Sing X n) :
    val0 (pre (stdC f) σ) = sMap σ (stdSimplex.vertex (f 0)) := by
  rw [val0, sMap_pre]
  exact congrArg (sMap σ) (stdC_pt0 f)

/-- The singular `1`-simplex attached to a path. -/
def pathSimp {x y : X} (γ : Path x y) : Sing X 1 :=
  sOf (γ.toContinuousMap.comp toI)

theorem singBd_pathSimp {x y : X} (γ : Path x y) :
    singBd X 0 (Finsupp.single (pathSimp γ) 1)
      = Finsupp.single (constSimp y 0) 1 + Finsupp.single (constSimp x 0) 1 := by
  rw [singBd_single, Fin.sum_univ_two]
  have hval : ∀ i : Fin 2, pre (stdC (Fin.succAbove i)) (pathSimp γ)
      = constSimp (γ (toI (stdSimplex.vertex (Fin.succAbove i 0)))) 0 := by
    intro i
    rw [sing0_eq_const (pre (stdC (Fin.succAbove i)) (pathSimp γ)),
      val0_pre_stdC (Fin.succAbove i) (pathSimp γ)]
    rfl
  rw [hval 0, hval 1]
  have h0 : Fin.succAbove (0 : Fin 2) (0 : Fin 1) = 1 := rfl
  have h1 : Fin.succAbove (1 : Fin 2) (0 : Fin 1) = 0 := rfl
  rw [h0, h1, show (stdSimplex.vertex (1 : Fin 2) : Δs 1) = e1 from rfl,
    show (stdSimplex.vertex (0 : Fin 2) : Δs 1) = e0 from rfl, toI_e0, toI_e1,
    γ.target, γ.source]

theorem ptCls_eq_of_path {x y : X} (γ : Path x y) : ptCls X x = ptCls X y := by
  have h : ptCls X y + ptCls X x = 0 := by
    rw [ptCls, ptCls, ← hcls_add]
    rw [hcls_sing_eq_zero_iff]
    exact ⟨Finsupp.single (pathSimp γ) 1, singBd_pathSimp γ⟩
  have h2 : ptCls X y = ptCls X x := by
    have h3 := congrArg (fun t => t + ptCls X x) h
    simp only [add_assoc, mod2_add_self, add_zero, zero_add] at h3
    exact h3
  exact h2.symm

theorem ptCls_eq_of_pathConnected [PathConnectedSpace ↥X] (x y : X) :
    ptCls X x = ptCls X y :=
  ptCls_eq_of_path (PathConnectedSpace.somePath x y)

/-! ## `H₀` of a nonempty path-connected space -/

theorem hcls_zero_eq_augS_smul [PathConnectedSpace ↥X] (x₀ : X)
    (z : SSetChain (TopCat.toSSet.obj X) 0) :
    hcls (K := singCx X) z (mem_Zc_zero z) = (augS X 0 z) • ptCls X x₀ := by
  induction z using lchain_induction with
  | h0 =>
    rw [map_zero, zero_smul]
    exact hcls_zero _
  | hadd f g hf hg =>
    rw [hcls_add (K := singCx X) f g (mem_Zc_zero f) (mem_Zc_zero g), hf, hg, map_add, add_smul]
  | hsingle σ =>
    rw [augS_single, one_smul, sing0_eq_const σ]
    exact ptCls_eq_of_pathConnected _ _

/-- **WP2.**  `H₀(X;ℤ₂) ≅ ℤ₂` for a nonempty path-connected space, via the augmentation. -/
def h0Equiv [PathConnectedSpace ↥X] (x₀ : X) : (singCx X).homology 0 ≃ₗ[ZMod 2] ZMod 2 where
  toFun := augH X
  map_add' := map_add _
  map_smul' := map_smul _
  invFun a := a • ptCls X x₀
  left_inv := by
    intro t
    obtain ⟨z, hz, rfl⟩ := hcls_surjective t
    rw [augH_hcls]
    exact (hcls_zero_eq_augS_smul x₀ z).symm
  right_inv := by
    intro a
    rw [map_smul, augH_ptCls, smul_eq_mul, mul_one]

theorem ptCls_ne_zero [PathConnectedSpace ↥X] (x : X) : ptCls X x ≠ 0 := by
  intro h
  have := congrArg (augH X) h
  rw [augH_ptCls, map_zero] at this
  exact one_ne_zero this

end SpineTask19
