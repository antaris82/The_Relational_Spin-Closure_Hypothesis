import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Topology.ContinuousMap.Basic
import RequestProject.Spine.AlgebraicTopology.Normalization

/-!
# Task 18, foundations : affine simplices and the codiscrete simplicial set

This module sets up the two elementary devices on which the whole Task-18 singular-homology
engine rests.  Nothing here is a new chain model: the singular chains stay the project's
`NerveGeom.SSetChain (TopCat.toSSet.obj X)`.

* `SpineTask18.Δs n` — the geometric standard `n`-simplex `stdSimplex ℝ (Fin (n+1))`, i.e.
  *exactly* the space `SimplexCategory.toTop.obj ⦋n⦌` is built from, so that singular
  `n`-simplices of `X` are continuous maps `Δs n → X` (`singEquiv`).
* `SpineTask18.combo p` — the affine singular simplex spanned by a tuple of points
  `p : Fin (m+1) → Δs n`; `combo_comp`, `combo_stdC` and `combo_vertex` are the three
  structural identities used everywhere later.
* `SpineTask18.codisc V` — the simplicial set whose `k`-simplices are the tuples
  `Fin (k+1) → V`.  Its `ℤ₂`-chains are the *linear chains* used for barycentric subdivision;
  because it is an honest simplicial set, `∂ ∘ ∂ = 0` is the project's
  `NerveGeom.sSetBoundary_comp_sSetBoundary` and needs no new combinatorics.
-/

noncomputable section

open CategoryTheory Opposite Simplicial NerveGeom

universe u v

namespace SpineTask18

/-! ## The geometric standard simplex -/

/-- The geometric standard `n`-simplex: the subspace of `Fin (n+1) → ℝ` cut out by
`0 ≤ xᵢ`, `∑ xᵢ = 1`.  This is the underlying space of `SimplexCategory.toTop.obj ⦋n⦌`. -/
abbrev Δs (n : ℕ) : Type := stdSimplex ℝ (Fin (n + 1))

/-- The continuous map `Δs m → Δs n` induced by a reindexing `f : Fin (m+1) → Fin (n+1)`. -/
def stdC {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) : C(Δs m, Δs n) :=
  ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩

@[simp] theorem stdC_apply {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (x : Δs m) :
    stdC f x = stdSimplex.map f x := rfl

theorem stdSimplex_map_apply {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (x : Δs m) (j : Fin (n + 1)) :
    (stdSimplex.map f x : Fin (n + 1) → ℝ) j = ∑ i ∈ Finset.univ.filter (fun i => f i = j), x i :=
  FunOnFinite.linearMap_apply_apply ℝ ℝ f _ j

/-! ## Affine simplices -/

theorem combo_mem {m n : ℕ} (p : Fin (m + 1) → Δs n) (x : Δs m) :
    (fun j => ∑ i, (x : Fin (m+1) → ℝ) i * (p i : Fin (n+1) → ℝ) j) ∈ stdSimplex ℝ (Fin (n + 1)) := by
  constructor
  · intro j
    exact Finset.sum_nonneg fun i _ => mul_nonneg (x.2.1 i) ((p i).2.1 j)
  · rw [Finset.sum_comm]
    have : ∀ i : Fin (m+1), ∑ j, (x : Fin (m+1) → ℝ) i * (p i : Fin (n+1) → ℝ) j
        = (x : Fin (m+1) → ℝ) i := by
      intro i
      rw [← Finset.mul_sum, show ∑ j, (p i : Fin (n+1) → ℝ) j = 1 from (p i).2.2, mul_one]
    calc ∑ i, ∑ j, (x : Fin (m+1) → ℝ) i * (p i : Fin (n+1) → ℝ) j
        = ∑ i, (x : Fin (m+1) → ℝ) i := Finset.sum_congr rfl fun i _ => this i
      _ = 1 := x.2.2

/-- The affine singular simplex spanned by the tuple of points `p`. -/
def combo {m n : ℕ} (p : Fin (m + 1) → Δs n) : C(Δs m, Δs n) where
  toFun x := ⟨_, combo_mem p x⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun j => ?_) _
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

@[simp] theorem combo_coe {m n : ℕ} (p : Fin (m + 1) → Δs n) (x : Δs m) (j : Fin (n + 1)) :
    ((combo p x : Δs n) : Fin (n+1) → ℝ) j
      = ∑ i, (x : Fin (m+1) → ℝ) i * (p i : Fin (n+1) → ℝ) j := rfl

/-- An affine simplex spanned by vertices is a reindexing map. -/
theorem combo_vertex {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    combo (fun i => stdSimplex.vertex (f i)) = stdC f := by
  ext x j
  rw [combo_coe, stdC_apply, stdSimplex_map_apply]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : f i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- `combo` of the tautological vertex tuple is the identity. -/
theorem combo_id (n : ℕ) : combo (fun i : Fin (n+1) => stdSimplex.vertex i) = ContinuousMap.id _ := by
  rw [combo_vertex]
  ext x j
  show (stdSimplex.map (fun i : Fin (n+1) => i) x : Fin (n+1) → ℝ) j = _
  rw [show (fun i : Fin (n+1) => i) = id from rfl, stdSimplex.map_id_apply]
  rfl

/-- Composition of affine simplices. -/
theorem combo_comp {l m n : ℕ} (q : Fin (m + 1) → Δs n) (p : Fin (l + 1) → Δs m) :
    (combo q).comp (combo p) = combo (fun i => combo q (p i)) := by
  ext x k
  simp only [ContinuousMap.comp_apply, combo_coe]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
    show (∑ i, (x : Fin (l+1) → ℝ) i * (p i : Fin (m+1) → ℝ) j) * (q j : Fin (n+1) → ℝ) k
      = ∑ i, (x : Fin (l+1) → ℝ) i * ((p i : Fin (m+1) → ℝ) j * (q j : Fin (n+1) → ℝ) k) from by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring), Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]

@[simp] theorem combo_apply_vertex {m n : ℕ} (q : Fin (m + 1) → Δs n) (i : Fin (m + 1)) :
    combo q (stdSimplex.vertex i) = q i := by
  ext j
  rw [combo_coe]
  simp [Pi.single_apply, Finset.sum_ite_eq']

/-- Reindexing an affine simplex. -/
theorem combo_stdC {l m n : ℕ} (p : Fin (m + 1) → Δs n) (f : Fin (l + 1) → Fin (m + 1)) :
    (combo p).comp (stdC f) = combo (p ∘ f) := by
  rw [← combo_vertex, combo_comp]
  simp [Function.comp_def]


/-! ## Singular simplices of a space, in the project's model -/

/-- A singular `n`-simplex of `X`, i.e. an element of the project's `n`-chains generator set. -/
abbrev Sing (X : TopCat.{u}) (n : ℕ) : Type u :=
  (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))

variable {X Y : TopCat.{u}}

/-- A singular simplex, viewed as a continuous map out of the geometric simplex. -/
def sMap {n : ℕ} (s : Sing X n) : C(Δs n, X) := TopCat.toSSetObjEquiv X _ s

/-- A continuous map out of the geometric simplex, viewed as a singular simplex. -/
def sOf {n : ℕ} (f : C(Δs n, X)) : Sing X n := (TopCat.toSSetObjEquiv X _).symm f

@[simp] theorem sMap_sOf {n : ℕ} (f : C(Δs n, X)) : sMap (sOf f) = f :=
  (TopCat.toSSetObjEquiv X _).apply_symm_apply f

@[simp] theorem sOf_sMap {n : ℕ} (s : Sing X n) : sOf (sMap s) = s :=
  (TopCat.toSSetObjEquiv X _).symm_apply_apply s

theorem sOf_injective {n : ℕ} : Function.Injective (sOf (X := X) (n := n)) :=
  (TopCat.toSSetObjEquiv X _).symm.injective

/-- Precomposition of a singular simplex with a continuous map of geometric simplices. -/
def pre {m n : ℕ} (φ : C(Δs m, Δs n)) (s : Sing X n) : Sing X m := sOf ((sMap s).comp φ)

@[simp] theorem sMap_pre {m n : ℕ} (φ : C(Δs m, Δs n)) (s : Sing X n) :
    sMap (pre φ s) = (sMap s).comp φ := by simp [pre]

theorem pre_pre {l m n : ℕ} (φ : C(Δs l, Δs m)) (ψ : C(Δs m, Δs n)) (s : Sing X n) :
    pre φ (pre ψ s) = pre (ψ.comp φ) s := by
  simp [pre, ContinuousMap.comp_assoc]

@[simp] theorem pre_id {n : ℕ} (s : Sing X n) : pre (ContinuousMap.id _) s = s := by
  simp [pre]

/-- The `i`-th face of a singular simplex is precomposition with the `i`-th coface map. -/
theorem sing_delta {n : ℕ} (i : Fin (n + 2)) (s : Sing X (n + 1)) :
    (TopCat.toSSet.obj X).δ i s = pre (stdC (Fin.succAbove i)) s := rfl

/-- Postcomposition with a continuous map, i.e. the action of `TopCat.toSSet` on morphisms. -/
theorem toSSet_map_app {n : ℕ} (g : X ⟶ Y) (s : Sing X n) :
    (TopCat.toSSet.map g).app _ s = sOf ((ConcreteCategory.hom g).comp (sMap s)) := rfl

/-! ## The codiscrete simplicial set : linear chains -/

/-- The simplicial set whose `k`-simplices are the `(k+1)`-tuples of points of `V`, with the
obvious reindexing action.  Its `ℤ₂`-chains are the *linear chains* on `V`. -/
def codisc (V : Type v) : SSet.{v} where
  obj n := Fin (n.unop.len + 1) → V
  map f g := g ∘ f.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem codisc_obj (V : Type v) (k : ℕ) :
    (codisc V).obj (op (SimplexCategory.mk k)) = (Fin (k + 1) → V) := rfl

theorem codisc_delta {V : Type v} {k : ℕ} (i : Fin (k + 2)) (p : Fin (k + 2) → V) :
    (codisc V).δ i p = p ∘ Fin.succAbove i := rfl

/-- Linear chains on `V`: the free `ℤ₂`-module on `(k+1)`-tuples of points of `V`.  This is,
definitionally, the project's `SSetChain` of the codiscrete simplicial set. -/
abbrev LChain (V : Type v) (k : ℕ) : Type v := (Fin (k + 1) → V) →₀ ZMod 2

/-- The boundary of linear chains. -/
def lbd (V : Type v) (k : ℕ) : LChain V (k + 1) →ₗ[ZMod 2] LChain V k :=
  ∑ i : Fin (k + 2), Finsupp.lmapDomain _ _ (fun p : Fin (k + 2) → V => p ∘ Fin.succAbove i)

theorem lbd_eq_sSetBoundary (V : Type v) (k : ℕ) : lbd V k = sSetBoundary (codisc V) k := rfl

@[simp] theorem lbd_single {V : Type v} {k : ℕ} (p : Fin (k + 2) → V) (c : ZMod 2) :
    lbd V k (Finsupp.single p c) = ∑ i : Fin (k + 2), Finsupp.single (p ∘ Fin.succAbove i) c := by
  simp [lbd, LinearMap.sum_apply, Finsupp.mapDomain_single]

theorem lbd_lbd {V : Type v} {k : ℕ} (c : LChain V (k + 2)) : lbd V k (lbd V (k + 1) c) = 0 :=
  congrFun (congrArg DFunLike.coe (SpineTask13.sSetBoundary_comp_sSetBoundary (codisc V) k)) c

/-- Functoriality of linear chains in the vertex set. -/
def lmap {V : Type v} {W : Type*} (h : V → W) (k : ℕ) : LChain V k →ₗ[ZMod 2] LChain W k :=
  Finsupp.lmapDomain _ _ (fun p => h ∘ p)

@[simp] theorem lmap_single {V : Type v} {W : Type*} (h : V → W) {k : ℕ}
    (p : Fin (k + 1) → V) (c : ZMod 2) :
    lmap h k (Finsupp.single p c) = Finsupp.single (h ∘ p) c :=
  Finsupp.mapDomain_single

theorem lmap_lbd {V : Type v} {W : Type*} (h : V → W) (k : ℕ) :
    (lmap h k).comp (lbd V k) = (lbd W k).comp (lmap h (k + 1)) := by
  refine Finsupp.lhom_ext' fun p => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, lmap_single, lbd_single, map_sum,
    lmap_single]
  exact Finset.sum_congr rfl fun i _ => rfl

/-! ## Realizing linear chains as singular chains -/

/-- The singular boundary in the project's model. -/
abbrev singBd (X : TopCat.{u}) (k : ℕ) :
    SSetChain (TopCat.toSSet.obj X) (k + 1) →ₗ[ZMod 2] SSetChain (TopCat.toSSet.obj X) k :=
  sSetBoundary (TopCat.toSSet.obj X) k

theorem singBd_single {k : ℕ} (s : Sing X (k + 1)) (c : ZMod 2) :
    singBd X k (Finsupp.single s c)
      = ∑ i : Fin (k + 2), Finsupp.single (pre (stdC (Fin.succAbove i)) s) c := by
  rw [show singBd X k = sSetBoundary (TopCat.toSSet.obj X) k from rfl, sSetBoundary_single]
  rfl

/-- The realization of a linear chain of the standard `n`-simplex along a singular
`n`-simplex `σ` : the affine simplex spanned by `p` is postcomposed with `σ`. -/
def realizeChain {n : ℕ} (σ : Sing X n) (k : ℕ) :
    LChain (Δs n) k →ₗ[ZMod 2] SSetChain (TopCat.toSSet.obj X) k :=
  Finsupp.lmapDomain _ _ (fun p => pre (combo p) σ)

@[simp] theorem realizeChain_single {n k : ℕ} (σ : Sing X n) (p : Fin (k + 1) → Δs n)
    (c : ZMod 2) : realizeChain σ k (Finsupp.single p c)
      = Finsupp.single (pre (combo p) σ) c :=
  Finsupp.mapDomain_single

/-- Realization is a chain map. -/
theorem realizeChain_lbd {n : ℕ} (σ : Sing X n) (k : ℕ) :
    (realizeChain σ k).comp (lbd (Δs n) k) = (singBd X k).comp (realizeChain σ (k + 1)) := by
  refine Finsupp.lhom_ext' fun p => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, realizeChain_single, lbd_single,
    map_sum, realizeChain_single, singBd_single]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pre_pre, combo_stdC]

/-- Realization is natural for affine reparametrisations. -/
theorem realizeChain_lmap {m n : ℕ} (σ : Sing X n) (q : Fin (m + 1) → Δs n) (k : ℕ) :
    (realizeChain σ k).comp (lmap (combo q) k) = realizeChain (pre (combo q) σ) k := by
  refine Finsupp.lhom_ext' fun p => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, lmap_single, realizeChain_single]
  rw [pre_pre, combo_comp]
  rfl

/-- The tautological linear `n`-simplex of the standard `n`-simplex. -/
def taut (n : ℕ) : Fin (n + 1) → Δs n := fun i => stdSimplex.vertex i

theorem combo_taut (n : ℕ) : combo (taut n) = ContinuousMap.id _ := combo_id n

@[simp] theorem realizeChain_taut {n : ℕ} (σ : Sing X n) (c : ZMod 2) :
    realizeChain σ n (Finsupp.single (taut n) c) = Finsupp.single σ c := by
  rw [realizeChain_single, combo_taut, pre_id]

@[simp] theorem lmap_combo_taut {m n : ℕ} (q : Fin (m + 1) → Δs n) (c : ZMod 2) :
    lmap (combo q) m (Finsupp.single (taut m) c) = Finsupp.single q c := by
  rw [lmap_single]
  exact congrArg (fun z => Finsupp.single z c) (funext fun i => combo_apply_vertex q i)

end SpineTask18
