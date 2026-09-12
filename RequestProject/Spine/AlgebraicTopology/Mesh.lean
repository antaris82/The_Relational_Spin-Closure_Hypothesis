import Mathlib.Analysis.Normed.Module.Convex
import RequestProject.Spine.AlgebraicTopology.LinearSubdivision

/-!
# Task 18, WP7 (geometry) : the barycentric mesh estimate

The classical estimate: every simplex occurring in the barycentric subdivision of a linear
`k`-simplex of `Δs n` has all its vertices in the original simplex, and all its edges are at
most `k/(k+1)` times as long as the longest edge of the original.

Iterating gives `SpineTask18.mesh_sdIter`, from which the eventual smallness of `sd^N σ`
follows in `Task18SmallSimplices`.

Distances are the sup-metric distances of `Fin (n+1) → ℝ`, restricted to the standard simplex.
-/

noncomputable section

open CategoryTheory Opposite Simplicial NerveGeom

universe u v

namespace SpineTask18

/-! ## Elementary metric facts about the standard simplex -/

theorem dist_coe {n : ℕ} (x y : Δs n) :
    dist x y = dist (x : Fin (n + 1) → ℝ) (y : Fin (n + 1) → ℝ) := rfl

/-- The mesh bound: all edges of the tuple `p` are at most `r`. -/
def MeshLE {n k : ℕ} (p : Fin (k + 1) → Δs n) (r : ℝ) : Prop := ∀ i j, dist (p i) (p j) ≤ r

theorem MeshLE.nonneg {n k : ℕ} {p : Fin (k + 1) → Δs n} {r : ℝ} (h : MeshLE p r) : 0 ≤ r :=
  le_trans dist_nonneg (h 0 0)

theorem MeshLE.mono {n k : ℕ} {p : Fin (k + 1) → Δs n} {r s : ℝ} (h : MeshLE p r) (hrs : r ≤ s) :
    MeshLE p s := fun i j => (h i j).trans hrs

theorem MeshLE.comp {n k l : ℕ} {p : Fin (k + 1) → Δs n} {r : ℝ} (h : MeshLE p r)
    (f : Fin (l + 1) → Fin (k + 1)) : MeshLE (p ∘ f) r := fun i j => h (f i) (f j)

/-! ## Convex hull facts -/

/-- A point of an affine simplex lies in the convex hull of its vertices. -/
theorem combo_mem_convexHull {n m : ℕ} (p : Fin (m + 1) → Δs n) (x : Δs m) :
    ((combo p x : Δs n) : Fin (n + 1) → ℝ)
      ∈ convexHull ℝ (Set.range (fun i => ((p i : Δs n) : Fin (n + 1) → ℝ))) := by
  have hval : ((combo p x : Δs n) : Fin (n + 1) → ℝ)
      = ∑ i, (x : Fin (m + 1) → ℝ) i • ((p i : Δs n) : Fin (n + 1) → ℝ) := by
    funext j
    rw [combo_coe]
    simp [Finset.sum_apply]
  rw [hval]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => x.2.1 i) x.2.2
    (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)

/-- If all vertices are within `R` of `b`, so is the whole convex hull. -/
theorem dist_le_of_mem_convexHull {n m : ℕ} (b : Fin (n + 1) → ℝ)
    (p : Fin (m + 1) → Δs n) {R : ℝ}
    (hR : ∀ i, dist b ((p i : Δs n) : Fin (n + 1) → ℝ) ≤ R)
    {z : Fin (n + 1) → ℝ}
    (hz : z ∈ convexHull ℝ (Set.range (fun i => ((p i : Δs n) : Fin (n + 1) → ℝ)))) :
    dist b z ≤ R := by
  have hsub : Set.range (fun i => ((p i : Δs n) : Fin (n + 1) → ℝ)) ⊆ Metric.closedBall b R := by
    rintro _ ⟨i, rfl⟩
    exact (Metric.mem_closedBall').2 (hR i)
  have := convexHull_min hsub (convex_closedBall b R) hz
  exact (Metric.mem_closedBall').1 this

theorem convexHull_range_comp_subset {n m l : ℕ} (p : Fin (m + 1) → Δs n)
    (f : Fin (l + 1) → Fin (m + 1)) :
    convexHull ℝ (Set.range (fun i => (((p ∘ f) i : Δs n) : Fin (n + 1) → ℝ)))
      ⊆ convexHull ℝ (Set.range (fun i => ((p i : Δs n) : Fin (n + 1) → ℝ))) := by
  refine convexHull_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨f i, rfl⟩

/-! ## The barycentre estimate -/

/-- **The barycentre estimate.**  The barycentre of a `k`-simplex is within `k/(k+1)` of the
mesh from each of its vertices. -/
theorem dist_bary_le {n k : ℕ} (p : Fin (k + 1) → Δs n) {r : ℝ} (h : MeshLE p r) (j : Fin (k + 1)) :
    dist ((bary p : Δs n) : Fin (n + 1) → ℝ) ((p j : Δs n) : Fin (n + 1) → ℝ)
      ≤ (k / (k + 1) : ℝ) * r := by
  have hr := h.nonneg
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hfac : (0 : ℝ) ≤ (k / (k + 1) : ℝ) * r := by positivity
  refine (dist_pi_le_iff hfac).2 fun l => ?_
  have hbary : ((bary p : Δs n) : Fin (n + 1) → ℝ) l
      = ∑ i, ((k : ℝ) + 1)⁻¹ * ((p i : Δs n) : Fin (n + 1) → ℝ) l := by
    rw [bary, combo_coe]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    show ((Fintype.card (Fin (k + 1)) : ℝ))⁻¹ = _
    simp
  have hpj : ((p j : Δs n) : Fin (n + 1) → ℝ) l
      = ∑ _i : Fin (k + 1), ((k : ℝ) + 1)⁻¹ * ((p j : Δs n) : Fin (n + 1) → ℝ) l := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  rw [Real.dist_eq, hbary]
  rw [hpj]
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ i : Fin (k + 1),
      |((k : ℝ) + 1)⁻¹ * ((p i : Δs n) : Fin (n + 1) → ℝ) l
        - ((k : ℝ) + 1)⁻¹ * ((p j : Δs n) : Fin (n + 1) → ℝ) l|
      ≤ ((k : ℝ) + 1)⁻¹ * (if i = j then 0 else r) := by
    intro i
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((k : ℝ) + 1)⁻¹)]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc |((p i : Δs n) : Fin (n + 1) → ℝ) l - ((p j : Δs n) : Fin (n + 1) → ℝ) l|
          = dist (((p i : Δs n) : Fin (n + 1) → ℝ) l) (((p j : Δs n) : Fin (n + 1) → ℝ) l) :=
            (Real.dist_eq _ _).symm
        _ ≤ dist ((p i : Δs n) : Fin (n + 1) → ℝ) ((p j : Δs n) : Fin (n + 1) → ℝ) :=
            dist_le_pi_dist _ _ l
        _ ≤ r := h i j
  refine le_trans (Finset.sum_le_sum fun i _ => hterm i) ?_
  rw [← Finset.mul_sum]
  have hsum : ∑ i : Fin (k + 1), (if i = j then (0:ℝ) else r) = (k : ℝ) * r := by
    have hrw : ∀ i : Fin (k + 1),
        (if i = j then (0:ℝ) else r) = r - (if i = j then r else 0) := by
      intro i
      by_cases hij : i = j <;> simp [hij]
    simp only [hrw]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_ite_eq' Finset.univ j (fun _ => r), if_pos (Finset.mem_univ j), nsmul_eq_mul]
    push_cast
    ring
  rw [hsum]
  have hfin : ((k : ℝ) + 1)⁻¹ * ((k : ℝ) * r) = ((k : ℝ) / ((k : ℝ) + 1)) * r := by
    field_simp
  rw [hfin]

/-! ## The mesh estimate for one subdivision -/

theorem div_succ_mono (k : ℕ) : ((k : ℝ) / (k + 1)) ≤ ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
  have h1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have h2 : (0:ℝ) < (k:ℝ) + 2 := by positivity
  rw [← sub_nonneg]
  have hid : ((k : ℝ) + 1) / ((k : ℝ) + 2) - (k : ℝ) / ((k : ℝ) + 1)
      = 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    field_simp
    ring
  rw [hid]
  positivity

/-- **The barycentric mesh estimate.**  Every simplex of the barycentric subdivision of a linear
`k`-simplex has its vertices in the original simplex and all its edges of length at most
`k/(k+1)` times the mesh of the original. -/
theorem sd_support_mesh (n : ℕ) : ∀ (k : ℕ) (p : Fin (k + 1) → Δs n) (r : ℝ), MeshLE p r →
    ∀ q ∈ (sd n k (Finsupp.single p 1)).support,
      (∀ i, ((q i : Δs n) : Fin (n + 1) → ℝ)
          ∈ convexHull ℝ (Set.range (fun i => ((p i : Δs n) : Fin (n + 1) → ℝ))))
        ∧ MeshLE q (((k : ℝ) / (k + 1)) * r)
  | 0, p, r, h, q, hq => by
    have hqp : q = p := by
      have := Finsupp.support_single_subset hq
      exact Finset.mem_singleton.1 this
    subst hqp
    refine ⟨fun i => subset_convexHull ℝ _ ⟨i, rfl⟩, fun i j => ?_⟩
    have hij : i = j := Fin.ext (by omega)
    subst hij
    simp
  | k + 1, p, r, h, q, hq => by
    classical
    have hr := h.nonneg
    -- decompose the support
    rw [sd_single, lbd_single, map_sum, map_sum] at hq
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hq)
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hi)
    have hIH := sd_support_mesh n k (p ∘ Fin.succAbove i) r (h.comp _) q' hq'
    have hhull : ∀ l, ((q' l : Δs n) : Fin (n + 1) → ℝ)
        ∈ convexHull ℝ (Set.range (fun i => ((p i : Δs n) : Fin (n + 1) → ℝ))) := fun l =>
      convexHull_range_comp_subset p (Fin.succAbove i) (hIH.1 l)
    have hbaryhull : ((bary p : Δs n) : Fin (n + 1) → ℝ)
        ∈ convexHull ℝ (Set.range (fun i => ((p i : Δs n) : Fin (n + 1) → ℝ))) :=
      combo_mem_convexHull p _
    have hfac : (0 : ℝ) ≤ ((k : ℝ) + 1) / ((k : ℝ) + 1 + 1) * r := by positivity
    have hb : ∀ z ∈ convexHull ℝ (Set.range (fun i => ((p i : Δs n) : Fin (n + 1) → ℝ))),
        dist ((bary p : Δs n) : Fin (n + 1) → ℝ) z
          ≤ (((k : ℝ) + 1) / ((k : ℝ) + 1 + 1)) * r := by
      intro z hz
      refine dist_le_of_mem_convexHull _ p (fun j => ?_) hz
      have := dist_bary_le p h j
      simpa using this
    refine ⟨fun l => ?_, fun a b => ?_⟩
    · induction l using Fin.cases with
      | zero => simpa using hbaryhull
      | succ l => simpa using hhull l
    · push_cast
      have hmono : ((k : ℝ) / (k + 1)) * r ≤ (((k : ℝ) + 1) / ((k : ℝ) + 1 + 1)) * r := by
        have h2 : ((k : ℝ) + 1) / ((k : ℝ) + 1 + 1) = ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
          ring
        rw [h2]
        exact mul_le_mul_of_nonneg_right (div_succ_mono k) hr
      induction a using Fin.cases with
      | zero =>
        induction b using Fin.cases with
        | zero => simpa using hfac
        | succ b =>
          rw [Fin.cons_zero, Fin.cons_succ]
          exact hb _ (hhull b)
      | succ a =>
        induction b using Fin.cases with
        | zero =>
          rw [Fin.cons_zero, Fin.cons_succ, dist_comm]
          exact hb _ (hhull a)
        | succ b =>
          rw [Fin.cons_succ, Fin.cons_succ]
          exact (hIH.2 a b).trans hmono

/-! ## Mesh of a chain, and iterated subdivision -/

/-- Every simplex of the chain `c` has mesh at most `r`. -/
def ChainMeshLE {n k : ℕ} (c : LChain (Δs n) k) (r : ℝ) : Prop := ∀ p ∈ c.support, MeshLE p r

theorem chainMesh_sd {n k : ℕ} {c : LChain (Δs n) k} {r : ℝ} (h : ChainMeshLE c r) :
    ChainMeshLE (sd n k c) (((k : ℝ) / (k + 1)) * r) := by
  classical
  intro q hq
  have hc : c = ∑ p ∈ c.support, Finsupp.single p (c p) := (Finsupp.sum_single c).symm
  rw [hc, map_sum] at hq
  obtain ⟨p, hp, hqp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hq)
  have hsm : Finsupp.single p (c p) = (c p) • Finsupp.single p (1 : ZMod 2) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hsm, map_smul] at hqp
  exact (sd_support_mesh n k p r (h p hp) q (Finsupp.support_smul hqp)).2

/-- Iterated barycentric subdivision of linear chains. -/
def sdIter (n k : ℕ) : ℕ → (LChain (Δs n) k →ₗ[ZMod 2] LChain (Δs n) k)
  | 0 => LinearMap.id
  | N + 1 => (sd n k).comp (sdIter n k N)

@[simp] theorem sdIter_zero (n k : ℕ) (c : LChain (Δs n) k) : sdIter n k 0 c = c := rfl

theorem sdIter_succ (n k N : ℕ) (c : LChain (Δs n) k) :
    sdIter n k (N + 1) c = sd n k (sdIter n k N c) := rfl

theorem chainMesh_sdIter {n k : ℕ} {c : LChain (Δs n) k} {r : ℝ} (h : ChainMeshLE c r) :
    ∀ N, ChainMeshLE (sdIter n k N c) ((((k : ℝ) / (k + 1)) ^ N) * r)
  | 0 => by simpa using h
  | N + 1 => by
    have := chainMesh_sd (chainMesh_sdIter h N)
    intro q hq
    have h2 := this q hq
    refine h2.mono (le_of_eq ?_)
    ring

/-! ## The initial mesh, and shrinking to zero -/

/-- Any tuple of points of the standard simplex has mesh at most `1`. -/
theorem meshLE_one {n k : ℕ} (p : Fin (k + 1) → Δs n) : MeshLE p 1 := by
  intro i j
  rw [dist_coe]
  exact le_trans
    (Metric.dist_le_diam_of_mem (bounded_stdSimplex (Fin (n + 1))) (p i).2 (p j).2)
    diam_stdSimplex_le

theorem exists_pow_mesh_lt (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, (((n : ℝ) / (n + 1)) ^ N) * 1 < ε := by
  have h0 : (0 : ℝ) ≤ (n : ℝ) / (n + 1) := by positivity
  have h1 : ((n : ℝ) / (n + 1)) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε h1
  exact ⟨N, by simpa using hN⟩

/-! ## Affine simplices spanned by a small tuple are small -/

/-- If the tuple `p` has mesh at most `r`, the affine simplex it spans has diameter at
most `r`. -/
theorem dist_combo_le {n m : ℕ} (p : Fin (m + 1) → Δs n) {r : ℝ} (h : MeshLE p r) (x y : Δs m) :
    dist (combo p x) (combo p y) ≤ r := by
  have hstep : ∀ z : Δs m, ∀ i, dist ((p i : Δs n) : Fin (n + 1) → ℝ)
      ((combo p z : Δs n) : Fin (n + 1) → ℝ) ≤ r := by
    intro z i
    exact dist_le_of_mem_convexHull _ p (fun j => h i j) (combo_mem_convexHull p z)
  exact dist_le_of_mem_convexHull _ p
    (fun i => by rw [dist_comm]; exact hstep x i) (combo_mem_convexHull p y)

end SpineTask18
