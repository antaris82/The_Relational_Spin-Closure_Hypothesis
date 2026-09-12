import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import RequestProject.Spine.Nerve.Geometry.StandardSimplex

/-!
# Task 20, geometry : an explicit retraction of the punctured barycentric boundary

Fix `n : ℕ` and work in the geometric standard simplex `Σ = stdSimplex ℝ (Fin (n+3))`, whose
boundary locus is `SpineTask17.bdLocus (n+2) = {x | ∃ i, x i = 0}`.  Two distinguished points
are removed from the boundary locus:

* `SpineTask20.vtx0 n` — the `0`-th vertex `e₀`, which lies on every face except the `0`-th;
* `SpineTask20.barPt n` — the barycentre of the `0`-th face, which lies on the `0`-th face
  only.

The remaining set `Wc n` retracts onto the *boundary of the `0`-th face*: project away from
`e₀` onto the `0`-th face (this is possible because `x₀ ≠ 1`), and then push the resulting
point of the `0`-th face radially away from its barycentre until it hits the boundary of that
face (this is possible because the projected point is not the barycentre).  The composite
`coordRetr` is continuous and fixes the boundary of the `0`-th face pointwise; that is all the
Task-20 argument needs — no homotopies are required.
-/

noncomputable section

open Finset

namespace SpineTask20

variable (n : ℕ)

/-! ## The two removed points -/

/-- The barycentre of the `0`-th face of the geometric `(n+2)`-simplex. -/
def barPt : stdSimplex ℝ (Fin (n + 3)) :=
  ⟨fun i => if i = 0 then 0 else (1 : ℝ) / (n + 2), by
    constructor
    · intro i
      by_cases h : i = 0
      · simp [h]
      · simp only [if_neg h]
        positivity
    · rw [Fin.sum_univ_succ]
      have h1 : ∀ i : Fin (n + 2), (if Fin.succ i = 0 then (0:ℝ) else (1:ℝ)/(n+2))
          = (1:ℝ)/(n+2) := fun i => if_neg (Fin.succ_ne_zero i)
      rw [Finset.sum_congr rfl (fun i _ => h1 i), if_pos rfl, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, zero_add]
      push_cast
      field_simp⟩

/-- The `0`-th vertex of the geometric `(n+2)`-simplex. -/
def vtx0 : stdSimplex ℝ (Fin (n + 3)) := stdSimplex.vertex 0

@[simp] theorem barPt_apply_zero : (barPt n : Fin (n + 3) → ℝ) 0 = 0 := rfl

@[simp] theorem barPt_apply_succ (k : Fin (n + 2)) :
    (barPt n : Fin (n + 3) → ℝ) k.succ = (1 : ℝ) / (n + 2) := by
  show (if Fin.succ k = 0 then (0:ℝ) else (1:ℝ)/(n+2)) = _
  exact if_neg (Fin.succ_ne_zero k)

@[simp] theorem vtx0_apply_zero : (vtx0 n : Fin (n + 3) → ℝ) 0 = 1 := by
  simp [vtx0, stdSimplex.vertex]

@[simp] theorem vtx0_apply_succ (k : Fin (n + 2)) :
    (vtx0 n : Fin (n + 3) → ℝ) k.succ = 0 := by
  simp [vtx0, stdSimplex.vertex, (Fin.succ_ne_zero k)]

theorem barPt_mem_bdLocus : barPt n ∈ SpineTask17.bdLocus (n + 2) := ⟨0, barPt_apply_zero n⟩

theorem vtx0_mem_bdLocus : vtx0 n ∈ SpineTask17.bdLocus (n + 2) :=
  ⟨1, by simpa using vtx0_apply_succ n 0⟩

theorem barPt_ne_vtx0 : barPt n ≠ vtx0 n := by
  intro h
  have := congrArg (fun x : stdSimplex ℝ (Fin (n + 3)) => (x : Fin (n + 3) → ℝ) 0) h
  simp at this

variable {n}

/-- Extensionality for points of a geometric standard simplex, in coordinate form. -/
theorem stdSimplex_ext {m : ℕ} {x y : stdSimplex ℝ (Fin m)}
    (h : ∀ j, (x : Fin m → ℝ) j = (y : Fin m → ℝ) j) : x = y := Subtype.ext (funext h)

/-- The coordinates other than the `0`-th one sum to `1 - x₀`. -/
theorem sum_succ_coords (x : stdSimplex ℝ (Fin (n + 3))) :
    ∑ k : Fin (n + 2), (x : Fin (n + 3) → ℝ) k.succ = 1 - (x : Fin (n + 3) → ℝ) 0 := by
  have hsum := stdSimplex.sum_eq_one x
  rw [Fin.sum_univ_succ] at hsum
  linarith

/-- A point of the standard simplex whose `0`-th coordinate is `1` is the `0`-th vertex. -/
theorem eq_vtx0_of_apply_zero_eq_one {x : stdSimplex ℝ (Fin (n + 3))}
    (h : (x : Fin (n + 3) → ℝ) 0 = 1) : x = vtx0 n := by
  have hz : ∑ k : Fin (n + 2), (x : Fin (n + 3) → ℝ) k.succ = 0 := by
    rw [sum_succ_coords x, h, sub_self]
  have hall : ∀ k : Fin (n + 2), (x : Fin (n + 3) → ℝ) k.succ = 0 := fun k =>
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => stdSimplex.zero_le x i.succ)).1 hz k (Finset.mem_univ k)
  refine stdSimplex_ext fun j => ?_
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
  · rw [h, vtx0_apply_zero]
  · rw [hall k, vtx0_apply_succ]

/-! ## The punctured boundary locus and its retraction -/

/-- The boundary locus of the geometric `(n+2)`-simplex, punctured at the `0`-th vertex and at
the barycentre of the `0`-th face. -/
def Wc (n : ℕ) : Set (stdSimplex ℝ (Fin (n + 3))) :=
  {x | (∃ i, (x : Fin (n + 3) → ℝ) i = 0) ∧ x ≠ barPt n ∧ x ≠ vtx0 n}

theorem one_sub_apply_zero_pos {x : stdSimplex ℝ (Fin (n + 3))} (hx : x ∈ Wc n) :
    0 < 1 - (x : Fin (n + 3) → ℝ) 0 := by
  have hne : (x : Fin (n + 3) → ℝ) 0 ≠ 1 := fun h => hx.2.2 (eq_vtx0_of_apply_zero_eq_one h)
  have hle : (x : Fin (n + 3) → ℝ) 0 ≤ 1 := by
    have h1 := sum_succ_coords x
    have h2 : (0:ℝ) ≤ ∑ k : Fin (n + 2), (x : Fin (n + 3) → ℝ) k.succ :=
      Finset.sum_nonneg fun k _ => stdSimplex.zero_le x k.succ
    linarith
  exact sub_pos.2 (lt_of_le_of_ne hle hne)

/-- The projection away from the `0`-th vertex onto the `0`-th face, in coordinates. -/
def piFun (x : stdSimplex ℝ (Fin (n + 3))) (k : Fin (n + 2)) : ℝ :=
  (x : Fin (n + 3) → ℝ) k.succ / (1 - (x : Fin (n + 3) → ℝ) 0)

theorem piFun_nonneg {x : stdSimplex ℝ (Fin (n + 3))} (hx : x ∈ Wc n) (k : Fin (n + 2)) :
    0 ≤ piFun x k :=
  div_nonneg (stdSimplex.zero_le x k.succ) (le_of_lt (one_sub_apply_zero_pos hx))

theorem piFun_sum {x : stdSimplex ℝ (Fin (n + 3))} (hx : x ∈ Wc n) :
    ∑ k : Fin (n + 2), piFun x k = 1 := by
  rw [show ∑ k : Fin (n + 2), piFun x k
      = (∑ k : Fin (n + 2), (x : Fin (n + 3) → ℝ) k.succ) / (1 - (x : Fin (n + 3) → ℝ) 0) from
    (Finset.sum_div _ _ _).symm, sum_succ_coords x]
  exact div_self (one_sub_apply_zero_pos hx).ne'

/-- The smallest coordinate of a point of `Fin (n+2) → ℝ`. -/
def minCoord (v : Fin (n + 2) → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty v

theorem minCoord_le (v : Fin (n + 2) → ℝ) (k : Fin (n + 2)) : minCoord v ≤ v k :=
  Finset.inf'_le _ (Finset.mem_univ k)

theorem exists_eq_minCoord (v : Fin (n + 2) → ℝ) : ∃ k, minCoord v = v k := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty) v
  exact ⟨k, hk⟩

/-- The scaling factor of the radial push is positive: the smallest coordinate of the projected
point is strictly below the barycentric value. -/
theorem minCoord_piFun_lt {x : stdSimplex ℝ (Fin (n + 3))} (hx : x ∈ Wc n) :
    ((n : ℝ) + 2) * minCoord (piFun x) < 1 := by
  by_contra hcon
  push_neg at hcon
  have hpos : (0:ℝ) < (n : ℝ) + 2 := by positivity
  have hge : ∀ k : Fin (n + 2), (1 : ℝ) / ((n : ℝ) + 2) ≤ piFun x k := by
    intro k
    have h := minCoord_le (piFun x) k
    have : (1 : ℝ) / ((n : ℝ) + 2) ≤ minCoord (piFun x) := by
      rw [div_le_iff₀ hpos]
      linarith [hcon]
    linarith
  have hsumconst : ∑ _k : Fin (n + 2), (1 : ℝ) / ((n : ℝ) + 2) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hall : ∀ k : Fin (n + 2), piFun x k = (1 : ℝ) / ((n : ℝ) + 2) := by
    have heq : ∑ k : Fin (n + 2), (1 : ℝ) / ((n : ℝ) + 2) = ∑ k : Fin (n + 2), piFun x k := by
      rw [hsumconst, piFun_sum hx]
    have := (Finset.sum_eq_sum_iff_of_le (fun i _ => hge i)).1 heq
    exact fun k => (this k (Finset.mem_univ k)).symm
  -- every coordinate other than the `0`-th one is positive
  have hposc : ∀ k : Fin (n + 2), 0 < (x : Fin (n + 3) → ℝ) k.succ := by
    intro k
    have hk := hall k
    rw [piFun, div_eq_iff (one_sub_apply_zero_pos hx).ne'] at hk
    rw [hk]
    have := one_sub_apply_zero_pos hx
    positivity
  -- hence the vanishing coordinate is the `0`-th one
  obtain ⟨i, hi⟩ := hx.1
  have hi0 : i = 0 := by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · rfl
    · exact absurd hi (hposc k).ne'
  subst hi0
  -- so `x` is the barycentre of the `0`-th face
  refine hx.2.1 (stdSimplex_ext fun j => ?_)
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
  · rw [hi, barPt_apply_zero]
  · have hk := hall k
    rw [piFun, hi, sub_zero, div_one] at hk
    rw [hk, barPt_apply_succ]

/-- The radial push away from the barycentre, in coordinates. -/
def rhoFun (v : Fin (n + 2) → ℝ) (k : Fin (n + 2)) : ℝ :=
  (v k - minCoord v) / (1 - ((n : ℝ) + 2) * minCoord v)

theorem rhoFun_nonneg {v : Fin (n + 2) → ℝ} (hv : ((n : ℝ) + 2) * minCoord v < 1)
    (k : Fin (n + 2)) : 0 ≤ rhoFun v k :=
  div_nonneg (sub_nonneg.2 (minCoord_le v k)) (by linarith)

theorem rhoFun_sum {v : Fin (n + 2) → ℝ} (hv : ((n : ℝ) + 2) * minCoord v < 1)
    (hs : ∑ k : Fin (n + 2), v k = 1) : ∑ k : Fin (n + 2), rhoFun v k = 1 := by
  have hd : (1 : ℝ) - ((n : ℝ) + 2) * minCoord v ≠ 0 := by linarith
  rw [show ∑ k : Fin (n + 2), rhoFun v k
      = (∑ k : Fin (n + 2), (v k - minCoord v)) / (1 - ((n : ℝ) + 2) * minCoord v) from
    (Finset.sum_div _ _ _).symm]
  rw [Finset.sum_sub_distrib, hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [div_eq_one_iff_eq hd]
  push_cast
  ring

/-- The retraction of the punctured boundary locus onto the boundary of the `0`-th face,
read in the barycentric coordinates of that face. -/
def coordRetr (x : Wc n) : stdSimplex ℝ (Fin (n + 2)) :=
  ⟨fun k => rhoFun (piFun (x : stdSimplex ℝ (Fin (n + 3)))) k,
    fun k => rhoFun_nonneg (minCoord_piFun_lt x.2) k,
    rhoFun_sum (minCoord_piFun_lt x.2) (piFun_sum x.2)⟩

@[simp] theorem coordRetr_apply (x : Wc n) (k : Fin (n + 2)) :
    (coordRetr x : Fin (n + 2) → ℝ) k = rhoFun (piFun (x : stdSimplex ℝ (Fin (n + 3)))) k := rfl

theorem continuous_coordRetr : Continuous (coordRetr (n := n)) := by
  have hval : Continuous fun x : Wc n => ((x : stdSimplex ℝ (Fin (n + 3))) : Fin (n + 3) → ℝ) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hcoord : ∀ j : Fin (n + 3),
      Continuous fun x : Wc n => ((x : stdSimplex ℝ (Fin (n + 3))) : Fin (n + 3) → ℝ) j :=
    fun j => (continuous_apply j).comp hval
  have hden : Continuous fun x : Wc n =>
      1 - ((x : stdSimplex ℝ (Fin (n + 3))) : Fin (n + 3) → ℝ) 0 :=
    continuous_const.sub (hcoord 0)
  have hpi : ∀ k : Fin (n + 2),
      Continuous fun x : Wc n => piFun (x : stdSimplex ℝ (Fin (n + 3))) k := by
    intro k
    exact (hcoord k.succ).div hden fun x => (one_sub_apply_zero_pos x.2).ne'
  have hmin : Continuous fun x : Wc n => minCoord (piFun (x : stdSimplex ℝ (Fin (n + 3)))) :=
    Continuous.finset_inf'_apply (f := fun (k : Fin (n + 2)) (x : Wc n) =>
      piFun (x : stdSimplex ℝ (Fin (n + 3))) k) Finset.univ_nonempty
      (fun k _ => hpi k)
  refine Continuous.subtype_mk (continuous_pi fun k => ?_) _
  refine ((hpi k).sub hmin).div (continuous_const.sub (continuous_const.mul hmin)) fun x => ?_
  have := minCoord_piFun_lt x.2
  linarith

/-- The retraction lands in the boundary of the `0`-th face. -/
theorem coordRetr_mem_bdLocus (x : Wc n) : coordRetr x ∈ SpineTask17.bdLocus (n + 1) := by
  obtain ⟨k, hk⟩ := exists_eq_minCoord (piFun (x : stdSimplex ℝ (Fin (n + 3))))
  refine ⟨k, ?_⟩
  rw [coordRetr_apply, rhoFun, ← hk, sub_self, zero_div]

/-- The retraction is the identity on the boundary of the `0`-th face: if `x` has vanishing
`0`-th coordinate and its remaining coordinates form a point `v` of the boundary of the
`(n+1)`-simplex, then `coordRetr x = v`. -/
theorem coordRetr_of_face (x : Wc n) (v : stdSimplex ℝ (Fin (n + 2)))
    (h0 : ((x : stdSimplex ℝ (Fin (n + 3))) : Fin (n + 3) → ℝ) 0 = 0)
    (hk : ∀ k : Fin (n + 2),
      ((x : stdSimplex ℝ (Fin (n + 3))) : Fin (n + 3) → ℝ) k.succ = (v : Fin (n + 2) → ℝ) k)
    (hv : ∃ k, (v : Fin (n + 2) → ℝ) k = 0) : coordRetr x = v := by
  have hpi : piFun (x : stdSimplex ℝ (Fin (n + 3))) = (v : Fin (n + 2) → ℝ) := by
    funext k
    rw [piFun, h0, sub_zero, div_one, hk k]
  have hmin : minCoord (piFun (x : stdSimplex ℝ (Fin (n + 3)))) = 0 := by
    obtain ⟨k, hk0⟩ := hv
    refine le_antisymm ?_ ?_
    · have h1 := minCoord_le (piFun (x : stdSimplex ℝ (Fin (n + 3)))) k
      have h2 : piFun (x : stdSimplex ℝ (Fin (n + 3))) k = 0 := (congrFun hpi k).trans hk0
      linarith
    · obtain ⟨j, hj⟩ := exists_eq_minCoord (piFun (x : stdSimplex ℝ (Fin (n + 3))))
      have h3 : piFun (x : stdSimplex ℝ (Fin (n + 3))) j = (v : Fin (n + 2) → ℝ) j :=
        congrFun hpi j
      have h4 : (0:ℝ) ≤ (v : Fin (n + 2) → ℝ) j := stdSimplex.zero_le v j
      rw [hj, h3]
      exact h4
  refine stdSimplex_ext fun k => ?_
  rw [coordRetr_apply, rhoFun, hmin, mul_zero, sub_zero, sub_zero, div_one, hpi]

end SpineTask20
