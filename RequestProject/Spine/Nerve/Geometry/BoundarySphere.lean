import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import RequestProject.Spine.Nerve.Geometry.StandardSimplex

/-!
# Task 17, WP6 — the realized boundary is a sphere

`SpineTask17.boundaryHomeo` identifies `|∂Δ[r]|` topologically with the barycentric boundary
locus `bdLocus r = {x ∈ Σ_r : ∃ i, x i = 0}` of the geometric standard `r`-simplex.  This
module identifies that locus with the standard sphere

`Metric.sphere (0 : EuclideanSpace ℝ (Fin r)) 1`,

by *radial projection from the barycentre*, and hence proves

`SpineTask17.boundaryRealizationSphereHomeo : |∂Δ[r]| ≃ₜ S^{r-1}`.

The construction is completely explicit:

* `bary r` is the barycentre `(1/(r+1), …, 1/(r+1))`;
* `simplexGauge r y = (r+1) · maxᵢ (-yᵢ)` is the gauge of the translated simplex: for `y` in
  the hyperplane `hyper r = {y : ∑ yᵢ = 0}` one has `bary r + y ∈ Σ_r ↔ simplexGauge r y ≤ 1`
  (`mem_stdSimplex_bary_add`) and `bary r + y ∈ ∂Σ_r ↔ simplexGauge r y = 1`
  (`exists_zero_coord`, `simplexGauge_sub_bary`);
* `hyperEquiv r : hyper r ≃L[ℝ] EuclideanSpace ℝ (Fin r)` is a linear homeomorphism, obtained
  from the computation `finrank_hyper : finrank ℝ (hyper r) = r`;
* the two mutually inverse continuous maps are `sphereMap` (normalise `x - bary r`) and
  `simplexPoint` (rescale by the gauge).

Both `r = 0` (both sides empty) and `r = 1` (both sides a two-point space) are covered by the
same statement; no case hypothesis is needed.
-/

noncomputable section

open CategoryTheory Simplicial Topology Finset Metric

universe u

namespace SpineTask17

/-! ## The barycentre and the gauge of the standard simplex -/

/-- The barycentre of the geometric standard `r`-simplex. -/
def bary (r : ℕ) : Fin (r + 1) → ℝ := fun _ => ((r : ℝ) + 1)⁻¹

/-- The gauge of the standard simplex translated to the barycentre: for `y` with `∑ yᵢ = 0`,
`bary r + y` lies in the simplex exactly when `simplexGauge r y ≤ 1`, and on its boundary
exactly when `simplexGauge r y = 1`. -/
def simplexGauge (r : ℕ) (y : Fin (r + 1) → ℝ) : ℝ :=
  ((r : ℝ) + 1) * Finset.univ.sup' Finset.univ_nonempty fun i => -y i

lemma rpos (r : ℕ) : (0 : ℝ) < (r : ℝ) + 1 := by positivity

lemma simplexGauge_smul (r : ℕ) {t : ℝ} (ht : 0 ≤ t) (y : Fin (r + 1) → ℝ) :
    simplexGauge r (t • y) = t * simplexGauge r y := by
  have h : (Finset.univ.sup' Finset.univ_nonempty fun i => -(t • y) i)
      = t * Finset.univ.sup' Finset.univ_nonempty fun i => -y i := by
    rw [Finset.comp_sup'_eq_sup'_comp (g := fun z : ℝ => t * z) (H := Finset.univ_nonempty)
      (f := fun i => -y i) fun x y => mul_max_of_nonneg x y ht]
    exact congrArg _ (funext fun i => by
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, mul_neg])
  rw [simplexGauge, simplexGauge, h]; ring

lemma continuous_simplexGauge (r : ℕ) : Continuous (simplexGauge r) := by
  unfold simplexGauge
  exact continuous_const.mul (Continuous.finset_sup'_apply Finset.univ_nonempty
    fun i _ => (continuous_apply i).neg)

lemma simplexGauge_pos (r : ℕ) {y : Fin (r + 1) → ℝ} (hsum : ∑ i, y i = 0) (hy : y ≠ 0) :
    0 < simplexGauge r y := by
  have hex : ∃ i, y i < 0 := by
    by_contra hc
    push_neg at hc
    have hall : ∀ i ∈ Finset.univ, y i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hc i).1 hsum
    exact hy (funext fun i => hall i (Finset.mem_univ i))
  obtain ⟨i, hi⟩ := hex
  have h1 : 0 < Finset.univ.sup' Finset.univ_nonempty fun i => -y i :=
    lt_of_lt_of_le (by linarith) (Finset.le_sup' (fun i => -y i) (Finset.mem_univ i))
  exact mul_pos (rpos r) h1

/-- A point at gauge at most one lies in the simplex. -/
lemma mem_stdSimplex_bary_add (r : ℕ) {y : Fin (r + 1) → ℝ} (hsum : ∑ i, y i = 0)
    (hg : simplexGauge r y ≤ 1) : (bary r + y) ∈ stdSimplex ℝ (Fin (r + 1)) := by
  have hr := rpos r
  constructor
  · intro i
    have h1 : -y i ≤ Finset.univ.sup' Finset.univ_nonempty fun i => -y i :=
      Finset.le_sup' (fun i => -y i) (Finset.mem_univ i)
    have h2 : (-y i) * ((r : ℝ) + 1) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt hr)
      rw [mul_comm]
      exact le_trans this hg
    have h3 : -y i ≤ ((r : ℝ) + 1)⁻¹ := by
      rw [← one_div]
      exact (le_div_iff₀ hr).2 h2
    simp only [Pi.add_apply, bary]
    linarith
  · simp only [Pi.add_apply, bary]
    rw [Finset.sum_add_distrib, hsum, add_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp

/-- A point at gauge exactly one has a vanishing coordinate. -/
lemma exists_zero_coord (r : ℕ) {y : Fin (r + 1) → ℝ} (hg : simplexGauge r y = 1) :
    ∃ i, (bary r + y) i = 0 := by
  have hr := rpos r
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i => -y i
  refine ⟨i, ?_⟩
  have hg' : ((r : ℝ) + 1) * Finset.univ.sup' Finset.univ_nonempty (fun i => -y i) = 1 := hg
  have hs : (Finset.univ.sup' Finset.univ_nonempty fun i => -y i) = ((r : ℝ) + 1)⁻¹ := by
    field_simp
    linarith [hg']
  simp only [Pi.add_apply, bary]
  rw [← hs, hi]
  ring

/-- Conversely, a point of the simplex with a vanishing coordinate has gauge one. -/
lemma simplexGauge_sub_bary (r : ℕ) {x : Fin (r + 1) → ℝ} (hx : x ∈ stdSimplex ℝ (Fin (r + 1)))
    {i₀ : Fin (r + 1)} (hi₀ : x i₀ = 0) : simplexGauge r (x - bary r) = 1 := by
  have hr := rpos r
  have hs : (Finset.univ.sup' Finset.univ_nonempty fun i => -(x - bary r) i)
      = ((r : ℝ) + 1)⁻¹ := by
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun i _ => ?_
      have := hx.1 i
      simp only [Pi.sub_apply, bary, neg_sub]
      linarith
    · have := Finset.le_sup' (fun i => -(x - bary r) i) (Finset.mem_univ i₀)
      simp only [Pi.sub_apply, bary, hi₀, zero_sub, neg_neg] at this ⊢
      exact this
  rw [simplexGauge, hs]
  field_simp

/-! ## The hyperplane of the simplex, and its linear identification with `ℝ^r` -/

/-- The sum of the coordinates, as a linear functional. -/
def sumL (r : ℕ) : (Fin (r + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun y := ∑ i, y i
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' t a := by simp [Finset.mul_sum]

/-- The hyperplane spanned by the standard simplex, translated to the origin. -/
def hyper (r : ℕ) : Submodule ℝ (Fin (r + 1) → ℝ) := LinearMap.ker (sumL r)

lemma mem_hyper {r : ℕ} {y : Fin (r + 1) → ℝ} : y ∈ hyper r ↔ ∑ i, y i = 0 := Iff.rfl

lemma sumL_surjective (r : ℕ) : Function.Surjective (sumL r) := fun c =>
  ⟨fun i => if i = 0 then c else 0, by simp [sumL]⟩

lemma finrank_hyper (r : ℕ) : Module.finrank ℝ (hyper r) = r := by
  have h := LinearMap.finrank_range_add_finrank_ker (sumL r)
  rw [LinearMap.range_eq_top.2 (sumL_surjective r), finrank_top, Module.finrank_self,
    Module.finrank_pi] at h
  simp only [Fintype.card_fin] at h
  show Module.finrank ℝ (LinearMap.ker (sumL r)) = r
  omega

/-- A linear homeomorphism between the hyperplane of the simplex and `ℝ^r`. -/
def hyperEquiv (r : ℕ) : hyper r ≃L[ℝ] EuclideanSpace ℝ (Fin r) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [finrank_hyper])

/-! ## Radial projection : the boundary locus is the sphere -/

variable {r : ℕ}

/-- The translation of a boundary point of the simplex to the hyperplane. -/
def toHyper (x : bdLocus r) : hyper r :=
  ⟨x.1.1 - bary r, by
    have hsum : ∑ i, x.1.1 i = 1 := stdSimplex.sum_eq_one x.1
    show ∑ i, (x.1.1 - bary r) i = 0
    simp only [Pi.sub_apply, bary]
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    field_simp
    norm_num⟩

lemma simplexGauge_toHyper (x : bdLocus r) : simplexGauge r (toHyper x : Fin (r + 1) → ℝ) = 1 := by
  obtain ⟨i, hi⟩ := x.2
  exact simplexGauge_sub_bary r x.1.2 hi

lemma toHyper_ne_zero (x : bdLocus r) : toHyper x ≠ 0 := by
  intro h
  have h0 : (toHyper x : Fin (r + 1) → ℝ) = 0 := congrArg Subtype.val h
  have hone := simplexGauge_toHyper x
  rw [h0] at hone
  simp [simplexGauge] at hone

lemma hyperEquiv_toHyper_ne_zero (x : bdLocus r) : hyperEquiv r (toHyper x) ≠ 0 := by
  intro h
  exact toHyper_ne_zero x (by simpa using congrArg (hyperEquiv r).symm h)

/-- Radial projection of the boundary of the simplex onto the unit sphere. -/
def sphereMap (x : bdLocus r) : sphere (0 : EuclideanSpace ℝ (Fin r)) 1 :=
  ⟨‖hyperEquiv r (toHyper x)‖⁻¹ • hyperEquiv r (toHyper x), by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 (hyperEquiv_toHyper_ne_zero x))]⟩

lemma symm_ne_zero (w : sphere (0 : EuclideanSpace ℝ (Fin r)) 1) :
    ((hyperEquiv r).symm w.1 : Fin (r + 1) → ℝ) ≠ 0 := by
  intro h
  have h0 : (hyperEquiv r).symm w.1 = 0 := Subtype.ext h
  have : w.1 = 0 := by simpa using congrArg (hyperEquiv r) h0
  have hw : ‖w.1‖ = 1 := mem_sphere_zero_iff_norm.1 w.2
  rw [this] at hw
  simp at hw

lemma gauge_symm_pos (w : sphere (0 : EuclideanSpace ℝ (Fin r)) 1) :
    0 < simplexGauge r ((hyperEquiv r).symm w.1 : Fin (r + 1) → ℝ) :=
  simplexGauge_pos r (((hyperEquiv r).symm w.1).2) (symm_ne_zero w)

/-- The inverse radial map: rescale a unit vector until it meets the boundary. -/
def simplexPoint (w : sphere (0 : EuclideanSpace ℝ (Fin r)) 1) : bdLocus r := by
  refine ⟨⟨bary r + (simplexGauge r ((hyperEquiv r).symm w.1 : Fin (r + 1) → ℝ))⁻¹ •
      ((hyperEquiv r).symm w.1 : Fin (r + 1) → ℝ), ?_⟩, ?_⟩
  · refine mem_stdSimplex_bary_add r ?_ (le_of_eq ?_)
    · have : ∑ i, ((hyperEquiv r).symm w.1 : Fin (r + 1) → ℝ) i = 0 :=
        ((hyperEquiv r).symm w.1).2
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, this, mul_zero]
    · rw [simplexGauge_smul r (le_of_lt (inv_pos.2 (gauge_symm_pos w))),
        inv_mul_cancel₀ (ne_of_gt (gauge_symm_pos w))]
  · exact exists_zero_coord r (by
      rw [simplexGauge_smul r (le_of_lt (inv_pos.2 (gauge_symm_pos w))),
        inv_mul_cancel₀ (ne_of_gt (gauge_symm_pos w))])

lemma simplexPoint_sphereMap (x : bdLocus r) : simplexPoint (sphereMap x) = x := by
  set u := hyperEquiv r (toHyper x) with hu
  have hune : u ≠ 0 := hyperEquiv_toHyper_ne_zero x
  have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hune
  have hsymm : (hyperEquiv r).symm (sphereMap x).1 = ‖u‖⁻¹ • toHyper x := by
    show (hyperEquiv r).symm (‖u‖⁻¹ • u) = _
    rw [map_smul, hu, ContinuousLinearEquiv.symm_apply_apply]
  have hcoe : ((hyperEquiv r).symm (sphereMap x).1 : Fin (r + 1) → ℝ)
      = ‖u‖⁻¹ • (toHyper x : Fin (r + 1) → ℝ) := by rw [hsymm]; rfl
  have hgauge : simplexGauge r ((hyperEquiv r).symm (sphereMap x).1 : Fin (r + 1) → ℝ)
      = ‖u‖⁻¹ := by
    rw [hcoe, simplexGauge_smul r (inv_nonneg.2 (norm_nonneg u)), simplexGauge_toHyper, mul_one]
  apply Subtype.ext
  apply Subtype.ext
  show bary r + (simplexGauge r ((hyperEquiv r).symm (sphereMap x).1 : Fin (r + 1) → ℝ))⁻¹ •
      ((hyperEquiv r).symm (sphereMap x).1 : Fin (r + 1) → ℝ) = x.1.1
  rw [hgauge, hcoe, smul_smul, inv_inv, mul_inv_cancel₀ hnorm, one_smul]
  show bary r + (x.1.1 - bary r) = x.1.1
  abel

lemma sphereMap_simplexPoint (w : sphere (0 : EuclideanSpace ℝ (Fin r)) 1) :
    sphereMap (simplexPoint w) = w := by
  set g := simplexGauge r ((hyperEquiv r).symm w.1 : Fin (r + 1) → ℝ) with hg
  have hgpos : 0 < g := gauge_symm_pos w
  have htoH : toHyper (simplexPoint w) = g⁻¹ • (hyperEquiv r).symm w.1 := by
    apply Subtype.ext
    show (bary r + g⁻¹ • ((hyperEquiv r).symm w.1 : Fin (r + 1) → ℝ)) - bary r
        = (g⁻¹ • (hyperEquiv r).symm w.1 : hyper r)
    show (bary r + g⁻¹ • ((hyperEquiv r).symm w.1 : Fin (r + 1) → ℝ)) - bary r
        = g⁻¹ • ((hyperEquiv r).symm w.1 : Fin (r + 1) → ℝ)
    abel
  have huv : hyperEquiv r (toHyper (simplexPoint w)) = g⁻¹ • w.1 := by
    rw [htoH, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  have hwn : ‖w.1‖ = 1 := mem_sphere_zero_iff_norm.1 w.2
  have hnorm : ‖hyperEquiv r (toHyper (simplexPoint w))‖ = g⁻¹ := by
    rw [huv, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hgpos, hwn, mul_one]
  apply Subtype.ext
  show ‖hyperEquiv r (toHyper (simplexPoint w))‖⁻¹ • hyperEquiv r (toHyper (simplexPoint w)) = w.1
  rw [hnorm, huv, smul_smul, inv_inv, mul_inv_cancel₀ (ne_of_gt hgpos), one_smul]

lemma continuous_toHyper : Continuous (toHyper (r := r)) :=
  Continuous.subtype_mk
    ((continuous_subtype_val.comp continuous_subtype_val).sub continuous_const) _

lemma continuous_sphereMap : Continuous (sphereMap (r := r)) := by
  refine Continuous.subtype_mk ?_ _
  have hc : Continuous fun x : bdLocus r => hyperEquiv r (toHyper x) :=
    (hyperEquiv r).continuous.comp continuous_toHyper
  exact ((hc.norm.inv₀ fun x => norm_ne_zero_iff.2 (hyperEquiv_toHyper_ne_zero x)).smul hc)

lemma continuous_simplexPoint : Continuous (simplexPoint (r := r)) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  have hy : Continuous fun w : sphere (0 : EuclideanSpace ℝ (Fin r)) 1 =>
      (((hyperEquiv r).symm w.1 : hyper r) : Fin (r + 1) → ℝ) :=
    continuous_subtype_val.comp ((hyperEquiv r).symm.continuous.comp continuous_subtype_val)
  exact continuous_const.add
    ((((continuous_simplexGauge r).comp hy).inv₀ fun w => ne_of_gt (gauge_symm_pos w)).smul hy)

/-- **WP6.**  The barycentric boundary locus of the geometric standard `r`-simplex is
homeomorphic to the standard `(r-1)`-sphere, by radial projection from the barycentre.  For
`r = 0` both sides are empty. -/
def bdLocusSphereHomeo (r : ℕ) : bdLocus r ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin r)) 1 where
  toFun := sphereMap
  invFun := simplexPoint
  left_inv := simplexPoint_sphereMap
  right_inv := sphereMap_simplexPoint
  continuous_toFun := continuous_sphereMap
  continuous_invFun := continuous_simplexPoint

/-- **WP6, the realized statement.**  The geometric realization of the boundary of the standard
`r`-simplex is homeomorphic to the standard sphere `S^{r-1}`. -/
def boundaryRealizationSphereHomeo (r : ℕ) :
    ↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u})) ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin r)) 1 :=
  (boundaryHomeo.{u} r).trans (bdLocusSphereHomeo r)

end SpineTask17
