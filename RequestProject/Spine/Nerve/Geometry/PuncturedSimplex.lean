import RequestProject.Spine.Nerve.Geometry.BoundarySphere

/-!
# Task 23, WP2 — the radial deformation retraction of a punctured standard cell

For the geometric standard `r`-simplex `Σ_r = stdSimplex ℝ (Fin (r+1))` with barycentre
`bary r` (Task 17), this module constructs the classical **radial deformation retraction**

```
Σ_r \ {bary}  ⟶  ∂Σ_r = bdLocus r
```

using *only* the gauge `SpineTask17.simplexGauge` already built for the Task-17
boundary-sphere homeomorphism.  No new radial geometry is introduced.

The construction is: for `x ≠ bary` write `y = x - bary`, let `g = simplexGauge r y`, which
satisfies `0 < g ≤ 1`, with `g = 1` exactly on the boundary locus.  Put

```
H t x = bary + ((1-t) + t·g)⁻¹ • y .
```

Then `H 0 = id`, `H 1` is the radial retraction onto the boundary locus (its gauge is `1`), and
`H t x = x` for every `t` whenever `g = 1`, i.e. the homotopy **fixes the boundary pointwise**.

Everything is first proved in the barycentric model and then transported to the realized cell
`|Δ[r]|` along the Task-17 homeomorphism `simplexHomeo` and the Task-17 boundary identification
`boundaryHomeo`.  The case `r = 0` needs no separate treatment: `Σ_0` is a single point, which
*is* the barycentre, so the punctured cell is empty and every statement below is vacuous there.
-/

noncomputable section

open Simplicial Topology Finset unitInterval SpineTask17

universe u

namespace SpineTask23

/-! ## The barycentre and the gauge as a function on the simplex -/

/-- The barycentre of the geometric standard `r`-simplex, as a point of the simplex. -/
def baryPt (r : ℕ) : stdSimplex ℝ (Fin (r + 1)) := by
  refine ⟨bary r, fun i => ?_, ?_⟩
  · simp only [bary]; positivity
  · simp [bary, Finset.sum_const, Finset.card_univ]
    field_simp

@[simp] theorem coe_baryPt (r : ℕ) : ((baryPt r : stdSimplex ℝ (Fin (r + 1))) :
    Fin (r + 1) → ℝ) = bary r := rfl

theorem sum_bary (r : ℕ) : ∑ i, bary r i = 1 := by
  simp [bary, Finset.sum_const, Finset.card_univ]
  field_simp

theorem sum_sub_bary (r : ℕ) {x : Fin (r + 1) → ℝ} (hx : x ∈ stdSimplex ℝ (Fin (r + 1))) :
    ∑ i, (x i - bary r i) = 0 := by
  rw [Finset.sum_sub_distrib, hx.2, sum_bary, sub_self]

/-- The gauge of a point of the simplex, measured from the barycentre.  It is `≤ 1` on the
simplex, `0` only at the barycentre, and `1` exactly on the boundary locus. -/
def gaugeAt (r : ℕ) (x : stdSimplex ℝ (Fin (r + 1))) : ℝ :=
  simplexGauge r ((x : Fin (r + 1) → ℝ) - bary r)

theorem gaugeAt_le_one (r : ℕ) (x : stdSimplex ℝ (Fin (r + 1))) : gaugeAt r x ≤ 1 := by
  have hr := rpos r
  have hs : (Finset.univ.sup' Finset.univ_nonempty
      fun i => -((x : Fin (r + 1) → ℝ) - bary r) i) ≤ ((r : ℝ) + 1)⁻¹ := by
    refine Finset.sup'_le _ _ fun i _ => ?_
    have hxi : (0 : ℝ) ≤ (x : Fin (r + 1) → ℝ) i := x.2.1 i
    show -((x : Fin (r + 1) → ℝ) i - bary r i) ≤ ((r : ℝ) + 1)⁻¹
    simp only [bary, neg_sub]
    linarith
  have hnn : (0 : ℝ) ≤ ((r : ℝ) + 1) := le_of_lt hr
  rw [gaugeAt, simplexGauge]
  calc ((r : ℝ) + 1) * (Finset.univ.sup' Finset.univ_nonempty
        fun i => -((x : Fin (r + 1) → ℝ) - bary r) i)
      ≤ ((r : ℝ) + 1) * ((r : ℝ) + 1)⁻¹ := by nlinarith
    _ = 1 := by field_simp

theorem gaugeAt_pos (r : ℕ) {x : stdSimplex ℝ (Fin (r + 1))} (hx : x ≠ baryPt r) :
    0 < gaugeAt r x := by
  refine simplexGauge_pos r (sum_sub_bary r x.2) ?_
  intro h
  refine hx (Subtype.ext ?_)
  have := sub_eq_zero.1 h
  simpa using this

theorem gaugeAt_eq_one_iff (r : ℕ) (x : stdSimplex ℝ (Fin (r + 1))) :
    gaugeAt r x = 1 ↔ x ∈ bdLocus r := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_zero_coord r h
    exact ⟨i, by simpa [sub_eq_iff_eq_add'] using hi⟩
  · rintro ⟨i, hi⟩
    exact simplexGauge_sub_bary r x.2 hi

theorem continuous_gaugeAt (r : ℕ) : Continuous (gaugeAt r) :=
  (continuous_simplexGauge r).comp (by fun_prop)

/-! ## The radial homotopy in the barycentric model -/

/-- The (strictly positive) denominator of the radial homotopy. -/
def denom (r : ℕ) (t : ℝ) (x : stdSimplex ℝ (Fin (r + 1))) : ℝ := (1 - t) + t * gaugeAt r x

theorem denom_pos (r : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {x : stdSimplex ℝ (Fin (r + 1))} (hx : x ≠ baryPt r) : 0 < denom r t x := by
  have hg := gaugeAt_pos r hx
  rcases eq_or_lt_of_le ht1 with rfl | h
  · simpa [denom] using hg
  · have : 0 < 1 - t := by linarith
    have : 0 ≤ t * gaugeAt r x := mul_nonneg ht0 hg.le
    simp only [denom]
    linarith

theorem denom_zero (r : ℕ) (x : stdSimplex ℝ (Fin (r + 1))) : denom r 0 x = 1 := by
  simp [denom]

theorem denom_one (r : ℕ) (x : stdSimplex ℝ (Fin (r + 1))) : denom r 1 x = gaugeAt r x := by
  simp [denom]

theorem denom_of_bdry (r : ℕ) (t : ℝ) {x : stdSimplex ℝ (Fin (r + 1))}
    (hx : gaugeAt r x = 1) : denom r t x = 1 := by
  simp [denom, hx]

/-- The underlying coordinate tuple of the radial homotopy. -/
def radialFun (r : ℕ) (t : ℝ) (x : stdSimplex ℝ (Fin (r + 1))) : Fin (r + 1) → ℝ :=
  bary r + (denom r t x)⁻¹ • ((x : Fin (r + 1) → ℝ) - bary r)

theorem gauge_radialFun (r : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {x : stdSimplex ℝ (Fin (r + 1))} (hx : x ≠ baryPt r) :
    simplexGauge r ((denom r t x)⁻¹ • ((x : Fin (r + 1) → ℝ) - bary r))
      = (denom r t x)⁻¹ * gaugeAt r x := by
  have hd := denom_pos r ht0 ht1 hx
  exact simplexGauge_smul r (le_of_lt (inv_pos.2 hd)) _

theorem gauge_radialFun_le_one (r : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {x : stdSimplex ℝ (Fin (r + 1))} (hx : x ≠ baryPt r) :
    simplexGauge r ((denom r t x)⁻¹ • ((x : Fin (r + 1) → ℝ) - bary r)) ≤ 1 := by
  have hd := denom_pos r ht0 ht1 hx
  rw [gauge_radialFun r ht0 ht1 hx]
  rw [inv_mul_le_iff₀ hd, mul_one]
  have hg1 := gaugeAt_le_one r x
  have : (1 - t) * (gaugeAt r x - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  simp only [denom]
  nlinarith

theorem radialFun_mem (r : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {x : stdSimplex ℝ (Fin (r + 1))} (hx : x ≠ baryPt r) :
    radialFun r t x ∈ stdSimplex ℝ (Fin (r + 1)) := by
  refine mem_stdSimplex_bary_add r ?_ (gauge_radialFun_le_one r ht0 ht1 hx)
  have hsum : ∑ i, ((x : Fin (r + 1) → ℝ) i - bary r i) = 0 := sum_sub_bary r x.2
  calc ∑ i, ((denom r t x)⁻¹ • ((x : Fin (r + 1) → ℝ) - bary r)) i
      = (denom r t x)⁻¹ * ∑ i, ((x : Fin (r + 1) → ℝ) i - bary r i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => rfl
    _ = 0 := by rw [hsum, mul_zero]

/-- The radial homotopy, as a point of the simplex. -/
def radialPt (r : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {x : stdSimplex ℝ (Fin (r + 1))} (hx : x ≠ baryPt r) : stdSimplex ℝ (Fin (r + 1)) :=
  ⟨radialFun r t x, radialFun_mem r ht0 ht1 hx⟩

theorem radialFun_ne_bary (r : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {x : stdSimplex ℝ (Fin (r + 1))} (hx : x ≠ baryPt r) :
    radialFun r t x ≠ bary r := by
  intro h
  have hd := denom_pos r ht0 ht1 hx
  have h0 : (denom r t x)⁻¹ • ((x : Fin (r + 1) → ℝ) - bary r) = 0 := by
    have := congrArg (fun z => z - bary r) h
    simpa [radialFun, add_comm] using this
  have hne : ((x : Fin (r + 1) → ℝ) - bary r) ≠ 0 := by
    intro hz
    exact hx (Subtype.ext (by simpa using sub_eq_zero.1 hz))
  exact hne (by
    have := smul_eq_zero.1 h0
    rcases this with h1 | h1
    · exact absurd h1 (inv_ne_zero (ne_of_gt hd))
    · exact h1)

theorem radialFun_zero (r : ℕ) (x : stdSimplex ℝ (Fin (r + 1))) :
    radialFun r 0 x = (x : Fin (r + 1) → ℝ) := by
  simp [radialFun, denom_zero]

theorem radialFun_of_bdry (r : ℕ) (t : ℝ) {x : stdSimplex ℝ (Fin (r + 1))}
    (hx : gaugeAt r x = 1) : radialFun r t x = (x : Fin (r + 1) → ℝ) := by
  simp [radialFun, denom_of_bdry r t hx]

/-- **The endpoint of the radial homotopy lands on the boundary locus.** -/
theorem radialFun_one_mem_bdLocus (r : ℕ) {x : stdSimplex ℝ (Fin (r + 1))}
    (hx : x ≠ baryPt r) :
    (⟨radialFun r 1 x, radialFun_mem r zero_le_one le_rfl hx⟩ :
      stdSimplex ℝ (Fin (r + 1))) ∈ bdLocus r := by
  have hg := gaugeAt_pos r hx
  have hgauge : simplexGauge r ((denom r 1 x)⁻¹ • ((x : Fin (r + 1) → ℝ) - bary r)) = 1 := by
    rw [gauge_radialFun r zero_le_one le_rfl hx, denom_one]
    field_simp
  obtain ⟨i, hi⟩ := exists_zero_coord r hgauge
  exact ⟨i, hi⟩

theorem continuous_denom (r : ℕ) :
    Continuous fun p : ℝ × stdSimplex ℝ (Fin (r + 1)) => denom r p.1 p.2 := by
  unfold denom
  exact ((continuous_const.sub continuous_fst)).add
    (continuous_fst.mul ((continuous_gaugeAt r).comp continuous_snd))

/-! ## The punctured simplex, its radial retraction and the radial homotopy -/

/-- The punctured geometric standard simplex `Σ_r \ {bary}`. -/
def puncturedLocus (r : ℕ) : Set (stdSimplex ℝ (Fin (r + 1))) := {baryPt r}ᶜ

theorem ne_baryPt_of_mem {r : ℕ} {x : stdSimplex ℝ (Fin (r + 1))} (hx : x ∈ puncturedLocus r) :
    x ≠ baryPt r := hx

theorem mem_puncturedLocus_of_ne {r : ℕ} {x : stdSimplex ℝ (Fin (r + 1))} (hx : x ≠ baryPt r) :
    x ∈ puncturedLocus r := hx

/-- Points of the boundary locus are punctured points. -/
theorem bdLocus_subset_puncturedLocus (r : ℕ) : bdLocus r ⊆ puncturedLocus r := by
  intro x hx
  refine mem_puncturedLocus_of_ne ?_
  intro h
  have h1 : gaugeAt r x = 1 := (gaugeAt_eq_one_iff r x).2 hx
  rw [h] at h1
  have h0 : gaugeAt r (baryPt r) = 0 := by
    simp [gaugeAt, simplexGauge, coe_baryPt]
  rw [h0] at h1
  exact zero_ne_one h1

theorem continuous_radialFun_pair (r : ℕ) :
    Continuous fun p : I × ↥(puncturedLocus r) =>
      radialFun r (p.1 : ℝ) (p.2 : stdSimplex ℝ (Fin (r + 1))) := by
  have hd : Continuous fun p : I × ↥(puncturedLocus r) =>
      denom r (p.1 : ℝ) (p.2 : stdSimplex ℝ (Fin (r + 1))) :=
    (continuous_denom r).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  have hne : ∀ p : I × ↥(puncturedLocus r),
      denom r (p.1 : ℝ) (p.2 : stdSimplex ℝ (Fin (r + 1))) ≠ 0 := fun p =>
    ne_of_gt (denom_pos r p.1.2.1 p.1.2.2 (ne_baryPt_of_mem p.2.2))
  refine continuous_const.add (Continuous.smul (hd.inv₀ hne) ?_)
  exact (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)).sub
    continuous_const

/-- The image of a punctured point under the radial homotopy, as a punctured point. -/
def radialHomotopyFun (r : ℕ) (p : I × ↥(puncturedLocus r)) : ↥(puncturedLocus r) :=
  ⟨⟨radialFun r (p.1 : ℝ) (p.2 : stdSimplex ℝ (Fin (r + 1))),
      radialFun_mem r p.1.2.1 p.1.2.2 (ne_baryPt_of_mem p.2.2)⟩,
    mem_puncturedLocus_of_ne (by
      intro h
      exact radialFun_ne_bary r p.1.2.1 p.1.2.2 (ne_baryPt_of_mem p.2.2)
        (congrArg Subtype.val h))⟩

/-- **The radial homotopy of the punctured standard simplex.** -/
def radialHomotopy (r : ℕ) : C(I × ↥(puncturedLocus r), ↥(puncturedLocus r)) where
  toFun := radialHomotopyFun r
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact continuous_radialFun_pair r

@[simp] theorem coe_radialHomotopy (r : ℕ) (p : I × ↥(puncturedLocus r)) :
    ((radialHomotopy r p : ↥(puncturedLocus r)) : Fin (r + 1) → ℝ)
      = radialFun r (p.1 : ℝ) (p.2 : stdSimplex ℝ (Fin (r + 1))) := rfl

/-- At time `0` the radial homotopy is the identity. -/
theorem radialHomotopy_zero (r : ℕ) (x : ↥(puncturedLocus r)) :
    radialHomotopy r (0, x) = x := by
  apply Subtype.ext; apply Subtype.ext
  simpa using radialFun_zero r (x : stdSimplex ℝ (Fin (r + 1)))

/-- The radial homotopy fixes the boundary locus pointwise, at every time. -/
theorem radialHomotopy_of_bdLocus (r : ℕ) (t : I) (x : ↥(puncturedLocus r))
    (hx : (x : stdSimplex ℝ (Fin (r + 1))) ∈ bdLocus r) :
    radialHomotopy r (t, x) = x := by
  apply Subtype.ext; apply Subtype.ext
  exact radialFun_of_bdry r (t : ℝ) ((gaugeAt_eq_one_iff r _).2 hx)

/-- At time `1` the radial homotopy lands in the boundary locus. -/
theorem radialHomotopy_one_mem_bdLocus (r : ℕ) (x : ↥(puncturedLocus r)) :
    ((radialHomotopy r (1, x) : ↥(puncturedLocus r)) : stdSimplex ℝ (Fin (r + 1)))
      ∈ bdLocus r :=
  radialFun_one_mem_bdLocus r (ne_baryPt_of_mem x.2)

/-- **The radial retraction of the punctured standard simplex onto its boundary locus.** -/
def radialRetract (r : ℕ) : C(↥(puncturedLocus r), ↥(bdLocus r)) where
  toFun x := ⟨(radialHomotopy r (1, x) : ↥(puncturedLocus r)),
    radialHomotopy_one_mem_bdLocus r x⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact ((radialHomotopy r).continuous.comp (by fun_prop)).subtype_val

@[simp] theorem coe_radialRetract (r : ℕ) (x : ↥(puncturedLocus r)) :
    ((radialRetract r x : ↥(bdLocus r)) : stdSimplex ℝ (Fin (r + 1)))
      = (radialHomotopy r (1, x) : ↥(puncturedLocus r)) := rfl

/-- **The retraction restricts to the identity on the boundary locus.** -/
theorem radialRetract_of_bdLocus (r : ℕ) (x : ↥(puncturedLocus r))
    (hx : (x : stdSimplex ℝ (Fin (r + 1))) ∈ bdLocus r) :
    ((radialRetract r x : ↥(bdLocus r)) : stdSimplex ℝ (Fin (r + 1)))
      = (x : stdSimplex ℝ (Fin (r + 1))) :=
  congrArg Subtype.val (radialHomotopy_of_bdLocus r 1 x hx)

/-- At time `1` the radial homotopy is the retraction followed by the inclusion. -/
theorem radialHomotopy_one (r : ℕ) (x : ↥(puncturedLocus r)) :
    ((radialHomotopy r (1, x) : ↥(puncturedLocus r)) : stdSimplex ℝ (Fin (r + 1)))
      = ((radialRetract r x : ↥(bdLocus r)) : stdSimplex ℝ (Fin (r + 1))) := rfl

/-! ## Transport to the realized standard cell `|Δ[r]|` -/

section Realized

open CategoryTheory SSet

variable (r : ℕ)

/-- The barycentre of the realized standard cell `|Δ[r]|`. -/
def cellBary : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})) := (simplexHomeo.{u} ⦋r⦌).symm (baryPt r)

/-- The punctured realized standard cell `|Δ[r]| \ {barycentre}`. -/
def puncturedCell : Set ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})) := {cellBary.{u} r}ᶜ

@[simp] theorem simplexHomeo_cellBary :
    simplexHomeo.{u} ⦋r⦌ (cellBary.{u} r) = baryPt r :=
  (simplexHomeo.{u} ⦋r⦌).apply_symm_apply _

theorem mem_puncturedCell_iff (x : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))) :
    x ∈ puncturedCell.{u} r ↔ simplexHomeo.{u} ⦋r⦌ x ∈ puncturedLocus r := by
  constructor
  · intro hx h
    exact hx (by
      have := congrArg (simplexHomeo.{u} ⦋r⦌).symm h
      simpa [cellBary] using this)
  · intro hx h
    have hxe : x = cellBary.{u} r := h
    exact hx (by rw [hxe, simplexHomeo_cellBary]; exact rfl)

/-- The punctured realized cell is homeomorphic to the punctured barycentric model. -/
def puncturedCellHomeo : ↥(puncturedCell.{u} r) ≃ₜ ↥(puncturedLocus r) :=
  (simplexHomeo.{u} ⦋r⦌).subtype (mem_puncturedCell_iff.{u} r)

@[simp] theorem coe_puncturedCellHomeo (x : ↥(puncturedCell.{u} r)) :
    ((puncturedCellHomeo.{u} r x : ↥(puncturedLocus r)) : stdSimplex ℝ (Fin (r + 1)))
      = simplexHomeo.{u} ⦋r⦌ (x : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))) := rfl

/-- The realized boundary inclusion `|∂Δ[r]| ⟶ |Δ[r]|`, as a continuous map. -/
def cellBdryIncl : C(↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u})),
    ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u}))) :=
  ⟨SpineTask16.Rz.{u}.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι,
    (SSet.toTop.{u}.map (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex).ι).hom.continuous⟩

theorem simplexHomeo_cellBdryIncl
    (b : ↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u}))) :
    simplexHomeo.{u} ⦋r⦌ (cellBdryIncl.{u} r b)
      = ((boundaryHomeo.{u} r b : bdLocus r) : stdSimplex ℝ (Fin (r + 1))) := rfl

/-- A point of the realized boundary is a punctured point of the cell. -/
theorem cellBdryIncl_mem_puncturedCell
    (b : ↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u}))) :
    cellBdryIncl.{u} r b ∈ puncturedCell.{u} r := by
  refine (mem_puncturedCell_iff.{u} r _).2 ?_
  rw [simplexHomeo_cellBdryIncl]
  exact bdLocus_subset_puncturedLocus r (boundaryHomeo.{u} r b).2

/-- The realized boundary, viewed inside the punctured cell. -/
def bdryToPunctured :
    C(↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u})),
      ↥(puncturedCell.{u} r)) where
  toFun b := ⟨cellBdryIncl.{u} r b, cellBdryIncl_mem_puncturedCell.{u} r b⟩
  continuous_toFun := (cellBdryIncl.{u} r).continuous.subtype_mk _

/-- **WP2, the retraction.**  The radial retraction of the punctured realized cell onto the
realized boundary. -/
def cellRetract : C(↥(puncturedCell.{u} r),
    ↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u}))) where
  toFun x := (boundaryHomeo.{u} r).symm (radialRetract r (puncturedCellHomeo.{u} r x))
  continuous_toFun :=
    (boundaryHomeo.{u} r).symm.continuous.comp
      ((radialRetract r).continuous.comp (puncturedCellHomeo.{u} r).continuous)

/-- **WP2, the homotopy.**  The radial homotopy of the punctured realized cell. -/
def cellHomotopy : C(I × ↥(puncturedCell.{u} r), ↥(puncturedCell.{u} r)) where
  toFun p := (puncturedCellHomeo.{u} r).symm (radialHomotopy r (p.1, puncturedCellHomeo.{u} r p.2))
  continuous_toFun :=
    (puncturedCellHomeo.{u} r).symm.continuous.comp
      ((radialHomotopy r).continuous.comp
        (continuous_fst.prodMk ((puncturedCellHomeo.{u} r).continuous.comp continuous_snd)))

/-- **The homotopy starts at the identity.** -/
theorem cellHomotopy_zero (x : ↥(puncturedCell.{u} r)) : cellHomotopy.{u} r (0, x) = x := by
  show (puncturedCellHomeo.{u} r).symm (radialHomotopy r (0, puncturedCellHomeo.{u} r x)) = x
  rw [radialHomotopy_zero]
  exact (puncturedCellHomeo.{u} r).symm_apply_apply x

/-- **The homotopy ends at the inclusion of the retraction.** -/
theorem cellHomotopy_one (x : ↥(puncturedCell.{u} r)) :
    (cellHomotopy.{u} r (1, x) : ↥(SSet.toTop.{u}.obj (Δ[r] : SSet.{u})))
      = cellBdryIncl.{u} r (cellRetract.{u} r x) := by
  apply (simplexHomeo.{u} ⦋r⦌).injective
  rw [simplexHomeo_cellBdryIncl]
  show (puncturedCellHomeo.{u} r ((puncturedCellHomeo.{u} r).symm
      (radialHomotopy r (1, puncturedCellHomeo.{u} r x))) : stdSimplex ℝ (Fin (r + 1))) = _
  rw [(puncturedCellHomeo.{u} r).apply_symm_apply]
  show ((radialHomotopy r (1, puncturedCellHomeo.{u} r x) : ↥(puncturedLocus r)) :
      stdSimplex ℝ (Fin (r + 1)))
    = ((boundaryHomeo.{u} r ((boundaryHomeo.{u} r).symm
        (radialRetract r (puncturedCellHomeo.{u} r x))) : bdLocus r) :
      stdSimplex ℝ (Fin (r + 1)))
  rw [(boundaryHomeo.{u} r).apply_symm_apply]
  exact radialHomotopy_one r _

/-- **The homotopy fixes the realized boundary pointwise.** -/
theorem cellHomotopy_bdry (t : I)
    (b : ↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u}))) :
    cellHomotopy.{u} r (t, bdryToPunctured.{u} r b) = bdryToPunctured.{u} r b := by
  show (puncturedCellHomeo.{u} r).symm
      (radialHomotopy r (t, puncturedCellHomeo.{u} r (bdryToPunctured.{u} r b)))
    = bdryToPunctured.{u} r b
  rw [radialHomotopy_of_bdLocus r t _ (by
    show simplexHomeo.{u} ⦋r⦌ (cellBdryIncl.{u} r b) ∈ bdLocus r
    rw [simplexHomeo_cellBdryIncl]
    exact (boundaryHomeo.{u} r b).2)]
  exact (puncturedCellHomeo.{u} r).symm_apply_apply _

/-- **The retraction restricts to the identity on the realized boundary.** -/
theorem cellRetract_bdryToPunctured
    (b : ↥(SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u}))) :
    cellRetract.{u} r (bdryToPunctured.{u} r b) = b := by
  have h := cellHomotopy_one.{u} r (bdryToPunctured.{u} r b)
  rw [cellHomotopy_bdry.{u} r 1 b] at h
  have hinj : Function.Injective (cellBdryIncl.{u} r) :=
    SpineTask16.subcomplexMono (∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)
  exact (hinj h.symm)

end Realized

end SpineTask23
