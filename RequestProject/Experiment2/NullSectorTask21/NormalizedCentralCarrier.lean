import RequestProject.Experiment2.NullSectorTask21.CentralProduct

/-!
# Task 21, Packages K and L: modulus/phase splitting and the normalized carrier

**IDENTIFICATION / COMPARISON MODULE.**

Package K splits the identified centre into its positive-modulus factor and its phase
factor, and asks whether the positive-modulus factor splits off the full internal carrier as
a direct central factor.

Package L then compares the resulting *normalized* carrier — the full internal carrier with
unit central modulus — with standard named objects.  The verdicts are recorded in
`TASK21_AUDIT.md`; only what is proved here is claimed.

`IMPORTED STANDARD RESULT`: `Circle`, `Matrix.unitaryGroup`, `Matrix.specialUnitaryGroup`.

Concerning `Spin(3)` and `Spinᶜ(3)`: the installed library provides `spinGroup` for a general
Clifford algebra but no three-dimensional model and no equivalence with unit quaternions, and
no `Spinᶜ` object at all.  Those two verdicts are therefore `NOT FORMALIZED`, and the
quotient expression proved below is kept as the formally proved object (item 108).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask21

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20

open Quaternion Matrix

/-! ## Package K — modulus and phase -/

/-- The positive real numbers as a multiplicative group. -/
abbrev Rpos : Type := {x : ℝ // 0 < x}

/-- **PACKAGE K (item 99).**  The polar decomposition of the nonzero complex numbers as a
group equivalence, with zero excluded constructively. -/
noncomputable def polarEquiv : ℂˣ ≃* Rpos × Circle where
  toFun z := (⟨‖(z : ℂ)‖, norm_pos_iff.2 (Units.ne_zero z)⟩,
    ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
      rw [Submonoid.unitSphere]
      refine mem_sphere_zero_iff_norm.2 ?_
      rw [norm_div, Complex.norm_real, norm_norm]
      exact div_self (by simp [Units.ne_zero z])⟩)
  invFun rc := Units.mk0 ((rc.1 : ℝ) • (rc.2 : ℂ)) (by
    have h1 : ((rc.2 : ℂ)) ≠ 0 := by
      intro h
      have h2 := Circle.norm_coe rc.2
      rw [h] at h2; simp at h2
    exact smul_ne_zero (ne_of_gt rc.1.2) h1)
  left_inv z := by
    refine Units.ext ?_
    show ((‖(z : ℂ)‖ : ℝ) • ((z : ℂ) / (‖(z : ℂ)‖ : ℂ))) = (z : ℂ)
    rw [Complex.real_smul]
    field_simp
  right_inv rc := by
    have hn : ‖(rc.2 : ℂ)‖ = 1 := Circle.norm_coe rc.2
    have hne : ((rc.1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt rc.1.2)
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      show ‖((rc.1 : ℝ) • (rc.2 : ℂ))‖ = (rc.1 : ℝ)
      rw [norm_smul, hn, Real.norm_eq_abs, abs_of_pos rc.1.2, mul_one]
    · refine Circle.ext ?_
      show ((rc.1 : ℝ) • (rc.2 : ℂ)) / (‖((rc.1 : ℝ) • (rc.2 : ℂ))‖ : ℂ) = (rc.2 : ℂ)
      rw [norm_smul, hn, Real.norm_eq_abs, abs_of_pos rc.1.2, mul_one, Complex.real_smul,
        mul_comm, mul_div_assoc, div_self hne, mul_one]
  map_mul' z w := by
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      show ‖((z * w : ℂˣ) : ℂ)‖ = ‖(z : ℂ)‖ * ‖(w : ℂ)‖
      rw [Units.val_mul, norm_mul]
    · refine Circle.ext ?_
      show ((z * w : ℂˣ) : ℂ) / (‖((z * w : ℂˣ) : ℂ)‖ : ℂ)
        = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) * ((w : ℂ) / (‖(w : ℂ)‖ : ℂ))
      rw [Units.val_mul, norm_mul]
      push_cast
      field_simp

theorem polarEquiv_fst (z : ℂˣ) : ((polarEquiv z).1 : ℝ) = ‖(z : ℂ)‖ := rfl

theorem polarEquiv_snd (z : ℂˣ) :
    (((polarEquiv z).2 : Circle) : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := rfl

/-! ## The coordinate modulus of the inherited carrier

The intrinsic modulus used below is the Euclidean coordinate sum of squares of the inherited
eight-dimensional carrier.  Two facts about it are all that Package K needs: it is
multiplicative under central factors, and it takes the value one on the internal core
carrier. -/

/-- **NEUTRAL DEFINITION.**  The coordinate sum of squares of a carrier element. -/
def nsq (x : W) : ℝ :=
  x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2

/-- **DERIVED.**  The coordinates of a central multiple. -/
theorem zc_mul_coords (a b : ℝ) (x : W) :
    (zc a b ⋆ x) 0 = a * x 0 - b * x 7 ∧ (zc a b ⋆ x) 1 = a * x 1 - b * x 6 ∧
      (zc a b ⋆ x) 2 = a * x 2 + b * x 5 ∧ (zc a b ⋆ x) 3 = a * x 3 - b * x 4 ∧
      (zc a b ⋆ x) 4 = a * x 4 + b * x 3 ∧ (zc a b ⋆ x) 5 = a * x 5 - b * x 2 ∧
      (zc a b ⋆ x) 6 = a * x 6 + b * x 1 ∧ (zc a b ⋆ x) 7 = a * x 7 + b * x 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [zc, w1, wS]

/-- **DERIVED.**  The coordinate modulus is multiplicative under central factors. -/
theorem nsq_zc_mul (a b : ℝ) (x : W) : nsq (zc a b ⋆ x) = (a ^ 2 + b ^ 2) * nsq x := by
  obtain ⟨h0, h1, h2, h3', h4, h5, h6, h7⟩ := zc_mul_coords a b x
  simp only [nsq, h0, h1, h2, h3', h4, h5, h6, h7]
  ring

/-- **DERIVED.**  A central factor with unit coefficient square is a real scalar. -/
theorem zc_smul_eq (r : ℝ) (x : W) : zc r 0 ⋆ x = r • x := by
  rw [zc, zero_smul, add_zero, smul_mul_W, one_mul_W]

/-- **DERIVED.**  The coordinate modulus is one on the internal core carrier. -/
theorem nsq_of_Lift {u : W} (hu : u ∈ Lift) : nsq u = 1 := by
  obtain ⟨a, v, ha, rfl⟩ := hu
  simp only [h3, dot3] at ha
  have hval : nsq (a • w1 - Jmap v) = a ^ 2 + (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) := by
    simp [nsq, w1, Jmap, wP, wQ, wR]
    ring
  rw [hval]
  nlinarith [ha]

/-! ## The normalized central plane and the normalized carrier -/

/-- **NEUTRAL DEFINITION.**  The unit-modulus part of the exact central plane. -/
def CUnit1 : Set W := {z : W | ∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧ z = zc a b}

theorem CUnit1_subset_CUnit : CUnit1 ⊆ CUnit := by
  rintro z ⟨a, b, hab, rfl⟩
  refine ⟨a, b, ?_, rfl⟩
  rintro ⟨rfl, rfl⟩
  norm_num at hab

theorem w1_mem_CUnit1 : w1 ∈ CUnit1 := ⟨1, 0, by norm_num, zc_one_zero.symm⟩

theorem CUnit1_mul_mem {z z' : W} (hz : z ∈ CUnit1) (hz' : z' ∈ CUnit1) : z ⋆ z' ∈ CUnit1 := by
  obtain ⟨a, b, hab, rfl⟩ := hz
  obtain ⟨c, d, hcd, rfl⟩ := hz'
  refine ⟨a * c - b * d, a * d + b * c, ?_, zc_mul a b c d⟩
  have h : (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
    ring
  rw [h, hab, hcd, mul_one]

/-- **DERIVED.**  The explicit inverse inside the normalized central plane. -/
theorem CUnit1_inv_pair {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    zc a b ⋆ zc a (-b) = w1 ∧ zc a (-b) ⋆ zc a b = w1 := by
  constructor
  · rw [zc_mul]
    have h1 : a * a - b * -b = 1 := by nlinarith [hab]
    have h2 : a * -b + b * a = 0 := by ring
    rw [h1, h2, zc_one_zero]
  · rw [zc_mul]
    have h1 : a * a - -b * b = 1 := by nlinarith [hab]
    have h2 : a * b + -b * a = 0 := by ring
    rw [h1, h2, zc_one_zero]

theorem CUnit1_neg_mem {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) : zc a (-b) ∈ CUnit1 :=
  ⟨a, -b, by nlinarith [hab], rfl⟩

/-- **PACKAGED.**  The unit-modulus central subgroup. -/
def CUnit1G : Subgroup WG where
  carrier := {u : WG | u.val ∈ CUnit1}
  one_mem' := by
    show (1 : WG).val ∈ CUnit1
    rw [WG.one_val]
    exact w1_mem_CUnit1
  mul_mem' := by
    intro a b ha hb
    exact CUnit1_mul_mem ha hb
  inv_mem' := by
    intro a ha
    obtain ⟨p, q, hpq, hval⟩ := ha
    have hpair := CUnit1_inv_pair hpq
    have hEq : zc p (-q) = a.inv := by
      refine inverse_unique (u := a.val) ?_ a.inv_val
      rw [hval]; exact hpair.1
    show a.inv ∈ CUnit1
    rw [← hEq]
    exact CUnit1_neg_mem hpq

/-- **NEUTRAL DEFINITION (item 104).**  The normalized full carrier: unit central
modulus. -/
def LiftZ1 : Set W := {u : W | ∃ z ∈ CUnit1, ∃ g ∈ Lift, u = z ⋆ g}

theorem LiftZ1_subset_LiftZ : LiftZ1 ⊆ LiftZ := by
  rintro u ⟨z, hz, g, hg, rfl⟩
  exact ⟨z, CUnit1_subset_CUnit hz, g, hg, rfl⟩

/-- **DERIVED.**  The coordinate modulus is one on the normalized carrier. -/
theorem nsq_of_LiftZ1 {u : W} (hu : u ∈ LiftZ1) : nsq u = 1 := by
  obtain ⟨z, ⟨a, b, hab, rfl⟩, g, hg, rfl⟩ := hu
  rw [nsq_zc_mul, nsq_of_Lift hg, hab, mul_one]

/-- **PACKAGED.**  The normalized full carrier as a group. -/
def LiftZ1G : Subgroup WG where
  carrier := {u : WG | u.val ∈ LiftZ1}
  one_mem' := by
    show (1 : WG).val ∈ LiftZ1
    rw [WG.one_val]
    exact ⟨w1, w1_mem_CUnit1, w1, w1_mem_Lift, (one_mul_W w1).symm⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨z, hz, g, hg, hav⟩ := ha
    obtain ⟨z', hz', g', hg', hbv⟩ := hb
    refine ⟨z ⋆ z', CUnit1_mul_mem hz hz', g ⋆ g', Lift_mul_mem hg hg', ?_⟩
    show a.val ⋆ b.val = (z ⋆ z') ⋆ (g ⋆ g')
    rw [hav, hbv]
    exact central_swap (CUnit1_subset_CUnit hz')
  inv_mem' := by
    intro a ha
    obtain ⟨z, ⟨p, q, hpq, rfl⟩, g, hg, hav⟩ := ha
    obtain ⟨g', hg', hgg1, hgg2⟩ := Lift_inv_mem hg
    have hpair := CUnit1_inv_pair hpq
    have hEq : zc p (-q) ⋆ g' = a.inv := by
      refine inverse_unique (u := a.val) ?_ a.inv_val
      rw [hav, central_swap (CUnit1_subset_CUnit (CUnit1_neg_mem hpq)), hpair.1, hgg1,
        one_mul_W]
    show a.inv ∈ LiftZ1
    rw [← hEq]
    exact ⟨zc p (-q), CUnit1_neg_mem hpq, g', hg', rfl⟩

theorem LiftZ1G_le_LiftZG : LiftZ1G ≤ LiftZG := fun _ hu => LiftZ1_subset_LiftZ hu

theorem zc_pos_mem_CUnit {r : ℝ} (hr : 0 < r) : zc r 0 ∈ CUnit :=
  ⟨r, 0, by rintro ⟨h, -⟩; exact absurd h (ne_of_gt hr), rfl⟩

/-- The positive central scalars inside the full internal carrier. -/
noncomputable def posCentral : Rpos →* LiftZG where
  toFun r := ⟨⟨zc (r : ℝ) 0, zc ((r : ℝ))⁻¹ 0, by
      rw [zc_mul, mul_inv_cancel₀ (ne_of_gt r.2)]
      norm_num, by
      rw [zc_mul, inv_mul_cancel₀ (ne_of_gt r.2)]
      norm_num⟩, by
    show zc (r : ℝ) 0 ∈ LiftZ
    exact CUnit_subset_LiftZ (zc_pos_mem_CUnit r.2)⟩
  map_one' := by
    refine Subtype.ext (WG.ext ?_)
    show zc ((1 : Rpos) : ℝ) 0 = w1
    have h : ((1 : Rpos) : ℝ) = 1 := rfl
    rw [h, zc_one_zero]
  map_mul' r s := by
    refine Subtype.ext (WG.ext ?_)
    show zc ((r * s : Rpos) : ℝ) 0 = zc (r : ℝ) 0 ⋆ zc (s : ℝ) 0
    rw [zc_mul, Positive.val_mul]
    norm_num

@[simp] theorem posCentral_val (r : Rpos) :
    ((posCentral r : LiftZG) : WG).val = zc (r : ℝ) 0 := rfl

/-- The map assembling a positive modulus and a normalized element. -/
noncomputable def splitMap : Rpos × LiftZ1G →* LiftZG where
  toFun rv := posCentral rv.1 * (Subgroup.inclusion LiftZ1G_le_LiftZG rv.2)
  map_one' := by
    rw [Prod.fst_one, Prod.snd_one, map_one, map_one, mul_one]
  map_mul' x y := by
    refine Subtype.ext (WG.ext ?_)
    show zc ((x.1 * y.1 : Rpos) : ℝ) 0 ⋆ ((x.2 : WG).val ⋆ (y.2 : WG).val)
      = (zc (x.1 : ℝ) 0 ⋆ (x.2 : WG).val) ⋆ (zc (y.1 : ℝ) 0 ⋆ (y.2 : WG).val)
    rw [central_swap (zc_pos_mem_CUnit y.1.2), zc_mul, Positive.val_mul]
    norm_num

theorem splitMap_val (r : Rpos) (v : LiftZ1G) :
    ((splitMap (r, v) : LiftZG) : WG).val = zc (r : ℝ) 0 ⋆ ((v : WG).val) := rfl

theorem splitMap_injective : Function.Injective splitMap := by
  rintro ⟨r, v⟩ ⟨s, w⟩ h
  have hv : nsq ((v : WG).val) = 1 := nsq_of_LiftZ1 v.2
  have hw : nsq ((w : WG).val) = 1 := nsq_of_LiftZ1 w.2
  have hval : zc (r : ℝ) 0 ⋆ (v : WG).val = zc (s : ℝ) 0 ⋆ (w : WG).val := by
    have h' := congrArg (fun u : LiftZG => ((u : WG)).val) h
    simpa only [splitMap_val] using h'
  have hn := congrArg nsq hval
  rw [nsq_zc_mul, nsq_zc_mul, hv, hw] at hn
  have hrs : (r : ℝ) = (s : ℝ) := by nlinarith [r.2, s.2]
  have hvw : (v : WG).val = (w : WG).val := by
    rw [zc_smul_eq, zc_smul_eq, hrs] at hval
    exact smul_right_injective W (ne_of_gt s.2) hval
  exact Prod.ext (Subtype.ext hrs) (Subtype.ext (WG.ext hvw))

theorem splitMap_surjective : Function.Surjective splitMap := by
  rintro ⟨u, hu⟩
  obtain ⟨z, hz, g, hg, huv⟩ := hu
  obtain ⟨a, b, hab, rfl⟩ := hz
  have hpos2 : 0 < a ^ 2 + b ^ 2 := by
    rcases (not_and_or.1 hab) with h | h
    · have : 0 < a ^ 2 := by positivity
      nlinarith [sq_nonneg b]
    · have : 0 < b ^ 2 := by positivity
      nlinarith [sq_nonneg a]
  set rr : ℝ := Real.sqrt (a ^ 2 + b ^ 2) with hrrdef
  have hpos : 0 < rr := Real.sqrt_pos.2 hpos2
  have hrr2 : rr ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (le_of_lt hpos2)
  have hnorm : (a / rr) ^ 2 + (b / rr) ^ 2 = 1 := by
    field_simp
    linarith [hrr2]
  have hmem : (zc (a / rr) (b / rr) ⋆ g) ∈ LiftZ1 :=
    ⟨zc (a / rr) (b / rr), ⟨a / rr, b / rr, hnorm, rfl⟩, g, hg, rfl⟩
  refine ⟨(⟨rr, hpos⟩,
    ⟨WG.ofInvertible (isInvertible_of_mem_LiftZ (LiftZ1_subset_LiftZ hmem)), hmem⟩), ?_⟩
  refine Subtype.ext (WG.ext ?_)
  show zc rr 0 ⋆ (zc (a / rr) (b / rr) ⋆ g) = u.val
  rw [← mul_assoc_W, zc_mul]
  have hne : rr ≠ 0 := ne_of_gt hpos
  have e1 : rr * (a / rr) - 0 * (b / rr) = a := by
    field_simp
    ring
  have e2 : rr * (b / rr) + 0 * (a / rr) = b := by
    field_simp
    ring
  rw [e1, e2, huv]

/-- **PACKAGE K (items 103, 112), principal.**  The positive-modulus factor splits off as a
direct central factor: the full internal carrier is the direct product of the positive
scalars and the normalized carrier. -/
noncomputable def liftZSplit : LiftZG ≃* Rpos × LiftZ1G :=
  (MulEquiv.ofBijective splitMap ⟨splitMap_injective, splitMap_surjective⟩).symm

theorem liftZSplit_symm_val (r : Rpos) (v : LiftZ1G) :
    ((liftZSplit.symm (r, v) : LiftZG) : WG).val = zc (r : ℝ) 0 ⋆ ((v : WG).val) := rfl

/-! ## Package L — the normalized carrier as a central extension -/

theorem circle_ne_zero (c : Circle) : ((c : ℂ)) ≠ 0 := by
  intro h
  have h2 := Circle.norm_coe c
  rw [h] at h2
  simp at h2

theorem circle_coord_sq (c : Circle) : ((c : ℂ).re) ^ 2 + ((c : ℂ).im) ^ 2 = 1 := by
  have h : Complex.normSq (c : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Circle.norm_coe c]
    norm_num
  rw [Complex.normSq_apply] at h
  nlinarith [h]

theorem ofComplex_circle_mem (c : Circle) : ofComplex ((c : ℂ)) ∈ CUnit1 :=
  ⟨(c : ℂ).re, (c : ℂ).im, circle_coord_sq c, rfl⟩

/-- The packaged invertible central element attached to a phase. -/
noncomputable def circWG (c : Circle) : WG where
  val := ofComplex ((c : ℂ))
  inv := ofComplex ((c : ℂ))⁻¹
  val_inv := by
    rw [ofComplex_mul, mul_inv_cancel₀ (circle_ne_zero c), ofComplex]
    exact zc_one_zero
  inv_val := by
    rw [ofComplex_mul, inv_mul_cancel₀ (circle_ne_zero c), ofComplex]
    exact zc_one_zero

@[simp] theorem circWG_val (c : Circle) : (circWG c).val = ofComplex ((c : ℂ)) := rfl

/-- **PACKAGE L.**  The standard-side multiplication map into the normalized carrier. -/
noncomputable def muNorm : Circle × UQ →* LiftZ1G where
  toFun cq := ⟨circWG cq.1 * quatWG cq.2, ⟨ofComplex ((cq.1 : ℂ)), ofComplex_circle_mem cq.1,
    fromQuat ((cq.2 : ℍ)), fromQuat_mem_Lift (UQ_normSq cq.2), rfl⟩⟩
  map_one' := by
    refine Subtype.ext (WG.ext ?_)
    show ofComplex (((1 : Circle) : ℂ)) ⋆ fromQuat (((1 : UQ) : ℍ)) = w1
    rw [Circle.coe_one, Metric.unitSphere.coe_one, fromQuat_one, ofComplex]
    rw [show (1 : ℂ).re = 1 from rfl, show (1 : ℂ).im = 0 from rfl, zc_one_zero, one_mul_W]
  map_mul' x y := by
    refine Subtype.ext (WG.ext ?_)
    show ofComplex (((x.1 * y.1 : Circle) : ℂ)) ⋆ fromQuat (((x.2 * y.2 : UQ) : ℍ))
      = (ofComplex ((x.1 : ℂ)) ⋆ fromQuat ((x.2 : ℍ)))
        ⋆ (ofComplex ((y.1 : ℂ)) ⋆ fromQuat ((y.2 : ℍ)))
    rw [central_swap (CUnit1_subset_CUnit (ofComplex_circle_mem y.1)), Circle.coe_mul,
      ← ofComplex_mul, Metric.unitSphere.coe_mul, fromQuat_mul]

@[simp] theorem muNorm_val (c : Circle) (q : UQ) :
    ((muNorm (c, q) : LiftZ1G) : WG).val = ofComplex ((c : ℂ)) ⋆ fromQuat ((q : ℍ)) := rfl

theorem muNorm_surjective : Function.Surjective muNorm := by
  rintro ⟨u, hu⟩
  obtain ⟨z, ⟨a, b, hab, rfl⟩, g, hg, huv⟩ := hu
  have hc : ‖((⟨a, b⟩ : ℂ))‖ = 1 := by
    have h : Complex.normSq (⟨a, b⟩ : ℂ) = 1 := by
      rw [Complex.normSq_apply]
      show a * a + b * b = 1
      nlinarith [hab]
    have h2 := Complex.normSq_eq_norm_sq (⟨a, b⟩ : ℂ)
    rw [h] at h2
    nlinarith [norm_nonneg ((⟨a, b⟩ : ℂ))]
  refine ⟨(⟨(⟨a, b⟩ : ℂ), by
      rw [Submonoid.unitSphere]; exact mem_sphere_zero_iff_norm.2 hc⟩,
    ⟨quatOf g, (mem_UQ_iff _).2 (quatOf_normSq hg)⟩), ?_⟩
  refine Subtype.ext (WG.ext ?_)
  show ofComplex ((⟨a, b⟩ : ℂ)) ⋆ fromQuat (quatOf g) = u.val
  rw [fromQuat_quatOf hg, ofComplex]
  show zc a b ⋆ g = u.val
  exact huv.symm

/-- The sign element of the phase circle. -/
def circleNegOne : Circle := ⟨-1, by simp [Submonoid.unitSphere, Metric.sphere]⟩

theorem fromQuat_neg_one : fromQuat (-1 : ℍ) = -w1 := by
  refine funext fun i => ?_
  fin_cases i <;> simp [fromQuat, w1, Jmap, wP, wQ, wR]

theorem fromQuat_injective : Function.Injective fromQuat := by
  intro q p h
  have h' := congrArg quatOf h
  rwa [quatOf_fromQuat, quatOf_fromQuat] at h'

theorem ofComplex_eq_w1 {z : ℂ} (h : ofComplex z = w1) : z = 1 := by
  have h' := congrArg toComplex h
  rwa [toComplex_ofComplex, toComplex_one] at h'

theorem ofComplex_eq_neg_w1 {z : ℂ} (h : ofComplex z = -w1) : z = -1 := by
  have h' := congrArg toComplex h
  rw [toComplex_ofComplex, ← zc_neg_one_zero, toComplex_zc] at h'
  rw [h']
  refine Complex.ext ?_ ?_ <;> simp

theorem ker_muNorm :
    (muNorm.ker : Set (Circle × UQ)) = {(1, 1), (circleNegOne, uqNegOne)} := by
  ext cq
  constructor
  · intro h
    have hval : ofComplex ((cq.1 : ℂ)) ⋆ fromQuat ((cq.2 : ℍ)) = w1 := by
      have h' := congrArg (fun v : LiftZ1G => ((v : WG)).val) (MonoidHom.mem_ker.1 h)
      simpa only [muNorm_val, WG.one_val] using h'
    -- the core factor is central, hence a sign
    have hinv : fromQuat ((cq.2 : ℍ)) = ofComplex (((cq.1 : ℂ))⁻¹) := by
      have := congrArg (fun x : W => ofComplex (((cq.1 : ℂ))⁻¹) ⋆ x) hval
      simp only at this
      rw [← mul_assoc_W, ofComplex_mul, inv_mul_cancel₀ (circle_ne_zero cq.1), ofComplex,
        show (1 : ℂ).re = 1 from rfl, show (1 : ℂ).im = 0 from rfl, zc_one_zero,
        one_mul_W, mul_one_W] at this
      exact this
    have hcore : fromQuat ((cq.2 : ℍ)) ∈ CUnit := by
      rw [hinv]
      exact ofComplex_mem_CUnit (inv_ne_zero (circle_ne_zero cq.1))
    have hlift : fromQuat ((cq.2 : ℍ)) ∈ Lift := fromQuat_mem_Lift (UQ_normSq cq.2)
    rcases CUnit_inter_Lift hcore hlift with hsign | hsign
    · left
      have hq : ((cq.2 : UQ) : ℍ) = 1 := by
        refine fromQuat_injective ?_
        rw [hsign, fromQuat_one]
      have hc : ((cq.1 : Circle) : ℂ) = 1 := by
        refine ofComplex_eq_w1 ?_
        have := hval
        rw [hsign, mul_one_W] at this
        exact this
      exact Prod.ext (Circle.ext (by rw [hc, Circle.coe_one]))
        (Subtype.ext (by rw [hq, Metric.unitSphere.coe_one]))
    · right
      have hq : ((cq.2 : UQ) : ℍ) = -1 := by
        refine fromQuat_injective ?_
        rw [hsign, fromQuat_neg_one]
      have hc : ((cq.1 : Circle) : ℂ) = -1 := by
        refine ofComplex_eq_neg_w1 ?_
        have h2 := hval
        rw [hsign, mul_neg_W, mul_one_W] at h2
        have h3 : ofComplex ((cq.1 : ℂ)) = -w1 := by
          have := congrArg (fun x : W => -x) h2
          simpa using this
        exact h3
      refine Prod.ext (Circle.ext ?_) (Subtype.ext ?_)
      · rw [hc]; rfl
      · rw [hq]; rfl
  · rintro (h | h) <;> rw [h] <;> refine MonoidHom.mem_ker.2 ?_
    · exact map_one muNorm
    · refine Subtype.ext (WG.ext ?_)
      show ofComplex ((circleNegOne : ℂ)) ⋆ fromQuat ((uqNegOne : ℍ)) = w1
      have h1 : ((circleNegOne : Circle) : ℂ) = -1 := rfl
      have h2 : ((uqNegOne : UQ) : ℍ) = -1 := rfl
      rw [h1, h2, fromQuat_neg_one, ofComplex,
        show (-1 : ℂ).re = -1 from rfl, show (-1 : ℂ).im = -0 from rfl]
      rw [show ((-0 : ℝ)) = 0 by norm_num, zc_neg_one_zero, neg_mul_W, mul_neg_W, one_mul_W,
        neg_neg]

/-- **PACKAGE L (item 105), principal.**  The exact quotient description of the normalized
carrier: it is the central product of the phase circle with the unit-quaternion core, modulo
the diagonal sign. -/
noncomputable def normalizedQuotientEquiv : ((Circle × UQ) ⧸ muNorm.ker) ≃* LiftZ1G :=
  QuotientGroup.quotientKerEquivOfSurjective muNorm muNorm_surjective

/-! ## Comparison with the standard unitary model -/

theorem smul_mem_unitary {c : ℂ} (hc : ‖c‖ = 1) {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) : c • A ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  rw [StarModule.star_smul, smul_mul_assoc, mul_smul_comm, hA, smul_smul]
  have hcc : c * star c = 1 := by
    rw [Complex.star_def, Complex.mul_conj]
    have h := Complex.normSq_eq_norm_sq c
    rw [hc] at h
    norm_num [h]
  rw [hcc, one_smul]

/-- **PACKAGE L (item 109).**  The standard-side map into the two-dimensional unitary
group. -/
noncomputable def nuU2 : Circle × UQ →* Matrix.unitaryGroup (Fin 2) ℂ where
  toFun wq := ⟨((wq.1 : ℂ) • quatMat (wq.2 : ℍ)),
    smul_mem_unitary (Circle.norm_coe wq.1) (quatMat_mem_unitary (UQ_normSq wq.2))⟩
  map_one' := by
    refine Subtype.ext ?_
    show (((1 : Circle) : ℂ)) • quatMat (((1 : UQ) : ℍ)) = 1
    rw [Circle.coe_one, Metric.unitSphere.coe_one, quatMat_one, one_smul]
  map_mul' x y := by
    refine Subtype.ext ?_
    show (((x.1 * y.1 : Circle) : ℂ)) • quatMat (((x.2 * y.2 : UQ) : ℍ))
      = ((x.1 : ℂ) • quatMat ((x.2 : ℍ))) * ((y.1 : ℂ) • quatMat ((y.2 : ℍ)))
    rw [Circle.coe_mul, Metric.unitSphere.coe_mul, quatMat_mul, smul_mul_smul_comm]

@[simp] theorem nuU2_val (c : Circle) (q : UQ) :
    ((nuU2 (c, q) : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = (c : ℂ) • quatMat ((q : ℍ)) := rfl

theorem unitary_det_norm {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) : ‖A.det‖ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.1 hA
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose,
    Matrix.det_conjTranspose, Complex.star_def, Complex.mul_conj] at h2
  have h3 : Complex.normSq A.det = 1 := by exact_mod_cast h2
  have h4 := Complex.normSq_eq_norm_sq A.det
  rw [h3] at h4
  nlinarith [norm_nonneg A.det]

theorem nuU2_surjective : Function.Surjective nuU2 := by
  rintro ⟨A, hA⟩
  obtain ⟨c, hc⟩ := IsSepClosed.exists_pow_nat_eq (A.det) 2
  have hdet : ‖A.det‖ = 1 := unitary_det_norm hA
  have hcn : ‖c‖ = 1 := by
    have h : ‖c‖ ^ 2 = 1 := by
      rw [← norm_pow, hc, hdet]
    nlinarith [norm_nonneg c, h]
  have hcne : c ≠ 0 := by
    intro h; rw [h] at hcn; simp at hcn
  have hcinv : ‖c⁻¹‖ = 1 := by rw [norm_inv, hcn, inv_one]
  have hB : c⁻¹ • A ∈ Matrix.unitaryGroup (Fin 2) ℂ := smul_mem_unitary hcinv hA
  have hBdet : (c⁻¹ • A).det = 1 := by
    rw [Matrix.det_smul]
    have hcard : (Fintype.card (Fin 2)) = 2 := by simp
    rw [hcard, ← hc]
    field_simp
  have hBSU : (c⁻¹ • A) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨hB, hBdet⟩
  obtain ⟨q, hq⟩ := toSU_surjective ⟨c⁻¹ • A, hBSU⟩
  have hqm : quatMat ((q : ℍ)) = c⁻¹ • A := congrArg Subtype.val hq
  refine ⟨(⟨c, by rw [Submonoid.unitSphere]; exact mem_sphere_zero_iff_norm.2 hcn⟩, q), ?_⟩
  refine Subtype.ext ?_
  show (c : ℂ) • quatMat ((q : ℍ)) = A
  rw [hqm, smul_smul, mul_inv_cancel₀ hcne, one_smul]

theorem quatMat_neg_one : quatMat (-1 : ℍ) = -1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [quatMat]

theorem ker_nuU2_set :
    (nuU2.ker : Set (Circle × UQ)) = {(1, 1), (circleNegOne, uqNegOne)} := by
  ext cq
  constructor
  · intro h
    have hval : ((cq.1 : ℂ)) • quatMat ((cq.2 : ℍ)) = 1 := by
      have h' := congrArg (fun U : Matrix.unitaryGroup (Fin 2) ℂ =>
        (U : Matrix (Fin 2) (Fin 2) ℂ)) (MonoidHom.mem_ker.1 h)
      have h1 : ((1 : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := rfl
      simpa only [nuU2_val, h1] using h'
    have hdet : ((cq.1 : ℂ)) ^ 2 = 1 := by
      have h2 := congrArg Matrix.det hval
      rw [Matrix.det_smul, Matrix.det_one, quatMat_det, UQ_normSq cq.2] at h2
      simpa using h2
    have hcases : ((cq.1 : ℂ)) = 1 ∨ ((cq.1 : ℂ)) = -1 := by
      have hfac : (((cq.1 : ℂ)) - 1) * (((cq.1 : ℂ)) + 1) = 0 := by
        have : ((cq.1 : ℂ)) ^ 2 - 1 = 0 := by rw [hdet]; ring
        linear_combination this
      rcases mul_eq_zero.1 hfac with h' | h'
      · exact Or.inl (by linear_combination h')
      · exact Or.inr (by linear_combination h')
    rcases hcases with hc | hc
    · left
      rw [hc, one_smul] at hval
      have hq : ((cq.2 : UQ) : ℍ) = 1 := by
        have := hval.trans quatMat_one.symm
        exact quatMat_injective this
      exact Prod.ext (Circle.ext (by rw [hc, Circle.coe_one]))
        (Subtype.ext (by rw [hq, Metric.unitSphere.coe_one]))
    · right
      rw [hc] at hval
      have hval' : quatMat ((cq.2 : ℍ)) = -1 := by
        have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (-1 : ℂ) • M) hval
        simpa [smul_smul] using this
      have hq : ((cq.2 : UQ) : ℍ) = -1 :=
        quatMat_injective (hval'.trans quatMat_neg_one.symm)
      refine Prod.ext (Circle.ext ?_) (Subtype.ext ?_)
      · rw [hc]; rfl
      · rw [hq]; rfl
  · rintro (h | h) <;> rw [h] <;> refine MonoidHom.mem_ker.2 ?_
    · exact map_one nuU2
    · refine Subtype.ext ?_
      show ((circleNegOne : Circle) : ℂ) • quatMat (((uqNegOne : UQ) : ℍ)) = 1
      have h1 : ((circleNegOne : Circle) : ℂ) = -1 := rfl
      have h2 : ((uqNegOne : UQ) : ℍ) = -1 := rfl
      rw [h1, h2, quatMat_neg_one]
      simp

theorem ker_nuU2 : nuU2.ker = muNorm.ker :=
  SetLike.ext' (ker_nuU2_set.trans ker_muNorm.symm)

/-- **PACKAGE L (item 111), verdict for the unitary model.**  The normalized carrier is
group-equivalent to the standard two-dimensional unitary group. -/
noncomputable def normalizedU2Equiv : LiftZ1G ≃* Matrix.unitaryGroup (Fin 2) ℂ :=
  normalizedQuotientEquiv.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ker_nuU2.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective nuU2 nuU2_surjective))

end NullSectorTask21
