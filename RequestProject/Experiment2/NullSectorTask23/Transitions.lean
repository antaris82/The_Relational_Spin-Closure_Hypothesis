import RequestProject.Experiment2.NullSectorTask23.Sections

/-!
# Task 23, Packages D and E: overlap factors and their exact laws

**RECONSTRUCTION LAYER.**

For two domains the two local representatives over a common visible element differ by a
factor of the kernel-sign carrier `Sgn`; that factor exists, is unique (item 32), lies in
`{+1,-1}` by construction (item 33) and is a *continuous* function of the visible element
on the overlap (item 34) — hence locally constant and constant on every preconnected subset
of the overlap (items 35, 37).

Item 36 is answered negatively and explicitly: an overlap of the chosen family need **not**
be preconnected, and the componentwise sign data are genuinely needed (item 38).

Package E proves the exact identity, inverse and triple-overlap laws (items 39–42).  Only
after them is the comparison remark permitted (item 43); it is made in the final comparison
module, not here.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask23

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21

open Quaternion Topology

/-! ## Elementary sign arithmetic -/

theorem sgnOf_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    sgnOf (mul_ne_zero ha hb) = sgnOf ha * sgnOf hb := by
  refine Subtype.ext ?_
  rw [Sgn.mul_val, sgnOf_val, sgnOf_val, sgnOf_val, abs_mul]
  field_simp

theorem sgnOf_smul_pos {a : ℝ} (ha : a ≠ 0) {u : LiftT} {i : Fin 4}
    (hu : qco i (u : W) = a) : 0 < qco i ((sact (sgnOf ha) u : LiftT) : W) := by
  rw [sact_val, qco_smul, hu]
  exact sgnOf_pos ha

/-! ## The relative factor -/

theorem qco_sec_ne_zero {i j : Fin 4} {g : GvisT} (hi : g ∈ Vset i) (hj : g ∈ Vset j) :
    qco j ((sec i ⟨g, hi⟩ : LiftT) : W) ≠ 0 :=
  mem_Vset_iff.1 hj (sec i ⟨g, hi⟩) (pr_sec i ⟨g, hi⟩)

/-- **PACKAGE D (item 31), principal definition.**  The relative factor of the two local
representatives over a point of an overlap. -/
noncomputable def tauAt (i j : Fin 4) (g : GvisT) (hi : g ∈ Vset i) (hj : g ∈ Vset j) : Sgn :=
  sgnOf (qco_sec_ne_zero hi hj)

/-- **PACKAGE D (items 31, 32, 33), principal.**  The relative factor is a kernel sign and it
relates the two local representatives exactly. -/
theorem sec_eq_tau_smul {i j : Fin 4} {g : GvisT} (hi : g ∈ Vset i) (hj : g ∈ Vset j) :
    sec j ⟨g, hj⟩ = sact (tauAt i j g hi hj) (sec i ⟨g, hi⟩) := by
  refine (sec_unique ?_ ?_).symm
  · rw [pr_sact, pr_sec]
  · exact sgnOf_smul_pos (qco_sec_ne_zero hi hj) rfl

/-- **PACKAGE D (item 32).**  The relative factor is the unique sign with that property. -/
theorem tauAt_unique {i j : Fin 4} {g : GvisT} (hi : g ∈ Vset i) (hj : g ∈ Vset j) {e : Sgn}
    (he : sec j ⟨g, hj⟩ = sact e (sec i ⟨g, hi⟩)) : e = tauAt i j g hi hj := by
  refine sact_injective_sign (sec i ⟨g, hi⟩) ?_
  rw [← he, sec_eq_tau_smul hi hj]

/-- **PACKAGE D.**  The relative factor computed from an arbitrary representative of the
visible element. -/
theorem tauAt_eq_of_rep {i j : Fin 4} {g : GvisT} (hi : g ∈ Vset i) (hj : g ∈ Vset j)
    {u : LiftT} (hu : pr u = g) :
    tauAt i j g hi hj =
      sgnOf (mul_ne_zero (mem_Vset_iff.1 hi u hu) (mem_Vset_iff.1 hj u hu)) := by
  have hui : qco i (u : W) ≠ 0 := mem_Vset_iff.1 hi u hu
  have huj : qco j (u : W) ≠ 0 := mem_Vset_iff.1 hj u hu
  have hsec : sec i ⟨g, hi⟩ = sact (sgnOf hui) u := by
    refine (sec_unique ?_ ?_).symm
    · rw [pr_sact, hu]
    · exact sgnOf_smul_pos hui rfl
  have hval : qco j ((sec i ⟨g, hi⟩ : LiftT) : W) = ((sgnOf hui : Sgn) : ℝ) * qco j (u : W) := by
    rw [hsec, sact_val, qco_smul]
  rcases lt_or_gt_of_ne hui with hA | hA <;> rcases lt_or_gt_of_ne huj with hB | hB
  · have hs : ((sgnOf hui : Sgn) : ℝ) = -1 := congrArg Subtype.val (sgnOf_eq_negOne hui hA)
    have h1 : 0 < qco j ((sec i ⟨g, hi⟩ : LiftT) : W) := by rw [hval, hs]; linarith
    rw [tauAt, sgnOf_eq_one _ h1, sgnOf_eq_one _ (mul_pos_of_neg_of_neg hA hB)]
  · have hs : ((sgnOf hui : Sgn) : ℝ) = -1 := congrArg Subtype.val (sgnOf_eq_negOne hui hA)
    have h1 : qco j ((sec i ⟨g, hi⟩ : LiftT) : W) < 0 := by rw [hval, hs]; linarith
    rw [tauAt, sgnOf_eq_negOne _ h1, sgnOf_eq_negOne _ (mul_neg_of_neg_of_pos hA hB)]
  · have hs : ((sgnOf hui : Sgn) : ℝ) = 1 := congrArg Subtype.val (sgnOf_eq_one hui hA)
    have h1 : qco j ((sec i ⟨g, hi⟩ : LiftT) : W) < 0 := by rw [hval, hs]; linarith
    rw [tauAt, sgnOf_eq_negOne _ h1, sgnOf_eq_negOne _ (mul_neg_of_pos_of_neg hA hB)]
  · have hs : ((sgnOf hui : Sgn) : ℝ) = 1 := congrArg Subtype.val (sgnOf_eq_one hui hA)
    have h1 : 0 < qco j ((sec i ⟨g, hi⟩ : LiftT) : W) := by rw [hval, hs]; linarith
    rw [tauAt, sgnOf_eq_one _ h1, sgnOf_eq_one _ (mul_pos hA hB)]

/-! ## Regularity of the relative factor (items 34, 35) -/

/-- The overlap of two domains. -/
def Ovl (i j : Fin 4) : Set GvisT := Vset i ∩ Vset j

theorem isOpen_Ovl (i j : Fin 4) : IsOpen (Ovl i j) := (isOpen_Vset i).inter (isOpen_Vset j)

/-- The relative factor as a function on the overlap. -/
noncomputable def tau (i j : Fin 4) (g : ↥(Ovl i j)) : Sgn := tauAt i j (g : GvisT) g.2.1 g.2.2

/-- **PACKAGE D (item 34), principal.**  The relative factor is continuous on the overlap. -/
theorem continuous_tau (i j : Fin 4) : Continuous (tau i j) := by
  have hincl : Continuous fun g : ↥(Ovl i j) => (⟨(g : GvisT), g.2.1⟩ : ↥(Vset i)) :=
    Continuous.subtype_mk continuous_subtype_val _
  have hr : Continuous fun g : ↥(Ovl i j) => qco j ((sec i ⟨(g : GvisT), g.2.1⟩ : LiftT) : W) :=
    ((continuous_qco j).comp continuous_subtype_val).comp ((continuous_sec i).comp hincl)
  refine Continuous.subtype_mk ?_ _
  have hne : ∀ g : ↥(Ovl i j), |qco j ((sec i ⟨(g : GvisT), g.2.1⟩ : LiftT) : W)| ≠ 0 :=
    fun g => abs_ne_zero.2 (qco_sec_ne_zero g.2.1 g.2.2)
  exact hr.div hr.abs hne

/-- **PACKAGE D (item 35).**  The relative factor is locally constant. -/
theorem isLocallyConstant_tau (i j : Fin 4) : IsLocallyConstant (tau i j) :=
  (IsLocallyConstant.iff_continuous _).2 (continuous_tau i j)

/-- **PACKAGE D (item 37).**  On every preconnected part of an overlap the relative factor is
a single sign. -/
theorem tau_const_of_isPreconnected {i j : Fin 4} {S : Set ↥(Ovl i j)} (hS : IsPreconnected S)
    {g h : ↥(Ovl i j)} (hg : g ∈ S) (hh : h ∈ S) : tau i j g = tau i j h :=
  (isLocallyConstant_tau i j).apply_eq_of_isPreconnected hS hg hh

/-! ## Package E: the exact laws -/

/-- **PACKAGE E (item 40).**  The relative factor of a domain with itself is the unit. -/
theorem tauAt_self (i : Fin 4) (g : GvisT) (hi : g ∈ Vset i) : tauAt i i g hi hi = 1 :=
  (tauAt_unique hi hi (by rw [sact_one])).symm

/-- **PACKAGE E (item 39), principal.**  The exact triple-overlap law, in the order fixed by
the definition. -/
theorem tauAt_trans (a b c : Fin 4) (g : GvisT) (ha : g ∈ Vset a) (hb : g ∈ Vset b)
    (hc : g ∈ Vset c) :
    tauAt a c g ha hc = tauAt b c g hb hc * tauAt a b g ha hb := by
  refine (tauAt_unique ha hc ?_).symm
  rw [sec_eq_tau_smul hb hc, sec_eq_tau_smul ha hb, ← sact_mul]

/-- **PACKAGE E (item 41).**  The inverse law. -/
theorem tauAt_symm (a b : Fin 4) (g : GvisT) (ha : g ∈ Vset a) (hb : g ∈ Vset b) :
    tauAt b a g hb ha = (tauAt a b g ha hb)⁻¹ := by
  have h := tauAt_trans a b a g ha hb ha
  rw [tauAt_self a g ha] at h
  have h' : tauAt b a g hb ha * tauAt a b g ha hb = 1 := h.symm
  exact eq_inv_of_mul_eq_one_left h'

/-- **PACKAGE E (item 42).**  Only after the general inverse law: since the kernel carrier has
order two, the inverse law simplifies to symmetry. -/
theorem tauAt_symm' (a b : Fin 4) (g : GvisT) (ha : g ∈ Vset a) (hb : g ∈ Vset b) :
    tauAt b a g hb ha = tauAt a b g ha hb := by
  rw [tauAt_symm a b g ha hb, Sgn.inv_eq]

/-! ## Items 36, 38: overlaps need not be connected -/

theorem sqrt_two_half_sq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  linarith [h]

theorem sqrt_two_half_pos : 0 < Real.sqrt 2 / 2 := by
  have h : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  linarith

/-- The two explicit overlap points used for the disconnectedness statement. -/
noncomputable def exPt (s : ℝ) : W :=
  fromQuat ⟨Real.sqrt 2 / 2, s * (Real.sqrt 2 / 2), 0, 0⟩

theorem exPt_mem_Lift {s : ℝ} (hs : s = 1 ∨ s = -1) : exPt s ∈ Lift := by
  refine fromQuat_mem_Lift ?_
  have h := sqrt_two_half_sq
  rcases hs with rfl | rfl <;>
    · simp only [normSq_def']
      nlinarith [h]

@[simp] theorem qco_zero_fromQuat (q : ℍ) : qco 0 (fromQuat q) = q.re := by
  have h := (fromQuat_coord q).1
  simp only [qco_zero, h]

@[simp] theorem qco_one_fromQuat (q : ℍ) : qco 1 (fromQuat q) = q.imI := by
  have h := (fromQuat_coord q).2.2.2
  simp only [qco_one, h, neg_neg]

theorem qco_zero_exPt (s : ℝ) : qco 0 (exPt s) = Real.sqrt 2 / 2 := by
  rw [exPt, qco_zero_fromQuat]

theorem qco_one_exPt (s : ℝ) : qco 1 (exPt s) = s * (Real.sqrt 2 / 2) := by
  rw [exPt, qco_one_fromQuat]

theorem exPt_mem_Ovl {s : ℝ} (hs : s = 1 ∨ s = -1) :
    pr ⟨exPt s, exPt_mem_Lift hs⟩ ∈ Ovl 0 1 := by
  have h0 : qco 0 (exPt s) ≠ 0 := by
    rw [qco_zero_exPt]; exact ne_of_gt sqrt_two_half_pos
  have h1 : qco 1 (exPt s) ≠ 0 := by
    rw [qco_one_exPt]
    rcases hs with rfl | rfl <;>
      · simp only [one_mul, neg_mul]
        first
          | exact ne_of_gt sqrt_two_half_pos
          | exact ne_of_lt (by linarith [sqrt_two_half_pos])
  exact ⟨mem_Vset_of h0, mem_Vset_of h1⟩

theorem tau_exPt {s : ℝ} (hs : s = 1 ∨ s = -1) :
    tau 0 1 ⟨pr ⟨exPt s, exPt_mem_Lift hs⟩, exPt_mem_Ovl hs⟩
      = sgnOf (show s * (Real.sqrt 2 / 2) ≠ 0 by
          rcases hs with rfl | rfl <;>
            · simp only [one_mul, neg_mul]
              first
                | exact ne_of_gt sqrt_two_half_pos
                | exact ne_of_lt (by linarith [sqrt_two_half_pos])) := by
  set u : LiftT := ⟨exPt s, exPt_mem_Lift hs⟩ with hu
  have hpos : 0 < qco 0 ((u : LiftT) : W) := by
    rw [hu]
    show 0 < qco 0 (exPt s)
    rw [qco_zero_exPt]; exact sqrt_two_half_pos
  have hsec : sec 0 ⟨pr u, (exPt_mem_Ovl hs).1⟩ = u := (sec_unique rfl hpos).symm
  refine Subtype.ext ?_
  rw [tau, tauAt, sgnOf_val, sgnOf_val, hsec]
  show qco 1 (exPt s) / |qco 1 (exPt s)| = _
  rw [qco_one_exPt]

/-- **PACKAGE D (items 36, 38), principal negative result.**  The overlap of two domains of
the chosen family need not be preconnected: the relative factor takes both signs on the
overlap `Vset 0 ∩ Vset 1`, so the sign data on an overlap are genuinely componentwise and
cannot be replaced by a single sign. -/
theorem ovl_not_preconnected :
    ∃ g h : ↥(Ovl 0 1), tau 0 1 g ≠ tau 0 1 h ∧ ¬ IsPreconnected (Set.univ : Set ↥(Ovl 0 1)) := by
  have hp : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have hm : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  refine ⟨⟨pr ⟨exPt 1, exPt_mem_Lift hp⟩, exPt_mem_Ovl hp⟩,
    ⟨pr ⟨exPt (-1), exPt_mem_Lift hm⟩, exPt_mem_Ovl hm⟩, ?_, ?_⟩
  · rw [tau_exPt hp, tau_exPt hm]
    intro hcon
    have h := congrArg Subtype.val hcon
    rw [sgnOf_val, sgnOf_val] at h
    have hpos : 0 < Real.sqrt 2 / 2 := sqrt_two_half_pos
    rw [show (1 : ℝ) * (Real.sqrt 2 / 2) = Real.sqrt 2 / 2 by ring,
      show (-1 : ℝ) * (Real.sqrt 2 / 2) = -(Real.sqrt 2 / 2) by ring,
      abs_of_pos hpos, abs_neg, abs_of_pos hpos] at h
    field_simp at h
    linarith
  · intro hpre
    have h := tau_const_of_isPreconnected hpre (g := ⟨pr ⟨exPt 1, exPt_mem_Lift hp⟩,
      exPt_mem_Ovl hp⟩) (h := ⟨pr ⟨exPt (-1), exPt_mem_Lift hm⟩, exPt_mem_Ovl hm⟩)
      (Set.mem_univ _) (Set.mem_univ _)
    rw [tau_exPt hp, tau_exPt hm] at h
    have h' := congrArg Subtype.val h
    rw [sgnOf_val, sgnOf_val] at h'
    have hpos : 0 < Real.sqrt 2 / 2 := sqrt_two_half_pos
    rw [show (1 : ℝ) * (Real.sqrt 2 / 2) = Real.sqrt 2 / 2 by ring,
      show (-1 : ℝ) * (Real.sqrt 2 / 2) = -(Real.sqrt 2 / 2) by ring,
      abs_of_pos hpos, abs_neg, abs_of_pos hpos] at h'
    field_simp at h'
    linarith

end NullSectorTask23
