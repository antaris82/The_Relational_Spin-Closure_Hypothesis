import RequestProject.Experiment2.NullSectorTask19.PlainMaximality

/-!
# Task 19, Package F: prescribed labels on a disconnected admissible domain

`D` is an arbitrary admissible set of unit directions (§49); no connectedness is assumed.

* §50.  The label is constant on every connected component, by the inherited ambient
  continuity theorem (restated here as `label_const_on_components`).
* §51, §52, necessity.  Closure contact is an obstruction: the closures of two level sets
  carrying **different** labels are disjoint.  Separation of differently labelled component
  closures is therefore **necessary**.
* §53, sufficiency, negative half.  Separation is **not** sufficient.  An explicit domain
  with pairwise disjoint (indeed one-point, hence closed) level sets is exhibited whose
  prescribed labels are not realizable, because the labelled directions accumulate.
* §53, sufficiency, positive half.  For **two** labels, separation is sufficient: if the
  two level sets have disjoint closures and the antipodal pairs inside the domain get
  opposite labels, the labelling is realized.
* §54.  A full necessity-and-sufficiency criterion is available in the following exact
  form: the prescribed labels are realizable **iff** the associated half-odd function
  extends continuously to the **closure** of the domain, compatibly with reversal.  This is
  an extension criterion stated on the closure, not on the whole direction space, and it is
  proved in both directions.
* §56, §57.  The Task-18 four-label domain is preserved as a positive control, and the
  no-accumulation theorem as a mandatory negative control.
-/

namespace NullSectorTask19

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18

/-! ## §49 — prescribed labels -/

/-- **NEUTRAL DEFINITION (§49).**  A prescribed integer labelling of a set of unit
directions is *realized* when some exact jointly regular representative on the set has
exactly those labels. -/
def LabelRealized (D : Set Vec3) (l : Vec3 → ℤ) : Prop :=
  ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧ IsTransformationValuedOn D U ∧
    ∀ n ∈ D, rateBeta U n = (l n : ℝ) + 1 / 2

/-- **NEUTRAL DEFINITION (§51).**  The level set of a prescribed labelling. -/
def LabelLevel (D : Set Vec3) (l : Vec3 → ℤ) (j : ℤ) : Set Vec3 := {n : Vec3 | n ∈ D ∧ l n = j}

theorem labelLevel_subset {D : Set Vec3} {l : Vec3 → ℤ} {j : ℤ} : LabelLevel D l j ⊆ D :=
  fun _ h => h.1

/-! ## §50 — the label is constant on components -/

/-- **PRINCIPAL THEOREM (§50).**  The label is constant on every connected component of the
domain.  This is the inherited ambient continuity theorem, restated for prescribed
labels. -/
theorem label_const_on_components {D : Set Vec3} {l : Vec3 → ℤ} (hunit : UnitSet D)
    (h : LabelRealized D l) (s : Sph) :
    ∀ t ∈ connectedComponentIn (sphSet D) s, ∀ t' ∈ connectedComponentIn (sphSet D) s,
      (t : Vec3) ∈ D → (t' : Vec3) ∈ D → l (t : Vec3) = l (t' : Vec3) := by
  obtain ⟨U, hU, hexact, hlab⟩ := h
  intro t ht t' ht' htD ht'D
  have := label_const_on_component hU hunit hexact s t ht t' ht'
  rw [hlab _ htD, hlab _ ht'D] at this
  exact_mod_cast (by linarith : ((l (t : Vec3) : ℝ)) = ((l (t' : Vec3) : ℝ)))

/-! ## §51, §52 — separation of differently labelled closures is necessary -/

/-- **DERIVED.**  A continuous rate constant on a set is constant on its closure. -/
theorem rate_eq_on_closure {b : Vec3 → ℝ} (hb : RateCont b) {S : Set Vec3} {c : ℝ}
    (h : ∀ n ∈ S, b n = c) {p : Sph} (hp : p ∈ closure (sphSet S)) : b (p : Vec3) = c := by
  have hclosed : IsClosed {s : Sph | b (s : Vec3) = c} := isClosed_eq hb continuous_const
  have hsub : sphSet S ⊆ {s : Sph | b (s : Vec3) = c} := fun s hs => h _ hs
  exact hclosed.closure_subset_iff.2 hsub hp

/-- **PRINCIPAL THEOREM (§51, §52).**  *Necessity of separation.*  If a prescribed
labelling is realized, the closures of two level sets with different labels are
disjoint. -/
theorem label_levels_separated {D : Set Vec3} {l : Vec3 → ℤ}
    (h : LabelRealized D l) {j k : ℤ} (hjk : j ≠ k) :
    closure (sphSet (LabelLevel D l j)) ∩ closure (sphSet (LabelLevel D l k)) = ∅ := by
  obtain ⟨U, hU, hexact, hlab⟩ := h
  have hcont : RateCont (rateBeta U) := jointlyRegular_beta_continuous hU
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro p ⟨hpj, hpk⟩
  have hj : rateBeta U (p : Vec3) = (j : ℝ) + 1 / 2 := by
    refine rate_eq_on_closure hcont ?_ hpj
    rintro n ⟨hnD, hnl⟩
    rw [hlab n hnD, hnl]
  have hk : rateBeta U (p : Vec3) = (k : ℝ) + 1 / 2 := by
    refine rate_eq_on_closure hcont ?_ hpk
    rintro n ⟨hnD, hnl⟩
    rw [hlab n hnD, hnl]
  have : ((j : ℝ)) = ((k : ℝ)) := by rw [hj] at hk; linarith
  exact hjk (by exact_mod_cast this)

/-! ## §54 — the exact extension criterion on the closure -/

/-- **PRINCIPAL THEOREM (§54).**  *Necessity and sufficiency.*  A prescribed labelling of an
arbitrary set of unit directions is realized **iff** the associated half-odd function
extends to a continuous function on the **closure** of the set which is odd on the antipodal
pairs contained in the set.  Both directions are proved; the sufficiency direction extends
the function from the closed set to all unit directions. -/
theorem label_closure_extension_criterion {D : Set Vec3} (hunit : UnitSet D) (l : Vec3 → ℤ) :
    LabelRealized D l ↔
      ∃ g : C(closure (sphSet D), ℝ),
        (∀ (n : Vec3) (h : n ∈ D),
          g ⟨⟨n, hunit n h⟩, subset_closure h⟩ = (l n : ℝ) + 1 / 2) ∧
        (∀ (n : Vec3) (h : n ∈ D) (h' : -n ∈ D),
          g ⟨⟨-n, hunit _ h'⟩, subset_closure h'⟩ = -g ⟨⟨n, hunit n h⟩, subset_closure h⟩) := by
  constructor
  · rintro ⟨U, hU, hexact, hlab⟩
    have hcont : RateCont (rateBeta U) := jointlyRegular_beta_continuous hU
    obtain ⟨-, -, -, hodd⟩ := admissible_necessary hU hunit hexact
    refine ⟨(⟨fun s : Sph => rateBeta U (s : Vec3), hcont⟩ :
      C(Sph, ℝ)).restrict (closure (sphSet D)), fun n h => hlab n h, fun n h h' => ?_⟩
    exact hodd n h h'
  · rintro ⟨g, hgval, hgodd⟩
    obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq (Y := ℝ) isClosed_closure g
    have hGval : ∀ (s : Sph) (hs : s ∈ closure (sphSet D)), G s = g ⟨s, hs⟩ := by
      intro s hs
      have := congrArg (fun f : C(closure (sphSet D), ℝ) => f ⟨s, hs⟩) hG
      simpa using this
    set b : Vec3 → ℝ := sepFun G with hb
    have hbval : ∀ n ∈ D, b n = (l n : ℝ) + 1 / 2 := by
      intro n hn
      have h1 : b n = G ⟨n, hunit n hn⟩ := sepFun_apply G ⟨n, hunit n hn⟩
      rw [h1, hGval _ (subset_closure hn), hgval n hn]
    refine (component_label_criterion hunit l).2 ⟨b, continuous_sepFun G, hbval, ?_⟩
    intro n hn hneg
    have h1 : b (-n) = G ⟨-n, hunit _ hneg⟩ := sepFun_apply G ⟨-n, hunit _ hneg⟩
    have h2 : b n = G ⟨n, hunit n hn⟩ := sepFun_apply G ⟨n, hunit n hn⟩
    rw [h1, h2, hGval _ (subset_closure hneg), hGval _ (subset_closure hn), hgodd n hn hneg]

/-! ## §53 — two labels: separation is sufficient -/

open Classical in
/-- **PRINCIPAL THEOREM (§53), positive half.**  For a domain split into two parts with
**disjoint closures**, any two labels compatible with reversal are realized. -/
theorem two_label_extension {S T : Set Vec3} (hunitS : UnitSet S) (hunitT : UnitSet T)
    (hdisj : Disjoint (closure (sphSet S)) (closure (sphSet T))) (j k : ℤ)
    (hodd : ∀ n ∈ S ∪ T, -n ∈ S ∪ T →
      (if n ∈ S then ((j : ℝ) + 1 / 2) else ((k : ℝ) + 1 / 2)) =
        -(if -n ∈ S then ((j : ℝ) + 1 / 2) else ((k : ℝ) + 1 / 2))) :
    IsAdmissibleDomain (S ∪ T) := by
  classical
  have hunit : UnitSet (S ∪ T) := by
    rintro n (hn | hn)
    · exact hunitS n hn
    · exact hunitT n hn
  obtain ⟨f, hf0, hf1, -⟩ :=
    exists_continuous_zero_one_of_isClosed (isClosed_closure (s := sphSet S))
      (isClosed_closure (s := sphSet T)) hdisj
  set F : Vec3 → ℝ := sepFun f with hF
  have hFS : ∀ n ∈ S, F n = 0 := by
    intro n hn
    have h1 : F n = f ⟨n, hunitS n hn⟩ := sepFun_apply f ⟨n, hunitS n hn⟩
    rw [h1]
    simpa using hf0 (subset_closure (a := (⟨n, hunitS n hn⟩ : Sph)) hn)
  have hFT : ∀ n ∈ T, F n = 1 := by
    intro n hn
    have h1 : F n = f ⟨n, hunitT n hn⟩ := sepFun_apply f ⟨n, hunitT n hn⟩
    rw [h1]
    simpa using hf1 (subset_closure (a := (⟨n, hunitT n hn⟩ : Sph)) hn)
  set b : Vec3 → ℝ := fun n => ((j : ℝ) + 1 / 2) + (((k : ℝ) + 1 / 2) - ((j : ℝ) + 1 / 2)) * F n
    with hbdef
  have hbS : ∀ n ∈ S, b n = (j : ℝ) + 1 / 2 := by
    intro n hn
    show ((j : ℝ) + 1 / 2) + (((k : ℝ) + 1 / 2) - ((j : ℝ) + 1 / 2)) * F n = (j : ℝ) + 1 / 2
    rw [hFS n hn]; ring
  have hbT : ∀ n ∈ T, b n = (k : ℝ) + 1 / 2 := by
    intro n hn
    show ((j : ℝ) + 1 / 2) + (((k : ℝ) + 1 / 2) - ((j : ℝ) + 1 / 2)) * F n = (k : ℝ) + 1 / 2
    rw [hFT n hn]; ring
  have hbif : ∀ n ∈ S ∪ T, b n = if n ∈ S then ((j : ℝ) + 1 / 2) else ((k : ℝ) + 1 / 2) := by
    rintro n (hn | hn)
    · rw [if_pos hn]; exact hbS n hn
    · by_cases hS : n ∈ S
      · rw [if_pos hS]; exact hbS n hS
      · rw [if_neg hS]; exact hbT n hn
  refine (admissible_iff_exists_rate_function hunit).2 ⟨b, ?_, ?_, ?_⟩
  · have hFcont : Continuous fun s : Sph => F (s : Vec3) := continuous_sepFun f
    exact continuous_const.add (continuous_const.mul hFcont)
  · rintro n (hn | hn)
    · exact ⟨j, hbS n hn⟩
    · by_cases hS : n ∈ S
      · exact ⟨j, hbS n hS⟩
      · exact ⟨k, hbT n hn⟩
  · intro n hn hneg
    rw [hbif n hn, hbif (-n) hneg]
    have h := hodd n hn hneg
    rcases hneg with h1 | h1
    · rw [if_pos h1]
      rw [if_pos h1] at h
      linarith [h]
    · by_cases hS : -n ∈ S
      · rw [if_pos hS]
        rw [if_pos hS] at h
        linarith [h]
      · rw [if_neg hS]
        rw [if_neg hS] at h
        linarith [h]

/-! ## §53 — separation alone is not sufficient -/

/-- **NEUTRAL DEFINITION.**  An explicit sequence of unit directions converging to the
first coordinate direction. -/
noncomputable def accPt (k : ℕ) : Vec3 := nrmz ((1, 1 / ((k : ℝ) + 1), 0) : Vec3)

theorem accPt_ne_zero (k : ℕ) : ((1, 1 / ((k : ℝ) + 1), 0) : Vec3) ≠ 0 := by
  intro hcon
  have := congrArg (fun w : Vec3 => w.1) hcon
  norm_num at this

theorem accPt_isUnitAxis (k : ℕ) : IsUnitAxis (accPt k) := nrmz_isUnitAxis (accPt_ne_zero k)

theorem accPt_ratio (k : ℕ) : (accPt k).2.1 = (1 / ((k : ℝ) + 1)) * (accPt k).1 := by
  show (nrm ((1, 1 / ((k : ℝ) + 1), 0) : Vec3))⁻¹ * (1 / ((k : ℝ) + 1))
      = (1 / ((k : ℝ) + 1)) * ((nrm ((1, 1 / ((k : ℝ) + 1), 0) : Vec3))⁻¹ * 1)
  ring

theorem accPt_fst_pos (k : ℕ) : 0 < (accPt k).1 := by
  show 0 < (nrm ((1, 1 / ((k : ℝ) + 1), 0) : Vec3))⁻¹ * 1
  have := inv_pos.2 (nrm_pos (accPt_ne_zero k))
  linarith

theorem accPt_injective : Function.Injective accPt := by
  intro k j hkj
  have h1 := accPt_ratio k
  have h2 := accPt_ratio j
  rw [hkj] at h1
  rw [h1] at h2
  have hpos := accPt_fst_pos j
  have hval : (1 / ((k : ℝ) + 1)) = (1 / ((j : ℝ) + 1)) := by
    exact (mul_right_cancel₀ (ne_of_gt hpos) h2.symm).symm
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have : ((k : ℝ) + 1) = ((j : ℝ) + 1) := by
    field_simp at hval
    linarith
  have : (k : ℝ) = (j : ℝ) := by linarith
  exact_mod_cast this

/-- **NEUTRAL DEFINITION.**  The accumulating label assignment: the index of the point in
the explicit sequence. -/
noncomputable def accLabel (n : Vec3) : ℤ :=
  open Classical in if h : ∃ k : ℕ, accPt k = n then ((h.choose : ℤ)) else 0

theorem accLabel_apply (k : ℕ) : accLabel (accPt k) = (k : ℤ) := by
  classical
  have hex : ∃ j : ℕ, accPt j = accPt k := ⟨k, rfl⟩
  rw [accLabel, dif_pos hex]
  have := hex.choose_spec
  have := accPt_injective this
  exact_mod_cast this

/-- **NEUTRAL DEFINITION.**  The domain of the counterexample: the range of the explicit
sequence. -/
def accDom : Set Vec3 := Set.range accPt

theorem accDom_unit : UnitSet accDom := by
  rintro n ⟨k, rfl⟩
  exact accPt_isUnitAxis k

/-- **DERIVED.**  The level sets of the accumulating labelling are single points, hence
closed, and their closures are pairwise disjoint. -/
theorem accDom_levels_disjoint {j k : ℤ} (hjk : j ≠ k) :
    closure (sphSet (LabelLevel accDom accLabel j)) ∩
      closure (sphSet (LabelLevel accDom accLabel k)) = ∅ := by
  have hsingle : ∀ i : ℤ, ∀ n ∈ LabelLevel accDom accLabel i, ∀ m ∈ LabelLevel accDom accLabel i,
      n = m := by
    rintro i n ⟨⟨kn, rfl⟩, hn⟩ m ⟨⟨km, rfl⟩, hm⟩
    rw [accLabel_apply] at hn hm
    have : kn = km := by omega
    rw [this]
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro p ⟨hpj, hpk⟩
  -- each level set is a subsingleton, hence closed; the closure is the set itself
  rcases Set.eq_empty_or_nonempty (LabelLevel accDom accLabel j) with hj | ⟨nj, hnj⟩
  · rw [hj] at hpj
    have : sphSet (∅ : Set Vec3) = (∅ : Set Sph) := by ext s; simp [sphSet]
    rw [this, closure_empty] at hpj
    exact hpj
  rcases Set.eq_empty_or_nonempty (LabelLevel accDom accLabel k) with hk | ⟨nk, hnk⟩
  · rw [hk] at hpk
    have : sphSet (∅ : Set Vec3) = (∅ : Set Sph) := by ext s; simp [sphSet]
    rw [this, closure_empty] at hpk
    exact hpk
  · have hclj : sphSet (LabelLevel accDom accLabel j) = {(⟨nj, accDom_unit nj hnj.1⟩ : Sph)} := by
      ext s
      constructor
      · intro hs
        exact Subtype.ext (hsingle j _ hs _ hnj)
      · intro hs
        have : (s : Vec3) = nj := congrArg Subtype.val hs
        rw [mem_sphSet, this]
        exact hnj
    have hclk : sphSet (LabelLevel accDom accLabel k) = {(⟨nk, accDom_unit nk hnk.1⟩ : Sph)} := by
      ext s
      constructor
      · intro hs
        exact Subtype.ext (hsingle k _ hs _ hnk)
      · intro hs
        have : (s : Vec3) = nk := congrArg Subtype.val hs
        rw [mem_sphSet, this]
        exact hnk
    rw [hclj, closure_singleton] at hpj
    rw [hclk, closure_singleton] at hpk
    have h1 : (p : Vec3) = nj := congrArg Subtype.val hpj
    have h2 : (p : Vec3) = nk := congrArg Subtype.val hpk
    have hnjk : nj = nk := by rw [← h1, h2]
    have hlj := hnj.2
    have hlk := hnk.2
    rw [hnjk] at hlj
    exact hjk (by rw [← hlj, hlk])

/-- **DERIVED.**  The explicit sequence converges to the first coordinate direction. -/
theorem accPt_tendsto : ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K,
    dist (⟨accPt k, accPt_isUnitAxis k⟩ : Sph) (⟨e1, e1_isUnitAxis⟩ : Sph) < ε := by
  intro ε hε
  have hne : ∀ u : ℝ, ((1, u, 0) : Vec3) ≠ 0 := by
    intro u hcon
    have := congrArg (fun w : Vec3 => w.1) hcon
    norm_num at this
  set g : ℝ → Vec3 := fun u => nrmz ((1, u, 0) : Vec3) with hg
  have hgu : ∀ u : ℝ, IsUnitAxis (g u) := fun u => nrmz_isUnitAxis (hne u)
  have hgc : Continuous g := by
    refine continuousOn_univ.1 ?_
    exact continuousOn_nrmz_comp (by fun_prop) (fun u _ => hne u)
  have hG : Continuous fun u : ℝ => (⟨g u, hgu u⟩ : Sph) := hgc.subtype_mk _
  have hg0 : g 0 = e1 := by
    have he : ((1 : ℝ), (0 : ℝ), (0 : ℝ)) = e1 := rfl
    rw [hg]
    simp only [he]
    exact nrmz_of_isUnitAxis e1_isUnitAxis
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hG 0 ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / δ)
  refine ⟨K, fun k hk => ?_⟩
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlt : 1 / ((k : ℝ) + 1) < δ := by
    have hKk : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h1 : 1 / δ < (k : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hkpos]
    rw [div_lt_iff₀ hδ] at h1
    linarith
  have hdist : dist (1 / ((k : ℝ) + 1)) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    exact hlt
  have := hball _ hdist
  have hpt : (⟨g 0, hgu 0⟩ : Sph) = (⟨e1, e1_isUnitAxis⟩ : Sph) := Subtype.ext hg0
  rw [hpt] at this
  exact this

/-- **PRINCIPAL THEOREM (§53), negative half: REFUTATION.**  Separation of the closures of
differently labelled level sets is **not** sufficient.  The explicit accumulating domain has
one-point level sets — so all closures are pairwise disjoint — and its prescribed labels are
**not** realized. -/
theorem separation_not_sufficient :
    (∀ j k : ℤ, j ≠ k →
      closure (sphSet (LabelLevel accDom accLabel j)) ∩
        closure (sphSet (LabelLevel accDom accLabel k)) = ∅) ∧
      ¬ LabelRealized accDom accLabel := by
  refine ⟨fun j k hjk => accDom_levels_disjoint hjk, ?_⟩
  rintro ⟨U, hU, hexact, hlab⟩
  obtain ⟨-, hhalf, hcont, -⟩ := admissible_necessary hU accDom_unit hexact
  obtain ⟨ε, hε, hloc⟩ :=
    labels_locally_constant hcont (fun n hn => hhalf n hn) (⟨e1, e1_isUnitAxis⟩ : Sph)
  obtain ⟨K, hK⟩ := accPt_tendsto ε hε
  have h1 := hloc ⟨accPt K, accPt_isUnitAxis K⟩ ⟨accPt (K + 1), accPt_isUnitAxis (K + 1)⟩
    ⟨K, rfl⟩ ⟨K + 1, rfl⟩ (hK K le_rfl) (hK (K + 1) (Nat.le_succ K))
  rw [hlab _ ⟨K, rfl⟩, hlab _ ⟨K + 1, rfl⟩, accLabel_apply, accLabel_apply] at h1
  have : ((K : ℝ)) = ((K : ℝ) + 1) := by push_cast at h1 ⊢; linarith
  linarith

/-! ## §56, §57 — the controls -/

/-- **POSITIVE CONTROL (§56).**  The Task-18 four-label admissible domain is preserved. -/
theorem four_label_control :
    IsAdmissibleDomain multiD ∧ e1 ∈ multiD ∧ -e1 ∈ multiD ∧ p35 ∈ multiD ∧ -p35 ∈ multiD ∧
      ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧ IsTransformationValuedOn multiD U ∧
        rateBeta U e1 = 5 / 2 ∧ rateBeta U (-e1) = -(5 / 2) ∧
        rateBeta U p35 = 3 / 2 ∧ rateBeta U (-p35) = -(3 / 2) :=
  multiD_admissible_four_labels

/-- **NEGATIVE CONTROL (§57).**  The no-accumulation theorem is preserved: labels are
locally constant, so differently labelled parts can never accumulate at a direction. -/
theorem no_accumulation_control {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    {D : Set Vec3} (hunit : UnitSet D) (hexact : IsTransformationValuedOn D U) (p : Sph) :
    ∃ ε > 0, ∀ s t : Sph, (s : Vec3) ∈ D → (t : Vec3) ∈ D →
      dist s p < ε → dist t p < ε → rateBeta U (s : Vec3) = rateBeta U (t : Vec3) :=
  admissible_labels_locally_constant hU hunit hexact p

end NullSectorTask19
