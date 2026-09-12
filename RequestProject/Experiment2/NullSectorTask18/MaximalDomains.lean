import RequestProject.Experiment2.NullSectorTask18.ConnectedAdmissibility

/-!
# Task 18, Package B: geometry of maximal connected admissible domains

The word *maximal* is meaningless without the class in which maximality is taken (§15), and
the answer really does depend on the class.  Four classes are named below and kept apart:

```
AdmClass         : admissible
OpenAdmClass     : open, admissible
OpenConnAdmClass : open, preconnected, admissible
PreconnAdmClass  : preconnected, admissible
```

Results (§16–§20):

* `lexA` — an explicit lexicographic half-space of unit directions containing exactly one
  member of every antipodal pair — is admissible and path-connected, and is
  inclusion-**maximal** in `PreconnAdmClass` (§16).  No maximality principle and no chain
  argument is used: the maximal member is constructed (§17).
* every nonempty inherited domain `Dom v` is inclusion-**maximal** in `OpenConnAdmClass`
  (§16), through an explicit curve leaving the domain transversally;
* `Dom e1` is **not** maximal in `OpenAdmClass`: dropping connectedness destroys the
  previous item, by an explicit strictly larger open admissible domain (§16);
* `Dom v` is not maximal in `AdmClass` (inherited Task-17 refutation) (§16);
* every nonempty `Dom v` has (at least) **two** inequivalent connected admissible
  extensions, neither containing the other (§18);
* the structural property preventing further enlargement is `AntipodalComplete`: for
  antipodal-free sets, inclusion-maximality among antipodal-free sets is *equivalent* to
  containing one member of every antipodal pair, and antipodal-completeness implies
  maximality in `PreconnAdmClass` (§19);
* no already reconstructed algebraic datum selects a maximal connected admissible
  extension: `lexA` and `lexB` are two **different** maximal members of `PreconnAdmClass`,
  both containing `Dom e1`, and *every* explicit local model `locFam k` is an exact
  representative on both.  Non-canonicity is therefore stated, not resolved by convention
  (§20).
-/

namespace NullSectorTask18

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17

/-! ## §15 — the classes, and inclusion-maximality inside a class -/

/-- **NEUTRAL DEFINITION (§15).**  Inclusion-maximality inside an explicitly given class of
sets of directions. -/
def IsMaximalIn (C : Set Vec3 → Prop) (D : Set Vec3) : Prop :=
  C D ∧ ∀ E : Set Vec3, C E → D ⊆ E → E = D

/-- **NEUTRAL DEFINITION (§15).**  Admissible sets of unit directions. -/
def AdmClass (D : Set Vec3) : Prop := UnitSet D ∧ IsAdmissibleDomain D

/-- **NEUTRAL DEFINITION (§15).**  Open admissible sets of unit directions. -/
def OpenAdmClass (D : Set Vec3) : Prop := UnitSet D ∧ OpenDomain D ∧ IsAdmissibleDomain D

/-- **NEUTRAL DEFINITION (§15).**  Open preconnected admissible sets of unit
directions. -/
def OpenConnAdmClass (D : Set Vec3) : Prop :=
  UnitSet D ∧ OpenDomain D ∧ PreconnDomain D ∧ IsAdmissibleDomain D

/-- **NEUTRAL DEFINITION (§15).**  Preconnected admissible sets of unit directions. -/
def PreconnAdmClass (D : Set Vec3) : Prop :=
  UnitSet D ∧ PreconnDomain D ∧ IsAdmissibleDomain D

/-- **NEUTRAL DEFINITION (§19).**  A set of directions meets every antipodal pair of unit
directions. -/
def AntipodalComplete (D : Set Vec3) : Prop := ∀ n : Vec3, IsUnitAxis n → n ∈ D ∨ -n ∈ D

theorem neg_ne_self_of_isUnitAxis {n : Vec3} (hn : IsUnitAxis n) : -n ≠ n := by
  intro h
  have h1 : (-n).1 = n.1 := by rw [h]
  have h2 : (-n).2.1 = n.2.1 := by rw [h]
  have h3' : (-n).2.2 = n.2.2 := by rw [h]
  simp only [Prod.fst_neg, Prod.snd_neg] at h1 h2 h3'
  have hu : h3 n n = 1 := hn
  rw [h3_self_coord] at hu
  have c1 : n.1 = 0 := by linarith
  have c2 : n.2.1 = 0 := by linarith
  have c3 : n.2.2 = 0 := by linarith
  rw [c1, c2, c3] at hu
  norm_num at hu

/-! ## §19 — antipodal completeness is exactly the obstruction to enlargement -/

/-- **PRINCIPAL THEOREM (§19).**  For an antipodal-free set of unit directions,
inclusion-maximality among antipodal-free sets of unit directions is *equivalent* to
meeting every antipodal pair. -/
theorem maximal_antipodalFree_iff_complete {D : Set Vec3} (hunit : UnitSet D)
    (hfree : AntipodalFree D) :
    (∀ E : Set Vec3, UnitSet E → AntipodalFree E → D ⊆ E → E = D) ↔ AntipodalComplete D := by
  constructor
  · intro hmax n hn
    by_contra hcon
    push_neg at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    have hunitE : UnitSet (D ∪ {n}) := by
      rintro m (hm | hm)
      · exact hunit m hm
      · rw [Set.mem_singleton_iff] at hm; rw [hm]; exact hn
    have hfreeE : AntipodalFree (D ∪ {n}) := by
      rintro m (hm | hm) hneg
      · rcases hneg with hneg | hneg
        · exact hfree m hm hneg
        · rw [Set.mem_singleton_iff] at hneg
          have : m = -n := by rw [← hneg]; simp
          rw [this] at hm
          exact hn2 hm
      · rw [Set.mem_singleton_iff] at hm
        subst hm
        rcases hneg with hneg | hneg
        · exact hn2 hneg
        · rw [Set.mem_singleton_iff] at hneg
          exact neg_ne_self_of_isUnitAxis hn hneg
    have := hmax (D ∪ {n}) hunitE hfreeE Set.subset_union_left
    have hmem : n ∈ D := by
      rw [← this]; exact Set.mem_union_right _ rfl
    exact hn1 hmem
  · intro hcomp E hunitE hfreeE hsub
    refine Set.Subset.antisymm ?_ hsub
    intro n hn
    rcases hcomp n (hunitE n hn) with h | h
    · exact h
    · exact absurd (hsub h) (hfreeE n hn)

/-- **DERIVED (§19).**  Antipodal completeness implies inclusion-maximality inside the
preconnected admissible class: any preconnected admissible enlargement is antipodal-free
(Package A) and therefore cannot add a new direction. -/
theorem maximal_preconnAdm_of_complete {D : Set Vec3} (hD : PreconnAdmClass D)
    (hcomp : AntipodalComplete D) : IsMaximalIn PreconnAdmClass D := by
  refine ⟨hD, fun E hE hsub => ?_⟩
  obtain ⟨hunitE, hpreE, hadmE⟩ := hE
  have hfreeE : AntipodalFree E := antipodalFree_of_admissible_preconn hunitE hpreE hadmE
  refine Set.Subset.antisymm ?_ hsub
  intro n hn
  rcases hcomp n (hunitE n hn) with h | h
  · exact h
  · exact absurd (hsub h) (hfreeE n hn)

/-! ## §16, §17 — an explicit maximal preconnected admissible domain -/

theorem lexA_pathConn : PathConnDomain lexA :=
  lexlike_isPathConnected lexA_unit (fun _ h => lexA_fst_nonneg h) Dom_e1_subset_lexA

theorem lexB_pathConn : PathConnDomain lexB :=
  lexlike_isPathConnected lexB_unit (fun _ h => lexB_fst_nonneg h) Dom_e1_subset_lexB

theorem lexA_admissible : IsAdmissibleDomain lexA :=
  (antipodalFree_admissible lexA_unit lexA_antipodalFree).2

theorem lexB_admissible : IsAdmissibleDomain lexB :=
  (antipodalFree_admissible lexB_unit lexB_antipodalFree).2

theorem lexA_preconnAdm : PreconnAdmClass lexA :=
  ⟨lexA_unit, lexA_pathConn.preconn, lexA_admissible⟩

theorem lexB_preconnAdm : PreconnAdmClass lexB :=
  ⟨lexB_unit, lexB_pathConn.preconn, lexB_admissible⟩

/-- **PRINCIPAL THEOREM (§16, §17).**  The explicit lexicographic half-space is an
inclusion-maximal preconnected admissible set of unit directions.  It is *constructed*: no
maximality principle, chain argument, or choice of an upper bound is used. -/
theorem lexA_maximal : IsMaximalIn PreconnAdmClass lexA :=
  maximal_preconnAdm_of_complete lexA_preconnAdm (fun _ hn => lexA_complete hn)

theorem lexB_maximal : IsMaximalIn PreconnAdmClass lexB :=
  maximal_preconnAdm_of_complete lexB_preconnAdm (fun _ hn => lexB_complete hn)

/-! ## §16 — the inherited domains are maximal among open preconnected admissible sets -/

theorem sphSet_union (A B : Set Vec3) : sphSet (A ∪ B) = sphSet A ∪ sphSet B := by
  ext s; simp [sphSet]

/-- **DERIVED.**  For a unit direction with vanishing inherited form against `v` the
renormalized straight line towards the reversed normalization of `v` is a curve of unit
directions which starts at the given direction and immediately leaves the domain. -/
theorem transversal_curve {v n : Vec3} (hv : v ≠ 0) (hn : IsUnitAxis n) (h0 : h3 n v = 0) :
    ∃ γ : ℝ → Vec3, Continuous γ ∧ (∀ t, IsUnitAxis (γ t)) ∧ γ 0 = n ∧
      ∀ t : ℝ, 0 < t → h3 (γ t) v < 0 := by
  set w : Vec3 := nrmz v with hw
  have hwpos : 0 < h3 w v := (nrmz_pos_iff hv v).2 (h3_self_pos hv)
  have hlin : ∀ t : ℝ, h3 (segLin n (-w) t) v = -(t * h3 w v) := by
    intro t
    rw [h3_segLin_left, h0, h3_neg_left]
    ring
  have hne : ∀ t : ℝ, segLin n (-w) t ≠ 0 := by
    intro t hz
    have h1 := hlin t
    have hz0 : h3 (0 : Vec3) v = 0 := by simp [h3, dot3]
    rw [hz, hz0] at h1
    have ht : t = 0 := by
      have h1' : t * h3 w v = 0 := by linarith [h1]
      rcases mul_eq_zero.1 h1' with h | h
      · exact h
      · exact absurd h (ne_of_gt hwpos)
    rw [ht, segLin_zero] at hz
    exact isUnitAxis_ne_zero hn hz
  refine ⟨fun t => segPath n (-w) t, ?_, fun t => nrmz_isUnitAxis (hne t), segPath_zero hn, ?_⟩
  · refine continuousOn_univ.1 ?_
    exact continuousOn_nrmz_comp (continuous_segLin n (-w)) (fun t _ => hne t)
  · intro t ht
    show h3 (nrmz (segLin n (-w) t)) v < 0
    rw [h3_nrmz_left, hlin t]
    have hinv : 0 < (nrm (segLin n (-w) t))⁻¹ := inv_pos.2 (nrm_pos (hne t))
    have : 0 < t * h3 w v := mul_pos ht hwpos
    nlinarith

/-- **PRINCIPAL THEOREM (§16).**  Every nonempty inherited domain is inclusion-maximal in
the class of **open preconnected admissible** sets of unit directions.  Both hypotheses are
used: openness supplies the transversal escape, preconnectedness supplies
antipodal-freeness. -/
theorem Dom_maximal_openConnAdm {v : Vec3} (hv : v ≠ 0) :
    IsMaximalIn OpenConnAdmClass (Dom v) := by
  have hunitD : UnitSet (Dom v) := fun n hn => hn.1
  refine ⟨⟨hunitD, isOpen_sphSet_Dom v, isPreconnected_sphSet_Dom hv,
    (antipodalFree_admissible hunitD (fun n hn => Dom_antipodal_free hn)).2⟩, ?_⟩
  rintro E ⟨hunitE, hopenE, hpreE, hadmE⟩ hsub
  have hfreeE : AntipodalFree E := antipodalFree_of_admissible_preconn hunitE hpreE hadmE
  refine Set.Subset.antisymm ?_ hsub
  intro n hn
  have hnu : IsUnitAxis n := hunitE n hn
  by_contra hcon
  have hle : h3 n v ≤ 0 := by
    by_contra hpos
    exact hcon (mem_Dom_iff.2 ⟨hnu, not_le.1 hpos⟩)
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hmem : -n ∈ Dom v := ⟨isUnitAxis_neg hnu, by rw [h3_neg_left]; linarith⟩
    exact hfreeE n hn (hsub hmem)
  · obtain ⟨γ, hcont, hunitγ, hγ0, hγneg⟩ := transversal_curve hv hnu heq
    obtain ⟨δ, hδ, hball⟩ := open_curve_nearby hopenE hcont hunitγ (by rw [hγ0]; exact hn)
    have ht : |δ / 2| < δ := by
      rw [abs_of_pos (by linarith)]; linarith
    have hmemE : γ (δ / 2) ∈ E := hball _ ht
    have hmemD : -γ (δ / 2) ∈ Dom v :=
      ⟨isUnitAxis_neg (hunitγ _), by rw [h3_neg_left]; linarith [hγneg (δ / 2) (by linarith)]⟩
    exact hfreeE _ hmemE (hsub hmemD)

/-! ## §16 — without connectedness the previous theorem fails -/

/-- **NEUTRAL DEFINITION.**  The clamped linear rate used in the counterexample below. -/
noncomputable def clampRate (x : Vec3) : ℝ := (1 / 2) * max (-1) (min 1 (4 * x.1 + 1))

/-- **NEUTRAL DEFINITION.**  An explicit open admissible set strictly containing
`Dom e1`: the domain together with the open cap around the reversed direction. -/
def bigCap : Set Vec3 := Dom e1 ∪ {n : Vec3 | IsUnitAxis n ∧ n.1 < -1 / 2}

theorem clampRate_of_pos {x : Vec3} (h : 0 < x.1) : clampRate x = 1 / 2 := by
  have h1 : min (1 : ℝ) (4 * x.1 + 1) = 1 := by
    apply min_eq_left; linarith
  rw [clampRate, h1, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num

theorem clampRate_of_neg {x : Vec3} (h : x.1 < -1 / 2) : clampRate x = -(1 / 2) := by
  have h1 : min (1 : ℝ) (4 * x.1 + 1) = 4 * x.1 + 1 := by
    apply min_eq_right; linarith
  rw [clampRate, h1, max_eq_left (by linarith : 4 * x.1 + 1 ≤ -1)]
  norm_num

theorem continuous_clampRate : Continuous fun s : Sph => clampRate (s : Vec3) := by
  have hfst : Continuous fun s : Sph => ((s : Vec3)).1 :=
    continuous_fst.comp continuous_subtype_val
  unfold clampRate
  fun_prop

/-- **PRINCIPAL THEOREM (§16): REFUTATION.**  Dropping preconnectedness invalidates the
maximality of the inherited domains: `bigCap` is open, admissible, and strictly contains
`Dom e1`.  (It is of course not preconnected — that is exactly the point.) -/
theorem Dom_not_maximal_openAdm :
    OpenAdmClass bigCap ∧ Dom e1 ⊆ bigCap ∧ bigCap ≠ Dom e1 ∧
      ¬ IsMaximalIn OpenAdmClass (Dom e1) := by
  have hunit : UnitSet bigCap := by
    rintro n (hn | hn)
    · exact hn.1
    · exact hn.1
  have hopen : OpenDomain bigCap := by
    have h2 : IsOpen (sphSet {n : Vec3 | IsUnitAxis n ∧ n.1 < -1 / 2}) := by
      have he : sphSet {n : Vec3 | IsUnitAxis n ∧ n.1 < -1 / 2}
          = (fun s : Sph => ((s : Vec3)).1) ⁻¹' Set.Iio (-1 / 2) := by
        ext s
        simp only [mem_sphSet, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio]
        exact ⟨fun h => h.2, fun h => ⟨s.2, h⟩⟩
      rw [he]
      exact ((continuous_fst.comp continuous_subtype_val).isOpen_preimage _ isOpen_Iio)
    rw [OpenDomain, bigCap, sphSet_union]
    exact (isOpen_sphSet_Dom e1).union h2
  have hhalf : ∀ n ∈ bigCap, ∃ k : ℤ, clampRate n = (k : ℝ) + 1 / 2 := by
    rintro n (hn | hn)
    · exact ⟨0, by rw [clampRate_of_pos (mem_Dom_e1.1 hn).2]; norm_num⟩
    · exact ⟨-1, by rw [clampRate_of_neg hn.2]; norm_num⟩
  have hodd : ∀ n ∈ bigCap, -n ∈ bigCap → clampRate (-n) = -clampRate n := by
    rintro n (hn | hn) hneg
    · have hpos : 0 < n.1 := (mem_Dom_e1.1 hn).2
      have hnegn : (-n).1 < -1 / 2 := by
        rcases hneg with h | h
        · exact absurd (mem_Dom_e1.1 h).2 (by simp only [Prod.fst_neg]; linarith)
        · exact h.2
      rw [clampRate_of_neg hnegn, clampRate_of_pos hpos]
    · have hnegn : 0 < (-n).1 := by
        simp only [Prod.fst_neg]; linarith [hn.2]
      rw [clampRate_of_pos hnegn, clampRate_of_neg hn.2]
      ring
  have hadm : IsAdmissibleDomain bigCap :=
    (admissible_iff_exists_rate_function hunit).2
      ⟨clampRate, continuous_clampRate, hhalf, hodd⟩
  have hsub : Dom e1 ⊆ bigCap := Set.subset_union_left
  have hne1 : (-e1) ∈ bigCap := by
    refine Or.inr ⟨isUnitAxis_neg e1_isUnitAxis, ?_⟩
    simp only [Prod.fst_neg, e1]
    norm_num
  have hnotin : (-e1) ∉ Dom e1 := by
    intro hcon
    have := (mem_Dom_e1.1 hcon).2
    simp only [Prod.fst_neg, e1] at this
    norm_num at this
  refine ⟨⟨hunit, hopen, hadm⟩, hsub, ?_, ?_⟩
  · intro hcon
    rw [hcon] at hne1
    exact hnotin hne1
  · rintro ⟨-, hmax⟩
    have := hmax bigCap ⟨hunit, hopen, hadm⟩ hsub
    rw [this] at hne1
    exact hnotin hne1

/-! ## §16 — and the inherited domains are not maximal among admissible sets -/

/-- **DERIVED (§16), inherited refutation.**  No inherited domain is maximal in the plain
admissible class. -/
theorem Dom_not_maximal_adm {v : Vec3} (hv : v ≠ 0) : ¬ IsMaximalIn AdmClass (Dom v) := by
  obtain ⟨E, hssub, hEadm⟩ := Dom_not_maximal hv
  rintro ⟨-, hmax⟩
  have hEq : E = Dom v := hmax E ⟨hEadm.1, hEadm⟩ hssub.1
  exact ((hEq ▸ hssub : Dom v ⊂ Dom v)).2 (subset_refl _)

/-! ## §18 — two inequivalent connected admissible extensions -/

/-- **PRINCIPAL THEOREM (§18).**  Every nonempty inherited domain has (at least) two
connected admissible extensions, neither of which contains the other.  The two extensions
add the two members of one antipodal pair on the boundary of the domain. -/
theorem Dom_two_connected_extensions {v : Vec3} (hv : v ≠ 0) :
    ∃ E₁ E₂ : Set Vec3,
      (UnitSet E₁ ∧ PathConnDomain E₁ ∧ IsAdmissibleDomain E₁) ∧
      (UnitSet E₂ ∧ PathConnDomain E₂ ∧ IsAdmissibleDomain E₂) ∧
      Dom v ⊆ E₁ ∧ Dom v ⊆ E₂ ∧ ¬ E₁ ⊆ E₂ ∧ ¬ E₂ ⊆ E₁ := by
  obtain ⟨m, hmu, hm0⟩ := exists_unit_orthogonal (nrmz_isUnitAxis hv)
  have hmv : h3 m v = 0 := by
    have h1 : h3 (nrmz v) m = 0 := hm0
    rw [h3_nrmz_left] at h1
    have hnrm : (nrm v)⁻¹ ≠ 0 := ne_of_gt (inv_pos.2 (nrm_pos hv))
    have h2 : h3 v m = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hnrm
      · exact h
    rw [h3_comm]; exact h2
  -- the general construction: adjoin one boundary direction
  have key : ∀ p : Vec3, IsUnitAxis p → h3 p v = 0 →
      (UnitSet (Dom v ∪ {p}) ∧ PathConnDomain (Dom v ∪ {p}) ∧
        IsAdmissibleDomain (Dom v ∪ {p})) ∧ Dom v ⊆ Dom v ∪ {p} := by
    intro p hpu hp0
    have hunit : UnitSet (Dom v ∪ {p}) := by
      rintro n (hn | hn)
      · exact hn.1
      · rw [Set.mem_singleton_iff] at hn; rw [hn]; exact hpu
    have hfree : AntipodalFree (Dom v ∪ {p}) := by
      rintro n (hn | hn) hneg
      · rcases hneg with hneg | hneg
        · exact Dom_antipodal_free hn hneg
        · rw [Set.mem_singleton_iff] at hneg
          have : h3 (-n) v = 0 := by rw [hneg]; exact hp0
          rw [h3_neg_left] at this
          linarith [hn.2]
      · rw [Set.mem_singleton_iff] at hn
        subst hn
        rcases hneg with hneg | hneg
        · have := hneg.2
          rw [h3_neg_left, hp0] at this
          linarith
        · rw [Set.mem_singleton_iff] at hneg
          exact neg_ne_self_of_isUnitAxis hpu hneg
    have hpath : PathConnDomain (Dom v ∪ {p}) := by
      set w : Vec3 := nrmz v with hw
      have hwmem : w ∈ Dom v := (nrmz_mem_Dom_iff v).2 hv
      have hwpos : 0 < h3 w v := hwmem.2
      have hlin : ∀ t : ℝ, h3 (segLin p w t) v = t * h3 w v := by
        intro t; rw [h3_segLin_left, hp0]; ring
      have hne : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → segLin p w t ≠ 0 := by
        intro t ht hz
        have h1 := hlin t
        have hz0 : h3 (0 : Vec3) v = 0 := by simp [h3, dot3]
        rw [hz, hz0] at h1
        have ht0 : t = 0 := by
          rcases mul_eq_zero.1 h1.symm with h | h
          · exact h
          · exact absurd h (ne_of_gt hwpos)
        rw [ht0, segLin_zero] at hz
        exact isUnitAxis_ne_zero hpu hz
      have hmem : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → segPath p w t ∈ Dom v ∪ {p} := by
        intro t ht
        rcases eq_or_lt_of_le ht.1 with h | h
        · rw [← h, segPath, segLin_zero, nrmz_of_isUnitAxis hpu]
          exact Or.inr rfl
        · refine Or.inl ⟨nrmz_isUnitAxis (hne t ht), ?_⟩
          rw [segPath, h3_nrmz_left, hlin t]
          have hinv : 0 < (nrm (segLin p w t))⁻¹ := inv_pos.2 (nrm_pos (hne t ht))
          have : 0 < t * h3 w v := mul_pos h hwpos
          positivity
      refine ⟨⟨w, hwmem.1⟩, Or.inl hwmem, ?_⟩
      intro s hs
      rcases hs with hs | hs
      · have hDom := isPathConnected_sphSet_Dom hv
        have := hDom.joinedIn ⟨w, hwmem.1⟩ hwmem ⟨(s : Vec3), s.2⟩ hs
        exact this.mono (by intro x hx; exact Or.inl hx)
      · rw [Set.mem_singleton_iff] at hs
        have hsp : (s : Vec3) = p := hs
        have hjoin : JoinedIn (sphSet (Dom v ∪ {p})) ⟨p, hpu⟩ ⟨w, hwmem.1⟩ :=
          joinedIn_segPath hpu hwmem.1 hne hmem
        have hs' : s = (⟨p, hpu⟩ : Sph) := Subtype.ext hsp
        rw [hs']
        exact hjoin.symm
    exact ⟨⟨hunit, hpath, (antipodalFree_admissible hunit hfree).2⟩, Set.subset_union_left⟩
  obtain ⟨h1, hs1⟩ := key m hmu hmv
  obtain ⟨h2, hs2⟩ := key (-m) (isUnitAxis_neg hmu) (by rw [h3_neg_left, hmv, neg_zero])
  refine ⟨Dom v ∪ {m}, Dom v ∪ {-m}, h1, h2, hs1, hs2, ?_, ?_⟩
  · intro hcon
    rcases hcon (Set.mem_union_right _ rfl) with h | h
    · rw [h3_comm] at hmv
      have := h.2
      rw [h3_comm] at this
      linarith [hmv]
    · rw [Set.mem_singleton_iff] at h
      exact neg_ne_self_of_isUnitAxis hmu h.symm
  · intro hcon
    rcases hcon (Set.mem_union_right _ rfl) with h | h
    · have := h.2
      rw [h3_neg_left, hmv] at this
      linarith
    · rw [Set.mem_singleton_iff] at h
      exact neg_ne_self_of_isUnitAxis hmu h

/-! ## §20 — non-canonicity of the maximal extension -/

/-- **PRINCIPAL THEOREM (§20).**  No already reconstructed algebraic datum selects a
maximal connected admissible extension of `Dom e1`.  There are two **different**
inclusion-maximal preconnected admissible sets containing it, and *every* explicit local
model `locFam k` — the complete list of exact local representatives produced by the Task-17
classification — is an exact representative on both of them.  The choice is therefore not
canonical, and none is made here. -/
theorem maximal_extension_not_canonical :
    lexA ≠ lexB ∧ Dom e1 ⊆ lexA ∧ Dom e1 ⊆ lexB ∧
      IsMaximalIn PreconnAdmClass lexA ∧ IsMaximalIn PreconnAdmClass lexB ∧
      (∀ k : ℤ, IsTransformationValuedOn lexA (locFam k)) ∧
      (∀ k : ℤ, IsTransformationValuedOn lexB (locFam k)) :=
  ⟨lexA_ne_lexB, Dom_e1_subset_lexA, Dom_e1_subset_lexB, lexA_maximal, lexB_maximal,
    (antipodalFree_admissible lexA_unit lexA_antipodalFree).1,
    (antipodalFree_admissible lexB_unit lexB_antipodalFree).1⟩

end NullSectorTask18
