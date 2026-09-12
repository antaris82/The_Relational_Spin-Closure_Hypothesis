import RequestProject.Experiment2.NullSectorTask18.RelationCoverage

/-!
# Task 18, Package H: disconnected admissible domains

Task 17 exhibited **one** disconnected admissible domain — an antipodal pair carrying the
two labels `1/2` and `-1/2`.  This module treats arbitrary disconnected admissible sets.

* §50.  The phenomenon is general: an explicit admissible domain is constructed whose
  members carry **four** different labels and which contains antipodal pairs.  It is a
  level set of an explicit linear rate; nothing about it is exceptional.
* §51.  The half-odd label is constant on every preconnected subset of an admissible
  domain, and in particular on every connected component of the domain, read inside the
  inherited subspace of unit directions.
* §52.  Which assignments of labels to components are compatible is settled **exactly**:
  an integer label assignment `ℓ` is realized by an exact jointly regular representative
  **iff** the function `n ↦ ℓ n + 1/2` extends to a function of the direction that is
  continuous on *all* unit directions and odd on the antipodal pairs inside the domain.
  Componentwise freedom is therefore not unconstrained.
* §53.  Accumulation is impossible: near every unit direction the labels of an admissible
  domain are **locally constant**.  Infinitely many components carrying pairwise different
  labels can therefore not accumulate anywhere, even though arbitrarily many different
  labels may occur globally.
-/

namespace NullSectorTask18

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17

/-! ## Bookkeeping: sets of unit directions and sets of directions -/

/-- **NEUTRAL DEFINITION.**  The set of directions underlying a set of unit directions. -/
def vecSet (A : Set Sph) : Set Vec3 := Subtype.val '' A

theorem sphSet_vecSet (A : Set Sph) : sphSet (vecSet A) = A := by
  ext s
  constructor
  · rintro ⟨t, ht, hts⟩
    have : t = s := Subtype.ext hts
    rwa [this] at ht
  · intro hs
    exact ⟨s, hs, rfl⟩

theorem vecSet_unit (A : Set Sph) : ∀ n ∈ vecSet A, IsUnitAxis n := by
  rintro n ⟨t, -, rfl⟩
  exact t.2

theorem vecSet_subset {A : Set Sph} {D : Set Vec3} (h : A ⊆ sphSet D) : vecSet A ⊆ D := by
  rintro n ⟨t, ht, rfl⟩
  exact h ht

theorem transformationValuedOn_mono {D D' : Set Vec3} {U : Vec3 → ℝ → W} (hsub : D' ⊆ D)
    (h : IsTransformationValuedOn D U) : IsTransformationValuedOn D' U :=
  fun n hn m hm θ φ hP => h n (hsub hn) m (hsub hm) θ φ hP

/-! ## §51 — the label is constant on preconnected parts and on components -/

/-- **PRINCIPAL THEOREM (§51).**  The recovered rate of an exact jointly regular
representative is constant on every preconnected subset of the domain. -/
theorem label_const_on_preconnected_part {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    {D S : Set Vec3} (hunit : UnitSet D) (hsub : S ⊆ D) (hpre : PreconnDomain S)
    (hexact : IsTransformationValuedOn D U) :
    ∀ n ∈ S, ∀ m ∈ S, rateBeta U n = rateBeta U m :=
  label_const_of_preconnected hU (fun n hn => hunit n (hsub hn)) hpre
    (transformationValuedOn_mono hsub hexact)

/-- **PRINCIPAL THEOREM (§51), components.**  In particular the label is constant on every
connected component of the domain, read inside the inherited subspace of unit
directions. -/
theorem label_const_on_component {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    {D : Set Vec3} (hunit : UnitSet D) (hexact : IsTransformationValuedOn D U) (s : Sph) :
    ∀ t ∈ connectedComponentIn (sphSet D) s, ∀ t' ∈ connectedComponentIn (sphSet D) s,
      rateBeta U (t : Vec3) = rateBeta U (t' : Vec3) := by
  intro t ht t' ht'
  have hsubD : vecSet (connectedComponentIn (sphSet D) s) ⊆ D :=
    vecSet_subset (connectedComponentIn_subset _ _)
  have hpre : PreconnDomain (vecSet (connectedComponentIn (sphSet D) s)) := by
    rw [PreconnDomain, sphSet_vecSet]
    exact isPreconnected_connectedComponentIn
  exact label_const_on_preconnected_part hU hunit hsubD hpre hexact _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩

/-! ## §52 — exactly which label assignments are compatible -/

/-- **PRINCIPAL THEOREM (§52).**  An integer label assignment on a set of unit directions is
realized by an exact jointly regular representative **iff** the associated half-odd function
extends to a rate function which is continuous on all unit directions and odd on the
antipodal pairs contained in the set. -/
theorem component_label_criterion {D : Set Vec3} (hunit : UnitSet D) (l : Vec3 → ℤ) :
    (∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧ IsTransformationValuedOn D U ∧
        ∀ n ∈ D, rateBeta U n = (l n : ℝ) + 1 / 2) ↔
      (∃ b : Vec3 → ℝ, (Continuous fun s : Sph => b (s : Vec3)) ∧
        (∀ n ∈ D, b n = (l n : ℝ) + 1 / 2) ∧ (∀ n ∈ D, -n ∈ D → b (-n) = -b n)) := by
  constructor
  · rintro ⟨U, hU, hexact, hlab⟩
    obtain ⟨-, -, hcont, hodd⟩ := admissible_necessary hU hunit hexact
    exact ⟨rateBeta U, hcont, hlab, hodd⟩
  · rintro ⟨b, hcont, hval, hodd⟩
    refine ⟨famOf (fun _ => 0) b, jointlyRegular_famOf continuous_const hcont, ?_, ?_⟩
    · exact famOfZ_exact_on hunit (fun n hn => ⟨l n, hval n hn⟩) hodd
    · intro n hn
      have hrate : rateBeta (famOf (fun _ => 0) b) n = b n :=
        ((regular_family_arbitrary_parameters (fun _ => 0) b).2 n (hunit n hn)).2
      rw [hrate, hval n hn]

/-! ## §50 — an explicit admissible domain with four different labels -/

/-- **NEUTRAL DEFINITION.**  An explicit linear rate. -/
noncomputable def linRate (n : Vec3) : ℝ := 5 / 2 * n.1

/-- **NEUTRAL DEFINITION.**  The explicit disconnected admissible domain: the unit
directions at which the linear rate is half-odd.  It contains isolated points, whole
circles, and antipodal pairs. -/
def multiD : Set Vec3 := {n : Vec3 | IsUnitAxis n ∧ IsHalfOdd (linRate n)}

/-- **NEUTRAL DEFINITION.**  An explicit rational unit direction. -/
noncomputable def p35 : Vec3 := (3 / 5, 4 / 5, 0)

theorem p35_isUnitAxis : IsUnitAxis p35 := by
  simp only [IsUnitAxis, h3, dot3, p35]
  norm_num

theorem continuous_linRate : Continuous fun s : Sph => linRate (s : Vec3) := by
  unfold linRate
  exact continuous_const.mul (continuous_fst.comp continuous_subtype_val)

theorem linRate_odd (n : Vec3) : linRate (-n) = -linRate n := by
  simp only [linRate, Prod.fst_neg]
  ring

/-- **PRINCIPAL THEOREM (§50).**  The antipodal-pair phenomenon of Task 17 is a special case
of a general one: there is an admissible domain of unit directions carrying **four**
different half-odd labels, containing antipodal pairs, and realized by one explicit exact
jointly regular representative. -/
theorem multiD_admissible_four_labels :
    IsAdmissibleDomain multiD ∧
      e1 ∈ multiD ∧ -e1 ∈ multiD ∧ p35 ∈ multiD ∧ -p35 ∈ multiD ∧
      ∃ U : Vec3 → ℝ → W, IsJointlyRegularFamily U ∧ IsTransformationValuedOn multiD U ∧
        rateBeta U e1 = 5 / 2 ∧ rateBeta U (-e1) = -(5 / 2) ∧
        rateBeta U p35 = 3 / 2 ∧ rateBeta U (-p35) = -(3 / 2) := by
  have hunit : UnitSet multiD := fun _ h => h.1
  have hhalf : ∀ n ∈ multiD, ∃ k : ℤ, linRate n = (k : ℝ) + 1 / 2 := fun n hn => hn.2
  have hodd : ∀ n ∈ multiD, -n ∈ multiD → linRate (-n) = -linRate n :=
    fun n _ _ => linRate_odd n
  have hjr : IsJointlyRegularFamily (famOf (fun _ => 0) linRate) :=
    jointlyRegular_famOf continuous_const continuous_linRate
  have hex : IsTransformationValuedOn multiD (famOf (fun _ => 0) linRate) :=
    famOfZ_exact_on hunit hhalf hodd
  have hrate : ∀ m : Vec3, IsUnitAxis m → rateBeta (famOf (fun _ => 0) linRate) m = linRate m :=
    fun m hm => ((regular_family_arbitrary_parameters (fun _ => 0) linRate).2 m hm).2
  have hne1 : IsUnitAxis (-e1) := isUnitAxis_neg e1_isUnitAxis
  have hnp35 : IsUnitAxis (-p35) := isUnitAxis_neg p35_isUnitAxis
  have he1v : linRate e1 = 5 / 2 := by simp [linRate, e1]
  have hne1v : linRate (-e1) = -(5 / 2) := by rw [linRate_odd, he1v]
  have hp35v : linRate p35 = 3 / 2 := by rw [linRate, p35]; norm_num
  have hnp35v : linRate (-p35) = -(3 / 2) := by rw [linRate_odd, hp35v]
  have m1 : e1 ∈ multiD := ⟨e1_isUnitAxis, 2, by rw [he1v]; norm_num⟩
  have m2 : -e1 ∈ multiD := ⟨hne1, -3, by rw [hne1v]; norm_num⟩
  have m3 : p35 ∈ multiD := ⟨p35_isUnitAxis, 1, by rw [hp35v]; norm_num⟩
  have m4 : -p35 ∈ multiD := ⟨hnp35, -2, by rw [hnp35v]; norm_num⟩
  exact ⟨⟨hunit, _, hjr, hex⟩, m1, m2, m3, m4,
    famOf (fun _ => 0) linRate, hjr, hex,
    by rw [hrate e1 e1_isUnitAxis, he1v],
    by rw [hrate (-e1) hne1, hne1v],
    by rw [hrate p35 p35_isUnitAxis, hp35v],
    by rw [hrate (-p35) hnp35, hnp35v]⟩

/-- **DERIVED (§50, §51).**  Consequently that domain is not preconnected: two of its
members carry different labels. -/
theorem multiD_not_preconnected : ¬ PreconnDomain multiD := by
  intro hpre
  obtain ⟨-, m1, -, m3, -, U, hU, hex, h1, -, h3', -⟩ := multiD_admissible_four_labels
  have := label_const_of_preconnected hU (fun _ h => h.1) hpre hex e1 m1 p35 m3
  rw [h1, h3'] at this
  norm_num at this

/-! ## §53 — labels cannot accumulate -/

/-- **PRINCIPAL THEOREM (§53).**  Around every unit direction the labels of an admissible
domain are locally constant: any two members of the domain close enough to a given
direction carry the same label.  Distinct labels can therefore not accumulate, however many
components the domain has. -/
theorem labels_locally_constant {D : Set Vec3} {b : Vec3 → ℝ}
    (hcont : Continuous fun s : Sph => b (s : Vec3))
    (hhalf : ∀ n ∈ D, IsHalfOdd (b n)) (p : Sph) :
    ∃ ε > 0, ∀ s t : Sph, (s : Vec3) ∈ D → (t : Vec3) ∈ D →
      dist s p < ε → dist t p < ε → b (s : Vec3) = b (t : Vec3) := by
  obtain ⟨ε, hε, hball⟩ := (Metric.continuous_iff.1 hcont) p (1 / 2) (by norm_num)
  refine ⟨ε, hε, fun s t hs ht hsp htp => ?_⟩
  have h1 : |b (s : Vec3) - b (p : Vec3)| < 1 / 2 := by
    have := hball s hsp
    rwa [Real.dist_eq] at this
  have h2 : |b (t : Vec3) - b (p : Vec3)| < 1 / 2 := by
    have := hball t htp
    rwa [Real.dist_eq] at this
  refine halfOdd_eq_of_close (hhalf _ hs) (hhalf _ ht) ?_
  have := abs_sub_abs_le_abs_sub (b (s : Vec3) - b (p : Vec3)) (b (t : Vec3) - b (p : Vec3))
  have hkey : |b (s : Vec3) - b (t : Vec3)|
      ≤ |b (s : Vec3) - b (p : Vec3)| + |b (t : Vec3) - b (p : Vec3)| := by
    have hrw : b (s : Vec3) - b (t : Vec3)
        = (b (s : Vec3) - b (p : Vec3)) - (b (t : Vec3) - b (p : Vec3)) := by ring
    rw [hrw]
    exact abs_sub _ _
  linarith

/-- **DERIVED (§53).**  Restated for an admissible domain: the labels realized by an exact
jointly regular representative are locally constant on the domain. -/
theorem admissible_labels_locally_constant {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    {D : Set Vec3} (hunit : UnitSet D) (hexact : IsTransformationValuedOn D U) (p : Sph) :
    ∃ ε > 0, ∀ s t : Sph, (s : Vec3) ∈ D → (t : Vec3) ∈ D →
      dist s p < ε → dist t p < ε → rateBeta U (s : Vec3) = rateBeta U (t : Vec3) := by
  obtain ⟨-, hhalf, hcont, -⟩ := admissible_necessary hU hunit hexact
  exact labels_locally_constant hcont (fun n hn => hhalf n hn) p

end NullSectorTask18
