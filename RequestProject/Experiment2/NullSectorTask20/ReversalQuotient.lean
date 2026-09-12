import RequestProject.Experiment2.NullSectorTask20.BridgeTorsor

/-!
# Task 20, Layer 5 (Package F): the reversal involution, its quotient, and selectors

Phase A only.  Reversal of a unit direction is treated as an intrinsic involution; its orbit
relation and quotient are constructed and given **no** conventional name.  The Task-XIX
domain properties are then translated into exact fibre statements for this quotient, and the
inherited classification of inclusion-maximal admissible domains is re-read as: *exactly one
representative in every fibre, plus density*.  The two ingredients are kept apart:

* "one representative in every fibre" is a statement about the involution quotient alone,
  proved here with no continuity and no rate;
* density is the ingredient that is **not** about the quotient; it enters through the
  inherited rigidity of a continuous rate, and is imported as such.

Nonuniqueness is preserved: two different maximal selectors are exhibited together with the
datum that distinguishes them (the fibre at which they choose differently).
-/

namespace NullSectorTask20

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19

/-! ## The involution and its orbit relation -/

/-- **NEUTRAL DEFINITION (item 52).**  The orbit relation of the reversal involution. -/
def revRel (s t : Sph) : Prop := t = s ∨ t = negSph s

theorem revRel_refl (s : Sph) : revRel s s := Or.inl rfl

theorem revRel_symm {s t : Sph} (h : revRel s t) : revRel t s := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h]; exact (negSph_involutive s).symm)

theorem revRel_trans {s t u : Sph} (h : revRel s t) (h' : revRel t u) : revRel s u := by
  rcases h with h | h
  · rcases h' with h' | h'
    · exact Or.inl (h'.trans h)
    · exact Or.inr (by rw [h', h])
  · rcases h' with h' | h'
    · exact Or.inr (h'.trans h)
    · exact Or.inl (by rw [h', h]; exact negSph_involutive s)

/-- **NEUTRAL DEFINITION (item 53).**  The orbit setoid of the reversal involution. -/
def revSetoid : Setoid Sph where
  r := revRel
  iseqv := ⟨revRel_refl, revRel_symm, revRel_trans⟩

/-- **NEUTRAL DEFINITION (item 53).**  The orbit quotient of the reversal involution.  No
conventional name is attached to it in Phase A. -/
def RevQuot : Type := Quotient revSetoid

/-- The orbit projection. -/
def revClass (s : Sph) : RevQuot := Quotient.mk revSetoid s

theorem revClass_eq_iff {s t : Sph} : revClass s = revClass t ↔ (t = s ∨ t = negSph s) :=
  Quotient.eq (r := revSetoid)

theorem revClass_surjective : Function.Surjective revClass := Quotient.mk_surjective

theorem revClass_negSph (s : Sph) : revClass (negSph s) = revClass s :=
  revClass_eq_iff.2 (Or.inr (negSph_involutive s).symm)

/-! ## Item 54 — the Task-XIX domain properties as fibre statements -/

/-- **PACKAGE F (item 54a).**  Antipodal freedom is exactly: every fibre of the orbit
quotient contains **at most one** direction of the domain. -/
theorem antipodalFree_iff_fibre_subsingleton {D : Set Vec3} (hunit : UnitSet D) :
    AntipodalFree D ↔
      ∀ s t : Sph, (s : Vec3) ∈ D → (t : Vec3) ∈ D → revClass s = revClass t → s = t := by
  constructor
  · intro hfree s t hs ht hcl
    rcases revClass_eq_iff.1 hcl with rfl | rfl
    · rfl
    · exact absurd (by simpa [negSph] using ht) (hfree (s : Vec3) hs)
  · intro hsub n hn hneg
    have hnu : IsUnitAxis n := hunit n hn
    have hnegu : IsUnitAxis (-n) := isUnitAxis_neg hnu
    have := hsub ⟨n, hnu⟩ ⟨-n, hnegu⟩ hn hneg (revClass_eq_iff.2 (Or.inr (Subtype.ext rfl)))
    have hcoord : n = -n := congrArg Subtype.val this
    have h0 : n = 0 := by
      have : (2 : ℝ) • n = 0 := by
        rw [two_smul]
        nth_rewrite 2 [hcoord]
        simp
      have h2 := congrArg (fun v : Vec3 => (2 : ℝ)⁻¹ • v) this
      simpa using h2
    exact isUnitAxis_ne_zero hnu h0

/-- **PACKAGE F (item 54b).**  Antipodal completeness is exactly: every fibre of the orbit
quotient contains **at least one** direction of the domain. -/
theorem antipodalComplete_iff_fibre_nonempty {D : Set Vec3} :
    AntipodalComplete D ↔ ∀ c : RevQuot, ∃ s : Sph, (s : Vec3) ∈ D ∧ revClass s = c := by
  constructor
  · intro hcomp c
    obtain ⟨t, rfl⟩ := revClass_surjective c
    rcases hcomp (t : Vec3) t.2 with h | h
    · exact ⟨t, h, rfl⟩
    · exact ⟨negSph t, h, revClass_negSph t⟩
  · intro hfib n hn
    obtain ⟨s, hsD, hs⟩ := hfib (revClass ⟨n, hn⟩)
    rcases revClass_eq_iff.1 hs with h | h
    · refine Or.inl ?_
      have hval : (s : Vec3) = n := (congrArg Subtype.val h).symm
      rwa [hval] at hsD
    · refine Or.inr ?_
      have hval : (s : Vec3) = -n := by
        have h2 : n = -(s : Vec3) := congrArg Subtype.val h
        rw [h2, neg_neg]
      rwa [hval] at hsD

/-- **PACKAGE F (item 54c), principal.**  Both properties together are exactly the statement
that the domain meets every fibre in exactly one direction: it is a *selector* for the orbit
quotient.  Purely a statement about the involution: no continuity, no rate. -/
theorem selector_iff {D : Set Vec3} (hunit : UnitSet D) :
    (AntipodalFree D ∧ AntipodalComplete D) ↔
      ∀ c : RevQuot, ∃! s : Sph, (s : Vec3) ∈ D ∧ revClass s = c := by
  constructor
  · rintro ⟨hfree, hcomp⟩ c
    obtain ⟨s, hsD, hs⟩ := (antipodalComplete_iff_fibre_nonempty).1 hcomp c
    refine ⟨s, ⟨hsD, hs⟩, ?_⟩
    rintro t ⟨htD, ht⟩
    exact (antipodalFree_iff_fibre_subsingleton hunit).1 hfree t s htD hsD (by rw [ht, hs])
  · intro hsel
    constructor
    · refine (antipodalFree_iff_fibre_subsingleton hunit).2 ?_
      intro s t hs ht hcl
      obtain ⟨u, -, huniq⟩ := hsel (revClass s)
      rw [huniq s ⟨hs, rfl⟩, huniq t ⟨ht, hcl.symm⟩]
    · refine (antipodalComplete_iff_fibre_nonempty).2 ?_
      intro c
      obtain ⟨s, ⟨hsD, hs⟩, -⟩ := hsel c
      exact ⟨s, hsD, hs⟩

/-- **PACKAGE F (item 55), principal.**  The inherited classification of inclusion-maximal
admissible domains, re-expressed purely in terms of the orbit quotient plus the ambient
condition: a set of unit directions is inclusion-maximal admissible **iff** it is a selector
for the orbit quotient and dense.  The selector half is the involution quotient; the density
half is the ambient extension condition. -/
theorem maximal_iff_dense_selector {D : Set Vec3} (hunit : UnitSet D) :
    IsMaximalIn AdmClass D ↔
      ((∀ c : RevQuot, ∃! s : Sph, (s : Vec3) ∈ D ∧ revClass s = c) ∧ DenseDom D) := by
  rw [maximal_adm_iff hunit]
  constructor
  · rintro ⟨hdense, hcomp, hfree⟩
    exact ⟨(selector_iff hunit).1 ⟨hfree, hcomp⟩, hdense⟩
  · rintro ⟨hsel, hdense⟩
    obtain ⟨hfree, hcomp⟩ := (selector_iff hunit).2 hsel
    exact ⟨hdense, hcomp, hfree⟩

/-! ## Item 58 — nonuniqueness, and the datum which distinguishes two maximal selectors -/

/-- **PACKAGE F (item 58), principal.**  Two different inclusion-maximal admissible selectors
exist, and the datum distinguishing them is exactly the fibre at which they choose the other
representative: the reversed selector chooses `-n` in every fibre where the original chooses
`n`. -/
theorem maximal_selectors_not_unique :
    ∃ D E : Set Vec3, IsMaximalIn AdmClass D ∧ IsMaximalIn AdmClass E ∧ D ≠ E ∧
      E = negSet D ∧ ∃ n : Vec3, IsUnitAxis n ∧ (n ∈ D ↔ n ∉ E) := by
  refine ⟨flipSet, negSet flipSet, exists_maximal_adm,
    negSet_maximal_adm flipSet_unit exists_maximal_adm, ?_, rfl, ?_⟩
  · intro hcon
    rcases flipSet_exactly_one e1_isUnitAxis with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : e1 ∈ negSet flipSet := by rw [← hcon]; exact h1
      exact h2 this
    · have : (-e1) ∈ negSet flipSet := by rw [← hcon]; exact h2
      rw [mem_negSet, neg_neg] at this
      exact h1 this
  · refine ⟨e1, e1_isUnitAxis, ?_⟩
    rcases flipSet_exactly_one e1_isUnitAxis with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun _ => fun hmem => h2 hmem, fun _ => h1⟩
    · constructor
      · intro hmem; exact absurd hmem h1
      · intro hmem
        exact absurd (show e1 ∈ negSet flipSet from h2) hmem

end NullSectorTask20
