import RequestProject.Experiment2.NullSectorTask19.MinimalObstruction

/-!
# Task 19, Package D: maximal preconnected admissible domains

The class is fixed once and for all (§33): sets of unit directions that are preconnected
and admissible, `PreconnAdmClass`.  Inside it, inclusion-maximality is analysed.

* §34, sufficiency.  Antipodal completeness implies maximality (inherited, restated as
  `antipodalComplete_maximal`).
* §35.  The empty domain is preconnected and admissible but **not** maximal, and every
  maximal member is nonempty.  The empty case is therefore settled explicitly and is not
  a counterexample to anything below.
* §34, necessity — the proved half.  Every maximal member is **closure-complete**: at every
  direction in the closure of `D`, either that direction or its reverse already lies in
  `D`.  The proof is intrinsic: a closure point can always be adjoined without destroying
  preconnectedness (a set squeezed between a preconnected set and its closure is
  preconnected) or antipodal-freeness.  Consequently `D ∪ (-D)` is **closed** and the
  missing set is **open**.
* §36, §37.  The remaining step — from closure-completeness to antipodal completeness — is
  isolated exactly.  It is proved *conditionally*, under one explicitly named hypothesis
  `AccessibleMissing D`: some preconnected antipodal-free part of the missing set has a
  given direction of `D` in its closure.  Without that hypothesis the argument stops at a
  precisely identified point, recorded in the audit as the unresolved obligation; no
  hemisphere or projective-space theorem is imported anywhere.
* §38.  The three maximality notions are separated by explicit witnesses:
  `lexA` is maximal preconnected admissible and maximal path-connected admissible but is
  **not open**; `Dom e1` is maximal *open* preconnected admissible but is **not** maximal
  preconnected admissible.
* §39, §40.  **Not** every maximal open preconnected admissible domain is an inherited
  domain `Dom v`.  A maximal one containing the Task-17 three-leg domain is produced, and
  that domain lies in no `Dom v`.  The maximality principle is applied only after chain
  closure has been established formally: unions of chains of open preconnected admissible
  domains containing a fixed one are again such domains.
-/

namespace NullSectorTask19

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18

instance : PreconnectedSpace Sph := ⟨sph_univ_isPreconnected⟩

/-! ## Bookkeeping -/

/-- **NEUTRAL DEFINITION (§38).**  Path-connected admissible sets of unit directions. -/
def PathConnAdmClass (D : Set Vec3) : Prop :=
  UnitSet D ∧ PathConnDomain D ∧ IsAdmissibleDomain D

theorem sphSet_singleton {n : Vec3} (hn : IsUnitAxis n) :
    sphSet ({n} : Set Vec3) = {(⟨n, hn⟩ : Sph)} := by
  ext s
  constructor
  · intro hs
    exact Subtype.ext hs
  · intro hs
    have : (s : Vec3) = n := congrArg Subtype.val hs
    exact this

theorem singleton_preconnAdm {n : Vec3} (hn : IsUnitAxis n) : PreconnAdmClass ({n} : Set Vec3) := by
  have hunit : UnitSet ({n} : Set Vec3) := by rintro m rfl; exact hn
  have hfree : AntipodalFree ({n} : Set Vec3) := by
    rintro m rfl hneg
    exact neg_ne_self_of_isUnitAxis hn hneg
  refine ⟨hunit, ?_, (antipodalFree_admissible hunit hfree).2⟩
  rw [PreconnDomain, sphSet_singleton hn]
  exact isPreconnected_singleton

/-! ## §34, sufficiency -/

/-- **PRINCIPAL THEOREM (§34), sufficiency.**  An antipodally complete preconnected
admissible set of unit directions is inclusion-maximal in its class. -/
theorem antipodalComplete_maximal {D : Set Vec3} (hD : PreconnAdmClass D)
    (hcomp : AntipodalComplete D) : IsMaximalIn PreconnAdmClass D :=
  maximal_preconnAdm_of_complete hD hcomp

/-! ## §35 — the empty case -/

/-- **PRINCIPAL THEOREM (§35).**  The empty domain lies in the class but is **not**
maximal in it. -/
theorem empty_not_maximal :
    PreconnAdmClass (∅ : Set Vec3) ∧ ¬ IsMaximalIn PreconnAdmClass (∅ : Set Vec3) := by
  refine ⟨⟨empty_unitSet, empty_preconn, empty_admissible⟩, ?_⟩
  rintro ⟨-, hmax⟩
  have h := hmax {e1} (singleton_preconnAdm e1_isUnitAxis) (Set.empty_subset _)
  have : e1 ∈ (∅ : Set Vec3) := by rw [← h]; rfl
  exact this

/-- **DERIVED (§35).**  Every maximal member of the class is nonempty. -/
theorem maximal_nonempty {D : Set Vec3} (hmax : IsMaximalIn PreconnAdmClass D) : D.Nonempty := by
  rcases Set.eq_empty_or_nonempty D with rfl | h
  · exact absurd hmax empty_not_maximal.2
  · exact h

/-! ## §34, necessity: closure-completeness -/

/-- **PRINCIPAL THEOREM (§34), necessity.**  A maximal preconnected admissible set is
*closure-complete*: every direction in its closure lies in it, or its reverse does.  The
proof adjoins a closure point, which preserves both preconnectedness and
antipodal-freeness. -/
theorem maximal_closureComplete {D : Set Vec3} (hmax : IsMaximalIn PreconnAdmClass D)
    {p : Sph} (hp : p ∈ closure (sphSet D)) : (p : Vec3) ∈ D ∨ -(p : Vec3) ∈ D := by
  obtain ⟨hunit, hpre, hadm⟩ := hmax.1
  have hfree : AntipodalFree D := antipodalFree_of_admissible_preconn hunit hpre hadm
  by_contra hcon
  push_neg at hcon
  obtain ⟨hpD, hpnD⟩ := hcon
  set E : Set Vec3 := D ∪ {(p : Vec3)} with hE
  have hunitE : UnitSet E := by
    rintro m (hm | hm)
    · exact hunit m hm
    · rw [Set.mem_singleton_iff] at hm; rw [hm]; exact p.2
  have hsub : sphSet D ⊆ sphSet E := fun s hs => Or.inl hs
  have hsubcl : sphSet E ⊆ closure (sphSet D) := by
    rintro s (hs | hs)
    · exact subset_closure hs
    · have : (s : Vec3) = (p : Vec3) := hs
      have hsp : s = p := Subtype.ext this
      rw [hsp]; exact hp
  have hpreE : PreconnDomain E := hpre.subset_closure hsub hsubcl
  have hfreeE : AntipodalFree E := by
    rintro m (hm | hm) hneg
    · rcases hneg with hneg | hneg
      · exact hfree m hm hneg
      · rw [Set.mem_singleton_iff] at hneg
        have : m = -(p : Vec3) := by rw [← hneg]; simp
        rw [this] at hm
        exact hpnD hm
    · rw [Set.mem_singleton_iff] at hm
      subst hm
      rcases hneg with hneg | hneg
      · exact hpnD hneg
      · rw [Set.mem_singleton_iff] at hneg
        exact neg_ne_self_of_isUnitAxis p.2 hneg
  have hEeq := hmax.2 E ⟨hunitE, hpreE, (antipodalFree_admissible hunitE hfreeE).2⟩
    Set.subset_union_left
  have : (p : Vec3) ∈ D := by
    rw [← hEeq]
    exact Set.mem_union_right _ rfl
  exact hpD this

/-! ## the missing set -/

/-- **NEUTRAL DEFINITION.**  The directions missed by a set together with their
reverses. -/
def MissingSet (D : Set Vec3) : Set Vec3 := {n : Vec3 | IsUnitAxis n ∧ n ∉ D ∧ -n ∉ D}

theorem missingSet_symm {D : Set Vec3} {n : Vec3} (h : n ∈ MissingSet D) :
    -n ∈ MissingSet D :=
  ⟨isUnitAxis_neg h.1, h.2.2, by rw [neg_neg]; exact h.2.1⟩

theorem sphSet_missingSet_compl (D : Set Vec3) :
    sphSet (MissingSet D) = (sphSet D ∪ sphSet (negSet D))ᶜ := by
  ext s
  constructor
  · rintro ⟨-, h1, h2⟩ (h | h)
    · exact h1 h
    · exact h2 h
  · intro hs
    refine ⟨s.2, fun h => hs (Or.inl h), fun h => hs (Or.inr h)⟩

/-- **PRINCIPAL THEOREM (§34), consequence.**  For a maximal member, the union of the
domain and its reverse is **closed**, hence the missing set is **open**. -/
theorem maximal_union_neg_isClosed {D : Set Vec3} (hmax : IsMaximalIn PreconnAdmClass D) :
    IsClosed (sphSet D ∪ sphSet (negSet D)) := by
  rw [← closure_subset_iff_isClosed, closure_union]
  rintro s (hs | hs)
  · rcases maximal_closureComplete hmax hs with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rw [closure_sphSet_negSet] at hs
    rcases maximal_closureComplete hmax hs with h | h
    · exact Or.inr h
    · refine Or.inl ?_
      have hrw : -((negSph s : Vec3)) = (s : Vec3) := neg_neg _
      rwa [hrw] at h

theorem maximal_missingSet_isOpen {D : Set Vec3} (hmax : IsMaximalIn PreconnAdmClass D) :
    IsOpen (sphSet (MissingSet D)) := by
  rw [sphSet_missingSet_compl]
  exact (maximal_union_neg_isClosed hmax).isOpen_compl

/-! ## §36, §37 — the conditional converse, with the missing hypothesis named -/

/-- **NEUTRAL DEFINITION (§37).**  The exact extra hypothesis that the proved part of the
argument leaves open: some preconnected antipodal-free part of the missing set accumulates
at a direction of `D`. -/
def AccessibleMissing (D : Set Vec3) : Prop :=
  ∀ q : Sph, (q : Vec3) ∈ D → q ∈ closure (sphSet (MissingSet D)) →
    ∃ A : Set Vec3, A ⊆ MissingSet D ∧ (sphSet A).Nonempty ∧ IsPreconnected (sphSet A) ∧
      AntipodalFree A ∧ q ∈ closure (sphSet A)

/-- **PRINCIPAL THEOREM (§36, §37), conditional.**  A maximal preconnected admissible set
whose missing set is accessible in the above sense is antipodally complete.  This is the
converse of `antipodalComplete_maximal`, proved **under one explicitly named additional
hypothesis**; the hypothesis is exactly the step the intrinsic argument does not supply. -/
theorem maximal_antipodalComplete_of_accessible {D : Set Vec3}
    (hmax : IsMaximalIn PreconnAdmClass D) (hacc : AccessibleMissing D) :
    AntipodalComplete D := by
  obtain ⟨hunit, hpre, hadm⟩ := hmax.1
  have hfree : AntipodalFree D := antipodalFree_of_admissible_preconn hunit hpre hadm
  by_contra hcon
  rw [AntipodalComplete] at hcon
  push_neg at hcon
  obtain ⟨n₀, hn₀u, hn₀D, hn₀nD⟩ := hcon
  -- the missing set is nonempty and open, the domain is nonempty
  have hMne : (sphSet (MissingSet D)).Nonempty := ⟨⟨n₀, hn₀u⟩, hn₀u, hn₀D, hn₀nD⟩
  obtain ⟨d₀, hd₀⟩ := maximal_nonempty hmax
  have hDne : (sphSet D).Nonempty := ⟨⟨d₀, hunit d₀ hd₀⟩, hd₀⟩
  -- the missing set is not closed
  have hnotclosed : ¬ IsClosed (sphSet (MissingSet D)) := by
    intro hclosed
    have hclopen : IsClopen (sphSet D ∪ sphSet (negSet D)) := by
      refine ⟨maximal_union_neg_isClosed hmax, ?_⟩
      have : sphSet D ∪ sphSet (negSet D) = (sphSet (MissingSet D))ᶜ := by
        rw [sphSet_missingSet_compl, compl_compl]
      rw [this]
      exact hclosed.isOpen_compl
    have huniv := hclopen.eq_univ ⟨hDne.choose, Or.inl hDne.choose_spec⟩
    obtain ⟨s, hs⟩ := hMne
    have : s ∈ (sphSet D ∪ sphSet (negSet D)) := by rw [huniv]; trivial
    rw [sphSet_missingSet_compl] at hs
    exact hs this
  -- so there is a closure point of the missing set outside it
  have hex : ∃ q : Sph, q ∈ closure (sphSet (MissingSet D)) ∧ q ∉ sphSet (MissingSet D) := by
    by_contra hc
    push_neg at hc
    exact hnotclosed (closure_subset_iff_isClosed.1 hc)
  obtain ⟨q₀, hq₀cl, hq₀out⟩ := hex
  -- the missing set is reversal-symmetric, so the closure point may be taken inside `D`
  have hMneg : negSet (MissingSet D) = MissingSet D := by
    ext m
    exact ⟨fun h => by simpa using missingSet_symm h, fun h => missingSet_symm h⟩
  have hclneg : ∀ s : Sph, s ∈ closure (sphSet (MissingSet D)) →
      negSph s ∈ closure (sphSet (MissingSet D)) := by
    intro s hs
    have : s ∈ closure (sphSet (negSet (MissingSet D))) := by rw [hMneg]; exact hs
    rw [closure_sphSet_negSet] at this
    exact this
  obtain ⟨q, hqD, hqcl⟩ : ∃ q : Sph, (q : Vec3) ∈ D ∧ q ∈ closure (sphSet (MissingSet D)) := by
    rw [sphSet_missingSet_compl] at hq₀out
    have hq₀in : q₀ ∈ sphSet D ∪ sphSet (negSet D) := not_not.1 hq₀out
    rcases hq₀in with h | h
    · exact ⟨q₀, h, hq₀cl⟩
    · exact ⟨negSph q₀, h, hclneg q₀ hq₀cl⟩
  obtain ⟨A, hAsub, hAne, hApre, hAfree, hAcl⟩ := hacc q hqD hqcl
  -- adjoin the accessible part
  set E : Set Vec3 := D ∪ A with hE
  have hunitE : UnitSet E := by
    rintro m (hm | hm)
    · exact hunit m hm
    · exact (hAsub hm).1
  have hqS : q ∈ sphSet D := hqD
  have hpreAq : IsPreconnected (sphSet A ∪ {q}) :=
    hApre.subset_closure Set.subset_union_left
      (Set.union_subset subset_closure (by simpa using hAcl))
  have hEeq : sphSet E = (sphSet A ∪ {q}) ∪ sphSet D := by
    rw [hE, sphSet_union]
    ext s
    constructor
    · rintro (hs | hs)
      · exact Or.inr hs
      · exact Or.inl (Or.inl hs)
    · rintro ((hs | hs) | hs)
      · exact Or.inr hs
      · rw [Set.mem_singleton_iff] at hs; rw [hs]; exact Or.inl hqS
      · exact Or.inl hs
  have hpreE : PreconnDomain E := by
    rw [PreconnDomain, hEeq]
    exact IsPreconnected.union q (Or.inr rfl) hqS hpreAq hpre
  have hfreeE : AntipodalFree E := by
    rintro m (hm | hm) hneg
    · rcases hneg with hneg | hneg
      · exact hfree m hm hneg
      · exact (hAsub hneg).2.2 (by rw [neg_neg]; exact hm)
    · rcases hneg with hneg | hneg
      · exact (hAsub hm).2.2 hneg
      · exact hAfree m hm hneg
  have hEq := hmax.2 E ⟨hunitE, hpreE, (antipodalFree_admissible hunitE hfreeE).2⟩
    Set.subset_union_left
  obtain ⟨a, ha⟩ := hAne
  have haE : (a : Vec3) ∈ E := Or.inr ha
  rw [hEq] at haE
  exact (hAsub ha).2.1 haE

/-! ## §38 — the three maximality notions -/

/-- **DERIVED (§38).**  `lexA` is maximal in the path-connected admissible class as well. -/
theorem lexA_maximal_pathConn : IsMaximalIn PathConnAdmClass lexA := by
  refine ⟨⟨lexA_unit, lexA_pathConn, lexA_admissible⟩, ?_⟩
  intro E hE hsub
  obtain ⟨hunitE, hpathE, hadmE⟩ := hE
  have hfreeE : AntipodalFree E :=
    antipodalFree_of_admissible_preconn hunitE hpathE.preconn hadmE
  refine Set.Subset.antisymm ?_ hsub
  intro n hn
  rcases lexA_complete (hunitE n hn) with h | h
  · exact h
  · exact absurd (hsub h) (hfreeE n hn)

/-- **DERIVED (§38).**  `lexA` is not open in the inherited subspace: it contains a
direction from which an explicit curve of unit directions leaves it immediately. -/
theorem lexA_not_open : ¬ OpenDomain lexA := by
  intro hopen
  have hne : ∀ t : ℝ, ((t, 1, 0) : Vec3) ≠ 0 := by
    intro t hcon
    have := congrArg (fun w : Vec3 => w.2.1) hcon
    norm_num at this
  set γ : ℝ → Vec3 := fun t => nrmz ((t, 1, 0) : Vec3) with hγ
  have hcont : Continuous γ := by
    refine continuousOn_univ.1 ?_
    exact continuousOn_nrmz_comp (by fun_prop) (fun t _ => hne t)
  have hunit : ∀ t : ℝ, IsUnitAxis (γ t) := fun t => nrmz_isUnitAxis (hne t)
  have h0 : γ 0 ∈ lexA := by
    refine ⟨hunit 0, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
    · show (nrmz ((0, 1, 0) : Vec3)).1 = 0
      rw [nrmz_fst]; norm_num
    · show 0 < (nrmz ((0, 1, 0) : Vec3)).2.1
      have hnrm : 0 < (nrm ((0, 1, 0) : Vec3))⁻¹ := inv_pos.2 (nrm_pos (hne 0))
      show 0 < (nrm ((0, 1, 0) : Vec3))⁻¹ * 1
      linarith
  obtain ⟨δ, hδ, hball⟩ := open_curve_nearby hopen hcont hunit h0
  have ht : |(-(δ / 2))| < δ := by
    rw [abs_of_neg (by linarith)]; linarith
  have hmem : γ (-(δ / 2)) ∈ lexA := hball _ ht
  have hfst : (γ (-(δ / 2))).1 < 0 := by
    show (nrm ((-(δ / 2), 1, 0) : Vec3))⁻¹ * (-(δ / 2)) < 0
    have hnrm : 0 < (nrm ((-(δ / 2), 1, 0) : Vec3))⁻¹ := inv_pos.2 (nrm_pos (hne _))
    nlinarith
  exact absurd (lexA_fst_nonneg hmem) (not_le.2 hfst)

/-- **DERIVED (§38).**  `Dom e1` is not maximal in the preconnected admissible class:
`lexA` is a strictly larger member. -/
theorem Dom_e1_not_maximal_preconn : ¬ IsMaximalIn PreconnAdmClass (Dom e1) := by
  rintro ⟨-, hmax⟩
  have hy : ((0, 1, 0) : Vec3) ∈ lexA := by
    refine ⟨by simp [IsUnitAxis, h3, dot3], Or.inr (Or.inl ⟨rfl, by norm_num⟩)⟩
  have h := hmax lexA lexA_preconnAdm Dom_e1_subset_lexA
  rw [h] at hy
  have := (mem_Dom_e1.1 hy).2
  norm_num at this

/-- **PRINCIPAL THEOREM (§38).**  The three maximality notions are genuinely different. -/
theorem three_maximality_notions_differ :
    IsMaximalIn PreconnAdmClass lexA ∧ IsMaximalIn PathConnAdmClass lexA ∧
      ¬ OpenDomain lexA ∧ IsMaximalIn OpenConnAdmClass (Dom e1) ∧
      ¬ IsMaximalIn PreconnAdmClass (Dom e1) :=
  ⟨lexA_maximal, lexA_maximal_pathConn, lexA_not_open, Dom_maximal_openConnAdm e1_ne_zero,
    Dom_e1_not_maximal_preconn⟩

/-! ## §39, §40 — maximal open preconnected admissible domains beyond the inherited ones -/

theorem sphSet_sUnion (c : Set (Set Vec3)) : sphSet (⋃₀ c) = ⋃₀ (sphSet '' c) := by
  ext s
  constructor
  · rintro ⟨E, hE, hs⟩
    exact ⟨sphSet E, ⟨E, hE, rfl⟩, hs⟩
  · rintro ⟨T, ⟨E, hE, rfl⟩, hs⟩
    exact ⟨E, hE, hs⟩

/-- **DERIVED (§39), chain closure.**  Unions of chains of open preconnected admissible
domains containing the Task-17 three-leg domain are again such domains.  This is
established **before** any maximality principle is invoked. -/
theorem chain_union_openConnAdm {c : Set (Set Vec3)}
    (hsub : c ⊆ {E : Set Vec3 | OpenConnAdmClass E ∧ YDom ⊆ E}) (hchain : IsChain (· ⊆ ·) c)
    (hne : c.Nonempty) : OpenConnAdmClass (⋃₀ c) ∧ YDom ⊆ ⋃₀ c := by
  have hmem : ∀ E ∈ c, OpenConnAdmClass E ∧ YDom ⊆ E := fun E hE => hsub hE
  have hYsub : YDom ⊆ ⋃₀ c := by
    obtain ⟨E, hE⟩ := hne
    exact fun n hn => ⟨E, hE, (hmem E hE).2 hn⟩
  have hunit : UnitSet (⋃₀ c) := by
    rintro n ⟨E, hE, hn⟩
    exact (hmem E hE).1.1 n hn
  have hopen : OpenDomain (⋃₀ c) := by
    rw [OpenDomain, sphSet_sUnion]
    refine isOpen_sUnion ?_
    rintro T ⟨E, hE, rfl⟩
    exact (hmem E hE).1.2.1
  have hpre : PreconnDomain (⋃₀ c) := by
    have hpt : ∀ T ∈ sphSet '' c, (⟨eThree, eThree_isUnitAxis⟩ : Sph) ∈ T := by
      rintro T ⟨E, hE, rfl⟩
      exact (hmem E hE).2 eThree_mem_YDom
    have hprec : ∀ T ∈ sphSet '' c, IsPreconnected T := by
      rintro T ⟨E, hE, rfl⟩
      exact (hmem E hE).1.2.2.1
    rw [PreconnDomain, sphSet_sUnion]
    exact isPreconnected_sUnion _ _ hpt hprec
  have hfree : AntipodalFree (⋃₀ c) := by
    rintro n ⟨E, hE, hn⟩ ⟨F, hF, hnF⟩
    have hfreeE : AntipodalFree E := antipodalFree_of_admissible_preconn (hmem E hE).1.1
      (hmem E hE).1.2.2.1 (hmem E hE).1.2.2.2
    have hfreeF : AntipodalFree F := antipodalFree_of_admissible_preconn (hmem F hF).1.1
      (hmem F hF).1.2.2.1 (hmem F hF).1.2.2.2
    by_cases hEF : E = F
    · subst hEF
      exact hfreeE n hn hnF
    · rcases hchain hE hF hEF with h | h
      · exact hfreeF n (h hn) hnF
      · exact hfreeE n hn (h hnF)
  exact ⟨⟨hunit, hopen, hpre, (antipodalFree_admissible hunit hfree).2⟩, hYsub⟩

/-- **PRINCIPAL THEOREM (§39, §40): REFUTATION.**  **Not** every maximal open preconnected
admissible domain is an inherited domain `Dom v`.  There is a maximal one containing the
Task-17 three-leg domain, and no `Dom v` contains that domain. -/
theorem exists_maximal_openConnAdm_not_Dom :
    ∃ E : Set Vec3, IsMaximalIn OpenConnAdmClass E ∧ YDom ⊆ E ∧ ∀ v : Vec3, E ≠ Dom v := by
  set S : Set (Set Vec3) := {E : Set Vec3 | OpenConnAdmClass E ∧ YDom ⊆ E} with hS
  have hYmem : YDom ∈ S :=
    ⟨⟨YDom_unit, YDom_open, YDom_pathConnected.isConnected.isPreconnected, YDom_admissible⟩,
      subset_rfl⟩
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hc hcne
    exact ⟨⋃₀ c, chain_union_openConnAdm hcS hc hcne, fun s hs n hn => ⟨s, hs, hn⟩⟩
  obtain ⟨E, hYE, hEmax⟩ := zorn_subset_nonempty S hchain YDom hYmem
  refine ⟨E, ⟨hEmax.1.1, ?_⟩, hYE, ?_⟩
  · intro F hF hEF
    have hFS : F ∈ S := ⟨hF, hYE.trans hEF⟩
    exact Set.Subset.antisymm (hEmax.2 hFS hEF) hEF
  · intro v hcon
    have : YDom ⊆ Dom v := by rw [← hcon]; exact hYE
    exact YDom_not_subset_Dom v this

end NullSectorTask19
