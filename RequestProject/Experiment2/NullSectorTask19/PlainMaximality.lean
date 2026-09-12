import RequestProject.Experiment2.NullSectorTask19.MaximalPreconnected

/-!
# Task 19, Package E: maximality in the plain admissible class

No connectedness and no openness is assumed anywhere in this module (§42).

* §44, §45.  **Chain unions of admissible sets need not be admissible.**  An explicit
  increasing chain of admissible domains — the closed "bands" `|n.1| ≥ 1/(k+1)`, each
  carrying an explicit continuous clamped rate — has as its union the set of unit
  directions with nonvanishing first coordinate, which is **not** admissible.  The failure
  mechanism is exactly the one named in §45: the union is dense, so any ambient continuous
  rate is half-odd everywhere, hence constant; and a constant rate cannot satisfy the
  reversal constraint, which the union does impose because it contains whole antipodal
  pairs.  Consequently **no maximality principle may be invoked** for this class, and none
  is.
* §42, §46, §47.  Maximal members are nevertheless classified **exactly**, with no
  maximality principle: a set of unit directions is inclusion-maximal admissible **iff** it
  is antipodal-free, antipodally complete, and dense.  Both directions are proved.  The
  "adjoin one direction" step uses only the inherited criterion and an ambient separation
  function.
* §42, existence.  A set with those three properties is **constructed explicitly**: the
  lexicographic half-space with its choice reversed exactly at the directions whose
  third-to-first coordinate ratio is rational.  Both the reversed and the unreversed part
  are dense, so the whole set is dense while still containing exactly one direction of
  every antipodal pair.
* §47, §48.  Existence, uniqueness and canonicality are kept apart: maximal admissible
  sets exist, they are **not unique** (the reversed set of a maximal admissible set is a
  different maximal admissible set), and nothing selects one — canonicality is **not**
  inferred from existence.
-/

namespace NullSectorTask19

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18

/-! ## Bookkeeping -/

/-- **NEUTRAL DEFINITION.**  Density of a set of unit directions inside the inherited
subspace. -/
def DenseDom (D : Set Vec3) : Prop := ∀ p : Sph, p ∈ closure (sphSet D)

theorem isHalfOdd_neg {x : ℝ} (h : IsHalfOdd x) : IsHalfOdd (-x) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨-k - 1, by rw [hk]; push_cast; ring⟩

/-- **DERIVED.**  Admissibility is inherited by subsets. -/
theorem admissible_mono {D E : Set Vec3} (hsub : D ⊆ E) (hE : IsAdmissibleDomain E) :
    IsAdmissibleDomain D := by
  obtain ⟨hunit, U, hU, hexact⟩ := hE
  exact ⟨fun n hn => hunit n (hsub hn), U, hU, transformationValuedOn_mono hsub hexact⟩

/-- **DERIVED.**  A parameterized curve of unit directions passing through a direction and
meeting a set arbitrarily close to the parameter value puts that direction in the closure
of the set. -/
theorem mem_closure_of_param' {m : Vec3} (hm : IsUnitAxis m) {T : Set Sph} {u₀ : ℝ}
    {g : ℝ → Vec3} (hg : Continuous g) (hunit : ∀ u : ℝ, IsUnitAxis (g u)) (h0 : g u₀ = m)
    (hmeet : ∀ ε > 0, ∃ u : ℝ, |u - u₀| < ε ∧ (⟨g u, hunit u⟩ : Sph) ∈ T) :
    (⟨m, hm⟩ : Sph) ∈ closure T := by
  have hG : Continuous fun u : ℝ => (⟨g u, hunit u⟩ : Sph) := hg.subtype_mk _
  refine Metric.mem_closure_iff.2 ?_
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hG u₀ ε hε
  obtain ⟨u, hu, huS⟩ := hmeet δ hδ
  refine ⟨⟨g u, hunit u⟩, huS, ?_⟩
  have hdu : dist u u₀ < δ := by rwa [Real.dist_eq]
  have := hball u hdu
  have hpt : (⟨g u₀, hunit u₀⟩ : Sph) = (⟨m, hm⟩ : Sph) := Subtype.ext h0
  rwa [hpt, dist_comm] at this

theorem mem_closure_of_param {m : Vec3} (hm : IsUnitAxis m) {S : Set Vec3} {u₀ : ℝ}
    {g : ℝ → Vec3} (hg : Continuous g) (hunit : ∀ u : ℝ, IsUnitAxis (g u)) (h0 : g u₀ = m)
    (hmeet : ∀ ε > 0, ∃ u : ℝ, |u - u₀| < ε ∧ g u ∈ S) :
    (⟨m, hm⟩ : Sph) ∈ closure (sphSet S) :=
  mem_closure_of_param' hm hg hunit h0 hmeet

/-! ## §46 — adjoining one direction -/

/-- **DERIVED (§46).**  An ambient continuous separating function, transported to a
function of the direction. -/
noncomputable def sepFun (f : C(Sph, ℝ)) (n : Vec3) : ℝ :=
  open Classical in if h : IsUnitAxis n then f ⟨n, h⟩ else 0

theorem sepFun_apply (f : C(Sph, ℝ)) (s : Sph) : sepFun f (s : Vec3) = f s := by
  rw [sepFun, dif_pos s.2]

theorem continuous_sepFun (f : C(Sph, ℝ)) : Continuous fun s : Sph => sepFun f (s : Vec3) := by
  have he : (fun s : Sph => sepFun f (s : Vec3)) = fun s : Sph => f s := funext (sepFun_apply f)
  rw [he]
  exact f.continuous

/-- **PRINCIPAL THEOREM (§46).**  An admissible set of unit directions stays admissible
after adjoining one direction which is **not** in the closure of the set.  The rate is
modified only away from the closure; the retained data are the same. -/
theorem adm_add_point_of_not_closure {D : Set Vec3} (hunit : UnitSet D)
    (hadm : IsAdmissibleDomain D) {p : Vec3} (hp : IsUnitAxis p)
    (hpc : (⟨p, hp⟩ : Sph) ∉ closure (sphSet D)) :
    IsAdmissibleDomain (D ∪ {p}) := by
  classical
  obtain ⟨b, hbcont, hbhalf, hbodd⟩ := (admissible_iff_exists_rate_function hunit).1 hadm
  have hunitE : UnitSet (D ∪ {p}) := by
    rintro m (hm | hm)
    · exact hunit m hm
    · rw [Set.mem_singleton_iff] at hm; rw [hm]; exact hp
  -- the target value at the new direction
  set t : ℝ := if -p ∈ D then -b (-p) else 1 / 2 with ht
  have hthalf : IsHalfOdd t := by
    rw [ht]
    by_cases h : -p ∈ D
    · rw [if_pos h]
      exact isHalfOdd_neg (hbhalf (-p) h)
    · rw [if_neg h]
      exact ⟨0, by norm_num⟩
  -- an ambient separation function
  obtain ⟨f, hf0, hf1, -⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_closure (s := sphSet D))
    (isClosed_singleton (X := Sph) (x := (⟨p, hp⟩ : Sph)))
    (Set.disjoint_singleton_right.2 hpc)
  set F : Vec3 → ℝ := sepFun f with hF
  have hFD : ∀ n ∈ D, F n = 0 := by
    intro n hn
    have hs : (⟨n, hunit n hn⟩ : Sph) ∈ closure (sphSet D) := subset_closure hn
    have h1 : F n = f ⟨n, hunit n hn⟩ := sepFun_apply f ⟨n, hunit n hn⟩
    rw [h1]
    simpa using hf0 hs
  have hFp : F p = 1 := by
    have h1 : F p = f ⟨p, hp⟩ := sepFun_apply f ⟨p, hp⟩
    rw [h1]
    simpa using hf1 (Set.mem_singleton (⟨p, hp⟩ : Sph))
  set b' : Vec3 → ℝ := fun n => b n + (t - b p) * F n with hb'
  have hb'D : ∀ n ∈ D, b' n = b n := by
    intro n hn
    show b n + (t - b p) * F n = b n
    rw [hFD n hn]; ring
  have hb'p : b' p = t := by
    show b p + (t - b p) * F p = t
    rw [hFp]; ring
  refine (admissible_iff_exists_rate_function hunitE).2 ⟨b', ?_, ?_, ?_⟩
  · have hFcont : Continuous fun s : Sph => F (s : Vec3) := continuous_sepFun f
    exact hbcont.add (continuous_const.mul hFcont)
  · rintro n (hn | hn)
    · rw [hb'D n hn]; exact hbhalf n hn
    · rw [Set.mem_singleton_iff] at hn
      rw [hn, hb'p]; exact hthalf
  · rintro n (hn | hn) hneg
    · rcases hneg with hneg | hneg
      · rw [hb'D n hn, hb'D (-n) hneg]; exact hbodd n hn hneg
      · rw [Set.mem_singleton_iff] at hneg
        -- `-n = p`, so `n = -p ∈ D`
        have hnp : n = -p := by rw [← hneg]; simp
        have hpD : -p ∈ D := by rw [← hnp]; exact hn
        rw [hneg, hb'p, hb'D n hn, ht, if_pos hpD, hnp]
    · rw [Set.mem_singleton_iff] at hn
      rcases hneg with hneg | hneg
      · rw [hn] at hneg ⊢
        rw [hb'p, hb'D (-p) hneg, ht, if_pos hneg]; ring
      · rw [Set.mem_singleton_iff] at hneg
        rw [hn] at hneg
        exact absurd hneg (neg_ne_self_of_isUnitAxis hp)

/-! ## §42 — the exact classification of maximal admissible sets -/

/-- **DERIVED.**  A dense admissible set forces every ambient rate to be constant. -/
theorem rate_const_of_dense {D : Set Vec3} {b : Vec3 → ℝ} (hcont : RateCont b)
    (hhalf : ∀ n ∈ D, IsHalfOdd (b n)) (hdense : DenseDom D) {n m : Vec3}
    (hn : IsUnitAxis n) (hm : IsUnitAxis m) : b n = b m := by
  have hall : ∀ k : Vec3, IsUnitAxis k → IsHalfOdd (b k) := by
    intro k hk
    exact halfOdd_of_mem_closure hcont hhalf (p := ⟨k, hk⟩) (hdense ⟨k, hk⟩)
  exact halfOdd_const_on_sph hcont hall hn hm

/-- **PRINCIPAL THEOREM (§42), necessity.**  A maximal admissible set is dense,
antipodally complete and antipodal-free. -/
theorem maximal_adm_necessary {D : Set Vec3} (hmax : IsMaximalIn AdmClass D) :
    DenseDom D ∧ AntipodalComplete D ∧ AntipodalFree D := by
  obtain ⟨hunit, hadm⟩ := hmax.1
  -- density
  have hdense : DenseDom D := by
    intro p
    by_contra hpc
    have hadmE : IsAdmissibleDomain (D ∪ {(p : Vec3)}) :=
      adm_add_point_of_not_closure hunit hadm p.2 hpc
    have hunitE : UnitSet (D ∪ {(p : Vec3)}) := hadmE.1
    have hEq := hmax.2 (D ∪ {(p : Vec3)}) ⟨hunitE, hadmE⟩ Set.subset_union_left
    have hpD : (p : Vec3) ∈ D := by rw [← hEq]; exact Set.mem_union_right _ rfl
    exact hpc (subset_closure hpD)
  have hDne : D.Nonempty := by
    rcases Set.eq_empty_or_nonempty D with hemp | h
    · exfalso
      have hcl := hdense ⟨e1, e1_isUnitAxis⟩
      have h0 : sphSet D = (∅ : Set Sph) := by rw [hemp]; ext s; simp [sphSet]
      rw [h0, closure_empty] at hcl
      exact hcl
    · exact h
  -- the ambient rate is constant
  obtain ⟨b, hbcont, hbhalf, hbodd⟩ := (admissible_iff_exists_rate_function hunit).1 hadm
  have hconst : ∀ n m : Vec3, IsUnitAxis n → IsUnitAxis m → b n = b m := by
    intro n m hn hm
    exact rate_const_of_dense hbcont (fun k hk => hbhalf k hk) hdense hn hm
  -- antipodal-freeness
  have hfree : AntipodalFree D := by
    intro n hn hneg
    have hb1 : b (-n) = -b n := hbodd n hn hneg
    have hb2 : b (-n) = b n := hconst _ _ (isUnitAxis_neg (hunit n hn)) (hunit n hn)
    have hz : b n = 0 := by linarith
    obtain ⟨k, hk⟩ := hbhalf n hn
    rw [hz] at hk
    have h2 : (2 * k : ℤ) = -1 := by
      have : (2 * (k : ℝ)) = -1 := by linarith
      exact_mod_cast this
    omega
  -- antipodal completeness
  refine ⟨hdense, ?_, hfree⟩
  intro n hn
  by_contra hcon
  push_neg at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  have hunitE : UnitSet (D ∪ {n}) := by
    rintro m (hm | hm)
    · exact hunit m hm
    · rw [Set.mem_singleton_iff] at hm; rw [hm]; exact hn
  have hadmE : IsAdmissibleDomain (D ∪ {n}) := by
    refine (admissible_iff_exists_rate_function hunitE).2 ⟨b, hbcont, ?_, ?_⟩
    · rintro m (hm | hm)
      · exact hbhalf m hm
      · rw [Set.mem_singleton_iff] at hm
        obtain ⟨d, hd⟩ := hDne
        rw [hm, hconst n d hn (hunit d hd)]
        exact hbhalf d hd
    · rintro m (hm | hm) hneg
      · rcases hneg with hneg | hneg
        · exact hbodd m hm hneg
        · rw [Set.mem_singleton_iff] at hneg
          have hmn : m = -n := by rw [← hneg]; simp
          rw [hmn] at hm
          exact absurd hm hn2
      · rw [Set.mem_singleton_iff] at hm
        subst hm
        rcases hneg with hneg | hneg
        · exact absurd hneg hn2
        · rw [Set.mem_singleton_iff] at hneg
          exact absurd hneg (neg_ne_self_of_isUnitAxis hn)
  have hEq := hmax.2 (D ∪ {n}) ⟨hunitE, hadmE⟩ Set.subset_union_left
  have : n ∈ D := by rw [← hEq]; exact Set.mem_union_right _ rfl
  exact hn1 this

/-- **PRINCIPAL THEOREM (§42), sufficiency.**  A dense, antipodally complete,
antipodal-free set of unit directions is inclusion-maximal admissible. -/
theorem maximal_adm_sufficient {D : Set Vec3} (hunit : UnitSet D) (hdense : DenseDom D)
    (hcomp : AntipodalComplete D) (hfree : AntipodalFree D) : IsMaximalIn AdmClass D := by
  refine ⟨⟨hunit, (antipodalFree_admissible hunit hfree).2⟩, ?_⟩
  rintro E ⟨hunitE, hadmE⟩ hsub
  refine Set.Subset.antisymm ?_ hsub
  intro n hn
  by_contra hnD
  -- `-n ∈ D ⊆ E`, so `E` contains a whole antipodal pair
  have hnegD : -n ∈ D := by
    rcases hcomp n (hunitE n hn) with h | h
    · exact absurd h hnD
    · exact h
  have hnegE : -n ∈ E := hsub hnegD
  obtain ⟨b, hbcont, hbhalf, hbodd⟩ := (admissible_iff_exists_rate_function hunitE).1 hadmE
  have hconst : ∀ k m : Vec3, IsUnitAxis k → IsUnitAxis m → b k = b m := by
    intro k m hk hm
    exact rate_const_of_dense hbcont (fun j hj => hbhalf j (hsub hj)) hdense hk hm
  have hb1 : b (-n) = -b n := hbodd n hn hnegE
  have hb2 : b (-n) = b n :=
    hconst _ _ (isUnitAxis_neg (hunitE n hn)) (hunitE n hn)
  have hz : b n = 0 := by linarith
  obtain ⟨k, hk⟩ := hbhalf n hn
  rw [hz] at hk
  have h2 : (2 * k : ℤ) = -1 := by
    have : (2 * (k : ℝ)) = -1 := by linarith
    exact_mod_cast this
  omega

/-- **PRINCIPAL THEOREM (§42).**  *Equivalence.*  A set of unit directions is
inclusion-maximal admissible **iff** it is dense, antipodally complete and
antipodal-free. -/
theorem maximal_adm_iff {D : Set Vec3} (hunit : UnitSet D) :
    IsMaximalIn AdmClass D ↔ (DenseDom D ∧ AntipodalComplete D ∧ AntipodalFree D) :=
  ⟨maximal_adm_necessary, fun h => maximal_adm_sufficient hunit h.1 h.2.1 h.2.2⟩

/-! ## §44, §45 — chain unions are not admissible -/

/-- **NEUTRAL DEFINITION (§44).**  The explicit increasing chain: the directions whose
first coordinate is at least `1/(k+1)` in absolute value. -/
def bandSet (k : ℕ) : Set Vec3 := {n : Vec3 | IsUnitAxis n ∧ 1 / ((k : ℝ) + 1) ≤ |n.1|}

/-- **NEUTRAL DEFINITION (§44).**  The explicit clamped rate adapted to the `k`-th band. -/
noncomputable def bandRate (k : ℕ) (n : Vec3) : ℝ :=
  (1 / 2) * max (-1) (min 1 (2 * ((k : ℝ) + 1) * n.1))

/-- **NEUTRAL DEFINITION (§44).**  The union of the chain: the directions with
nonvanishing first coordinate. -/
def bandUnion : Set Vec3 := {n : Vec3 | IsUnitAxis n ∧ n.1 ≠ 0}

theorem bandSet_mono {k l : ℕ} (h : k ≤ l) : bandSet k ⊆ bandSet l := by
  rintro n ⟨hn, hle⟩
  refine ⟨hn, le_trans ?_ hle⟩
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2 : ((k : ℝ) + 1) ≤ ((l : ℝ) + 1) := by
    have : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast h
    linarith
  exact one_div_le_one_div_of_le h1 h2

theorem bandSet_subset_bandUnion (k : ℕ) : bandSet k ⊆ bandUnion := by
  rintro n ⟨hn, hle⟩
  refine ⟨hn, ?_⟩
  have h1 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  intro hz
  rw [hz] at hle
  simp only [abs_zero] at hle
  linarith

theorem bandUnion_eq_iUnion : bandUnion = ⋃ k : ℕ, bandSet k := by
  ext n
  constructor
  · rintro ⟨hn, hne⟩
    have hpos : 0 < |n.1| := abs_pos.2 hne
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / |n.1|)
    refine Set.mem_iUnion.2 ⟨k, hn, ?_⟩
    have hk1 : 1 / |n.1| < (k : ℝ) + 1 := by linarith
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hkpos]
    rw [div_lt_iff₀ hpos] at hk1
    nlinarith
  · intro h
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h
    exact bandSet_subset_bandUnion k hk

theorem continuous_bandRate (k : ℕ) : RateCont (bandRate k) := by
  have hfst : Continuous fun s : Sph => ((s : Vec3)).1 :=
    continuous_fst.comp continuous_subtype_val
  unfold RateCont bandRate
  fun_prop

theorem bandRate_pos {k : ℕ} {n : Vec3} (h : 1 / ((k : ℝ) + 1) ≤ n.1) :
    bandRate k n = 1 / 2 := by
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : 1 ≤ ((k : ℝ) + 1) * n.1 := by
    rw [div_le_iff₀ hkpos] at h
    linarith [h]
  have hmin : min 1 (2 * ((k : ℝ) + 1) * n.1) = 1 := by
    apply min_eq_left; nlinarith
  rw [bandRate, hmin, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num

theorem bandRate_neg {k : ℕ} {n : Vec3} (h : n.1 ≤ -(1 / ((k : ℝ) + 1))) :
    bandRate k n = -(1 / 2) := by
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : ((k : ℝ) + 1) * n.1 ≤ -1 := by
    rw [le_neg, div_le_iff₀ hkpos] at h
    nlinarith [h]
  have hmin : min 1 (2 * ((k : ℝ) + 1) * n.1) = 2 * ((k : ℝ) + 1) * n.1 := by
    apply min_eq_right; nlinarith
  rw [bandRate, hmin, max_eq_left (by nlinarith)]
  norm_num

theorem bandSet_admissible (k : ℕ) : IsAdmissibleDomain (bandSet k) := by
  have hunit : UnitSet (bandSet k) := fun _ h => h.1
  have hkpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hval : ∀ n ∈ bandSet k, bandRate k n = 1 / 2 ∨ bandRate k n = -(1 / 2) := by
    rintro n ⟨-, hle⟩
    rcases abs_cases n.1 with ⟨heq, -⟩ | ⟨heq, -⟩
    · left
      exact bandRate_pos (by rw [← heq]; exact hle)
    · right
      refine bandRate_neg ?_
      rw [heq] at hle
      linarith
  refine (admissible_iff_exists_rate_function hunit).2
    ⟨bandRate k, continuous_bandRate k, ?_, ?_⟩
  · intro n hn
    rcases hval n hn with h | h
    · exact ⟨0, by rw [h]; norm_num⟩
    · exact ⟨-1, by rw [h]; norm_num⟩
  · intro n hn hneg
    have hn1 : (-n).1 = -n.1 := rfl
    rcases abs_cases n.1 with ⟨heq, hsgn⟩ | ⟨heq, hsgn⟩
    · have hp : 1 / ((k : ℝ) + 1) ≤ n.1 := by rw [← heq]; exact hn.2
      have hm : (-n).1 ≤ -(1 / ((k : ℝ) + 1)) := by rw [hn1]; linarith
      rw [bandRate_pos hp, bandRate_neg hm]
    · have hp : n.1 ≤ -(1 / ((k : ℝ) + 1)) := by
        have := hn.2; rw [heq] at this; linarith
      have hm : 1 / ((k : ℝ) + 1) ≤ (-n).1 := by rw [hn1]; linarith
      rw [bandRate_neg hp, bandRate_pos hm]
      ring

/-- **DERIVED.**  Every unit direction is a limit of unit directions with nonvanishing
first coordinate: the union of the chain is dense. -/
theorem bandUnion_dense : DenseDom bandUnion := by
  intro p
  set m : Vec3 := (p : Vec3) with hm
  have hmu : IsUnitAxis m := p.2
  by_cases h0 : m.1 = 0
  · -- perturb the first coordinate
    have hne : ∀ u : ℝ, ((u, m.2.1, m.2.2) : Vec3) ≠ 0 := by
      intro u hcon
      have h1 : m.2.1 = 0 := by
        have := congrArg (fun w : Vec3 => w.2.1) hcon; simpa using this
      have h2 : m.2.2 = 0 := by
        have := congrArg (fun w : Vec3 => w.2.2) hcon; simpa using this
      have hu : h3 m m = 1 := hmu
      rw [h3_self_coord, h0, h1, h2] at hu
      norm_num at hu
    set g : ℝ → Vec3 := fun u => nrmz ((u, m.2.1, m.2.2) : Vec3) with hg
    have hgc : Continuous g := by
      refine continuousOn_univ.1 ?_
      exact continuousOn_nrmz_comp (by fun_prop) (fun u _ => hne u)
    have hgu : ∀ u : ℝ, IsUnitAxis (g u) := fun u => nrmz_isUnitAxis (hne u)
    have hg0 : g 0 = m := by
      have hmeq : ((0 : ℝ), m.2.1, m.2.2) = m := by
        rw [← h0]
      rw [hg]
      simp only [hmeq]
      exact nrmz_of_isUnitAxis hmu
    have hmeet : ∀ ε > 0, ∃ u : ℝ, |u - 0| < ε ∧ g u ∈ bandUnion := by
      intro ε hε
      refine ⟨ε / 2, by rw [sub_zero, abs_of_pos (by linarith)]; linarith, hgu _, ?_⟩
      show (nrmz ((ε / 2, m.2.1, m.2.2) : Vec3)).1 ≠ 0
      rw [nrmz_fst]
      have hinv : 0 < (nrm ((ε / 2, m.2.1, m.2.2) : Vec3))⁻¹ := inv_pos.2 (nrm_pos (hne _))
      have : 0 < (nrm ((ε / 2, m.2.1, m.2.2) : Vec3))⁻¹ * (ε / 2) := by positivity
      exact ne_of_gt this
    have := mem_closure_of_param hmu hgc hgu hg0 hmeet
    simpa using this
  · exact subset_closure (show p ∈ sphSet bandUnion from ⟨hmu, h0⟩)

/-- **PRINCIPAL THEOREM (§44, §45): REFUTATION.**  The union of an increasing chain of
admissible sets need not be admissible.  Each band is admissible, the bands increase, their
union is the set of directions with nonvanishing first coordinate, and that union is
**not** admissible.  The mechanism is the one described in §45: the union is dense, so any
ambient rate is constant, and a constant rate contradicts the reversal constraint that the
union imposes. -/
theorem bandUnion_not_admissible : ¬ IsAdmissibleDomain bandUnion := by
  intro hadm
  have hunit : UnitSet bandUnion := fun _ h => h.1
  obtain ⟨b, hcont, hhalf, hodd⟩ := (admissible_iff_exists_rate_function hunit).1 hadm
  have hall : ∀ n : Vec3, IsUnitAxis n → IsHalfOdd (b n) := by
    intro n hn
    exact halfOdd_of_mem_closure hcont (fun m hm => hhalf m hm) (bandUnion_dense ⟨n, hn⟩)
  have he1 : e1 ∈ bandUnion := ⟨e1_isUnitAxis, by norm_num [e1]⟩
  have hne1 : -e1 ∈ bandUnion := by
    refine ⟨isUnitAxis_neg e1_isUnitAxis, ?_⟩
    show -e1.1 ≠ 0
    norm_num [e1]
  have hoddv : b (-e1) = -b e1 := hodd e1 he1 hne1
  have hconst : b (-e1) = b e1 :=
    halfOdd_const_on_sph hcont hall (isUnitAxis_neg e1_isUnitAxis) e1_isUnitAxis
  have hz : b e1 = 0 := by linarith
  obtain ⟨k, hk⟩ := hall e1 e1_isUnitAxis
  rw [hz] at hk
  have h2 : (2 * k : ℤ) = -1 := by
    have : (2 * (k : ℝ)) = -1 := by linarith
    exact_mod_cast this
  omega

theorem chain_union_not_admissible :
    (∀ k : ℕ, IsAdmissibleDomain (bandSet k)) ∧
      (∀ k l : ℕ, k ≤ l → bandSet k ⊆ bandSet l) ∧
      bandUnion = (⋃ k : ℕ, bandSet k) ∧
      ¬ IsAdmissibleDomain bandUnion :=
  ⟨bandSet_admissible, fun _ _ h => bandSet_mono h, bandUnion_eq_iUnion,
    bandUnion_not_admissible⟩

/-! ## §42, existence — an explicit maximal admissible set -/

/-- **NEUTRAL DEFINITION.**  The directions whose third coordinate is a rational multiple
of the first.  The set is reversal-symmetric. -/
def ratioSet : Set Vec3 := {n : Vec3 | ∃ q : ℚ, n.2.2 = (q : ℝ) * n.1}

/-- **NEUTRAL DEFINITION.**  The lexicographic half-space with its choice reversed exactly
on the rational-ratio directions. -/
def flipSet : Set Vec3 :=
  {n : Vec3 | IsUnitAxis n ∧ ((n ∈ lexA ∧ n ∉ ratioSet) ∨ (n ∉ lexA ∧ n ∈ ratioSet))}

theorem ratioSet_symm {n : Vec3} : -n ∈ ratioSet ↔ n ∈ ratioSet := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    have h1 : (-n).2.2 = -n.2.2 := rfl
    have h2 : (-n).1 = -n.1 := rfl
    rw [h1, h2] at hq
    linarith
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    show -n.2.2 = (q : ℝ) * (-n.1)
    rw [hq]; ring

theorem flipSet_unit : UnitSet flipSet := fun _ h => h.1

/-- **DERIVED.**  The reversed lexicographic half-space contains exactly one direction of
every antipodal pair. -/
theorem flipSet_exactly_one {n : Vec3} (hn : IsUnitAxis n) :
    (n ∈ flipSet ∧ -n ∉ flipSet) ∨ (n ∉ flipSet ∧ -n ∈ flipSet) := by
  have hnn : IsUnitAxis (-n) := isUnitAxis_neg hn
  rcases lexA_exactly_one hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · by_cases hr : n ∈ ratioSet
    · refine Or.inr ⟨?_, ⟨hnn, Or.inr ⟨h2, ratioSet_symm.2 hr⟩⟩⟩
      rintro ⟨-, ⟨-, hc⟩ | ⟨hc, -⟩⟩
      · exact hc hr
      · exact hc h1
    · refine Or.inl ⟨⟨hn, Or.inl ⟨h1, hr⟩⟩, ?_⟩
      rintro ⟨-, ⟨hc, -⟩ | ⟨-, hc⟩⟩
      · exact h2 hc
      · exact hr (ratioSet_symm.1 hc)
  · by_cases hr : n ∈ ratioSet
    · refine Or.inl ⟨⟨hn, Or.inr ⟨h1, hr⟩⟩, ?_⟩
      rintro ⟨-, ⟨-, hc⟩ | ⟨hc, -⟩⟩
      · exact hc (ratioSet_symm.2 hr)
      · exact hc h2
    · refine Or.inr ⟨?_, ⟨hnn, Or.inl ⟨h2, fun hc => hr (ratioSet_symm.1 hc)⟩⟩⟩
      rintro ⟨-, ⟨hc, -⟩ | ⟨-, hc⟩⟩
      · exact h1 hc
      · exact hr hc

theorem flipSet_antipodalFree : AntipodalFree flipSet := by
  intro n hn hneg
  rcases flipSet_exactly_one hn.1 with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact h2 hneg
  · exact h1 hn

theorem flipSet_antipodalComplete : AntipodalComplete flipSet := by
  intro n hn
  rcases flipSet_exactly_one hn with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact Or.inl h1
  · exact Or.inr h2

theorem nrmz_snd_snd (w : Vec3) : (nrmz w).2.2 = (nrm w)⁻¹ * w.2.2 := rfl

/-- **DERIVED.**  Every direction with nonvanishing first coordinate is a limit of
directions of the reversed lexicographic half-space: along the explicit family with fixed
first two coordinates and varying third-to-first ratio, membership is governed exactly by
rationality of the ratio, and both the rationals and their complement are dense. -/
theorem flipSet_dense_of_fst_ne {m : Vec3} (hmu : IsUnitAxis m) (h0 : m.1 ≠ 0) :
    (⟨m, hmu⟩ : Sph) ∈ closure (sphSet flipSet) := by
  set u₀ : ℝ := m.2.2 / m.1 with hu₀
  have hne : ∀ u : ℝ, ((m.1, m.2.1, u * m.1) : Vec3) ≠ 0 := by
    intro u hcon
    have h := congrArg (fun w : Vec3 => w.1) hcon
    exact h0 (by simpa using h)
  set g : ℝ → Vec3 := fun u => nrmz ((m.1, m.2.1, u * m.1) : Vec3) with hg
  have hgu : ∀ u : ℝ, IsUnitAxis (g u) := fun u => nrmz_isUnitAxis (hne u)
  have hgc : Continuous g := by
    refine continuousOn_univ.1 ?_
    exact continuousOn_nrmz_comp (by fun_prop) (fun u _ => hne u)
  have hg0 : g u₀ = m := by
    have h : ((m.1, m.2.1, u₀ * m.1) : Vec3) = m := by
      rw [hu₀, div_mul_cancel₀ _ h0]
    rw [hg]
    simp only [h]
    exact nrmz_of_isUnitAxis hmu
  set c : ℝ → ℝ := fun u => (nrm ((m.1, m.2.1, u * m.1) : Vec3))⁻¹ with hc
  have hcpos : ∀ u : ℝ, 0 < c u := fun u => inv_pos.2 (nrm_pos (hne u))
  have hgfst : ∀ u : ℝ, (g u).1 = c u * m.1 := fun u => rfl
  have hgsnd : ∀ u : ℝ, (g u).2.2 = c u * (u * m.1) := fun u => rfl
  have hratio : ∀ u : ℝ, g u ∈ ratioSet ↔ ∃ q : ℚ, u = (q : ℝ) := by
    intro u
    have hcm : c u * m.1 ≠ 0 := by
      have := hcpos u
      exact mul_ne_zero (ne_of_gt this) h0
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨q, ?_⟩
      rw [hgsnd u, hgfst u] at hq
      have h2 : (c u * m.1) * u = (c u * m.1) * (q : ℝ) := by linear_combination hq
      exact mul_left_cancel₀ hcm h2
    · rintro ⟨q, rfl⟩
      refine ⟨q, ?_⟩
      rw [hgsnd, hgfst]
      ring
  have hlexpos : ∀ u : ℝ, 0 < m.1 → g u ∈ lexA := by
    intro u hpos
    refine ⟨hgu u, Or.inl ?_⟩
    show 0 < (g u).1
    rw [hgfst u]
    exact mul_pos (hcpos u) hpos
  have hlexneg : ∀ u : ℝ, m.1 < 0 → g u ∉ lexA := by
    intro u hneg hmem
    have h1 : 0 ≤ (g u).1 := lexA_fst_nonneg hmem
    rw [hgfst u] at h1
    nlinarith [hcpos u]
  refine mem_closure_of_param hmu hgc hgu hg0 ?_
  intro ε hε
  rcases lt_trichotomy m.1 0 with hm1 | hm1 | hm1
  · -- the direction is on the negative side: use a rational ratio
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u₀ < u₀ + ε by linarith)
    refine ⟨(q : ℝ), ?_, ?_⟩
    · rw [abs_of_pos (by linarith)]; linarith
    · exact ⟨hgu _, Or.inr ⟨hlexneg _ hm1, (hratio _).2 ⟨q, rfl⟩⟩⟩
  · exact absurd hm1 h0
  · -- the direction is on the positive side: use an irrational ratio
    obtain ⟨x, hx, hx1, hx2⟩ := exists_irrational_btwn (show u₀ < u₀ + ε by linarith)
    refine ⟨x, ?_, ?_⟩
    · rw [abs_of_pos (by linarith)]; linarith
    · refine ⟨hgu _, Or.inl ⟨hlexpos _ hm1, ?_⟩⟩
      intro hmem
      obtain ⟨q, hq⟩ := (hratio x).1 hmem
      exact hx ⟨q, hq.symm⟩

/-- **PRINCIPAL THEOREM (§42), existence.**  The reversed lexicographic half-space is
dense. -/
theorem flipSet_dense : DenseDom flipSet := by
  intro p
  set m : Vec3 := (p : Vec3) with hm
  have hmu : IsUnitAxis m := p.2
  by_cases h0 : m.1 = 0
  · have hne : ∀ u : ℝ, ((u, m.2.1, m.2.2) : Vec3) ≠ 0 := by
      intro u hcon
      have h1 : m.2.1 = 0 := by
        have := congrArg (fun w : Vec3 => w.2.1) hcon; simpa using this
      have h2 : m.2.2 = 0 := by
        have := congrArg (fun w : Vec3 => w.2.2) hcon; simpa using this
      have hu : h3 m m = 1 := hmu
      rw [h3_self_coord, h0, h1, h2] at hu
      norm_num at hu
    set g : ℝ → Vec3 := fun u => nrmz ((u, m.2.1, m.2.2) : Vec3) with hg
    have hgu : ∀ u : ℝ, IsUnitAxis (g u) := fun u => nrmz_isUnitAxis (hne u)
    have hgc : Continuous g := by
      refine continuousOn_univ.1 ?_
      exact continuousOn_nrmz_comp (by fun_prop) (fun u _ => hne u)
    have hg0 : g 0 = m := by
      have hmeq : ((0 : ℝ), m.2.1, m.2.2) = m := by rw [← h0]
      rw [hg]
      simp only [hmeq]
      exact nrmz_of_isUnitAxis hmu
    have hmeet : ∀ ε > 0, ∃ u : ℝ, |u - 0| < ε ∧
        (⟨g u, hgu u⟩ : Sph) ∈ closure (sphSet flipSet) := by
      intro ε hε
      refine ⟨ε / 2, by rw [sub_zero, abs_of_pos (by linarith)]; linarith, ?_⟩
      refine flipSet_dense_of_fst_ne (hgu _) ?_
      show (nrmz ((ε / 2, m.2.1, m.2.2) : Vec3)).1 ≠ 0
      rw [nrmz_fst]
      have hinv : 0 < (nrm ((ε / 2, m.2.1, m.2.2) : Vec3))⁻¹ := inv_pos.2 (nrm_pos (hne _))
      have hpos : 0 < (nrm ((ε / 2, m.2.1, m.2.2) : Vec3))⁻¹ * (ε / 2) := by positivity
      exact ne_of_gt hpos
    have hcl := mem_closure_of_param' hmu hgc hgu hg0 hmeet
    rw [closure_closure] at hcl
    exact hcl
  · exact flipSet_dense_of_fst_ne hmu h0

/-- **PRINCIPAL THEOREM (§42).**  Inclusion-maximal members of the plain admissible class
**exist**, and one is given explicitly. -/
theorem exists_maximal_adm : IsMaximalIn AdmClass flipSet :=
  maximal_adm_sufficient flipSet_unit flipSet_dense flipSet_antipodalComplete
    flipSet_antipodalFree

/-! ## §47, §48 — existence, uniqueness, canonicality -/

theorem negSet_unitSet {D : Set Vec3} (hunit : UnitSet D) : UnitSet (negSet D) := by
  intro n hn
  have : IsUnitAxis (-n) := hunit (-n) hn
  simpa using isUnitAxis_neg this

/-- **DERIVED (§47).**  The reversed set of a maximal admissible set is again maximal
admissible. -/
theorem negSet_maximal_adm {D : Set Vec3} (hunit : UnitSet D)
    (hmax : IsMaximalIn AdmClass D) : IsMaximalIn AdmClass (negSet D) := by
  obtain ⟨hdense, hcomp, hfree⟩ := maximal_adm_necessary hmax
  refine maximal_adm_sufficient (negSet_unitSet hunit) ?_ ?_ ?_
  · intro p
    have h := hdense (negSph p)
    rw [closure_sphSet_negSet]
    exact h
  · intro n hn
    rcases hcomp n hn with h | h
    · refine Or.inr ?_
      show -(-n) ∈ D
      rwa [neg_neg]
    · exact Or.inl h
  · intro n hn hneg
    have h1 : -n ∈ D := hn
    have h2 : n ∈ D := by
      have : -(-n) ∈ D := hneg
      rwa [neg_neg] at this
    exact hfree (-n) h1 (by rwa [neg_neg])

/-- **PRINCIPAL THEOREM (§47, §48): REFUTATION of uniqueness.**  Maximal admissible sets
are **not** unique: the reversed set of one is a different one.  Canonicality is therefore
not available, and is not inferred from existence. -/
theorem maximal_adm_not_unique :
    ∃ D E : Set Vec3, IsMaximalIn AdmClass D ∧ IsMaximalIn AdmClass E ∧ D ≠ E := by
  refine ⟨flipSet, negSet flipSet, exists_maximal_adm,
    negSet_maximal_adm flipSet_unit exists_maximal_adm, ?_⟩
  intro hcon
  rcases flipSet_exactly_one e1_isUnitAxis with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : e1 ∈ negSet flipSet := by rw [← hcon]; exact h1
    exact h2 this
  · have : (-e1) ∈ negSet flipSet := by rw [← hcon]; exact h2
    rw [mem_negSet, neg_neg] at this
    exact h1 this

end NullSectorTask19
