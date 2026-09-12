import RequestProject.Experiment2.NullSectorTask19.RelationBridge

/-!
# Task 19, Package I: regularity above `C¹`

The Task-18 extension-and-staircase construction is inspected step by step (§74) rather than
used as a black box:

1. the continuous rate is extended from the unit directions to the whole carrier and cut off
   (`exists_compactSupport_extension`) — this step produces a merely continuous function and
   is *not* required to be differentiable;
2. that function is approximated within `1/4` by a function which Mathlib already provides
   as **infinitely** differentiable (`UniformContinuous.exists_contDiff_dist_le`);
3. the staircase is a finite sum of translated copies of `Real.smoothTransition`, which is
   `Cᵏ` for **every** `k` — the Task-18 file merely instantiated `k = 1`;
4. the composition is as smooth as its two factors.

So no step of the construction is limited to `C¹`.

* §75, §76.  `IsAdmissibleDomain D ↔ IsCkAdmissibleDomain k D` for every finite `k` and every
  set `D` of unit directions.
* §77, §78.  The same holds for `C∞`: `IsAdmissibleDomain D ↔ IsCkAdmissibleDomain ∞ D`.
* §80, §81.  Analyticity is audited **separately** and is not inferred from smoothness.  The
  exact plateau of the staircase is genuinely incompatible with analytic continuation:
  `analytic_plateau_forces_constant`.  For antipodal-free domains an analytic rate does
  exist (a constant), so the analytic question is not uniformly negative; the
  arbitrary-domain analytic problem is left open and is recorded as such.
-/

namespace NullSectorTask19

open scoped ContDiff

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18

/-! ## §75 — the regularity index -/

/-- **NEUTRAL DEFINITION (§75).**  A jointly `Cʳ` family, for an arbitrary smoothness index
`r`: jointly regular, and presented by two `Cʳ` rate functions of the direction.  For
`r = 1` this is literally the Task-18 notion. -/
def IsCkJointlyRegularFamily (r : WithTop ℕ∞) (U : Vec3 → ℝ → W) : Prop :=
  IsJointlyRegularFamily U ∧ ∃ a b : Vec3 → ℝ, ContDiff ℝ r a ∧ ContDiff ℝ r b ∧
    ∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, U n θ = zexp (a n) (b n) θ ⋆ Un n θ

/-- **NEUTRAL DEFINITION (§75).**  `Cʳ` admissibility, with exactly the same quantifiers as
continuous admissibility. -/
def IsCkAdmissibleDomain (r : WithTop ℕ∞) (D : Set Vec3) : Prop :=
  (∀ n ∈ D, IsUnitAxis n) ∧
    ∃ U : Vec3 → ℝ → W, IsCkJointlyRegularFamily r U ∧ IsTransformationValuedOn D U

theorem IsCkJointlyRegularFamily.toJointlyRegular {r : WithTop ℕ∞} {U : Vec3 → ℝ → W}
    (h : IsCkJointlyRegularFamily r U) : IsJointlyRegularFamily U := h.1

/-- **DERIVED.**  The Task-18 `C¹` notion is the case `r = 1`. -/
theorem isCkJointlyRegular_one_iff {U : Vec3 → ℝ → W} :
    IsCkJointlyRegularFamily 1 U ↔ IsC1JointlyRegularFamily U := Iff.rfl

theorem isCkAdmissible_one_iff {D : Set Vec3} :
    IsCkAdmissibleDomain 1 D ↔ IsC1AdmissibleDomain D := Iff.rfl

/-- **DERIVED.**  Lower smoothness indices are weaker. -/
theorem IsCkJointlyRegularFamily.of_le {r s : WithTop ℕ∞} (hrs : r ≤ s) {U : Vec3 → ℝ → W}
    (h : IsCkJointlyRegularFamily s U) : IsCkJointlyRegularFamily r U := by
  obtain ⟨hU, a, b, ha, hb, hval⟩ := h
  exact ⟨hU, a, b, ha.of_le hrs, hb.of_le hrs, hval⟩

theorem IsCkAdmissibleDomain.of_le {r s : WithTop ℕ∞} (hrs : r ≤ s) {D : Set Vec3}
    (h : IsCkAdmissibleDomain s D) : IsCkAdmissibleDomain r D := by
  obtain ⟨hunit, U, hU, hexact⟩ := h
  exact ⟨hunit, U, hU.of_le hrs, hexact⟩

/-! ## §74 — step 3 of the construction is smooth, not merely `C¹` -/

/-- **PRINCIPAL THEOREM (§74), step 3.**  The Task-18 staircase is infinitely
differentiable.  The Task-18 file proved only the instance `k = 1`; the same proof works
verbatim at `∞`, because `Real.smoothTransition` is `Cᵏ` for every `k`. -/
theorem stair_contDiff_infty (N : ℕ) : ContDiff ℝ ∞ (stair N) := by
  unfold stair
  refine contDiff_const.add (ContDiff.sum ?_)
  intro j _
  have h : ContDiff ℝ ∞ fun x : ℝ => 2 * (x - (-(N : ℝ) + j + 3 / 4)) :=
    (contDiff_id.sub contDiff_const).const_smul (2 : ℝ)
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp h

/-! ## §77 — the smooth rate -/

/-- **PRINCIPAL THEOREM (§77), the construction.**  Every rate function which is continuous
on the unit directions and half-odd on an arbitrary set `D` of unit directions is matched on
`D` by an **infinitely differentiable** function of the direction.  Every step of the
Task-18 construction is reused at smoothness index `∞`. -/
theorem exists_smooth_rate {b : Vec3 → ℝ} (hb : Continuous fun s : Sph => b (s : Vec3))
    {D : Set Vec3} (hunit : ∀ n ∈ D, IsUnitAxis n)
    (hhalf : ∀ n ∈ D, ∃ k : ℤ, b n = (k : ℝ) + 1 / 2) :
    ∃ c : Vec3 → ℝ, ContDiff ℝ ∞ c ∧ ∀ n ∈ D, c n = b n := by
  obtain ⟨B, hBcont, hBsupp, hBval⟩ := exists_compactSupport_extension hb
  obtain ⟨g, hgsmooth, hgapp⟩ :=
    (hBsupp.uniformContinuous_of_continuous hBcont).exists_contDiff_dist_le
      (ε := 1 / 4) (by norm_num)
  obtain ⟨M, hM⟩ := rate_bounded hb
  obtain ⟨N, hN⟩ := exists_nat_ge (M + 1)
  refine ⟨stair N ∘ g, (stair_contDiff_infty N).comp hgsmooth, ?_⟩
  intro n hn
  obtain ⟨k, hk⟩ := hhalf n hn
  have hbn : |b n| ≤ M := hM n (hunit n hn)
  have hkM : |((k : ℝ) + 1 / 2)| ≤ M := by rw [← hk]; exact hbn
  have hkabs : |(k : ℝ)| ≤ (N : ℝ) := by
    rcases abs_le.1 hkM with ⟨h1, h2⟩
    rw [abs_le]
    constructor <;> linarith
  have hk1 : -(N : ℤ) ≤ k := by
    have : -(N : ℝ) ≤ (k : ℝ) := (abs_le.1 hkabs).1
    exact_mod_cast this
  have hk2 : k ≤ (N : ℤ) := by
    have : (k : ℝ) ≤ (N : ℝ) := (abs_le.1 hkabs).2
    exact_mod_cast this
  have hdist : |g n - ((k : ℝ) + 1 / 2)| ≤ 1 / 4 := by
    have h1 : dist (g n) (B n) < 1 / 4 := hgapp n
    rw [Real.dist_eq, hBval n (hunit n hn), hk] at h1
    linarith [le_of_lt h1]
  show stair N (g n) = b n
  rw [stair_eq N k hk1 hk2 (g n) hdist, hk]

/-! ## §78 — continuous admissibility is smooth admissibility -/

/-- **PRINCIPAL THEOREM (§78).**  For **every** set of unit directions — no openness, no
connectedness, no antipodal condition — continuous admissibility and `C∞` admissibility
coincide.  The forward direction constructs the smooth rate. -/
theorem admissible_iff_smoothAdmissible {D : Set Vec3} :
    IsAdmissibleDomain D ↔ IsCkAdmissibleDomain ∞ D := by
  constructor
  · rintro ⟨hunit, U, hU, hexact⟩
    obtain ⟨b, hcont, hhalf, hodd⟩ := (admissible_iff_exists_rate_function hunit).1
      ⟨hunit, U, hU, hexact⟩
    obtain ⟨c, hcsm, hcval⟩ := exists_smooth_rate hcont hunit hhalf
    have hchalf : ∀ n ∈ D, ∃ k : ℤ, c n = (k : ℝ) + 1 / 2 := by
      intro n hn
      obtain ⟨k, hk⟩ := hhalf n hn
      exact ⟨k, by rw [hcval n hn, hk]⟩
    have hcodd : ∀ n ∈ D, -n ∈ D → c (-n) = -c n := by
      intro n hn hneg
      rw [hcval n hn, hcval (-n) hneg]
      exact hodd n hn hneg
    have hccont : Continuous fun s : Sph => c (s : Vec3) :=
      (hcsm.continuous).comp continuous_subtype_val
    refine ⟨hunit, famOf (fun _ => 0) c, ⟨jointlyRegular_famOf continuous_const hccont,
      fun _ => 0, c, contDiff_const, hcsm, fun _ _ _ => rfl⟩, ?_⟩
    exact famOfZ_exact_on hunit hchalf hcodd
  · rintro ⟨hunit, U, hU, hexact⟩
    exact ⟨hunit, U, hU.toJointlyRegular, hexact⟩

/-- **PRINCIPAL THEOREM (§76).**  For every **finite** `k` and every set of unit directions,
continuous admissibility and `Cᵏ` admissibility coincide. -/
theorem admissible_iff_ckAdmissible (k : ℕ) {D : Set Vec3} :
    IsAdmissibleDomain D ↔ IsCkAdmissibleDomain (k : WithTop ℕ∞) D := by
  constructor
  · intro h
    exact (admissible_iff_smoothAdmissible.1 h).of_le (by exact_mod_cast le_top)
  · rintro ⟨hunit, U, hU, hexact⟩
    exact ⟨hunit, U, hU.toJointlyRegular, hexact⟩

/-- **PRINCIPAL THEOREM (§75)–(§78), summary.**  The whole regularity ladder from continuity
to `C∞` collapses, for arbitrary domains. -/
theorem regularity_ladder_collapses {D : Set Vec3} :
    (IsAdmissibleDomain D ↔ IsCkAdmissibleDomain ∞ D) ∧
      (∀ k : ℕ, IsAdmissibleDomain D ↔ IsCkAdmissibleDomain (k : WithTop ℕ∞) D) ∧
      (IsAdmissibleDomain D ↔ IsC1AdmissibleDomain D) :=
  ⟨admissible_iff_smoothAdmissible, fun k => admissible_iff_ckAdmissible k,
    admissible_iff_c1Admissible⟩

/-! ## §80, §81 — the separate analyticity audit -/

/-- **PRINCIPAL THEOREM (§81), the obstruction to analyticity of the construction.**  An
exact plateau conflicts with analytic continuation: a real function analytic on the whole
line which is constant on some nonempty open interval is constant everywhere.  The staircase
step of the construction is therefore **not** available in the analytic category, and
smoothness must not be upgraded to analyticity. -/
theorem analytic_plateau_forces_constant {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f Set.univ) {p q c : ℝ} (hpq : p < q)
    (hconst : ∀ x ∈ Set.Ioo p q, f x = c) : ∀ x : ℝ, f x = c := by
  have hg : AnalyticOnNhd ℝ (fun _ : ℝ => c) Set.univ := fun _ _ => analyticAt_const
  have hmid : (p + q) / 2 ∈ Set.Ioo p q := ⟨by linarith, by linarith⟩
  have hnb : Set.Ioo p q ∈ nhds ((p + q) / 2) := isOpen_Ioo.mem_nhds hmid
  have heq : f =ᶠ[nhds ((p + q) / 2)] fun _ : ℝ => c := by
    filter_upwards [hnb] with x hx using hconst x hx
  have := hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ
    (Set.mem_univ ((p + q) / 2)) heq
  intro x
  exact this (Set.mem_univ x)

/-- **DERIVED (§80).**  Analyticity is nevertheless *not* uniformly obstructed: every
antipodal-free set of unit directions carries an **analytic** rate, namely a constant one.
So the analytic question is a genuinely separate problem, not a corollary of the smooth
one. -/
theorem antipodalFree_analyticAdmissible {D : Set Vec3} (hunit : ∀ n ∈ D, IsUnitAxis n)
    (hfree : AntipodalFree D) : IsCkAdmissibleDomain ω D := by
  refine ⟨hunit, famOf (fun _ => 0) (fun _ => (1 : ℝ) / 2),
    ⟨jointlyRegular_famOf continuous_const continuous_const,
      fun _ => 0, fun _ => (1 : ℝ) / 2, contDiff_const, contDiff_const, fun _ _ _ => rfl⟩, ?_⟩
  exact famOfZ_exact_on hunit (fun _ _ => ⟨0, by norm_num⟩)
    (fun n hn hneg => absurd hneg (hfree n hn))

/-- **DERIVED (§80), the boundary.**  Smoothness holds for arbitrary domains; analyticity is
established here only for antipodal-free domains.  The two statements are recorded
separately and the second is **not** inferred from the first. -/
theorem smooth_not_analytic_boundary {D : Set Vec3} :
    (IsAdmissibleDomain D ↔ IsCkAdmissibleDomain ∞ D) ∧
      ((∀ n ∈ D, IsUnitAxis n) → AntipodalFree D → IsCkAdmissibleDomain ω D) :=
  ⟨admissible_iff_smoothAdmissible, fun hunit hfree => antipodalFree_analyticAdmissible hunit hfree⟩

end NullSectorTask19
