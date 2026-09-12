import RequestProject.Experiment2.NullSectorTask16.ExactCoincidences

/-!
# Task 16, Layer 2 (Work Package 2): joint direction–parameter regularity

The Task-15 regular-family predicate imposes regularity only in the parameter, separately
for each fixed direction.  This layer defines the strictly stronger notion in which the
*full* map `(n, θ) ↦ U n θ` is continuous, and settles exactly what that implies for the
two rate functions recovered by the Task-15 one-axis classification.

The definition of joint regularity does **not** mention `α` or `β`: it says only that each
`U n` is an internal implementation of the inherited automorphism family of `n` (unit at
zero, one-axis group law, conjugation action) and that the two-variable map is continuous
on the inherited set of unit directions.

The answer is an exact equivalence:

* joint continuity **forces both** recovered rates to be continuous functions of the
  direction (`jointlyRegular_alpha_continuous`, `jointlyRegular_beta_continuous`);
  in particular no more general phenomenon appears and the one-axis `α`/`β`
  parametrization needs no refinement;
* conversely, every pair of continuous rate functions produces a jointly regular family
  (`jointlyRegular_famOf`);
* hence `jointRegularity_classification`: jointly regular families are *exactly* the
  families `U n θ = zexp (α n) (β n) θ ⋆ Un n θ` with `α, β` continuous on the unit
  directions.

The analytic core is the elementary lemma `continuous_of_joint_circle`: if the two
circular coordinates of `b x · θ` are jointly continuous in `(x, θ)`, then `b` itself is
continuous.  It is proved from scratch (compactness of a parameter interval, the sign
change of the cosine at `π`, and the elementary lower bound for the sine on a quarter
period); nothing about covering spaces or winding is used.
-/

namespace NullSectorTask16

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15

/-! ## The analytic core -/

/-- **DERIVED (analytic core).**  If the two circular coordinates of `b x · θ` depend
continuously on the *pair* `(x, θ)`, then `b` is continuous.  Only compactness of the
parameter interval `[0,1]`, the value of the cosine at `π` and the elementary bound
`2x/π ≤ sin x` on a quarter period are used. -/
theorem continuous_of_joint_circle {X : Type*} [TopologicalSpace X] {b : X → ℝ}
    (hc : Continuous fun p : X × ℝ => Real.cos (b p.1 * p.2))
    (hs : Continuous fun p : X × ℝ => Real.sin (b p.1 * p.2)) : Continuous b := by
  have hpi := Real.pi_pos
  rw [continuous_iff_continuousAt]
  intro x₀
  set F : X × ℝ → ℝ := fun p => Real.cos ((b p.1 - b x₀) * p.2) with hF
  have hFc : Continuous F := by
    have he : F = fun p : X × ℝ =>
        Real.cos (b p.1 * p.2) * Real.cos (b x₀ * p.2)
          + Real.sin (b p.1 * p.2) * Real.sin (b x₀ * p.2) := by
      funext p
      rw [hF]
      simp only [sub_mul]
      rw [Real.cos_sub]
    rw [he]
    fun_prop
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := min ε Real.pi with hδ
  have hδpos : 0 < δ := lt_min hε hpi
  have hδpi : δ ≤ Real.pi := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hpi2 : (0 : ℝ) < Real.pi ^ 2 := by positivity
  set κ : ℝ := 1 - 2 * (δ ^ 2 / Real.pi ^ 2) with hκ
  have hκlt : κ < 1 := by
    rw [hκ]
    have : 0 < 2 * (δ ^ 2 / Real.pi ^ 2) := by positivity
    linarith
  have hκlb : -1 ≤ κ := by
    rw [hκ]
    have h2 : δ ^ 2 / Real.pi ^ 2 ≤ 1 := by
      rw [div_le_one hpi2]; nlinarith
    linarith
  obtain ⟨u, v, hu, -, hx₀u, hIv, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := x₀))
      (isCompact_Icc (a := (0 : ℝ)) (b := 1))
      (hFc.isOpen_preimage (Set.Ioi κ) isOpen_Ioi) (by
        rintro ⟨x, θ⟩ ⟨hx, -⟩
        simp only [Set.mem_singleton_iff] at hx
        subst hx
        simp only [Set.mem_preimage, Set.mem_Ioi, hF, sub_self, zero_mul, Real.cos_zero]
        exact hκlt)
  filter_upwards [hu.mem_nhds (hx₀u rfl)] with x hx
  set t : ℝ := b x - b x₀ with ht
  have hkey : ∀ θ ∈ Set.Icc (0 : ℝ) 1, κ < Real.cos (t * θ) := by
    intro θ hθ
    have hmem : (x, θ) ∈ u ×ˢ v := ⟨hx, hIv hθ⟩
    have := huv hmem
    simpa [hF, ht] using this
  have hstep1 : |t| < Real.pi := by
    by_contra hcon
    push_neg at hcon
    have htne : t ≠ 0 := by
      intro h0; rw [h0] at hcon; simp at hcon; linarith
    have habs : 0 < |t| := abs_pos.2 htne
    have hθmem : Real.pi / |t| ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one habs]; exact hcon
    have hk := hkey _ hθmem
    have hval : t * (Real.pi / |t|) = Real.pi ∨ t * (Real.pi / |t|) = -Real.pi := by
      rcases abs_cases t with ⟨h1, -⟩ | ⟨h1, -⟩
      · left; rw [h1]; field_simp
      · right; rw [h1]; field_simp
    rcases hval with h' | h' <;> rw [h'] at hk
    · rw [Real.cos_pi] at hk; linarith
    · rw [Real.cos_neg, Real.cos_pi] at hk; linarith
  have h1 := hkey 1 (by norm_num)
  rw [mul_one] at h1
  have hhalf : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    have h2 := Real.cos_two_mul (t / 2)
    have hpy := Real.sin_sq_add_cos_sq (t / 2)
    rw [show 2 * (t / 2) = t by ring] at h2
    linarith
  have hjord : |t| / Real.pi ≤ Real.sin (|t| / 2) := by
    have hm := Real.mul_le_sin (x := |t| / 2) (by positivity) (by linarith [hstep1])
    calc |t| / Real.pi = 2 / Real.pi * (|t| / 2) := by ring
      _ ≤ Real.sin (|t| / 2) := hm
  have hsq : |t| ^ 2 / Real.pi ^ 2 ≤ Real.sin (t / 2) ^ 2 := by
    have hnn : 0 ≤ |t| / Real.pi := by positivity
    have hs2 : Real.sin (|t| / 2) ^ 2 = Real.sin (t / 2) ^ 2 := by
      rcases abs_cases t with ⟨h', -⟩ | ⟨h', -⟩
      · rw [h']
      · rw [h', show -t / 2 = -(t / 2) by ring, Real.sin_neg]; ring
    have hle : (|t| / Real.pi) ^ 2 ≤ Real.sin (|t| / 2) ^ 2 := by nlinarith [hjord, hnn]
    rw [div_pow] at hle
    linarith [hle, hs2]
  have hsin_lt : Real.sin (t / 2) ^ 2 < δ ^ 2 / Real.pi ^ 2 := by
    rw [hhalf, hκ] at h1
    linarith
  have habs2 : |t| ^ 2 < δ ^ 2 := by
    have hlt := lt_of_le_of_lt hsq hsin_lt
    rw [div_lt_div_iff_of_pos_right hpi2] at hlt
    exact hlt
  have hlt : |t| < δ := by nlinarith [abs_nonneg t, hδpos, habs2]
  rw [Real.dist_eq]
  calc |b x - b x₀| = |t| := by rw [ht]
    _ < δ := hlt
    _ ≤ ε := hδε

/-! ## The set of unit directions as a carrier for joint continuity -/

/-- **NEUTRAL DEFINITION.**  The inherited unit spatial directions, carrying the subspace
topology of the inherited old spatial carrier.  No further structure is attached. -/
abbrev Sph : Type := {n : Vec3 // IsUnitAxis n}

theorem continuous_sph_val : Continuous (fun s : Sph => (s : Vec3)) := continuous_subtype_val

/-! ## Work Package 2 — the definition -/

/-- **NEUTRAL DEFINITION (Work Package 2).**  A *jointly regular family*: for every unit
direction an internal implementation of the inherited automorphism family of that
direction — normalized at the identity parameter, obeying the one-axis group law, and
implementing `PhiGen n θ` by conjugation — such that the full two-variable map is
continuous on the unit directions.

This is strictly stronger than the Task-15 axiswise predicate: no regularity in the
direction is assumed there.  Nothing about `α` or `β` is assumed here. -/
structure IsJointlyRegularFamily (U : Vec3 → ℝ → W) : Prop where
  /-- Each direction carries an internal implementation of its automorphism family. -/
  lift : ∀ n : Vec3, IsUnitAxis n → IsAxisLift n (U n)
  /-- Joint continuity in the direction and the parameter. -/
  joint : Continuous fun p : Sph × ℝ => U (p.1 : Vec3) p.2

namespace IsJointlyRegularFamily

variable {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
include hU

/-- **DERIVED.**  Joint regularity implies the Task-15 axiswise regularity. -/
theorem toRegularFamily : IsRegularFamily U := by
  intro n hn
  refine ⟨hU.lift n hn, ?_⟩
  have he : U n = (fun p : Sph × ℝ => U (p.1 : Vec3) p.2) ∘ fun θ : ℝ => ((⟨n, hn⟩ : Sph), θ) :=
    rfl
  rw [he]
  exact hU.joint.comp (by fun_prop)

/-- **DERIVED.**  Every coordinate of a jointly regular family is jointly continuous. -/
theorem coord_continuous (i : Fin 8) :
    Continuous fun p : Sph × ℝ => U (p.1 : Vec3) p.2 i :=
  (continuous_apply i).comp hU.joint

end IsJointlyRegularFamily

/-! ## Recovery of the two rate functions -/

/-- **NEUTRAL DEFINITION.**  The first coefficient of the central residual, written as an
explicit continuous expression in the coordinates of the family. -/
noncomputable def recA (U : Vec3 → ℝ → W) (s : Sph) (θ : ℝ) : ℝ :=
  Real.cos (θ / 2) * U (s : Vec3) θ 0
    - Real.sin (θ / 2) * ((s : Vec3).1 * U (s : Vec3) θ 6 - (s : Vec3).2.1 * U (s : Vec3) θ 5
        + (s : Vec3).2.2 * U (s : Vec3) θ 4)

/-- **NEUTRAL DEFINITION.**  The second coefficient of the central residual. -/
noncomputable def recB (U : Vec3 → ℝ → W) (s : Sph) (θ : ℝ) : ℝ :=
  Real.cos (θ / 2) * U (s : Vec3) θ 7
    + Real.sin (θ / 2) * ((s : Vec3).1 * U (s : Vec3) θ 1 + (s : Vec3).2.1 * U (s : Vec3) θ 2
        + (s : Vec3).2.2 * U (s : Vec3) θ 3)

theorem continuous_axis_coord_1 : Continuous fun p : Sph × ℝ => ((p.1 : Vec3)).1 :=
  continuous_fst.comp (continuous_subtype_val.comp continuous_fst)

theorem continuous_axis_coord_2 : Continuous fun p : Sph × ℝ => ((p.1 : Vec3)).2.1 :=
  continuous_fst.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))

theorem continuous_axis_coord_3 : Continuous fun p : Sph × ℝ => ((p.1 : Vec3)).2.2 :=
  continuous_snd.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))

theorem continuous_recA {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) :
    Continuous fun p : Sph × ℝ => recA U p.1 p.2 := by
  have h0 := hU.coord_continuous 0
  have h4 := hU.coord_continuous 4
  have h5 := hU.coord_continuous 5
  have h6 := hU.coord_continuous 6
  have hcos : Continuous fun p : Sph × ℝ => Real.cos (p.2 / 2) :=
    Real.continuous_cos.comp (continuous_snd.div_const 2)
  have hsin : Continuous fun p : Sph × ℝ => Real.sin (p.2 / 2) :=
    Real.continuous_sin.comp (continuous_snd.div_const 2)
  exact (hcos.mul h0).sub (hsin.mul
    (((continuous_axis_coord_1.mul h6).sub (continuous_axis_coord_2.mul h5)).add
      (continuous_axis_coord_3.mul h4)))

theorem continuous_recB {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) :
    Continuous fun p : Sph × ℝ => recB U p.1 p.2 := by
  have h7 := hU.coord_continuous 7
  have h1 := hU.coord_continuous 1
  have h2 := hU.coord_continuous 2
  have h3 := hU.coord_continuous 3
  have hcos : Continuous fun p : Sph × ℝ => Real.cos (p.2 / 2) :=
    Real.continuous_cos.comp (continuous_snd.div_const 2)
  have hsin : Continuous fun p : Sph × ℝ => Real.sin (p.2 / 2) :=
    Real.continuous_sin.comp (continuous_snd.div_const 2)
  exact (hcos.mul h7).add (hsin.mul
    (((continuous_axis_coord_1.mul h1).add (continuous_axis_coord_2.mul h2)).add
      (continuous_axis_coord_3.mul h3)))

/-- **DERIVED.**  The two explicit expressions really are the two coefficients of the
central residual of the family. -/
theorem recA_recB_eq {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) (s : Sph) (θ : ℝ) :
    recA U s θ = Real.exp (rateAlpha U (s : Vec3) * θ) *
        Real.cos (rateBeta U (s : Vec3) * θ) ∧
      recB U s θ = Real.exp (rateAlpha U (s : Vec3) * θ) *
        Real.sin (rateBeta U (s : Vec3) * θ) := by
  have hspec := regularFamily_param_spec hU.toRegularFamily s.2 θ
  have hzc : U (s : Vec3) θ
      = zc (Real.exp (rateAlpha U (s : Vec3) * θ) * Real.cos (rateBeta U (s : Vec3) * θ))
          (Real.exp (rateAlpha U (s : Vec3) * θ) * Real.sin (rateBeta U (s : Vec3) * θ))
        ⋆ Un (s : Vec3) θ := by
    rw [hspec, zexp]
  have h := residual_coeffs_of_coords s.2
    (Real.exp (rateAlpha U (s : Vec3) * θ) * Real.cos (rateBeta U (s : Vec3) * θ))
    (Real.exp (rateAlpha U (s : Vec3) * θ) * Real.sin (rateBeta U (s : Vec3) * θ)) θ
  rw [← hzc] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-! ## Work Package 2 — necessity: both recovered rates are continuous -/

/-- **PRINCIPAL THEOREM (Work Package 2), first rate.**  Joint continuity forces the first
recovered central rate to be a continuous function of the direction. -/
theorem jointlyRegular_alpha_continuous {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) :
    Continuous fun s : Sph => rateAlpha U (s : Vec3) := by
  have hsq : ∀ s : Sph,
      recA U s 1 ^ 2 + recB U s 1 ^ 2 = Real.exp (2 * rateAlpha U (s : Vec3)) := by
    intro s
    obtain ⟨ha, hb⟩ := recA_recB_eq hU s 1
    rw [ha, hb]
    have hpy := Real.sin_sq_add_cos_sq (rateBeta U (s : Vec3) * 1)
    have hexp2 : Real.exp (rateAlpha U (s : Vec3) * 1) * Real.exp (rateAlpha U (s : Vec3) * 1)
        = Real.exp (2 * rateAlpha U (s : Vec3)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← hexp2]
    linear_combination (Real.exp (rateAlpha U (s : Vec3) * 1)) ^ 2 * hpy
  have hpos : ∀ s : Sph, 0 < recA U s 1 ^ 2 + recB U s 1 ^ 2 := by
    intro s; rw [hsq s]; exact Real.exp_pos _
  have hcont : Continuous fun s : Sph => recA U s 1 ^ 2 + recB U s 1 ^ 2 := by
    have hpair : Continuous fun s : Sph => ((s, (1 : ℝ)) : Sph × ℝ) :=
      continuous_id.prodMk continuous_const
    have hA' := (continuous_recA hU).comp hpair
    have hB' := (continuous_recB hU).comp hpair
    have heA : ((fun p : Sph × ℝ => recA U p.1 p.2) ∘ fun s : Sph => ((s, (1 : ℝ)) : Sph × ℝ))
        = fun s : Sph => recA U s 1 := by funext s; rfl
    have heB : ((fun p : Sph × ℝ => recB U p.1 p.2) ∘ fun s : Sph => ((s, (1 : ℝ)) : Sph × ℝ))
        = fun s : Sph => recB U s 1 := by funext s; rfl
    rw [heA] at hA'
    rw [heB] at hB'
    exact (hA'.pow 2).add (hB'.pow 2)
  have heq : (fun s : Sph => rateAlpha U (s : Vec3))
      = fun s : Sph => Real.log (recA U s 1 ^ 2 + recB U s 1 ^ 2) / 2 := by
    funext s
    rw [hsq s, Real.log_exp]
    ring
  rw [heq]
  exact (hcont.log fun s => ne_of_gt (hpos s)).div_const 2

/-- **PRINCIPAL THEOREM (Work Package 2), second rate.**  Joint continuity forces the
second recovered central rate to be a continuous function of the direction as well.  This
is the substantive half: the second rate is only determined *through* the whole parameter
family, and its continuity is not a formal consequence of continuity at one parameter. -/
theorem jointlyRegular_beta_continuous {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) :
    Continuous fun s : Sph => rateBeta U (s : Vec3) := by
  have hα := jointlyRegular_alpha_continuous hU
  have hexp : Continuous fun p : Sph × ℝ =>
      Real.exp (-(rateAlpha U (p.1 : Vec3) * p.2)) :=
    Real.continuous_exp.comp (((hα.comp continuous_fst).mul continuous_snd).neg)
  refine continuous_of_joint_circle (b := fun s : Sph => rateBeta U (s : Vec3)) ?_ ?_
  · have he : (fun p : Sph × ℝ => Real.cos (rateBeta U (p.1 : Vec3) * p.2))
        = fun p : Sph × ℝ => recA U p.1 p.2 *
            Real.exp (-(rateAlpha U (p.1 : Vec3) * p.2)) := by
      funext p
      rw [(recA_recB_eq hU p.1 p.2).1, mul_right_comm, ← Real.exp_add]
      simp
    rw [he]
    exact (continuous_recA hU).mul hexp
  · have he : (fun p : Sph × ℝ => Real.sin (rateBeta U (p.1 : Vec3) * p.2))
        = fun p : Sph × ℝ => recB U p.1 p.2 *
            Real.exp (-(rateAlpha U (p.1 : Vec3) * p.2)) := by
      funext p
      rw [(recA_recB_eq hU p.1 p.2).2, mul_right_comm, ← Real.exp_add]
      simp
    rw [he]
    exact (continuous_recB hU).mul hexp

/-! ## Work Package 2 — sufficiency -/

/-- **PRINCIPAL THEOREM (Work Package 2), converse.**  Every pair of rate functions that is
continuous on the unit directions produces a jointly regular family. -/
theorem jointlyRegular_famOf {a b : Vec3 → ℝ} (ha : Continuous fun s : Sph => a (s : Vec3))
    (hb : Continuous fun s : Sph => b (s : Vec3)) :
    IsJointlyRegularFamily (famOf a b) := by
  refine ⟨fun n hn => ((continuousAxisLift_classification hn _).2 ⟨a n, b n, fun _ => rfl⟩).1,
    ?_⟩
  have he : (fun p : Sph × ℝ => famOf a b (p.1 : Vec3) p.2) = fun p : Sph × ℝ =>
      (Real.exp (a (p.1 : Vec3) * p.2) * Real.cos (b (p.1 : Vec3) * p.2) *
          Real.cos (p.2 / 2)) • w1
      + (Real.exp (a (p.1 : Vec3) * p.2) * Real.sin (b (p.1 : Vec3) * p.2) *
          Real.cos (p.2 / 2)) • wS
      + (-(Real.exp (a (p.1 : Vec3) * p.2) * Real.cos (b (p.1 : Vec3) * p.2) *
          Real.sin (p.2 / 2))) • Jmap (p.1 : Vec3)
      + (Real.exp (a (p.1 : Vec3) * p.2) * Real.sin (b (p.1 : Vec3) * p.2) *
          Real.sin (p.2 / 2)) • spat (p.1 : Vec3) := by
    funext p
    exact zc_mul_Un (p.1 : Vec3) _ _ p.2
  rw [he]
  have hA : Continuous fun p : Sph × ℝ => a (p.1 : Vec3) := ha.comp continuous_fst
  have hB : Continuous fun p : Sph × ℝ => b (p.1 : Vec3) := hb.comp continuous_fst
  have hJ : Continuous fun p : Sph × ℝ => Jmap (p.1 : Vec3) := by
    have : Continuous fun n : Vec3 => Jmap n := by
      refine continuous_pi (fun i => ?_)
      fin_cases i <;> simp [Jmap, wP, wQ, wR] <;> fun_prop
    exact this.comp (continuous_sph_val.comp continuous_fst)
  have hS : Continuous fun p : Sph × ℝ => spat (p.1 : Vec3) := by
    have : Continuous fun n : Vec3 => spat n := by
      refine continuous_pi (fun i => ?_)
      fin_cases i <;> simp [spat, sp] <;> fun_prop
    exact this.comp (continuous_sph_val.comp continuous_fst)
  have hE : Continuous fun p : Sph × ℝ => Real.exp (a (p.1 : Vec3) * p.2) :=
    Real.continuous_exp.comp (hA.mul continuous_snd)
  have hCb : Continuous fun p : Sph × ℝ => Real.cos (b (p.1 : Vec3) * p.2) :=
    Real.continuous_cos.comp (hB.mul continuous_snd)
  have hSb : Continuous fun p : Sph × ℝ => Real.sin (b (p.1 : Vec3) * p.2) :=
    Real.continuous_sin.comp (hB.mul continuous_snd)
  have hCh : Continuous fun p : Sph × ℝ => Real.cos (p.2 / 2) :=
    Real.continuous_cos.comp (continuous_snd.div_const 2)
  have hSh : Continuous fun p : Sph × ℝ => Real.sin (p.2 / 2) :=
    Real.continuous_sin.comp (continuous_snd.div_const 2)
  have c1 : Continuous fun p : Sph × ℝ => Real.exp (a (p.1 : Vec3) * p.2) *
      Real.cos (b (p.1 : Vec3) * p.2) * Real.cos (p.2 / 2) := (hE.mul hCb).mul hCh
  have c2 : Continuous fun p : Sph × ℝ => Real.exp (a (p.1 : Vec3) * p.2) *
      Real.sin (b (p.1 : Vec3) * p.2) * Real.cos (p.2 / 2) := (hE.mul hSb).mul hCh
  have c3 : Continuous fun p : Sph × ℝ => -(Real.exp (a (p.1 : Vec3) * p.2) *
      Real.cos (b (p.1 : Vec3) * p.2) * Real.sin (p.2 / 2)) := ((hE.mul hCb).mul hSh).neg
  have c4 : Continuous fun p : Sph × ℝ => Real.exp (a (p.1 : Vec3) * p.2) *
      Real.sin (b (p.1 : Vec3) * p.2) * Real.sin (p.2 / 2) := (hE.mul hSb).mul hSh
  exact (((c1.smul continuous_const).add (c2.smul continuous_const)).add
    (c3.smul hJ)).add (c4.smul hS)

/-- **PRINCIPAL THEOREM (Work Package 2): the exact classification.**  Jointly regular
families are *exactly* the exponential–rotation multiples of the inherited reference
implementations whose two rate functions are continuous on the unit directions.  Neither a
weaker combination nor a more general phenomenon survives, and no refinement of the
one-axis `α`/`β` parametrization is needed. -/
theorem jointRegularity_classification (U : Vec3 → ℝ → W) :
    IsJointlyRegularFamily U ↔
      ∃ a b : Vec3 → ℝ, (Continuous fun s : Sph => a (s : Vec3)) ∧
        (Continuous fun s : Sph => b (s : Vec3)) ∧
        ∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, U n θ = zexp (a n) (b n) θ ⋆ Un n θ := by
  constructor
  · intro hU
    exact ⟨rateAlpha U, rateBeta U, jointlyRegular_alpha_continuous hU,
      jointlyRegular_beta_continuous hU,
      fun n hn θ => regularFamily_param_spec hU.toRegularFamily hn θ⟩
  · rintro ⟨a, b, ha, hb, hUe⟩
    have hfam := jointlyRegular_famOf ha hb
    refine ⟨fun n hn => ?_, ?_⟩
    · have : U n = famOf a b n := funext fun θ => hUe n hn θ
      rw [this]
      exact hfam.lift n hn
    · have he : (fun p : Sph × ℝ => U (p.1 : Vec3) p.2)
          = fun p : Sph × ℝ => famOf a b (p.1 : Vec3) p.2 := by
        funext p
        exact hUe (p.1 : Vec3) p.1.2 p.2
      rw [he]
      exact hfam.joint

end NullSectorTask16
