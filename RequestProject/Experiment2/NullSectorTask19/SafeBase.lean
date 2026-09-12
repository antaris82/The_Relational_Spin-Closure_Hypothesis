import RequestProject.Experiment2.NullSectorTask18.NegativeControls

/-!
# Task 19, Layer 0: the inherited (safe) base

## Import ledger (INHERITED)

* `RequestProject.Experiment2.NullSectorTask18.NegativeControls` — the last *reconstruction* layer of
  Task 18.  Through it, and only through it, Task 19 inherits the whole Task-18
  reconstruction development (Packages A–I and the Task-18 controls) and, transitively, the
  Task-17 and Task-16 reconstruction layers:

  * the associative carrier `W` with product `⋆`, unit `w1`, exact centre `Z`, the central
    one-parameter elements `zexp`, `zc`, the spatial carrier `Vec3` with the inherited form
    `h3`, the unit directions `IsUnitAxis`, the inherited subspace `Sph`, the reference
    implementations `Un n θ`, the visible family `PhiGen n θ`;
  * the exact coincidence classification `coincidence_iff`, `coincidence_iff_coords`;
  * joint regularity `IsJointlyRegularFamily`, the recovered rates `rateAlpha`, `rateBeta`,
    the presentation `famOf`, and the criterion `admissible_iff_exists_rate_function`;
  * the local layer `Dom`, `IsTransformationValuedOn`, `locFam`, the global sign-relaxed
    reference `refFam`, the relative factor `ovl`;
  * the Task-18 notions `IsHalfOdd`, `UnitSet`, `PreconnDomain`, `OpenDomain`,
    `IsMaximalIn`, `AdmClass`, `PreconnAdmClass`, `OpenConnAdmClass`, `AntipodalComplete`,
    `Bridge`, `IsGlobalBridge`, `Coincident`, `CoversRelations`, `IsC1AdmissibleDomain`,
    `lexA`, `lexB`, `multiD`, `signRate`, and all their proved properties.

**Reconstruction firewall.**  `RequestProject.Experiment2.NullSectorTask18.Identification` — the only
comparison module of Task 18 — is *not* imported here, nor by any other Task-19
reconstruction module; neither is `RequestProject.Experiment2.NullSectorTask18.Task18` (which imports
it).  The single Task-19 comparison module,
`RequestProject.Experiment2.NullSectorTask19.Identification`, is imported by nothing but
`RequestProject.Experiment2.NullSectorTask19.Task19`.

No conventional geometric or topological target is imported or used anywhere in the
Task-19 reconstruction modules: no rotation or double-cover group, no spinor, no covering
space, no bundle, no principal bundle, no Čech datum, no cocycle, no cohomology, no
connection, no holonomy, no gauge datum, no fundamental group, no projective
representation.  The words `open`, `closed`, `dense`, `connected`, `path`, `component` are
used in their bare point-set sense for the inherited subspace `Sph` of unit directions.  No
physical vocabulary occurs in any reconstruction statement.  No central factor, sign, or
local normalization is ever quotiented out.

## Content of this module

Bookkeeping only, all of it about the inherited subspace `Sph`:

* the full set of unit directions and its elementary identities;
* non-degeneracy of the inherited renormalized segment between two non-opposite unit
  directions, and, from it, path-connectedness and preconnectedness of `Sph`;
* rigidity of a continuous half-odd-valued rate on all of `Sph` (it is constant), and the
  limit stability of half-oddness (a continuous rate that is half-odd on a set is half-odd
  on its closure);
* the three rate conditions `RateCont`, `RateHalfOdd`, `RateRev` named separately, together
  with the explicit witnesses used later as negative controls.
-/

namespace NullSectorTask19

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18

/-! ## Continuity of the inherited product -/

/-- **DERIVED.**  The inherited carrier product is continuous in both arguments: the
coordinates of a product are polynomials in the coordinates of the factors. -/
theorem continuous_starW {X : Type*} [TopologicalSpace X] {f g : X → W} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => f x ⋆ g x := by
  have hfi : ∀ j, Continuous fun x => f x j := fun j => (continuous_apply j).comp hf
  have hgi : ∀ j, Continuous fun x => g x j := fun j => (continuous_apply j).comp hg
  rw [continuous_pi_iff]
  intro i
  fin_cases i <;> simp only [wit8Mul_apply, wit8MulFun] <;> simp <;> fun_prop

/-! ## The full set of unit directions -/

/-- **NEUTRAL DEFINITION.**  The set of all unit directions. -/
def allUnit : Set Vec3 := {n : Vec3 | IsUnitAxis n}

theorem mem_allUnit {n : Vec3} : n ∈ allUnit ↔ IsUnitAxis n := Iff.rfl

theorem allUnit_unitSet : UnitSet allUnit := fun _ h => h

theorem sphSet_allUnit : sphSet allUnit = (Set.univ : Set Sph) := by
  ext s; exact ⟨fun _ => trivial, fun _ => s.2⟩

/-! ## The renormalized segment between two non-opposite unit directions -/

/-- **DERIVED.**  For two unit directions which are not opposite, the straight segment
between them never passes through the origin. -/
theorem segLin_ne_zero_of_ne_neg {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m)
    (hne : m ≠ -n) (t : ℝ) : segLin n m t ≠ 0 := by
  intro hz
  have hnn : h3 n n = 1 := hn
  have hmm : h3 m m = 1 := hm
  have h0 : h3 (0 : Vec3) n = 0 := by simp [h3, dot3]
  have h0' : h3 (0 : Vec3) m = 0 := by simp [h3, dot3]
  have e1 : (1 - t) * h3 n n + t * h3 m n = 0 := by
    rw [← h3_segLin_left n m n t, hz, h0]
  have e2 : (1 - t) * h3 n m + t * h3 m m = 0 := by
    rw [← h3_segLin_left n m m t, hz, h0']
  rw [hnn] at e1
  rw [hmm] at e2
  rw [h3_comm m n] at e1
  set c : ℝ := h3 n m with hc
  -- `(1 - c) * (1 - 2 t) = 0`
  have hfac : (1 - c) * (1 - 2 * t) = 0 := by nlinarith [e1, e2]
  rcases mul_eq_zero.1 hfac with h | h
  · have hc1 : c = 1 := by linarith
    rw [hc1] at e1
    linarith
  · have ht2 : t = 1 / 2 := by linarith
    rw [ht2] at hz
    have : m = -n := by
      have hz' : (1 / 2 : ℝ) • (n + m) = 0 := by
        rw [← hz, segLin]; module
      have hsum : n + m = 0 := by
        have := congrArg (fun w : Vec3 => (2 : ℝ) • w) hz'
        simpa using this
      have := congrArg (fun w : Vec3 => w - n) hsum
      simpa using this
    exact hne this

/-- **DERIVED.**  Two non-opposite unit directions are joined inside the inherited
subspace of unit directions, by the explicit renormalized segment. -/
theorem joined_of_ne_neg {n m : Vec3} (hn : IsUnitAxis n) (hm : IsUnitAxis m) (hne : m ≠ -n) :
    JoinedIn (sphSet allUnit) ⟨n, hn⟩ ⟨m, hm⟩ :=
  joinedIn_segPath hn hm (fun t _ => segLin_ne_zero_of_ne_neg hn hm hne t)
    (fun t _ => segPath_isUnitAxis (segLin_ne_zero_of_ne_neg hn hm hne t))

/-- **DERIVED.**  The inherited subspace of unit directions is path-connected.  The proof
uses only the explicit renormalized segment and the inherited existence of an orthogonal
unit direction; no sphere theorem is imported. -/
theorem sph_isPathConnected : IsPathConnected (sphSet allUnit) := by
  refine ⟨⟨e1, e1_isUnitAxis⟩, e1_isUnitAxis, ?_⟩
  intro s _
  have hs : IsUnitAxis (s : Vec3) := s.2
  by_cases hne : (s : Vec3) ≠ -e1
  · have := joined_of_ne_neg e1_isUnitAxis hs hne
    exact this
  · push_neg at hne
    obtain ⟨k, hku, hk0⟩ := exists_unit_orthogonal e1_isUnitAxis
    have hkne : k ≠ -e1 := by
      intro hk
      have : h3 e1 k = -1 := by rw [hk, h3_comm, h3_neg_left]; rw [h3_comm]; exact congrArg Neg.neg e1_isUnitAxis
      rw [hk0] at this
      norm_num at this
    have h1 : JoinedIn (sphSet allUnit) ⟨e1, e1_isUnitAxis⟩ ⟨k, hku⟩ :=
      joined_of_ne_neg e1_isUnitAxis hku hkne
    have hsne : (s : Vec3) ≠ -k := by
      rw [hne]
      intro hcon
      have : k = e1 := by
        have := congrArg (fun w : Vec3 => -w) hcon
        simpa using this.symm
      rw [this] at hk0
      have : h3 e1 e1 = 1 := e1_isUnitAxis
      rw [hk0] at this
      norm_num at this
    have h2 : JoinedIn (sphSet allUnit) ⟨k, hku⟩ ⟨(s : Vec3), hs⟩ :=
      joined_of_ne_neg hku hs hsne
    exact h1.trans h2

theorem sph_isPreconnected : IsPreconnected (sphSet allUnit) :=
  sph_isPathConnected.isConnected.isPreconnected

theorem sph_univ_isPreconnected : IsPreconnected (Set.univ : Set Sph) := by
  have := sph_isPreconnected
  rwa [sphSet_allUnit] at this

/-! ## The reversal map on unit directions -/

/-- **NEUTRAL DEFINITION.**  Reversal of a unit direction. -/
def negSph (s : Sph) : Sph := ⟨-(s : Vec3), isUnitAxis_neg s.2⟩

theorem negSph_involutive : Function.Involutive negSph :=
  fun s => Subtype.ext (neg_neg (s : Vec3))

theorem continuous_negSph : Continuous negSph :=
  (continuous_neg.comp continuous_subtype_val).subtype_mk _

/-- **DERIVED.**  Reversal is a homeomorphism of the inherited subspace of unit
directions. -/
def negSphHomeo : Sph ≃ₜ Sph where
  toFun := negSph
  invFun := negSph
  left_inv := negSph_involutive
  right_inv := negSph_involutive
  continuous_toFun := continuous_negSph
  continuous_invFun := continuous_negSph

/-- **NEUTRAL DEFINITION.**  The reversed set of directions. -/
def negSet (D : Set Vec3) : Set Vec3 := {n : Vec3 | -n ∈ D}

theorem mem_negSet {D : Set Vec3} {n : Vec3} : n ∈ negSet D ↔ -n ∈ D := Iff.rfl

theorem sphSet_negSet (D : Set Vec3) : sphSet (negSet D) = negSph ⁻¹' sphSet D := rfl

theorem closure_sphSet_negSet (D : Set Vec3) :
    closure (sphSet (negSet D)) = negSph ⁻¹' closure (sphSet D) := by
  rw [sphSet_negSet]
  exact (negSphHomeo.preimage_closure (sphSet D)).symm

/-! ## Rigidity of a continuous half-odd rate -/

/-- **DERIVED.**  A rate function continuous on the unit directions and half-odd at *every*
unit direction is constant. -/
theorem halfOdd_const_on_sph {b : Vec3 → ℝ} (hb : Continuous fun s : Sph => b (s : Vec3))
    (hhalf : ∀ n : Vec3, IsUnitAxis n → IsHalfOdd (b n)) {n m : Vec3} (hn : IsUnitAxis n)
    (hm : IsUnitAxis m) : b n = b m := by
  have hconst := halfodd_const_of_preconnected sph_univ_isPreconnected
    (f := fun s : Sph => b (s : Vec3)) hb.continuousOn
    (fun s _ => hhalf (s : Vec3) s.2)
  exact hconst ⟨n, hn⟩ trivial ⟨m, hm⟩ trivial

/-- **DERIVED.**  Half-oddness of a continuous rate passes to the closure: if a rate is
continuous on the unit directions and half-odd on a set `D`, it is half-odd at every
direction in the closure of `D`. -/
theorem halfOdd_of_mem_closure {b : Vec3 → ℝ} (hb : Continuous fun s : Sph => b (s : Vec3))
    {D : Set Vec3} (hhalf : ∀ n ∈ D, IsHalfOdd (b n)) {p : Sph}
    (hp : p ∈ closure (sphSet D)) : IsHalfOdd (b (p : Vec3)) := by
  obtain ⟨δ₀, hδ₀, hball₀⟩ := Metric.continuous_iff.1 hb p (1 / 4) (by norm_num)
  obtain ⟨s₀, hs₀D, hs₀⟩ := Metric.mem_closure_iff.1 hp δ₀ hδ₀
  have hs₀' : dist s₀ p < δ₀ := by rwa [dist_comm] at hs₀
  have hb₀ : |b (s₀ : Vec3) - b (p : Vec3)| < 1 / 4 := by
    have := hball₀ s₀ hs₀'
    rwa [Real.dist_eq] at this
  have key : b (p : Vec3) = b (s₀ : Vec3) := by
    by_contra hne
    set ε : ℝ := |b (s₀ : Vec3) - b (p : Vec3)| with hεdef
    have hε : 0 < ε := abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
    obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hb p (min ε (1 / 4))
      (lt_min hε (by norm_num))
    obtain ⟨s, hsD, hs⟩ := Metric.mem_closure_iff.1 hp (min δ δ₀) (lt_min hδ hδ₀)
    have hs' : dist s p < δ := lt_of_lt_of_le (by rwa [dist_comm] at hs) (min_le_left _ _)
    have h1 : |b (s : Vec3) - b (p : Vec3)| < min ε (1 / 4) := by
      have := hball s hs'
      rwa [Real.dist_eq] at this
    have heq : b (s : Vec3) = b (s₀ : Vec3) := by
      refine halfOdd_eq_of_close (hhalf _ hsD) (hhalf _ hs₀D) ?_
      have h2 : |b (s : Vec3) - b (s₀ : Vec3)|
          ≤ |b (s : Vec3) - b (p : Vec3)| + |b (s₀ : Vec3) - b (p : Vec3)| := by
        have hrw : b (s : Vec3) - b (s₀ : Vec3)
            = (b (s : Vec3) - b (p : Vec3)) - (b (s₀ : Vec3) - b (p : Vec3)) := by ring
        rw [hrw]; exact abs_sub _ _
      have := lt_of_lt_of_le h1 (min_le_right _ _)
      linarith
    rw [heq] at h1
    have hfin := lt_of_lt_of_le h1 (min_le_left _ _)
    rw [← hεdef] at hfin
    exact absurd hfin (lt_irrefl ε)
  rw [key]
  exact hhalf _ hs₀D

/-! ## The three rate conditions, named separately -/

/-- **NEUTRAL DEFINITION.**  Continuity of a rate function on the unit directions. -/
def RateCont (b : Vec3 → ℝ) : Prop := Continuous fun s : Sph => b (s : Vec3)

/-- **NEUTRAL DEFINITION.**  Half-oddness of a rate function at every unit direction. -/
def RateHalfOdd (b : Vec3 → ℝ) : Prop := ∀ n : Vec3, IsUnitAxis n → IsHalfOdd (b n)

/-- **NEUTRAL DEFINITION.**  Oddness of a rate function under reversal of the direction. -/
def RateRev (b : Vec3 → ℝ) : Prop := ∀ n : Vec3, IsUnitAxis n → b (-n) = -b n

/-! ### The three explicit witnesses -/

/-- **NEUTRAL DEFINITION.**  The identically vanishing rate: continuous and reversal-odd,
not half-odd. -/
def rateZero : Vec3 → ℝ := fun _ => 0

/-- **NEUTRAL DEFINITION.**  The constant rate `1/2`: continuous and half-odd, not
reversal-odd. -/
noncomputable def rateHalf : Vec3 → ℝ := fun _ => 1 / 2

theorem rateZero_cont : RateCont rateZero := continuous_const
theorem rateZero_rev : RateRev rateZero := fun _ _ => by norm_num [rateZero]

theorem rateZero_not_halfOdd : ¬ RateHalfOdd rateZero := by
  intro h
  obtain ⟨k, hk⟩ := h e1 e1_isUnitAxis
  have h2 : (2 * k : ℤ) = -1 := by
    have : (2 * (k : ℝ)) = -1 := by
      have h0 : (0 : ℝ) = (k : ℝ) + 1 / 2 := hk
      linarith
    exact_mod_cast this
  omega

theorem rateHalf_cont : RateCont rateHalf := continuous_const
theorem rateHalf_halfOdd : RateHalfOdd rateHalf := fun _ _ => ⟨0, by norm_num [rateHalf]⟩

theorem rateHalf_not_rev : ¬ RateRev rateHalf := by
  intro h
  have := h e1 e1_isUnitAxis
  norm_num [rateHalf] at this

theorem signRate_halfOdd' : RateHalfOdd signRate := fun n _ => signRate_halfOdd n
theorem signRate_rev : RateRev signRate := fun _ hn => signRate_odd hn

theorem signRate_not_cont : ¬ RateCont signRate := by
  intro hcont
  exact no_global_halfodd_odd_rate
    ⟨signRate, hcont, fun n _ => signRate_halfOdd n, fun n hn => signRate_odd hn⟩

end NullSectorTask19
