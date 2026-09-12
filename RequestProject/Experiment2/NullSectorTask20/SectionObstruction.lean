import RequestProject.Experiment2.NullSectorTask20.GlobalObstruction

/-!
# Task 20, Layer 7 (Packages C, G, H): internal choices over the visible quotient

Phase A only.  This module contains the sharpest new Task-20 statement:

* a **quotient-compatible internal choice exists** set-theoretically — there is a map from
  the parameter carrier to the internal core carrier which lifts the visible map and is
  constant on the classes of visible equality;
* **no such choice is continuous**.  The proof uses only: the core relative-factor theorem
  (the ambiguity is exactly a sign), connectedness of the parameter carrier, and the value
  of a reference implementer after a full turn.

Together these locate the whole global phenomenon in one place: the failure is continuity of
an internal choice over the visible quotient, not the existence of the choice.

The module closes by re-exporting, unchanged, the inherited equivalences between relation
completeness, primitive global bridges, and global exact representability, so that they can
be read against the Task-20 packaging.
-/

namespace NullSectorTask20

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19

instance instConnectedSph : ConnectedSpace Sph where
  toPreconnectedSpace := inferInstance
  toNonempty := ⟨⟨e1, e1_isUnitAxis⟩⟩

/-! ## The inherited pairing and the normalization of a reference implementer -/

/-- **NEUTRAL DEFINITION.**  The coordinate pairing of the inherited carrier. -/
def dotW (u v : W) : ℝ := ∑ i, u i * v i

theorem continuous_dotW {X : Type*} [TopologicalSpace X] {f g : X → W} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => dotW (f x) (g x) := by
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((continuous_apply i).comp hf).mul ((continuous_apply i).comp hg)

theorem dotW_Un_self {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) : dotW (Un n θ) (Un n θ) = 1 := by
  have hnn : n.1 ^ 2 + n.2.1 ^ 2 + n.2.2 ^ 2 = 1 := by
    have h := hn
    simp only [IsUnitAxis, h3, dot3] at h
    nlinarith [h]
  have hpy := Real.sin_sq_add_cos_sq (θ / 2)
  simp only [dotW, Fin.sum_univ_eight, Un, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, w1,
    Jmap, wP, wQ, wR]
  simp
  nlinarith [hnn, hpy]

theorem dotW_neg_left (u v : W) : dotW (-u) v = -dotW u v := by
  simp only [dotW, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-! ## A quotient-compatible internal choice exists -/

/-- **PACKAGE H, principal (positive half).**  There **is** a map from the parameter carrier
to the internal core carrier which lifts the visible map and is constant on the classes of
visible equality.  Nothing but choice of a representative in each class is used. -/
theorem exists_quotient_compatible_lift :
    ∃ σ : VisParam → W, (∀ p : VisParam, σ p ∈ Lift) ∧
      (∀ p : VisParam, proj (σ p) = visMap p) ∧
      (∀ p q : VisParam, visRel p q → σ p = σ q) := by
  classical
  refine ⟨fun p => Un ((Quotient.out (visClass p)).1 : Vec3) (Quotient.out (visClass p)).2,
    ?_, ?_, ?_⟩
  · intro p
    exact Un_mem_Lift (Quotient.out (visClass p)).1.2 _
  · intro p
    have hrep : visClass (Quotient.out (visClass p)) = visClass p :=
      Quotient.out_eq (visClass p)
    have hrel : visRel (Quotient.out (visClass p)) p := visClass_eq_iff.1 hrep
    rw [proj_Un (Quotient.out (visClass p)).1.2]
    exact hrel
  · intro p q hpq
    have hcl : visClass p = visClass q := visClass_eq_iff.2 hpq
    simp only [hcl]

/-! ## No quotient-compatible internal choice is continuous -/

/-- **PACKAGE C/G/H, principal (negative half).**  No quotient-compatible internal choice is
continuous.  The three ingredients are: the relative factor between two core lifts of the
same visible datum is exactly a sign; the parameter carrier is connected; and a full turn of
the parameter changes the reference implementer by that sign. -/
theorem no_continuous_quotient_compatible_lift :
    ¬ ∃ σ : VisParam → W, Continuous σ ∧ (∀ p : VisParam, σ p ∈ Lift) ∧
      (∀ p : VisParam, proj (σ p) = visMap p) ∧
      (∀ p q : VisParam, visRel p q → σ p = σ q) := by
  rintro ⟨σ, hcont, hmem, hproj, hdesc⟩
  -- the ambiguity is exactly a sign
  have hsign : ∀ p : VisParam, σ p = Un (p.1 : Vec3) p.2 ∨ σ p = -Un (p.1 : Vec3) p.2 := by
    intro p
    refine relative_factor_core (hmem p) (Un_mem_Lift p.1.2 p.2) ?_
    rw [hproj p, visMap_eq_proj p]
  -- the sign, read off by the coordinate pairing, is continuous
  set g : VisParam → ℝ := fun p => dotW (σ p) (Un (p.1 : Vec3) p.2) with hg
  have hUncont : Continuous fun p : VisParam => Un (p.1 : Vec3) p.2 :=
    continuous_Un_comp (continuous_subtype_val.comp continuous_fst) continuous_snd
  have hgcont : Continuous g := continuous_dotW hcont hUncont
  have hgval : ∀ p : VisParam, g p = 1 ∨ g p = -1 := by
    intro p
    rcases hsign p with h | h
    · left; rw [hg]; simp only; rw [h, dotW_Un_self p.1.2 p.2]
    · right; rw [hg]; simp only; rw [h, dotW_neg_left, dotW_Un_self p.1.2 p.2]
  have hgne : ∀ p : VisParam, g p ≠ 0 := by
    intro p hp
    rcases hgval p with h | h <;> rw [h] at hp <;> norm_num at hp
  -- hence constant
  have hgconst : ∀ p q : VisParam, g p = g q := by
    intro p q
    by_contra hne
    rcases hgval p with h1 | h1 <;> rcases hgval q with h2 | h2
    · exact hne (h1.trans h2.symm)
    · obtain ⟨t, ht⟩ := intermediate_value_univ q p hgcont
        (show (0 : ℝ) ∈ Set.Icc (g q) (g p) from
          Set.mem_Icc.2 ⟨by rw [h2]; norm_num, by rw [h1]; norm_num⟩)
      exact hgne t ht
    · obtain ⟨t, ht⟩ := intermediate_value_univ p q hgcont
        (show (0 : ℝ) ∈ Set.Icc (g p) (g q) from
          Set.mem_Icc.2 ⟨by rw [h1]; norm_num, by rw [h2]; norm_num⟩)
      exact hgne t ht
    · exact hne (h1.trans h2.symm)
  -- evaluate on a full turn
  set s : Sph := ⟨e1, e1_isUnitAxis⟩ with hs
  have hzero : σ (s, (0 : ℝ)) = g (s, (0 : ℝ)) • w1 := by
    rcases hsign (s, (0 : ℝ)) with h | h
    · have hgv : g (s, (0 : ℝ)) = 1 := by
        rw [hg]; simp only; rw [h, dotW_Un_self s.2]
      rw [h, hgv, Un_zero, one_smul]
    · have hgv : g (s, (0 : ℝ)) = -1 := by
        rw [hg]; simp only; rw [h, dotW_neg_left, dotW_Un_self s.2]
      rw [h, hgv, Un_zero]
      module
  have hturn : σ (s, 2 * Real.pi) = -(g (s, 2 * Real.pi) • w1) := by
    rcases hsign (s, 2 * Real.pi) with h | h
    · have hgv : g (s, 2 * Real.pi) = 1 := by
        rw [hg]; simp only; rw [h, dotW_Un_self s.2]
      rw [h, hgv, Un_two_pi, one_smul]
    · have hgv : g (s, 2 * Real.pi) = -1 := by
        rw [hg]; simp only; rw [h, dotW_neg_left, dotW_Un_self s.2]
      rw [h, hgv, Un_two_pi]
      module
  have hrel : visRel (s, (0 : ℝ)) (s, 2 * Real.pi) := by
    show PhiGen (s : Vec3) 0 = PhiGen (s : Vec3) (2 * Real.pi)
    refine phiGen_eq_of_signRelated ⟨-1, Or.inr rfl, ?_⟩
    rw [Un_zero, Un_two_pi]
    module
  have hEq : σ (s, (0 : ℝ)) = σ (s, 2 * Real.pi) := hdesc _ _ hrel
  rw [hzero, hturn, hgconst (s, (0 : ℝ)) (s, 2 * Real.pi)] at hEq
  have hw : (w1 : W) 0 = 1 := by simp [w1]
  have h0 := congrFun hEq 0
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hw, mul_one] at h0
  exact hgne (s, 2 * Real.pi) (by linarith)

/-! ## Inherited equivalences, re-exported for the Task-20 packaging -/

/-- **PACKAGE H (items 65–71).**  The inherited relation-completeness equivalences, preserved
verbatim: only the reversal-related coincidence class is nonautomatic, relation completeness
of a locally exact open covering system is equivalent to existence of a primitive global
bridge with globally exact reconstruction, and the global obstruction is exactly relation
incompleteness. -/
theorem relation_completeness_package :
    ((∃ (ι : Type) (D : ι → Set Vec3) (U : ι → Vec3 → ℝ → W),
          IsLocalSystem D U ∧ SystemRelationComplete D U) ↔
        ∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsTransformationValued (recon c)) ∧
      (¬ ∃ (ι : Type) (D : ι → Set Vec3) (U : ι → Vec3 → ℝ → W),
        IsLocalSystem D U ∧ SystemRelationComplete D U) ∧
      (∀ U : Vec3 → ℝ → W, IsJointlyRegularFamily U → RateZeroHalfOdd U →
        (IsRelationComplete U ↔ AntipodalRelated U)) :=
  ⟨relationComplete_system_iff_primitiveBridge,
    global_obstruction_is_relation_incompleteness.1,
    fun _ hU hr => relationComplete_iff_antipodalRelated hU hr⟩

end NullSectorTask20
