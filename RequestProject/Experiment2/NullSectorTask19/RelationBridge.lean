import RequestProject.Experiment2.NullSectorTask19.RelationCompletion

/-!
# Task 19, Package H: relation completion versus the primitive global bridge

An *indexed local system* is a family of open sets of unit directions, each carrying its own
jointly regular family which is exactly transformation-valued on it, together covering every
unit direction (§67).  On top of the ordinary overlap data we add exactly the cross-domain
comparison data isolated in Package G: full visible-relation compatibility.

* §68.  *Sufficiency.*  Complete visible-relation compatibility of such a system **is**
  enough to construct one primitive global bridge; the construction glues the recovered
  directional rates and is proved continuous from openness alone.
* §69.  *Necessity.*  Existence of one primitive global bridge with globally exact
  reconstruction returns a relation-complete system.
* §70.  Both directions hold, so the equivalence is genuine — and it is proved
  constructively in both directions, not by `ex falso`.
* §71.  The explicit counterexample: the inherited system has coherent ordinary overlaps and
  satisfies the same-direction and identity-degenerate relation classes, yet fails the
  antipodal class, and global bridge reconstruction fails for it.
* §72.  Consequently the global obstruction can be restated **purely** as failure of
  complete visible-relation compatibility.

No conventional groupoid, bundle, covering or cocycle language is used anywhere below.
-/

namespace NullSectorTask19

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18

/-! ## §67 — indexed local systems -/

/-- **NEUTRAL DEFINITION (§67).**  A locally exact indexed system of open domains covering
every unit direction. -/
structure IsLocalSystem {ι : Type*} (D : ι → Set Vec3) (U : ι → Vec3 → ℝ → W) : Prop where
  /-- each domain consists of unit directions -/
  unit : ∀ i : ι, UnitSet (D i)
  /-- each domain is open in the unit-direction space -/
  isOpen : ∀ i : ι, IsOpen (sphSet (D i))
  /-- each local member is jointly regular -/
  regular : ∀ i : ι, IsJointlyRegularFamily (U i)
  /-- each local member is exact on its own domain -/
  exact : ∀ i : ι, IsTransformationValuedOn (D i) (U i)
  /-- the domains cover every unit direction -/
  covers : ∀ n : Vec3, IsUnitAxis n → ∃ i : ι, n ∈ D i

/-- **NEUTRAL DEFINITION (§67).**  Ordinary overlap coherence: on a common direction the two
local members agree.  This is strictly weaker than relation completeness. -/
def CoherentOverlaps {ι : Type*} (D : ι → Set Vec3) (U : ι → Vec3 → ℝ → W) : Prop :=
  ∀ (i j : ι) (n : Vec3), n ∈ D i → n ∈ D j → ∀ θ : ℝ, U i n θ = U j n θ

/-- **DERIVED.**  Relation completeness implies ordinary overlap coherence. -/
theorem coherentOverlaps_of_systemRelationComplete {ι : Type*} {D : ι → Set Vec3}
    {U : ι → Vec3 → ℝ → W} (h : SystemRelationComplete D U) : CoherentOverlaps D U :=
  fun i j n hi hj θ => h i j n n hi hj θ θ rfl

/-! ## Recovered rates are shared across overlaps -/

/-- **DERIVED.**  Two jointly regular families that agree along a direction have the same
recovered rates there. -/
theorem rates_eq_of_eq_along {U V : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    (hV : IsJointlyRegularFamily V) {n : Vec3} (hn : IsUnitAxis n) (h : ∀ θ : ℝ, U n θ = V n θ) :
    rateAlpha U n = rateAlpha V n ∧ rateBeta U n = rateBeta V n := by
  have hspec : ∀ θ : ℝ, V n θ = zexp (rateAlpha U n) (rateBeta U n) θ ⋆ Un n θ := by
    intro θ
    rw [← h θ]
    exact recovered_form hU hn θ
  exact regularFamily_param_unique hV.toRegularFamily hn hspec

/-! ## §68 — the glued directional rate -/

open Classical in
/-- **NEUTRAL DEFINITION (§68).**  The glued directional rate of a covering system: at a unit
direction it is the recovered directional rate of some local member containing it. -/
noncomputable def glueRate {ι : Type*} {D : ι → Set Vec3} {U : ι → Vec3 → ℝ → W}
    (hcov : ∀ n : Vec3, IsUnitAxis n → ∃ i : ι, n ∈ D i) (n : Vec3) : ℝ :=
  if h : IsUnitAxis n then rateBeta (U (hcov n h).choose) n else 0

/-- **DERIVED (§68).**  Under ordinary overlap coherence the glued rate is well defined: it
agrees with the recovered rate of *every* local member containing the direction. -/
theorem glueRate_eq {ι : Type*} {D : ι → Set Vec3} {U : ι → Vec3 → ℝ → W}
    (hsys : IsLocalSystem D U) (hco : CoherentOverlaps D U)
    (hcov : ∀ n : Vec3, IsUnitAxis n → ∃ i : ι, n ∈ D i) {n : Vec3} (hn : IsUnitAxis n) {i : ι}
    (hi : n ∈ D i) : glueRate (U := U) hcov n = rateBeta (U i) n := by
  classical
  have hj : n ∈ D (hcov n hn).choose := (hcov n hn).choose_spec
  have h1 : glueRate (U := U) hcov n = rateBeta (U (hcov n hn).choose) n := dif_pos hn
  rw [h1]
  exact (rates_eq_of_eq_along (hsys.regular _) (hsys.regular i) hn
    (fun θ => hco _ i n hj hi θ)).2

/-- **DERIVED (§68).**  The glued rate is continuous, by openness of the domains alone. -/
theorem glueRate_continuous {ι : Type*} {D : ι → Set Vec3} {U : ι → Vec3 → ℝ → W}
    (hsys : IsLocalSystem D U) (hco : CoherentOverlaps D U)
    (hcov : ∀ n : Vec3, IsUnitAxis n → ∃ i : ι, n ∈ D i) :
    Continuous fun s : Sph => glueRate (U := U) hcov (s : Vec3) := by
  rw [continuous_iff_continuousAt]
  intro s
  obtain ⟨i, hi⟩ := hcov (s : Vec3) s.2
  have hnb : sphSet (D i) ∈ nhds s := (hsys.isOpen i).mem_nhds hi
  have heq : (fun t : Sph => rateBeta (U i) (t : Vec3)) =ᶠ[nhds s]
      fun t : Sph => glueRate (U := U) hcov (t : Vec3) := by
    filter_upwards [hnb] with t ht
    exact (glueRate_eq hsys hco hcov t.2 ht).symm
  exact ((jointlyRegular_beta_continuous (hsys.regular i)).continuousAt).congr heq

/-- **DERIVED (§68).**  The glued family reproduces each local member on its own domain. -/
theorem glueFam_eq {ι : Type*} {D : ι → Set Vec3} {U : ι → Vec3 → ℝ → W}
    (hsys : IsLocalSystem D U) (hco : CoherentOverlaps D U)
    (hcov : ∀ n : Vec3, IsUnitAxis n → ∃ i : ι, n ∈ D i) {n : Vec3} (hn : IsUnitAxis n) {i : ι}
    (hi : n ∈ D i) (θ : ℝ) :
    famOf (fun _ => 0) (glueRate (U := U) hcov) n θ = U i n θ := by
  have hα : rateAlpha (U i) n = 0 := (pointwise_rates (hsys.regular i) (hsys.exact i) hi hn).1
  have hb : glueRate (U := U) hcov n = rateBeta (U i) n := glueRate_eq hsys hco hcov hn hi
  show zexp 0 (glueRate (U := U) hcov n) θ ⋆ Un n θ = U i n θ
  rw [hb, recovered_form (hsys.regular i) hn θ, hα]

/-- **PRINCIPAL THEOREM (§68).**  *Sufficiency.*  Complete visible-relation compatibility of
a locally exact covering system of open domains produces one primitive global bridge whose
reconstruction is globally exact. -/
theorem primitiveBridge_of_systemRelationComplete {ι : Type*} {D : ι → Set Vec3}
    {U : ι → Vec3 → ℝ → W} (hsys : IsLocalSystem D U) (hrel : SystemRelationComplete D U) :
    ∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsTransformationValued (recon c) := by
  have hco : CoherentOverlaps D U := coherentOverlaps_of_systemRelationComplete hrel
  set hcov := hsys.covers with hcovdef
  set b : Vec3 → ℝ := glueRate (U := U) hcov with hbdef
  have hbcont : Continuous fun s : Sph => b (s : Vec3) := glueRate_continuous hsys hco hcov
  have hjr : IsJointlyRegularFamily (famOf (fun _ => 0) b) :=
    jointlyRegular_famOf continuous_const hbcont
  have hTV : IsTransformationValued (famOf (fun _ => 0) b) := by
    intro n m θ φ hn hm hP
    obtain ⟨i, hi⟩ := hcov n hn
    obtain ⟨j, hj⟩ := hcov m hm
    rw [glueFam_eq hsys hco hcov hn hi θ, glueFam_eq hsys hco hcov hm hj φ]
    exact hrel i j n m hi hj θ φ hP
  exact primitiveBridge_iff_globalExactFamily.2 ⟨famOf (fun _ => 0) b, hjr, hTV⟩

/-! ## §69 — necessity -/

/-- **PRINCIPAL THEOREM (§69).**  *Necessity.*  One primitive global bridge with globally
exact reconstruction produces a relation-complete locally exact covering system — the
one-member system whose single domain is the whole unit-direction space. -/
theorem systemRelationComplete_of_primitiveBridge {c : Vec3 → ℝ → W} (hc : IsPrimitiveBridge c)
    (hex : IsTransformationValued (recon c)) :
    IsLocalSystem (fun _ : Unit => allUnit) (fun _ : Unit => recon c) ∧
      SystemRelationComplete (fun _ : Unit => allUnit) (fun _ : Unit => recon c) := by
  refine ⟨⟨fun _ => allUnit_unitSet, fun _ => ?_, fun _ => primitiveBridge_jointlyRegular hc,
    fun _ n hn m hm θ φ hP => hex n m θ φ hn hm hP, fun n hn => ⟨(), hn⟩⟩,
    fun _ _ n m hn hm θ φ hP => hex n m θ φ hn hm hP⟩
  rw [sphSet_allUnit]
  exact isOpen_univ

/-! ## §70 — the genuine equivalence -/

/-- **PRINCIPAL THEOREM (§70).**  *Genuine equivalence, both directions proved
constructively.*  A relation-complete locally exact covering system of open domains exists
**iff** a primitive global bridge with globally exact reconstruction exists. -/
theorem relationComplete_system_iff_primitiveBridge :
    (∃ (ι : Type) (D : ι → Set Vec3) (U : ι → Vec3 → ℝ → W),
        IsLocalSystem D U ∧ SystemRelationComplete D U) ↔
      ∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsTransformationValued (recon c) := by
  constructor
  · rintro ⟨ι, D, U, hsys, hrel⟩
    exact primitiveBridge_of_systemRelationComplete hsys hrel
  · rintro ⟨c, hc, hex⟩
    obtain ⟨hsys, hrel⟩ := systemRelationComplete_of_primitiveBridge hc hex
    exact ⟨Unit, _, _, hsys, hrel⟩

/-! ## §71 — the counterexample: coherent overlaps, one failing relation class -/

/-- **DERIVED.**  The inherited system is a locally exact covering system of open
domains. -/
theorem inhSystem_isLocalSystem : IsLocalSystem Dom inhSystem where
  unit := fun _ _ hn => hn.1
  isOpen := fun v => isOpen_sphSet_Dom v
  regular := fun _ => locFam_jointlyRegular 0
  exact := fun v => locFam_transformationValuedOn 0 v
  covers := fun n hn => ⟨n, Dom_covers hn⟩

/-- **PRINCIPAL THEOREM (§71).**  The explicit counterexample.  The inherited system has
coherent ordinary overlaps, satisfies the same-direction relation class and the
identity-degenerate relation class across arbitrary domains, and yet fails the antipodal
relation class — and no primitive global bridge with globally exact reconstruction exists at
all.  Coherent ordinary overlaps together with all but one relation class are therefore not
enough. -/
theorem inhSystem_relation_counterexample :
    IsLocalSystem Dom inhSystem ∧
      CoherentOverlaps Dom inhSystem ∧
      (∀ (i j n : Vec3), n ∈ Dom i → n ∈ Dom j → ∀ θ φ : ℝ,
        SameDirectionRel n θ n φ → inhSystem i n θ = inhSystem j n φ) ∧
      (∀ (i j n m : Vec3), n ∈ Dom i → m ∈ Dom j → ∀ θ φ : ℝ,
        DegenerateRel n θ m φ → inhSystem i n θ = inhSystem j m φ) ∧
      ¬ (∀ (i j n : Vec3), n ∈ Dom i → -n ∈ Dom j → ∀ θ : ℝ,
        inhSystem i n θ = inhSystem j (-n) (-θ)) ∧
      ¬ SystemRelationComplete Dom inhSystem ∧
      ¬ ∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsTransformationValued (recon c) := by
  refine ⟨inhSystem_isLocalSystem, fun _ _ _ _ _ _ => rfl, fun _ _ n hn _ θ φ h => ?_,
    fun _ _ n m hn hm θ φ h => ?_, fun hanti => ?_, ?_,
    no_global_rate_and_no_primitive_global_bridge.2⟩
  · exact same_direction_automatic (locFam_jointlyRegular 0) hn.1
      (locFam_zero_rates n hn.1).1 (locFam_zero_rates n hn.1).2 h.2
  · exact degenerate_automatic (locFam_jointlyRegular 0) locFam_zero_rates hn.1 hm.1 h
  · refine locFam_zero_not_antipodalRelated (fun n hn θ => ?_)
    exact hanti n (-n) n (Dom_covers hn) (Dom_covers (isUnitAxis_neg hn)) θ
  · exact (coverage_not_relationComplete).2.2.2

/-! ## §72 — the global obstruction is exactly relation incompleteness -/

/-- **PRINCIPAL THEOREM (§72).**  The global obstruction restated purely as failure of
complete visible-relation compatibility: no relation-complete locally exact covering system
of open domains exists, and this statement is equivalent to the nonexistence of a primitive
global bridge and to the nonexistence of a global directional rate. -/
theorem global_obstruction_is_relation_incompleteness :
    (¬ ∃ (ι : Type) (D : ι → Set Vec3) (U : ι → Vec3 → ℝ → W),
        IsLocalSystem D U ∧ SystemRelationComplete D U) ∧
      ((∃ (ι : Type) (D : ι → Set Vec3) (U : ι → Vec3 → ℝ → W),
          IsLocalSystem D U ∧ SystemRelationComplete D U) ↔
        ∃ c : Vec3 → ℝ → W, IsPrimitiveBridge c ∧ IsTransformationValued (recon c)) ∧
      ((∃ (ι : Type) (D : ι → Set Vec3) (U : ι → Vec3 → ℝ → W),
          IsLocalSystem D U ∧ SystemRelationComplete D U) ↔ ∃ b : Vec3 → ℝ, IsGlobalRate b) := by
  refine ⟨fun h => no_global_rate_and_no_primitive_global_bridge.2
      (relationComplete_system_iff_primitiveBridge.1 h),
    relationComplete_system_iff_primitiveBridge,
    relationComplete_system_iff_primitiveBridge.trans primitiveBridge_iff_globalRate⟩

end NullSectorTask19
