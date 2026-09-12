import RequestProject.Experiment2.NullSectorTask21.Task22

/-!
# Task 23, Package A: the certified projection, frozen intrinsically

**RECONSTRUCTION LAYER.  No conventional covering-space terminology occurs in this module
(item 16).**

Task XXI/XXII certified an intrinsic projection of the internal core carrier onto the
visible carrier.  Nothing of that identification work is reproved here: the quaternion,
`SU(2)`, `SO(3)`, `U(2)` and central-product statements are *not* used.  What is packaged
here is only the data that the local analysis of Task 23 needs:

* the carriers `LiftT` (the intrinsic core carrier `Lift` with its inherited topology) and
  `GvisT` (the intrinsic visible carrier `visImageFun` with its inherited topology);
* the intrinsic projection `pr : LiftT → GvisT`, its continuity and its surjectivity;
* the two-element sign carrier `Sgn` and its action on `LiftT`;
* the exact fibre description `pr u = pr v ↔ ∃ ε : Sgn, v = ε • u`, and the uniqueness of
  `ε` (items 14, 15);
* the kernel-sign subgroup of the packaged group `LiftG`, defined intrinsically as the
  kernel of the packaged projection and computed to be a two-element subgroup (item 13).

The multiplicative structure is the inherited product `⋆`; the topology is the inherited
topology of the finite-dimensional carrier `W` and of the space of maps `W → W`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask23

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21

open Quaternion Topology

/-! ## The two-element sign carrier -/

/-- **NEUTRAL DEFINITION.**  The two-element set of real signs. -/
def SgnSet : Set ℝ := {r : ℝ | r = 1 ∨ r = -1}

/-- **NEUTRAL DEFINITION.**  The two-element sign carrier, with the topology inherited from
the reals. -/
abbrev Sgn : Type := ↥SgnSet

theorem mem_SgnSet {r : ℝ} : r ∈ SgnSet ↔ r = 1 ∨ r = -1 := Iff.rfl

theorem Sgn.val_cases (e : Sgn) : (e : ℝ) = 1 ∨ (e : ℝ) = -1 := e.2

instance : Finite Sgn :=
  Set.Finite.to_subtype (by
    have h : SgnSet = ({1, -1} : Set ℝ) := by ext r; simp [SgnSet]
    rw [h]; simp)

instance : One Sgn := ⟨⟨1, Or.inl rfl⟩⟩

instance : Mul Sgn :=
  ⟨fun a b => ⟨(a : ℝ) * b, by
    rcases a.2 with h | h <;> rcases b.2 with h' | h' <;> simp [SgnSet, h, h']⟩⟩

instance : Inv Sgn := ⟨fun a => a⟩

@[simp] theorem Sgn.one_val : ((1 : Sgn) : ℝ) = 1 := rfl
@[simp] theorem Sgn.mul_val (a b : Sgn) : ((a * b : Sgn) : ℝ) = (a : ℝ) * b := rfl
@[simp] theorem Sgn.inv_val (a : Sgn) : ((a⁻¹ : Sgn) : ℝ) = (a : ℝ) := rfl

instance : CommGroup Sgn where
  mul_assoc a b c := Subtype.ext (by simp [mul_assoc])
  one_mul a := Subtype.ext (by simp)
  mul_one a := Subtype.ext (by simp)
  inv_mul_cancel a := Subtype.ext (by rcases a.2 with h | h <;> simp [h])
  mul_comm a b := Subtype.ext (by simp [mul_comm])

/-- **DERIVED.**  Every sign squares to the unit. -/
theorem Sgn.mul_self (a : Sgn) : a * a = 1 :=
  Subtype.ext (by rcases a.2 with h | h <;> simp [h])

theorem Sgn.inv_eq (a : Sgn) : a⁻¹ = a := rfl

theorem Sgn.eq_mul_of_mul_eq {a b c : Sgn} (h : a * b = c) : b = a * c := by
  rw [← h, ← mul_assoc, Sgn.mul_self, one_mul]

theorem Sgn.mul_left_self (a b : Sgn) : a * (b * a) = b := by
  rw [mul_comm b a, ← mul_assoc, Sgn.mul_self, one_mul]

/-- The nontrivial sign. -/
def Sgn.negOne : Sgn := ⟨-1, Or.inr rfl⟩

@[simp] theorem Sgn.negOne_val : ((Sgn.negOne : Sgn) : ℝ) = -1 := rfl

theorem Sgn.negOne_ne_one : (Sgn.negOne : Sgn) ≠ 1 := by
  intro h
  have := congrArg Subtype.val h
  norm_num at this

theorem Sgn.eq_one_or_negOne (a : Sgn) : a = 1 ∨ a = Sgn.negOne := by
  rcases a.2 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- **DERIVED.**  The sign carrier is discrete: this is the exact regularity available for
sign-valued data below. -/
theorem Sgn.discrete : DiscreteTopology Sgn := inferInstance

/-- **NEUTRAL DEFINITION.**  The sign attached to a nonzero real number. -/
noncomputable def sgnOf {r : ℝ} (hr : r ≠ 0) : Sgn :=
  ⟨r / |r|, by
    rcases lt_or_gt_of_ne hr with h | h
    · right
      rw [abs_of_neg h]
      field_simp
    · left
      rw [abs_of_pos h]
      field_simp⟩

theorem sgnOf_val {r : ℝ} (hr : r ≠ 0) : ((sgnOf hr : Sgn) : ℝ) = r / |r| := rfl

theorem sgnOf_eq_one {r : ℝ} (hr : r ≠ 0) (h : 0 < r) : sgnOf hr = 1 :=
  Subtype.ext (show r / |r| = (1 : ℝ) by rw [abs_of_pos h]; field_simp)

theorem sgnOf_eq_negOne {r : ℝ} (hr : r ≠ 0) (h : r < 0) : sgnOf hr = Sgn.negOne :=
  Subtype.ext (show r / |r| = (-1 : ℝ) by rw [abs_of_neg h]; field_simp)

theorem sgnOf_pos {r : ℝ} (hr : r ≠ 0) : 0 < ((sgnOf hr : Sgn) : ℝ) * r := by
  rcases lt_or_gt_of_ne hr with h | h
  · rw [sgnOf_eq_negOne hr h]; simpa using h
  · rw [sgnOf_eq_one hr h]; simpa using h

/-! ## Continuity of the inherited product -/

/-- **DERIVED.**  The inherited product is jointly continuous along continuous data.  The
proof is coordinatewise: every coordinate of the inherited product is a polynomial in the
coordinates of the two factors. -/
theorem continuous_mulW_comp {X : Type*} [TopologicalSpace X] {f g : X → W} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => f x ⋆ g x := by
  have hf' : ∀ j, Continuous fun x => f x j := fun j => (continuous_apply j).comp hf
  have hg' : ∀ j, Continuous fun x => g x j := fun j => (continuous_apply j).comp hg
  rw [continuous_pi_iff]
  intro i
  fin_cases i <;> fun_prop

/-- **DERIVED.**  The inherited product is jointly continuous. -/
theorem continuous_mulW : Continuous fun p : W × W => p.1 ⋆ p.2 :=
  continuous_mulW_comp continuous_fst continuous_snd

/-! ## The inherited inverse on the core carrier -/

/-- **NEUTRAL DEFINITION.**  The reflection of the generator part, written through the
inherited coordinates. -/
noncomputable def conjW (u : W) : W := fromQuat (star (quatOf u))

theorem continuous_conjW : Continuous conjW :=
  continuous_fromQuat.comp (continuous_star.comp continuous_quatOf)

theorem mul_conjW {u : W} (hu : u ∈ Lift) : u ⋆ conjW u = w1 := by
  have h1 : fromQuat (quatOf u) = u := fromQuat_quatOf hu
  have h2 : normSq (quatOf u) = 1 := quatOf_normSq hu
  calc u ⋆ conjW u = fromQuat (quatOf u) ⋆ fromQuat (star (quatOf u)) := by rw [h1, conjW]
    _ = fromQuat (quatOf u * star (quatOf u)) := (fromQuat_mul _ _).symm
    _ = w1 := by rw [quat_mul_star_of_normSq_one h2, fromQuat_one]

theorem conjW_mul {u : W} (hu : u ∈ Lift) : conjW u ⋆ u = w1 := by
  have h1 : fromQuat (quatOf u) = u := fromQuat_quatOf hu
  have h2 : normSq (quatOf u) = 1 := quatOf_normSq hu
  calc conjW u ⋆ u = fromQuat (star (quatOf u)) ⋆ fromQuat (quatOf u) := by rw [h1, conjW]
    _ = fromQuat (star (quatOf u) * quatOf u) := (fromQuat_mul _ _).symm
    _ = w1 := by rw [quat_star_mul_of_normSq_one h2, fromQuat_one]

theorem invW_eq_conjW {u : W} (hu : u ∈ Lift) : invW u = conjW u :=
  invW_eq (mul_conjW hu) (conjW_mul hu)

theorem conjW_mem_Lift {u : W} (hu : u ∈ Lift) : conjW u ∈ Lift := by
  refine fromQuat_mem_Lift ?_
  rw [normSq_star]
  exact quatOf_normSq hu

/-! ## The scalar sign action on the core carrier -/

theorem smul_mem_Lift {c : ℝ} (hc : c = 1 ∨ c = -1) {u : W} (hu : u ∈ Lift) :
    c • u ∈ Lift := by
  have h1 : fromQuat (quatOf u) = u := fromQuat_quatOf hu
  have h2 : normSq (quatOf u) = 1 := quatOf_normSq hu
  have hsm : c • u = fromQuat (c • quatOf u) := by
    rw [show fromQuat (c • quatOf u) = c • fromQuat (quatOf u) from fromQuatL.map_smul c _, h1]
  rw [hsm]
  refine fromQuat_mem_Lift ?_
  have hns : normSq (c • quatOf u) = c ^ 2 * normSq (quatOf u) := by
    simp only [normSq_def', Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
      Quaternion.imK_smul, smul_eq_mul]
    ring
  rw [hns, h2]
  rcases hc with rfl | rfl <;> norm_num

theorem neg_mem_Lift {u : W} (hu : u ∈ Lift) : -u ∈ Lift := by
  have h := smul_mem_Lift (c := -1) (Or.inr rfl) hu
  simpa using h

/-! ## The two carriers and the intrinsic projection -/

/-- **NEUTRAL DEFINITION.**  The internal core carrier with its inherited topology. -/
abbrev LiftT : Type := (Lift : Set W)

/-- **NEUTRAL DEFINITION.**  The visible carrier with its inherited topology. -/
abbrev GvisT : Type := (visImageFun : Set (W → W))

theorem proj_mem_visImageFun {u : W} (hu : u ∈ Lift) : ⇑(proj u) ∈ visImageFun := by
  obtain ⟨n, θ, hn, rfl⟩ := (mem_Lift_iff_exists_Un u).1 hu
  exact ⟨(⟨n, hn⟩, θ), congrArg (fun F : W →ₗ[ℝ] W => (F : W → W)) (proj_Un hn θ).symm⟩

/-- **NEUTRAL DEFINITION (item 12).**  The certified projection, frozen as a map of the two
topological carriers. -/
noncomputable def pr (u : LiftT) : GvisT := ⟨⇑(proj (u : W)), proj_mem_visImageFun u.2⟩

@[simp] theorem pr_val (u : LiftT) : ((pr u : GvisT) : W → W) = ⇑(proj (u : W)) := rfl

theorem pr_eq_iff_proj_eq {u v : LiftT} : pr u = pr v ↔ proj (u : W) = proj (v : W) := by
  constructor
  · intro h
    exact DFunLike.coe_injective (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (congrArg (fun F : W →ₗ[ℝ] W => (F : W → W)) h)

/-- **PACKAGE A (item 12).**  The projection is continuous. -/
theorem continuous_pr : Continuous pr := by
  refine Continuous.subtype_mk ?_ _
  rw [continuous_pi_iff]
  intro x
  have h : ∀ u : LiftT, (⇑(proj (u : W))) x = ((u : W) ⋆ x) ⋆ conjW (u : W) := by
    intro u
    rw [proj_apply, invW_eq_conjW u.2]
  simp only [h]
  exact continuous_mulW_comp
    (continuous_mulW_comp continuous_subtype_val continuous_const)
    (continuous_conjW.comp continuous_subtype_val)

/-- **PACKAGE A (item 12).**  The projection is surjective. -/
theorem pr_surjective : Function.Surjective pr := by
  rintro ⟨F, ⟨p, rfl⟩⟩
  refine ⟨⟨Un (p.1 : Vec3) p.2, Un_mem_Lift p.1.2 p.2⟩, ?_⟩
  refine Subtype.ext ?_
  show ⇑(proj (Un (p.1 : Vec3) p.2)) = ⇑(visMap p)
  rw [proj_Un p.1.2]
  rfl

noncomputable instance : CompactSpace LiftT := liftQuatHomeo.compactSpace

/-- **PACKAGE A.**  The projection is a closed map: the source carrier is compact and the
target carrier is separated. -/
theorem isClosedMap_pr : IsClosedMap pr := continuous_pr.isClosedMap

/-- **PACKAGE A.**  The projection identifies the target topology. -/
theorem isQuotientMap_pr : IsQuotientMap pr :=
  isClosedMap_pr.isQuotientMap continuous_pr pr_surjective

/-! ## The sign action -/

/-- **NEUTRAL DEFINITION.**  The action of a sign on the core carrier. -/
def sact (e : Sgn) (u : LiftT) : LiftT := ⟨(e : ℝ) • (u : W), smul_mem_Lift e.2 u.2⟩

@[simp] theorem sact_val (e : Sgn) (u : LiftT) : ((sact e u : LiftT) : W) = (e : ℝ) • (u : W) :=
  rfl

@[simp] theorem sact_one (u : LiftT) : sact 1 u = u := Subtype.ext (by simp)

theorem sact_mul (e f : Sgn) (u : LiftT) : sact (e * f) u = sact e (sact f u) :=
  Subtype.ext (by simp [smul_smul])

theorem continuous_sact (e : Sgn) : Continuous (sact e) :=
  Continuous.subtype_mk (continuous_const.smul continuous_subtype_val) _

/-- **PACKAGE A.**  The sign action is invisible to the projection. -/
theorem pr_sact (e : Sgn) (u : LiftT) : pr (sact e u) = pr u := by
  refine pr_eq_iff_proj_eq.2 ?_
  rcases e.2 with h | h
  · rw [sact_val, h, one_smul]
  · rw [sact_val, h]
    have hneg : (-1 : ℝ) • (u : W) = -(u : W) := by module
    rw [hneg]
    exact proj_neg (isInvertible_of_mem_Lift u.2)

/-- **PACKAGE A (item 14), principal.**  Two core elements have the same projection exactly
when they differ by a sign.  This is the strongest exact fibre description. -/
theorem pr_eq_iff (u v : LiftT) : pr u = pr v ↔ ∃ e : Sgn, v = sact e u := by
  constructor
  · intro h
    have hproj : proj (u : W) = proj (v : W) := pr_eq_iff_proj_eq.1 h
    have hcu : conjW (u : W) ∈ Lift := conjW_mem_Lift u.2
    have hw : (v : W) ⋆ conjW (u : W) ∈ Lift := Lift_mul_mem v.2 hcu
    have hprojw : proj ((v : W) ⋆ conjW (u : W)) = LinearMap.id := by
      rw [proj_mul (isInvertible_of_mem_Lift v.2) (isInvertible_of_mem_Lift hcu), ← hproj,
        ← proj_mul (isInvertible_of_mem_Lift u.2) (isInvertible_of_mem_Lift hcu),
        mul_conjW u.2, proj_w1]
    have hmem : (v : W) ⋆ conjW (u : W) ∈ ({w1, -w1} : Set W) := by
      rw [← kernel_core]; exact ⟨hw, hprojw⟩
    have hval : ((v : W) ⋆ conjW (u : W)) ⋆ (u : W) = (v : W) := by
      rw [mul_assoc_W, conjW_mul u.2, mul_one_W]
    rcases hmem with h1 | h1
    · refine ⟨1, Subtype.ext ?_⟩
      rw [sact_val, Sgn.one_val, one_smul, ← hval, h1, one_mul_W]
    · refine ⟨Sgn.negOne, Subtype.ext ?_⟩
      rw [sact_val, Sgn.negOne_val, ← hval, h1, neg_mul_W, one_mul_W]
      module
  · rintro ⟨e, rfl⟩
    exact (pr_sact e u).symm

/-- **PACKAGE A (item 15).**  The sign relating two core elements with the same projection is
unique. -/
theorem sact_injective_sign (u : LiftT) {e f : Sgn} (h : sact e u = sact f u) : e = f := by
  have hval : (e : ℝ) • (u : W) = (f : ℝ) • (u : W) := congrArg Subtype.val h
  have hzero : ((e : ℝ) - f) • (u : W) = 0 := by
    rw [sub_smul, hval, sub_self]
  rcases smul_eq_zero.1 hzero with h1 | h1
  · exact Subtype.ext (by linarith [sub_eq_zero.1 h1])
  · exact absurd (h1 ▸ u.2) zero_notMem_Lift

theorem sact_free (u : LiftT) : sact Sgn.negOne u ≠ u := by
  intro h
  have h' : sact Sgn.negOne u = sact 1 u := by rw [h, sact_one]
  exact Sgn.negOne_ne_one (sact_injective_sign u h')

/-! ## The kernel-sign subgroup, intrinsically (item 13) -/

/-- **NEUTRAL DEFINITION (item 13).**  The kernel-sign subgroup: the kernel of the packaged
certified projection. -/
noncomputable def KerSign : Subgroup LiftG := projCore.ker

/-- **PACKAGE A (item 13).**  The kernel-sign subgroup has exactly two elements, the unit and
the sign element.  This is the packaged Task-XXI kernel theorem, restated. -/
theorem KerSign_eq :
    (KerSign : Set LiftG) = {⟨1, LiftG.one_mem⟩, ⟨WG.negOne, negOne_mem_LiftG⟩} :=
  ker_projCore

theorem mem_KerSign_iff {u : LiftG} :
    u ∈ KerSign ↔ ((u : WG).val = w1 ∨ (u : WG).val = -w1) := by
  constructor
  · intro hu
    have h : u ∈ ({⟨1, LiftG.one_mem⟩, ⟨WG.negOne, negOne_mem_LiftG⟩} : Set LiftG) := by
      rw [← KerSign_eq]; exact hu
    rcases h with h1 | h1
    · exact Or.inl (congrArg (fun v : LiftG => (v : WG).val) h1)
    · exact Or.inr (congrArg (fun v : LiftG => (v : WG).val) h1)
  · intro hu
    have h : u ∈ ({⟨1, LiftG.one_mem⟩, ⟨WG.negOne, negOne_mem_LiftG⟩} : Set LiftG) := by
      rcases hu with h1 | h1
      · exact Or.inl (Subtype.ext (WG.ext h1))
      · exact Or.inr (Subtype.ext (WG.ext h1))
    rw [← KerSign_eq] at h
    exact h

end NullSectorTask23
