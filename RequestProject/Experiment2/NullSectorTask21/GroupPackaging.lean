import RequestProject.Experiment2.NullSectorTask21.SafeBase

/-!
# Task 21, Layer 1: intrinsic group packaging (RECONSTRUCTION LAYER)

**No conventional named group occurs in this module.**  Nothing here is a new mathematical
input: every closure, kernel and centre fact used below was already proved intrinsically in
Task 20.  The only thing done here is *packaging*: the inherited carriers are presented as
bundled algebraic objects so that later identification modules can state exact equivalences
of maps, kernels and quotients.

* `WG` — the invertible elements of the inherited carrier `W` with the inherited product.
* `LiftG`, `CUnitG`, `LiftZG` — the Task-20 carriers `Lift`, `CUnit`, `LiftZ` as sub-objects
  of `WG`; the closure proofs are exactly the Task-20 theorems.
* `GvisG` — the Task-20 visible image `visImage` as a sub-object of the invertible linear
  self-maps of `W`; the closure proofs are exactly `visImage_id`, `visImage_comp_mem`,
  `visImage_inv_mem`.
* `projU`, `projZ`, `projCore` — the Task-20 intrinsic projection `proj`, packaged.

The kernel theorems of Task 20 are then restated in the packaged form; they are *derived
from*, not substituted for, the intrinsic statements.
-/

namespace NullSectorTask21

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20

/-! ## The invertible elements of the inherited carrier -/

/-- **NEUTRAL DEFINITION.**  An invertible element of the inherited carrier, together with
its (unique) two-sided inverse. -/
structure WG where
  val : W
  inv : W
  val_inv : val ⋆ inv = w1
  inv_val : inv ⋆ val = w1

namespace WG

theorem inv_eq_of_val_eq {u v : WG} (h : u.val = v.val) : u.inv = v.inv :=
  inverse_unique (h ▸ u.val_inv) v.inv_val

@[ext] theorem ext {u v : WG} (h : u.val = v.val) : u = v := by
  obtain ⟨a, b, h1, h2⟩ := u
  obtain ⟨c, d, h3, h4⟩ := v
  have hb : b = d := inv_eq_of_val_eq (u := ⟨a, b, h1, h2⟩) (v := ⟨c, d, h3, h4⟩) h
  simp only at h hb
  subst h; subst hb; rfl

instance : One WG := ⟨⟨w1, w1, mul_one_W w1, one_mul_W w1⟩⟩

instance : Mul WG :=
  ⟨fun u v => ⟨u.val ⋆ v.val, v.inv ⋆ u.inv, by
      calc (u.val ⋆ v.val) ⋆ (v.inv ⋆ u.inv)
          = (u.val ⋆ (v.val ⋆ v.inv)) ⋆ u.inv := by
            rw [mul_assoc_W, mul_assoc_W, mul_assoc_W]
        _ = w1 := by rw [v.val_inv, mul_one_W, u.val_inv], by
      calc (v.inv ⋆ u.inv) ⋆ (u.val ⋆ v.val)
          = (v.inv ⋆ (u.inv ⋆ u.val)) ⋆ v.val := by
            rw [mul_assoc_W, mul_assoc_W, mul_assoc_W]
        _ = w1 := by rw [u.inv_val, mul_one_W, v.inv_val]⟩⟩

instance : Inv WG := ⟨fun u => ⟨u.inv, u.val, u.inv_val, u.val_inv⟩⟩

@[simp] theorem one_val : (1 : WG).val = w1 := rfl
@[simp] theorem mul_val (u v : WG) : (u * v).val = u.val ⋆ v.val := rfl
@[simp] theorem inv_val_eq (u : WG) : (u⁻¹).val = u.inv := rfl

instance : Group WG where
  mul_assoc u v w := WG.ext (mul_assoc_W _ _ _)
  one_mul u := WG.ext (one_mul_W _)
  mul_one u := WG.ext (mul_one_W _)
  inv_mul_cancel u := WG.ext u.inv_val

/-- **NEUTRAL DEFINITION.**  The packaged form of an invertible carrier element. -/
noncomputable def ofInvertible {u : W} (h : IsInvertible u) : WG :=
  ⟨u, invW u, (invW_spec h).1, (invW_spec h).2⟩

@[simp] theorem ofInvertible_val {u : W} (h : IsInvertible u) : (ofInvertible h).val = u := rfl

/-- The distinguished sign element. -/
def negOne : WG := ⟨-w1, -w1, by rw [neg_mul_W, mul_neg_W, one_mul_W, neg_neg], by
  rw [neg_mul_W, mul_neg_W, one_mul_W, neg_neg]⟩

@[simp] theorem negOne_val : negOne.val = -w1 := rfl

theorem negOne_ne_one : negOne ≠ 1 := by
  intro h
  exact w1_ne_neg_w1 (congrArg WG.val h).symm

@[simp] theorem negOne_mul_negOne : negOne * negOne = 1 := by
  refine WG.ext ?_
  simp only [mul_val, negOne_val, one_val, neg_mul_W, mul_neg_W, one_mul_W, neg_neg]

end WG

/-! ## The intrinsic carriers as sub-objects -/

/-- **PACKAGED (Task-20 `Lift`).** -/
def LiftG : Subgroup WG where
  carrier := {u : WG | u.val ∈ Lift}
  one_mem' := w1_mem_Lift
  mul_mem' := by
    intro a b ha hb
    exact Lift_mul_mem ha hb
  inv_mem' := by
    intro a ha
    obtain ⟨a', ha', h1, _⟩ := Lift_inv_mem ha
    have hEq : a' = a.inv := inverse_unique h1 a.inv_val
    show a.inv ∈ Lift
    rw [← hEq]
    exact ha'

/-- **PACKAGED (Task-20 `CUnit`).** -/
def CUnitG : Subgroup WG where
  carrier := {u : WG | u.val ∈ CUnit}
  one_mem' := w1_mem_CUnit
  mul_mem' := by
    intro a b ha hb
    exact CUnit_mul_mem ha hb
  inv_mem' := by
    intro a ha
    obtain ⟨a', ha', h1, _⟩ := CUnit_inv_mem ha
    have hEq : a' = a.inv := inverse_unique h1 a.inv_val
    show a.inv ∈ CUnit
    rw [← hEq]
    exact ha'

/-- **PACKAGED (Task-20 `LiftZ`).** -/
def LiftZG : Subgroup WG where
  carrier := {u : WG | u.val ∈ LiftZ}
  one_mem' := Lift_subset_LiftZ w1_mem_Lift
  mul_mem' := by
    intro a b ha hb
    exact LiftZ_mul_mem ha hb
  inv_mem' := by
    intro a ha
    obtain ⟨a', ha', h1, _⟩ := LiftZ_inv_mem ha
    have hEq : a' = a.inv := inverse_unique h1 a.inv_val
    show a.inv ∈ LiftZ
    rw [← hEq]
    exact ha'

@[simp] theorem mem_LiftG {u : WG} : u ∈ LiftG ↔ u.val ∈ Lift := Iff.rfl
@[simp] theorem mem_CUnitG {u : WG} : u ∈ CUnitG ↔ u.val ∈ CUnit := Iff.rfl
@[simp] theorem mem_LiftZG {u : WG} : u ∈ LiftZG ↔ u.val ∈ LiftZ := Iff.rfl

theorem LiftG_le_LiftZG : LiftG ≤ LiftZG := fun _ hu => Lift_subset_LiftZ hu
theorem CUnitG_le_LiftZG : CUnitG ≤ LiftZG := fun _ hu => CUnit_subset_LiftZ hu

theorem negOne_mem_LiftG : WG.negOne ∈ LiftG := neg_w1_mem_Lift

/-- **PACKAGED.**  The packaged reference implementers. -/
noncomputable def UnG {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) : WG :=
  WG.ofInvertible (isInvertible_of_mem_Lift (Un_mem_Lift hn θ))

@[simp] theorem UnG_val {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) : (UnG hn θ).val = Un n θ := rfl

theorem UnG_mem_LiftG {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) : UnG hn θ ∈ LiftG :=
  Un_mem_Lift hn θ

/-! ## The visible image as a sub-object -/

/-- **PACKAGED (Task-20 `visImage`).**  The visible image, inside the invertible real-linear
self-maps of the inherited carrier. -/
def GvisG : Subgroup (Module.End ℝ W)ˣ where
  carrier := {U : (Module.End ℝ W)ˣ | (U : Module.End ℝ W) ∈ visImage}
  one_mem' := visImage_id
  mul_mem' := by
    intro a b ha hb
    exact visImage_comp_mem ha hb
  inv_mem' := by
    intro a ha
    obtain ⟨G, hG, h1, _⟩ := visImage_inv_mem ha
    have hmul : (a : Module.End ℝ W) * G = 1 := h1
    show (↑a⁻¹ : Module.End ℝ W) ∈ visImage
    rw [Units.inv_eq_of_mul_eq_one_right hmul]
    exact hG

@[simp] theorem mem_GvisG {U : (Module.End ℝ W)ˣ} :
    U ∈ GvisG ↔ (U : Module.End ℝ W) ∈ visImage := Iff.rfl

/-! ## The packaged projection -/

/-- **PACKAGED (Task-20 `proj`).**  The intrinsic projection as a group homomorphism. -/
noncomputable def projU : WG →* (Module.End ℝ W)ˣ where
  toFun u :=
    ⟨proj u.val, proj u.inv, by
        rw [show proj u.val * proj u.inv = (proj u.val).comp (proj u.inv) from rfl,
          ← proj_mul ⟨u.inv, u.val_inv, u.inv_val⟩ ⟨u.val, u.inv_val, u.val_inv⟩,
          u.val_inv, proj_w1]
        rfl, by
        rw [show proj u.inv * proj u.val = (proj u.inv).comp (proj u.val) from rfl,
          ← proj_mul ⟨u.val, u.inv_val, u.val_inv⟩ ⟨u.inv, u.val_inv, u.inv_val⟩,
          u.inv_val, proj_w1]
        rfl⟩
  map_one' := by
    refine Units.ext ?_
    exact proj_w1
  map_mul' u v := by
    refine Units.ext ?_
    exact proj_mul ⟨u.inv, u.val_inv, u.inv_val⟩ ⟨v.inv, v.val_inv, v.inv_val⟩

@[simp] theorem projU_coe (u : WG) : ((projU u : (Module.End ℝ W)ˣ) : Module.End ℝ W)
    = proj u.val := rfl

theorem invW_of (u : WG) : invW u.val = u.inv := invW_eq u.val_inv u.inv_val

theorem projU_apply (u : WG) (x : W) :
    ((projU u : (Module.End ℝ W)ˣ) : Module.End ℝ W) x = (u.val ⋆ x) ⋆ u.inv := by
  rw [projU_coe, proj_apply, invW_of]

theorem projU_UnG {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    ((projU (UnG hn θ) : (Module.End ℝ W)ˣ) : Module.End ℝ W) = PhiGen n θ := by
  rw [projU_coe, UnG_val, proj_Un hn]

theorem projU_mem_GvisG_of_LiftG {u : WG} (hu : u ∈ LiftG) : projU u ∈ GvisG := by
  obtain ⟨n, θ, hn, hval⟩ := (mem_Lift_iff_exists_Un u.val).1 hu
  refine ⟨⟨⟨n, hn⟩, θ⟩, ?_⟩
  rw [visMap, projU_coe, hval, proj_Un hn]

theorem projU_mem_GvisG_of_LiftZG {u : WG} (hu : u ∈ LiftZG) : projU u ∈ GvisG := by
  obtain ⟨z, hz, g, hg, hval⟩ := hu
  have hgi : IsInvertible g := isInvertible_of_mem_Lift hg
  obtain ⟨n, θ, hn, hgval⟩ := (mem_Lift_iff_exists_Un g).1 hg
  refine ⟨⟨⟨n, hn⟩, θ⟩, ?_⟩
  rw [visMap, projU_coe, hval, proj_central_mul hz hgi, hgval, proj_Un hn]

/-- **PACKAGED.**  The intrinsic projection restricted to the internal core carrier. -/
noncomputable def projCore : LiftG →* GvisG where
  toFun u := ⟨projU u.1, projU_mem_GvisG_of_LiftG u.2⟩
  map_one' := by
    refine Subtype.ext ?_
    simp only [OneMemClass.coe_one, map_one]
  map_mul' u v := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, map_mul]

/-- **PACKAGED.**  The intrinsic projection restricted to the full internal carrier. -/
noncomputable def projZ : LiftZG →* GvisG where
  toFun u := ⟨projU u.1, projU_mem_GvisG_of_LiftZG u.2⟩
  map_one' := by
    refine Subtype.ext ?_
    simp only [OneMemClass.coe_one, map_one]
  map_mul' u v := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, map_mul]

@[simp] theorem projCore_coe (u : LiftG) :
    (((projCore u : GvisG) : (Module.End ℝ W)ˣ) : Module.End ℝ W) = proj (u : WG).val := rfl

@[simp] theorem projZ_coe (u : LiftZG) :
    (((projZ u : GvisG) : (Module.End ℝ W)ˣ) : Module.End ℝ W) = proj (u : WG).val := rfl

/-! ## The packaged kernel theorems -/

/-- **PACKAGED (Task-20 `kernel_core`).**  The kernel of the packaged core projection is the
two-element set consisting of the unit and the sign element. -/
theorem ker_projCore :
    (projCore.ker : Set LiftG) = {⟨1, LiftG.one_mem⟩, ⟨WG.negOne, negOne_mem_LiftG⟩} := by
  ext u
  constructor
  · intro hu
    have h : proj (u : WG).val = LinearMap.id := by
      have := congrArg (fun U : GvisG => ((U : (Module.End ℝ W)ˣ) : Module.End ℝ W))
        (MonoidHom.mem_ker.1 hu)
      simpa using this
    have hmem : (u : WG).val ∈ ({w1, -w1} : Set W) := by
      rw [← kernel_core]; exact ⟨u.2, h⟩
    rcases hmem with h1 | h1
    · left; exact Subtype.ext (WG.ext h1)
    · right; exact Subtype.ext (WG.ext h1)
  · intro hu
    rcases hu with h1 | h1
    · rw [h1]; exact MonoidHom.mem_ker.2 (map_one projCore)
    · subst h1
      refine MonoidHom.mem_ker.2 (Subtype.ext (Units.ext ?_))
      have : (WG.negOne).val ∈ ({w1, -w1} : Set W) := Or.inr rfl
      have h := kernel_core ▸ this
      exact h.2

/-- **PACKAGED (Task-20 `kernel_full`).**  The kernel of the packaged full projection is
exactly the packaged invertible centre. -/
theorem ker_projZ :
    (projZ.ker : Set LiftZG) = {u : LiftZG | (u : WG).val ∈ CUnit} := by
  ext u
  constructor
  · intro hu
    have h : proj (u : WG).val = LinearMap.id := by
      have := congrArg (fun U : GvisG => ((U : (Module.End ℝ W)ˣ) : Module.End ℝ W))
        (MonoidHom.mem_ker.1 hu)
      simpa using this
    have : (u : WG).val ∈ ({x : W | x ∈ LiftZ ∧ proj x = LinearMap.id}) := ⟨u.2, h⟩
    rwa [kernel_full] at this
  · intro hu
    obtain ⟨a, b, hab, hval⟩ := hu
    refine MonoidHom.mem_ker.2 (Subtype.ext (Units.ext ?_))
    show proj (u : WG).val = LinearMap.id
    rw [hval]
    exact proj_zc hab

/-- **PACKAGED.**  The packaged core projection is surjective onto the packaged visible
image: this is the Task-20 statement that every visible transformation is implemented. -/
theorem projCore_surjective : Function.Surjective projCore := by
  rintro ⟨U, p, hp⟩
  refine ⟨⟨UnG p.1.2 p.2, UnG_mem_LiftG p.1.2 p.2⟩, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  rw [projCore_coe]
  show proj (Un (p.1 : Vec3) p.2) = (U : Module.End ℝ W)
  rw [proj_Un p.1.2, ← hp, visMap]

theorem projZ_surjective : Function.Surjective projZ := by
  intro U
  obtain ⟨u, hu⟩ := projCore_surjective U
  exact ⟨⟨(u : WG), LiftG_le_LiftZG u.2⟩, Subtype.ext (Units.ext (congrArg
    (fun V : GvisG => ((V : (Module.End ℝ W)ˣ) : Module.End ℝ W)) hu))⟩

end NullSectorTask21
