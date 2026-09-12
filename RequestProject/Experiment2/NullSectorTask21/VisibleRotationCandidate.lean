import RequestProject.Experiment2.NullSectorTask21.SU2Model

/-!
# Task 21, Packages C and D: the visible transformations as three-dimensional rotations

**IDENTIFICATION / COMPARISON MODULE.**

Package C constructs the induced real-linear action of a visible transformation on the
inherited three-dimensional spatial sector, proves that it is well defined (it depends on
the visible transformation only, not on an internal representative), that it preserves the
inherited positive-definite spatial form and the inherited inner product, and packages it as
an explicit real matrix.

Package D then compares the resulting matrix group with the standard three-dimensional
special orthogonal group.

`IMPORTED STANDARD RESULT`: `Matrix.specialOrthogonalGroup`, `Matrix.orthogonalGroup`,
`Matrix.det_fin_three`, `Matrix.exists_mulVec_eq_zero_iff`.

`DERIVED IN TASK 21`: every statement below.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask21

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20

open Matrix

/-! ## The induced action on the inherited spatial sector -/

/-- **PACKAGE C.**  The real-linear map induced on the inherited three-dimensional spatial
sector by a linear self-map of the carrier.  It is defined directly from the transformation,
so it visibly does not depend on any internal representative. -/
noncomputable def spatAct (F : W →ₗ[ℝ] W) : Vec3 →ₗ[ℝ] Vec3 where
  toFun p := spatInv (F (spat p))
  map_add' p q := by
    rw [spat_add, map_add, spatInv_add]
  map_smul' c p := by
    rw [spat_smul, map_smul, spatInv_smul, RingHom.id_apply]

@[simp] theorem spatAct_apply (F : W →ₗ[ℝ] W) (p : Vec3) :
    spatAct F p = spatInv (F (spat p)) := rfl

/-- **PACKAGE C.**  On a reference implementer the induced action is exactly the inherited
spatial coordinate action. -/
theorem spatAct_PhiGen {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) (p : Vec3) :
    spatAct (PhiGen n θ) p = rotv n θ p := by
  rw [spatAct_apply, PhiGen_spat hn, spatInv_spat]

/-- **PACKAGE C (item 29).**  Well-definedness: the induced action depends only on the
visible transformation.  Two internal elements with the same visible transformation — in
particular two elements differing by an invertible central factor — induce the same spatial
map. -/
theorem spatAct_indep_of_representative {u u' : W} (h : proj u = proj u') :
    spatAct (proj u) = spatAct (proj u') := by rw [h]

theorem spatAct_central_mul {z g : W} (hz : z ∈ CUnit) (hg : IsInvertible g) :
    spatAct (proj (z ⋆ g)) = spatAct (proj g) := by rw [proj_central_mul hz hg]

/-- **PACKAGE C.**  The induced action preserves the inherited positive-definite spatial
form. -/
theorem spatAct_preserves_form {F : W →ₗ[ℝ] W} (hF : F ∈ visImage) (p : Vec3) :
    h3 (spatAct F p) (spatAct F p) = h3 p p := by
  obtain ⟨q, rfl⟩ := hF
  rw [visMap, spatAct_PhiGen q.1.2, rotv_preserves_form q.1.2]

/-- **PACKAGE C (item 31).**  The induced action preserves the inherited inner product, by
polarization. -/
theorem spatAct_preserves_inner {F : W →ₗ[ℝ] W} (hF : F ∈ visImage) (p q : Vec3) :
    h3 (spatAct F p) (spatAct F q) = h3 p q := by
  have hsum := spatAct_preserves_form hF (p + q)
  have hp := spatAct_preserves_form hF p
  have hq := spatAct_preserves_form hF q
  rw [map_add] at hsum
  simp only [h3, dot3, Prod.fst_add, Prod.snd_add] at hsum hp hq ⊢
  nlinarith [hsum, hp, hq]

theorem spatAct_one : spatAct (LinearMap.id) = LinearMap.id := by
  refine LinearMap.ext fun p => ?_
  rw [spatAct_apply, LinearMap.id_apply, spatInv_spat, LinearMap.id_apply]

theorem spatAct_comp {F G : W →ₗ[ℝ] W} (hF : F ∈ visImage) (hG : G ∈ visImage) (p : Vec3) :
    spatAct (F.comp G) p = spatAct F (spatAct G p) := by
  obtain ⟨a, rfl⟩ := hF
  obtain ⟨b, rfl⟩ := hG
  rw [spatAct_apply, LinearMap.comp_apply, visMap, visMap, PhiGen_spat b.1.2,
    spatAct_apply, spatAct_apply, PhiGen_spat b.1.2, spatInv_spat]

/-! ## Rigidity: the spatial action determines the visible transformation -/

theorem proj_unital {u : W} (hu : IsInvertible u) : proj u w1 = w1 := by
  obtain ⟨h1, -⟩ := invW_spec hu
  rw [proj_apply, mul_one_W, h1]

theorem proj_multiplicative {u : W} (hu : IsInvertible u) (x y : W) :
    proj u (x ⋆ y) = proj u x ⋆ proj u y := by
  obtain ⟨h1, h2⟩ := invW_spec hu
  simp only [proj_apply]
  calc (u ⋆ (x ⋆ y)) ⋆ invW u
      = (u ⋆ (x ⋆ (w1 ⋆ y))) ⋆ invW u := by rw [one_mul_W]
    _ = (u ⋆ (x ⋆ ((invW u ⋆ u) ⋆ y))) ⋆ invW u := by rw [h2]
    _ = ((u ⋆ x) ⋆ invW u) ⋆ ((u ⋆ y) ⋆ invW u) := by simp only [mul_assoc_W]

/-- **PACKAGE C/D.**  If the induced spatial action of an internal core element is trivial,
the whole visible transformation is trivial.  This is the exact faithfulness statement, and
it uses the fact that the inherited carrier is generated by its spatial sector. -/
theorem proj_eq_id_of_spatAct_id {u : W} (hu : u ∈ Lift)
    (h : ∀ p : Vec3, spatAct (proj u) p = p) : proj u = LinearMap.id := by
  obtain ⟨n, θ, hn, rfl⟩ := (mem_Lift_iff_exists_Un u).1 hu
  refine linear_eq_id_of_fixes_spat _ (proj_unital (isInvertible_of_mem_Lift hu))
    (proj_multiplicative (isInvertible_of_mem_Lift hu)) ?_
  intro p
  have hp := h p
  rw [spatAct_apply, proj_Un hn, PhiGen_spat hn, spatInv_spat] at hp
  rw [proj_Un hn, PhiGen_spat hn, hp]

/-! ## Coordinates -/

/-- Coordinate vector of an inherited spatial vector. -/
def vc (p : Vec3) : Fin 3 → ℝ := ![p.1, p.2.1, p.2.2]

/-- The inherited spatial vector of a coordinate vector. -/
def cv (v : Fin 3 → ℝ) : Vec3 := (v 0, v 1, v 2)

@[simp] theorem cv_vc (p : Vec3) : cv (vc p) = p := rfl

@[simp] theorem vc_cv (v : Fin 3 → ℝ) : vc (cv v) = v := by
  funext i; fin_cases i <;> rfl

/-- The three inherited coordinate directions. -/
def be : Fin 3 → Vec3 := ![((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (0, 0, 1)]

theorem vec_decomp (p : Vec3) : p = p.1 • be 0 + p.2.1 • be 1 + p.2.2 • be 2 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp [be, Prod.smul_def, Prod.fst_add, Prod.snd_add]

/-- **PACKAGE C.**  The matrix of the induced spatial action in the inherited coordinate
directions. -/
noncomputable def rotMat (F : W →ₗ[ℝ] W) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => vc (spatAct F (be j)) i

theorem rotMat_mulVec (F : W →ₗ[ℝ] W) (p : Vec3) :
    rotMat F *ᵥ vc p = vc (spatAct F p) := by
  have hlin : spatAct F p
      = p.1 • spatAct F (be 0) + p.2.1 • spatAct F (be 1) + p.2.2 • spatAct F (be 2) := by
    conv_lhs => rw [vec_decomp p]
    simp only [map_add, map_smul]
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, rotMat, Matrix.of_apply, hlin]
  fin_cases i <;> simp [vc, Prod.fst_add, Prod.snd_add, Prod.smul_def] <;> ring

theorem rotMat_one : rotMat LinearMap.id = 1 := by
  refine Matrix.ext fun i j => ?_
  rw [rotMat, Matrix.of_apply, spatAct_one]
  fin_cases i <;> fin_cases j <;> simp [vc, be, Matrix.one_apply]

theorem rotMat_comp {F G : W →ₗ[ℝ] W} (hF : F ∈ visImage) (hG : G ∈ visImage) :
    rotMat (F.comp G) = rotMat F * rotMat G := by
  refine Matrix.ext fun i j => ?_
  have h1 : (rotMat F * rotMat G) i j = (rotMat F *ᵥ (fun k => rotMat G k j)) i := rfl
  have h2 : (fun k => rotMat G k j) = vc (spatAct G (be j)) := by
    funext k; rfl
  rw [h1, h2, rotMat_mulVec]
  rw [rotMat, Matrix.of_apply, spatAct_comp hF hG]

/-- **PACKAGE C.**  The matrix of a visible transformation is orthogonal. -/
theorem rotMat_mem_orthogonalGroup {F : W →ₗ[ℝ] W} (hF : F ∈ visImage) :
    rotMat F ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  refine (mul_eq_one_comm (M := Matrix (Fin 3) (Fin 3) ℝ)).1 ?_
  refine Matrix.ext fun j k => ?_
  have hjk : ((rotMat F)ᵀ * rotMat F) j k
      = h3 (spatAct F (be j)) (spatAct F (be k)) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, rotMat, Matrix.of_apply,
      Fin.sum_univ_three, h3, dot3, vc]
    simp
  rw [hjk, spatAct_preserves_inner hF]
  fin_cases j <;> fin_cases k <;> simp [h3, dot3, be, Matrix.one_apply]

/-- **PACKAGE C (item 36).**  Orientation preservation: the determinant of the matrix of a
visible transformation is `+1`.  This is computed directly from the inherited coordinate
action, not assumed. -/
theorem rotMat_det {F : W →ₗ[ℝ] W} (hF : F ∈ visImage) : (rotMat F).det = 1 := by
  obtain ⟨q, rfl⟩ := hF
  set n : Vec3 := (q.1 : Vec3) with hn_def
  set θ : ℝ := q.2 with hθ_def
  have hn : n.1 ^ 2 + n.2.1 ^ 2 + n.2.2 ^ 2 = 1 := by
    have h := q.1.2
    simp only [IsUnitAxis, h3, dot3] at h
    nlinarith [h]
  have hcs : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hentry : ∀ i j : Fin 3, rotMat (visMap q) i j = vc (rotv n θ (be j)) i := by
    intro i j
    rw [rotMat, Matrix.of_apply, visMap, spatAct_PhiGen q.1.2]
  rw [Matrix.det_fin_three]
  simp only [hentry]
  simp only [vc, be, rotv, spCross, h3, dot3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Prod.fst_add, Prod.snd_add,
    Prod.smul_def, smul_eq_mul]
  set c := Real.cos θ
  set s := Real.sin θ
  linear_combination (-c ^ 3 + c ^ 2 - c * n.1 ^ 2 * s ^ 2 - c * n.2.1 ^ 2 * s ^ 2
      - c * n.2.2 ^ 2 * s ^ 2 + n.1 ^ 2 * s ^ 2 + n.2.1 ^ 2 * s ^ 2 + n.2.2 ^ 2 * s ^ 2
      + s ^ 2) * hn + hcs

theorem rotMat_mem_SO3 {F : W →ₗ[ℝ] W} (hF : F ∈ visImage) :
    rotMat F ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  Matrix.mem_specialOrthogonalGroup_iff.2 ⟨rotMat_mem_orthogonalGroup hF, rotMat_det hF⟩

/-- **PACKAGE C (item 33).**  The candidate identification map from the visible image to the
standard three-dimensional special orthogonal group. -/
noncomputable def toRot : GvisG →* Matrix.specialOrthogonalGroup (Fin 3) ℝ where
  toFun U := ⟨rotMat (U : (Module.End ℝ W)ˣ), rotMat_mem_SO3 U.2⟩
  map_one' := by
    refine Subtype.ext ?_
    exact rotMat_one
  map_mul' U V := by
    refine Subtype.ext ?_
    exact rotMat_comp U.2 V.2

/-- **PACKAGE C (item 35).**  The candidate map is injective: the visible image acts
faithfully on the inherited three-dimensional spatial sector. -/
theorem spatAct_eq_id_of_rotMat_one {F : W →ₗ[ℝ] W} (h : rotMat F = 1) (p : Vec3) :
    spatAct F p = p := by
  have hv := rotMat_mulVec F p
  rw [h, Matrix.one_mulVec] at hv
  have h2 := congrArg cv hv
  simpa using h2.symm

theorem toRot_injective : Function.Injective toRot := by
  refine (injective_iff_map_eq_one toRot).2 ?_
  intro U hU
  have hrot : rotMat ((U : (Module.End ℝ W)ˣ) : Module.End ℝ W) = 1 := congrArg Subtype.val hU
  obtain ⟨q, hq⟩ := U.2
  have hid : proj (Un (q.1 : Vec3) q.2) = LinearMap.id := by
    refine proj_eq_id_of_spatAct_id (Un_mem_Lift q.1.2 q.2) ?_
    intro p
    rw [proj_Un q.1.2, ← visMap, hq]
    exact spatAct_eq_id_of_rotMat_one hrot p
  refine Subtype.ext (Units.ext ?_)
  rw [← hq, visMap, ← proj_Un q.1.2, hid]
  rfl

/-! ## Package D: the standard rotation group is exactly the visible image

The proof of surjectivity is the classical axis–angle argument, carried out here from the
inherited data: an orthogonal matrix of determinant one fixes a unit direction, acts on the
orthogonal plane of that direction as a plane rotation, and the resulting angle reproduces
the inherited coordinate action `rotv`.
-/

/-- The action of a real 3×3 matrix on the inherited spatial carrier. -/
noncomputable def matAct (M : Matrix (Fin 3) (Fin 3) ℝ) (p : Vec3) : Vec3 := cv (M *ᵥ vc p)

theorem vc_smul (a : ℝ) (p : Vec3) : vc (a • p) = a • vc p := by
  funext i; fin_cases i <;> simp [vc, Prod.smul_def]

theorem vc_add (p q : Vec3) : vc (p + q) = vc p + vc q := by
  funext i; fin_cases i <;> simp [vc, Prod.fst_add, Prod.snd_add]

theorem matAct_smul (M : Matrix (Fin 3) (Fin 3) ℝ) (a : ℝ) (p : Vec3) :
    matAct M (a • p) = a • matAct M p := by
  rw [matAct, matAct, vc_smul, Matrix.mulVec_smul]; rfl

theorem matAct_add (M : Matrix (Fin 3) (Fin 3) ℝ) (p q : Vec3) :
    matAct M (p + q) = matAct M p + matAct M q := by
  rw [matAct, matAct, matAct, vc_add, Matrix.mulVec_add]; rfl

theorem vc_matAct (M : Matrix (Fin 3) (Fin 3) ℝ) (p : Vec3) : vc (matAct M p) = M *ᵥ vc p := by
  rw [matAct, vc_cv]

theorem h3_eq_dot (p q : Vec3) : h3 p q = vc p ⬝ᵥ vc q := by
  simp [h3, dot3, vc, dotProduct, Fin.sum_univ_three]

theorem matAct_inner {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : Mᵀ * M = 1) (p q : Vec3) :
    h3 (matAct M p) (matAct M q) = h3 p q := by
  rw [h3_eq_dot, h3_eq_dot, vc_matAct, vc_matAct, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]

theorem h3_smul_smul (a b : ℝ) (p q : Vec3) : h3 (a • p) (b • q) = a * b * h3 p q := by
  simp [h3, dot3, Prod.smul_def]; ring

theorem h3_smul_right (a : ℝ) (p q : Vec3) : h3 p (a • q) = a * h3 p q := by
  simp [h3, dot3, Prod.smul_def]; ring

theorem h3_comb (a b a' b' : ℝ) (x y : Vec3) :
    h3 (a • x + b • y) (a' • x + b' • y)
      = a * a' * h3 x x + (a * b' + b * a') * h3 x y + b * b' * h3 y y := by
  simp [h3, dot3, Prod.smul_def, Prod.fst_add, Prod.snd_add]; ring

theorem h3_cross_left (n a : Vec3) : h3 n (spCross n a) = 0 := by
  simp [h3, dot3, spCross]; ring

theorem h3_cross_arg (n a : Vec3) : h3 a (spCross n a) = 0 := by
  simp [h3, dot3, spCross]; ring

theorem lagrange3 (n u : Vec3) :
    h3 (spCross n u) (spCross n u) = h3 n n * h3 u u - h3 n u * h3 n u := by
  simp [h3, dot3, spCross]; ring

theorem cross_cross (n u : Vec3) :
    spCross n (spCross n u) = (h3 n u) • n - (h3 n n) • u := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp [spCross, h3, dot3, Prod.smul_def] <;> ring

theorem h3_pos_of_ne_zero {p : Vec3} (hp : p ≠ 0) : 0 < h3 p p := by
  rcases lt_or_eq_of_le (NullSectorTask20.h3_self_nonneg p) with h | h
  · exact h
  · exact absurd ((NullSectorTask20.h3_self_eq_zero_iff p).1 h.symm) hp

theorem normalize_unit {w : Vec3} (hw : w ≠ 0) :
    h3 ((Real.sqrt (h3 w w))⁻¹ • w) ((Real.sqrt (h3 w w))⁻¹ • w) = 1 := by
  have hpos : 0 < h3 w w := h3_pos_of_ne_zero hw
  rw [h3_smul_smul]
  have hs : Real.sqrt (h3 w w) ^ 2 = h3 w w := Real.sq_sqrt hpos.le
  have hne : Real.sqrt (h3 w w) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  field_simp
  nlinarith [hs]

theorem exists_orthonormal_partner (n : Vec3) :
    ∃ u : Vec3, h3 u u = 1 ∧ h3 n u = 0 := by
  by_cases hz : n.2.1 = 0 ∧ n.2.2 = 0
  · exact ⟨(0, 1, 0), by simp [h3, dot3], by simp [h3, dot3, hz.1, hz.2]⟩
  · set w : Vec3 := (0, n.2.2, -n.2.1) with hw
    have hwne : w ≠ 0 := by
      intro h
      apply hz
      have h1 : w.2.1 = 0 := by rw [h]; rfl
      have h2 : w.2.2 = 0 := by rw [h]; rfl
      rw [hw] at h1 h2
      exact ⟨by simpa using neg_eq_zero.1 (by simpa using h2), by simpa using h1⟩
    refine ⟨(Real.sqrt (h3 w w))⁻¹ • w, normalize_unit hwne, ?_⟩
    rw [h3_smul_right]
    have hnw : h3 n w = 0 := by simp [h3, dot3, hw]; ring
    rw [hnw, mul_zero]

theorem frame_expansion {n u v : Vec3} (hn1 : h3 n n = 1) (hu1 : h3 u u = 1) (hv1 : h3 v v = 1)
    (hnu : h3 n u = 0) (hnv : h3 n v = 0) (huv : h3 u v = 0) (p : Vec3) :
    p = (h3 n p) • n + (h3 u p) • u + (h3 v p) • v := by
  set P : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![vc n, vc u, vc v] with hP
  simp only [h3, dot3] at hn1 hu1 hv1 hnu hnv huv
  have hPPt : P * Pᵀ = 1 := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [hP, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, vc] <;> linarith
  have hPtP : Pᵀ * P = 1 := mul_eq_one_comm.1 hPPt
  have e : ∀ j k : Fin 3, (vc n) j * (vc n) k + (vc u) j * (vc u) k + (vc v) j * (vc v) k
      = if j = k then (1 : ℝ) else 0 := by
    intro j k
    have h := congrFun (congrFun hPtP j) k
    simpa [hP, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
      Matrix.one_apply] using h
  have e00 := e 0 0; have e01 := e 0 1; have e02 := e 0 2
  have e10 := e 1 0; have e11 := e 1 1; have e12 := e 1 2
  have e20 := e 2 0; have e21 := e 2 1; have e22 := e 2 2
  simp [vc] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [h3, dot3, Prod.fst_add, Prod.snd_add, Prod.smul_def, smul_eq_mul]
  · linear_combination (-p.1) * e00 - p.2.1 * e01 - p.2.2 * e02
  · linear_combination (-p.1) * e10 - p.2.1 * e11 - p.2.2 * e12
  · linear_combination (-p.1) * e20 - p.2.1 * e21 - p.2.2 * e22

theorem exists_fixed_unit {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : Mᵀ * M = 1) (hdet : M.det = 1) :
    ∃ n : Vec3, h3 n n = 1 ∧ matAct M n = n := by
  have hMMt : M * Mᵀ = 1 := mul_eq_one_comm.1 hM
  have key : (M - 1).det = -((M - 1).det) := by
    calc (M - 1).det = (M * (1 - Mᵀ)).det := by rw [mul_sub, mul_one, hMMt]
      _ = M.det * (1 - Mᵀ).det := Matrix.det_mul _ _
      _ = (1 - Mᵀ).det := by rw [hdet, one_mul]
      _ = ((1 - M)ᵀ).det := by rw [Matrix.transpose_sub, Matrix.transpose_one]
      _ = (1 - M).det := Matrix.det_transpose _
      _ = (-(M - 1)).det := by rw [neg_sub]
      _ = (-1 : ℝ) ^ (Fintype.card (Fin 3)) * (M - 1).det := Matrix.det_neg _
      _ = -((M - 1).det) := by norm_num
  have hdet0 : (M - 1).det = 0 := by linarith
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
  have hfix : M *ᵥ x = x := by
    have hh := hx
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hh
    exact hh
  set p : Vec3 := cv x with hp
  have hpne : p ≠ 0 := by
    intro h
    refine hx0 ?_
    funext i
    fin_cases i <;> rw [hp] at h <;> simp [cv, Prod.ext_iff] at h <;> simp [h.1, h.2.1, h.2.2]
  refine ⟨(Real.sqrt (h3 p p))⁻¹ • p, normalize_unit hpne, ?_⟩
  rw [matAct_smul]
  congr 1
  rw [matAct, hp, vc_cv, hfix]

theorem exists_angle {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = c ∧ Real.sin θ = s := by
  have hc1 : -1 ≤ c := by nlinarith [sq_nonneg s, sq_nonneg (c + 1)]
  have hc2 : c ≤ 1 := by nlinarith [sq_nonneg s, sq_nonneg (c - 1)]
  by_cases hs : 0 ≤ s
  · refine ⟨Real.arccos c, Real.cos_arccos hc1 hc2, ?_⟩
    rw [Real.sin_arccos]
    have hsq : 1 - c ^ 2 = s ^ 2 := by linarith
    rw [hsq, Real.sqrt_sq hs]
  · refine ⟨-Real.arccos c, ?_, ?_⟩
    · rw [Real.cos_neg, Real.cos_arccos hc1 hc2]
    · rw [Real.sin_neg, Real.sin_arccos]
      have hsq : 1 - c ^ 2 = (-s) ^ 2 := by ring_nf; linarith
      rw [hsq, Real.sqrt_sq (by linarith)]
      ring

theorem rotv_add (n : Vec3) (θ : ℝ) (x y : Vec3) :
    rotv n θ (x + y) = rotv n θ x + rotv n θ y := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp [rotv, spCross, h3, dot3, Prod.smul_def] <;> ring

theorem rotv_smul (n : Vec3) (θ : ℝ) (r : ℝ) (x : Vec3) :
    rotv n θ (r • x) = r • rotv n θ x := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp [rotv, spCross, h3, dot3, Prod.smul_def] <;> ring

/-- The plane block of an orthonormal frame adapted to a fixed direction has determinant one:
this is where orientation preservation of the given matrix enters. -/
theorem frame_det {M : Matrix (Fin 3) (Fin 3) ℝ} {n u v : Vec3}
    (hn1 : h3 n n = 1) (hu1 : h3 u u = 1) (hv1 : h3 v v = 1)
    (hnu : h3 n u = 0) (hnv : h3 n v = 0) (huv : h3 u v = 0) {c s a b : ℝ}
    (hnfix : matAct M n = n) (hTu : matAct M u = c • u + s • v)
    (hTv : matAct M v = a • u + b • v) (hdet : M.det = 1) :
    c * b - a * s = 1 := by
  set fr : Fin 3 → Vec3 := ![n, u, v] with hfr
  set Q : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => vc (fr j) i with hQ
  set B : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, c, a; 0, s, b] with hB
  simp only [h3, dot3] at hn1 hu1 hv1 hnu hnv huv
  have hQtQ : Qᵀ * Q = 1 := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [hQ, hfr, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, vc] <;>
      linarith
  have hcol : ∀ (j : Fin 3) (i : Fin 3), (M * Q) i j = vc (matAct M (fr j)) i := by
    intro j i
    rw [vc_matAct]
    simp [hQ, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hMQ : M * Q = Q * B := by
    refine Matrix.ext fun i j => ?_
    rw [hcol j i]
    fin_cases j
    · simp [hQ, hB, hfr, Matrix.mul_apply, Fin.sum_univ_three, hnfix]
    · simp [hQ, hB, hfr, Matrix.mul_apply, Fin.sum_univ_three, hTu, vc_add, vc_smul]
      ring
    · simp [hQ, hB, hfr, Matrix.mul_apply, Fin.sum_univ_three, hTv, vc_add, vc_smul]
      ring
  have hq2 : Q.det * Q.det = 1 := by
    have h := congrArg Matrix.det hQtQ
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    exact h
  have hBeq : B = Qᵀ * (M * Q) := by
    rw [hMQ, ← Matrix.mul_assoc, hQtQ, Matrix.one_mul]
  have hdetB : B.det = 1 := by
    rw [hBeq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet]
    nlinarith [hq2]
  rw [Matrix.det_fin_three] at hdetB
  simp [hB] at hdetB
  linarith [hdetB]

/-- **PACKAGE D (item 40).**  The candidate map is surjective: every standard
three-dimensional rotation matrix is the matrix of a visible transformation.  The proof is
the axis–angle argument: the matrix fixes a unit direction, acts on the orthogonal plane by a
plane rotation whose determinant is forced to be `+1`, and the resulting angle reproduces the
inherited coordinate action. -/
theorem toRot_surjective : Function.Surjective toRot := by
  rintro ⟨M, hMem⟩
  obtain ⟨hOrth, hdet⟩ := Matrix.mem_specialOrthogonalGroup_iff.1 hMem
  have hMMt : M * Mᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).1 hOrth
  have hMtM : Mᵀ * M = 1 := mul_eq_one_comm.1 hMMt
  obtain ⟨n, hn1, hnfix⟩ := exists_fixed_unit hMtM hdet
  obtain ⟨u, hu1, hnu⟩ := exists_orthonormal_partner n
  set v : Vec3 := spCross n u with hvdef
  have hv1 : h3 v v = 1 := by rw [hvdef, lagrange3, hn1, hu1, hnu]; ring
  have hnv : h3 n v = 0 := h3_cross_left n u
  have huv : h3 u v = 0 := h3_cross_arg n u
  set c : ℝ := h3 u (matAct M u) with hcdef
  set s : ℝ := h3 v (matAct M u) with hsdef
  set a : ℝ := h3 u (matAct M v) with hadef
  set b : ℝ := h3 v (matAct M v) with hbdef
  have hnTu : h3 n (matAct M u) = 0 := by
    have h := matAct_inner hMtM n u
    rw [hnfix] at h
    rw [h, hnu]
  have hnTv : h3 n (matAct M v) = 0 := by
    have h := matAct_inner hMtM n v
    rw [hnfix] at h
    rw [h, hnv]
  have hTu : matAct M u = c • u + s • v := by
    have hexp := frame_expansion hn1 hu1 hv1 hnu hnv huv (matAct M u)
    rw [hnTu, zero_smul, zero_add] at hexp
    exact hexp
  have hTv : matAct M v = a • u + b • v := by
    have hexp := frame_expansion hn1 hu1 hv1 hnu hnv huv (matAct M v)
    rw [hnTv, zero_smul, zero_add] at hexp
    exact hexp
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    have h := matAct_inner hMtM u u
    rw [hTu, h3_comb, hu1, huv, hv1] at h
    nlinarith [h]
  have hab : a ^ 2 + b ^ 2 = 1 := by
    have h := matAct_inner hMtM v v
    rw [hTv, h3_comb, hu1, huv, hv1] at h
    nlinarith [h]
  have hortho : c * a + s * b = 0 := by
    have h := matAct_inner hMtM u v
    rw [hTu, hTv, h3_comb, hu1, huv, hv1] at h
    linarith [h]
  have hdetB : c * b - a * s = 1 :=
    frame_det hn1 hu1 hv1 hnu hnv huv hnfix hTu hTv hdet
  have ha : a = -s := by linear_combination c * hortho - a * hcs - s * hdetB
  have hb : b = c := by linear_combination c * hdetB + s * hortho - b * hcs
  obtain ⟨θ, hcos, hsin⟩ := exists_angle hcs
  have hru : rotv n θ u = matAct M u := by
    rw [hTu, rotv, hcos, hsin, hnu, hvdef]
    module
  have hrv : rotv n θ v = matAct M v := by
    rw [hTv, ha, hb, rotv, hcos, hsin, hnv, hvdef, cross_cross, hn1, hnu]
    module
  have hrn : rotv n θ n = matAct M n := by
    rw [hnfix, rotv_axis hn1]
  have key : ∀ p : Vec3, rotv n θ p = matAct M p := by
    intro p
    have hexp := frame_expansion hn1 hu1 hv1 hnu hnv huv p
    conv_lhs => rw [hexp]
    conv_rhs => rw [hexp]
    rw [rotv_add, rotv_add, rotv_smul, rotv_smul, rotv_smul, matAct_add, matAct_add,
      matAct_smul, matAct_smul, matAct_smul, hrn, hru, hrv]
  refine ⟨⟨projU (UnG hn1 θ), projU_mem_GvisG_of_LiftG (UnG_mem_LiftG hn1 θ)⟩, ?_⟩
  refine Subtype.ext ?_
  show rotMat (proj (Un n θ)) = M
  rw [proj_Un hn1]
  refine Matrix.ext fun i j => ?_
  rw [rotMat, Matrix.of_apply, spatAct_PhiGen hn1, key, vc_matAct]
  fin_cases j <;>
    simp [vc, be, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- **PACKAGE D, principal verdict.**  The intrinsic visible image is exactly the standard
three-dimensional special orthogonal group. -/
noncomputable def visibleRotationEquiv : GvisG ≃* Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  MulEquiv.ofBijective toRot ⟨toRot_injective, toRot_surjective⟩

end NullSectorTask21
