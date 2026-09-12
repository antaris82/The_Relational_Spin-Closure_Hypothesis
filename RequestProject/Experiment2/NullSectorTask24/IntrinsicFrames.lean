import RequestProject.Experiment2.NullSectorTask24.SafeBase

/-!
# Task 24, Package B: oriented orthonormal frames, defined intrinsically

**Hard target A, first half.**

An intrinsic frame is an *ordered triple* of elements of the inherited carrier `E`, encoded
as a map `Fin 3 → E` (items 18, 23: extensionality is then exactly agreement of the three
vectors).  Orthonormality is stated by the exact inherited inner-product relations (item 19),
positive orientation by the minimal orientation datum of Package A (item 20), and
`FramePlus` is the resulting subtype (item 21).

The definition mentions neither the visible carrier nor any reference frame: a fixed
coordinate triple is used *only* to prove nonemptiness (item 22).

Items 24: every frame is a basis of `E`; the finite-dimensional linear algebra is the
existing `Basis.mk` interface, no general basis library is developed.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask24

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21 NullSectorTask23

open Matrix

/-! ## The two intrinsic predicates -/

/-- **NEWLY DEFINED (item 19).**  Exact orthonormality of an ordered triple, stated by the
inherited inner-product relations. -/
def IsOrthonormalTriple (f : Fin 3 → E) : Prop :=
  ∀ i j, h3 (f i) (f j) = if i = j then 1 else 0

/-- **NEWLY DEFINED (item 20).**  Positive orientation, stated with the minimal orientation
datum of Package A. -/
def IsPositivelyOriented (f : Fin 3 → E) : Prop := 0 < triple (f 0) (f 1) (f 2)

theorem on_self {f : Fin 3 → E} (h : IsOrthonormalTriple f) (i : Fin 3) : h3 (f i) (f i) = 1 := by
  simpa using h i i

theorem on_ne {f : Fin 3 → E} (h : IsOrthonormalTriple f) {i j : Fin 3} (hij : i ≠ j) :
    h3 (f i) (f j) = 0 := by
  simpa [hij] using h i j

/-! ## The intrinsic frame carrier (item 21) -/

/-- **NEWLY DEFINED (item 21), principal.**  The intrinsic carrier of positively oriented
orthonormal frames of `E`.  Note that neither the visible carrier nor any chosen reference
frame occurs in this definition. -/
def FramePlus : Type := {f : Fin 3 → E // IsOrthonormalTriple f ∧ IsPositivelyOriented f}

namespace FramePlus

/-- The three vectors of a frame. -/
def vec (F : FramePlus) : Fin 3 → E := F.1

theorem orthonormal (F : FramePlus) : IsOrthonormalTriple F.vec := F.2.1

theorem oriented (F : FramePlus) : IsPositivelyOriented F.vec := F.2.2

theorem self_ip (F : FramePlus) (i : Fin 3) : h3 (F.vec i) (F.vec i) = 1 := on_self F.2.1 i

theorem ne_ip (F : FramePlus) {i j : Fin 3} (hij : i ≠ j) : h3 (F.vec i) (F.vec j) = 0 :=
  on_ne F.2.1 hij

/-- **DERIVED (item 23).**  Extensionality: two frames are equal exactly when their three
vectors agree. -/
@[ext] theorem ext {F G : FramePlus} (h : ∀ i, F.vec i = G.vec i) : F = G :=
  Subtype.ext (funext h)

theorem ext_iff_three {F G : FramePlus} :
    F = G ↔ F.vec 0 = G.vec 0 ∧ F.vec 1 = G.vec 1 ∧ F.vec 2 = G.vec 2 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2⟩
    refine ext fun i => ?_
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

end FramePlus

/-! ## Nonemptiness (item 22)

The fixed inherited coordinate triple is used *only here*. -/

theorem be_orthonormal : IsOrthonormalTriple be := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [be, h3, dot3]

theorem be_oriented : IsPositivelyOriented be := by
  show 0 < triple (be 0) (be 1) (be 2)
  norm_num [triple_apply, be, Matrix.cons_val_two, Matrix.tail_cons]

/-- **DERIVED (item 22), principal.**  The intrinsic frame carrier is nonempty. -/
def coordFrame : FramePlus := ⟨be, be_orthonormal, be_oriented⟩

theorem framePlus_nonempty : Nonempty FramePlus := ⟨coordFrame⟩

instance : Nonempty FramePlus := framePlus_nonempty

/-! ## The matrix of a frame -/

theorem mat3_transpose_mul (F : FramePlus) : (mat3 F.vec)ᵀ * mat3 F.vec = 1 := by
  refine Matrix.ext fun j k => ?_
  rw [transpose_mul_mat3, F.orthonormal j k, Matrix.one_apply]

theorem mat3_mul_transpose (F : FramePlus) : mat3 F.vec * (mat3 F.vec)ᵀ = 1 :=
  mul_eq_one_comm.1 (mat3_transpose_mul F)

/-- **DERIVED.**  The matrix of a positively oriented orthonormal frame has determinant one.
Only the sign of the orientation datum is used. -/
theorem mat3_det_one (F : FramePlus) : (mat3 F.vec).det = 1 := by
  have hsq : (mat3 F.vec).det * (mat3 F.vec).det = 1 := by
    have h := congrArg Matrix.det (mat3_transpose_mul F)
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have hpos : 0 < (mat3 F.vec).det := by
    rw [det_mat3]; exact F.oriented
  nlinarith [hsq, hpos]

theorem triple_frame (F : FramePlus) : triple (F.vec 0) (F.vec 1) (F.vec 2) = 1 := by
  rw [← det_mat3]; exact mat3_det_one F

/-! ## Every frame is a basis (item 24) -/

/-- **DERIVED (item 24).**  The exact expansion of an arbitrary element of `E` in a frame. -/
theorem frame_expand (F : FramePlus) (p : E) :
    p = h3 (F.vec 0) p • F.vec 0 + h3 (F.vec 1) p • F.vec 1 + h3 (F.vec 2) p • F.vec 2 :=
  frame_expansion (F.self_ip 0) (F.self_ip 1) (F.self_ip 2)
    (F.ne_ip (by decide)) (F.ne_ip (by decide)) (F.ne_ip (by decide)) p

theorem frame_span (F : FramePlus) : Submodule.span ℝ (Set.range F.vec) = ⊤ := by
  refine eq_top_iff.2 fun p _ => ?_
  rw [frame_expand F p]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem frame_linearIndependent (F : FramePlus) : LinearIndependent ℝ F.vec := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (fun p : E => h3 (F.vec j) p) hc
  simp only [Fin.sum_univ_three] at h
  rw [ip_add_right, ip_add_right, ip_smul_right, ip_smul_right, ip_smul_right] at h
  have h0 : h3 (F.vec j) (F.vec 0) = if j = 0 then (1 : ℝ) else 0 := F.orthonormal j 0
  have h1 : h3 (F.vec j) (F.vec 1) = if j = 1 then (1 : ℝ) else 0 := F.orthonormal j 1
  have h2 : h3 (F.vec j) (F.vec 2) = if j = 2 then (1 : ℝ) else 0 := F.orthonormal j 2
  have hz : h3 (F.vec j) (0 : E) = 0 := by simp [h3, dot3]
  rw [h0, h1, h2, hz] at h
  fin_cases j <;> simpa using h

/-- **DERIVED (item 24), principal.**  Every intrinsic frame is a basis of `E`. -/
noncomputable def frameBasis (F : FramePlus) : Module.Basis (Fin 3) ℝ E :=
  Module.Basis.mk (frame_linearIndependent F) (by rw [frame_span F])

@[simp] theorem frameBasis_apply (F : FramePlus) (i : Fin 3) : frameBasis F i = F.vec i :=
  Module.Basis.mk_apply _ _ i

/-- **DERIVED.**  A linear map is determined by its values on a frame; the version needed
below is the pointwise one. -/
theorem eq_of_agree_on_frame (F : FramePlus) {S T : E → E}
    (hSadd : ∀ x y, S (x + y) = S x + S y) (hSsmul : ∀ (c : ℝ) x, S (c • x) = c • S x)
    (hTadd : ∀ x y, T (x + y) = T x + T y) (hTsmul : ∀ (c : ℝ) x, T (c • x) = c • T x)
    (h : ∀ i, S (F.vec i) = T (F.vec i)) (p : E) : S p = T p := by
  conv_lhs => rw [frame_expand F p]
  conv_rhs => rw [frame_expand F p]
  rw [hSadd, hSadd, hSsmul, hSsmul, hSsmul, hTadd, hTadd, hTsmul, hTsmul, hTsmul,
    h 0, h 1, h 2]

end NullSectorTask24
