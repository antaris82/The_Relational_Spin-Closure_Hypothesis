import RequestProject.Experiment2.NullSectorTask24.VisibleFrameAction

/-!
# Task 24, Packages D and E: freeness and transitivity

**Hard target A, second half.**

*Freeness* (items 30–32) is proved intrinsically along the preferred route: equality on the
three frame vectors, the frame spans `E`, maps agreeing on a frame agree everywhere, and
finally faithfulness of the inherited visible representation.  No theorem about a
conventional rotation group is transported.

*Transitivity* (items 33–37) constructs the candidate transformation as the unique linear map
carrying one frame to the other, in the inherited coordinates; it is orthogonal and
orientation preserving because both frames are orthonormal and positively oriented, and it
lies in the visible carrier by the already certified surjectivity theorem of Task 21
(item 34, "use the already-certified identification/surjectivity theorem for `Gvis`").

Combining the two gives the unique visible transformation between any two frames (items
36–38).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask24

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21 NullSectorTask23

open Matrix

/-! ## Package D — freeness -/

/-- **DERIVED (item 30, step 3).**  A visible transformation fixing the three vectors of one
frame fixes every element of `E`. -/
theorem gact_eq_self_of_fixes_frame {g : Gvis} {F : FramePlus}
    (h : ∀ i, gact g (F.vec i) = F.vec i) (p : E) : gact g p = p :=
  eq_of_agree_on_frame F (T := fun x => x) (gact_add g) (gact_smul g) (fun _ _ => rfl)
    (fun _ _ => rfl) h p

/-- **DERIVED (item 30, step 4).**  Faithfulness of the inherited visible representation, in
the coordinate form needed here. -/
theorem rotMat_eq_one_of_gact_id {g : Gvis} (h : ∀ p : E, gact g p = p) :
    rotMat ((g : (Module.End ℝ W)ˣ) : Module.End ℝ W) = 1 := by
  refine Matrix.ext fun i j => ?_
  have hb : spatAct ((g : (Module.End ℝ W)ˣ) : Module.End ℝ W) (be j) = be j := h (be j)
  rw [rotMat, Matrix.of_apply, hb]
  fin_cases i <;> fin_cases j <;> simp [vc, be]

theorem eq_one_of_gact_id {g : Gvis} (h : ∀ p : E, gact g p = p) : g = 1 := by
  have htr : toRot g = 1 := Subtype.ext (by
    show rotMat ((g : (Module.End ℝ W)ˣ) : Module.End ℝ W) = 1
    exact rotMat_eq_one_of_gact_id h)
  exact (injective_iff_map_eq_one toRot).1 toRot_injective g htr

/-- **PACKAGE D (item 32), principal endpoint.**  The visible action on the intrinsic frame
carrier is free. -/
theorem frameAction_free {g : Gvis} {F : FramePlus} (h : g • F = F) : g = 1 := by
  refine eq_one_of_gact_id (gact_eq_self_of_fixes_frame (F := F) fun i => ?_)
  have := congrArg (fun G : FramePlus => G.vec i) h
  simpa using this

theorem frameAction_free_iff (g : Gvis) (F : FramePlus) : g • F = F ↔ g = 1 := by
  constructor
  · exact fun h => frameAction_free h
  · rintro rfl; exact one_smul _ _

/-- **PACKAGE D.**  Cancellation form of freeness. -/
theorem frameAction_cancel {g g' : Gvis} {F : FramePlus} (h : g • F = g' • F) : g = g' := by
  have h1 : (g'⁻¹ * g) • F = F := by
    rw [frame_mul_smul, h, ← frame_mul_smul, inv_mul_cancel, frame_one_smul]
  have h2 : g'⁻¹ * g = 1 := frameAction_free h1
  exact (inv_mul_eq_one.1 h2).symm

/-! ## Package E — transitivity -/

theorem mat3_injective {f f' : Fin 3 → E} (h : mat3 f = mat3 f') (j : Fin 3) : f j = f' j := by
  have hv : vc (f j) = vc (f' j) := by
    funext i
    exact congrFun (congrFun h i) j
  calc f j = cv (vc (f j)) := (cv_vc _).symm
    _ = cv (vc (f' j)) := by rw [hv]
    _ = f' j := cv_vc _

/-- **NEWLY DEFINED (item 33/34).**  The candidate transformation between two frames, in the
inherited coordinates: the unique linear map carrying the first frame to the second. -/
def frameChange (F G : FramePlus) : Matrix (Fin 3) (Fin 3) ℝ := mat3 G.vec * (mat3 F.vec)ᵀ

theorem frameChange_orthogonal (F G : FramePlus) :
    frameChange F G ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  show frameChange F G * (frameChange F G)ᵀ = 1
  rw [frameChange, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (mat3 F.vec)ᵀ, mat3_transpose_mul F, Matrix.one_mul,
    mat3_mul_transpose G]

theorem frameChange_det (F G : FramePlus) : (frameChange F G).det = 1 := by
  rw [frameChange, Matrix.det_mul, Matrix.det_transpose, mat3_det_one F, mat3_det_one G,
    one_mul]

theorem frameChange_mem_SO3 (F G : FramePlus) :
    frameChange F G ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  Matrix.mem_specialOrthogonalGroup_iff.2 ⟨frameChange_orthogonal F G, frameChange_det F G⟩

theorem frameChange_mul_mat3 (F G : FramePlus) : frameChange F G * mat3 F.vec = mat3 G.vec := by
  rw [frameChange, Matrix.mul_assoc, mat3_transpose_mul F, Matrix.mul_one]

/-- **PACKAGE E (item 35), principal.**  Transitivity: some visible transformation carries a
given frame to any other. -/
theorem frameAction_transitive (F G : FramePlus) : ∃ g : Gvis, g • F = G := by
  obtain ⟨g, hg⟩ := toRot_surjective ⟨frameChange F G, frameChange_mem_SO3 F G⟩
  have hrot : rotMat ((g : (Module.End ℝ W)ˣ) : Module.End ℝ W) = frameChange F G :=
    congrArg Subtype.val hg
  have hmat : mat3 (fun i => gact g (F.vec i)) = mat3 G.vec := by
    rw [← rotMat_mul_mat3 g F.vec, hrot, frameChange_mul_mat3]
  exact ⟨g, FramePlus.ext fun i => mat3_injective hmat i⟩

noncomputable instance : MulAction.IsPretransitive Gvis FramePlus :=
  ⟨fun F G => frameAction_transitive F G⟩

/-- **PACKAGE E (item 37), principal endpoint.**  There is exactly one visible transformation
carrying a given frame to another. -/
theorem existsUnique_gvis_map_frame (F G : FramePlus) : ∃! g : Gvis, g • F = G := by
  obtain ⟨g, hg⟩ := frameAction_transitive F G
  refine ⟨g, hg, fun g' hg' => ?_⟩
  exact frameAction_cancel (hg'.trans hg.symm)

/-- **PACKAGE E (item 38).**  The packaged statement: the intrinsic frame carrier is a
nonempty, free and transitive visible set.  (The word *torsor* is used in the documentation
only; no general torsor API is developed.) -/
theorem framePlus_free_transitive :
    Nonempty FramePlus ∧ (∀ (g : Gvis) (F : FramePlus), g • F = F → g = 1) ∧
      (∀ F G : FramePlus, ∃! g : Gvis, g • F = G) :=
  ⟨framePlus_nonempty, fun _ _ h => frameAction_free h, existsUnique_gvis_map_frame⟩

/-- **PACKAGE D/E.**  Freeness in stabilizer form. -/
theorem stabilizer_frame_eq_bot (F : FramePlus) : MulAction.stabilizer Gvis F = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
  exact frameAction_free (MulAction.mem_stabilizer_iff.1 hg)

/-- **DERIVED.**  The unique visible transformation carrying one frame to another. -/
noncomputable def frameHom (F G : FramePlus) : Gvis := (existsUnique_gvis_map_frame F G).choose

@[simp] theorem frameHom_smul (F G : FramePlus) : frameHom F G • F = G :=
  (existsUnique_gvis_map_frame F G).choose_spec.1

theorem frameHom_unique {F G : FramePlus} {g : Gvis} (h : g • F = G) : g = frameHom F G :=
  frameAction_cancel (h.trans (frameHom_smul F G).symm)

@[simp] theorem frameHom_self (F : FramePlus) : frameHom F F = 1 :=
  (frameHom_unique (one_smul Gvis F)).symm

end NullSectorTask24
