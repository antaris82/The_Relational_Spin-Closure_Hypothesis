import RequestProject.Spine.E2.Family.FamilyBase

/-!
# Task 26, Package C: oriented orthonormal frames, fibrewise

**Hard target B, first half (items 38–44).**

For a single real inner-product space `V` with an orientation datum `o` we define the
carrier `FramePlusOf o` of *positively oriented orthonormal frames*: orthonormal bases of `V`
indexed by `Fin 3` whose orientation datum is exactly `o`.  The definition is intrinsic: no
reference frame, no group, no model carrier and no trivialization occurs in it.

For a `MetricOrientedRankThreeFamily B E` the fibrewise carrier is then

`FramePlusAt F b := FramePlusOf (F.orient b)`,

again intrinsic, and *not* identified with any fixed group (item 40) and not equipped with a
globally chosen element (item 44): only *existence* in each fibre is proved.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask26

open Module

universe u v

noncomputable section OneSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **NEWLY DEFINED (item 38), principal.**  The intrinsic carrier of positively oriented
orthonormal frames of the metric-oriented space `(V, o)`. -/
def FramePlusOf (o : Orientation ℝ V (Fin 3)) : Type _ :=
  {v : OrthonormalBasis (Fin 3) ℝ V // v.toBasis.orientation = o}

namespace FramePlusOf

variable {o : Orientation ℝ V (Fin 3)}

/-- The underlying orthonormal basis of a frame. -/
noncomputable def onb (v : FramePlusOf o) : OrthonormalBasis (Fin 3) ℝ V := v.1

/-- The three vectors of a frame. -/
noncomputable def vec (v : FramePlusOf o) (i : Fin 3) : V := v.1 i

@[simp] theorem onb_apply (v : FramePlusOf o) (i : Fin 3) : v.onb i = v.vec i := rfl

theorem orientation_eq (v : FramePlusOf o) : v.onb.toBasis.orientation = o := v.2

/-- **DERIVED (item 42).**  Frame equality is componentwise. -/
@[ext] theorem ext {v w : FramePlusOf o} (h : ∀ i, v.vec i = w.vec i) : v = w :=
  Subtype.ext (DFunLike.ext_iff.mpr h)

theorem eq_iff_vec {v w : FramePlusOf o} : v = w ↔ ∀ i, v.vec i = w.vec i :=
  ⟨fun h _ => by rw [h], ext⟩

/-- **DERIVED (item 42).**  The frame vectors are orthonormal. -/
theorem orthonormal (v : FramePlusOf o) : Orthonormal ℝ v.vec := v.onb.orthonormal

theorem inner_eq (v : FramePlusOf o) (i j : Fin 3) :
    (inner ℝ (v.vec i) (v.vec j)) = if i = j then 1 else 0 := by
  exact (orthonormal_iff_ite.1 v.orthonormal) i j

/-- **DERIVED (item 42), principal.**  The frame vectors form a basis of `V`. -/
noncomputable def basis (v : FramePlusOf o) : Basis (Fin 3) ℝ V := v.onb.toBasis

@[simp] theorem basis_apply (v : FramePlusOf o) (i : Fin 3) : v.basis i = v.vec i := by
  simp [basis, vec]

theorem linearIndependent (v : FramePlusOf o) : LinearIndependent ℝ v.vec := by
  simpa using v.basis.linearIndependent

theorem span_eq_top (v : FramePlusOf o) : Submodule.span ℝ (Set.range v.vec) = ⊤ := by
  have h : ⇑v.basis = v.vec := funext (basis_apply v)
  simpa [h] using v.basis.span_eq

theorem basis_orientation (v : FramePlusOf o) : v.basis.orientation = o := v.2

end FramePlusOf

/-- **DERIVED (item 43), principal.**  Existence of a positively oriented orthonormal frame
in a three-dimensional metric-oriented space.  The construction uses two classical
finite-dimensional library results: the existence of an orthonormal basis
(`stdOrthonormalBasis`) and the adjustment of an orthonormal basis to a prescribed
orientation (`OrthonormalBasis.adjustToOrientation`). -/
noncomputable def frameOfRankThree [FiniteDimensional ℝ V] (hV : finrank ℝ V = 3)
    (o : Orientation ℝ V (Fin 3)) : FramePlusOf o :=
  ⟨((stdOrthonormalBasis ℝ V).reindex (finCongr hV)).adjustToOrientation o,
    OrthonormalBasis.orientation_adjustToOrientation _ _⟩

theorem framePlusOf_nonempty [FiniteDimensional ℝ V] (hV : finrank ℝ V = 3)
    (o : Orientation ℝ V (Fin 3)) : Nonempty (FramePlusOf o) :=
  ⟨frameOfRankThree hV o⟩

/-! ### The transporter between two frames of one space -/

/-- **NEWLY DEFINED.**  The linear isometry of `V` carrying the frame `v` to the frame `w`,
constructed from the two coordinate isometries.  No group structure is used here. -/
noncomputable def frameTransport {o : Orientation ℝ V (Fin 3)} (v w : FramePlusOf o) :
    V ≃ₗᵢ[ℝ] V :=
  v.onb.repr.trans w.onb.repr.symm

@[simp] theorem frameTransport_apply_vec {o : Orientation ℝ V (Fin 3)} (v w : FramePlusOf o)
    (i : Fin 3) : frameTransport v w (v.vec i) = w.vec i := by
  show w.onb.repr.symm (v.onb.repr (v.onb i)) = w.onb i
  rw [OrthonormalBasis.repr_self, OrthonormalBasis.repr_symm_single]

end OneSpace

/-! ## The fibrewise frame carriers (items 38–44) -/

namespace MetricOrientedRankThreeFamily

variable {B : Type u} {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)]

/-- **NEWLY DEFINED (item 38), principal.**  The intrinsic carrier of positively oriented
orthonormal frames of the fibre over `b`.  It is defined from the fibre data alone. -/
def FramePlusAt (F : MetricOrientedRankThreeFamily B E) (b : B) : Type _ :=
  FramePlusOf (F.orient b)

/-- **DERIVED (item 43), principal.**  Every fibre has at least one positively oriented
orthonormal frame.  No frame is chosen globally. -/
theorem framePlusAt_nonempty (F : MetricOrientedRankThreeFamily B E) (b : B) :
    Nonempty (F.FramePlusAt b) := by
  haveI := F.finiteDimensional b
  exact framePlusOf_nonempty (F.rank_three b) (F.orient b)

instance (F : MetricOrientedRankThreeFamily B E) (b : B) : Nonempty (F.FramePlusAt b) :=
  F.framePlusAt_nonempty b

/-- **DERIVED (item 42).**  Fibrewise frame equality is componentwise. -/
theorem framePlusAt_ext {F : MetricOrientedRankThreeFamily B E} {b : B}
    {v w : F.FramePlusAt b} (h : ∀ i, FramePlusOf.vec v i = FramePlusOf.vec w i) : v = w :=
  FramePlusOf.ext h

/-- **DERIVED (item 42).**  Every fibrewise frame is a basis of its fibre. -/
noncomputable def framePlusAt_basis {F : MetricOrientedRankThreeFamily B E} {b : B}
    (v : F.FramePlusAt b) : Basis (Fin 3) ℝ (E b) :=
  FramePlusOf.basis v

end MetricOrientedRankThreeFamily

end NullSectorTask26
