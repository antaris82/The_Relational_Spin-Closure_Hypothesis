import RequestProject.Spine.Emergent.Symmetric

/-!
# Spine / Emergent : the base is not determined by the local data alone

**Fifth module of the manifold-emergence layer (Task 32, §7 Case 2).**

This module proves, at theorem level, the discriminating negative statement of Task 32:

> the local pieces alone — and hence anything defined *over* them, such as fibre transition
> data — do not determine the emergent base.

The witness is a pair of base-gluing data over the *same* index type and with the *same*
local domains, differing only in the incidence datum:

* `EmergentBase.symmetricGluing` — every pair of pieces completely incident;
* `EmergentBase.disjointGluing` — distinct pieces nowhere incident.

Their emergent bases are not homeomorphic: the first is connected and the second is not
(`EmergentBase.base_not_determined_by_local_pieces`).  Since the incidence datum is exactly
the part of `BaseGluingData` that no Spin/Lorentz fibre datum mentions, this is the precise
statement that base-incidence information is irreducibly additional; the forgetful
formulation is `EmergentBase.base_incidence_not_determined_by_local_piece_data` in
`RequestProject.Spine.Emergent.LocalPieceData`.  No claim of *minimality* of the primitive
is made here (Task-33 correction).

The Spin-level form of the same statement is `SpinNative.spin_data_do_not_determine_base` in
the comparison layer.  Note that the two Spin transition data there are *not* literally the
same typed object — they live over different covers of different bases; what the theorem
says is that the *same trivial transition law* `g_ij(x) = 1` holds on both covers while the
underlying emergent bases are non-homeomorphic (Task-33 correction of the earlier
"literally identical" wording).
-/

noncomputable section

namespace EmergentBase

universe u t

open BaseGluingData

variable {V : Type u} [TopologicalSpace V] {ι : Type t}

/-- **NEWLY DEFINED (Task 32).**  The *disjoint* base-gluing datum on a fixed open local
domain `D`: the same local pieces as `symmetricGluing`, but no incidence between distinct
pieces. -/
def disjointGluing (ι : Type t) [DecidableEq ι] {D : Set V} (hD : IsOpen D) :
    BaseGluingData V ι where
  D _ := D
  isOpen_D _ := hD
  W i j := if i = j then D else ∅
  isOpen_W i j := by by_cases h : i = j <;> simp [h, hD]
  W_subset i j := by by_cases h : i = j <;> simp [h]
  W_self i := by simp
  φ _ _ x := x
  continuousOn_φ _ _ := continuousOn_id
  φ_mapsTo i j := by
    by_cases h : i = j
    · subst h
      exact fun x hx => hx
    · simp only [if_neg h]
      exact fun x hx => absurd hx (by simp)
  φ_self _ _ _ := rfl
  φ_inv _ _ _ _ := rfl
  φ_cocycle i j k x hx h := by
    by_cases hij : i = j
    · subst hij
      by_cases hjk : i = k
      · subst hjk; exact ⟨hx, rfl⟩
      · simp [hjk] at h
    · simp [hij] at hx

namespace disjointGluing

variable [DecidableEq ι] {D : Set V} (hD : IsOpen D)

@[simp] theorem W_ne {i j : ι} (h : i ≠ j) : (disjointGluing ι hD).W i j = ∅ := by
  simp [disjointGluing, h]

/-- **DERIVED (Task 32).**  Points of distinct pieces are never identified. -/
theorem not_rel {i j : ι} (h : i ≠ j) (x : ((disjointGluing ι hD).D i : Set V))
    (y : ((disjointGluing ι hD).D j : Set V)) :
    ¬ (disjointGluing ι hD).Rel ⟨i, x⟩ ⟨j, y⟩ := by
  intro hrel
  have := hrel.1
  rw [W_ne hD h] at this
  exact this

/-- **DERIVED (Task 32).**  Distinct pieces have disjoint images in the emergent base. -/
theorem chartRange_disjoint {i j : ι} (h : i ≠ j) :
    Disjoint ((disjointGluing ι hD).chartRange i) ((disjointGluing ι hD).chartRange j) := by
  rw [Set.disjoint_left]
  rintro p ⟨x, rfl⟩ ⟨y, hy⟩
  exact not_rel hD h x y
    (((disjointGluing ι hD).mk_eq_mk_iff).1 (by exact hy.symm))

/-- **DERIVED (Task 32).**  With at least two indices and a nonempty local domain the
emergent base of the disjoint datum is disconnected. -/
theorem not_preconnectedSpace {i j : ι} (hij : i ≠ j) (hne : D.Nonempty) :
    ¬ PreconnectedSpace (Space (disjointGluing ι hD)) := by
  intro hpre
  have hopen := (disjointGluing ι hD).isOpen_chartRange i
  have hnonempty : ((disjointGluing ι hD).chartRange i).Nonempty :=
    ⟨(disjointGluing ι hD).chart i ⟨hne.choose, hne.choose_spec⟩, ⟨_, rfl⟩⟩
  have hnonempty' : ((disjointGluing ι hD).chartRange j).Nonempty :=
    ⟨(disjointGluing ι hD).chart j ⟨hne.choose, hne.choose_spec⟩, ⟨_, rfl⟩⟩
  have hcompl : ((disjointGluing ι hD).chartRange i)ᶜ.Nonempty := by
    obtain ⟨q, hq⟩ := hnonempty'
    refine ⟨q, ?_⟩
    intro hqi
    exact (Set.disjoint_left.1 (chartRange_disjoint hD hij)) hqi hq
  have hclosed : IsClosed ((disjointGluing ι hD).chartRange i) := by
    have hcomplUnion : ((disjointGluing ι hD).chartRange i)ᶜ
        = ⋃ k ∈ {k : ι | k ≠ i}, (disjointGluing ι hD).chartRange k := by
      ext p
      constructor
      · intro hp
        obtain ⟨q, rfl⟩ := (disjointGluing ι hD).mk_surjective p
        refine Set.mem_iUnion₂.2 ⟨q.1, ?_, ⟨q.2, rfl⟩⟩
        intro hqi
        exact hp (by rw [← hqi]; exact ⟨q.2, rfl⟩)
      · rintro hp hpi
        obtain ⟨k, hk, hpk⟩ := Set.mem_iUnion₂.1 hp
        exact (Set.disjoint_left.1 (chartRange_disjoint hD (Ne.symm hk))) hpi hpk
    rw [← isOpen_compl_iff, hcomplUnion]
    exact isOpen_biUnion fun k _ => (disjointGluing ι hD).isOpen_chartRange k
  rcases isClopen_iff.1 ⟨hclosed, hopen⟩ with h | h
  · exact hnonempty.ne_empty h
  · obtain ⟨q, hq⟩ := hcompl
    exact hq (h ▸ trivial)

end disjointGluing

/-- **DERIVED (Task 32), PRINCIPAL — the base-gluing gate falls in Case 2.**  Two base-gluing
data with the *same* local pieces but different incidence data have non-homeomorphic emergent
bases.  Hence the local pieces — and anything defined over them, such as fibre transition
data — cannot determine the base: an explicit incidence primitive is unavoidable. -/
theorem base_not_determined_by_local_pieces {D : Set V} (hD : IsOpen D) (hne : D.Nonempty)
    (hconn : IsPreconnected D) :
    (symmetricGluing Bool hD).D = (disjointGluing Bool hD).D ∧
      ¬ Nonempty (Space (symmetricGluing Bool hD) ≃ₜ Space (disjointGluing Bool hD)) := by
  refine ⟨rfl, ?_⟩
  rintro ⟨e⟩
  haveI : PreconnectedSpace (Space (symmetricGluing Bool hD)) :=
    symmetricGluing.preconnectedSpace hD hconn
  have : PreconnectedSpace (Space (disjointGluing Bool hD)) :=
    ⟨by
      simpa [Set.image_univ] using
        (isPreconnected_univ (α := Space (symmetricGluing Bool hD))).image e
          e.continuous.continuousOn⟩
  exact disjointGluing.not_preconnectedSpace hD (by decide : (false : Bool) ≠ true) hne this


end EmergentBase

end
