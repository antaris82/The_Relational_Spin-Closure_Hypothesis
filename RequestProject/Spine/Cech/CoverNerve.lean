import RequestProject.Spine.Cech.Refinement
import RequestProject.Spine.E2.Cech.Cover

/-!
# Task 6 : the Task-3 cover as a nerve

This module connects the two representations of overlaps that Task 6 has to keep in step:

* the Task-3 representation, `CechSpinLift.CechCover.overlap₂ / overlap₃ / overlap₄`, which
  names the two-, three- and fourfold overlaps explicitly;
* the nerve representation `CechZ2.Nerve 𝓤.U n` of the Čech complex, whose elements are
  `(n+1)`-tuples of indices with nonempty overlap.

Both descriptions of an overlap are proved *equal as sets* (`inter_pair`, `inter_triple`,
`inter_quad`), so no new cover model is introduced: the Čech complex of Task 6 is built on the
Task-3 cover itself.  The constructors `nerve₁ / nerve₂ / nerve₃` turn a nonempty Task-3
overlap into a nerve simplex, the lemmas `nonempty₂ / nonempty₃ / nonempty₄` go the other way,
and `nerve₁_self / nerve₂_self / nerve₃_self` show the two passages are mutually inverse.  The
`face_*` lemmas compute the faces of a nerve simplex in terms of the index tuple.
-/

namespace CechSpinZ2

open CechSpinLift CechZ2

universe w t

variable {X : Type w} [TopologicalSpace X] {ι : Type t}

/-! ## The overlaps of a Task-3 cover are the nerve overlaps -/

theorem inter_single (𝓤 : CechCover X ι) (i : ι) : inter 𝓤.U ![i] = 𝓤.U i := by
  ext x
  rw [mem_inter_iff]
  constructor
  · intro h; exact h 0
  · intro h s; fin_cases s; simpa using h

theorem inter_pair (𝓤 : CechCover X ι) (i j : ι) : inter 𝓤.U ![i, j] = 𝓤.overlap₂ i j := by
  ext x
  rw [mem_inter_iff]
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · rintro ⟨h1, h2⟩ s; fin_cases s <;> simpa using ‹_›

theorem inter_triple (𝓤 : CechCover X ι) (i j k : ι) :
    inter 𝓤.U ![i, j, k] = 𝓤.overlap₃ i j k := by
  ext x
  rw [mem_inter_iff]
  constructor
  · intro h; exact ⟨⟨h 0, h 1⟩, h 2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩ s; fin_cases s <;> simpa using ‹_›

theorem inter_quad (𝓤 : CechCover X ι) (i j k l : ι) :
    inter 𝓤.U ![i, j, k, l] = 𝓤.overlap₄ i j k l := by
  ext x
  rw [mem_inter_iff]
  constructor
  · intro h; exact ⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ s; fin_cases s <;> simpa using ‹_›

/-! ## From Task-3 overlaps to nerve simplices -/

/-- A nonempty patch of the Task-3 cover, as a degree-`0` nerve simplex. -/
def nerve₀ (𝓤 : CechCover X ι) (i : ι) (h : (𝓤.U i).Nonempty) : Nerve 𝓤.U 0 :=
  ⟨![i], by rw [inter_single]; exact h⟩

/-- A nonempty double overlap of the Task-3 cover, as a degree-`1` nerve simplex. -/
def nerve₁ (𝓤 : CechCover X ι) (i j : ι) (h : (𝓤.overlap₂ i j).Nonempty) : Nerve 𝓤.U 1 :=
  ⟨![i, j], by rw [inter_pair]; exact h⟩

/-- A nonempty triple overlap of the Task-3 cover, as a degree-`2` nerve simplex. -/
def nerve₂ (𝓤 : CechCover X ι) (i j k : ι) (h : (𝓤.overlap₃ i j k).Nonempty) :
    Nerve 𝓤.U 2 :=
  ⟨![i, j, k], by rw [inter_triple]; exact h⟩

/-- A nonempty quadruple overlap of the Task-3 cover, as a degree-`3` nerve simplex. -/
def nerve₃ (𝓤 : CechCover X ι) (i j k l : ι) (h : (𝓤.overlap₄ i j k l).Nonempty) :
    Nerve 𝓤.U 3 :=
  ⟨![i, j, k, l], by rw [inter_quad]; exact h⟩

@[simp] theorem nerve₀_idx (𝓤 : CechCover X ι) (i : ι) (h : (𝓤.U i).Nonempty) :
    (nerve₀ 𝓤 i h).idx = ![i] := rfl

@[simp] theorem nerve₁_idx (𝓤 : CechCover X ι) (i j : ι) (h : (𝓤.overlap₂ i j).Nonempty) :
    (nerve₁ 𝓤 i j h).idx = ![i, j] := rfl

@[simp] theorem nerve₂_idx (𝓤 : CechCover X ι) (i j k : ι)
    (h : (𝓤.overlap₃ i j k).Nonempty) : (nerve₂ 𝓤 i j k h).idx = ![i, j, k] := rfl

@[simp] theorem nerve₃_idx (𝓤 : CechCover X ι) (i j k l : ι)
    (h : (𝓤.overlap₄ i j k l).Nonempty) : (nerve₃ 𝓤 i j k l h).idx = ![i, j, k, l] := rfl

/-! ## From nerve simplices to Task-3 overlaps -/

theorem mem_overlap₂_of_mem_inter {𝓤 : CechCover X ι} (σ : Nerve 𝓤.U 1) {x : X}
    (hx : x ∈ inter 𝓤.U σ.idx) : x ∈ 𝓤.overlap₂ (σ.idx 0) (σ.idx 1) := by
  rw [mem_inter_iff] at hx
  exact ⟨hx 0, hx 1⟩

theorem mem_overlap₃_of_mem_inter {𝓤 : CechCover X ι} (σ : Nerve 𝓤.U 2) {x : X}
    (hx : x ∈ inter 𝓤.U σ.idx) : x ∈ 𝓤.overlap₃ (σ.idx 0) (σ.idx 1) (σ.idx 2) := by
  rw [mem_inter_iff] at hx
  exact ⟨⟨hx 0, hx 1⟩, hx 2⟩

theorem mem_overlap₄_of_mem_inter {𝓤 : CechCover X ι} (σ : Nerve 𝓤.U 3) {x : X}
    (hx : x ∈ inter 𝓤.U σ.idx) :
    x ∈ 𝓤.overlap₄ (σ.idx 0) (σ.idx 1) (σ.idx 2) (σ.idx 3) := by
  rw [mem_inter_iff] at hx
  exact ⟨⟨⟨hx 0, hx 1⟩, hx 2⟩, hx 3⟩

theorem nonempty₂ {𝓤 : CechCover X ι} (σ : Nerve 𝓤.U 1) :
    (𝓤.overlap₂ (σ.idx 0) (σ.idx 1)).Nonempty :=
  let ⟨x, hx⟩ := σ.nonempty; ⟨x, mem_overlap₂_of_mem_inter σ hx⟩

theorem nonempty₃ {𝓤 : CechCover X ι} (σ : Nerve 𝓤.U 2) :
    (𝓤.overlap₃ (σ.idx 0) (σ.idx 1) (σ.idx 2)).Nonempty :=
  let ⟨x, hx⟩ := σ.nonempty; ⟨x, mem_overlap₃_of_mem_inter σ hx⟩

theorem nonempty₄ {𝓤 : CechCover X ι} (σ : Nerve 𝓤.U 3) :
    (𝓤.overlap₄ (σ.idx 0) (σ.idx 1) (σ.idx 2) (σ.idx 3)).Nonempty :=
  let ⟨x, hx⟩ := σ.nonempty; ⟨x, mem_overlap₄_of_mem_inter σ hx⟩

/-! ## The two passages are mutually inverse -/

theorem nerve₁_self {𝓤 : CechCover X ι} (σ : Nerve 𝓤.U 1)
    (h : (𝓤.overlap₂ (σ.idx 0) (σ.idx 1)).Nonempty) :
    nerve₁ 𝓤 (σ.idx 0) (σ.idx 1) h = σ := by
  apply Nerve.ext
  funext u
  fin_cases u <;> simp [nerve₁, Nerve.idx]

theorem nerve₂_self {𝓤 : CechCover X ι} (σ : Nerve 𝓤.U 2)
    (h : (𝓤.overlap₃ (σ.idx 0) (σ.idx 1) (σ.idx 2)).Nonempty) :
    nerve₂ 𝓤 (σ.idx 0) (σ.idx 1) (σ.idx 2) h = σ := by
  apply Nerve.ext
  funext u
  fin_cases u <;> simp [nerve₂, Nerve.idx]

theorem nerve₃_self {𝓤 : CechCover X ι} (σ : Nerve 𝓤.U 3)
    (h : (𝓤.overlap₄ (σ.idx 0) (σ.idx 1) (σ.idx 2) (σ.idx 3)).Nonempty) :
    nerve₃ 𝓤 (σ.idx 0) (σ.idx 1) (σ.idx 2) (σ.idx 3) h = σ := by
  apply Nerve.ext
  funext u
  fin_cases u <;> simp [nerve₃, Nerve.idx]

/-! ## Faces of a nerve simplex, in index form -/

theorem face₂_zero {𝓤 : CechCover X ι} (σ : Nerve 𝓤.U 2) :
    face 0 σ = nerve₁ 𝓤 (σ.idx 1) (σ.idx 2) (by
      obtain ⟨x, hx⟩ := (face (0 : Fin 3) σ).nonempty
      exact ⟨x, mem_overlap₂_of_mem_inter (face 0 σ) hx⟩) := by
  apply Nerve.ext
  funext u
  fin_cases u <;> rfl

theorem face₂_one {𝓤 : CechCover X ι} (σ : Nerve 𝓤.U 2) :
    face 1 σ = nerve₁ 𝓤 (σ.idx 0) (σ.idx 2) (by
      obtain ⟨x, hx⟩ := (face (1 : Fin 3) σ).nonempty
      exact ⟨x, mem_overlap₂_of_mem_inter (face 1 σ) hx⟩) := by
  apply Nerve.ext
  funext u
  fin_cases u <;> rfl

theorem face₂_two {𝓤 : CechCover X ι} (σ : Nerve 𝓤.U 2) :
    face 2 σ = nerve₁ 𝓤 (σ.idx 0) (σ.idx 1) (by
      obtain ⟨x, hx⟩ := (face (2 : Fin 3) σ).nonempty
      exact ⟨x, mem_overlap₂_of_mem_inter (face 2 σ) hx⟩) := by
  apply Nerve.ext
  funext u
  fin_cases u <;> rfl


/-! ## Faces of a nerve simplex built from an explicit index tuple -/

theorem face_nerve₁_zero (𝓤 : CechCover X ι) (i j : ι) (h : (𝓤.overlap₂ i j).Nonempty)
    (h' : (𝓤.U j).Nonempty) : face 0 (nerve₁ 𝓤 i j h) = nerve₀ 𝓤 j h' := by
  apply Nerve.ext
  funext u
  fin_cases u
  rfl

theorem face_nerve₁_one (𝓤 : CechCover X ι) (i j : ι) (h : (𝓤.overlap₂ i j).Nonempty)
    (h' : (𝓤.U i).Nonempty) : face 1 (nerve₁ 𝓤 i j h) = nerve₀ 𝓤 i h' := by
  apply Nerve.ext
  funext u
  fin_cases u
  rfl

theorem face_nerve₂_zero (𝓤 : CechCover X ι) (i j k : ι) (h : (𝓤.overlap₃ i j k).Nonempty)
    (h' : (𝓤.overlap₂ j k).Nonempty) : face 0 (nerve₂ 𝓤 i j k h) = nerve₁ 𝓤 j k h' := by
  apply Nerve.ext
  funext u
  fin_cases u <;> rfl

theorem face_nerve₂_one (𝓤 : CechCover X ι) (i j k : ι) (h : (𝓤.overlap₃ i j k).Nonempty)
    (h' : (𝓤.overlap₂ i k).Nonempty) : face 1 (nerve₂ 𝓤 i j k h) = nerve₁ 𝓤 i k h' := by
  apply Nerve.ext
  funext u
  fin_cases u <;> rfl

theorem face_nerve₂_two (𝓤 : CechCover X ι) (i j k : ι) (h : (𝓤.overlap₃ i j k).Nonempty)
    (h' : (𝓤.overlap₂ i j).Nonempty) : face 2 (nerve₂ 𝓤 i j k h) = nerve₁ 𝓤 i j h' := by
  apply Nerve.ext
  funext u
  fin_cases u <;> rfl

end CechSpinZ2
