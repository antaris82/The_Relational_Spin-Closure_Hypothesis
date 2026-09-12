import RequestProject.Experiment2.NullSectorTask10.SafeBase

/-!
# Task 10, Layer 1: the distinguished axis and the longitudinal/transverse split

Exactly **one** old normalized spatial direction is designated, namely the
inherited `dirA`.  This is a kinematic choice of coordinates only: no mass,
energy, frequency, wavelength or particle is attached to it, and the vocabulary
of this module is exhausted by

```
DISTINGUISHED AXIS,  LONGITUDINAL,  TRANSVERSE.
```

Everything below is proved from the inherited old rest-space data
(`Rest`, `dot3`, `dirA`, `dirB`, `dirC`) alone.
-/

namespace NullSectorTask10

open NullSectorTask01 NullSectorTask04 NullSectorTask07 NullSectorTask08
open NullSectorTask09

/-! ## The distinguished axis -/

/-- **THE DISTINGUISHED AXIS** (old carrier level): the inherited spatial
direction `dirA`.  Neutral name only. -/
def axis : Vec4 := dirA

@[simp] theorem axis_coords : axis = (0, 1, 0, 0) := rfl

/-- **LONGITUDINAL** old subspace: the real line of the distinguished axis. -/
def Long : Submodule ℝ Vec4 := Submodule.span ℝ {axis}

/-- **TRANSVERSE** old subspace: the real plane spanned by the two remaining
inherited spatial directions. -/
def Trans : Submodule ℝ Vec4 := Submodule.span ℝ {dirB, dirC}

theorem axis_mem_Long : axis ∈ Long := Submodule.subset_span rfl

theorem dirB_mem_Trans : dirB ∈ Trans := Submodule.subset_span (by simp)

theorem dirC_mem_Trans : dirC ∈ Trans := Submodule.subset_span (by simp)

theorem mem_Long_iff (X : Vec4) : X ∈ Long ↔ ∃ a : ℝ, X = a • axis := by
  rw [Long, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩

theorem mem_Trans_iff (X : Vec4) : X ∈ Trans ↔ ∃ b c : ℝ, X = b • dirB + c • dirC := by
  rw [Trans, Submodule.mem_span_pair]
  constructor
  · rintro ⟨b, c, rfl⟩; exact ⟨b, c, rfl⟩
  · rintro ⟨b, c, rfl⟩; exact ⟨b, c, rfl⟩

theorem Long_coords (X : Vec4) : X ∈ Long ↔ X = (0, X.2.1, 0, 0) := by
  rw [mem_Long_iff]
  constructor
  · rintro ⟨a, rfl⟩; simp [axis, dirA, sp, s₁]
  · intro h; exact ⟨X.2.1, by rw [h]; simp [axis, dirA, sp, s₁]⟩

theorem Trans_coords (X : Vec4) : X ∈ Trans ↔ X = (0, 0, X.2.2.1, X.2.2.2) := by
  rw [mem_Trans_iff]
  constructor
  · rintro ⟨b, c, rfl⟩; simp [dirB, dirC, sp, s₂, s₃]
  · intro h
    exact ⟨X.2.2.1, X.2.2.2, by rw [h]; simp [dirB, dirC, sp, s₂, s₃]⟩

/-! ## The decomposition of the old rest space -/

theorem Long_le_Rest : Long ≤ Rest := by
  rw [Long, Submodule.span_le]
  rintro X rfl
  simp [axis, dirA, sp]

theorem Trans_le_Rest : Trans ≤ Rest := by
  rw [Trans, Submodule.span_le]
  rintro X hX
  rcases hX with h | h <;> subst h <;> simp [dirB, dirC, sp]

/-- **DISJOINTNESS.**  The longitudinal line and the transverse plane meet only
in the origin. -/
theorem Long_inf_Trans : Long ⊓ Trans = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro X hX
  rw [Submodule.mem_inf] at hX
  obtain ⟨hL, hT⟩ := hX
  rw [Long_coords] at hL
  rw [Trans_coords] at hT
  have h1 : X.2.1 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.2.1) hT
    simpa using this
  have h2 : X.2.2.1 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.2.2.1) hL
    simpa using this
  have h3 : X.2.2.2 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.2.2.2) hL
    simpa using this
  have h0 : X.1 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.1) hL
    simpa using this
  simp only [Submodule.mem_bot]
  rw [show X = (X.1, X.2.1, X.2.2.1, X.2.2.2) from rfl, h0, h1, h2, h3]
  rfl

/-- **SPANNING.**  Together the longitudinal line and the transverse plane span
the whole inherited old rest space. -/
theorem Long_sup_Trans : Long ⊔ Trans = Rest := by
  refine le_antisymm (sup_le Long_le_Rest Trans_le_Rest) ?_
  intro X hX
  rw [mem_Rest] at hX
  have hdec : X = X.2.1 • axis + (X.2.2.1 • dirB + X.2.2.2 • dirC) := by
    rw [show X = (X.1, X.2.1, X.2.2.1, X.2.2.2) from rfl, hX]
    simp [axis, dirA, dirB, dirC, sp, s₁, s₂, s₃, Prod.ext_iff]
  rw [hdec]
  exact Submodule.add_mem_sup
    ((mem_Long_iff _).2 ⟨X.2.1, rfl⟩)
    ((mem_Trans_iff _).2 ⟨X.2.2.1, X.2.2.2, rfl⟩)

/-- **THE LONGITUDINAL/TRANSVERSE DECOMPOSITION.**  `Rest = Long ⊕ Trans` for
the chosen orthonormal old basis. -/
theorem rest_isCompl : IsCompl (Long.comap Rest.subtype) (Trans.comap Rest.subtype) := by
  constructor
  · rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    rintro ⟨X, hX⟩ ⟨hL, hT⟩
    have : X ∈ Long ⊓ Trans := ⟨hL, hT⟩
    rw [Long_inf_Trans] at this
    simp only [Submodule.mem_bot] at this
    simp only [Submodule.mem_bot, Submodule.mk_eq_zero]
    exact this
  · rw [codisjoint_iff]
    refine le_antisymm le_top ?_
    rintro ⟨X, hX⟩ -
    have hXm : X ∈ Long ⊔ Trans := by rw [Long_sup_Trans]; exact hX
    rcases Submodule.mem_sup.1 hXm with ⟨u, hu, v, hv, huv⟩
    have hu' : u ∈ Rest := Long_le_Rest hu
    have hv' : v ∈ Rest := Trans_le_Rest hv
    refine Submodule.mem_sup.2 ⟨⟨u, hu'⟩, hu, ⟨v, hv'⟩, hv, ?_⟩
    apply Subtype.ext
    simpa using huv

/-- The decomposition in explicit coordinates: every rest vector is uniquely a
longitudinal plus a transverse vector. -/
theorem rest_decomp_unique {X : Vec4} (hX : X ∈ Rest) :
    ∃! p : Vec4 × Vec4, p.1 ∈ Long ∧ p.2 ∈ Trans ∧ X = p.1 + p.2 := by
  refine ⟨(X.2.1 • axis, X.2.2.1 • dirB + X.2.2.2 • dirC), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (mem_Long_iff _).2 ⟨_, rfl⟩
  · exact (mem_Trans_iff _).2 ⟨_, _, rfl⟩
  · rw [mem_Rest] at hX
    rw [show X = (X.1, X.2.1, X.2.2.1, X.2.2.2) from rfl, hX]
    simp [axis, dirA, dirB, dirC, sp, s₁, s₂, s₃, Prod.ext_iff]
  · rintro ⟨u, v⟩ ⟨hu, hv, huv⟩
    dsimp only at hu hv huv
    rw [Long_coords] at hu
    rw [Trans_coords] at hv
    have e1 : X.2.1 = u.2.1 := by
      have := congrArg (fun Y : Vec4 => Y.2.1) huv
      have hv1 : v.2.1 = 0 := by
        have := congrArg (fun Y : Vec4 => Y.2.1) hv; simpa using this
      simpa [hv1] using this
    have e2 : X.2.2.1 = v.2.2.1 := by
      have := congrArg (fun Y : Vec4 => Y.2.2.1) huv
      have hu1 : u.2.2.1 = 0 := by
        have := congrArg (fun Y : Vec4 => Y.2.2.1) hu; simpa using this
      simpa [hu1] using this
    have e3 : X.2.2.2 = v.2.2.2 := by
      have := congrArg (fun Y : Vec4 => Y.2.2.2) huv
      have hu2 : u.2.2.2 = 0 := by
        have := congrArg (fun Y : Vec4 => Y.2.2.2) hu; simpa using this
      simpa [hu2] using this
    have hu' : u = X.2.1 • axis := by
      rw [hu, e1]; simp [axis, dirA, sp, s₁]
    have hv' : v = X.2.2.1 • dirB + X.2.2.2 • dirC := by
      rw [hv, e2, e3]; simp [dirB, dirC, sp, s₂, s₃]
    simp only [Prod.mk.injEq]
    exact ⟨hu', hv'⟩

/-! ## Orthogonality of the two sectors for the inherited Euclidean rest form -/

/-- The distinguished axis is `dot3`-orthogonal to the whole transverse
plane. -/
theorem axis_orthogonal_Trans {X : Vec4} (hX : X ∈ Trans) : dot3 axis.2 X.2 = 0 := by
  rw [Trans_coords] at hX
  rw [show axis.2 = ((1 : ℝ), (0 : ℝ), (0 : ℝ)) from rfl]
  have : X.2 = (0, X.2.2.1, X.2.2.2) := by
    conv_lhs => rw [hX]
  rw [this]
  simp

end NullSectorTask10
