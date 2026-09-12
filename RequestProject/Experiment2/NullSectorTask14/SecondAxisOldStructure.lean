import RequestProject.Experiment2.NullSectorTask14.SafeBase

/-!
# Task 14, Layer 1 (§9): the independent second-axis old-space decomposition

**INDEPENDENT SECOND-AXIS DERIVATION.**  The second distinguished direction is the
inherited old spatial direction `dirB`.  Its longitudinal line and transverse plane are
defined *intrinsically*, by the inherited spatial form alone:

```
Long_B := spanℝ {B},        Trans_B := {v ∈ Rest | h(v,B) = 0}.
```

In particular the transverse plane is **not** defined by naming an ordered basis; that
`{A, C}` is a basis of it is proved afterwards from the inherited orthogonality relations
(`old_carrier_data`, Task 08).

No A-axis formula and no spatial transformation is used anywhere in this module.
-/

namespace NullSectorTask14

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08 NullSectorTask09
open NullSectorTask10 NullSectorTask12 NullSectorTask13

/-! ## The two intrinsic subspaces -/

/-- **INDEPENDENT SECOND-AXIS DERIVATION (§9).**  The longitudinal line of the second
axis. -/
def LongB : Submodule ℝ Vec4 := Submodule.span ℝ {dirB}

/-- **INDEPENDENT SECOND-AXIS DERIVATION (§9).**  The transverse plane of the second axis:
the inherited rest vectors `h`-orthogonal to the second axis.  Defined by the inherited
form only — no ordered basis is inserted. -/
def TransB : Submodule ℝ Vec4 where
  carrier := {X | X ∈ Rest ∧ dot3 X.2 dirB.2 = 0}
  add_mem' := by
    rintro X Y ⟨hX, hX'⟩ ⟨hY, hY'⟩
    refine ⟨Submodule.add_mem _ hX hY, ?_⟩
    simp only [dot3_apply] at hX' hY' ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    linarith [hX', hY']
  zero_mem' := by
    refine ⟨Submodule.zero_mem _, ?_⟩
    simp [dirB, sp, s₂]
  smul_mem' := by
    rintro c X ⟨hX, hX'⟩
    refine ⟨Submodule.smul_mem _ c hX, ?_⟩
    simp only [dot3_apply] at hX' ⊢
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination c * hX'

theorem mem_TransB_iff (X : Vec4) :
    X ∈ TransB ↔ X ∈ Rest ∧ dot3 X.2 dirB.2 = 0 := Iff.rfl

theorem mem_LongB_iff (X : Vec4) : X ∈ LongB ↔ ∃ a : ℝ, X = a • dirB := by
  rw [LongB, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩

theorem dirB_mem_LongB : dirB ∈ LongB := Submodule.subset_span rfl

/-- **DERIVED (§9).**  Coordinate description of the second longitudinal line. -/
theorem LongB_coords (X : Vec4) : X ∈ LongB ↔ X = (0, 0, X.2.2.1, 0) := by
  rw [mem_LongB_iff]
  constructor
  · rintro ⟨a, rfl⟩; simp [dirB, sp, s₂]
  · intro hX
    exact ⟨X.2.2.1, by rw [hX]; simp [dirB, sp, s₂]⟩

/-- **DERIVED (§9).**  Coordinate description of the second transverse plane: the vanishing
of the temporal coordinate and of the second spatial coordinate. -/
theorem TransB_coords (X : Vec4) : X ∈ TransB ↔ X = (0, X.2.1, 0, X.2.2.2) := by
  rw [mem_TransB_iff, mem_Rest]
  constructor
  · rintro ⟨h0, horth⟩
    simp only [dirB, sp, s₂, dot3_apply] at horth
    have hy : X.2.2.1 = 0 := by simpa using horth
    simp [Prod.ext_iff, h0, hy]
  · intro hX
    constructor
    · rw [hX]
    · simp only [dirB, sp, s₂, dot3_apply]
      have : X.2.2.1 = 0 := by
        have := congrArg (fun Y : Vec4 => Y.2.2.1) hX
        simpa using this
      simp [this]

/-! ## The inherited old directions and the two subspaces -/

theorem dirA_mem_TransB : dirA ∈ TransB :=
  ⟨dirA_mem_Rest, by simp [dirA, dirB, s₁, s₂]⟩

theorem dirC_mem_TransB : dirC ∈ TransB :=
  ⟨dirC_mem_Rest, by simp [dirC, dirB, s₂, s₃]⟩

theorem LongB_le_Rest : LongB ≤ Rest := by
  rw [LongB, Submodule.span_le]
  rintro X rfl
  simp [dirB, sp]

theorem TransB_le_Rest : TransB ≤ Rest := fun _ hX => hX.1

/-! ## §9 — the decomposition `Rest = Long_B ⊕ Trans_B` -/

/-- **PRINCIPAL THEOREM (§9), part 1.**  The second longitudinal line and the second
transverse plane intersect trivially. -/
theorem LongB_inf_TransB : LongB ⊓ TransB = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro X hX
  rw [Submodule.mem_inf] at hX
  obtain ⟨hL, hT⟩ := hX
  rw [LongB_coords] at hL
  rw [TransB_coords] at hT
  have h1 : X.2.1 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.2.1) hL; simpa using this
  have h2 : X.2.2.1 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.2.2.1) hT; simpa using this
  have h3 : X.2.2.2 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.2.2.2) hL; simpa using this
  have h0 : X.1 = 0 := by
    have := congrArg (fun Y : Vec4 => Y.1) hL; simpa using this
  simp only [Submodule.mem_bot]
  rw [show X = (X.1, X.2.1, X.2.2.1, X.2.2.2) from rfl, h0, h1, h2, h3]
  rfl

/-- **PRINCIPAL THEOREM (§9), part 2.**  Together they span the inherited rest space. -/
theorem LongB_sup_TransB : LongB ⊔ TransB = Rest := by
  refine le_antisymm (sup_le LongB_le_Rest TransB_le_Rest) ?_
  intro X hX
  rw [mem_Rest] at hX
  have hdec : X = X.2.2.1 • dirB + (0, X.2.1, 0, X.2.2.2) := by
    rw [show X = (X.1, X.2.1, X.2.2.1, X.2.2.2) from rfl, hX]
    simp [dirB, sp, s₂, Prod.ext_iff]
  rw [hdec]
  refine Submodule.add_mem_sup ((mem_LongB_iff _).2 ⟨X.2.2.1, rfl⟩) ?_
  rw [TransB_coords]

/-- **PRINCIPAL THEOREM (§9): `second_axis_decomposition`.**  The inherited old spatial
space is the internal direct sum of the second longitudinal line and the second transverse
plane. -/
theorem second_axis_decomposition :
    IsCompl (LongB.comap Rest.subtype) (TransB.comap Rest.subtype) := by
  constructor
  · rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    rintro ⟨X, hX⟩ ⟨hL, hT⟩
    have hmem : X ∈ LongB ⊓ TransB := ⟨hL, hT⟩
    rw [LongB_inf_TransB] at hmem
    simp only [Submodule.mem_bot] at hmem
    simp only [Submodule.mem_bot, Submodule.mk_eq_zero]
    exact hmem
  · rw [codisjoint_iff]
    refine le_antisymm le_top ?_
    rintro ⟨X, hX⟩ -
    have hXm : X ∈ LongB ⊔ TransB := by rw [LongB_sup_TransB]; exact hX
    rcases Submodule.mem_sup.1 hXm with ⟨u, hu, v, hv, huv⟩
    refine Submodule.mem_sup.2 ⟨⟨u, LongB_le_Rest hu⟩, hu, ⟨v, TransB_le_Rest hv⟩, hv, ?_⟩
    apply Subtype.ext
    simpa using huv

/-! ## §9 — the exact real dimension of the second transverse plane -/

/-- **DERIVED (§9).**  `{A, C}` spans the second transverse plane.  This is *proved* from
the inherited orthogonality relations, not built into the definition. -/
theorem TransB_eq_span : TransB = Submodule.span ℝ {dirA, dirC} := by
  refine le_antisymm ?_ ?_
  · intro X hX
    rw [TransB_coords] at hX
    have hdec : X = X.2.1 • dirA + X.2.2.2 • dirC := by
      conv_lhs => rw [hX]
      simp [dirA, dirC, sp, s₁, s₃, Prod.ext_iff]
    rw [hdec]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [Submodule.span_le]
    rintro X hX
    rcases hX with h | h <;> subst h
    · exact dirA_mem_TransB
    · exact dirC_mem_TransB

theorem dirA_dirC_linearIndependent : LinearIndependent ℝ ![dirA, dirC] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (fun Y : Vec4 => Y.2.1) hst
  have h2 := congrArg (fun Y : Vec4 => Y.2.2.2) hst
  simp [dirA, dirC, sp, s₁, s₃] at h1 h2
  exact ⟨h1, h2⟩

/-- **PRINCIPAL THEOREM (§9): `second_axis_transverse_dimension`.**  The inherited real
dimension of the second transverse plane is exactly two. -/
theorem finrank_TransB : Module.finrank ℝ (TransB : Submodule ℝ Vec4) = 2 := by
  have hspan : TransB = Submodule.span ℝ (Set.range ![dirA, dirC]) := by
    rw [TransB_eq_span]
    congr 1
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
  rw [hspan, finrank_span_eq_card dirA_dirC_linearIndependent]
  simp

/-- **DERIVED (§9).**  The second longitudinal line has dimension one. -/
theorem finrank_LongB : Module.finrank ℝ (LongB : Submodule ℝ Vec4) = 1 := by
  have hne : dirB ≠ 0 := by
    intro hcon
    have := congrArg (fun Y : Vec4 => Y.2.2.1) hcon
    simp [dirB, sp, s₂] at this
  rw [LongB, finrank_span_singleton hne]

end NullSectorTask14
