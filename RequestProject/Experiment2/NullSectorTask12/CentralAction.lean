import RequestProject.Experiment2.NullSectorTask12.LiftStability

/-!
# Task 12, Layer 9: the action of the central plane on a minimal carrier (§30, §31)

* **CENTRAL ACTION, automatic.**  A left carrier absorbs multiplication by *every*
  algebra element, so in particular `S ⋆ L ⊆ L` and `Z ⋆ L ⊆ L` hold with no extra
  hypothesis.
* The induced real-linear operator `ψ ↦ S ⋆ ψ` of a left carrier squares to minus the
  identity.  It is *not* called multiplication by a complex unit anywhere in this layer.
* **Z-rank two (§31).**  Every minimal left carrier admits two elements such that every
  element of the carrier is a sum of central multiples of them, in exactly one way.  This
  is stated purely with the inherited central plane; no complex vector-space dimension is
  imported.  Together with `dimℝ L = 4` this is the intrinsic count
  `Z-rank L = 2`.
-/

namespace NullSectorTask12

open NullSectorTask08 NullSectorTask09 NullSectorTask10

/-! ## The central action is automatic -/

/-- **DERIVED (§30).**  The central plane acts on every left carrier; nothing has to be
assumed. -/
theorem central_mul_mem {L : Submodule ℝ W} (hL : IsLeftCarrier L) {z : W} (_hz : z ∈ Z)
    {ψ : W} (hψ : ψ ∈ L) : z ⋆ ψ ∈ L := hL _ _ hψ

theorem wS_mul_mem_carrier {L : Submodule ℝ W} (hL : IsLeftCarrier L) {ψ : W}
    (hψ : ψ ∈ L) : wS ⋆ ψ ∈ L := hL _ _ hψ

/-- The induced real-linear operator of the central element `S` on a left carrier. -/
noncomputable def Sop {L : Submodule ℝ W} (hL : IsLeftCarrier L) : L →ₗ[ℝ] L where
  toFun ψ := ⟨wS ⋆ (ψ : W), hL _ _ ψ.2⟩
  map_add' := by
    intro ψ φ
    apply Subtype.ext
    exact mul_add_W wS (ψ : W) (φ : W)
  map_smul' := by
    intro c ψ
    apply Subtype.ext
    exact mul_smul_W c wS (ψ : W)

@[simp] theorem Sop_coe {L : Submodule ℝ W} (hL : IsLeftCarrier L) (ψ : L) :
    ((Sop hL ψ : L) : W) = wS ⋆ (ψ : W) := rfl

/-- **PRINCIPAL THEOREM (§30).**  The induced operator squares to minus the identity of
the carrier. -/
theorem Sop_sq {L : Submodule ℝ W} (hL : IsLeftCarrier L) (ψ : L) :
    Sop hL (Sop hL ψ) = -ψ := by
  apply Subtype.ext
  show wS ⋆ (wS ⋆ (ψ : W)) = -(ψ : W)
  rw [← mul_assoc_W, wit8_wS_wS, neg_mul_W, one_mul_W]

/-! ## Z-rank two -/

/-- **DERIVED.**  A nonzero central multiple of a nonzero element of a minimal carrier is
nonzero, hence the plane of central multiples of any nonzero element of the carrier is
two-dimensional. -/
theorem finrank_Zspan_of_mem {ψ : W} (hψ : ψ ≠ 0) : Module.finrank ℝ (Zspan ψ) = 2 :=
  finrank_Zspan hψ

theorem Zspan_le_of_mem {L : Submodule ℝ W} (hL : IsLeftCarrier L) {ψ : W} (hψ : ψ ∈ L) :
    Zspan ψ ≤ L := by
  intro y hy
  obtain ⟨z, -, rfl⟩ := (mem_Zspan_iff_central _ _).1 hy
  exact hL _ _ hψ

/-- **PRINCIPAL THEOREM (§31): `Z-rank = 2`.**  Every minimal left carrier is the direct
sum of the central multiples of two of its elements: every element of the carrier is a
sum of two central multiples in exactly one way. -/
theorem Zrank_two {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    ∃ ψ₁ ψ₂ : W, ψ₁ ∈ L ∧ ψ₂ ∈ L ∧
      (∀ ψ ∈ L, ∃ a b c d : ℝ,
        (a • w1 + b • wS) ⋆ ψ₁ + (c • w1 + d • wS) ⋆ ψ₂ = ψ) ∧
      (∀ a b c d : ℝ, (a • w1 + b • wS) ⋆ ψ₁ + (c • w1 + d • wS) ⋆ ψ₂ = 0 →
        a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) := by
  obtain ⟨e, he, hne, -, he0, he7, rfl⟩ := isMinimal_eq_Lgen_selfProduct hL
  have hcarrier : IsLeftCarrier (Lgen e) := isLeftCarrier_Lgen e
  have hL4 : Module.finrank ℝ (Lgen e) = 4 := finrank_of_isMinimal hL
  have hZle : Zspan e ≤ Lgen e := Zspan_le_of_mem hcarrier (self_mem_Lgen e)
  have hZ2 : Module.finrank ℝ (Zspan e) = 2 := finrank_Zspan hne
  have hZne : Zspan e ≠ Lgen e := by
    intro hcon
    rw [hcon, hL4] at hZ2
    norm_num at hZ2
  obtain ⟨ψ₂, hψ₂L, hψ₂Z⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hZle hZne)
  have hψ₂ne : ψ₂ ≠ 0 := by
    intro hzero
    exact hψ₂Z (by rw [hzero]; exact Submodule.zero_mem _)
  have hZ2' : Module.finrank ℝ (Zspan ψ₂) = 2 := finrank_Zspan hψ₂ne
  have hinf : Zspan e ⊓ Zspan ψ₂ = ⊥ := by
    refine le_bot_iff.1 ?_
    intro y hy
    obtain ⟨z, hz, hze⟩ := (mem_Zspan_iff_central _ _).1 (Submodule.mem_inf.1 hy).1
    obtain ⟨z', hz', hz'ψ⟩ := (mem_Zspan_iff_central _ _).1 (Submodule.mem_inf.1 hy).2
    obtain ⟨c, d, rfl⟩ := (mem_Z_iff z').1 hz'
    by_cases hcd : c = 0 ∧ d = 0
    · rw [hcd.1, hcd.2] at hz'ψ
      simp only [zero_smul, add_zero, zero_mul_W] at hz'ψ
      simp only [Submodule.mem_bot]
      rw [← hz'ψ]
    · exfalso
      refine hψ₂Z ?_
      have hinv := zinv_spec' (a := c) (b := d) hcd
      have : ψ₂ = zinv c d ⋆ ((c • w1 + d • wS) ⋆ ψ₂) := by
        rw [← mul_assoc_W, hinv, one_mul_W]
      rw [hz'ψ, ← hze] at this
      rw [this, ← mul_assoc_W]
      exact (mem_Zspan_iff_central _ _).2
        ⟨zinv c d ⋆ z, Z_mul_mem (by
          rw [zinv]; exact smul_add_smul_mem_Z _ _) hz, rfl⟩
  have hsup : Zspan e ⊔ Zspan ψ₂ = Lgen e := by
    have hle : Zspan e ⊔ Zspan ψ₂ ≤ Lgen e :=
      sup_le hZle (Zspan_le_of_mem hcarrier hψ₂L)
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (Zspan e) (Zspan ψ₂)
    rw [hinf, hZ2, hZ2'] at hdim
    simp only [finrank_bot, add_zero] at hdim
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim, hL4])
  refine ⟨e, ψ₂, self_mem_Lgen e, hψ₂L, ?_, ?_⟩
  · intro ψ hψ
    rw [← hsup] at hψ
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hψ
    obtain ⟨z, hz, rfl⟩ := (mem_Zspan_iff_central _ _).1 hy₁
    obtain ⟨z', hz', rfl⟩ := (mem_Zspan_iff_central _ _).1 hy₂
    obtain ⟨a, b, rfl⟩ := (mem_Z_iff z).1 hz
    obtain ⟨c, d, rfl⟩ := (mem_Z_iff z').1 hz'
    exact ⟨a, b, c, d, rfl⟩
  · intro a b c d hzero
    have h1 : (a • w1 + b • wS) ⋆ e ∈ Zspan e :=
      (mem_Zspan_iff_central _ _).2 ⟨_, smul_add_smul_mem_Z a b, rfl⟩
    have h2 : (c • w1 + d • wS) ⋆ ψ₂ ∈ Zspan ψ₂ :=
      (mem_Zspan_iff_central _ _).2 ⟨_, smul_add_smul_mem_Z c d, rfl⟩
    have hmem : (a • w1 + b • wS) ⋆ e ∈ Zspan e ⊓ Zspan ψ₂ := by
      refine Submodule.mem_inf.2 ⟨h1, ?_⟩
      have : (a • w1 + b • wS) ⋆ e = -((c • w1 + d • wS) ⋆ ψ₂) := by
        rw [eq_neg_iff_add_eq_zero]; exact hzero
      rw [this]
      exact Submodule.neg_mem _ h2
    rw [hinf, Submodule.mem_bot] at hmem
    have hab : a = 0 ∧ b = 0 := by
      by_contra hcon
      exact central_smul_ne_zero hne hcon (by rw [← zsmul_mul]; exact hmem)
    have hcd : c = 0 ∧ d = 0 := by
      by_contra hcon
      refine central_smul_ne_zero hψ₂ne hcon ?_
      rw [← zsmul_mul]
      rw [hmem, zero_add] at hzero
      exact hzero
    exact ⟨hab.1, hab.2, hcd.1, hcd.2⟩

/-- **PRINCIPAL SUMMARY (§30, §31).**  The central action on a minimal left carrier is
automatic, the induced operator of `S` squares to minus the identity, the real dimension
is four and the intrinsic count of independent central directions is two. -/
theorem central_action_report {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) :
    (∀ ψ ∈ L, wS ⋆ ψ ∈ L) ∧ (∀ ψ : L, Sop hL.1.1 (Sop hL.1.1 ψ) = -ψ) ∧
    Module.finrank ℝ L = 4 ∧
    ∃ ψ₁ ψ₂ : W, ψ₁ ∈ L ∧ ψ₂ ∈ L ∧
      (∀ ψ ∈ L, ∃ a b c d : ℝ,
        (a • w1 + b • wS) ⋆ ψ₁ + (c • w1 + d • wS) ⋆ ψ₂ = ψ) ∧
      (∀ a b c d : ℝ, (a • w1 + b • wS) ⋆ ψ₁ + (c • w1 + d • wS) ⋆ ψ₂ = 0 →
        a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) :=
  ⟨fun _ hψ => wS_mul_mem_carrier hL.1.1 hψ, fun ψ => Sop_sq hL.1.1 ψ,
    finrank_of_isMinimal hL, Zrank_two hL⟩

end NullSectorTask12
