import RequestProject.Experiment2.NullSectorTask13.CarrierSlices

/-!
# Task 13, Layer 3: the central structure of the slices (§9, §10, §41)

The exact center `Z = spanℝ{1, S}` acts on every left carrier (INHERITED, Task 12).  Here
we determine what it does to the two axis-relative slices of an **arbitrary** minimal
carrier, and we classify the freedom in choosing a generator of a slice.

Nothing is inferred from the fact that a two-dimensional real space *could* be viewed as
a one-dimensional space over a quadratic extension: the statements below are proved from
the inherited sector relations, the centrality of `Z` and the inherited dimension count
(§9).

## Results

* `Kplus_central_stable`, `Kminus_central_stable` — both slices are `Z`-stable;
* `slice_plus_central_rank`, `slice_minus_central_rank` — each slice is the set of
  central multiples of any one of its nonzero elements, with *unique* coefficients:
  the exact central rank is one;
* `slice_generator_freedom` — the nonzero central elements act simply transitively on the
  generators of a slice, so a generator is never canonically selected (§10);
* `slice_plus_central_commutant` — the real-linear endomorphisms of a slice commuting with
  the restricted central action are exactly the central multiplications (§41, first
  commutant).
-/

namespace NullSectorTask13

open NullSectorTask08 NullSectorTask09 NullSectorTask10 NullSectorTask12

/-! ## §9 — central stability of the slices -/

/-- **DERIVED (§9).**  The plus slice of a left carrier is stable under the exact
center. -/
theorem Kplus_central_stable {L : Submodule ℝ W} (hL : IsLeftCarrier L) {z : W}
    (_hz : z ∈ Z) {ψ : W} (hψ : ψ ∈ Kplus L) : z ⋆ ψ ∈ Kplus L := by
  refine ⟨hL _ _ hψ.1, ?_⟩
  obtain ⟨a, b, rfl⟩ := (mem_Z_iff z).1 _hz
  rw [add_mul_W, smul_mul_W, smul_mul_W, one_mul_W]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hψ.2)
    (Submodule.smul_mem _ _ (wS_mul_mem_SectorPlus hψ.2))

/-- **DERIVED (§9).**  The minus slice of a left carrier is stable under the exact
center. -/
theorem Kminus_central_stable {L : Submodule ℝ W} (hL : IsLeftCarrier L) {z : W}
    (_hz : z ∈ Z) {ψ : W} (hψ : ψ ∈ Kminus L) : z ⋆ ψ ∈ Kminus L := by
  refine ⟨hL _ _ hψ.1, ?_⟩
  obtain ⟨a, b, rfl⟩ := (mem_Z_iff z).1 _hz
  rw [add_mul_W, smul_mul_W, smul_mul_W, one_mul_W]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hψ.2)
    (Submodule.smul_mem _ _ (wS_mul_mem_SectorMinus hψ.2))

theorem wS_mul_mem_Kplus {L : Submodule ℝ W} (hL : IsLeftCarrier L) {ψ : W}
    (hψ : ψ ∈ Kplus L) : wS ⋆ ψ ∈ Kplus L := by
  have := Kplus_central_stable hL (z := wS) wS_mem_Z hψ
  exact this

theorem wS_mul_mem_Kminus {L : Submodule ℝ W} (hL : IsLeftCarrier L) {ψ : W}
    (hψ : ψ ∈ Kminus L) : wS ⋆ ψ ∈ Kminus L := by
  have := Kminus_central_stable hL (z := wS) wS_mem_Z hψ
  exact this

/-! ## §9 — the exact central rank of a slice -/

theorem Zspan_le_Kplus {L : Submodule ℝ W} (hL : IsLeftCarrier L) {ψ : W}
    (hψ : ψ ∈ Kplus L) : Zspan ψ ≤ Kplus L := by
  intro y hy
  obtain ⟨a, b, rfl⟩ := (mem_Zspan_iff ψ y).1 hy
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hψ)
    (Submodule.smul_mem _ _ (wS_mul_mem_Kplus hL hψ))

theorem Zspan_le_Kminus {L : Submodule ℝ W} (hL : IsLeftCarrier L) {ψ : W}
    (hψ : ψ ∈ Kminus L) : Zspan ψ ≤ Kminus L := by
  intro y hy
  obtain ⟨a, b, rfl⟩ := (mem_Zspan_iff ψ y).1 hy
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hψ)
    (Submodule.smul_mem _ _ (wS_mul_mem_Kminus hL hψ))

/-- **PRINCIPAL THEOREM (§9): `slice_plus_central_rank`.**  Every nonzero element of the
plus slice of a minimal carrier generates the whole slice over the exact center: the
slice is the plane of its central multiples.  The exact central rank is one. -/
theorem Kplus_eq_Zspan {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) {ψ : W}
    (hψ : ψ ∈ Kplus L) (hne : ψ ≠ 0) : Kplus L = Zspan ψ := by
  refine (Submodule.eq_of_le_of_finrank_eq (Zspan_le_Kplus hL.1.1 hψ) ?_).symm
  rw [finrank_Zspan hne, finrank_Kplus hL]

/-- **PRINCIPAL THEOREM (§9): `slice_minus_central_rank`. -/
theorem Kminus_eq_Zspan {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L) {ψ : W}
    (hψ : ψ ∈ Kminus L) (hne : ψ ≠ 0) : Kminus L = Zspan ψ := by
  refine (Submodule.eq_of_le_of_finrank_eq (Zspan_le_Kminus hL.1.1 hψ) ?_).symm
  rw [finrank_Zspan hne, finrank_Kminus hL]

/-- **DERIVED (§9).**  Existence and uniqueness of the central representation
`φ = (a • 1 + b • S) ⋆ ψ` on the plus slice, for an arbitrary nonzero generator `ψ`. -/
theorem Kplus_central_representation {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L)
    {ψ : W} (hψ : ψ ∈ Kplus L) (hne : ψ ≠ 0) {φ : W} (hφ : φ ∈ Kplus L) :
    ∃! p : ℝ × ℝ, φ = zz p.1 p.2 ⋆ ψ := by
  have hmem : φ ∈ Zspan ψ := by rw [← Kplus_eq_Zspan hL hψ hne]; exact hφ
  obtain ⟨a, b, hab⟩ := (mem_Zspan_iff ψ φ).1 hmem
  refine ⟨(a, b), ?_, ?_⟩
  · show φ = zz a b ⋆ ψ
    rw [zz_mul]; exact hab.symm
  · rintro ⟨c, d⟩ hcd
    have hcd' : φ = zz c d ⋆ ψ := hcd
    have h : zz c d ⋆ ψ = zz a b ⋆ ψ := by
      rw [← hcd', zz_mul]; exact hab.symm
    have hzero : zz (c - a) (d - b) ⋆ ψ = 0 := by
      have hexp : zz (c - a) (d - b) ⋆ ψ = zz c d ⋆ ψ - zz a b ⋆ ψ := by
        simp only [zz_mul]
        module
      rw [hexp, h, sub_self]
    by_cases hcase : c - a = 0 ∧ d - b = 0
    · obtain ⟨h1, h2⟩ := hcase
      have hca : c = a := by linarith
      have hdb : d = b := by linarith
      simp [hca, hdb]
    · refine absurd ?_ (central_smul_ne_zero hne hcase)
      rw [← zz_mul]; exact hzero

/-- **DERIVED (§9).**  The same statement on the minus slice. -/
theorem Kminus_central_representation {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L)
    {ψ : W} (hψ : ψ ∈ Kminus L) (hne : ψ ≠ 0) {φ : W} (hφ : φ ∈ Kminus L) :
    ∃! p : ℝ × ℝ, φ = zz p.1 p.2 ⋆ ψ := by
  have hmem : φ ∈ Zspan ψ := by rw [← Kminus_eq_Zspan hL hψ hne]; exact hφ
  obtain ⟨a, b, hab⟩ := (mem_Zspan_iff ψ φ).1 hmem
  refine ⟨(a, b), ?_, ?_⟩
  · show φ = zz a b ⋆ ψ
    rw [zz_mul]; exact hab.symm
  · rintro ⟨c, d⟩ hcd
    have hcd' : φ = zz c d ⋆ ψ := hcd
    have h : zz c d ⋆ ψ = zz a b ⋆ ψ := by
      rw [← hcd', zz_mul]; exact hab.symm
    have hzero : zz (c - a) (d - b) ⋆ ψ = 0 := by
      have hexp : zz (c - a) (d - b) ⋆ ψ = zz c d ⋆ ψ - zz a b ⋆ ψ := by
        simp only [zz_mul]
        module
      rw [hexp, h, sub_self]
    by_cases hcase : c - a = 0 ∧ d - b = 0
    · obtain ⟨h1, h2⟩ := hcase
      have hca : c = a := by linarith
      have hdb : d = b := by linarith
      simp [hca, hdb]
    · refine absurd ?_ (central_smul_ne_zero hne hcase)
      rw [← zz_mul]; exact hzero

/-! ## §10 — generator freedom: the slice is not the same thing as a generator -/

/-- **PRINCIPAL CLASSIFICATION (§10): `SELECTION FREEDOM`.**  For an arbitrary minimal
carrier the generators of the plus slice are exactly its nonzero elements, and the
nonzero central elements act on them simply transitively: any generator is carried to any
other by exactly one central factor.  Nothing in the inherited structure selects one of
them, so the slice and a generator of the slice are kept strictly distinct. -/
theorem slice_generator_freedom {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L)
    {ψ : W} (hψ : ψ ∈ Kplus L) (hne : ψ ≠ 0) :
    (∀ a b : ℝ, ¬ (a = 0 ∧ b = 0) → zz a b ⋆ ψ ∈ Kplus L ∧ zz a b ⋆ ψ ≠ 0
        ∧ Kplus L = Zspan (zz a b ⋆ ψ)) ∧
    (∀ φ ∈ Kplus L, φ ≠ 0 → ∃! p : ℝ × ℝ, φ = zz p.1 p.2 ⋆ ψ) := by
  constructor
  · intro a b hab
    have hmem : zz a b ⋆ ψ ∈ Kplus L :=
      Kplus_central_stable hL.1.1 (zz_mem_Z a b) hψ
    have hne' : zz a b ⋆ ψ ≠ 0 := by
      rw [zz_mul]
      exact central_smul_ne_zero hne hab
    exact ⟨hmem, hne', Kplus_eq_Zspan hL hmem hne'⟩
  · intro φ hφ _
    exact Kplus_central_representation hL hψ hne hφ

/-! ## §41 — the commutant of the restricted central action on a slice -/

/-- The restricted action of the central element `S` on the plus slice. -/
noncomputable def SopP {L : Submodule ℝ W} (hL : IsLeftCarrier L) :
    Kplus L →ₗ[ℝ] Kplus L where
  toFun ψ := ⟨wS ⋆ (ψ : W), wS_mul_mem_Kplus hL ψ.2⟩
  map_add' := by intro ψ φ; apply Subtype.ext; exact mul_add_W wS (ψ : W) (φ : W)
  map_smul' := by intro c ψ; apply Subtype.ext; exact mul_smul_W c wS (ψ : W)

@[simp] theorem SopP_coe {L : Submodule ℝ W} (hL : IsLeftCarrier L) (ψ : Kplus L) :
    ((SopP hL ψ : Kplus L) : W) = wS ⋆ (ψ : W) := rfl

/-- The restricted action of the central element `S` on the minus slice. -/
noncomputable def SopM {L : Submodule ℝ W} (hL : IsLeftCarrier L) :
    Kminus L →ₗ[ℝ] Kminus L where
  toFun ψ := ⟨wS ⋆ (ψ : W), wS_mul_mem_Kminus hL ψ.2⟩
  map_add' := by intro ψ φ; apply Subtype.ext; exact mul_add_W wS (ψ : W) (φ : W)
  map_smul' := by intro c ψ; apply Subtype.ext; exact mul_smul_W c wS (ψ : W)

@[simp] theorem SopM_coe {L : Submodule ℝ W} (hL : IsLeftCarrier L) (ψ : Kminus L) :
    ((SopM hL ψ : Kminus L) : W) = wS ⋆ (ψ : W) := rfl

/-- **PRINCIPAL THEOREM (§41), plus slice.**  A real-linear endomorphism of the plus
slice commutes with the restricted central action **iff** it is multiplication by a fixed
central element.  The commutant of the central action therefore has exactly two real
parameters. -/
theorem slice_plus_central_commutant {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L)
    {ψ : W} (hψ : ψ ∈ Kplus L) (hne : ψ ≠ 0) (T : Kplus L →ₗ[ℝ] Kplus L) :
    (∀ φ : Kplus L, (T (SopP hL.1.1 φ) : W) = wS ⋆ ((T φ : Kplus L) : W)) ↔
      ∃ a b : ℝ, ∀ φ : Kplus L, ((T φ : Kplus L) : W) = zz a b ⋆ (φ : W) := by
  constructor
  · intro hT
    obtain ⟨a, b, hab⟩ := (mem_Zspan_iff ψ ((T ⟨ψ, hψ⟩ : Kplus L) : W)).1
      (by rw [← Kplus_eq_Zspan hL hψ hne]; exact (T ⟨ψ, hψ⟩).2)
    have hSS : wS ⋆ (wS ⋆ ψ) = -ψ := by
      rw [← mul_assoc_W, wit8_wS_wS, neg_mul_W, one_mul_W]
    have hexp : ∀ u v : ℝ, wS ⋆ (u • ψ + v • (wS ⋆ ψ)) = u • (wS ⋆ ψ) + v • (-ψ) := by
      intro u v; rw [mul_add_W, mul_smul_W, mul_smul_W, hSS]
    refine ⟨a, b, ?_⟩
    intro φ
    obtain ⟨c, d, hcd⟩ := (mem_Zspan_iff ψ (φ : W)).1
      (by rw [← Kplus_eq_Zspan hL hψ hne]; exact φ.2)
    have hφ : φ = c • (⟨ψ, hψ⟩ : Kplus L) + d • SopP hL.1.1 ⟨ψ, hψ⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_smul, SopP_coe]
      exact hcd.symm
    have hTφ : ((T φ : Kplus L) : W)
        = c • ((T ⟨ψ, hψ⟩ : Kplus L) : W)
          + d • ((T (SopP hL.1.1 ⟨ψ, hψ⟩) : Kplus L) : W) := by
      rw [hφ, map_add, map_smul, map_smul]
      simp
    rw [hTφ, hT ⟨ψ, hψ⟩, ← hab, zz_mul, ← hcd]
    simp only [hexp]
    module
  · rintro ⟨a, b, hab⟩ φ
    rw [hab, hab]
    simp only [SopP_coe]
    rw [← mul_assoc_W, ← mul_assoc_W, zz_central a b wS]

/-- **PRINCIPAL THEOREM (§41), minus slice.**  Same statement, proved independently on the
minus slice. -/
theorem slice_minus_central_commutant {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L)
    {ψ : W} (hψ : ψ ∈ Kminus L) (hne : ψ ≠ 0) (T : Kminus L →ₗ[ℝ] Kminus L) :
    (∀ φ : Kminus L, (T (SopM hL.1.1 φ) : W) = wS ⋆ ((T φ : Kminus L) : W)) ↔
      ∃ a b : ℝ, ∀ φ : Kminus L, ((T φ : Kminus L) : W) = zz a b ⋆ (φ : W) := by
  constructor
  · intro hT
    obtain ⟨a, b, hab⟩ := (mem_Zspan_iff ψ ((T ⟨ψ, hψ⟩ : Kminus L) : W)).1
      (by rw [← Kminus_eq_Zspan hL hψ hne]; exact (T ⟨ψ, hψ⟩).2)
    have hSS : wS ⋆ (wS ⋆ ψ) = -ψ := by
      rw [← mul_assoc_W, wit8_wS_wS, neg_mul_W, one_mul_W]
    have hexp : ∀ u v : ℝ, wS ⋆ (u • ψ + v • (wS ⋆ ψ)) = u • (wS ⋆ ψ) + v • (-ψ) := by
      intro u v; rw [mul_add_W, mul_smul_W, mul_smul_W, hSS]
    refine ⟨a, b, ?_⟩
    intro φ
    obtain ⟨c, d, hcd⟩ := (mem_Zspan_iff ψ (φ : W)).1
      (by rw [← Kminus_eq_Zspan hL hψ hne]; exact φ.2)
    have hφ : φ = c • (⟨ψ, hψ⟩ : Kminus L) + d • SopM hL.1.1 ⟨ψ, hψ⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_smul, SopM_coe]
      exact hcd.symm
    have hTφ : ((T φ : Kminus L) : W)
        = c • ((T ⟨ψ, hψ⟩ : Kminus L) : W)
          + d • ((T (SopM hL.1.1 ⟨ψ, hψ⟩) : Kminus L) : W) := by
      rw [hφ, map_add, map_smul, map_smul]
      simp
    rw [hTφ, hT ⟨ψ, hψ⟩, ← hab, zz_mul, ← hcd]
    simp only [hexp]
    module
  · rintro ⟨a, b, hab⟩ φ
    rw [hab, hab]
    simp only [SopM_coe]
    rw [← mul_assoc_W, ← mul_assoc_W, zz_central a b wS]

end NullSectorTask13
