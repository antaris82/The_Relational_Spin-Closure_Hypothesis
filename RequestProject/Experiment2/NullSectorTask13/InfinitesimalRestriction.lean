import RequestProject.Experiment2.NullSectorTask13.RelativeSectorAction
import RequestProject.Experiment2.NullSectorTask11.GeneratorSeparation

/-!
# Task 13, Layer 8: the restricted infinitesimal generator (§24, §25, §26)

The inherited Task-11 general infinitesimal implementer is

`G(α,β) = α • 1 + β • S − (1/2) • R`,

with `(α, β)` arbitrary (§19, §27).  Here left multiplication by `G(α,β)` is restricted to
the two axis-relative slices of an **arbitrary** minimal carrier and the exact restricted
generators are *derived* from the sector relations `R ⋆ ψ = ± S ⋆ ψ`; no coefficient is
inserted by hand (§24).

The classification into a common central part and a sector-distinguishing part follows
(§25), and the Task-10 rate parameter `λ` is kept strictly apart from `(α, β)` (§26).
-/

namespace NullSectorTask13

open NullSectorTask08 NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12

/-- **INHERITED (Task 11, §24).**  The general infinitesimal implementer. -/
noncomputable def Ggen (α β : ℝ) : W := zz α β - (2⁻¹ : ℝ) • wR

theorem Ggen_eq_leftGen (α β : ℝ) : Ggen α β = zc α β - (2⁻¹ : ℝ) • wR := by
  rw [Ggen, zz, zc]

/-! ## §24 — the exact restricted generators -/

/-- **PRINCIPAL THEOREM (§24): `infinitesimal_plus_exact`.**  On the plus sector — hence
on the plus slice of every minimal carrier — left multiplication by the general
infinitesimal implementer is multiplication by the central element
`α • 1 + (β − 1/2) • S`. -/
theorem infinitesimal_plus_exact {ψ : W} (hψ : ψ ∈ Hplus) (α β : ℝ) :
    Ggen α β ⋆ ψ = zz α (β - 2⁻¹) ⋆ ψ := by
  rw [Ggen, sub_mul_W, smul_mul_W, wR_mul_eq_wS_mul_of_mem_Hplus hψ, zz_mul, zz_mul]
  module

/-- **PRINCIPAL THEOREM (§24): `infinitesimal_minus_exact`.**  Independently derived on
the minus sector, from `R ⋆ ψ = -(S ⋆ ψ)`: the central element is
`α • 1 + (β + 1/2) • S`. -/
theorem infinitesimal_minus_exact {ψ : W} (hψ : ψ ∈ Hminus) (α β : ℝ) :
    Ggen α β ⋆ ψ = zz α (β + 2⁻¹) ⋆ ψ := by
  rw [Ggen, sub_mul_W, smul_mul_W, wR_mul_eq_neg_wS_mul_of_mem_Hminus hψ, zz_mul, zz_mul]
  module

/-- **DERIVED (§24).**  Both slices are stable under the restricted generator. -/
theorem infinitesimal_preserves_slices {L : Submodule ℝ W} (hL : IsLeftCarrier L)
    (α β : ℝ) :
    (∀ ψ ∈ Kplus L, Ggen α β ⋆ ψ ∈ Kplus L) ∧
    (∀ ψ ∈ Kminus L, Ggen α β ⋆ ψ ∈ Kminus L) := by
  constructor
  · intro ψ hψ
    rw [infinitesimal_plus_exact hψ.2]
    exact Kplus_central_stable hL (zz_mem_Z _ _) hψ
  · intro ψ hψ
    rw [infinitesimal_minus_exact hψ.2]
    exact Kminus_central_stable hL (zz_mem_Z _ _) hψ

/-! ## §25 — common versus relative infinitesimal freedom -/

/-- **PRINCIPAL THEOREM (§25): `infinitesimal_relative_exact`.**  The difference of the
two restricted generators is the fixed central element `-S`, for **every** `(α, β)`: the
whole residual freedom is common to the two slices and disappears completely from the
relative generator. -/
theorem infinitesimal_relative_exact (α β : ℝ) :
    zz α (β - 2⁻¹) - zz α (β + 2⁻¹) = -wS := by
  rw [zz, zz]
  module

/-- **PRINCIPAL CLASSIFICATION (§25).**  The exact split of the restricted infinitesimal
action: a **COMMON FACTOR** `α • 1 + β • S`, which acts identically on both slices, and a
**RELATIVE FACTOR** `∓ (1/2) • S`, which is completely independent of `(α, β)`.  No
combination of `α` and `β` affects the two slices differently, and no combination survives
in the relative generator. -/
theorem infinitesimal_common_relative_split (α β : ℝ) :
    zz α (β - 2⁻¹) = zz α β + (-(2⁻¹ : ℝ)) • wS ∧
    zz α (β + 2⁻¹) = zz α β + (2⁻¹ : ℝ) • wS ∧
    zz α (β - 2⁻¹) - zz α (β + 2⁻¹) = -wS ∧
    (∀ α' β' : ℝ, zz α' (β' - 2⁻¹) - zz α' (β' + 2⁻¹)
      = zz α (β - 2⁻¹) - zz α (β + 2⁻¹)) := by
  refine ⟨?_, ?_, infinitesimal_relative_exact α β, ?_⟩
  · rw [zz, zz]; module
  · rw [zz, zz]; module
  · intro α' β'
    rw [infinitesimal_relative_exact, infinitesimal_relative_exact]

/-- **DERIVED (§25).**  The two restricted generators agree for no value of the
parameters: the sector-distinguishing part never vanishes.  (Stated on a nonzero element
of the plus slice, where the difference of the two central factors acts by `-S`.) -/
theorem infinitesimal_sectors_never_agree {ψ : W} (hne : ψ ≠ 0) (α β : ℝ) :
    zz α (β - 2⁻¹) ⋆ ψ ≠ zz α (β + 2⁻¹) ⋆ ψ := by
  intro hcon
  have hzero : zz 0 (-1) ⋆ ψ = 0 := by
    have h : zz 0 (-1) = zz α (β - 2⁻¹) - zz α (β + 2⁻¹) := by
      rw [infinitesimal_relative_exact, zz]; module
    rw [h, sub_mul_W, hcon, sub_self]
  exact central_smul_ne_zero hne (by norm_num : ¬((0 : ℝ) = 0 ∧ (-1 : ℝ) = 0))
    (by rw [← zz_mul]; exact hzero)

/-! ## §26 — the Task-10 rate `λ` is not a combination of `α` and `β` -/

/-- **PRINCIPAL SEPARATION THEOREM (§26).**  The two freedoms are logically independent:
whatever `(α, β)`, the commutator of the infinitesimal implementer is exactly the
inherited algebra generator, i.e. the Task-10 rate is forced to `λ = 1`; while the whole
`(α, β)` plane is invisible to the algebra, changing only the internal carrier action.  In
particular `λ` is never identified with any combination of `α` and `β`. -/
theorem rate_versus_residual_separation (α β : ℝ) :
    inducedDer (Ggen α β) = Dgen ∧
    (∀ α' β' : ℝ, inducedDer (Ggen α' β') = inducedDer (Ggen α β)) ∧
    (∀ l : ℝ, (∀ x : W, inducedDer (Ggen α β) x = l • Dgen x) ↔ l = 1) := by
  have hD : ∀ a b : ℝ, inducedDer (Ggen a b) = Dgen := by
    intro a b
    rw [Ggen_eq_leftGen, inducedDer_generator]
  refine ⟨hD α β, fun α' β' => by rw [hD, hD], fun l => ?_⟩
  constructor
  · intro h
    have h2 := h wB
    rw [hD] at h2
    simp only [Dgen_wB] at h2
    have h3 := congrFun h2 3
    simp [wC] at h3
    linarith
  · intro h x
    rw [hD, h, one_smul]

/-- **DERIVED (§26).**  Nevertheless the residual parameters are *visible* on the reduced
carrier: distinct `(α, β)` give distinct restricted generators on both slices.  Algebra
invisibility and carrier visibility are different statements. -/
theorem residual_visible_on_carrier {ψ : W} (hne : ψ ≠ 0) {α β α' β' : ℝ}
    (hne' : ¬ (α = α' ∧ β = β')) :
    zz α (β - 2⁻¹) ⋆ ψ ≠ zz α' (β' - 2⁻¹) ⋆ ψ := by
  intro hcon
  have hzero : zz (α - α') (β - β') ⋆ ψ = 0 := by
    have h : zz (α - α') (β - β') = zz α (β - 2⁻¹) - zz α' (β' - 2⁻¹) := by
      rw [zz, zz, zz]; module
    rw [h, sub_mul_W, hcon, sub_self]
  refine central_smul_ne_zero hne ?_ (by rw [← zz_mul]; exact hzero)
  rintro ⟨h1, h2⟩
  exact hne' ⟨by linarith, by linarith⟩

end NullSectorTask13
