import RequestProject.Experiment2.NullSectorTask25.LiftedFrameEquivariance

/-!
# Task 25, Packages H, I, J: reference change upstairs

**Hard target C.**

Downstairs, Task 24 proved that there is *exactly one* visible element carrying one reference
frame to another (`existsUnique_gvis_map_frame`, inherited, not reproved).  Upstairs the
situation is strictly weaker and is classified here:

* Package H (items 52–56): the set of internal lifts of the unique downstairs reference
  change has exactly two elements; they differ by the unique nontrivial kernel sign; the set
  is exactly one free and transitive `KerSign`-orbit inside the fibre of `projCore`.  No lift
  is chosen permanently: every statement quantifies over the chosen lift.
* Package I (items 57–63): the inherited transfer map `liftedTransfer F₀ F₁ u₀ h₀` — whose
  dependence on the chosen lift `u₀` is already explicit in Task 24, so nothing has to be
  un-hidden — is equivariant for the new internal action.  **Convention check (item 60):** the
  inherited transfer multiplies the internal representative on the *right* by `u₀⁻¹` while the
  new action multiplies on the *left*; the two therefore commute exactly, and the plain
  (unconjugated) equivariance identity is the correct one.  This is recorded rather than
  assumed in advance.
* Package J (items 64–70): the two transfer maps attached to the two possible lifts differ by
  a *unique* kernel sign, and conversely multiplying the chosen lift by a kernel sign produces
  exactly the sign-shifted transfer.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask25

open NullSectorTask20 NullSectorTask21 NullSectorTask23 NullSectorTask24

/-! ## Kernel signs are involutions -/

/-- **DERIVED.**  Every kernel sign is its own inverse. -/
theorem kerSign_inv_self {e : LiftGrp} (he : e ∈ KerSign) : e⁻¹ = e := by
  have hinv : e⁻¹ ∈ KerSign := Subgroup.inv_mem _ he
  rcases mem_KerSign_iff'.1 he with rfl | rfl
  · simp
  · rcases mem_KerSign_iff'.1 hinv with h1 | h1
    · exact absurd (inv_eq_one.1 h1) lNegOne_ne_one
    · exact h1

/-! ## Package H — the two lifts of the unique downstairs reference change -/

/-- The set of internal lifts of a visible element. -/
def liftsOf (g : Gvis) : Set LiftGrp := {u : LiftGrp | projCore u = g}

theorem mem_liftsOf {g : Gvis} {u : LiftGrp} : u ∈ liftsOf g ↔ projCore u = g := Iff.rfl

/-- **DERIVED.**  The set of lifts of a visible element is nonempty (inherited surjectivity of
the certified projection). -/
theorem liftsOf_nonempty (g : Gvis) : (liftsOf g).Nonempty := by
  obtain ⟨u, hu⟩ := projCore_surjective g
  exact ⟨u, hu⟩

/-- **PACKAGE H (item 54), principal endpoint.**  Any two lifts of the same visible element
differ by a *unique* kernel sign. -/
theorem lifts_differ_unique_kerSign {g : Gvis} {u v : LiftGrp} (hu : u ∈ liftsOf g)
    (hv : v ∈ liftsOf g) : ∃! e : KerSign, v = (e : LiftGrp) * u := by
  obtain ⟨e, he, hve⟩ := projCore_eq_iff.1 (hu.trans hv.symm)
  refine ⟨⟨e, he⟩, hve, fun f hf => Subtype.ext ?_⟩
  have h1 : (f : LiftGrp) * u = e * u := by rw [← hf, hve]
  have h2 := congrArg (fun w : LiftGrp => w * u⁻¹) h1
  simpa [mul_assoc] using h2

/-- **PACKAGE H (item 56), principal endpoint.**  The set of lifts of a visible element is
exactly one `KerSign`-orbit: it is the orbit of any one of its elements, and the kernel-sign
action on it is free and transitive.  This is a theorem about the existing fibre of
`projCore`; no quotient is constructed. -/
theorem liftsOf_eq_kerSign_orbit {g : Gvis} {u : LiftGrp} (hu : u ∈ liftsOf g) :
    liftsOf g = (fun e : KerSign => (e : LiftGrp) * u) '' Set.univ ∧
      (∀ e f : KerSign, (e : LiftGrp) * u = (f : LiftGrp) * u → e = f) := by
  constructor
  · ext v
    constructor
    · intro hv
      obtain ⟨e, he⟩ := lifts_differ_unique_kerSign hu hv
      exact ⟨e, Set.mem_univ _, he.1.symm⟩
    · rintro ⟨e, -, rfl⟩
      show projCore ((e : LiftGrp) * u) = g
      rw [map_mul, MonoidHom.mem_ker.1 e.2, one_mul]
      exact hu
  · intro e f hef
    refine Subtype.ext ?_
    have h2 := congrArg (fun w : LiftGrp => w * u⁻¹) hef
    simpa [mul_assoc] using h2

/-- **PACKAGE H (item 53), principal endpoint.**  The unique downstairs reference change has
exactly two internal lifts, and they differ by the nontrivial kernel sign (item 55: no lift is
selected — both are displayed). -/
theorem two_lifts_of_reference_change (F₀ F₁ : FramePlus) :
    ∃ u : LiftGrp, liftsOf (frameHom F₀ F₁) = {u, lNegOne * u} ∧ u ≠ lNegOne * u := by
  obtain ⟨u, hu⟩ := liftsOf_nonempty (frameHom F₀ F₁)
  refine ⟨u, ?_, ?_⟩
  · ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hv
      obtain ⟨e, he⟩ := lifts_differ_unique_kerSign hu hv
      rcases mem_KerSign_iff'.1 e.2 with h1 | h1
      · exact Or.inl (by rw [he.1, h1, one_mul])
      · exact Or.inr (by rw [he.1, h1])
    · rintro (rfl | rfl)
      · exact hu
      · show projCore (lNegOne * u) = frameHom F₀ F₁
        rw [map_mul, projCore_lNegOne, one_mul]
        exact hu
  · intro h
    refine lNegOne_ne_one ?_
    have h2 := congrArg (fun w : LiftGrp => w * u⁻¹) h
    simpa [mul_assoc] using h2.symm

/-- **PACKAGE H (item 53).**  The same statement in cardinality form. -/
theorem liftsOf_reference_change_ncard (F₀ F₁ : FramePlus) :
    (liftsOf (frameHom F₀ F₁)).ncard = 2 := by
  obtain ⟨u, hset, hne⟩ := two_lifts_of_reference_change F₀ F₁
  rw [hset, Set.ncard_pair hne]

/-! ## Package I — equivariance of the lifted reference transfer -/

section Transfer

variable (F₀ F₁ : FramePlus) (u₀ : LiftGrp)

/-- **PACKAGE I (item 63), principal endpoint.**  For each valid chosen lift `u₀` of the
unique downstairs reference change, the inherited transfer map is equivariant for the new
internal action.  The inherited convention (right multiplication by `u₀⁻¹` on the internal
representative) commutes with the left action, so the plain identity — not a conjugated one —
is the correct statement. -/
theorem liftedTransfer_equivariant (h₀ : projCore u₀ = frameHom F₀ F₁) (a : LiftGrp)
    (x : LiftedFrame F₀) :
    liftedTransfer F₀ F₁ u₀ h₀ (a • x) = a • liftedTransfer F₀ F₁ u₀ h₀ x :=
  NullSectorTask24.LiftedFrame.ext (by
    show (a * x.elt) * u₀⁻¹ = a * (x.elt * u₀⁻¹)
    rw [mul_assoc])

/-- **PACKAGE I (item 61).**  Compatibility with the projection to ordinary frames
(inherited), restated next to the equivariance theorem. -/
theorem liftedTransfer_proj' (h₀ : projCore u₀ = frameHom F₀ F₁) (x : LiftedFrame F₀) :
    liftedFrameProj F₁ (liftedTransfer F₀ F₁ u₀ h₀ x) = liftedFrameProj F₀ x :=
  liftedTransfer_proj F₀ F₁ u₀ h₀ x

/-- **PACKAGE I (item 62).**  Compatibility with the kernel signs, now as a *corollary* of
the equivariance theorem and the kernel-restriction theorem. -/
theorem liftedTransfer_kerSign (h₀ : projCore u₀ = frameHom F₀ F₁) (e : KerSign)
    (x : LiftedFrame F₀) :
    liftedTransfer F₀ F₁ u₀ h₀ ((e : LiftGrp) • x)
      = (e : LiftGrp) • liftedTransfer F₀ F₁ u₀ h₀ x :=
  liftedTransfer_equivariant F₀ F₁ u₀ h₀ (e : LiftGrp) x

end Transfer

/-! ## Package J — the residual two-valued ambiguity of the lifted reference change -/

/-- **PACKAGE J (item 69), principal endpoint, converse direction.**  Multiplying a chosen
lift by a kernel sign produces exactly the sign-shifted transfer map. -/
theorem liftedTransfer_sign_shift (F₀ F₁ : FramePlus) (u₀ : LiftGrp) (e : KerSign)
    (h₀ : projCore u₀ = frameHom F₀ F₁)
    (h₁ : projCore ((e : LiftGrp) * u₀) = frameHom F₀ F₁) (x : LiftedFrame F₀) :
    liftedTransfer F₀ F₁ ((e : LiftGrp) * u₀) h₁ x
      = (e : LiftGrp) • liftedTransfer F₀ F₁ u₀ h₀ x :=
  NullSectorTask24.LiftedFrame.ext (by
    show x.elt * ((e : LiftGrp) * u₀)⁻¹ = (e : LiftGrp) * (x.elt * u₀⁻¹)
    rw [mul_inv_rev, kerSign_inv_self e.2, ← mul_assoc,
      KerSign_central e.2 (x.elt * u₀⁻¹)])

/-- **PACKAGE J (item 68), principal endpoint.**  The two transfer maps attached to two lifts
of the same downstairs reference change differ by a *unique* kernel sign, pointwise. -/
theorem liftedTransfer_difference_unique_kerSign (F₀ F₁ : FramePlus) (u v : LiftGrp)
    (hu : projCore u = frameHom F₀ F₁) (hv : projCore v = frameHom F₀ F₁) :
    ∃! e : KerSign, ∀ x : LiftedFrame F₀,
      liftedTransfer F₀ F₁ v hv x = (e : LiftGrp) • liftedTransfer F₀ F₁ u hu x := by
  obtain ⟨e, he⟩ := liftedTransfer_choice F₀ F₁ u v hu hv
  refine ⟨e, fun x => ?_, fun f hf => ?_⟩
  · exact (he x).trans (liftSmul_restrict_kerSign_eq_signSmul F₁ e _).symm
  · have h2 : ∀ x : LiftedFrame F₀,
        (f : LiftGrp) • liftedTransfer F₀ F₁ u hu x
          = (e : LiftGrp) • liftedTransfer F₀ F₁ u hu x := by
      intro x
      exact (hf x).symm.trans
        ((he x).trans (liftSmul_restrict_kerSign_eq_signSmul F₁ e _).symm)
    exact Subtype.ext (liftedFrameAction_cancel F₁
      (h2 (NullSectorTask24.LiftedFrame.mk F₀ 1)))

/-- **PACKAGE J (item 67).**  The same statement as an equality of *functions*, obtained by
extensionality from the pointwise version. -/
theorem liftedTransfer_difference_funext (F₀ F₁ : FramePlus) (u v : LiftGrp)
    (hu : projCore u = frameHom F₀ F₁) (hv : projCore v = frameHom F₀ F₁) :
    ∃! e : KerSign,
      (fun x : LiftedFrame F₀ => liftedTransfer F₀ F₁ v hv x)
        = fun x : LiftedFrame F₀ => (e : LiftGrp) • liftedTransfer F₀ F₁ u hu x := by
  obtain ⟨e, he, huniq⟩ := liftedTransfer_difference_unique_kerSign F₀ F₁ u v hu hv
  exact ⟨e, funext he, fun f hf => huniq f fun x => congrFun hf x⟩

/-- **PACKAGE J (item 70), final interpretation theorem.**  Downstairs, the reference change
is *unique*.  Upstairs, the possible lifted reference changes form a two-element family on
which the kernel sign acts freely and transitively, and the corresponding transfer maps differ
by exactly one kernel sign.  There is therefore **no** canonical lifted reference change; the
residual ambiguity is classified, not removed. -/
theorem reference_change_downstairs_unique_upstairs_two (F₀ F₁ : FramePlus) :
    (∃! g : Gvis, g • F₀ = F₁) ∧
      (liftsOf (frameHom F₀ F₁)).ncard = 2 ∧
      (∀ u v : LiftGrp, ∀ hu : projCore u = frameHom F₀ F₁,
        ∀ hv : projCore v = frameHom F₀ F₁,
          ∃! e : KerSign, ∀ x : LiftedFrame F₀,
            liftedTransfer F₀ F₁ v hv x = (e : LiftGrp) • liftedTransfer F₀ F₁ u hu x) :=
  ⟨existsUnique_gvis_map_frame F₀ F₁, liftsOf_reference_change_ncard F₀ F₁,
    fun u v hu hv => liftedTransfer_difference_unique_kerSign F₀ F₁ u v hu hv⟩

/-- **NEGATIVE CONTROL (item 89).**  Uniqueness of the reference change downstairs does not
give uniqueness upstairs: the fibre over the unique downstairs element has two distinct
members. -/
theorem reference_change_not_unique_upstairs (F₀ F₁ : FramePlus) :
    ∃ u v : LiftGrp, u ≠ v ∧ projCore u = frameHom F₀ F₁ ∧ projCore v = frameHom F₀ F₁ := by
  obtain ⟨u, hset, hne⟩ := two_lifts_of_reference_change F₀ F₁
  have hu : u ∈ liftsOf (frameHom F₀ F₁) := by rw [hset]; exact Or.inl rfl
  have hv : lNegOne * u ∈ liftsOf (frameHom F₀ F₁) := by rw [hset]; exact Or.inr rfl
  exact ⟨u, lNegOne * u, hne, hu, hv⟩

end NullSectorTask25
