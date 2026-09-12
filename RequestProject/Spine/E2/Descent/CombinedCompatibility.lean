import RequestProject.Spine.E2.Descent.RefinementBehavior

/-!
# Task 29, Packages M and N: pairwise descent under kernel adjustment, and the combined
one-adjustment criterion

**SYNTHESIS OF HARD TARGETS A–C (items 82–93).**

Package M computes exactly how the same-pair discrepancy `κ` changes under an admissible
kernel adjustment,

`κ'_ijαβ = (ε_ijβ * ε_ijα⁻¹) * κ_ijαβ`,

defines `CanDescendPairwise` (existence of an adjustment making every same-pair discrepancy
trivial) and characterizes it by gluing of the adjusted representatives on each *original*
pair overlap.

Package N settles the combined criterion.  Because Package D proved that triple-defect
freeness already forces same-pair agreement — *for the same representatives, hence for the
same adjustment* — no second, possibly incompatible, adjustment is needed:

`CompatibilityReady C := CanTrivialise C`

and the required endpoint
`compatibility_ready_iff_single_adjustment_solves_all_required_kernel_equations` states that
this is equivalent to the existence of **one** admissible kernel adjustment which
simultaneously trivializes all triple defects *and* all same-pair discrepancies.  The
combined condition is therefore **not** strictly stronger than simultaneous trivializability
(item 93), and this is proved rather than assumed.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask29

universe u v w t

open NullSectorTask28
open NullSectorTask28.InternalProjection

section Combined

variable {L : Type w} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {P : InternalProjection L G} {B : Type u}
  [TopologicalSpace B] {ι : Type t} {S : TransitionSystem B ι G}

/-! ## Package M — the same-pair discrepancy under a kernel adjustment -/

/-- **PACKAGE M (items 82, 83), principal.**  The exact transformation law of the same-pair
discrepancy under an admissible kernel adjustment `u'_ijα = ε_ijα * u_ijα`:

`κ'_ijαβ = (ε_ijβ * ε_ijα⁻¹) * κ_ijαβ`,

the order being forced by centrality of the kernel. -/
theorem kappa_adjust (C : InternalTransitionCandidate P S) (ε : Adj C) (i j : ι)
    (a b : C.Idx i j) {x : ↥(S.U i ∩ S.U j)} (hx : x ∈ C.V i j a) :
    kappa (adjust C ε) i j a b x
      = (ε.e i j b x * (ε.e i j a x)⁻¹) * kappa C i j a b x := by
  have hker : ε.e i j a x ∈ P.Ker := (ε.e_isKer i j a).2 x hx
  have hcomm : Commute (ε.e i j a x)⁻¹ (C.u i j b x * (C.u i j a x)⁻¹) :=
    (P.ker_commute hker _).inv_left
  simp only [kappa_apply, adjust_u, mul_inv_rev]
  calc ε.e i j b x * C.u i j b x * ((C.u i j a x)⁻¹ * (ε.e i j a x)⁻¹)
      = ε.e i j b x * ((C.u i j b x * (C.u i j a x)⁻¹) * (ε.e i j a x)⁻¹) := by group
    _ = ε.e i j b x * ((ε.e i j a x)⁻¹ * (C.u i j b x * (C.u i j a x)⁻¹)) := by
          rw [hcomm.eq]
    _ = ε.e i j b x * (ε.e i j a x)⁻¹ * (C.u i j b x * (C.u i j a x)⁻¹) := by group

/-- **NEWLY DEFINED (item 84), principal.**  There is an admissible kernel adjustment after
which all same-pair discrepancies vanish, i.e. after which the representatives of one fixed
ordinary transition agree on all intersections of their refinement patches. -/
def CanDescendPairwise (C : InternalTransitionCandidate P S) : Prop :=
  ∃ ε : Adj C, PairwiseRefinementCoherent (adjust C ε)

/-- **PACKAGE M (item 85), principal endpoint.**  `CanDescendPairwise` holds **iff** there is
an admissible kernel adjustment whose adjusted representatives glue to one continuous
internal map on each *original* pair overlap, projecting onto the ordinary transition. -/
theorem canDescendPairwise_iff_glue (C : InternalTransitionCandidate P S) :
    CanDescendPairwise C ↔
      ∃ ε : Adj C, ∀ i j : ι, ∃ v : ↥(S.U i ∩ S.U j) → L,
        Continuous v ∧
        (∀ (a : C.Idx i j) (x : ↥(S.U i ∩ S.U j)), x ∈ C.V i j a →
          v x = (adjust C ε).u i j a x) ∧
        (∀ x, P.proj (v x) = S.g i j x) := by
  constructor
  · rintro ⟨ε, hco⟩
    refine ⟨ε, fun i j => ⟨gluedRep (adjust C ε) i j, ?_, ?_, ?_⟩⟩
    · exact continuous_gluedRep (adjust C ε) hco i j
    · exact fun a x hx => gluedRep_eq (adjust C ε) hco i j a hx
    · exact proj_gluedRep (adjust C ε) hco i j
  · rintro ⟨ε, hv⟩
    refine ⟨ε, fun i j a b x hx => ?_⟩
    obtain ⟨v, -, hres, -⟩ := hv i j
    rw [← hres a x hx.1, hres b x hx.2]

/-- **PACKAGE M (item 86), principal.**  Because triple-defect freeness already forces
same-pair agreement (Package D), the *same* adjustment that trivializes all triple defects
also trivializes all same-pair discrepancies.  Pairwise descent is therefore not an
independent datum here, and no second adjustment is introduced (item 87). -/
theorem canTrivialise_imp_canDescendPairwise {C : InternalTransitionCandidate P S}
    (h : CanTrivialise C) : CanDescendPairwise C := by
  obtain ⟨ε, hε⟩ := h
  exact ⟨ε, tripleDefectFree_imp_pairwiseRefinementCoherent hε⟩

/-! ## Package N — the combined compatibility criterion -/

/-- **NEWLY DEFINED (item 88), principal.**  The strongest justified readiness predicate.
Since pairwise descent is automatic for a defect-free system (Package D), readiness is
exactly simultaneous trivializability; the equivalence with the *combined* one-adjustment
condition is the theorem below, not the definition. -/
def CompatibilityReady (C : InternalTransitionCandidate P S) : Prop :=
  CanTrivialise C

/-- **PACKAGE N (item 92), principal endpoint —
`compatibility_ready_iff_single_adjustment_solves_all_required_kernel_equations`.**
Compatibility readiness holds **iff** there exists a *single* admissible kernel adjustment
which at once

* trivializes every triple defect, and
* trivializes every same-pair refinement discrepancy.

The forward direction is the non-trivial one: it uses Package D to show that the adjustment
solving the triple equations automatically solves the pairwise equations as well.  Separate
adjustments for the two conditions are never combined (item 89, negative control 112). -/
theorem compatibility_ready_iff_single_adjustment_solves_all_required_kernel_equations
    (C : InternalTransitionCandidate P S) :
    CompatibilityReady C ↔
      ∃ ε : Adj C, TripleDefectFree (adjust C ε) ∧ PairwiseRefinementCoherent (adjust C ε) := by
  constructor
  · rintro ⟨ε, hε⟩
    exact ⟨ε, hε, tripleDefectFree_imp_pairwiseRefinementCoherent hε⟩
  · rintro ⟨ε, hε, -⟩
    exact ⟨ε, hε⟩

/-- **PACKAGE N (item 93), principal.**  The combined condition is **not** strictly stronger
than simultaneous trivializability: the two are equivalent, and this is proved. -/
theorem compatibilityReady_iff_canTrivialise (C : InternalTransitionCandidate P S) :
    CompatibilityReady C ↔ CanTrivialise C := Iff.rfl

/-- **PACKAGE N.**  Readiness is also invariant under the initial choice of local internal
representatives. -/
theorem compatibilityReady_rep_choice_invariant (C : InternalTransitionCandidate P S)
    (u' : ∀ i j, C.Idx i j → (↥(S.U i ∩ S.U j) → L))
    (hu' : ∀ i j a, P.IsInternalRepOn (S.g i j) (C.V i j a) (u' i j a)) :
    CompatibilityReady (withReps C u' hu') ↔ CompatibilityReady C :=
  simultaneous_trivialisability_rep_choice_invariant C u' hu'

end Combined

end NullSectorTask29
