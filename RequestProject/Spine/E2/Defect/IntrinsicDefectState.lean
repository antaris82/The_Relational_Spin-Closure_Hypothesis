import RequestProject.Spine.E2.Defect.UniversalExistenceAudit

/-!
# Task 31, Packages G and H: defect systems, the admissible change relation and the
intrinsic defect state of a candidate

**HARD TARGET C (items 57–71).**

Task XXIX already provides the ingredients (items 58–60): the kernel-valued triple defect
`δ_ijk` of a refined candidate, its continuity, the admissible continuous kernel adjustments
`ε_ij`, and the inherited change-of-representative law

```
δ'_ijk = (ε_jk · ε_ij · ε_ik⁻¹) · δ_ijk .
```

This module *reuses* that law; nothing of it is redefined (firewall items 5–7).  What is new
here is the intrinsic packaging:

* `adjShift` — the admissible change factor `ε_jk · ε_ij · ε_ik⁻¹`, with its three structural
  laws (`adjShift_one`, `adjShift_comp`, `adjShift_inv_mul`), all *derived* from centrality of
  the kernel;
* `DefectSystem` — a continuous kernel-valued triple-overlap family on the refined domains of
  a candidate (item 59), with the two distinguished members: the actual defect
  `DefectSystem.ofCandidate` and the neutral one `DefectSystem.neutral` (item 61);
* `DefectEquivalent` — the exact admissible-change relation (item 62), proved reflexive,
  symmetric and transitive (item 63), hence a `Setoid`;
* `DefectClass` — the **actual quotient** (item 70, preferred form), with `defectState C` the
  class of the candidate's own defect and `neutralDefectState C` the class of the neutral
  system;
* `isNeutralDefectState_iff_canTrivialise` — the class of the defect is the neutral class
  exactly when the internally derived kernel equations are solvable.

No conventional name is attached to any of these objects (items 10–15, 71, 121).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask31

open NullSectorTask28 NullSectorTask29 NullSectorTask30

universe u v w t

/-! ## Central kernel algebra -/

section CentralAlgebra

variable {L : Type w} [Group L]

/-- **DERIVED, elementary.**  For central `A`, `B`, `C` the two change factors of an
adjustment and of its inverse cancel. -/
theorem central_shift_inv_mul {A B C : L} (hB : ∀ l : L, Commute B l)
    (hC : ∀ l : L, Commute C l) : (A⁻¹ * B⁻¹ * C) * (A * B * C⁻¹) = 1 := by
  have cB' : ∀ l : L, B⁻¹ * l = l * B⁻¹ := fun l => ((hB l).inv_left).eq
  have cC : ∀ l : L, C * l = l * C := fun l => (hC l).eq
  calc (A⁻¹ * B⁻¹ * C) * (A * B * C⁻¹)
      = A⁻¹ * (B⁻¹ * (C * (A * (B * C⁻¹)))) := by simp [mul_assoc]
    _ = A⁻¹ * (B⁻¹ * (A * (C * (B * C⁻¹)))) := by rw [← mul_assoc C A, cC A, mul_assoc]
    _ = A⁻¹ * (A * (B⁻¹ * (C * (B * C⁻¹)))) := by rw [← mul_assoc B⁻¹ A, cB' A, mul_assoc]
    _ = B⁻¹ * (C * (B * C⁻¹)) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    _ = B⁻¹ * (B * (C * C⁻¹)) := by rw [← mul_assoc C B, cC B, mul_assoc]
    _ = 1 := by simp

/-- **DERIVED, elementary.**  For central `A`, `B`, `C` the change factor of a composite
adjustment is the product of the two change factors. -/
theorem central_shift_mul {A B C A' B' C' : L} (hB : ∀ l : L, Commute B l)
    (hC : ∀ l : L, Commute C l) :
    (A * A') * (B * B') * (C * C')⁻¹ = (A * B * C⁻¹) * (A' * B' * C'⁻¹) := by
  have cB : ∀ l : L, B * l = l * B := fun l => (hB l).eq
  have cC' : ∀ l : L, C⁻¹ * l = l * C⁻¹ := fun l => ((hC l).inv_left).eq
  calc (A * A') * (B * B') * (C * C')⁻¹
      = A * (A' * (B * (B' * (C'⁻¹ * C⁻¹)))) := by simp [mul_assoc, mul_inv_rev]
    _ = A * (B * (A' * (B' * (C'⁻¹ * C⁻¹)))) := by rw [← mul_assoc A', ← cB A', mul_assoc]
    _ = A * (B * (C⁻¹ * (A' * (B' * C'⁻¹)))) := by
          rw [cC' (A' * (B' * C'⁻¹))]
          simp [mul_assoc]
    _ = (A * B * C⁻¹) * (A' * B' * C'⁻¹) := by simp [mul_assoc]

end CentralAlgebra

section DefectStates

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {P : InternalProjection L G} {S : TransitionSystem B ι G}

/-! ## The admissible change factor -/

/-- **PACKAGE G (item 60).**  The admissible change factor `ε_jk · ε_ij · ε_ik⁻¹` of the
inherited Task-XXIX representative-change law, read on a triple overlap. -/
def adjShift (C : InternalTransitionCandidate P S) (ε : Adj C) (i j k : ι) (a : C.Idx i j)
    (b : C.Idx j k) (c : C.Idx i k) (x : ↥(S.tripleDom i j k)) : L :=
  ε.e j k b (S.incJK i j k x) * ε.e i j a (S.incIJ i j k x) *
    (ε.e i k c (S.incIK i j k x))⁻¹

/-- **PACKAGE G.**  The change factor of the identity adjustment is trivial. -/
theorem adjShift_one (C : InternalTransitionCandidate P S) (i j k : ι) (a : C.Idx i j)
    (b : C.Idx j k) (c : C.Idx i k) (x : ↥(S.tripleDom i j k)) :
    adjShift C (KernelAdjustment.one P S C.Idx C.V) i j k a b c x = 1 := by
  simp [adjShift]

/-- **PACKAGE G.**  The change factor of a composite adjustment is the product of the two
change factors.  Derived from centrality of the kernel. -/
theorem adjShift_comp (C : InternalTransitionCandidate P S) (η ε : Adj C) (i j k : ι)
    (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k) {x : ↥(S.tripleDom i j k)}
    (hx : x ∈ C.defectDom i j k a b c) :
    adjShift C (KernelAdjustment.comp η ε) i j k a b c x
      = adjShift C η i j k a b c x * adjShift C ε i j k a b c x := by
  have hB : ∀ l : L, Commute (η.e i j a (S.incIJ i j k x)) l :=
    fun l => P.ker_commute ((adj_kerFun_IJ C η i j k a b c).2 x hx) l
  have hC : ∀ l : L, Commute (η.e i k c (S.incIK i j k x)) l :=
    fun l => P.ker_commute ((adj_kerFun_IK C η i j k a b c).2 x hx) l
  exact central_shift_mul hB hC

/-- **PACKAGE G.**  The change factors of an adjustment and of its inverse cancel.  Derived
from centrality of the kernel. -/
theorem adjShift_inv_mul (C : InternalTransitionCandidate P S) (ε : Adj C) (i j k : ι)
    (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k) {x : ↥(S.tripleDom i j k)}
    (hx : x ∈ C.defectDom i j k a b c) :
    adjShift C (KernelAdjustment.inv ε) i j k a b c x * adjShift C ε i j k a b c x = 1 := by
  have hB : ∀ l : L, Commute (ε.e i j a (S.incIJ i j k x)) l :=
    fun l => P.ker_commute ((adj_kerFun_IJ C ε i j k a b c).2 x hx) l
  have hC : ∀ l : L, Commute (ε.e i k c (S.incIK i j k x)) l :=
    fun l => P.ker_commute ((adj_kerFun_IK C ε i j k a b c).2 x hx) l
  simp only [adjShift, KernelAdjustment.inv_e, inv_inv]
  exact central_shift_inv_mul hB hC

/-! ## Defect systems -/

/-- **PACKAGE G (item 59), principal definition.**  A *defect system* on the refined domains
of a candidate: a continuous kernel-valued function on every triple-overlap defect domain.
The actual triple defect of the candidate is one of these; so is the everywhere-neutral
system. -/
structure DefectSystem (C : InternalTransitionCandidate P S) where
  /-- The stored triple-overlap functions. -/
  d : ∀ i j k : ι, C.Idx i j → C.Idx j k → C.Idx i k → (↥(S.tripleDom i j k) → L)
  /-- Each of them is continuous and kernel-valued on its defect domain. -/
  d_isKer : ∀ i j k a b c, P.IsKerFunOn (C.defectDom i j k a b c) (d i j k a b c)

namespace DefectSystem

/-- **PACKAGE H (item 64).**  The defect system *of* a candidate: its inherited Task-XXVIII
triple defect. -/
def ofCandidate (C : InternalTransitionCandidate P S) : DefectSystem C where
  d := C.defect
  d_isKer := C.defect_isKerFunOn

/-- **PACKAGE G (item 61).**  The neutral defect system: identity everywhere. -/
def neutral (C : InternalTransitionCandidate P S) : DefectSystem C where
  d := fun _ _ _ _ _ _ _ => 1
  d_isKer := fun i j k a b c => kerFun_one P (C.defectDom i j k a b c)

@[simp] theorem ofCandidate_d (C : InternalTransitionCandidate P S) (i j k : ι)
    (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k) (x : ↥(S.tripleDom i j k)) :
    (ofCandidate C).d i j k a b c x = C.defect i j k a b c x := rfl

@[simp] theorem neutral_d (C : InternalTransitionCandidate P S) (i j k : ι) (a : C.Idx i j)
    (b : C.Idx j k) (c : C.Idx i k) (x : ↥(S.tripleDom i j k)) :
    (neutral C).d i j k a b c x = 1 := rfl

end DefectSystem

/-! ## The admissible-change relation -/

/-- **PACKAGE G (item 62), principal definition.**  Two defect systems on the same refined
domains are *equivalent* when an admissible continuous kernel adjustment carries one to the
other by the inherited Task-XXIX representative-change law.  No conventional name is
attached. -/
def DefectEquivalent {C : InternalTransitionCandidate P S} (d d' : DefectSystem C) : Prop :=
  ∃ ε : Adj C, ∀ (i j k : ι) (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k),
    ∀ x ∈ C.defectDom i j k a b c,
      d'.d i j k a b c x = adjShift C ε i j k a b c x * d.d i j k a b c x

/-- **PACKAGE G (item 63).**  Reflexivity. -/
theorem defectEquivalent_refl {C : InternalTransitionCandidate P S} (d : DefectSystem C) :
    DefectEquivalent d d :=
  ⟨KernelAdjustment.one P S C.Idx C.V, fun i j k a b c x _ => by
    rw [adjShift_one, one_mul]⟩

/-- **PACKAGE G (item 63).**  Symmetry. -/
theorem defectEquivalent_symm {C : InternalTransitionCandidate P S} {d d' : DefectSystem C}
    (h : DefectEquivalent d d') : DefectEquivalent d' d := by
  obtain ⟨ε, hε⟩ := h
  refine ⟨KernelAdjustment.inv ε, fun i j k a b c x hx => ?_⟩
  rw [hε i j k a b c x hx, ← mul_assoc, adjShift_inv_mul C ε i j k a b c hx, one_mul]

/-- **PACKAGE G (item 63).**  Transitivity. -/
theorem defectEquivalent_trans {C : InternalTransitionCandidate P S}
    {d d' d'' : DefectSystem C} (h : DefectEquivalent d d') (h' : DefectEquivalent d' d'') :
    DefectEquivalent d d'' := by
  obtain ⟨ε, hε⟩ := h
  obtain ⟨η, hη⟩ := h'
  refine ⟨KernelAdjustment.comp η ε, fun i j k a b c x hx => ?_⟩
  rw [hη i j k a b c x hx, hε i j k a b c x hx, ← mul_assoc,
    ← adjShift_comp C η ε i j k a b c hx]

/-- **PACKAGE G (item 63).**  The admissible-change relation is an equivalence relation. -/
def defectSetoid (C : InternalTransitionCandidate P S) : Setoid (DefectSystem C) where
  r := DefectEquivalent
  iseqv := ⟨defectEquivalent_refl, defectEquivalent_symm, defectEquivalent_trans⟩

/-! ## The intrinsic defect state of a candidate (item 70, preferred quotient form) -/

/-- **PACKAGE H (item 70), preferred form.**  The quotient of defect systems by the
admissible-change relation. -/
def DefectClass (C : InternalTransitionCandidate P S) : Type _ :=
  Quotient (defectSetoid C)

/-- **PACKAGE H (item 70).**  The defect state of a candidate: the class of its own triple
defect. -/
def defectState (C : InternalTransitionCandidate P S) : DefectClass C :=
  Quotient.mk (defectSetoid C) (DefectSystem.ofCandidate C)

/-- **PACKAGE I (item 72).**  The neutral class. -/
def neutralDefectState (C : InternalTransitionCandidate P S) : DefectClass C :=
  Quotient.mk (defectSetoid C) (DefectSystem.neutral C)

/-- **PACKAGE I (item 72).**  A candidate has *neutral* defect state when the class of its
triple defect is the neutral class. -/
def IsNeutralDefectState (C : InternalTransitionCandidate P S) : Prop :=
  defectState C = neutralDefectState C

/-- **PACKAGE I.**  Neutrality of the state unfolds to the admissible-change relation between
the candidate's defect and the everywhere-identity defect system. -/
theorem isNeutralDefectState_iff_equivalent (C : InternalTransitionCandidate P S) :
    IsNeutralDefectState C ↔
      DefectEquivalent (DefectSystem.ofCandidate C) (DefectSystem.neutral C) :=
  Quotient.eq_iff_equiv

/-- **PACKAGE J, the local half (item 75).**  The defect state of a candidate is the neutral
class **iff** the internally derived kernel equations of that candidate are solvable.  Both
directions are the inherited Task-XXIX equation, read through the quotient. -/
theorem isNeutralDefectState_iff_canTrivialise (C : InternalTransitionCandidate P S) :
    IsNeutralDefectState C ↔ CanTrivialise C := by
  rw [isNeutralDefectState_iff_equivalent]
  constructor
  · rintro ⟨ε, hε⟩
    refine (canTrivialise_iff_kernel_equations_solvable C).2 ⟨ε, fun i j k a b c x hx => ?_⟩
    exact (hε i j k a b c x hx).symm
  · intro h
    obtain ⟨ε, hε⟩ := (canTrivialise_iff_kernel_equations_solvable C).1 h
    exact ⟨ε, fun i j k a b c x hx => (hε i j k a b c x hx).symm⟩

end DefectStates

end NullSectorTask31
