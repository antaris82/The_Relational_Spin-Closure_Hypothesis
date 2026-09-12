import RequestProject.Spine.E2.Descent.KernelAdjustment

/-!
# Task 29, Packages G and H: the exact simultaneous-trivialization equation

**HARD TARGET B (items 51–60).**

The inherited change-of-representative law

`δ'_ijk = (ε_jk * ε_ij * ε_ik⁻¹) * δ_ijk`

is *reused, not reproved*.  From it we obtain the exact solvability equation: the adjusted
candidate `C^ε` is triple-defect free **iff** for every relevant triple and every point of
the corresponding defect domain

`(ε_jk * ε_ij * ε_ik⁻¹) * δ_ijk = 1`,

equivalently (by centrality of the kernel)

`ε_ik = ε_jk * ε_ij * δ_ijk`.

The Task-XXIX solvability predicate `CanTrivialise` is proved to be exactly the inherited
Task-XXVIII predicate `CanTrivialiseSimultaneously`, and to be exactly the existence of a
defect-free adjusted candidate (items 54–56).

Package H (items 57–60) packages a solution: the adjusted candidate together with its
proof of defect-freeness is a `DefectFreeRefinedInternalSystem`, with the *same* ordinary
transitions and projection data, all triple defects trivial, the exact triple multiplication
law, and the identity/inverse normalizations of Package B.  It is **not** called a globally
glued transition system (item 59); whole-overlap gluing is treated separately.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask29

universe u v w t

open NullSectorTask28
open NullSectorTask28.InternalProjection

section Trivialisation

variable {L : Type w} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {P : InternalProjection L G} {B : Type u}
  [TopologicalSpace B] {ι : Type t} {S : TransitionSystem B ι G}

/-! ## The adjustment factors read on a triple overlap -/

theorem adj_kerFun_IJ (C : InternalTransitionCandidate P S) (ε : Adj C) (i j k : ι)
    (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k) :
    P.IsKerFunOn (C.defectDom i j k a b c) (fun y => ε.e i j a (S.incIJ i j k y)) :=
  kerFun_mono P (kerFun_comp P (ε.e_isKer i j a) (S.continuous_incIJ i j k))
    (fun _ hx => hx.1.1)

theorem adj_kerFun_JK (C : InternalTransitionCandidate P S) (ε : Adj C) (i j k : ι)
    (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k) :
    P.IsKerFunOn (C.defectDom i j k a b c) (fun y => ε.e j k b (S.incJK i j k y)) :=
  kerFun_mono P (kerFun_comp P (ε.e_isKer j k b) (S.continuous_incJK i j k))
    (fun _ hx => hx.1.2)

theorem adj_kerFun_IK (C : InternalTransitionCandidate P S) (ε : Adj C) (i j k : ι)
    (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k) :
    P.IsKerFunOn (C.defectDom i j k a b c) (fun y => ε.e i k c (S.incIK i j k y)) :=
  kerFun_mono P (kerFun_comp P (ε.e_isKer i k c) (S.continuous_incIK i j k))
    (fun _ hx => hx.2)

/-! ## Package G — the exact equation -/

/-- **PACKAGE G (items 51, 52), principal.**  The inherited defect-change law, read on the
candidate interface: the defect of the adjusted candidate is the defect of the original one,
multiplied on the left by `ε_jk * ε_ij * ε_ik⁻¹`. -/
theorem adjust_defect (C : InternalTransitionCandidate P S) (ε : Adj C) (i j k : ι)
    (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k) {x : ↥(S.tripleDom i j k)}
    (hx : x ∈ C.defectDom i j k a b c) :
    (adjust C ε).defect i j k a b c x
      = (ε.e j k b (S.incJK i j k x) * ε.e i j a (S.incIJ i j k x) *
          (ε.e i k c (S.incIK i j k x))⁻¹) * C.defect i j k a b c x :=
  P.triple_defect_change_of_rep (adj_kerFun_IJ C ε i j k a b c)
    (adj_kerFun_IK C ε i j k a b c) hx

/-- **PACKAGE G (item 53).**  The rearranged form of the same equation, derived from
centrality of the kernel: the equation says exactly that the `ik` adjustment is determined by
the other two and the defect. -/
theorem adjust_defect_eq_one_iff (C : InternalTransitionCandidate P S) (ε : Adj C)
    (i j k : ι) (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k) {x : ↥(S.tripleDom i j k)}
    (hx : x ∈ C.defectDom i j k a b c) :
    (ε.e j k b (S.incJK i j k x) * ε.e i j a (S.incIJ i j k x) *
        (ε.e i k c (S.incIK i j k x))⁻¹) * C.defect i j k a b c x = 1
      ↔ ε.e i k c (S.incIK i j k x)
          = ε.e j k b (S.incJK i j k x) * ε.e i j a (S.incIJ i j k x) *
            C.defect i j k a b c x := by
  have hker : ε.e i k c (S.incIK i j k x) ∈ P.Ker :=
    (adj_kerFun_IK C ε i j k a b c).2 x hx
  have hcomm : Commute (ε.e i k c (S.incIK i j k x))⁻¹ (C.defect i j k a b c x) :=
    (P.ker_commute hker (C.defect i j k a b c x)).inv_left
  set A := ε.e j k b (S.incJK i j k x)
  set E := ε.e i j a (S.incIJ i j k x)
  set F := ε.e i k c (S.incIK i j k x)
  set D := C.defect i j k a b c x
  constructor
  · intro h
    have h' : (A * E) * (F⁻¹ * D) = 1 := by rw [← h]; group
    rw [hcomm.eq] at h'
    have h'' : (A * E * D) * F⁻¹ = 1 := by rw [← h']; group
    exact (mul_inv_eq_one.1 h'').symm
  · intro h
    have h' : (A * E) * (F⁻¹ * D) = 1 := by
      rw [hcomm.eq, h]; group
    rw [← h']; group

/-- **PACKAGE G (item 54), principal endpoint —
`simultaneous_trivialisation_iff_kernel_equations`.**  The adjusted candidate is
triple-defect free **iff** the admissible kernel adjustment solves, at every point of every
defect domain, the exact kernel equation `ε_jk * ε_ij * ε_ik⁻¹ * δ_ijk = 1`. -/
theorem simultaneous_trivialisation_iff_kernel_equations
    (C : InternalTransitionCandidate P S) (ε : Adj C) :
    TripleDefectFree (adjust C ε) ↔
      ∀ (i j k : ι) (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k),
        ∀ x ∈ C.defectDom i j k a b c,
          (ε.e j k b (S.incJK i j k x) * ε.e i j a (S.incIJ i j k x) *
              (ε.e i k c (S.incIK i j k x))⁻¹) * C.defect i j k a b c x = 1 := by
  constructor
  · intro h i j k a b c x hx
    rw [← adjust_defect C ε i j k a b c hx]
    exact h i j k a b c x hx
  · intro h i j k a b c x hx
    rw [adjust_defect C ε i j k a b c hx]
    exact h i j k a b c x hx

/-- **PACKAGE G (item 53), the rearranged system.** -/
theorem simultaneous_trivialisation_iff_kernel_equations_rearranged
    (C : InternalTransitionCandidate P S) (ε : Adj C) :
    TripleDefectFree (adjust C ε) ↔
      ∀ (i j k : ι) (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k),
        ∀ x ∈ C.defectDom i j k a b c,
          ε.e i k c (S.incIK i j k x)
            = ε.e j k b (S.incJK i j k x) * ε.e i j a (S.incIJ i j k x) *
              C.defect i j k a b c x := by
  rw [simultaneous_trivialisation_iff_kernel_equations]
  constructor
  · intro h i j k a b c x hx
    exact (adjust_defect_eq_one_iff C ε i j k a b c hx).1 (h i j k a b c x hx)
  · intro h i j k a b c x hx
    exact (adjust_defect_eq_one_iff C ε i j k a b c hx).2 (h i j k a b c x hx)

/-! ## The Task-XXIX solvability predicate -/

/-- **NEWLY DEFINED (item 55), principal.**  All triple defects can be removed
simultaneously: there is one admissible kernel adjustment whose adjusted candidate is
triple-defect free. -/
def CanTrivialise (C : InternalTransitionCandidate P S) : Prop :=
  ∃ ε : Adj C, TripleDefectFree (adjust C ε)

/-- **PACKAGE G (items 55, 56), principal endpoint.**  The Task-XXIX predicate is *exactly*
the inherited Task-XXVIII frontier predicate `CanTrivialiseSimultaneously`.  This is a
theorem, not a definitional restatement: the inherited predicate quantifies over raw families
of kernel-valued functions, the Task-XXIX one over admissible adjustments and the resulting
adjusted candidate. -/
theorem canTrivialise_iff_canTrivialiseSimultaneously (C : InternalTransitionCandidate P S) :
    CanTrivialise C ↔ CanTrivialiseSimultaneously P S C := by
  constructor
  · rintro ⟨ε, h⟩
    exact ⟨ε.e, ε.e_isKer, fun i j k a b c x hx => h i j k a b c x hx⟩
  · rintro ⟨e, hker, h⟩
    exact ⟨⟨e, hker⟩, fun i j k a b c x hx => h i j k a b c x hx⟩

/-- **PACKAGE G, principal.**  Solvability of the internally derived kernel equations is
exactly simultaneous trivializability. -/
theorem canTrivialise_iff_kernel_equations_solvable (C : InternalTransitionCandidate P S) :
    CanTrivialise C ↔
      ∃ ε : Adj C, ∀ (i j k : ι) (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k),
        ∀ x ∈ C.defectDom i j k a b c,
          (ε.e j k b (S.incJK i j k x) * ε.e i j a (S.incIJ i j k x) *
              (ε.e i k c (S.incIK i j k x))⁻¹) * C.defect i j k a b c x = 1 := by
  constructor
  · rintro ⟨ε, h⟩
    exact ⟨ε, (simultaneous_trivialisation_iff_kernel_equations C ε).1 h⟩
  · rintro ⟨ε, h⟩
    exact ⟨ε, (simultaneous_trivialisation_iff_kernel_equations C ε).2 h⟩

/-- **PACKAGE G.**  A candidate which is already defect-free is trivializable (by the
identity adjustment). -/
theorem canTrivialise_of_tripleDefectFree {C : InternalTransitionCandidate P S}
    (h : TripleDefectFree C) : CanTrivialise C :=
  ⟨KernelAdjustment.one P S C.Idx C.V, by rw [adjust_one]; exact h⟩

/-! ## Package H — the defect-free adjusted candidate -/

/-- **NEWLY DEFINED (item 60), principal.**  A refined internal system all of whose triple
defects are trivial.  It is deliberately *not* called a global transition system (item 59):
its representatives still live on refinement patches. -/
structure DefectFreeRefinedInternalSystem (P : InternalProjection L G)
    (S : TransitionSystem B ι G) where
  /-- The underlying refined candidate. -/
  C : InternalTransitionCandidate P S
  /-- All its triple defects are trivial. -/
  defectFree : TripleDefectFree C

namespace DefectFreeRefinedInternalSystem

variable (D : DefectFreeRefinedInternalSystem P S)

/-- **PACKAGE H (item 58).**  The projection data is the inherited ordinary transition
data. -/
theorem proj_u (i j : ι) (a : D.C.Idx i j) {x : ↥(S.U i ∩ S.U j)} (hx : x ∈ D.C.V i j a) :
    P.proj (D.C.u i j a x) = S.g i j x := (D.C.u_isRep i j a).2 x hx

/-- **PACKAGE H (item 58).**  Identity normalization. -/
theorem u_self (i : ι) (a : D.C.Idx i i) {y : ↥(S.U i ∩ S.U i)} (hy : y ∈ D.C.V i i a) :
    D.C.u i i a y = 1 := defectFree_identity_normalisation D.defectFree i a hy

/-- **PACKAGE H (item 58).**  Inverse normalization. -/
theorem u_swap (i j : ι) (a : D.C.Idx i j) (b : D.C.Idx j i) (c : D.C.Idx i i)
    {x : ↥(S.U i ∩ S.U j)} (ha : x ∈ D.C.V i j a) (hb : swapPt S x ∈ D.C.V j i b)
    (hc : diagPt S x ∈ D.C.V i i c) : D.C.u j i b (swapPt S x) = (D.C.u i j a x)⁻¹ :=
  defectFree_inverse_normalisation D.defectFree i j a b c ha hb hc

/-- **PACKAGE H (item 58).**  The exact triple multiplication law. -/
theorem u_trans (i j k : ι) (a : D.C.Idx i j) (b : D.C.Idx j k) (c : D.C.Idx i k)
    {x : ↥(S.tripleDom i j k)} (hx : x ∈ D.C.defectDom i j k a b c) :
    D.C.u j k b (S.incJK i j k x) * D.C.u i j a (S.incIJ i j k x)
      = D.C.u i k c (S.incIK i j k x) :=
  defectFree_exact_triple_law D.defectFree i j k a b c hx

/-- **PACKAGE H / D.**  A defect-free refined system is automatically pairwise coherent. -/
theorem pairwiseCoherent : PairwiseRefinementCoherent D.C :=
  tripleDefectFree_imp_pairwiseRefinementCoherent D.defectFree

end DefectFreeRefinedInternalSystem

/-- **PACKAGE H (item 57), principal endpoint.**  A solution of the simultaneous equations
produces a defect-free refined internal system on the *same* refined domains, with the same
ordinary projection data. -/
noncomputable def defectFreeSystemOfSolution (C : InternalTransitionCandidate P S)
    (ε : Adj C) (h : TripleDefectFree (adjust C ε)) :
    DefectFreeRefinedInternalSystem P S where
  C := adjust C ε
  defectFree := h

/-- **PACKAGE H (item 57), principal endpoint.**  Simultaneous trivializability is exactly
the existence of a defect-free refined internal system obtained from `C` by an admissible
kernel adjustment. -/
theorem canTrivialise_iff_exists_defectFree_adjusted (C : InternalTransitionCandidate P S) :
    CanTrivialise C ↔ ∃ ε : Adj C, TripleDefectFree (adjust C ε) := Iff.rfl

end Trivialisation

end NullSectorTask29
