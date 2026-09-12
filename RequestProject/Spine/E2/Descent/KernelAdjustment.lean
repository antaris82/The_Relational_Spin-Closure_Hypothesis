import RequestProject.Spine.E2.Descent.PairwiseDescent

/-!
# Task 29, Package F: kernel adjustments of refined representatives

**HARD TARGET B, first half (items 47–50).**

An *admissible kernel adjustment* of a refined internal candidate assigns to every stored
representative a continuous kernel-valued function on the *same* refined domain.  Adjusting
the representatives,

`u^ε_ij = ε_ij * u_ij`   (the inherited left convention),

produces a new candidate on exactly the same refined domains.  Proved here:

* the adjusted maps are again continuous internal representatives, so the adjusted candidate
  exists and has the *same* ordinary projection data (item 49);
* the identity, composition and inverse adjustments exist, and the corresponding candidates
  are related by the expected equations (items 49, 50);
* the elementary `withReps` bookkeeping used throughout Task XXIX: two candidates on the same
  refined domains differ only in their stored representatives, and two such candidates are
  equal as soon as their stored representatives are equal.

This is a lightweight package of elementary operations; no general gauge-theory API is
imported (item 50).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask29

universe u v w t

open NullSectorTask28
open NullSectorTask28.InternalProjection

section Helpers

variable {L : Type w} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] (P : InternalProjection L G) {X : Type u}
  [TopologicalSpace X]

/-! ## Elementary kernel-function algebra (Task-XXIX local helpers) -/

theorem kerFun_one (V : Set X) : P.IsKerFunOn V (fun _ => 1) :=
  ⟨continuousOn_const, fun _ _ => Subgroup.one_mem _⟩

theorem kerFun_mul {V : Set X} {e f : X → L} (he : P.IsKerFunOn V e)
    (hf : P.IsKerFunOn V f) : P.IsKerFunOn V (fun x => e x * f x) :=
  ⟨he.1.mul hf.1, fun x hx => Subgroup.mul_mem _ (he.2 x hx) (hf.2 x hx)⟩

theorem kerFun_inv {V : Set X} {e : X → L} (he : P.IsKerFunOn V e) :
    P.IsKerFunOn V (fun x => (e x)⁻¹) :=
  ⟨he.1.inv, fun x hx => Subgroup.inv_mem _ (he.2 x hx)⟩

theorem kerFun_mono {V V' : Set X} {e : X → L} (he : P.IsKerFunOn V e) (h : V' ⊆ V) :
    P.IsKerFunOn V' e :=
  ⟨he.1.mono h, fun x hx => he.2 x (h hx)⟩

theorem kerFun_comp {Y : Type u} [TopologicalSpace Y] {V : Set X} {e : X → L}
    (he : P.IsKerFunOn V e) {f : Y → X} (hf : Continuous f) :
    P.IsKerFunOn (f ⁻¹' V) (fun y => e (f y)) :=
  ⟨he.1.comp hf.continuousOn fun _ hy => hy, fun y hy => he.2 (f y) hy⟩

end Helpers

section Adjustment

variable {L : Type w} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {P : InternalProjection L G} {B : Type u}
  [TopologicalSpace B] {ι : Type t} {S : TransitionSystem B ι G}

/-! ## Candidates on fixed refined domains -/

/-- **NEWLY DEFINED, bookkeeping.**  The candidate obtained from `C` by keeping the refined
domains and replacing the stored representatives.  Every Task-XXIX comparison of two
candidate systems "on the same domains" is phrased through this constructor. -/
def withReps (C : InternalTransitionCandidate P S)
    (u' : ∀ i j, C.Idx i j → (↥(S.U i ∩ S.U j) → L))
    (hu' : ∀ i j a, P.IsInternalRepOn (S.g i j) (C.V i j a) (u' i j a)) :
    InternalTransitionCandidate P S where
  Idx := C.Idx
  V := C.V
  isOpen_V := C.isOpen_V
  covers := C.covers
  u := u'
  u_isRep := hu'

@[simp] theorem withReps_Idx (C : InternalTransitionCandidate P S) (u') (hu') :
    (withReps C u' hu').Idx = C.Idx := rfl

@[simp] theorem withReps_V (C : InternalTransitionCandidate P S) (u') (hu') :
    (withReps C u' hu').V = C.V := rfl

@[simp] theorem withReps_u (C : InternalTransitionCandidate P S) (u') (hu') :
    (withReps C u' hu').u = u' := rfl

/-- The trivial instance: replacing the representatives by themselves changes nothing. -/
theorem withReps_self (C : InternalTransitionCandidate P S) :
    withReps C C.u C.u_isRep = C := rfl

/-- **Bookkeeping.**  Two candidates on the same refined domains are equal as soon as their
stored representatives are equal. -/
theorem withReps_ext (C : InternalTransitionCandidate P S) {u₁ u₂}
    (h₁ : ∀ i j a, P.IsInternalRepOn (S.g i j) (C.V i j a) (u₁ i j a))
    (h₂ : ∀ i j a, P.IsInternalRepOn (S.g i j) (C.V i j a) (u₂ i j a)) (h : u₁ = u₂) :
    withReps C u₁ h₁ = withReps C u₂ h₂ := by
  subst h; rfl

/-! ## Package F — admissible kernel adjustments -/

/-- **NEWLY DEFINED (item 47), principal.**  An admissible kernel adjustment for the refined
domains `V`: a continuous kernel-valued function on each refined domain. -/
structure KernelAdjustment (P : InternalProjection L G) (S : TransitionSystem B ι G)
    (Idx : ι → ι → Type u) (V : ∀ i j, Idx i j → Set ↥(S.U i ∩ S.U j)) where
  /-- The kernel-valued function stored on each refined domain. -/
  e : ∀ i j, Idx i j → (↥(S.U i ∩ S.U j) → L)
  /-- Each stored function is continuous and kernel-valued there. -/
  e_isKer : ∀ i j a, P.IsKerFunOn (V i j a) (e i j a)

/-- An admissible kernel adjustment of the refined domains of the candidate `C`. -/
abbrev Adj (C : InternalTransitionCandidate P S) :=
  KernelAdjustment P S C.Idx C.V

namespace KernelAdjustment

variable {Idx : ι → ι → Type u} {V : ∀ i j, Idx i j → Set ↥(S.U i ∩ S.U j)}

/-- **PACKAGE F (item 49).**  The identity adjustment. -/
def one (P : InternalProjection L G) (S : TransitionSystem B ι G) (Idx) (V) :
    KernelAdjustment P S Idx V where
  e := fun _ _ _ _ => 1
  e_isKer := fun i j a => kerFun_one P (V i j a)

/-- **PACKAGE F (item 49).**  Composition of adjustments. -/
def comp (η ε : KernelAdjustment P S Idx V) : KernelAdjustment P S Idx V where
  e := fun i j a x => η.e i j a x * ε.e i j a x
  e_isKer := fun i j a => kerFun_mul P (η.e_isKer i j a) (ε.e_isKer i j a)

/-- **PACKAGE F (item 49).**  The inverse adjustment. -/
def inv (ε : KernelAdjustment P S Idx V) : KernelAdjustment P S Idx V where
  e := fun i j a x => (ε.e i j a x)⁻¹
  e_isKer := fun i j a => kerFun_inv P (ε.e_isKer i j a)

@[simp] theorem one_e (P : InternalProjection L G) (S : TransitionSystem B ι G) (Idx) (V)
    (i j) (a : Idx i j) (x) : (one P S Idx V).e i j a x = 1 := rfl

@[simp] theorem comp_e (η ε : KernelAdjustment P S Idx V) (i j) (a : Idx i j) (x) :
    (comp η ε).e i j a x = η.e i j a x * ε.e i j a x := rfl

@[simp] theorem inv_e (ε : KernelAdjustment P S Idx V) (i j) (a : Idx i j) (x) :
    (inv ε).e i j a x = (ε.e i j a x)⁻¹ := rfl

end KernelAdjustment

/-! ## The adjusted candidate -/

/-- **PACKAGE F (item 48), principal.**  The candidate obtained by adjusting every stored
representative: `u^ε_ij = ε_ij * u_ij`, on the same refined domains. -/
def adjust (C : InternalTransitionCandidate P S) (ε : Adj C) :
    InternalTransitionCandidate P S :=
  withReps C (fun i j a x => ε.e i j a x * C.u i j a x)
    (fun i j a => P.isInternalRepOn_kerFun_mul (C.u_isRep i j a) (ε.e_isKer i j a))

@[simp] theorem adjust_Idx (C : InternalTransitionCandidate P S) (ε : Adj C) :
    (adjust C ε).Idx = C.Idx := rfl

@[simp] theorem adjust_V (C : InternalTransitionCandidate P S) (ε : Adj C) :
    (adjust C ε).V = C.V := rfl

@[simp] theorem adjust_u (C : InternalTransitionCandidate P S) (ε : Adj C) (i j)
    (a : C.Idx i j) (x : ↥(S.U i ∩ S.U j)) :
    (adjust C ε).u i j a x = ε.e i j a x * C.u i j a x := rfl

/-- **PACKAGE F (item 49), principal.**  The adjusted representatives are continuous and have
*unchanged* ordinary projection: they represent exactly the same ordinary transitions. -/
theorem adjust_isRep (C : InternalTransitionCandidate P S) (ε : Adj C) (i j : ι)
    (a : C.Idx i j) : P.IsInternalRepOn (S.g i j) (C.V i j a) ((adjust C ε).u i j a) :=
  (adjust C ε).u_isRep i j a

/-- **PACKAGE F (item 49).**  Explicitly: adjusting does not change the ordinary transition
data. -/
theorem proj_adjust (C : InternalTransitionCandidate P S) (ε : Adj C) (i j : ι)
    (a : C.Idx i j) {x : ↥(S.U i ∩ S.U j)} (hx : x ∈ C.V i j a) :
    P.proj ((adjust C ε).u i j a x) = S.g i j x :=
  ((adjust C ε).u_isRep i j a).2 x hx

/-- **PACKAGE F (item 49).**  The identity adjustment does nothing. -/
theorem adjust_one (C : InternalTransitionCandidate P S) :
    adjust C (KernelAdjustment.one P S C.Idx C.V) = C := by
  refine Eq.trans (withReps_ext C _ C.u_isRep ?_) (withReps_self C)
  funext i j a x
  simp

/-- **PACKAGE F (item 49), principal.**  Adjustments compose: adjusting twice is adjusting by
the composite. -/
theorem adjust_adjust (C : InternalTransitionCandidate P S) (ε η : Adj C) :
    adjust (adjust C ε) η = adjust C (KernelAdjustment.comp η ε) := by
  refine withReps_ext C _ _ ?_
  funext i j a x
  simp [mul_assoc]

/-- **PACKAGE F (item 49), principal.**  The inverse adjustment undoes the adjustment. -/
theorem adjust_inv_adjust (C : InternalTransitionCandidate P S) (ε : Adj C) :
    adjust (adjust C ε) (KernelAdjustment.inv ε) = C := by
  refine Eq.trans (withReps_ext C _ C.u_isRep ?_) (withReps_self C)
  funext i j a x
  simp

/-- **PACKAGE F.**  Adjusted candidates have literally the same defect domains as the
original: only the stored representatives change. -/
theorem adjust_defectDom (C : InternalTransitionCandidate P S) (ε : Adj C) (i j k : ι)
    (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k) :
    (adjust C ε).defectDom i j k a b c = C.defectDom i j k a b c := rfl

end Adjustment

end NullSectorTask29
