import RequestProject.Spine.E2.Lift.RepresentativeChange

/-!
# Task 28, Packages N, O and P: transition systems, the local action diagram, the exact
Level A/B/C frontier and the frozen output interface

The abstract packages C–M are applied to a whole *transition system* over a base: an open
cover, continuous transition maps between its members, and the inherited identity, inverse
and triple-overlap laws.  The Task-XXVII endpoint `OrdinaryTransitionSystem` is exactly such
a system, valued in the fixed visible model group (`ofOrdinary` below); nothing of it is
modified.

Contents:

* `TransitionSystem`: the neutral packaging of an ordinary transition system valued in a
  topological group, together with `ofOrdinary`, which exhibits the Task-XXVII output as one
  of them (Package A);
* refinement of every overlap carrying continuous internal representatives (Packages C, D);
* triple overlaps: the inclusions, the inherited law read on the triple overlap, and the
  kernel-valued, continuous, locally constant defect (Package H);
* Package N: every internal representative projects to exactly the ordinary transition, and
  the local action diagram commutes;
* Package O: the exact Level A / Level B / Level C distinction, with `Level C ⇒ all defects
  trivial` and the converse for a *fixed* representative system only;
* Package P: the frozen output interface `InternalTransitionCandidate` — which deliberately
  contains **no** field asserting triviality of the defect — and the special case
  `CompatibleInternalTransitionSystem`, whose existence is *not* claimed.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask28

universe u v w t

/-! ## Transition systems -/

/-- **NEWLY DEFINED (Package A, neutral packaging).**  A continuous transition system over a
topological base, valued in a topological group: exactly the shape of the Task-XXVII
endpoint, with the group left general so that the Task-28 theory can be applied to it
through any frozen internal projection. -/
structure TransitionSystem (B : Type u) [TopologicalSpace B] (ι : Type t) (G : Type v)
    [Group G] [TopologicalSpace G] where
  /-- The chart domains. -/
  U : ι → Set B
  /-- Each chart domain is open. -/
  isOpen_U : ∀ i, IsOpen (U i)
  /-- The chart domains cover the base. -/
  cover : ∀ b : B, ∃ i, b ∈ U i
  /-- The ordinary transition maps. -/
  g : ∀ i j : ι, ↥(U i ∩ U j) → G
  /-- Continuity of the transition maps. -/
  continuous_g : ∀ i j, Continuous (g i j)
  /-- Identity law. -/
  g_self : ∀ (i : ι) (b : ↥(U i ∩ U i)), g i i b = 1
  /-- Inverse law. -/
  g_symm : ∀ (i j : ι) (b : B) (h : b ∈ U i ∩ U j) (h' : b ∈ U j ∩ U i),
    g j i ⟨b, h'⟩ = (g i j ⟨b, h⟩)⁻¹
  /-- Triple-overlap law, in the inherited order. -/
  g_trans : ∀ (i j k : ι) (b : B) (h₁ : b ∈ U i ∩ U k) (h₂ : b ∈ U j ∩ U k)
    (h₃ : b ∈ U i ∩ U j), g i k ⟨b, h₁⟩ = g j k ⟨b, h₂⟩ * g i j ⟨b, h₃⟩

/-- **IMPORTED (Package A, items 22–24).**  The Task-XXVII ordinary transition system is a
transition system in the above sense, valued in the fixed visible model group.  Nothing is
added: every field is the inherited one. -/
def ofOrdinary {B : Type u} [TopologicalSpace B] {ι : Type t}
    (S : OrdinaryTransitionSystem B ι) :
    TransitionSystem B ι (NullSectorTask26.GvisModel) where
  U := S.U
  isOpen_U := S.isOpen_U
  cover := S.cover
  g := S.g
  continuous_g := S.continuous_g
  g_self := S.g_self
  g_symm := S.g_symm
  g_trans := S.g_trans

namespace TransitionSystem

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]

/-! ### Triple overlaps -/

variable (S : TransitionSystem B ι G)

/-- The triple overlap domain. -/
def tripleDom (i j k : ι) : Set B := S.U i ∩ S.U j ∩ S.U k

/-- Inclusion of a triple overlap into the `ij` double overlap. -/
def incIJ (i j k : ι) (x : ↥(S.tripleDom i j k)) : ↥(S.U i ∩ S.U j) :=
  ⟨(x : B), x.2.1.1, x.2.1.2⟩

/-- Inclusion of a triple overlap into the `jk` double overlap. -/
def incJK (i j k : ι) (x : ↥(S.tripleDom i j k)) : ↥(S.U j ∩ S.U k) :=
  ⟨(x : B), x.2.1.2, x.2.2⟩

/-- Inclusion of a triple overlap into the `ik` double overlap. -/
def incIK (i j k : ι) (x : ↥(S.tripleDom i j k)) : ↥(S.U i ∩ S.U k) :=
  ⟨(x : B), x.2.1.1, x.2.2⟩

theorem continuous_incIJ (i j k : ι) : Continuous (S.incIJ i j k) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem continuous_incJK (i j k : ι) : Continuous (S.incJK i j k) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem continuous_incIK (i j k : ι) : Continuous (S.incIK i j k) :=
  Continuous.subtype_mk continuous_subtype_val _

/-- **DERIVED.**  The inherited triple-overlap law, read on the triple overlap domain. -/
theorem g_trans_on (i j k : ι) (x : ↥(S.tripleDom i j k)) :
    S.g i k (S.incIK i j k x) = S.g j k (S.incJK i j k x) * S.g i j (S.incIJ i j k x) :=
  S.g_trans i j k (x : B) _ _ _

end TransitionSystem

namespace InternalProjection

variable {L : Type w} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] (P : InternalProjection L G)
  {B : Type u} [TopologicalSpace B] {ι : Type t}

/-! ## Packages C and D for a whole transition system -/

/-- **PACKAGE C (items 33, 34), principal.**  Every point of every overlap of a transition
system lies in an open subdomain on which the ordinary transition map has a continuous
internal representative. -/
theorem exists_local_rep_of_transitionSystem (S : TransitionSystem B ι G) (i j : ι)
    (x : ↥(S.U i ∩ S.U j)) :
    ∃ V : Set ↥(S.U i ∩ S.U j), IsOpen V ∧ x ∈ V ∧
      P.HasContinuousInternalRep (S.g i j) V :=
  P.exists_local_continuous_internal_rep (S.continuous_g i j) x

/-- **PACKAGE D (items 36, 37), principal.**  Every overlap carries a refinement on whose
members continuous internal representatives are stored. -/
noncomputable def overlapRefinement (S : TransitionSystem B ι G) (i j : ι) :
    P.OverlapRefinement (S.g i j) :=
  P.refinementOfContinuous (S.continuous_g i j)

/-! ## Package H for a transition system -/

/-- **PACKAGE H (items 62–69), principal.**  Three continuous internal representatives of the
three ordinary transitions of a triple overlap, read on the triple overlap domain, are
compared by a continuous, locally constant, kernel-valued defect.  The ordinary law used is
the inherited one; nothing is assumed about the defect. -/
theorem tripleDefect_isKerFunOn_system (S : TransitionSystem B ι G) (i j k : ι)
    {Vij : Set ↥(S.U i ∩ S.U j)} {Vjk : Set ↥(S.U j ∩ S.U k)} {Vik : Set ↥(S.U i ∩ S.U k)}
    {uij : ↥(S.U i ∩ S.U j) → L} {ujk : ↥(S.U j ∩ S.U k) → L} {uik : ↥(S.U i ∩ S.U k) → L}
    (hij : P.IsInternalRepOn (S.g i j) Vij uij) (hjk : P.IsInternalRepOn (S.g j k) Vjk ujk)
    (hik : P.IsInternalRepOn (S.g i k) Vik uik) :
    P.IsKerFunOn
      ((S.incIJ i j k ⁻¹' Vij) ∩ (S.incJK i j k ⁻¹' Vjk) ∩ (S.incIK i j k ⁻¹' Vik))
      (tripleDefect (fun x => uij (S.incIJ i j k x)) (fun x => ujk (S.incJK i j k x))
        (fun x => uik (S.incIK i j k x))) := by
  have hij' := (hij.comp P (S.continuous_incIJ i j k)).mono P
    (fun x hx => hx.1.1 : ((S.incIJ i j k ⁻¹' Vij) ∩ (S.incJK i j k ⁻¹' Vjk)
      ∩ (S.incIK i j k ⁻¹' Vik)) ⊆ S.incIJ i j k ⁻¹' Vij)
  have hjk' := (hjk.comp P (S.continuous_incJK i j k)).mono P
    (fun x hx => hx.1.2 : ((S.incIJ i j k ⁻¹' Vij) ∩ (S.incJK i j k ⁻¹' Vjk)
      ∩ (S.incIK i j k ⁻¹' Vik)) ⊆ S.incJK i j k ⁻¹' Vjk)
  have hik' := (hik.comp P (S.continuous_incIK i j k)).mono P
    (fun x hx => hx.2 : ((S.incIJ i j k ⁻¹' Vij) ∩ (S.incJK i j k ⁻¹' Vjk)
      ∩ (S.incIK i j k ⁻¹' Vik)) ⊆ S.incIK i j k ⁻¹' Vik)
  exact P.tripleDefect_isKerFunOn hij' hjk' hik' (fun x _ => S.g_trans_on i j k x)

/-! ## Package N — relation to the ordinary transition data (items 101–107) -/

/-- **PACKAGE N (item 102), principal.**  Every internal representative projects to exactly
the ordinary transition map it represents. -/
theorem proj_rep_eq_transition (S : TransitionSystem B ι G) {i j : ι}
    {V : Set ↥(S.U i ∩ S.U j)} {u : ↥(S.U i ∩ S.U j) → L}
    (hu : P.IsInternalRepOn (S.g i j) V u) {x : ↥(S.U i ∩ S.U j)} (hx : x ∈ V) :
    P.proj (u x) = S.g i j x := hu.2 x hx

/-- **PACKAGE N (items 103–106), principal — the local action diagram.**  Let the ordinary
group act on an ordinary model `F`, let the internal group act on an internal model `F'`, and
let `π : F' → F` intertwine the two actions along the projection.  Then the action of a
continuous internal representative on the internal model covers, through `π`, the action of
the ordinary transition on the ordinary model.  Nothing is glued: this is one commuting local
diagram (item 104). -/
theorem local_action_diagram_commutes {X : Type u} [TopologicalSpace X] {g : X → G}
    {V : Set X} {u : X → L} (hu : P.IsInternalRepOn g V u)
    {F F' : Type*} [MulAction G F] [MulAction L F'] (π : F' → F)
    (hπ : ∀ (l : L) (f' : F'), π (l • f') = P.proj l • π f')
    {x : X} (hx : x ∈ V) (f' : F') :
    π (u x • f') = g x • π f' := by
  rw [hπ, hu.2 x hx]

end InternalProjection

/-! ## Package P — the frozen output interface (items 113–115) -/

/-- **NEWLY DEFINED (item 113), principal interface.**  The frozen Task-28 output: for each
pair of indices a refinement of the overlap, and on each refined overlap a continuous
internal representative of the ordinary transition map.  There is deliberately **no** field
asserting that any defect is trivial. -/
structure InternalTransitionCandidate {L : Type w} {G : Type v} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] [Group G] [TopologicalSpace G] (P : InternalProjection L G)
    {B : Type u} [TopologicalSpace B] {ι : Type t} (S : TransitionSystem B ι G) where
  /-- The refinement index of each overlap. -/
  Idx : ι → ι → Type u
  /-- The refined overlap domains. -/
  V : ∀ i j, Idx i j → Set ↥(S.U i ∩ S.U j)
  /-- Each refined domain is open. -/
  isOpen_V : ∀ i j a, IsOpen (V i j a)
  /-- The refined domains cover the overlap. -/
  covers : ∀ i j (x : ↥(S.U i ∩ S.U j)), ∃ a, x ∈ V i j a
  /-- The stored continuous internal representatives. -/
  u : ∀ i j, Idx i j → (↥(S.U i ∩ S.U j) → L)
  /-- Each stored map is a continuous internal representative of the ordinary transition. -/
  u_isRep : ∀ i j a, P.IsInternalRepOn (S.g i j) (V i j a) (u i j a)

namespace InternalTransitionCandidate

open InternalProjection

variable {L : Type w} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {P : InternalProjection L G} {B : Type u} [TopologicalSpace B]
  {ι : Type t} {S : TransitionSystem B ι G}

/-- **PACKAGE P.**  The kernel ambiguity carried by the interface: on the intersection of two
refined domains the two stored representatives of the same ordinary transition differ by a
continuous kernel-valued function. -/
theorem kerAmbiguity (C : InternalTransitionCandidate P S) (i j : ι) (a b : C.Idx i j) :
    P.IsKerFunOn (C.V i j a ∩ C.V i j b) (relFactor (C.u i j a) (C.u i j b)) :=
  P.relFactor_isKerFunOn ((C.u_isRep i j a).mono P Set.inter_subset_left)
    ((C.u_isRep i j b).mono P Set.inter_subset_right)

/-- **PACKAGE P.**  The triple-overlap defect carried by the interface. -/
def defect (C : InternalTransitionCandidate P S) (i j k : ι) (a : C.Idx i j) (b : C.Idx j k)
    (c : C.Idx i k) : ↥(S.tripleDom i j k) → L :=
  tripleDefect (fun x => C.u i j a (S.incIJ i j k x)) (fun x => C.u j k b (S.incJK i j k x))
    (fun x => C.u i k c (S.incIK i j k x))

/-- The domain on which the interface defect is defined. -/
def defectDom (C : InternalTransitionCandidate P S) (i j k : ι) (a : C.Idx i j) (b : C.Idx j k)
    (c : C.Idx i k) : Set ↥(S.tripleDom i j k) :=
  (S.incIJ i j k ⁻¹' C.V i j a) ∩ (S.incJK i j k ⁻¹' C.V j k b) ∩
    (S.incIK i j k ⁻¹' C.V i k c)

/-- **PACKAGE P, principal.**  The interface defect is a continuous kernel-valued function. -/
theorem defect_isKerFunOn (C : InternalTransitionCandidate P S) (i j k : ι) (a : C.Idx i j)
    (b : C.Idx j k) (c : C.Idx i k) :
    P.IsKerFunOn (C.defectDom i j k a b c) (C.defect i j k a b c) :=
  P.tripleDefect_isKerFunOn_system S i j k (C.u_isRep i j a) (C.u_isRep j k b)
    (C.u_isRep i k c)

/-- **PACKAGE P.**  The interface defect is locally constant. -/
theorem defect_isLocallyConstant (C : InternalTransitionCandidate P S) (i j k : ι)
    (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k) :
    IsLocallyConstant (P.toKerFun (C.defect_isKerFunOn i j k a b c)) :=
  P.isLocallyConstant_toKerFun _

/-- **PACKAGE I / P, principal.**  Exact compatibility of the stored representatives on a
triple overlap holds exactly when the interface defect is trivial there. -/
theorem exact_compatibility_iff_defect_trivial (C : InternalTransitionCandidate P S)
    (i j k : ι) (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k) :
    (∀ x ∈ C.defectDom i j k a b c,
        C.u j k b (S.incJK i j k x) * C.u i j a (S.incIJ i j k x)
          = C.u i k c (S.incIK i j k x))
      ↔ ∀ x ∈ C.defectDom i j k a b c, C.defect i j k a b c x = 1 :=
  InternalProjection.exact_internal_transition_compatibility_iff_defect_trivial _ _ _

end InternalTransitionCandidate

/-- **PACKAGE D / P, principal.**  The frozen interface exists: every transition system,
together with a frozen internal projection, produces a candidate — refined overlaps carrying
continuous internal representatives.  No compatibility is claimed. -/
noncomputable def candidateOfSystem {L : Type w} {G : Type v} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] [Group G] [TopologicalSpace G] (P : InternalProjection L G)
    {B : Type u} [TopologicalSpace B] {ι : Type t} (S : TransitionSystem B ι G) :
    InternalTransitionCandidate P S where
  Idx := fun i j => (P.overlapRefinement S i j).Idx
  V := fun i j => (P.overlapRefinement S i j).V
  isOpen_V := fun i j => (P.overlapRefinement S i j).isOpen_V
  covers := fun i j x => (P.overlapRefinement S i j).covers x
  u := fun i j => (P.overlapRefinement S i j).rep
  u_isRep := fun i j => (P.overlapRefinement S i j).rep_isRep

/-- **PACKAGE P (item 114).**  The special case: a candidate all of whose triple defects are
trivial.  Its existence is **not** claimed anywhere (item 115). -/
def IsCompatibleInternalTransitionSystem {L : Type w} {G : Type v} [Group L]
    [TopologicalSpace L] [IsTopologicalGroup L] [Group G] [TopologicalSpace G]
    {P : InternalProjection L G} {B : Type u} [TopologicalSpace B] {ι : Type t}
    {S : TransitionSystem B ι G} (C : InternalTransitionCandidate P S) : Prop :=
  ∀ (i j k : ι) (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k),
    ∀ x ∈ C.defectDom i j k a b c, C.defect i j k a b c x = 1

end NullSectorTask28
