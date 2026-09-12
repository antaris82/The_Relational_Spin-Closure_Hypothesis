import RequestProject.Spine.E2.Descent.PairwiseDescent

/-!
# Task 29, Package D: the preserved negative control

**PERMANENTLY PRESERVED COUNTEREXAMPLE (items 38, 110, 140).**

Package D proves the positive verdict

`TripleDefectFree C → PairwiseRefinementCoherent C`

*for the inherited defect-free predicate*, which quantifies over **all** index triples,
repeated indices included.  The repeated-index instances are genuinely load-bearing: this
module exhibits, inside the existing kernel system and with no extra machinery, a refined
internal candidate whose triple defects are trivial for every triple of **pairwise distinct**
indices, and which nevertheless fails same-pair refinement coherence.

The example is the smallest one available: a one-point base, a one-element index set (so that
*no* triple of pairwise distinct indices exists at all), a trivial ordinary group, the
two-element discrete central kernel `K2`, and two refinement patches on the single overlap
carrying the two different constant representatives `1` and `z ≠ 1`.

It follows that

* the distinct-index restriction `TripleDefectFreeDistinct` does **not** imply
  `PairwiseRefinementCoherent` (`tripleDefectFreeDistinct_not_imp_pairwiseRefinementCoherent`);
* consequently `κ` is *not* formally derivable from the distinct-index part of `δ`, and the
  positive verdict of Package D really does depend on the repeated-index triples;
* the same example is **not** triple-defect-free in the inherited sense
  (`badCandidate_not_tripleDefectFree`), exactly as the positive verdict requires.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask29

namespace Counterexample

open NullSectorTask28
open NullSectorTask28.InternalProjection

/-! ## The minimal carrier data -/

/-- The two-element discrete central internal group. -/
def K2 : Type := Multiplicative (ZMod 2)

instance : CommGroup K2 := inferInstanceAs (CommGroup (Multiplicative (ZMod 2)))
instance : DecidableEq K2 := inferInstanceAs (DecidableEq (Multiplicative (ZMod 2)))
instance : TopologicalSpace K2 := ⊥
instance : DiscreteTopology K2 := ⟨rfl⟩
instance : ContinuousMul K2 := ⟨continuous_of_discreteTopology⟩
instance : ContinuousInv K2 := ⟨continuous_of_discreteTopology⟩
instance : IsTopologicalGroup K2 := ⟨⟩

/-- The nontrivial element of the kernel. -/
def z : K2 := Multiplicative.ofAdd (1 : ZMod 2)

theorem z_ne_one : z ≠ 1 := by decide

/-- The trivial ordinary group. -/
def GTriv : Type := PUnit

instance : CommGroup GTriv := inferInstanceAs (CommGroup PUnit)
instance : TopologicalSpace GTriv := ⊥
instance : Subsingleton GTriv := inferInstanceAs (Subsingleton PUnit)

/-- The one-point base. -/
def Pt : Type := PUnit

instance : TopologicalSpace Pt := ⊥
instance : Subsingleton Pt := inferInstanceAs (Subsingleton PUnit)

/-- The single point of the base. -/
def ptB : Pt := PUnit.unit

/-- The one-element index set of the cover. -/
def Ix : Type := PUnit

instance : Subsingleton Ix := inferInstanceAs (Subsingleton PUnit)

/-- The single chart index. -/
def ix : Ix := PUnit.unit

/-- The projection onto the trivial ordinary group: everything is in the kernel. -/
def projTriv : K2 →* GTriv where
  toFun := fun _ => 1
  map_one' := rfl
  map_mul' := fun _ _ => Subsingleton.elim _ _

/-- The frozen internal projection of the counterexample: continuous, surjective, with a
global (hence local) continuous section, central discrete kernel. -/
def PTriv : InternalProjection K2 GTriv where
  proj := projTriv
  continuous_proj := continuous_const
  surjective_proj := fun _ => ⟨1, Subsingleton.elim _ _⟩
  hasLocalSection := fun k => ⟨Set.univ, isOpen_univ, Set.mem_univ k, fun _ => 1,
    continuousOn_const, fun _ _ => Subsingleton.elim _ _⟩
  ker_central := fun a _ b => mul_comm a b
  ker_discrete := inferInstance

/-- The trivial ordinary transition system on the one-point base with one chart. -/
def trivSystem : TransitionSystem Pt Ix GTriv where
  U := fun _ => Set.univ
  isOpen_U := fun _ => isOpen_univ
  cover := fun _ => ⟨ix, Set.mem_univ _⟩
  g := fun _ _ _ => 1
  continuous_g := fun _ _ => continuous_const
  g_self := fun _ _ => rfl
  g_symm := fun _ _ _ _ _ => Subsingleton.elim _ _
  g_trans := fun _ _ _ _ _ _ _ => Subsingleton.elim _ _

/-- The one point of the single overlap. -/
def pt : ↥(trivSystem.U ix ∩ trivSystem.U ix) :=
  ⟨ptB, Set.mem_univ _, Set.mem_univ _⟩

/-- **THE COUNTEREXAMPLE (item 38).**  Two refinement patches on the single overlap, carrying
the two different constant representatives `1` and `z`.  Both are continuous internal
representatives of the (trivial) ordinary transition. -/
def badCandidate : InternalTransitionCandidate PTriv trivSystem where
  Idx := fun _ _ => Bool
  V := fun _ _ _ => Set.univ
  isOpen_V := fun _ _ _ => isOpen_univ
  covers := fun _ _ _ => ⟨true, Set.mem_univ _⟩
  u := fun _ _ p _ => if p then z else 1
  u_isRep := fun _ _ _ => ⟨continuousOn_const, fun _ _ => Subsingleton.elim _ _⟩

/-- The two stored representatives really are different. -/
theorem badCandidate_u_ne :
    badCandidate.u ix ix false pt
      ≠ badCandidate.u ix ix true pt := by
  simpa [badCandidate] using (Ne.symm z_ne_one)

/-- **PACKAGE D, negative control.**  The counterexample is defect-free for every triple of
pairwise distinct indices — vacuously, since the index set has one element. -/
theorem badCandidate_tripleDefectFreeDistinct : TripleDefectFreeDistinct badCandidate := by
  intro i j _ hij _ _ _ _ _ _ _
  exact absurd (Subsingleton.elim i j) hij

/-- **PACKAGE D, negative control.**  The counterexample is *not* pairwise refinement
coherent. -/
theorem badCandidate_not_pairwiseRefinementCoherent :
    ¬ PairwiseRefinementCoherent badCandidate := by
  intro h
  exact badCandidate_u_ne
    (h ix ix false true pt ⟨Set.mem_univ _, Set.mem_univ _⟩)

/-- **PACKAGE D, principal negative endpoint (items 38, 110).**  Triviality of the triple
defects for pairwise *distinct* index triples does **not** imply same-pair refinement
agreement.  The repeated-index instances used in
`tripleDefectFree_imp_pairwiseRefinementCoherent` are therefore indispensable. -/
theorem tripleDefectFreeDistinct_not_imp_pairwiseRefinementCoherent :
    ∃ (C : InternalTransitionCandidate PTriv trivSystem),
      TripleDefectFreeDistinct C ∧ ¬ PairwiseRefinementCoherent C :=
  ⟨badCandidate, badCandidate_tripleDefectFreeDistinct,
    badCandidate_not_pairwiseRefinementCoherent⟩

/-- **CONSISTENCY CHECK.**  The counterexample is not triple-defect-free in the inherited
(full) sense: its completely repeated defect on the patch `true` equals `z ≠ 1`.  This is
exactly what the positive verdict of Package D predicts. -/
theorem badCandidate_not_tripleDefectFree : ¬ TripleDefectFree badCandidate := by
  intro h
  exact z_ne_one (by
    simpa [badCandidate] using
      defectFree_identity_normalisation h ix (C := badCandidate) (a := true)
        (y := pt) (Set.mem_univ _))

end Counterexample

end NullSectorTask29

/-! ## Axiom report of the control (moved here from the Task-29 endpoint) -/

#print axioms NullSectorTask29.Counterexample.tripleDefectFreeDistinct_not_imp_pairwiseRefinementCoherent
#print axioms NullSectorTask29.Counterexample.badCandidate_not_tripleDefectFree
