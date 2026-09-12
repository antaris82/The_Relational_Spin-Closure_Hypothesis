import RequestProject.Spine.Deformation.NeutralRegression
import RequestProject.Spine.Task36.OrientationReversing

/-!
# Task 37 / Part II : regular closure solutions and their admissibility

**Fourth module of the Task-37 deformation-preparation branch.**

A deformed Spin-side transport candidate is **not** automatically a geometry.  This module
separates the two notions once and for all:

```text
    candidate            : a member of a deformation family at a parameter value
    closure solution     : that member *together with* a globally consistent
                           smooth gluing and a regular tangent solder
```

`Task37.Deformation.RegularClosureSolution F p` is the solution object and
`Task37.Deformation.RegularClosureAdmissible F p` its existence statement.  The fields are

1. `smoothGluing` — the parameter's base gluing is `C^∞`, so the emergent base really is a
   smooth four-manifold (Task 33);
2. `solder` — a *regular tangent solder* for the parameter's native Spin datum: fibrewise
   linear comparisons with `C^∞` local representatives satisfying the exact intertwining square
   between the genuine tangent transitions `D(φ_ij)` of the atlas and the **projected** native
   Spin transition (Task 35).

Nothing here is true by construction: the solder equation constrains the parameter's Spin datum
against the parameter's own base, and neither side may be adjusted independently.

## Ordering of observables (Task 37 §16)

The **first** question for any deformation is closure existence:

```text
    λ  ⟶  shared Spin deformation  ⟶  gluing/solder compatibility  ⟶  EXISTS / DOES NOT EXIST
```

Metric, transport-law, symmetry-class or any other classification question may only be asked
*about admitted solutions*, and only in a later task.  This module therefore contains no
classification notion at all.

## Anti-vacuity (Task 37 §17)

The predicate is genuinely falsifiable, and this is proved here, not asserted:

* `moebiusTransportFamily_not_admissible` — a family over the frozen orientation-reversing
  model is admissible at **no** parameter value;
* `selective_family_admissible_zero` together with `selective_family_not_admissible_of_ne` —
  a co-varying family which is admissible **exactly** at `λ = 0`.

So there is no theorem of the form `∀ λ, RegularClosureAdmissible F λ`, and there cannot be
one for arbitrary families.  Whether the *Spin-side* smoke-test family
`Task37.Deformation.loopTransportFamily` is admissible away from `λ = 0` is deliberately left
open: it is the Task-38 question.

## The two future experiments (Task 37 §15)

* **CONTROL A — fixed geometry.**  `SharedTransportFamily.fixedBase` families, characterised by
  `Task37.Deformation.IsFixedBase`: the base is held frozen while the Spin-side transport is
  deformed.  Diagnostic only.
* **MAIN TEST B — reciprocal closure.**  General `SharedTransportFamily` families, in which the
  relational/base geometry co-varies with the shared Spin-side transport.  This is the
  experiment the project hypothesis is about.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task37

namespace Deformation

open CechSpinLift SpinCore SpinNative EmergentBase Task36
open EmergentBase.BaseGluingData

universe t u

/-! ## The solution object -/

/-- **NEWLY DEFINED (Task 37), PRINCIPAL — a regular global closure solution.**

At the parameter value `p` of a deformation family: the base gluing is smooth and the family's
native Spin datum at `p` is regularly soldered to the genuine tangent geometry of the emergent
manifold.  The Lorentz side of the solder square is the *projected* Spin datum, so the whole
system has one common origin. -/
structure RegularClosureSolution {P : Type u} {ι : Type t} (F : SharedTransportFamily P ι)
    (p : P) where
  /-- The parameter's base gluing is `C^∞`. -/
  smoothGluing : (F.base p).SmoothGluing
  /-- A regular tangent solder for the parameter's native Spin transition datum. -/
  solder : SmoothTangentSolderData (F.base p) (F.spin p)

/-- **NEWLY DEFINED (Task 37), PRINCIPAL — the closure observable.**

`RegularClosureAdmissible F p` says that the deformation family `F` closes regularly at the
parameter value `p`.  This existence question is the *first* observable of the next task. -/
def RegularClosureAdmissible {P : Type u} {ι : Type t} (F : SharedTransportFamily P ι)
    (p : P) : Prop :=
  Nonempty (RegularClosureSolution F p)

namespace RegularClosureSolution

variable {P : Type u} {ι : Type t} {F : SharedTransportFamily P ι} {p : P}

/-- **DERIVED (Task 37).**  Every admitted solution inherits the frozen Task-36 endpoints:
orientation compatibility of the emergent atlas, the identification of the tangent Lorentz
transition system with the projected native Spin cocycle, and triviality of the project-native
Čech Spin-lifting obstruction. -/
theorem reconvergence (Sol : RegularClosureSolution F p) :
    (∃ a : ι → LocalModel → ℝ,
      (∀ i, ContinuousOn (a i) ((F.base p).D i)) ∧
      (∀ i y, a i y ≠ 0) ∧
      (∀ i j, ∀ y ∈ (F.base p).W i j,
        LinearMap.det (((F.base p).tangentTransitionMap i j y : LocalModel →ₗ[ℝ] LocalModel))
          * a i y = a j ((F.base p).φ i j y))) ∧
    (∀ (i j : ι) (y : LocalModel) (hy : y ∈ (F.base p).W i j) (v : LocalModel),
      Sol.solder.solderLorentzRep i j y v
        = projectedLorentzTransition (F.spin p) i j
            ((F.base p).chart i ⟨y, (F.base p).W_subset i j hy⟩) v) ∧
    (∀ D : SpinLiftFamily internalSpinProjection (project internalSpinProjection (F.spin p)),
      D.obstruction = trivialClass internalSpinProjection (emergentCover (F.base p))) :=
  classical_reconvergence Sol.smoothGluing Sol.solder

end RegularClosureSolution

/-! ## CONTROL A versus MAIN TEST B -/

/-- **NEWLY DEFINED (Task 37).**  A family is a *fixed-base control* when its relational
geometry does not move with the parameter.  CONTROL A experiments are exactly the experiments
run on such families. -/
def IsFixedBase {P : Type u} {ι : Type t} (F : SharedTransportFamily P ι) : Prop :=
  ∀ p q : P, F.base p = F.base q

theorem isFixedBase_fixedBase {P : Type u} {ι : Type t} {B : BaseGluingData LocalModel ι}
    (S : P → NativeSpinTransitionData ↥SpinGroup (emergentCover B)) :
    IsFixedBase (SharedTransportFamily.fixedBase S) :=
  fun _ _ => rfl

theorem isFixedBase_loopTransportFamily (κ : Type) [DecidableEq κ] :
    IsFixedBase (loopTransportFamily κ) :=
  fun _ _ => rfl

/-! ## The neutral reference sector is a solution -/

/-- **DERIVED (Task 37), PRINCIPAL — the neutral reference sector closes.**

The `λ = 0` member of the Spin-side smoke-test family is a regular global closure solution:
the frozen Task-36 data solve it exactly. -/
def loopTransportFamily_zero_solution (κ : Type) [DecidableEq κ] :
    RegularClosureSolution (loopTransportFamily κ) 0 where
  smoothGluing := loopTransportFamily_zero_smoothGluing κ
  solder := loopTransportFamily_zero_solder κ

theorem loopTransportFamily_admissible_zero (κ : Type) [DecidableEq κ] :
    RegularClosureAdmissible (loopTransportFamily κ) 0 :=
  ⟨loopTransportFamily_zero_solution κ⟩

/-! ## Anti-vacuity controls -/

section AntiVacuity

/-- The family over the frozen orientation-reversing model, with the trivial native Spin
datum at every parameter value. -/
def moebiusTransportFamily : ScalarTransportFamily (Unit × Bool) :=
  SharedTransportFamily.fixedBase (B := moebiusGluing)
    (fun _ : ℝ => trivialCocycle (↥SpinGroup) (emergentCover moebiusGluing))

/-- **DERIVED (Task 37), PRINCIPAL anti-vacuity control I.**  There is a deformation family
which admits **no** regular closure solution at any parameter value: the closure predicate is
not inhabited by construction. -/
theorem moebiusTransportFamily_not_admissible (l : ℝ) :
    ¬ RegularClosureAdmissible moebiusTransportFamily l := by
  rintro ⟨Sol⟩
  exact (orientation_reversing_gluing_no_solder
    (trivialCocycle (↥SpinGroup) (emergentCover moebiusGluing))).false Sol.solder

/-- The wrap-around involution selected by a parameter value: the identity at the neutral
value, the orientation-reversing flip elsewhere. -/
def selectiveTwist (l : ℝ) : LoopTwist :=
  if l = 0 then LoopTwist.id' else LoopTwist.flip

theorem selectiveTwist_zero : selectiveTwist 0 = LoopTwist.id' := if_pos rfl

theorem selectiveTwist_of_ne {l : ℝ} (hl : l ≠ 0) : selectiveTwist l = LoopTwist.flip :=
  if_neg hl

/-- A **co-varying** (MAIN TEST B shaped) family: the relational geometry itself moves with the
parameter, and the Spin datum is trivial throughout. -/
def selectiveFamily : ScalarTransportFamily (Unit × Bool) where
  base := fun l => loopGluingOf Unit (selectiveTwist l)
  spin := fun l =>
    trivialCocycle (↥SpinGroup) (emergentCover (loopGluingOf Unit (selectiveTwist l)))

/-- A regular solder of the periodic model, transported along an equation of involutions. -/
def loopSolderOfEq {t : LoopTwist} (ht : t = LoopTwist.id') :
    SmoothTangentSolderData (loopGluingOf Unit t)
      (trivialCocycle (↥SpinGroup) (emergentCover (loopGluingOf Unit t))) := by
  subst ht
  exact loopRegularSolder

theorem no_solder_of_eq_flip {t : LoopTwist} (ht : t = LoopTwist.flip)
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover (loopGluingOf Unit t))) :
    IsEmpty (SmoothTangentSolderData (loopGluingOf Unit t) S) := by
  subst ht
  exact orientation_reversing_gluing_no_solder S

/-- **DERIVED (Task 37), anti-vacuity control II (a).**  The co-varying family closes at the
neutral value. -/
theorem selective_family_admissible_zero : RegularClosureAdmissible selectiveFamily 0 :=
  ⟨{ smoothGluing := loopGluingOf_smoothGluing Unit (selectiveTwist 0)
     solder := loopSolderOfEq selectiveTwist_zero }⟩

/-- **DERIVED (Task 37), PRINCIPAL anti-vacuity control II (b).**  The same family closes at
**no** other parameter value.  So the closure predicate genuinely separates parameter values:
`λ = 0` can be isolated, and a universal existence theorem is impossible. -/
theorem selective_family_not_admissible_of_ne {l : ℝ} (hl : l ≠ 0) :
    ¬ RegularClosureAdmissible selectiveFamily l := by
  rintro ⟨Sol⟩
  exact (no_solder_of_eq_flip (selectiveTwist_of_ne hl) (selectiveFamily.spin l)).false Sol.solder

/-- **DERIVED (Task 37), PRINCIPAL — no universal closure theorem.**  It is *false* that every
deformation family closes at every parameter value. -/
theorem not_forall_regularClosureAdmissible :
    ¬ ∀ (ι : Type) (F : ScalarTransportFamily ι) (l : ℝ), RegularClosureAdmissible F l :=
  fun h => moebiusTransportFamily_not_admissible 0 (h (Unit × Bool) moebiusTransportFamily 0)

end AntiVacuity

/-! ## Regimes for the next task (Task 37 §19)

Only the *vocabulary* is prepared here.  No theorem below the definitions decides any of these
regimes: deciding them is the Task-38 experiment. -/

section Regimes

variable {ι : Type t}

/-- The set of finite parameter values at which a scalar family closes regularly. -/
def regularRegion (F : ScalarTransportFamily ι) : Set ℝ :=
  {l : ℝ | RegularClosureAdmissible F l}

theorem mem_regularRegion_iff (F : ScalarTransportFamily ι) (l : ℝ) :
    l ∈ regularRegion F ↔ RegularClosureAdmissible F l := Iff.rfl

theorem zero_mem_regularRegion_loopTransportFamily (κ : Type) [DecidableEq κ] :
    (0 : ℝ) ∈ regularRegion (loopTransportFamily κ) :=
  loopTransportFamily_admissible_zero κ

/-- `λ = 0` is an *isolated* regular value: some punctured neighbourhood of `0` closes
nowhere.  (A question, not a claim.) -/
def NeutralIsolated (F : ScalarTransportFamily ι) : Prop :=
  ∃ ε > 0, ∀ l : ℝ, l ≠ 0 → |l| < ε → ¬ RegularClosureAdmissible F l

/-- An open interval of regular values around the neutral value.  (A question, not a claim.) -/
def NeutralInterval (F : ScalarTransportFamily ι) : Prop :=
  ∃ ε > 0, ∀ l : ℝ, |l| < ε → RegularClosureAdmissible F l

/-- Regularity persists arbitrarily far in the positive direction: the `λ → +∞` regime, stated
without ever using an extended real as a parameter. -/
def RegularUnboundedAbove (F : ScalarTransportFamily ι) : Prop :=
  ∀ M : ℝ, ∃ l : ℝ, M < l ∧ RegularClosureAdmissible F l

/-- Regularity persists arbitrarily far in the negative direction: the `λ → -∞` regime. -/
def RegularUnboundedBelow (F : ScalarTransportFamily ι) : Prop :=
  ∀ M : ℝ, ∃ l : ℝ, l < M ∧ RegularClosureAdmissible F l

/-- A finite critical parameter above the neutral value: regular strictly below it, singular at
it.  This is the "branch terminates at finite λ" question. -/
def CriticalAbove (F : ScalarTransportFamily ι) (c : ℝ) : Prop :=
  0 < c ∧ (∀ l : ℝ, 0 ≤ l → l < c → RegularClosureAdmissible F l) ∧
    ¬ RegularClosureAdmissible F c

/-- Asymmetry of the two deformation directions.  (A question, not a claim; nothing in the
interface privileges either sign.) -/
def SignAsymmetric (F : ScalarTransportFamily ι) : Prop :=
  ∃ l : ℝ, 0 < l ∧ (RegularClosureAdmissible F l ↔ ¬ RegularClosureAdmissible F (-l))

end Regimes

end Deformation

end Task37

end

/-! ## Axiom audit -/

#print axioms Task37.Deformation.RegularClosureSolution
#print axioms Task37.Deformation.RegularClosureAdmissible
#print axioms Task37.Deformation.RegularClosureSolution.reconvergence
#print axioms Task37.Deformation.loopTransportFamily_admissible_zero
#print axioms Task37.Deformation.moebiusTransportFamily_not_admissible
#print axioms Task37.Deformation.selective_family_admissible_zero
#print axioms Task37.Deformation.selective_family_not_admissible_of_ne
#print axioms Task37.Deformation.not_forall_regularClosureAdmissible
