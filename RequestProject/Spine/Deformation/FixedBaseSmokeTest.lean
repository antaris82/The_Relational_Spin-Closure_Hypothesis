import RequestProject.Spine.Deformation.ProjectedParaAction
import RequestProject.Spine.Deformation.ClosureAdmissibility

/-!
# Task 38 / Parts II–III : the fixed-base (CONTROL A) admissibility locus

**Second module of the Task-38 fixed-base smoke test.**

What is varied, and what is not, in the present experiment:

```text
    VARIED        : the native Spin transition/cocycle state of the frozen periodic model
                    (Task37.Deformation.loopSharedSpin l, built from transportState l)
    DERIVED       : the projected Lorentz transition, only through SpinCore.spinCover
    HELD FIXED    : the base gluing datum  Task36.loopGluingOf κ LoopTwist.id'
                    (CONTROL A: Task37.Deformation.IsFixedBase holds)
    SOLVED FOR    : a regular tangent solder, i.e. a C^∞ fibrewise invertible comparison
                    satisfying the exact Task-35 intertwining square
    NOT PRESENT   : transport one-form, path-ordered exponential, loop-transport functional,
                    two-form field strength, Riemann tensor, Einstein dynamics
```

## The question and the answer

```text
    R_A = { l : ℝ | RegularClosureAdmissible (loopTransportFamily κ) l } = ?
```

The answer proved here is `R_A = ℝ`: **every** finite parameter value is admissible, and the
witness is explicit, not obtained from a choice principle.  The reason is structural and is
worth stating precisely, because it is what the smoke test was for:

* on the frozen periodic model every tangent transition of the atlas is the identity
  (`Task36.tangentTransitionMap_loop_id`);
* the deformed Spin datum is supported on the wrap-around incidence component only, where it
  equals the shared state `transportState l`;
* the two patches of one loop are *slabs*, and the wrap-around component and the ordinary
  component sit at opposite ends of the second slab, with room in between.

So the intertwining square can be solved by a comparison field which interpolates smoothly,
inside the second slab, between the identity and the projected transport state: the solder
`A_(n,true)(y) = paraEquiv (l · χ(y₀))` with `χ` a `C^∞` transition function which is `0` on
the ordinary component and `1` on the wrap-around component, and `A_(n,false) = id`.  This is
a genuine compensating regular solder (audit class **A** of Task 38 §14): it is *constructed*,
its smoothness is proved from `Real.smoothTransition`, its invertibility is the Task-37
one-parameter group law, and the intertwining equation is verified on every overlap
component.  It does **not** use `TangentSpace = LocalModel`, an independently chosen Lorentz
transition, an independently chosen base gluing, or a supplied compatibility field.

That the *same* interpolation also exhibits the deformation as a Spin-side coboundary is the
subject of `RequestProject.Spine.Deformation.CocycleGaugeOrbit`; admissibility alone does not
decide it.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task37

namespace Deformation

open CechSpinLift SpinCore SpinNative EmergentBase Task36
open EmergentBase.BaseGluingData

section Loop

variable {κ : Type} [DecidableEq κ]

/-! ## The interpolation profile -/

/-- **NEWLY DEFINED (Task 38).**  The `C^∞` profile used to interpolate inside the second slab
of a loop: it vanishes for loop coordinate `≤ 3` (which covers the ordinary incidence
component `2 < y₀ < 3`) and is `1` for loop coordinate `≥ 4` (which covers the wrap-around
incidence component `4 < y₀ < 5`). -/
def wrapProfile (y : LocalModel) : ℝ := Real.smoothTransition (y.1 - 3)

theorem wrapProfile_of_le {y : LocalModel} (hy : y.1 ≤ 3) : wrapProfile y = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem wrapProfile_of_ge {y : LocalModel} (hy : 4 ≤ y.1) : wrapProfile y = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem contDiff_wrapProfile : ContDiff ℝ (⊤ : ℕ∞) wrapProfile :=
  Real.smoothTransition.contDiff.comp (contDiff_fst.sub contDiff_const)

/-- **NEWLY DEFINED (Task 38).**  The parameter carried by the solder comparison of a patch:
zero on the first patch of a loop, the interpolated parameter on the second. -/
def solderAngle (l : ℝ) (b : Bool) (y : LocalModel) : ℝ :=
  cond b (l * wrapProfile y) 0

theorem solderAngle_false (l : ℝ) (y : LocalModel) : solderAngle l false y = 0 := rfl

theorem solderAngle_true (l : ℝ) (y : LocalModel) :
    solderAngle l true y = l * wrapProfile y := rfl

theorem solderAngle_zero (b : Bool) (y : LocalModel) : solderAngle 0 b y = 0 := by
  cases b
  · rfl
  · show 0 * wrapProfile y = 0
    exact zero_mul _

/-! ## The deformed transition, read as a parameter -/

open Classical in
/-- **NEWLY DEFINED (Task 38).**  The parameter of the deformed native Spin transition on an
overlap: `±l` on the wrap-around component of a crossing overlap, `0` elsewhere.  It is a
*reading* of the Task-37 datum, not a new datum (`loopTransportFun_eq_transportState`). -/
def loopAngle (l : ℝ) (p q : κ × Bool) (x : Space (loopGluingOf κ LoopTwist.id')) : ℝ :=
  if p.2 ≠ q.2 ∧ x ∈ wrapSet κ p.1 then cond p.2 (-l) l else 0

theorem loopAngle_of_eq (l : ℝ) {p q : κ × Bool} (h : p.2 = q.2)
    (x : Space (loopGluingOf κ LoopTwist.id')) : loopAngle l p q x = 0 :=
  if_neg (fun hc => hc.1 h)

theorem loopAngle_of_notMem (l : ℝ) (p q : κ × Bool)
    {x : Space (loopGluingOf κ LoopTwist.id')} (hx : x ∉ wrapSet κ p.1) :
    loopAngle l p q x = 0 :=
  if_neg (fun hc => hx hc.2)

theorem loopAngle_of_mem_wrap (l : ℝ) {p q : κ × Bool} (h : p.2 ≠ q.2)
    {x : Space (loopGluingOf κ LoopTwist.id')} (hx : x ∈ wrapSet κ p.1) :
    loopAngle l p q x = cond p.2 (-l) l :=
  if_pos ⟨h, hx⟩

/-- **DERIVED (Task 38).**  The Task-37 deformed transition function *is* the shared transport
state at the parameter read off by `loopAngle`. -/
theorem loopTransportFun_eq_transportState (l : ℝ) (p q : κ × Bool)
    (x : Space (loopGluingOf κ LoopTwist.id')) :
    loopTransportFun l p q x = transportState (loopAngle l p q x) := by
  unfold loopTransportFun loopAngle
  split
  · cases hp : p.2
    · show dirTransport l false = transportState (cond false (-l) l)
      rfl
    · show dirTransport l true = transportState (cond true (-l) l)
      exact (transportState_neg l).symm
  · exact transportState_zero.symm

/-- **DERIVED (Task 38), PRINCIPAL — the closed form of the deformed projected transition.**
On every overlap the projected Lorentz transition of the Task-37 deformed datum is the closed
form `paraMap` at the parameter `loopAngle`. -/
theorem projectedLoop_apply (l : ℝ) (p q : κ × Bool)
    (x : Space (loopGluingOf κ LoopTwist.id')) (v : LocalModel) :
    projectedLorentzTransition (loopSharedSpin l) p q x v = paraMap (loopAngle l p q x) v := by
  rw [projectedLorentzTransition_def, loopSharedSpin_g, loopTransportFun_eq_transportState]
  exact projectedTransportState_apply _ v

/-! ## Where the wrap-around component is seen from each patch -/

theorem mem_wrapSet_of_slab01 {n : κ} {y : LocalModel} (hy : y ∈ slab 0 1)
    (hyD : y ∈ (loopGluingOf κ LoopTwist.id').D (n, false)) :
    (loopGluingOf κ LoopTwist.id').chart (n, false) ⟨y, hyD⟩ ∈ wrapSet κ n :=
  ⟨⟨y, hyD⟩, hy, rfl⟩

theorem notMem_wrapSet_of_slab23 {n : κ} {y : LocalModel} (hy : y ∈ slab 2 3)
    (hyD : y ∈ (loopGluingOf κ LoopTwist.id').D (n, false)) :
    (loopGluingOf κ LoopTwist.id').chart (n, false) ⟨y, hyD⟩ ∉ wrapSet κ n :=
  fun hw => notMem_overSet_of_mem_wrapSet hw ⟨⟨y, hyD⟩, hy, rfl⟩

theorem mem_wrapSet_of_slab45 {n : κ} {y : LocalModel} (hy : y ∈ slab 4 5)
    (hyD : y ∈ (loopGluingOf κ LoopTwist.id').D (n, true)) :
    (loopGluingOf κ LoopTwist.id').chart (n, true) ⟨y, hyD⟩ ∈ wrapSet κ n := by
  have hyW : y ∈ (loopGluingOf κ LoopTwist.id').W (n, true) (n, false) := by
    rw [loopGluingOf_W_same]
    exact Or.inl hy
  have hchart := (loopGluingOf κ LoopTwist.id').chart_eq_chart_of_mem_W (n, true) (n, false) hyW
  have hφ : (loopGluingOf κ LoopTwist.id').φ (n, true) (n, false) y = unwrap LoopTwist.id' y :=
    φb_tf_of_gt LoopTwist.id' (by linarith [hy.1])
  have hy1 : (4 : ℝ) < y.1 := hy.1
  have hy2 : y.1 < 5 := hy.2
  have hfst : (unwrap LoopTwist.id' y).1 = y.1 - 4 := unwrap_fst LoopTwist.id' y
  have hmem : unwrap LoopTwist.id' y ∈ slab 0 1 :=
    mem_slab.2 ⟨by rw [hfst]; linarith, by rw [hfst]; linarith⟩
  rw [show (⟨y, hyD⟩ : ((loopGluingOf κ LoopTwist.id').D (n, true) : Set LocalModel))
      = ⟨y, (loopGluingOf κ LoopTwist.id').W_subset (n, true) (n, false) hyW⟩ from rfl, hchart]
  exact mem_wrapSet_of_slab01 (by rw [hφ]; exact hmem) _

theorem notMem_wrapSet_of_slab23' {n : κ} {y : LocalModel} (hy : y ∈ slab 2 3)
    (hyD : y ∈ (loopGluingOf κ LoopTwist.id').D (n, true)) :
    (loopGluingOf κ LoopTwist.id').chart (n, true) ⟨y, hyD⟩ ∉ wrapSet κ n := by
  have hyW : y ∈ (loopGluingOf κ LoopTwist.id').W (n, true) (n, false) := by
    rw [loopGluingOf_W_same]
    exact Or.inr hy
  have hchart := (loopGluingOf κ LoopTwist.id').chart_eq_chart_of_mem_W (n, true) (n, false) hyW
  have hφ : (loopGluingOf κ LoopTwist.id').φ (n, true) (n, false) y = y :=
    φb_tf_of_lt LoopTwist.id' (by linarith [hy.2])
  rw [show (⟨y, hyD⟩ : ((loopGluingOf κ LoopTwist.id').D (n, true) : Set LocalModel))
      = ⟨y, (loopGluingOf κ LoopTwist.id').W_subset (n, true) (n, false) hyW⟩ from rfl, hchart]
  exact notMem_wrapSet_of_slab23 (by rw [hφ]; exact hy) _

/-! ## The scalar form of the intertwining equation -/

/-- **DERIVED (Task 38), PRINCIPAL — the solder equation, solved.**

The interpolation profile satisfies, on **every** component of **every** overlap of the frozen
periodic model, the additive equation which the intertwining square reduces to once the
tangent transitions (all of them the identity) and the closed form of the projected transport
state are inserted. -/
theorem solderAngle_step (l : ℝ) (p q : κ × Bool) {y : LocalModel}
    (hy : y ∈ (loopGluingOf κ LoopTwist.id').W p q) :
    solderAngle l q.2 ((loopGluingOf κ LoopTwist.id').φ p q y)
      = solderAngle l p.2 y
        + loopAngle l p q ((loopGluingOf κ LoopTwist.id').chart p
            ⟨y, (loopGluingOf κ LoopTwist.id').W_subset p q hy⟩) := by
  obtain ⟨n, b⟩ := p
  obtain ⟨m, c⟩ := q
  by_cases hnm : n = m
  · subst hnm
    rw [loopGluingOf_W_same] at hy
    cases b <;> cases c
    · rw [loopAngle_of_eq l rfl, add_zero]
      show solderAngle l false _ = solderAngle l false y
      rw [solderAngle_false, solderAngle_false]
    · rcases hy with hy | hy
      · have hφ : (loopGluingOf κ LoopTwist.id').φ (n, false) (n, true) y
            = wrap LoopTwist.id' y := φb_ft_of_lt LoopTwist.id' (by linarith [hy.2])
        have hge : (4 : ℝ) ≤ (wrap LoopTwist.id' y).1 := by
          rw [wrap_fst]; linarith [hy.1]
        rw [hφ, solderAngle_true, wrapProfile_of_ge hge, solderAngle_false,
          loopAngle_of_mem_wrap l (show ((n, false) : κ × Bool).2 ≠ ((n, true) : κ × Bool).2
            from Bool.false_ne_true) (mem_wrapSet_of_slab01 hy _)]
        show l * 1 = 0 + l
        ring
      · have hφ : (loopGluingOf κ LoopTwist.id').φ (n, false) (n, true) y = y :=
          φb_ft_of_gt LoopTwist.id' (by linarith [hy.1])
        rw [hφ, solderAngle_true, wrapProfile_of_le (by linarith [hy.2]), solderAngle_false,
          loopAngle_of_notMem l (n, false) (n, true) (notMem_wrapSet_of_slab23 hy _)]
        show l * 0 = 0 + 0
        ring
    · rcases hy with hy | hy
      · have hφ : (loopGluingOf κ LoopTwist.id').φ (n, true) (n, false) y
            = unwrap LoopTwist.id' y := φb_tf_of_gt LoopTwist.id' (by linarith [hy.1])
        have hle : (unwrap LoopTwist.id' y).1 ≤ 3 := by
          rw [unwrap_fst]; linarith [hy.2]
        rw [hφ, solderAngle_false, solderAngle_true, wrapProfile_of_ge (by linarith [hy.1]),
          loopAngle_of_mem_wrap l (show ((n, true) : κ × Bool).2 ≠ ((n, false) : κ × Bool).2
            from Ne.symm Bool.false_ne_true) (mem_wrapSet_of_slab45 hy _)]
        show (0 : ℝ) = l * 1 + -l
        ring
      · have hφ : (loopGluingOf κ LoopTwist.id').φ (n, true) (n, false) y = y :=
          φb_tf_of_lt LoopTwist.id' (by linarith [hy.2])
        rw [hφ, solderAngle_false, solderAngle_true, wrapProfile_of_le (by linarith [hy.2]),
          loopAngle_of_notMem l (n, true) (n, false) (notMem_wrapSet_of_slab23' hy _)]
        show (0 : ℝ) = l * 0 + 0
        ring
    · rw [loopAngle_of_eq l rfl, add_zero]
      show solderAngle l true _ = solderAngle l true y
      rw [show (loopGluingOf κ LoopTwist.id').φ (n, true) (n, true) y = y from rfl]
  · rw [loopGluingOf_W_ne κ LoopTwist.id'
      (show ((n, b) : κ × Bool).1 ≠ ((m, c) : κ × Bool).1 from hnm)] at hy
    exact absurd hy (Set.notMem_empty y)

/-! ## The explicit regular solder for an arbitrary parameter value -/

/-- **NEWLY DEFINED (Task 38), PRINCIPAL — the compensating regular solder.**

For **every** finite parameter value, an explicit regular tangent solder of the frozen periodic
model for the Task-37 deformed native Spin datum.  The comparison is the identity on the first
patch of every loop and the closed form of the projected transport state, at the interpolated
parameter, on the second; smoothness comes from `Real.smoothTransition`, invertibility from the
Task-37 one-parameter group law, and the overlap law from `solderAngle_step`. -/
def loopParaSolder (l : ℝ) :
    SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l) where
  A p y := paraEquiv (solderAngle l p.2 y)
  contDiffOn_A p := by
    obtain ⟨n, b⟩ := p
    cases b
    · show ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : LocalModel => paraMap (0 : ℝ))
        ((loopGluingOf κ LoopTwist.id').D (n, false))
      exact contDiffOn_const
    · have hprof : ContDiff ℝ (⊤ : ℕ∞) (fun y : LocalModel => l * wrapProfile y) :=
        contDiff_const.mul contDiff_wrapProfile
      show ContDiffOn ℝ (⊤ : ℕ∞) (fun y : LocalModel => paraMap (l * wrapProfile y))
        ((loopGluingOf κ LoopTwist.id').D (n, true))
      exact (contDiff_paraMap.comp hprof).contDiffOn
  intertwine p q y hy v := by
    show paraMap (solderAngle l q.2 _) v
      = (loopGluingOf κ LoopTwist.id').tangentTransitionMap p q y
          (paraMap (solderAngle l p.2 y)
            (projectedLorentzTransition (loopSharedSpin l) p q _ v))
    rw [tangentTransitionMap_loop_id p q hy, projectedLoop_apply, ← paraMap_add,
      solderAngle_step l p q hy]
    rfl

theorem loopParaSolder_A (l : ℝ) (p : κ × Bool) (y : LocalModel) :
    (loopParaSolder l).A p y = paraEquiv (solderAngle l p.2 y) := rfl

/-- **DERIVED (Task 38).**  Exact reduction at the neutral value: the comparison field of the
constructed solder is *literally* the identity comparison of the frozen Task-36 regular solder
at `l = 0`. -/
theorem loopParaSolder_zero_A (p : κ × Bool) (y : LocalModel) :
    (loopParaSolder (κ := κ) 0).A p y = (loopSharedSpin_zero_solder (κ := κ)).A p y := by
  rw [loopParaSolder_A, solderAngle_zero, paraEquiv_zero]
  rfl

/-! ## The admissibility locus -/

/-- **NEWLY DEFINED (Task 38), the fixed-base smoke-test predicate.**  Exactly the Task-37
closure observable, specialised to the CONTROL A family: the base gluing is the frozen
periodic model at every parameter value (`isFixedBase_loopTransportFamily`), and the only
thing that moves is the native Spin transition state. -/
def ControlAAdmissible (κ : Type) [DecidableEq κ] (l : ℝ) : Prop :=
  RegularClosureAdmissible (loopTransportFamily κ) l

theorem controlAAdmissible_iff (l : ℝ) :
    ControlAAdmissible κ l ↔ RegularClosureAdmissible (loopTransportFamily κ) l := Iff.rfl

/-- **DERIVED (Task 38), Part II §4 — the neutral control, reusing the frozen solution.**  This
is the Task-37 endpoint verbatim: the exact Task-36 regular solder solves `l = 0`. -/
theorem controlAAdmissible_zero : ControlAAdmissible κ 0 :=
  loopTransportFamily_admissible_zero κ

/-- **DERIVED (Task 38), PRINCIPAL — the admissibility locus is all of `ℝ`.**

Every finite parameter value of the fixed-base smoke-test family admits a regular global
closure solution, with the explicit witness `loopParaSolder`. -/
theorem controlAAdmissible_all (l : ℝ) : ControlAAdmissible κ l :=
  ⟨{ smoothGluing := loopGluingOf_smoothGluing κ LoopTwist.id'
     solder := loopParaSolder l }⟩

theorem regularRegion_loopTransportFamily :
    regularRegion (loopTransportFamily κ) = Set.univ :=
  Set.eq_univ_of_forall fun l => controlAAdmissible_all l

/-- **DERIVED (Task 38), Part III §7 — the two deformation directions behave identically.**
The admissibility predicate of the fixed control is symmetric under `l ↦ -l`.  Nothing
geometric is read into this: `-l` is only the opposite direction along the native Spin
one-parameter subgroup, and the statement is a corollary of the universal theorem, not of a
separate symmetry argument. -/
theorem controlAAdmissible_neg_iff (l : ℝ) :
    ControlAAdmissible κ l ↔ ControlAAdmissible κ (-l) :=
  ⟨fun _ => controlAAdmissible_all (-l), fun _ => controlAAdmissible_all l⟩

/-- **DERIVED (Task 38).**  The fixed control is *not* in the `NeutralIsolated` regime, and it
*is* in the `NeutralInterval`, `RegularUnboundedAbove` and `RegularUnboundedBelow` regimes of
the Task-37 vocabulary; and there is no finite critical value. -/
theorem controlA_regimes :
    ¬ NeutralIsolated (loopTransportFamily κ) ∧
    NeutralInterval (loopTransportFamily κ) ∧
    RegularUnboundedAbove (loopTransportFamily κ) ∧
    RegularUnboundedBelow (loopTransportFamily κ) ∧
    (∀ c : ℝ, ¬ CriticalAbove (loopTransportFamily κ) c) := by
  refine ⟨?_, ⟨1, one_pos, fun l _ => controlAAdmissible_all l⟩,
    fun M => ⟨M + 1, by linarith, controlAAdmissible_all _⟩,
    fun M => ⟨M - 1, by linarith, controlAAdmissible_all _⟩,
    fun c hc => hc.2.2 (controlAAdmissible_all c)⟩
  rintro ⟨ε, hε, h⟩
  exact h (ε / 2) (by positivity) (by rw [abs_of_pos (by positivity)]; linarith)
    (controlAAdmissible_all _)

end Loop

end Deformation

end Task37

end

/-! ## Axiom audit -/

#print axioms Task37.Deformation.wrapProfile
#print axioms Task37.Deformation.loopTransportFun_eq_transportState
#print axioms Task37.Deformation.projectedLoop_apply
#print axioms Task37.Deformation.solderAngle_step
#print axioms Task37.Deformation.loopParaSolder
#print axioms Task37.Deformation.loopParaSolder_zero_A
#print axioms Task37.Deformation.controlAAdmissible_zero
#print axioms Task37.Deformation.controlAAdmissible_all
#print axioms Task37.Deformation.regularRegion_loopTransportFamily
#print axioms Task37.Deformation.controlAAdmissible_neg_iff
#print axioms Task37.Deformation.controlA_regimes
