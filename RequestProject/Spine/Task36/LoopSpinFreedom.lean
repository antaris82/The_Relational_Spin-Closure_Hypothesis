import RequestProject.Spine.Task36.LoopSolder
import RequestProject.Spine.SpinNative.GaugeEquivalence

/-!
# Task 36 / Adversarial : residual `±1` Spin-lift freedom around a loop (§§7–8)

**Fifth module of the Task-36 adversarial battery.**

Task 31 produced the fixed-cover kernel-twist machinery (`SpinNative.KerCocycle`,
`SpinNative.twist`, `SpinNative.GaugeEquiv`) and the control
`RequestProject.Spine.Controls.SpinNative.KernelTwistControl`, which showed that on a
*two-patch cover with a single overlap* every kernel twist is pure gauge, and recorded
explicitly that producing a **gauge-nontrivial** kernel twist requires cover topology that
that control does not provide.

The periodic model of `RequestProject.Spine.Task36.LoopModel` provides exactly that topology:
the emergent cover of one loop has two patches whose overlap has **two components**.  This
module builds the corresponding sign cocycles and proves the two facts the adversarial battery
asks for:

* `Task36.loop_spin_lift_has_solder` — every sign choice `σ : κ → Bool` twists the trivial
  Spin seed into a native Spin datum which still carries the *same* regular solder, because
  the twist is invisible after projection.  So all of these data solder the *same* tangent
  geometry;
* `Task36.loop_spin_lifts_inequivalent` — distinct sign choices give **gauge-inequivalent**
  Spin data, at the exact fixed-cover equivalence relation `SpinNative.GaugeEquiv` implemented
  by the project.

Consequently:

* `Task36.one_loop_has_kernel_sign_freedom` (one loop): two inequivalent Spin lifts of one and
  the same projected Lorentz transition system;
* `Task36.fixed_cover_spin_choice_family` and `Task36.two_loop_spin_choice_family`
  (`κ` loops, and `κ = Fin 2`): the sign choices inject into the set of gauge classes, so `N`
  independent loops produce `2^N` pairwise inequivalent classes.

## Exactly what is and is not claimed (§8, §17)

**This is the project's fixed-cover, `H¹`-like control, not a theorem identifying it with
`H¹(M; ℤ/2)`**, and the base is `N` *independent periodic fixed-cover loop models* (a disjoint
union of `N` copies of the two-component periodic overlap model), not a literal `T^N`: the
project has no `T^N` construction and no Čech-to-singular comparison for this cover, so no
such identification is asserted.  (Task-37 wording correction §6: `Space B ≅ S¹ × ℝ³` and
`π₁(Space B) ≠ 0` are *not* proved and are not used.)  What is proved is the exact
statement above: `2^N` pairwise gauge-inequivalent native Spin data over one and the same
projected Lorentz transition system, all of them regularly soldered to the same tangent
bundle.

The two lifts are **not** called physically distinct, and neither is called canonical: the
canonical-representative results of the Spin-native branch select a representative inside one
construction, they do not remove the other classes (see `TASK36_AUDIT.md` §17).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task36

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase
open EmergentBase.BaseGluingData

/-! ## A continuity tool -/

/-- **DERIVED (Task 36).**  A function which is constant on each of two open sets covering a
set `S` is continuous on `S`. -/
theorem continuousOn_of_two_opens {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {S U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hS : S ⊆ U ∪ V) {a b : Y}
    (hfU : ∀ x ∈ U, f x = a) (hfV : ∀ x ∈ V, f x = b) : ContinuousOn f S := by
  intro x hx
  rcases hS hx with h | h
  · have heq : (fun _ : X => a) =ᶠ[nhds x] f := by
      filter_upwards [hU.mem_nhds h] with z hz
      exact (hfU z hz).symm
    exact (continuousAt_const.congr heq).continuousWithinAt
  · have heq : (fun _ : X => b) =ᶠ[nhds x] f := by
      filter_upwards [hV.mem_nhds h] with z hz
      exact (hfV z hz).symm
    exact (continuousAt_const.congr heq).continuousWithinAt

/-! ## The two incidence components of a loop, seen in the emergent base -/

section Components

variable (κ : Type) [DecidableEq κ]

/-- The image in the emergent base of the wrap-around incidence component of the loop `n`. -/
def wrapSet (n : κ) : Set (Space (loopGluingOf κ LoopTwist.id')) :=
  (loopGluingOf κ LoopTwist.id').chart (n, false) ''
    {y : ((loopGluingOf κ LoopTwist.id').D (n, false) : Set LocalModel) |
      (y : LocalModel) ∈ slab 0 1}

/-- The image in the emergent base of the ordinary incidence component of the loop `n`. -/
def overSet (n : κ) : Set (Space (loopGluingOf κ LoopTwist.id')) :=
  (loopGluingOf κ LoopTwist.id').chart (n, false) ''
    {y : ((loopGluingOf κ LoopTwist.id').D (n, false) : Set LocalModel) |
      (y : LocalModel) ∈ slab 2 3}

variable {κ}

theorem isOpen_wrapSet (n : κ) : IsOpen (wrapSet κ n) :=
  (loopGluingOf κ LoopTwist.id').isOpenMap_chart (n, false) _
    ((isOpen_slab 0 1).preimage continuous_subtype_val)

theorem isOpen_overSet (n : κ) : IsOpen (overSet κ n) :=
  (loopGluingOf κ LoopTwist.id').isOpenMap_chart (n, false) _
    ((isOpen_slab 2 3).preimage continuous_subtype_val)

/-- **DERIVED (Task 36).**  The wrap-around component and the ordinary component are
disjoint, also across different loops. -/
theorem notMem_overSet_of_mem_wrapSet {n m : κ} {x : Space (loopGluingOf κ LoopTwist.id')}
    (hx : x ∈ wrapSet κ n) : x ∉ overSet κ m := by
  rintro ⟨z, hz, hzx⟩
  obtain ⟨y, hy, hyx⟩ := hx
  by_cases hnm : n = m
  · subst hnm
    have hyz : y = z := (loopGluingOf κ LoopTwist.id').injective_chart (n, false)
      (hyx.trans hzx.symm)
    rw [hyz] at hy
    have h1 : (z : LocalModel).1 < 1 := hy.2
    have h2 : (2 : ℝ) < (z : LocalModel).1 := hz.1
    linarith
  · have hmem : x ∈ (loopGluingOf κ LoopTwist.id').chartRange (m, false) := ⟨z, hzx⟩
    rw [← hyx] at hmem
    have hW := ((loopGluingOf κ LoopTwist.id').mem_chartRange_inter_iff (n, false)
      (m, false) y).1 hmem
    rw [loopGluingOf_W_ne κ LoopTwist.id' (show ((n, false) : κ × Bool).1 ≠ ((m, false) :
      κ × Bool).1 from hnm)] at hW
    exact absurd hW (Set.notMem_empty _)

/-- **DERIVED (Task 36).**  The *cross* double overlap of the two patches of the loop `n` is
covered by its two components. -/
theorem overlap₂_subset_components (n : κ) :
    (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₂ (n, false) (n, true)
      ⊆ wrapSet κ n ∪ overSet κ n := by
  rintro x ⟨⟨y, rfl⟩, hxc⟩
  have hW := ((loopGluingOf κ LoopTwist.id').mem_chartRange_inter_iff (n, false) (n, true) y).1
    hxc
  rw [loopGluingOf_W_same] at hW
  rcases hW with hW | hW
  · exact Or.inl ⟨y, hW, rfl⟩
  · exact Or.inr ⟨y, hW, rfl⟩

theorem overlap₂_subset_components' (n : κ) :
    (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₂ (n, true) (n, false)
      ⊆ wrapSet κ n ∪ overSet κ n := by
  intro x hx
  exact overlap₂_subset_components n ⟨hx.2, hx.1⟩

end Components

/-! ## The `±1` sign cocycles of the loop cover -/

section SignCocycle

variable {κ : Type} [DecidableEq κ]

/-- The kernel element selected by a Boolean: the unit, or the intrinsic `-1`. -/
def zOf : Bool → ↥SpinGroup
  | false => 1
  | true => negOneSpin

theorem zOf_mem_ker (s : Bool) : zOf s ∈ internalSpinProjection.Ker := by
  cases s
  · exact one_mem _
  · exact (InternalProjection.mem_Ker_iff internalSpinProjection).2 spinCover_negOneSpin

theorem zOf_mul_self (s : Bool) : zOf s * zOf s = 1 := by
  cases s
  · exact one_mul 1
  · exact negOneSpin_mul_self

theorem zOf_inj {s r : Bool} (h : zOf s = zOf r) : s = r := by
  cases s <;> cases r
  · rfl
  · exact absurd h.symm negOneSpin_ne_one
  · exact absurd h negOneSpin_ne_one
  · rfl

theorem overlap₂_eq_empty_of_ne {p q : κ × Bool} (h : p.1 ≠ q.1) :
    (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₂ p q = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro x ⟨⟨y, rfl⟩, hx⟩
  have hW := ((loopGluingOf κ LoopTwist.id').mem_chartRange_inter_iff p q y).1 hx
  rw [loopGluingOf_W_ne κ LoopTwist.id' h] at hW
  exact absurd hW (Set.notMem_empty _)

open Classical in
/-- **NEWLY DEFINED (Task 36), principal.**  The `±1` sign function of a choice of sign for
each loop: it is the nontrivial kernel element on the wrap-around component of the loop `n`
whenever the two patch indices differ, and the unit everywhere else. -/
def signFun (σ : κ → Bool) (p q : κ × Bool) (x : Space (loopGluingOf κ LoopTwist.id')) :
    ↥SpinGroup :=
  if p.2 ≠ q.2 ∧ x ∈ wrapSet κ p.1 then zOf (σ p.1) else 1

theorem signFun_of_eq (σ : κ → Bool) {p q : κ × Bool} (h : p.2 = q.2)
    (x : Space (loopGluingOf κ LoopTwist.id')) : signFun σ p q x = 1 :=
  if_neg (fun hc => hc.1 h)

theorem signFun_of_notMem (σ : κ → Bool) (p q : κ × Bool)
    {x : Space (loopGluingOf κ LoopTwist.id')} (hx : x ∉ wrapSet κ p.1) :
    signFun σ p q x = 1 :=
  if_neg (fun hc => hx hc.2)

theorem signFun_of_mem_wrap (σ : κ → Bool) {p q : κ × Bool} (h : p.2 ≠ q.2)
    {x : Space (loopGluingOf κ LoopTwist.id')} (hx : x ∈ wrapSet κ p.1) :
    signFun σ p q x = zOf (σ p.1) :=
  if_pos ⟨h, hx⟩

theorem signFun_mem_ker (σ : κ → Bool) (p q : κ × Bool)
    (x : Space (loopGluingOf κ LoopTwist.id')) :
    signFun σ p q x ∈ internalSpinProjection.Ker := by
  unfold signFun
  split
  · exact zOf_mem_ker _
  · exact one_mem _

/-- **NEWLY DEFINED (Task 36), principal.**  The sign function is a genuine kernel-valued
Čech 1-cocycle on the emergent cover of the periodic model. -/
def signKerCocycle (σ : κ → Bool) :
    KerCocycle internalSpinProjection (emergentCover (loopGluingOf κ LoopTwist.id')) where
  e := signFun σ
  isKer p q := by
    refine ⟨?_, fun x _ => signFun_mem_ker σ p q x⟩
    obtain ⟨n, b⟩ := p
    obtain ⟨m, c⟩ := q
    by_cases hnm : n = m
    · subst hnm
      by_cases hbc : b = c
      · exact continuousOn_const.congr (fun x _ => signFun_of_eq σ (show b = c from hbc) x)
      · have hsub : (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₂ (n, b) (n, c)
            ⊆ wrapSet κ n ∪ overSet κ n := by
          cases b <;> cases c
          · exact absurd rfl hbc
          · exact overlap₂_subset_components n
          · exact overlap₂_subset_components' n
          · exact absurd rfl hbc
        refine continuousOn_of_two_opens (isOpen_wrapSet n) (isOpen_overSet n) hsub
          (a := zOf (σ n)) (b := 1) (fun x hx => ?_) (fun x hx => ?_)
        · exact signFun_of_mem_wrap σ (show ((n, b) : κ × Bool).2 ≠ ((n, c) : κ × Bool).2
            from hbc) hx
        · exact signFun_of_notMem σ (n, b) (n, c)
            (fun hw => notMem_overSet_of_mem_wrapSet hw hx)
    · rw [overlap₂_eq_empty_of_ne (show ((n, b) : κ × Bool).1 ≠ ((m, c) : κ × Bool).1 from hnm)]
      exact continuousOn_empty _
  cocycle p q r x hx := by
    obtain ⟨n, b⟩ := p
    obtain ⟨m, c⟩ := q
    obtain ⟨l, d⟩ := r
    have hpq : x ∈ (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₂ (n, b) (m, c) :=
      (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₃_subset_ij (n, b) (m, c) (l, d) hx
    have hqr : x ∈ (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₂ (m, c) (l, d) :=
      (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₃_subset_jk (n, b) (m, c) (l, d) hx
    have hnm : n = m := by
      by_contra hne
      rw [overlap₂_eq_empty_of_ne (show ((n, b) : κ × Bool).1 ≠ ((m, c) : κ × Bool).1
        from hne)] at hpq
      exact absurd hpq (Set.notMem_empty _)
    have hml : m = l := by
      by_contra hne
      rw [overlap₂_eq_empty_of_ne (show ((m, c) : κ × Bool).1 ≠ ((l, d) : κ × Bool).1
        from hne)] at hqr
      exact absurd hqr (Set.notMem_empty _)
    subst hnm
    subst hml
    by_cases hw : x ∈ wrapSet κ n
    · have hbc : ∀ u v : Bool, u ≠ v → signFun σ (n, u) (n, v) x = zOf (σ n) :=
        fun u v huv => signFun_of_mem_wrap σ (show ((n, u) : κ × Bool).2 ≠ ((n, v) : κ × Bool).2
          from huv) hw
      have heq : ∀ u : Bool, signFun σ (n, u) (n, u) x = 1 :=
        fun u => signFun_of_eq σ rfl x
      cases b <;> cases c <;> cases d
      · rw [heq]; exact one_mul 1
      · rw [heq false, hbc false true Bool.false_ne_true]
        exact one_mul _
      · rw [hbc false true Bool.false_ne_true, hbc true false (Ne.symm Bool.false_ne_true),
          heq false]
        exact zOf_mul_self _
      · rw [hbc false true Bool.false_ne_true, heq true]
        exact mul_one _
      · rw [hbc true false (Ne.symm Bool.false_ne_true), heq false]
        exact mul_one _
      · rw [hbc true false (Ne.symm Bool.false_ne_true), hbc false true Bool.false_ne_true,
          heq true]
        exact zOf_mul_self _
      · rw [heq true, hbc true false (Ne.symm Bool.false_ne_true)]
        exact one_mul _
      · rw [heq]; exact one_mul 1
    · rw [signFun_of_notMem σ (n, b) (n, c) hw, signFun_of_notMem σ (n, c) (n, d) hw,
        signFun_of_notMem σ (n, b) (n, d) hw]
      exact one_mul 1

/-- **NEWLY DEFINED (Task 36).**  The native Spin transition datum obtained by twisting the
trivial seed by the sign cocycle of a choice of signs. -/
def twistedSpin (σ : κ → Bool) :
    NativeSpinTransitionData ↥SpinGroup (emergentCover (loopGluingOf κ LoopTwist.id')) :=
  twist (trivialCocycle (↥SpinGroup) (emergentCover (loopGluingOf κ LoopTwist.id')))
    (signKerCocycle σ)

theorem twistedSpin_g (σ : κ → Bool) (p q : κ × Bool)
    (x : Space (loopGluingOf κ LoopTwist.id')) :
    (twistedSpin σ).g p q x = signFun σ p q x := mul_one _

/-- **DERIVED (Task 36), the invisibility of the twist.**  The projected internal Lorentz
transition of a sign-twisted Spin datum is the identity: the sign is a kernel element and the
projection forgets it. -/
theorem projectedLorentzTransition_twistedSpin (σ : κ → Bool) (p q : κ × Bool)
    (x : Space (loopGluingOf κ LoopTwist.id')) :
    projectedLorentzTransition (twistedSpin σ) p q x = LinearEquiv.refl ℝ LocalModel := by
  rw [projectedLorentzTransition_def, twistedSpin_g]
  have h1 : spinCover (signFun σ p q x) = 1 :=
    (InternalProjection.mem_Ker_iff internalSpinProjection).1 (signFun_mem_ker σ p q x)
  rw [h1]
  rfl

/-- **DERIVED (Task 36), §7 — every sign choice is regularly soldered.**  All the twisted
Spin data solder the *same* tangent geometry of the periodic model, by the same comparison
field. -/
theorem loop_spin_lift_has_solder (σ : κ → Bool) :
    Nonempty (SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (twistedSpin σ)) :=
  ⟨loopRegularSolderOf (twistedSpin σ)
    (fun p q x _ => projectedLorentzTransition_twistedSpin σ p q x)⟩

/-! ### Gauge inequivalence of distinct sign choices -/

theorem isPreconnected_chartRange (p : κ × Bool) :
    IsPreconnected ((loopGluingOf κ LoopTwist.id').chartRange p) := by
  haveI : PreconnectedSpace (((loopGluingOf κ LoopTwist.id').D p : Set LocalModel)) :=
    isPreconnected_iff_preconnectedSpace.1 (isPreconnected_D LoopTwist.id' p)
  exact isPreconnected_range ((loopGluingOf κ LoopTwist.id').continuous_chart p)

/-- **DERIVED (Task 36).**  A continuous kernel-valued function on a preconnected set is
constant: the kernel of the intrinsic Spin cover is discrete. -/
theorem ker_const_of_isPreconnected {X : Type} [TopologicalSpace X] {U : Set X}
    (hU : IsPreconnected U) {f : X → ↥SpinGroup}
    (hf : internalSpinProjection.IsKerFunOn U f) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    f x = f y :=
  hU.constant_of_mapsTo (T := (internalSpinProjection.Ker : Set ↥SpinGroup))
    (SetLike.isDiscrete_iff_discreteTopology.2 internalSpinProjection.ker_discrete) hf.1
    (fun z hz => hf.2 z hz) hx hy

/-- **NEWLY DEFINED (Task 36), PRINCIPAL — `loop_spin_lifts_inequivalent`.**

Distinct sign choices give **gauge-inequivalent** native Spin transition data on the periodic
model, at the exact fixed-cover equivalence relation `SpinNative.GaugeEquiv`.

The two components of the cross overlap are what makes this possible: a gauge relabelling is
continuous and kernel-valued on each *connected* patch, hence constant there, so it can only
change the sign on **both** components at once — while the two data differ on exactly one of
them. -/
theorem loop_spin_lifts_inequivalent {σ τ : κ → Bool} (h : σ ≠ τ) :
    ¬ GaugeEquiv internalSpinProjection (twistedSpin σ) (twistedSpin τ) := by
  obtain ⟨n, hn⟩ := Function.ne_iff.1 h
  rintro ⟨lam, hlam⟩
  have hbne : ((n, false) : κ × Bool).2 ≠ ((n, true) : κ × Bool).2 := Bool.false_ne_true
  -- the two test points of the cross overlap
  set xA : Space (loopGluingOf κ LoopTwist.id') :=
    (loopGluingOf κ LoopTwist.id').chart (n, false)
      ⟨pWrap, (loopGluingOf κ LoopTwist.id').W_subset (n, false) (n, true)
        (pWrap_mem_W LoopTwist.id' n)⟩ with hxAdef
  set xB : Space (loopGluingOf κ LoopTwist.id') :=
    (loopGluingOf κ LoopTwist.id').chart (n, false)
      ⟨pOver, (loopGluingOf κ LoopTwist.id').W_subset (n, false) (n, true)
        (pOver_mem_W LoopTwist.id' n)⟩ with hxBdef
  have hxA_i : xA ∈ (loopGluingOf κ LoopTwist.id').chartRange (n, false) := ⟨_, rfl⟩
  have hxB_i : xB ∈ (loopGluingOf κ LoopTwist.id').chartRange (n, false) := ⟨_, rfl⟩
  have hxA_j : xA ∈ (loopGluingOf κ LoopTwist.id').chartRange (n, true) := by
    rw [hxAdef, (loopGluingOf κ LoopTwist.id').chart_eq_chart_of_mem_W (n, false) (n, true)
      (pWrap_mem_W LoopTwist.id' n)]
    exact ⟨_, rfl⟩
  have hxB_j : xB ∈ (loopGluingOf κ LoopTwist.id').chartRange (n, true) := by
    rw [hxBdef, (loopGluingOf κ LoopTwist.id').chart_eq_chart_of_mem_W (n, false) (n, true)
      (pOver_mem_W LoopTwist.id' n)]
    exact ⟨_, rfl⟩
  have hxA_wrap : xA ∈ wrapSet κ n :=
    ⟨⟨pWrap, _⟩, pWrap_mem_slab, rfl⟩
  have hxB_over : xB ∈ overSet κ n :=
    ⟨⟨pOver, _⟩, pOver_mem_slab, rfl⟩
  have hxB_not_wrap : xB ∉ wrapSet κ n :=
    fun hw => notMem_overSet_of_mem_wrapSet hw hxB_over
  -- the gauge law at the two points
  have hA := hlam (n, false) (n, true) xA ⟨hxA_i, hxA_j⟩
  have hB := hlam (n, false) (n, true) xB ⟨hxB_i, hxB_j⟩
  rw [twistedSpin_g, twistedSpin_g, signFun_of_mem_wrap σ hbne hxA_wrap,
    signFun_of_mem_wrap τ hbne hxA_wrap] at hA
  rw [twistedSpin_g, twistedSpin_g, signFun_of_notMem σ (n, false) (n, true) hxB_not_wrap,
    signFun_of_notMem τ (n, false) (n, true) hxB_not_wrap] at hB
  -- the gauge relabelling is constant on each connected patch
  have hconst_i : lam.l (n, false) xA = lam.l (n, false) xB :=
    ker_const_of_isPreconnected (isPreconnected_chartRange (n, false)) (lam.isKer (n, false))
      hxA_i hxB_i
  have hconst_j : lam.l (n, true) xA = lam.l (n, true) xB :=
    ker_const_of_isPreconnected (isPreconnected_chartRange (n, true)) (lam.isKer (n, true))
      hxA_j hxB_j
  rw [hconst_i, hconst_j] at hA
  -- the `xB` equation says the relabelling is trivial there
  have hB' : lam.l (n, false) xB * (lam.l (n, true) xB)⁻¹ = 1 := by
    rw [mul_one] at hB
    exact hB.symm
  -- and the `xA` equation then forces the two signs to agree
  have hcomm := internalSpinProjection.ker_comm (zOf_mem_ker (σ n)) (lam.l (n, false) xB)
  have hfinal : zOf (τ n) = zOf (σ n) := by
    rw [hA, ← hcomm, mul_assoc, hB', mul_one]
  exact hn (zOf_inj hfinal).symm

end SignCocycle

/-! ## The packaged adversarial endpoints -/

/-- **NEWLY DEFINED (Task 36), PRINCIPAL — `one_loop_has_kernel_sign_freedom`.**

On the one-loop model there are two native Spin transition data which

* have the *same* projected visible (Lorentz) transition data on every double overlap,
* both carry a regular tangent solder — so both are Spin lifts of one and the same tangent
  geometry — and yet
* are **not** gauge equivalent.

The residual `±1` freedom around the periodic wrap-around component (the project-native loop
sign control, a fixed-cover `ℤ₂` lift freedom) therefore survives inside the bottom-up
construction; it was not inserted anywhere. -/
theorem one_loop_has_kernel_sign_freedom :
    ∃ S S' : NativeSpinTransitionData ↥SpinGroup
        (emergentCover (loopGluingOf Unit LoopTwist.id')),
      Nonempty (SmoothTangentSolderData (loopGluingOf Unit LoopTwist.id') S) ∧
      Nonempty (SmoothTangentSolderData (loopGluingOf Unit LoopTwist.id') S') ∧
      (∀ (p q : Unit × Bool) (x : Space (loopGluingOf Unit LoopTwist.id')),
        x ∈ (emergentCover (loopGluingOf Unit LoopTwist.id')).overlap₂ p q →
          (project internalSpinProjection S').g p q x
            = (project internalSpinProjection S).g p q x) ∧
      ¬ GaugeEquiv internalSpinProjection S S' := by
  refine ⟨twistedSpin (fun _ => false), twistedSpin (fun _ => true),
    loop_spin_lift_has_solder _, loop_spin_lift_has_solder _, ?_, ?_⟩
  · intro p q x _
    have h1 : spinCover ((twistedSpin (fun _ : Unit => true)).g p q x) = 1 := by
      rw [twistedSpin_g]
      exact (InternalProjection.mem_Ker_iff internalSpinProjection).1 (signFun_mem_ker _ p q x)
    have h2 : spinCover ((twistedSpin (fun _ : Unit => false)).g p q x) = 1 := by
      rw [twistedSpin_g]
      exact (InternalProjection.mem_Ker_iff internalSpinProjection).1 (signFun_mem_ker _ p q x)
    show spinCover _ = spinCover _
    rw [h1, h2]
  · refine loop_spin_lifts_inequivalent ?_
    intro hcon
    have := congrFun hcon ()
    exact absurd this (by decide)

/-- **NEWLY DEFINED (Task 36), PRINCIPAL — the fixed-cover `H¹`-like multiplicity control.**

For a family of `κ` independent loops, the sign choices `κ → Bool` inject into the set of
gauge classes of native Spin data over one and the same projected Lorentz transition system,
and every one of them is regularly soldered.

**This is the project's fixed-cover Čech control, not a theorem identifying the family with
`H¹(M; ℤ/2)`, and the base is a disjoint family of loops, not a literal `T^N`.** -/
theorem fixed_cover_spin_choice_family {κ : Type} [DecidableEq κ] (σ τ : κ → Bool) :
    Nonempty (SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (twistedSpin σ)) ∧
    (GaugeEquiv internalSpinProjection (twistedSpin σ) (twistedSpin τ) → σ = τ) := by
  refine ⟨loop_spin_lift_has_solder σ, fun hg => ?_⟩
  by_contra hne
  exact loop_spin_lifts_inequivalent hne hg

/-- **DERIVED (Task 36), the `N = 2` instance (§8).**  Two independent loops carry
`2² = 4` pairwise gauge-inequivalent native Spin data over the same projected Lorentz
transition system, each of them regularly soldered. -/
theorem two_loop_spin_choice_family :
    Fintype.card (Fin 2 → Bool) = 4 ∧
    (∀ σ τ : Fin 2 → Bool,
      Nonempty (SmoothTangentSolderData (loopGluingOf (Fin 2) LoopTwist.id') (twistedSpin σ)) ∧
      (GaugeEquiv internalSpinProjection (twistedSpin σ) (twistedSpin τ) → σ = τ)) :=
  ⟨by decide, fun σ τ => fixed_cover_spin_choice_family σ τ⟩


end Task36

end

/-! ## Axiom audit -/

#print axioms Task36.signKerCocycle
#print axioms Task36.loop_spin_lift_has_solder
#print axioms Task36.loop_spin_lifts_inequivalent
#print axioms Task36.one_loop_has_kernel_sign_freedom
#print axioms Task36.fixed_cover_spin_choice_family
#print axioms Task36.two_loop_spin_choice_family
