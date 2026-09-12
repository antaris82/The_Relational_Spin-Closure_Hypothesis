import RequestProject.Spine.SpinNative.Rigidity
import RequestProject.Spine.E2.SpinProjection

/-!
# Native control : the residual kernel freedom of the *symmetric* Spin-native gluing state

Downstream control for the Task-31 uniqueness layer.  It answers, by explicit witnesses, the
question that Task 31 forbids assuming:

> does the **maximally symmetric Spin-native gluing state** — the identity Spin transition
> data — by itself eliminate all residual kernel ambiguity?

**No.**  On a two-patch cover of a nonempty base, and for *any* central double cover with a
nontrivial kernel element, the identity Spin gluing datum can be twisted by a nontrivial
`{±1}`-valued Čech 1-cocycle.  The twisted datum

* differs from the identity datum at a point of a double overlap
  (`SpinNativeControl.sign_twist_ne_null`), yet
* has exactly the same projection through `ρ`
  (`SpinNativeControl.project_sign_twist_eq`), and therefore
* is a *second* Spin structure over the same projected visible data
  (`SpinNativeControl.two_distinct_native_spin_structures`).

Consequently the strict rigidity condition `SpinNative.NoNontrivialKernelTwist` **fails** on
such a cover (`SpinNativeControl.not_noNontrivialKernelTwist`): it is a genuine assumption,
not a theorem, and "uniqueness" in Task 31 is not an artifact of the API.

The same witness also shows that the two rigidity conditions of
`RequestProject.Spine.SpinNative.Rigidity` are genuinely different: this particular cocycle
*is* gauge trivial (`SpinNativeControl.signTwist_isGaugeTrivial`), so the two Spin structures,
although distinct as gluing data, are gauge equivalent
(`SpinNativeControl.two_structures_gaugeEquiv`).  On a two-patch cover the residual freedom
is therefore pure gauge; nothing here claims that this remains so for a general cover, and
producing a *gauge*-nontrivial kernel twist requires cover topology that this control does
not provide (see `TASK31_PROVENANCE.md`).

**Interpretation boundary.**  `nullGluing` is a *gluing* null state: identity comparison maps
on a fixed cover.  It is not flat spacetime, not a connection, not a curvature statement and
not a dynamical equilibrium; no connection, holonomy or transport exists anywhere in the
Task-31 layer.
-/

noncomputable section

namespace SpinNativeControl

open CechSpinLift NullSectorTask28 SpinNative SpinCore

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] (X : Type w) [TopologicalSpace X]

/-! ## The two-patch cover and the symmetric (null) gluing state -/

/-- The two-patch cover of `X` by the whole space, indexed by `Bool`.  Every overlap is `X`
itself. -/
def twoPatchCover : CechCover X Bool where
  U _ := Set.univ
  isOpen_U _ := isOpen_univ
  covers x := ⟨false, Set.mem_univ x⟩

variable {X}

theorem mem_twoPatch_overlap₂ (i j : Bool) (x : X) : x ∈ (twoPatchCover X).overlap₂ i j :=
  ⟨Set.mem_univ x, Set.mem_univ x⟩

/-- **CONTROL (§7), the GLUING null state.**  The maximally symmetric Spin-native gluing
datum: all comparison maps are the identity of the Spin group.  This is a statement about
gluing only. -/
def nullGluing (L : Type u) [Group L] [TopologicalSpace L] {ι : Type t}
    (𝓤 : CechCover X ι) : NativeSpinTransitionData L 𝓤 where
  g _ _ _ := 1
  continuousOn_g _ _ := continuousOn_const
  cocycle _ _ _ _ _ := one_mul 1

omit [IsTopologicalGroup L] in
@[simp] theorem nullGluing_g {ι : Type t} (𝓤 : CechCover X ι) (i j : ι) (x : X) :
    (nullGluing L 𝓤).g i j x = 1 := rfl

/-! ## The nontrivial kernel twist -/

variable {P : InternalProjection L G} {z : L}

/-- **CONTROL.**  The `{±1}`-valued Čech 1-cocycle of a two-patch cover: the nontrivial
kernel element off the diagonal.  Its cocycle law is exactly `z * z = 1`. -/
def signTwist (P : InternalProjection L G) (hz : z ∈ P.Ker) (hz2 : z * z = 1) :
    KerCocycle P (twoPatchCover X) where
  e i j _ := if i = j then 1 else z
  isKer i j := by
    refine ⟨continuousOn_const, fun _ _ => ?_⟩
    by_cases h : i = j
    · simp only [h, if_pos]
      exact Subgroup.one_mem _
    · simpa only [if_neg h] using hz
  cocycle i j k _ _ := by cases i <;> cases j <;> cases k <;> simp [hz2]

@[simp] theorem signTwist_e (hz : z ∈ P.Ker) (hz2 : z * z = 1) (i j : Bool) (x : X) :
    (signTwist P hz hz2).e i j x = if i = j then 1 else z := rfl

/-- **CONTROL, principal (§7).**  The twisted symmetric state differs from the symmetric
state at every point of the overlap of the two patches. -/
theorem sign_twist_ne_null (hz : z ∈ P.Ker) (hz2 : z * z = 1) (hz1 : z ≠ 1) (x : X) :
    (twist (nullGluing L (twoPatchCover X)) (signTwist P hz hz2)).g false true x
      ≠ (nullGluing L (twoPatchCover X)).g false true x := by
  show (if (false : Bool) = true then 1 else z) * 1 ≠ 1
  simpa only [if_neg (by decide : ¬((false : Bool) = true)), mul_one] using hz1

/-- **CONTROL, principal (§10).**  The twist is invisible after projection through `ρ`. -/
theorem project_sign_twist_eq (hz : z ∈ P.Ker) (hz2 : z * z = 1) (i j : Bool) (x : X) :
    (project P (twist (nullGluing L (twoPatchCover X)) (signTwist P hz hz2))).g i j x
      = (project P (nullGluing L (twoPatchCover X))).g i j x :=
  project_twist P _ _ i j (mem_twoPatch_overlap₂ i j x)

/-- **CONTROL, principal negative result (§10).**  Strict rigidity fails on a two-patch cover
of a nonempty base as soon as the kernel is nontrivial: `SpinNative.NoNontrivialKernelTwist`
is a genuine additional assumption. -/
theorem not_noNontrivialKernelTwist [Nonempty X] (hz : z ∈ P.Ker) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) : ¬ NoNontrivialKernelTwist P (twoPatchCover X) := by
  intro h
  have hval := h (signTwist P hz hz2) false true (Classical.arbitrary X)
    (mem_twoPatch_overlap₂ false true _)
  rw [signTwist_e, if_neg (by decide : ¬((false : Bool) = true))] at hval
  exact hz1 hval

/-- **CONTROL, principal (§10).**  Two *distinct* Spin structures over the same projected
visible data: projection through `ρ` does not make the Spin structure unique. -/
theorem two_distinct_native_spin_structures [Nonempty X] (hz : z ∈ P.Ker) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) :
    ∃ C C' : SpinStructureOver P (project P (nullGluing L (twoPatchCover X))),
      ∃ i j : Bool, ∃ x : X, C.data.g i j x ≠ C'.data.g i j x := by
  classical
  refine ⟨canonicalSpinStructure P (nullGluing L (twoPatchCover X)),
    ⟨twist (nullGluing L (twoPatchCover X)) (signTwist P hz hz2),
      fun i j x _ => project_sign_twist_eq hz hz2 i j x⟩,
    false, true, Classical.arbitrary X, ?_⟩
  exact fun h => sign_twist_ne_null hz hz2 hz1 (Classical.arbitrary X) h.symm

/-! ## …but on a two-patch cover the residual freedom is pure gauge -/

/-- **CONTROL.**  The two-patch sign cocycle is a coboundary: `ε = δλ` with `λ_false = z`,
`λ_true = 1`.  So the strict condition `NoNontrivialKernelTwist` fails here while the
`H¹`-type condition `KernelTwistsGaugeTrivial` is not contradicted. -/
theorem signTwist_isGaugeTrivial (hz : z ∈ P.Ker) (hz2 : z * z = 1) :
    (signTwist P hz hz2 (X := X)).IsGaugeTrivial := by
  have hinv : z⁻¹ = z := by
    rw [inv_eq_iff_mul_eq_one]; exact hz2
  refine ⟨⟨fun i _ => if i = true then 1 else z, fun i => ⟨continuousOn_const, fun _ _ => ?_⟩⟩,
    fun i j x _ => ?_⟩
  · by_cases h : i = true
    · simp only [h, if_pos]
      exact Subgroup.one_mem _
    · simpa only [if_neg h] using hz
  · cases i <;> cases j <;> simp [hinv, hz2]

/-- **CONTROL, principal.**  The two distinct Spin structures over the same projected data are
gauge equivalent: on a two-patch cover the residual kernel freedom is entirely gauge. -/
theorem two_structures_gaugeEquiv (hz : z ∈ P.Ker) (hz2 : z * z = 1) :
    GaugeEquiv P (nullGluing L (twoPatchCover X))
      (twist (nullGluing L (twoPatchCover X)) (signTwist P hz hz2)) :=
  gaugeEquiv_twist_of_isGaugeTrivial _ (signTwist_isGaugeTrivial hz hz2)

/-! ## The intrinsic Spin/Lorentz instance -/

/-- **CONTROL, intrinsic instance.**  The witness for the native intrinsic double cover
`ρ : Spin⁺(1,3) → GLor`, with `z = -1`: the symmetric Spin-native gluing state of a two-patch
cover carries a second, distinct Spin structure with the same `GLor`-valued projection. -/
theorem spin_two_distinct_native_spin_structures (X : Type w) [TopologicalSpace X]
    [Nonempty X] :
    ∃ C C' : SpinStructureOver internalSpinProjection
        (project internalSpinProjection (nullGluing (↥SpinGroup) (twoPatchCover X))),
      ∃ i j : Bool, ∃ x : X, C.data.g i j x ≠ C'.data.g i j x := by
  have hz : negOneSpin ∈ internalSpinProjection.Ker :=
    (mem_ker_spinCover_iff negOneSpin).2 (Or.inr rfl)
  have hz2 : negOneSpin * negOneSpin = 1 := by
    have h := negOneSpin_sq
    rwa [pow_two] at h
  exact two_distinct_native_spin_structures hz hz2 negOneSpin_ne_one

end SpinNativeControl

/-! ## Axiom audit of the controls -/

#print axioms SpinNativeControl.sign_twist_ne_null
#print axioms SpinNativeControl.project_sign_twist_eq
#print axioms SpinNativeControl.not_noNontrivialKernelTwist
#print axioms SpinNativeControl.two_distinct_native_spin_structures
#print axioms SpinNativeControl.signTwist_isGaugeTrivial
#print axioms SpinNativeControl.two_structures_gaugeEquiv
#print axioms SpinNativeControl.spin_two_distinct_native_spin_structures
