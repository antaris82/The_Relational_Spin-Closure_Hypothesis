import RequestProject.Spine.Emergent.TangentTransition
import RequestProject.Spine.Solder.InternalLorentz

/-!
# Spine / Solder : the two transition systems are independent

**Third module of the Task-34 tangent/solder layer — the negative control.**

**TASK-35 CORRECTION NOTICE.**  The exact content of this module's endpoint is that
*direct/raw transition identification is not forced*.  It is **not** a proof that no solder
coupling can be derived by any construction: the very gluing used here admits a *regular*
solder (`SpinNative.rescaleRegularSolder`, `RequestProject.Spine.Solder.RegularExamples`), so
raw transition inequality is not an obstruction to solder equivalence.  Task 35 also shows
that the fibrewise/algebraic gate closed by Task 34 is strictly weaker than the
topological/smooth one (`SpinNative.weak_solder_not_regular`).

Two transition systems are now available over one and the same emergent smooth manifold:

* **A.** the genuine tangent coordinate transition `D(φ_ij)` of Mathlib's tangent bundle of
  `EmergentBase.Space B`, computed for the actual Task-33 atlas in
  `RequestProject.Spine.Emergent.TangentTransition`;
* **B.** the internal Lorentz transition `ρ(g̃_ij)` of an emergent Spin-native gluing datum,
  acting on the local model, in `RequestProject.Spine.Solder.InternalLorentz`.

The Task-34 scientific question is whether the already certified data force these to agree.
They do not, and this module proves it by an explicit two-chart example:

`EmergentBase.rescaleGluing` is the base-gluing datum on the whole local model with two
pieces and the smooth linear identification `φ₀₁(v) = 2 • v`, `φ₁₀(v) = 2⁻¹ • v`.  It
satisfies every law of the primitive and is smooth, so Task 33 applies verbatim and the
emergent base is a `C^∞` four-manifold.  Paired with the pointwise trivial Spin-native
gluing datum — which exists on *every* cover — the projected internal Lorentz transition is
the identity, while the tangent coordinate transition is `2 • id`.  A dilation by `2` is not
the identity, and (being no isometry of the intrinsic form) it is not even a Lorentz
transformation.

`SpinNative.tangent_spin_base_data_do_not_force_transition_identification` is the packaged
statement.

## What this does *not* say (Task 34 §8)

It does **not** say that no solder form exists.  The failure is one of *derivability*: the
base-gluing datum and the Spin-native datum, both coherent, do not determine a compatible
identification of the internal Lorentz model with the tangent spaces.  A compensating local
frame field may still exist, and for this very example one does — see
`RequestProject.Spine.Solder.Solder`, where the missing datum is isolated as
`SpinNative.TangentSolderData`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace EmergentBase

open BaseGluingData

/-! ## The smooth rescaling two-chart base gluing -/

/-- The identification maps of the rescaling example: a dilation by `2` from the piece `0`
to the piece `1`, its inverse in the other direction, the identity on a piece. -/
def rescaleφ : Bool → Bool → LocalModel → LocalModel
  | false, true => fun v => (2 : ℝ) • v
  | true, false => fun v => (2 : ℝ)⁻¹ • v
  | false, false => id
  | true, true => id

theorem contDiff_smul_localModel (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : LocalModel => r • v) :=
  contDiff_id.const_smul r

/-- **NEWLY DEFINED (Task 34), the negative control.**  A two-piece base-gluing datum on the
whole local model whose identification map is a nontrivial smooth linear dilation. -/
def rescaleGluing : BaseGluingData LocalModel Bool where
  D _ := Set.univ
  isOpen_D _ := isOpen_univ
  W _ _ := Set.univ
  isOpen_W _ _ := isOpen_univ
  W_subset _ _ := Set.subset_univ _
  W_self _ := rfl
  φ := rescaleφ
  continuousOn_φ i j := by
    cases i <;> cases j <;>
      simp only [rescaleφ] <;>
      first
        | exact continuousOn_id
        | exact (continuous_const_smul _).continuousOn
  φ_mapsTo _ _ := Set.mapsTo_univ _ _
  φ_self i x _ := by cases i <;> rfl
  φ_inv i j x _ := by
    cases i <;> cases j <;> simp [rescaleφ, smul_smul]
  φ_cocycle i j k x _ _ := by
    refine ⟨Set.mem_univ _, ?_⟩
    cases i <;> cases j <;> cases k <;> simp [rescaleφ, smul_smul]

@[simp] theorem rescaleGluing_φ_zero_one :
    rescaleGluing.φ false true = fun v : LocalModel => (2 : ℝ) • v := rfl

@[simp] theorem rescaleGluing_W (i j : Bool) : rescaleGluing.W i j = Set.univ := rfl

/-- **DERIVED (Task 34).**  The rescaling datum is smooth, so Task 33 applies to it: its
emergent base is a `C^∞` manifold over the four-dimensional local model. -/
theorem rescaleGluing_smoothGluing : rescaleGluing.SmoothGluing := by
  intro i j
  cases i <;> cases j <;>
    simp only [rescaleGluing, rescaleφ] <;>
    first
      | exact contDiffOn_id
      | exact (contDiff_smul_localModel _).contDiffOn

theorem rescaleGluing_isManifold :
    IsManifold localModelI (⊤ : ℕ∞) (Space rescaleGluing) :=
  isManifold_of_smoothGluing rescaleGluing_smoothGluing

/-- **DERIVED (Task 34), the tangent side of the control.**  The tangent coordinate
transition of the rescaling example is the dilation by `2`, everywhere. -/
theorem rescaleGluing_tangentTransitionMap (y : LocalModel) :
    rescaleGluing.tangentTransitionMap false true y
      = (2 : ℝ) • ContinuousLinearMap.id ℝ LocalModel := by
  have h : HasFDerivAt (fun v : LocalModel => (2 : ℝ) • v)
      ((2 : ℝ) • ContinuousLinearMap.id ℝ LocalModel) y :=
    (hasFDerivAt_id y).const_smul (2 : ℝ)
  rw [BaseGluingData.tangentTransitionMap, rescaleGluing_W, fderivWithin_univ]
  exact h.fderiv

/-- The dilation by `2` moves the intrinsic unit: it is not the identity. -/
theorem two_smul_sOne_ne_sOne : (2 : ℝ) • (SpinCore.sOne : LocalModel) ≠ SpinCore.sOne := by
  intro h
  have h1 : (2 : ℝ) • (1 : ℝ) = 1 := congrArg Prod.fst h
  rw [smul_eq_mul, mul_one] at h1
  exact one_ne_zero (by linarith : (1 : ℝ) = 0)

end EmergentBase

/-! ## The independence theorem -/

namespace SpinNative

open CechSpinLift NullSectorTask28 SpinCore EmergentBase EmergentBase.BaseGluingData

universe t

/-- **DERIVED (Task 34).**  The projection of the pointwise trivial Spin-native gluing datum
is the identity Lorentz transition at every point and every pair of indices. -/
theorem projectedLorentzTransition_trivial {ι : Type t} {B : BaseGluingData LocalModel ι}
    (i j : ι) (x : Space B) :
    projectedLorentzTransition (trivialCocycle (↥SpinGroup) (emergentCover B)) i j x
      = LinearEquiv.refl ℝ LocalModel := by
  rw [projectedLorentzTransition_def]
  simp only [trivialCocycle_g, map_one, OneMemClass.coe_one]
  rfl

/-- **DERIVED (Task 34), PRINCIPAL — the main independence theorem.**

There is a base-gluing datum `B` which

1. satisfies every law of the Task-32 primitive,
2. is smooth, so that by Task 33 its emergent base is a genuine `C^∞` four-manifold,

and an emergent Spin-native gluing datum `S` on its emergent cover which

3. satisfies every Čech law (it is the pointwise trivial one, which exists on every cover),

such that the **projected internal Lorentz transition is the identity everywhere** while the
**genuine tangent coordinate transition of the emergent manifold is a dilation by `2`**, and
the two therefore differ already in their action on the intrinsic unit vector.

Consequently: *a smooth base gluing together with a coherent Spin-native gluing does not by
itself identify their transition systems.*  The coupling of the internal Lorentz structure
with the tangent geometry is **not derivable** from the certified Task-32/33 data; it is an
additional datum.  (This is a non-derivability statement, not a non-existence statement:
compare `SpinNative.TangentSolderData`.) -/
theorem tangent_spin_base_data_do_not_force_transition_identification :
    ∃ (B : BaseGluingData LocalModel Bool)
      (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)),
      B.SmoothGluing ∧
      IsManifold localModelI (⊤ : ℕ∞) (Space B) ∧
      (∀ (i j : Bool) (x : Space B),
        projectedLorentzTransition S i j x = LinearEquiv.refl ℝ LocalModel) ∧
      ∃ (i j : Bool) (y : LocalModel) (v : LocalModel) (hy : y ∈ B.W i j),
        B.tangentTransitionMap i j y v
          ≠ projectedLorentzTransition S i j (B.chart i ⟨y, B.W_subset i j hy⟩) v := by
  refine ⟨rescaleGluing, trivialCocycle (↥SpinGroup) (emergentCover rescaleGluing),
    rescaleGluing_smoothGluing, rescaleGluing_isManifold,
    fun i j x => projectedLorentzTransition_trivial i j x,
    false, true, 0, SpinCore.sOne, Set.mem_univ _, ?_⟩
  rw [projectedLorentzTransition_trivial, rescaleGluing_tangentTransitionMap]
  exact two_smul_sOne_ne_sOne

end SpinNative

end

/-! ## Axiom audit -/

#print axioms EmergentBase.rescaleGluing
#print axioms EmergentBase.rescaleGluing_tangentTransitionMap
#print axioms SpinNative.tangent_spin_base_data_do_not_force_transition_identification
