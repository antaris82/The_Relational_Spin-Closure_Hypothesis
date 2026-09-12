import RequestProject.Spine.Solder.Independence

/-!
# Spine / Solder : the solder coupling datum and the tangent Lorentz metric

**Fourth module of the Task-34 tangent/solder layer — the isolated missing primitive.**

**TASK-35 CORRECTION NOTICE.**  The datum defined here is the **fibrewise/algebraic** solder.
It carries no regularity, and Task 35 proves it insufficient for bundle-level geometry
(`SpinNative.weak_solder_not_regular`): the regular object is
`SpinNative.SmoothTangentSolderData` (`RequestProject.Spine.Solder.RegularSolder`), which is
equivalent to a bundle equivalence `InternalLorentzBundle(S) ≃ TM`
(`SpinNative.smooth_solder_iff_regular_bundle_equivalence`).  The "torsor" statements below
are for arbitrary *pointwise* automorphism fields; the corresponding statement for the
*regular* gauge group is `SpinNative.SmoothTangentSolderData.regular_solder_torsor`.

`RequestProject.Spine.Solder.Independence` proved that the certified Task-32/33 data do not
determine a coupling between

* the genuine tangent coordinate transitions `D(φ_ij)` of the emergent smooth manifold, and
* the internal Lorentz transitions `ρ(g̃_ij)` of the emergent Spin seed.

This module isolates exactly the additional datum that does couple them, and derives the
tangent Lorentz geometry from it.

## The datum

`SpinNative.TangentSolderData B S` consists of one field and one law:

* `frame i x : LocalModel ≃ₗ[ℝ] TangentSpace localModelI x` — a fibrewise **real-linear
  equivalence** of the internal Lorentz model with the genuine Mathlib tangent space, one for
  each piece of the emergent cover (invertibility is built into the type);
* `compatibility` — on every double overlap of the emergent cover, the exact commuting
  square

  ```text
  LocalModel  --ρ(g̃_ij)(x)-->  LocalModel
      | frame j x                  | frame i x
      v                            v
    T_x M    ----- identity ---->  T_x M
  ```

  i.e. `frame j x = frame i x ∘ ρ(g̃_ij)(x)`.

**Orientation of the square.**  It is fixed by the existing cocycle conventions and is not
guessed: the project's frame comparison is `g_ij = e_i⁻¹ ∘ e_j`
(`LorentzFrames.LorentzFrameData.comparison`), and with that convention
`e_j = e_i ∘ g_ij` is the unique orientation for which the Čech law
`g_ij · g_jk = g_ik` of `CechSpinLift.VisibleCocycle` composes correctly
(`TangentSolderData.compatibility_comp`).

**Nothing else is added.**  No metric, connection, curvature, torsion or dynamics is part of
the datum; the tangent metric below is *derived* from it and the intrinsic form `B_𝒮`.

## Regularity (Task 34 §9.2), stated exactly

The datum imposes **no** pointwise regularity on the frames, and none is needed for the
results below: the regularity that the Lorentz side can see — continuity of the frame
comparison maps on the double overlaps — is already *derived* from the law, because those
comparisons are the projected Spin transitions
(`TangentSolderData.continuousOn_comparison`).  What is *not* derivable, and is explicitly
not claimed, is continuity of the frame field itself in a trivialization of the tangent
bundle, and hence continuity of the induced metric field as a section; see
`TASK34_AUDIT.md`.  Keeping the datum this weak makes the sufficiency statements of this
module correspondingly strong.

## Residual freedom (Task 34 §15)

A solder field is *not* canonical and is not claimed to be: the compatible solder data for a
fixed `(B, S)` form a torsor under the pointwise automorphism fields of the tangent spaces
(`TangentSolderData.exists_gauge`, `TangentSolderData.gauge`), and as soon as the emergent
base is inhabited there are at least two distinct ones
(`TangentSolderData.not_unique`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace SpinNative

open CechSpinLift NullSectorTask28 SpinCore EmergentBase EmergentBase.BaseGluingData

universe t

/-! ## The intrinsic bilinear form as a linear map -/

/-- The intrinsic polarized Lorentz form `B_𝒮` of the E1 core, packaged as a bilinear map.
This is not a new form: it is `SpinCore.BS`. -/
def BSbil : LocalModel →ₗ[ℝ] LocalModel →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ BS
    (fun x y z => by simp only [BS_eq, sip, Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring)
    (fun r x y => by
      simp only [BS_eq, sip, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y z => by simp only [BS_eq, sip, Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring)
    (fun r x y => by
      simp only [BS_eq, sip, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; ring)

@[simp] theorem BSbil_apply (x y : LocalModel) : BSbil x y = BS x y := rfl

/-- **DERIVED.**  The intrinsic form is nondegenerate on the local model. -/
theorem BS_nondegenerate {x : LocalModel} (hx : x ≠ 0) : ∃ y : LocalModel, BS x y ≠ 0 := by
  refine ⟨(x.1, -x.2), ?_⟩
  have hsip : sip x.2 (-x.2) = - sip x.2 x.2 := by
    simp only [sip, Pi.neg_apply]; ring
  have hval : BS x (x.1, -x.2) = x.1 ^ 2 + sip x.2 x.2 := by
    rw [BS_eq, hsip]; ring
  rw [hval]
  rcases eq_or_ne x.1 0 with h1 | h1
  · have h2 : x.2 ≠ 0 := by
      intro h
      exact hx (Prod.ext h1 h)
    have : 0 < sip x.2 x.2 := lt_of_le_of_ne (sip_self_nonneg x.2)
      (fun h => h2 (sip_self_eq_zero h.symm))
    rw [h1]
    positivity
  · have : 0 < x.1 ^ 2 := by positivity
    have h3 := sip_self_nonneg x.2
    linarith

/-! ## The solder datum -/

variable {ι : Type t} {B : BaseGluingData LocalModel ι}

/-- **NEWLY DEFINED (Task 34), PRINCIPAL — the isolated coupling primitive.**  A *tangent
solder datum* for an emergent base `B` and an emergent Spin-native gluing datum `S`: a
fibrewise real-linear identification of the internal Lorentz model with the genuine tangent
space of the emergent manifold, one per piece of the emergent cover, whose failure to be
index-independent is *exactly* the projected internal Lorentz transition.

This is the datum proved additional in
`SpinNative.tangent_spin_base_data_do_not_force_transition_identification`. -/
structure TangentSolderData (B : BaseGluingData LocalModel ι)
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) where
  /-- The local solder frames: fibrewise linear equivalences of the internal Lorentz model
  with the genuine tangent space of the emergent manifold. -/
  frame : ι → ∀ x : Space B, LocalModel ≃ₗ[ℝ] TangentSpace localModelI x
  /-- **The coupling law.**  On every double overlap of the emergent cover the two solder
  frames differ exactly by the projected internal Lorentz transition. -/
  compatibility : ∀ i j, ∀ x ∈ (emergentCover B).overlap₂ i j, ∀ v : LocalModel,
    frame j x v = frame i x (projectedLorentzTransition S i j x v)

namespace TangentSolderData

variable {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)} (E : TangentSolderData B S)

/-- **DERIVED (Task 34).**  The comparison of two solder frames *is* the projected internal
Lorentz transition — this is the commuting square read as an equation between automorphisms
of the local model. -/
theorem comparison_eq (i j : ι) {x : Space B} (hx : x ∈ (emergentCover B).overlap₂ i j) :
    (E.frame j x).trans (E.frame i x).symm = projectedLorentzTransition S i j x := by
  refine LinearEquiv.ext fun v => ?_
  show (E.frame i x).symm (E.frame j x v) = _
  rw [E.compatibility i j x hx v, LinearEquiv.symm_apply_apply]

/-- **DERIVED (Task 34).**  The orientation of the commuting square is the one that composes
correctly with the Čech cocycle law: `e_k = e_j ∘ g_jk = e_i ∘ g_ij ∘ g_jk = e_i ∘ g_ik`. -/
theorem compatibility_comp (i j k : ι) {x : Space B}
    (hx : x ∈ (emergentCover B).overlap₃ i j k) (v : LocalModel) :
    E.frame k x v = E.frame i x (projectedLorentzTransition S i j x
      (projectedLorentzTransition S j k x v)) := by
  rw [projectedLorentzTransition_cocycle S i j k hx v]
  exact E.compatibility i k x ⟨((emergentCover B).overlap₃_subset_ik i j k hx).1,
    ((emergentCover B).overlap₃_subset_ik i j k hx).2⟩ v

/-- **DERIVED (Task 34).**  The regularity of the solder comparison is inherited from the
Spin cocycle: the frame comparisons are continuous on the double overlaps.  It is *not* a
field of the datum. -/
theorem continuousOn_comparison (i j : ι) :
    ContinuousOn (fun x => (E.frame j x).trans (E.frame i x).symm)
      ((emergentCover B).overlap₂ i j) :=
  (continuousOn_projectedLorentzTransition S i j).congr fun _ hx => E.comparison_eq i j hx

/-! ## The tangent identification -/

/-- The index of a piece containing a given point of the emergent base. -/
def idx (x : Space B) : ι := ((emergentCover B).covers x).choose

theorem mem_idx (x : Space B) : x ∈ (emergentCover B).U (idx (B := B) x) :=
  ((emergentCover B).covers x).choose_spec

/-- **NEWLY DEFINED (Task 34), principal.**  The solder identification of the internal
Lorentz model with the tangent space at a point: the solder frame of a piece containing the
point.  Different choices of the piece differ by a Lorentz transformation, so every
`GLor`-invariant construction made through it is well defined — see `tangentMetric`. -/
def tangentLinearEquiv (x : Space B) : LocalModel ≃ₗ[ℝ] TangentSpace localModelI x :=
  E.frame (idx (B := B) x) x

theorem tangentLinearEquiv_eq_frame {i : ι} {x : Space B}
    (hx : x ∈ (emergentCover B).U i) (v : LocalModel) :
    E.tangentLinearEquiv x v
      = E.frame i x (projectedLorentzTransition S i (idx (B := B) x) x v) :=
  E.compatibility i (idx (B := B) x) x ⟨hx, mem_idx (B := B) x⟩ v

include E in
/-- **DERIVED (Task 34).**  Every tangent space of the emergent manifold is four-dimensional,
*through the solder identification* — not through the model-space implementation of
`TangentSpace`. -/
theorem finrank_tangentSpace (x : Space B) :
    Module.finrank ℝ (TangentSpace localModelI x) = 4 := by
  rw [← (E.tangentLinearEquiv x).finrank_eq]
  exact finrank_localModel

/-! ## The tangent Lorentz metric -/

/-- **NEWLY DEFINED (Task 34), PRINCIPAL — the solder-transported Lorentz metric.**  The
intrinsic bilinear form `B_𝒮` of the Clifford core, carried to each tangent fibre through the
solder identification.  No Riemannian or pseudo-Riemannian Mathlib structure is faked: this
is the project's native fibrewise bilinear-form representation, exactly the one that
`LorentzFrames.LorentzFrameData` consumes. -/
def tangentMetric (x : Space B) :
    TangentSpace localModelI x →ₗ[ℝ] TangentSpace localModelI x →ₗ[ℝ] ℝ :=
  BSbil.compl₁₂ ((E.tangentLinearEquiv x).symm : TangentSpace localModelI x →ₗ[ℝ] LocalModel)
    ((E.tangentLinearEquiv x).symm : TangentSpace localModelI x →ₗ[ℝ] LocalModel)

theorem tangentMetric_apply (x : Space B) (u v : TangentSpace localModelI x) :
    E.tangentMetric x u v
      = BS ((E.tangentLinearEquiv x).symm u) ((E.tangentLinearEquiv x).symm v) := rfl

/-- **DERIVED (Task 34), PRINCIPAL — the metric does not depend on the chart index.**  The
transported form computed in *any* solder frame whose piece contains the point is the same,
because the overlap law makes the two frames differ by a `GLor` element and `GLor` preserves
`B_𝒮`.  This is the exact place where the Lorentz overlap law is used. -/
theorem tangentMetric_wellDefined {i : ι} {x : Space B} (hx : x ∈ (emergentCover B).U i)
    (u v : TangentSpace localModelI x) :
    E.tangentMetric x u v = BS ((E.frame i x).symm u) ((E.frame i x).symm v) := by
  set k := idx (B := B) x with hk
  have hov : x ∈ (emergentCover B).overlap₂ i k := ⟨hx, mem_idx (B := B) x⟩
  have hcomp : ∀ w : TangentSpace localModelI x,
      (E.frame i x).symm w
        = projectedLorentzTransition S i k x ((E.frame k x).symm w) := by
    intro w
    have hw := E.compatibility i k x hov ((E.frame k x).symm w)
    rw [LinearEquiv.apply_symm_apply] at hw
    conv_lhs => rw [hw]
    rw [LinearEquiv.symm_apply_apply]
  rw [hcomp u, hcomp v, projectedLorentzTransition_BS]
  rfl

/-- **DERIVED (Task 34).**  Every solder frame is a Lorentz isometry: it pulls the tangent
metric back to the intrinsic form `B_𝒮`. -/
theorem tangentMetric_frame_isometry {i : ι} {x : Space B}
    (hx : x ∈ (emergentCover B).U i) (u v : LocalModel) :
    E.tangentMetric x (E.frame i x u) (E.frame i x v) = BS u v := by
  rw [E.tangentMetric_wellDefined hx, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

/-- **DERIVED (Task 34).**  The tangent metric is nondegenerate on every fibre. -/
theorem tangentMetric_nondegenerate {x : Space B} {u : TangentSpace localModelI x}
    (hu : u ≠ 0) : ∃ v : TangentSpace localModelI x, E.tangentMetric x u v ≠ 0 := by
  have hu' : (E.tangentLinearEquiv x).symm u ≠ 0 := fun h =>
    hu (by rw [← (E.tangentLinearEquiv x).apply_symm_apply u, h, map_zero])
  obtain ⟨y, hy⟩ := BS_nondegenerate hu'
  exact ⟨E.tangentLinearEquiv x y, by
    rw [tangentMetric_apply, LinearEquiv.symm_apply_apply]; exact hy⟩

/-- **DERIVED (Task 34), packaged — the tangent fibre is a four-dimensional Lorentz space.**

1. `tangentMetric x` is a bilinear form on the genuine tangent space (it is a `LinearMap`);
2. it is nondegenerate;
3. every solder frame is an isometry onto the intrinsic form `B_𝒮`;
4. the fibre is four-dimensional;
5. the value does not depend on which piece of the emergent cover is used.

No connection, parallel transport, curvature or torsion occurs. -/
theorem tangentMetric_isLorentz :
    (∀ x : Space B, ∀ u : TangentSpace localModelI x, u ≠ 0 →
      ∃ v, E.tangentMetric x u v ≠ 0) ∧
    (∀ i, ∀ x ∈ (emergentCover B).U i, ∀ u v : LocalModel,
      E.tangentMetric x (E.frame i x u) (E.frame i x v) = BS u v) ∧
    (∀ x : Space B, Module.finrank ℝ (TangentSpace localModelI x) = 4) ∧
    (∀ i j, ∀ x ∈ (emergentCover B).overlap₂ i j, ∀ u v : TangentSpace localModelI x,
      BS ((E.frame i x).symm u) ((E.frame i x).symm v)
        = BS ((E.frame j x).symm u) ((E.frame j x).symm v)) :=
  ⟨fun _ _ hu => E.tangentMetric_nondegenerate hu,
   fun _ _ hx _ _ => E.tangentMetric_frame_isometry hx _ _,
   fun x => E.finrank_tangentSpace x,
   fun i j x hx u v => by
     rw [← E.tangentMetric_wellDefined hx.1, ← E.tangentMetric_wellDefined hx.2]⟩

/-! ## Non-vacuity: the datum is satisfiable -/

end TangentSolderData

/-- **NEWLY DEFINED (Task 34), the inhabitation witness.**  For the pointwise trivial
Spin-native gluing datum — which exists over *every* emergent base, in particular over the
negative-control base of `RequestProject.Spine.Solder.Independence` — a solder datum exists:
take every solder frame to be the model-space identification.

This is *exactly* the type-level artefact of Task 34 §4, and it is used *only* here, for the
single purpose of showing that `TangentSolderData` is not a vacuous structure (so that the
sufficiency theorems of this module and of
`RequestProject.Spine.Comparison.SolderTangentGate` are not vacuous).  It is not a proof of
any coupling statement, it is not canonical, and the coupling law it satisfies is nontrivial
only because the projected Lorentz transition of the trivial seed is the identity.

It also shows that the Task-34 negative theorem is a statement about *derivability* and not
about existence: the very base-gluing datum for which `D(φ_ij) ≠ ρ(g̃_ij)` still carries a
compatible solder field. -/
def modelSolder (B : BaseGluingData LocalModel ι) :
    TangentSolderData B (trivialCocycle (↥SpinGroup) (emergentCover B)) where
  frame _ _ := LinearEquiv.refl ℝ LocalModel
  compatibility i j x hx v := by
    rw [projectedLorentzTransition_trivial i j x]
    rfl

theorem nonempty_tangentSolderData (B : BaseGluingData LocalModel ι) :
    Nonempty (TangentSolderData B (trivialCocycle (↥SpinGroup) (emergentCover B))) :=
  ⟨modelSolder B⟩

/-- **DERIVED (Task 34).**  In particular the negative-control base — the one whose tangent
transition provably differs from its internal Lorentz transition — does carry a compatible
solder structure.  Non-derivability is therefore not non-existence. -/
theorem nonempty_tangentSolderData_rescaleGluing :
    Nonempty (TangentSolderData rescaleGluing
      (trivialCocycle (↥SpinGroup) (emergentCover rescaleGluing))) :=
  nonempty_tangentSolderData rescaleGluing

namespace TangentSolderData

variable {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)} (E : TangentSolderData B S)

/-! ## Residual gauge freedom: a solder field is not canonical -/

/-- **NEWLY DEFINED (Task 34).**  A solder datum transformed by a pointwise automorphism
field of the tangent spaces is again a solder datum for the *same* `B` and `S`: the coupling
law is insensitive to it. -/
def gauge (a : ∀ x : Space B, TangentSpace localModelI x ≃ₗ[ℝ] TangentSpace localModelI x) :
    TangentSolderData B S where
  frame i x := (E.frame i x).trans (a x)
  compatibility i j x hx v := by
    show a x (E.frame j x v) = a x (E.frame i x _)
    rw [E.compatibility i j x hx v]

/-- **DERIVED (Task 34), PRINCIPAL — the exact residual freedom.**  Any two solder data for
the same emergent base and the same Spin seed differ, over every point, by one and the same
automorphism of the tangent space — *independent of the index*.  So the compatible solder
fields form a torsor under the pointwise automorphism fields of `TM`; there is no canonical
one, and none is called canonical here. -/
theorem exists_gauge (E' : TangentSolderData B S) :
    ∃ a : ∀ x : Space B, TangentSpace localModelI x ≃ₗ[ℝ] TangentSpace localModelI x,
      ∀ i, ∀ x ∈ (emergentCover B).U i, ∀ v : LocalModel,
        E'.frame i x v = a x (E.frame i x v) := by
  refine ⟨fun x => (E.tangentLinearEquiv x).symm.trans (E'.tangentLinearEquiv x),
    fun i x hx v => ?_⟩
  have hov : x ∈ (emergentCover B).overlap₂ (idx (B := B) x) i := ⟨mem_idx (B := B) x, hx⟩
  have hE : (E.tangentLinearEquiv x).symm (E.frame i x v)
      = projectedLorentzTransition S (idx (B := B) x) i x v := by
    have h1 := E.compatibility (idx (B := B) x) i x hov v
    show (E.frame (idx (B := B) x) x).symm (E.frame i x v) = _
    rw [h1, LinearEquiv.symm_apply_apply]
  show E'.frame i x v
      = E'.tangentLinearEquiv x ((E.tangentLinearEquiv x).symm (E.frame i x v))
  rw [hE]
  exact E'.compatibility (idx (B := B) x) i x hov v

/-- **DERIVED (Task 34).**  Over an inhabited emergent base a solder datum is never unique:
rescaling every frame by `2` gives a different compatible datum.  "Canonical" is therefore
*not* claimed for any solder field. -/
theorem not_unique (i : ι) (x₀ : Space B) :
    ∃ E' : TangentSolderData B S, E' ≠ E := by
  refine ⟨E.gauge (fun x => LinearEquiv.smulOfNeZero ℝ (TangentSpace localModelI x) 2
    two_ne_zero), fun h => ?_⟩
  have hframe := congrArg
    (fun F : TangentSolderData B S => F.frame i x₀ (SpinCore.sOne : LocalModel)) h
  have h2 : (2 : ℝ) • E.frame i x₀ (SpinCore.sOne : LocalModel)
      = E.frame i x₀ (SpinCore.sOne : LocalModel) := hframe
  have h3 : ((2 : ℝ) - 1) • E.frame i x₀ (SpinCore.sOne : LocalModel) = 0 := by
    rw [sub_smul, one_smul, h2, sub_self]
  have h4 : E.frame i x₀ (SpinCore.sOne : LocalModel) = 0 := by
    have hone : ((2 : ℝ) - 1) = 1 := by norm_num
    rwa [hone, one_smul] at h3
  have h5 : (SpinCore.sOne : LocalModel) = 0 := by
    rw [← (E.frame i x₀).symm_apply_apply (SpinCore.sOne : LocalModel), h4, map_zero]
  exact one_ne_zero (congrArg Prod.fst h5)

end TangentSolderData

end SpinNative

end

/-! ## Axiom audit -/

#print axioms SpinNative.TangentSolderData
#print axioms SpinNative.TangentSolderData.tangentMetric
#print axioms SpinNative.TangentSolderData.tangentMetric_wellDefined
#print axioms SpinNative.TangentSolderData.tangentMetric_isLorentz
#print axioms SpinNative.TangentSolderData.exists_gauge
#print axioms SpinNative.TangentSolderData.not_unique
#print axioms SpinNative.nonempty_tangentSolderData
