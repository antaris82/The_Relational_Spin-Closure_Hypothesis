import RequestProject.Spine.Solder.LorentzBundle

/-!
# Spine / Solder : the *regular* (smooth) tangent solder datum

**First module of the Task-35 regularity layer.**

Task 34 isolated the weak coupling primitive `SpinNative.TangentSolderData`: a fibrewise
linear identification of the internal Lorentz model with the genuine tangent spaces of the
Task-33 emergent manifold, subject to the exact overlap law.  It carries **no** regularity
of the frames themselves, and Task 34 was explicit that nothing bundle-level or smooth could
follow from it (see `RequestProject.Spine.Solder.WeakInsufficiency` for the Task-35
theorem-level version of that remark).

This module introduces the regular object.  It is *local on the cover* and stated in the
actual chart coordinates of the Task-33 atlas, not as an abstract global field:

`SpinNative.SmoothTangentSolderData B S` consists of

* `A i : LocalModel → (LocalModel ≃L[ℝ] LocalModel)`, a **continuous linear automorphism of
  the local model for each chart coordinate** `y ∈ D i` — the comparison, read in the chart
  `i`, of the internal Lorentz fibre with the tangent space;
* `contDiffOn_A`: `y ↦ A i y` is `C^∞` on the local domain `D i`;
* `intertwine`: the exact commuting square on overlaps.

## The commuting square and its orientation

For `y ∈ W i j` and `x` the point of the emergent base with chart-`i` coordinate `y`:

```text
   internal fibre, j-coordinates  --ρ(g̃_ij)(x)-->  internal fibre, i-coordinates
              | A j (φ_ij y)                                | A i y
              v                                             v
   tangent chart j  <-------- D(φ_ij)(y) ---------  tangent chart i
```

i.e. `A j (φ_ij y) = D(φ_ij)(y) ∘ A i y ∘ ρ(g̃_ij)(x)`.

**The orientation is derived, not chosen by analogy.**  The tangent side is fixed by
`EmergentBase.BaseGluingData.tangentTransition_eq_derivative_baseTransition`: the genuine
coordinate change of `tangentBundleCore` from the chart of the piece `i` to the chart of the
piece `j`, at the point with `i`-coordinate `y`, *is* `D(φ_ij)(y)`; so `D(φ_ij)(y)` converts
`i`-components into `j`-components.  The internal side is fixed by the project's Čech
convention `e_j = e_i ∘ g_ij` (`SpinNative.TangentSolderData.compatibility`), so
`ρ(g̃_ij)(x)` converts `j`-components into `i`-components.  Reading the square from the
`j`-internal corner to the `j`-tangent corner in the two possible ways gives exactly the law
above, and `SmoothTangentSolderData.toTangentSolderData` proves that with this orientation
the regular datum forgets to a weak Task-34 datum — which is the independent check that the
convention is the right one.

## What is *derived* here

* `SmoothTangentSolderData.contDiffOn_A_symm` — smoothness of the inverse comparison
  (through `contDiffAt_map_inverse`; it is **not** an extra field);
* `SmoothTangentSolderData.localFrame` — the solder frame at a point of a chart domain, as a
  continuous linear equivalence, and `localFrame_compat`, the exact Task-34 overlap law for
  it;
* `SmoothTangentSolderData.toTangentSolderData` — the forgetful map to the weak Task-34
  datum, so that every Task-34 fibrewise consequence (the tangent Lorentz form, chart
  independence, nondegeneracy, the frame cocycle) applies verbatim to a regular solder;
* `SmoothTangentSolderData.contDiffOn_solderLorentzRep` — **a new obstruction-flavoured
  consequence**: a regular solder forces the *projected internal Lorentz transition* to have
  a `C^∞` representative in the chart coordinates, although the native Spin cocycle of
  `CechSpinLift.VisibleCocycle` is only required to be continuous.  So regular soldering is
  not a free addition: it constrains the Spin datum.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace EmergentBase

universe u t

namespace BaseGluingData

/-! ## Chart coordinates of a point of the emergent base -/

section Coord

variable {V : Type u} [TopologicalSpace V] {ι : Type t} (B : BaseGluingData V ι)

/-- The index of the piece carrying the representative that the quotient selects for a point
of the emergent base.  This is *the* index of the Task-32 chart at the point: by
`EmergentBase.BaseGluingData.chartOfPoint_eq_pieceChart` the Mathlib chart `chartAt` at `x`
is `pieceChart (outIndex x)`. -/
def outIndex (x : Space B) : ι := (Quotient.out (s := B.setoid) x).1

/-- The local coordinate of the selected representative of a point of the emergent base. -/
def outCoord (x : Space B) : V := ((Quotient.out (s := B.setoid) x).2 : V)

theorem outCoord_mem (x : Space B) : B.outCoord x ∈ B.D (B.outIndex x) :=
  (Quotient.out (s := B.setoid) x).2.2

theorem chart_outCoord (x : Space B) :
    B.chart (B.outIndex x) ⟨B.outCoord x, B.outCoord_mem x⟩ = x :=
  Quotient.out_eq (s := B.setoid) x

theorem mem_chartRange_outIndex (x : Space B) : x ∈ B.chartRange (B.outIndex x) :=
  ⟨⟨B.outCoord x, B.outCoord_mem x⟩, B.chart_outCoord x⟩

theorem outCoord_mem_W {i : ι} {x : Space B} (hx : x ∈ B.chartRange i) :
    B.outCoord x ∈ B.W (B.outIndex x) i := by
  have h := (B.mem_chartRange_inter_iff (B.outIndex x) i
    ⟨B.outCoord x, B.outCoord_mem x⟩).1
  rw [B.chart_outCoord] at h
  exact h hx

/-- **NEWLY DEFINED (Task 35).**  The coordinate of a point of the emergent base in the
chart of the piece `i`.  It is the genuine chart coordinate: on the chart domain it agrees
with `pieceChart i` (`pieceChart_eq_pieceCoord`). -/
def pieceCoord (i : ι) (x : Space B) : V := B.φ (B.outIndex x) i (B.outCoord x)

theorem pieceCoord_mem_W {i : ι} {x : Space B} (hx : x ∈ B.chartRange i) :
    B.pieceCoord i x ∈ B.W i (B.outIndex x) :=
  B.φ_mapsTo _ i (B.outCoord_mem_W hx)

theorem pieceCoord_mem_D {i : ι} {x : Space B} (hx : x ∈ B.chartRange i) :
    B.pieceCoord i x ∈ B.D i :=
  B.W_subset _ _ (B.pieceCoord_mem_W hx)

theorem chart_pieceCoord {i : ι} {x : Space B} (hx : x ∈ B.chartRange i) :
    B.chart i ⟨B.pieceCoord i x, B.pieceCoord_mem_D hx⟩ = x := by
  have h := B.chart_eq_chart_of_mem_W (B.outIndex x) i (B.outCoord_mem_W hx)
  rw [B.chart_outCoord] at h
  exact h.symm

theorem pieceCoord_outIndex (x : Space B) : B.pieceCoord (B.outIndex x) x = B.outCoord x :=
  B.φ_self _ _ (B.outCoord_mem x)

/-- **DERIVED (Task 35).**  Two chart coordinates of one and the same point are related by
the primitive identification map, on the incidence domain: the coordinate system
`pieceCoord` is the atlas of the emergent manifold. -/
theorem pieceCoord_mem_W_of_mem {i j : ι} {x : Space B} (hi : x ∈ B.chartRange i)
    (hj : x ∈ B.chartRange j) : B.pieceCoord i x ∈ B.W i j := by
  have h := (B.mem_chartRange_inter_iff i j ⟨B.pieceCoord i x, B.pieceCoord_mem_D hi⟩).1
  rw [B.chart_pieceCoord hi] at h
  exact h hj

theorem φ_pieceCoord {i j : ι} {x : Space B} (hi : x ∈ B.chartRange i)
    (hj : x ∈ B.chartRange j) : B.φ i j (B.pieceCoord i x) = B.pieceCoord j x :=
  (B.φ_cocycle (B.outIndex x) i j _ (B.outCoord_mem_W hi)
    (B.pieceCoord_mem_W_of_mem hi hj)).2

theorem pieceChart_eq_pieceCoord {i : ι} (hne : Nonempty (B.D i : Set V)) {x : Space B}
    (hx : x ∈ B.chartRange i) : B.pieceChart i hne x = B.pieceCoord i x := by
  conv_lhs => rw [← B.chart_pieceCoord hx]
  exact pieceChart_apply hne _

theorem continuousOn_pieceCoord (i : ι) (hne : Nonempty (B.D i : Set V)) :
    ContinuousOn (B.pieceCoord i) (B.chartRange i) := by
  refine ((B.pieceChart i hne).continuousOn.congr fun x hx => ?_).mono (le_of_eq ?_)
  · exact (B.pieceChart_eq_pieceCoord hne (by rwa [pieceChart_source hne] at hx)).symm
  · rw [pieceChart_source hne]

end Coord

/-! ## The chain rule for the tangent transitions -/

section Tangent

variable {ι : Type t} {B : BaseGluingData LocalModel ι}

/-- **DERIVED (Task 35).**  The tangent transitions compose along the cocycle law of the
primitive: this is the chain rule applied to `φ_jk ∘ φ_ij = φ_ik`. -/
theorem tangentTransitionMap_comp (h : B.SmoothGluing) {i j k : ι} {y : LocalModel}
    (hy : y ∈ B.W i j) (hy' : B.φ i j y ∈ B.W j k) (v : LocalModel) :
    B.tangentTransitionMap j k (B.φ i j y) (B.tangentTransitionMap i j y v)
      = B.tangentTransitionMap i k y v := by
  have hik : y ∈ B.W i k := (B.φ_cocycle i j k y hy hy').1
  have hcomp : HasFDerivAt (B.φ j k ∘ B.φ i j)
      ((B.tangentTransitionMap j k (B.φ i j y)).comp (B.tangentTransitionMap i j y)) y :=
    (hasFDerivAt_φ h hy').comp y (hasFDerivAt_φ h hy)
  have hopen : IsOpen (B.W i j ∩ B.φ i j ⁻¹' B.W j k) :=
    (B.continuousOn_φ i j).isOpen_inter_preimage (B.isOpen_W i j) (B.isOpen_W j k)
  have heq : (B.φ i k) =ᶠ[nhds y] (B.φ j k ∘ B.φ i j) := by
    filter_upwards [hopen.mem_nhds ⟨hy, hy'⟩] with z hz
    exact ((B.φ_cocycle i j k z hz.1 hz.2).2).symm
  have hik' : HasFDerivAt (B.φ i k) (B.tangentTransitionMap i k y) y := hasFDerivAt_φ h hik
  have huniq := (hcomp.congr_of_eventuallyEq heq).unique hik'
  exact congrArg (fun f : LocalModel →L[ℝ] LocalModel => f v) huniq

end Tangent

end BaseGluingData

end EmergentBase

/-! ## The regular solder datum -/

namespace SpinNative

open CechSpinLift NullSectorTask28 SpinCore EmergentBase EmergentBase.BaseGluingData

universe t

variable {ι : Type t} {B : BaseGluingData LocalModel ι}

/-- **NEWLY DEFINED (Task 35), PRINCIPAL — the regular (smooth) solder datum.**

For each piece `i` of the emergent cover, a `C^∞` family of continuous linear automorphisms
`A i y` of the local model, indexed by the chart coordinate `y ∈ D i`, comparing the
internal Lorentz fibre (in `i`-coordinates) with the tangent space (in the `i`-chart
components), subject on every overlap to the exact intertwining square between

* the internal Lorentz transition `ρ(g̃_ij)` of the native Spin seed, and
* the genuine tangent transition `D(φ_ij)` of the Task-33 atlas.

Unlike Task-34's `TangentSolderData` this datum is *local on the cover* and carries genuine
regularity; `toTangentSolderData` below is the forgetful map onto the weak notion. -/
structure SmoothTangentSolderData (B : BaseGluingData LocalModel ι)
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) where
  /-- The local comparison, in chart coordinates. -/
  A : ι → LocalModel → (LocalModel ≃L[ℝ] LocalModel)
  /-- **The regularity condition.**  The comparison is `C^∞` on the chart domain. -/
  contDiffOn_A : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
    (fun y => ((A i y : LocalModel →L[ℝ] LocalModel))) (B.D i)
  /-- **The coupling law**, in the orientation derived from the two source conventions. -/
  intertwine : ∀ (i j : ι) (y : LocalModel) (hy : y ∈ B.W i j) (v : LocalModel),
    A j (B.φ i j y) v
      = B.tangentTransitionMap i j y
          (A i y (projectedLorentzTransition S i j (B.chart i ⟨y, B.W_subset i j hy⟩) v))

namespace SmoothTangentSolderData

variable {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}
  (E : SmoothTangentSolderData B S)

/-- **DERIVED (Task 35).**  The inverse comparison is smooth as well; this is not an extra
field of the datum. -/
theorem contDiffOn_A_symm (i : ι) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => (((E.A i y).symm : LocalModel →L[ℝ] LocalModel))) (B.D i) := by
  intro y hy
  have hA : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y => ((E.A i y : LocalModel →L[ℝ] LocalModel))) y :=
    (E.contDiffOn_A i).contDiffAt ((B.isOpen_D i).mem_nhds hy)
  have hinv : ContDiffAt ℝ (⊤ : ℕ∞)
      (ContinuousLinearMap.inverse : (LocalModel →L[ℝ] LocalModel) →
        (LocalModel →L[ℝ] LocalModel)) ((E.A i y : LocalModel →L[ℝ] LocalModel)) :=
    contDiffAt_map_inverse (E.A i y)
  have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z => ContinuousLinearMap.inverse ((E.A i z : LocalModel →L[ℝ] LocalModel))) y :=
    ContDiffAt.comp (g := ContinuousLinearMap.inverse)
      (f := fun z => ((E.A i z : LocalModel →L[ℝ] LocalModel))) y hinv hA
  refine (hcomp.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards with z
  exact (ContinuousLinearMap.inverse_equiv (E.A i z)).symm

/-! ### The solder frames -/

/-- **NEWLY DEFINED (Task 35).**  The solder frame of the piece `i` at a point of its chart
domain: the local comparison `A i` followed by the genuine tangent coordinate change from
the chart of the piece `i` to the chart that Mathlib attaches to the point. -/
def localFrame (h : B.SmoothGluing) (i : ι) {x : Space B} (hx : x ∈ B.chartRange i) :
    LocalModel ≃L[ℝ] LocalModel :=
  (E.A i (B.pieceCoord i x)).trans
    (BaseGluingData.tangentTransition h i (B.outIndex x) (B.pieceCoord_mem_W hx))

@[simp] theorem localFrame_apply (h : B.SmoothGluing) (i : ι) {x : Space B}
    (hx : x ∈ B.chartRange i) (v : LocalModel) :
    E.localFrame h i hx v
      = B.tangentTransitionMap i (B.outIndex x) (B.pieceCoord i x) (E.A i (B.pieceCoord i x) v) :=
  rfl

/-- **DERIVED (Task 35), PRINCIPAL — the regular frames satisfy the Task-34 overlap law.**
On a double overlap the two solder frames differ exactly by the projected internal Lorentz
transition.  Nothing is assumed about the frames beyond the intertwining law of the datum:
this is the chain rule for `D(φ)` together with the cocycle law of the primitive. -/
theorem localFrame_compat (h : B.SmoothGluing) (i j : ι) {x : Space B}
    (hi : x ∈ B.chartRange i) (hj : x ∈ B.chartRange j) (v : LocalModel) :
    E.localFrame h j hj v = E.localFrame h i hi (projectedLorentzTransition S i j x v) := by
  have hij : B.pieceCoord i x ∈ B.W i j := B.pieceCoord_mem_W_of_mem hi hj
  have hφ : B.φ i j (B.pieceCoord i x) = B.pieceCoord j x := B.φ_pieceCoord hi hj
  have hpt : B.chart i ⟨B.pieceCoord i x, B.W_subset i j hij⟩ = x := B.chart_pieceCoord hi
  have hjk : B.φ i j (B.pieceCoord i x) ∈ B.W j (B.outIndex x) := by
    rw [hφ]; exact B.pieceCoord_mem_W hj
  have hA : E.A j (B.pieceCoord j x) v
      = B.tangentTransitionMap i j (B.pieceCoord i x)
          (E.A i (B.pieceCoord i x) (projectedLorentzTransition S i j x v)) := by
    have := E.intertwine i j (B.pieceCoord i x) hij v
    rw [hφ, hpt] at this
    exact this
  rw [localFrame_apply, localFrame_apply, hA]
  have hcomp := BaseGluingData.tangentTransitionMap_comp h hij hjk
    (E.A i (B.pieceCoord i x) (projectedLorentzTransition S i j x v))
  rw [hφ] at hcomp
  exact hcomp

/-! ### The forgetful map to the Task-34 weak datum -/

open Classical in
/-- The weak Task-34 frame attached to a regular solder: the `localFrame` on the chart
domain of the piece, and an irrelevant identity off it (the Task-34 law never sees the
off-patch values). -/
def weakFrame (h : B.SmoothGluing) (i : ι) (x : Space B) :
    LocalModel ≃ₗ[ℝ] TangentSpace localModelI x :=
  if hx : x ∈ B.chartRange i then ((E.localFrame h i hx).toLinearEquiv) else
    LinearEquiv.refl ℝ LocalModel

theorem weakFrame_of_mem (h : B.SmoothGluing) (i : ι) {x : Space B}
    (hx : x ∈ B.chartRange i) (v : LocalModel) :
    E.weakFrame h i x v = E.localFrame h i hx v := by
  have hdite : E.weakFrame h i x = (E.localFrame h i hx).toLinearEquiv := dif_pos hx
  rw [hdite]
  rfl

/-- **NEWLY DEFINED (Task 35).**  Every regular solder datum is in particular a weak Task-34
solder datum: the frames are the `localFrame`s on their own chart domains (and an irrelevant
identity off patch, which the Task-34 law never sees).  Consequently all Task-34 fibrewise
consequences — the transported Lorentz form, its chart independence, nondegeneracy, the
frame isometry and the frame cocycle — hold verbatim for a regular solder. -/
def toTangentSolderData (h : B.SmoothGluing) : TangentSolderData B S where
  frame := E.weakFrame h
  compatibility i j x hx v := by
    rw [E.weakFrame_of_mem h j hx.2, E.weakFrame_of_mem h i hx.1]
    exact E.localFrame_compat h i j hx.1 hx.2 v

theorem toTangentSolderData_frame (h : B.SmoothGluing) (i : ι) {x : Space B}
    (hx : x ∈ B.chartRange i) (v : LocalModel) :
    (E.toTangentSolderData h).frame i x v = E.localFrame h i hx v :=
  E.weakFrame_of_mem h i hx v

/-- **DERIVED (Task 35).**  The exact relation between the two chart comparisons: pulling a
tangent vector back through the comparison of the chart `j`, after the genuine tangent
transition, is the projected internal Lorentz transition applied to its pull-back through
the comparison of the chart `i`.  This is the intertwining law solved for the inverse
comparisons, and it is what makes every `GLor`-invariant construction chart-independent. -/
theorem frameChange_symm (i j : ι) {y : LocalModel} (hy : y ∈ B.W i j) (w : LocalModel) :
    (E.A j (B.φ i j y)).symm (B.tangentTransitionMap i j y w)
      = projectedLorentzTransition S j i (B.chart i ⟨y, B.W_subset i j hy⟩)
          ((E.A i y).symm w) := by
  have hxi : B.chart i ⟨y, B.W_subset i j hy⟩ ∈ B.chartRange i := ⟨_, rfl⟩
  have hxj : B.chart i ⟨y, B.W_subset i j hy⟩ ∈ B.chartRange j := by
    rw [B.chart_eq_chart_of_mem_W i j hy]
    exact ⟨_, rfl⟩
  have hsymm := projectedLorentzTransition_symm S j i ⟨hxj, hxi⟩ ((E.A i y).symm w)
  have hlaw := E.intertwine i j y hy
    (projectedLorentzTransition S j i (B.chart i ⟨y, B.W_subset i j hy⟩) ((E.A i y).symm w))
  rw [hsymm, ContinuousLinearEquiv.apply_symm_apply] at hlaw
  rw [← hlaw, ContinuousLinearEquiv.symm_apply_apply]

/-! ### Regular soldering constrains the Spin datum -/

/-- **NEWLY DEFINED (Task 35).**  The representative, in the chart coordinates of the piece
`i`, of the projected internal Lorentz transition *as computed from a regular solder*:
`A i y⁻¹ ∘ D(φ_ji)(φ_ij y) ∘ A j (φ_ij y)`.  It is a totally defined, manifestly smooth
expression; `solderLorentzRep_eq` identifies it with `ρ(g̃_ij)` on the incidence domain. -/
def solderLorentzRep (i j : ι) (y : LocalModel) : LocalModel →L[ℝ] LocalModel :=
  ((E.A i y).symm : LocalModel →L[ℝ] LocalModel).comp
    ((B.tangentTransitionMap j i (B.φ i j y)).comp
      ((E.A j (B.φ i j y) : LocalModel →L[ℝ] LocalModel)))

/-- **DERIVED (Task 35).**  On the incidence domain the solder representative *is* the
projected internal Lorentz transition. -/
theorem solderLorentzRep_eq (h : B.SmoothGluing) (i j : ι) {y : LocalModel}
    (hy : y ∈ B.W i j) (v : LocalModel) :
    E.solderLorentzRep i j y v
      = projectedLorentzTransition S i j (B.chart i ⟨y, B.W_subset i j hy⟩) v := by
  have hA : E.A j (B.φ i j y) v
      = B.tangentTransitionMap i j y
          (E.A i y (projectedLorentzTransition S i j
            (B.chart i ⟨y, B.W_subset i j hy⟩) v)) := E.intertwine i j y hy v
  show ((E.A i y).symm : LocalModel →L[ℝ] LocalModel)
      ((B.tangentTransitionMap j i (B.φ i j y))
        ((E.A j (B.φ i j y) : LocalModel →L[ℝ] LocalModel) v)) = _
  show ((E.A i y).symm : LocalModel →L[ℝ] LocalModel)
      ((B.tangentTransitionMap j i (B.φ i j y)) (E.A j (B.φ i j y) v)) = _
  rw [hA, BaseGluingData.tangentTransitionMap_left_inv h hy]
  exact (E.A i y).symm_apply_apply _

/-- **DERIVED (Task 35), PRINCIPAL — a regular solder forces the native Spin cocycle to be
smooth in the chart coordinates.**  The native transition datum
`CechSpinLift.VisibleCocycle` requires only *continuity* of the Spin cocycle; but if the
internal Lorentz fibre is regularly soldered to the tangent bundle then the projected
Lorentz transition necessarily has a `C^∞` representative in the actual chart coordinates.

Regular soldering is therefore **not** a free addition on top of the Task-34 data: it
constrains the Spin seed. -/
theorem contDiffOn_solderLorentzRep (h : B.SmoothGluing) (i j : ι) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => E.solderLorentzRep i j y) (B.W i j) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => ((E.A i y).symm : LocalModel →L[ℝ] LocalModel)) (B.W i j) :=
    (E.contDiffOn_A_symm i).mono (B.W_subset i j)
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (B.φ i j) (B.W i j) := h i j
  have hmaps : Set.MapsTo (B.φ i j) (B.W i j) (B.W j i) := B.φ_mapsTo i j
  have hd : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => fderivWithin ℝ (B.φ j i) (B.W j i) z) (B.W j i) :=
    (h j i).fderivWithin ((B.isOpen_W j i).uniqueDiffOn) (le_of_eq ENat.coe_top_add_one)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => B.tangentTransitionMap j i (B.φ i j y)) (B.W i j) := hd.comp hφ hmaps
  have h3 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => ((E.A j (B.φ i j y) : LocalModel →L[ℝ] LocalModel))) (B.W i j) :=
    (E.contDiffOn_A j).comp hφ (hmaps.mono_right (B.W_subset j i))
  exact h1.clm_comp (h2.clm_comp h3)

end SmoothTangentSolderData

end SpinNative

end

/-! ## Axiom audit -/

#print axioms SpinNative.SmoothTangentSolderData
#print axioms SpinNative.SmoothTangentSolderData.contDiffOn_A_symm
#print axioms SpinNative.SmoothTangentSolderData.localFrame_compat
#print axioms SpinNative.SmoothTangentSolderData.toTangentSolderData
#print axioms SpinNative.SmoothTangentSolderData.solderLorentzRep_eq
#print axioms SpinNative.SmoothTangentSolderData.contDiffOn_solderLorentzRep
#print axioms EmergentBase.BaseGluingData.tangentTransitionMap_comp
