import RequestProject.Spine.Solder.RegularSolder

/-!
# Spine / Solder : regular soldering **is** a bundle equivalence with the tangent bundle

**Third module of the Task-35 regularity layer, and its principal theorem.**

Task 34 stopped at a *fibrewise* statement: a weak solder datum gives a linear equivalence of
each internal Lorentz fibre with the corresponding tangent space, and intertwines the two
transition systems, but nothing was said about the total spaces, because nothing could be
(the weak datum has no regularity).

Here the regular datum of `RequestProject.Spine.Solder.RegularSolder` is shown to produce a
genuine **topological vector-bundle equivalence**

`InternalLorentzBundle(S)  ≃  TM`

covering the identity of the emergent base, with smooth local coordinate representatives.

## The Mathlib situation (see `TASK35_AUDIT.md`)

The pinned Mathlib (`v4.28.0`) has `VectorBundleCore`, `tangentBundleCore`, `Trivialization`,
`Bundle.TotalSpace`, the `ContMDiffVectorBundle` class and the `VectorBundleCore.IsContMDiff`
mixin — but **no** type of vector-bundle morphisms or equivalences.  A project-native
certificate is therefore defined here, with its local-coordinate content stated explicitly:

`SolderBundle.CoreBundleEquiv Z₁ Z₂` — a fibrewise continuous linear equivalence
`L : X → (F ≃L[ℝ] F)` whose induced total-space maps, in both directions, are continuous.
From it one gets `CoreBundleEquiv.toHomeomorph`, a homeomorphism of total spaces covering the
identity of the base and linear on every fibre; `SolderBundle.coreRep` is its local
representative in a pair of `localTriv` trivializations, and `continuous_coreTotalMap` is the
general criterion: continuity of the local representatives implies continuity of the total
map.

## The principal theorem

`SpinNative.SmoothTangentSolderData.toCoreBundleEquiv` builds, from a regular solder datum,
such an equivalence between `SpinNative.internalLorentzBundleCore S` and Mathlib's own
`tangentBundleCore` of the Task-33 emergent manifold, and

* `SpinNative.SmoothTangentSolderData.coreRep_eq` — **the exact local coordinate content**:
  the local representative of the equivalence in the trivializations attached to the piece
  `i` is *exactly* `A i`, the local comparison of the solder datum, so it is `C^∞`;
* `SpinNative.SmoothTangentSolderData.coreRep_inv_eq` — and the inverse representative is
  `A i⁻¹`;
* `SpinNative.smooth_solder_iff_regular_bundle_equivalence` — the **equivalence of the two
  notions**: a regular solder datum exists if and only if there is a fibrewise linear
  equivalence of the two bundles, continuous in both directions on the total spaces, whose
  local representatives in the actual chart trivializations are `C^∞`.

## Exact regularity status (Task 35 §6, §9)

The equivalence proved here is **topological** (a total-space homeomorphism, fibrewise
linear, covering `id`) **with smooth local representatives**.  It is *not* claimed to be a
morphism of *smooth* vector bundles, and it cannot be: the internal Lorentz bundle is built
from the native Spin cocycle, which `CechSpinLift.VisibleCocycle` only requires to be
**continuous**, so `SpinNative.internalLorentzBundleCore S` does not satisfy Mathlib's
`VectorBundleCore.IsContMDiff` mixin in general.  What *is* proved, in
`RequestProject.Spine.Solder.RegularSolder`, is the converse constraint: a regular solder
forces the projected Lorentz transition to have a `C^∞` representative in the chart
coordinates.  See `TASK35_PROVENANCE.md` for the classification.

## CORRECTION NOTICE (Task 36 §1) — the paragraph above is too strong

The Task-35 wording immediately above is **preserved for provenance but is an
overstatement**, and the following supersedes it.

The sentence "it cannot be [a morphism of smooth vector bundles]: the internal Lorentz
bundle is built from the native Spin cocycle, which ... only requires [it] to be
continuous" conflates two different things:

* **internal Lorentz bundle smoothness** — the smoothness of the *projected* Lorentz
  transition representatives.  Task 35 already proves this, through
  `SpinNative.SmoothTangentSolderData.contDiffOn_solderLorentzRep`: whenever a regular
  solder exists the coordinate changes of the internal Lorentz bundle *do* have `C^∞`
  representatives in the chart coordinates.  So the smoothness of the *bundle* data is not
  obstructed by the Spin cocycle at all.
* **smooth Spin bundle structure** — smoothness of the native Spin *lift* itself.  That is a
  genuinely separate question, and it is not needed for a smooth equivalence of the internal
  **Lorentz** bundle with `TM`.

What actually blocks the packaging is **infrastructure, not mathematics**: the pinned
Mathlib `v4.28.0` has no type of (smooth) vector-bundle morphisms or equivalences, and
`VectorBundleCore.IsContMDiff` is stated for the coordinate changes as functions on the
base *manifold*, whereas the project's smooth representatives are functions of the *chart
coordinate*.  The honest classification is therefore

```text
    smooth total-space packaging: BLOCKED BY INFRASTRUCTURE
```

and **not** "smooth total-space equivalence requires smooth native Spin transitions".

The strongest correct statement available in this project is proved in
`RequestProject.Spine.Task36.SmoothBundlePackaging`:
`Task36.RegularBundleCertificate` packages, explicitly and without any assumption on the
smoothness of the Spin lift, (i) a continuous total-space equivalence, (ii) a continuous
inverse, (iii) fibrewise linearity, (iv) smooth local representatives, (v) smooth local
representatives of the inverse and (vi) the exact transition intertwining; and
`Task36.nonempty_regularBundleCertificate_iff` shows it exists exactly when a regular solder
does.  The smoothness of the internal coordinate changes in charts is
`Task36.internal_bundle_coordChange_smooth_in_charts`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

open Bundle

/-! ## A project-native notion of bundle equivalence -/

namespace SolderBundle

variable {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι₁ ι₂ : Type*}

/-- **NEWLY DEFINED (Task 35).**  The total-space map induced by a fibrewise linear
equivalence between two vector bundle cores over the same base with the same model fibre.
It covers the identity of the base by construction. -/
def coreTotalMap (Z₁ : VectorBundleCore ℝ X F ι₁) (Z₂ : VectorBundleCore ℝ X F ι₂)
    (L : X → (F ≃L[ℝ] F)) (p : Z₁.TotalSpace) : Z₂.TotalSpace := ⟨p.proj, L p.proj p.snd⟩

@[simp] theorem proj_coreTotalMap (Z₁ : VectorBundleCore ℝ X F ι₁)
    (Z₂ : VectorBundleCore ℝ X F ι₂) (L : X → (F ≃L[ℝ] F)) (p : Z₁.TotalSpace) :
    (coreTotalMap Z₁ Z₂ L p).proj = p.proj := rfl

/-- **NEWLY DEFINED (Task 35).**  The local representative of a fibrewise linear map in the
`localTriv i` trivialization of the source and the `localTriv j` trivialization of the
target: this is the object whose regularity is the real content of "bundle morphism". -/
def coreRep (Z₁ : VectorBundleCore ℝ X F ι₁) (Z₂ : VectorBundleCore ℝ X F ι₂)
    (L : X → (F ≃L[ℝ] F)) (i : ι₁) (j : ι₂) (x : X) : F →L[ℝ] F :=
  (Z₂.coordChange (Z₂.indexAt x) j x).comp
    ((L x : F →L[ℝ] F).comp (Z₁.coordChange i (Z₁.indexAt x) x))

variable {Z₁ : VectorBundleCore ℝ X F ι₁} {Z₂ : VectorBundleCore ℝ X F ι₂}

/-- **DERIVED (Task 35).**  On the overlap of the two trivialization domains the total map is
the local representative read through the trivializations. -/
theorem coreTotalMap_eq (L : X → (F ≃L[ℝ] F)) (i : ι₁) (j : ι₂) (p : Z₁.TotalSpace)
    (hi : p.proj ∈ Z₁.baseSet i) (hj : p.proj ∈ Z₂.baseSet j) :
    coreTotalMap Z₁ Z₂ L p
      = TotalSpace.mk' F p.proj
          ((Z₂.localTriv j).symm p.proj (coreRep Z₁ Z₂ L i j p.proj ((Z₁.localTriv i p).2))) := by
  have h1 : (Z₁.localTriv i p).2 = Z₁.coordChange (Z₁.indexAt p.proj) i p.proj p.snd := by
    rw [Z₁.localTriv_apply]
  have h2 : Z₁.coordChange i (Z₁.indexAt p.proj) p.proj
      (Z₁.coordChange (Z₁.indexAt p.proj) i p.proj p.snd) = p.snd := by
    rw [Z₁.coordChange_comp (Z₁.indexAt p.proj) i (Z₁.indexAt p.proj) p.proj
      ⟨⟨Z₁.mem_baseSet_at p.proj, hi⟩, Z₁.mem_baseSet_at p.proj⟩,
      Z₁.coordChange_self _ p.proj (Z₁.mem_baseSet_at p.proj)]
  have h3 : (Z₂.localTriv j).symm p.proj
      (Z₂.coordChange (Z₂.indexAt p.proj) j p.proj (L p.proj p.snd))
      = L p.proj p.snd := by
    rw [Z₂.localTriv_symm_apply j hj,
      Z₂.coordChange_comp (Z₂.indexAt p.proj) j (Z₂.indexAt p.proj) p.proj
        ⟨⟨Z₂.mem_baseSet_at p.proj, hj⟩, Z₂.mem_baseSet_at p.proj⟩,
      Z₂.coordChange_self _ p.proj (Z₂.mem_baseSet_at p.proj)]
  show (⟨p.proj, L p.proj p.snd⟩ : Z₂.TotalSpace) = _
  rw [h1]
  show _ = TotalSpace.mk' F p.proj ((Z₂.localTriv j).symm p.proj
      (Z₂.coordChange (Z₂.indexAt p.proj) j p.proj (L p.proj
        (Z₁.coordChange i (Z₁.indexAt p.proj) p.proj
          (Z₁.coordChange (Z₁.indexAt p.proj) i p.proj p.snd)))))
  rw [h2, h3]

/-- **DERIVED (Task 35).**  The representatives of a fibrewise equivalence and of its
fibrewise inverse are mutually inverse. -/
theorem coreRep_symm_comp (L : X → (F ≃L[ℝ] F)) (i : ι₁) (j : ι₂) {x : X}
    (hi : x ∈ Z₁.baseSet i) (hj : x ∈ Z₂.baseSet j) (v : F) :
    coreRep Z₂ Z₁ (fun y => (L y).symm) j i x (coreRep Z₁ Z₂ L i j x v) = v := by
  show Z₁.coordChange (Z₁.indexAt x) i x ((L x).symm
      (Z₂.coordChange j (Z₂.indexAt x) x (Z₂.coordChange (Z₂.indexAt x) j x
        (L x (Z₁.coordChange i (Z₁.indexAt x) x v))))) = v
  rw [Z₂.coordChange_comp (Z₂.indexAt x) j (Z₂.indexAt x) x
      ⟨⟨Z₂.mem_baseSet_at x, hj⟩, Z₂.mem_baseSet_at x⟩,
    Z₂.coordChange_self _ x (Z₂.mem_baseSet_at x),
    ContinuousLinearEquiv.symm_apply_apply,
    Z₁.coordChange_comp i (Z₁.indexAt x) i x ⟨⟨hi, Z₁.mem_baseSet_at x⟩, hi⟩,
    Z₁.coordChange_self _ x hi]

/-- **DERIVED (Task 35).**  Continuity of the local representative over one pair of
trivialization domains gives continuity of the total map there. -/
theorem continuousOn_coreTotalMap (L : X → (F ≃L[ℝ] F)) (i : ι₁) (j : ι₂)
    (hrep : ContinuousOn (coreRep Z₁ Z₂ L i j) (Z₁.baseSet i ∩ Z₂.baseSet j)) :
    ContinuousOn (coreTotalMap Z₁ Z₂ L)
      {p : Z₁.TotalSpace | p.proj ∈ Z₁.baseSet i ∩ Z₂.baseSet j} := by
  set U : Set Z₁.TotalSpace := {p : Z₁.TotalSpace | p.proj ∈ Z₁.baseSet i ∩ Z₂.baseSet j}
    with hU
  have hproj : Continuous (fun p : Z₁.TotalSpace => p.proj) :=
    Z₁.toFiberBundleCore.continuous_proj
  have hsrc : U ⊆ (Z₁.localTriv i).source := fun p hp => (Z₁.mem_localTriv_source i p).2 hp.1
  have htriv : ContinuousOn (fun p : Z₁.TotalSpace => ((Z₁.localTriv i) p).2) U :=
    continuous_snd.comp_continuousOn ((Z₁.localTriv i).continuousOn.mono hsrc)
  have hrep' : ContinuousOn (fun p : Z₁.TotalSpace => coreRep Z₁ Z₂ L i j p.proj) U :=
    hrep.comp hproj.continuousOn (fun p hp => hp)
  have hinner : ContinuousOn
      (fun p : Z₁.TotalSpace =>
        (p.proj, coreRep Z₁ Z₂ L i j p.proj ((Z₁.localTriv i p).2))) U :=
    hproj.continuousOn.prodMk
      (isBoundedBilinearMap_apply.continuous.comp_continuousOn (hrep'.prodMk htriv))
  have hsymm : ContinuousOn
      (fun z : X × F => TotalSpace.mk' F z.1 ((Z₂.localTriv j).symm z.1 z.2))
      ((Z₂.localTriv j).baseSet ×ˢ (Set.univ : Set F)) := (Z₂.localTriv j).continuousOn_symm
  have hmaps : Set.MapsTo
      (fun p : Z₁.TotalSpace => (p.proj, coreRep Z₁ Z₂ L i j p.proj ((Z₁.localTriv i p).2))) U
      ((Z₂.localTriv j).baseSet ×ˢ (Set.univ : Set F)) := fun p hp => ⟨hp.2, Set.mem_univ _⟩
  exact (hsymm.comp hinner hmaps).congr fun p hp => coreTotalMap_eq L i j p hp.1 hp.2

/-- **DERIVED (Task 35), the general continuity criterion.**  If every point of the base
admits a pair of trivializations in which the local representative is continuous, the total
map is continuous. -/
theorem continuous_coreTotalMap (L : X → (F ≃L[ℝ] F))
    (hcov : ∀ x : X, ∃ (i : ι₁) (j : ι₂), x ∈ Z₁.baseSet i ∧ x ∈ Z₂.baseSet j ∧
      ContinuousOn (coreRep Z₁ Z₂ L i j) (Z₁.baseSet i ∩ Z₂.baseSet j)) :
    Continuous (coreTotalMap Z₁ Z₂ L) := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨i, j, hi, hj, hrep⟩ := hcov p.proj
  have hproj : Continuous (fun q : Z₁.TotalSpace => q.proj) :=
    Z₁.toFiberBundleCore.continuous_proj
  have hopen : IsOpen {q : Z₁.TotalSpace | q.proj ∈ Z₁.baseSet i ∩ Z₂.baseSet j} :=
    ((Z₁.isOpen_baseSet i).inter (Z₂.isOpen_baseSet j)).preimage hproj
  exact (continuousOn_coreTotalMap L i j hrep).continuousAt (hopen.mem_nhds ⟨hi, hj⟩)

/-- **NEWLY DEFINED (Task 35), the project-native bundle-equivalence certificate.**  A
fibrewise continuous linear equivalence of two vector bundle cores over the same base whose
induced total-space maps are continuous in both directions.  It is *not* a mere fibrewise
family: `toHomeomorph` below is a genuine homeomorphism of total spaces covering the
identity of the base. -/
structure CoreBundleEquiv (Z₁ : VectorBundleCore ℝ X F ι₁)
    (Z₂ : VectorBundleCore ℝ X F ι₂) where
  /-- The fibrewise linear equivalence. -/
  L : X → (F ≃L[ℝ] F)
  /-- The induced total-space map is continuous. -/
  continuous_toTotal : Continuous (coreTotalMap Z₁ Z₂ L)
  /-- The induced inverse total-space map is continuous. -/
  continuous_invTotal : Continuous (coreTotalMap Z₂ Z₁ fun x => (L x).symm)

namespace CoreBundleEquiv

variable (e : CoreBundleEquiv Z₁ Z₂)

/-- **DERIVED (Task 35), PRINCIPAL — the total spaces are homeomorphic.** -/
def toHomeomorph : Z₁.TotalSpace ≃ₜ Z₂.TotalSpace where
  toFun := coreTotalMap Z₁ Z₂ e.L
  invFun := coreTotalMap Z₂ Z₁ fun x => (e.L x).symm
  left_inv p := by
    obtain ⟨x, v⟩ := p
    show (⟨x, (e.L x).symm (e.L x v)⟩ : Z₁.TotalSpace) = ⟨x, v⟩
    rw [ContinuousLinearEquiv.symm_apply_apply]
  right_inv p := by
    obtain ⟨x, v⟩ := p
    show (⟨x, (e.L x) ((e.L x).symm v)⟩ : Z₂.TotalSpace) = ⟨x, v⟩
    rw [ContinuousLinearEquiv.apply_symm_apply]
  continuous_toFun := e.continuous_toTotal
  continuous_invFun := e.continuous_invTotal

/-- **DERIVED (Task 35).**  The equivalence covers the identity of the base. -/
theorem toHomeomorph_proj (p : Z₁.TotalSpace) : (e.toHomeomorph p).proj = p.proj := rfl

/-- **DERIVED (Task 35).**  The equivalence is linear on every fibre — it *is* `e.L x`
there. -/
theorem toHomeomorph_apply (x : X) (v : F) :
    e.toHomeomorph ⟨x, v⟩ = (⟨x, e.L x v⟩ : Z₂.TotalSpace) := rfl

end CoreBundleEquiv

end SolderBundle

/-! ## The solder equivalence of the internal Lorentz bundle with the tangent bundle -/

namespace SpinNative

open CechSpinLift NullSectorTask28 SpinCore EmergentBase EmergentBase.BaseGluingData
open SolderBundle

universe t

variable {ι : Type t} {B : BaseGluingData LocalModel ι}

/-- **EXPOSED (Task 35).**  Mathlib's own tangent bundle core of the Task-33 emergent smooth
manifold.  No new tangent bundle is introduced: this is literally
`tangentBundleCore localModelI (Space B)`, with the `IsManifold` instance supplied by the
Task-33 smooth gate (the instance is a `Prop`, hence unique). -/
def tangentCore (h : B.SmoothGluing) :
    VectorBundleCore ℝ (Space B) LocalModel (atlas LocalModel (Space B)) :=
  haveI : IsManifold localModelI 1 (Space B) :=
    (isManifold_of_smoothGluing h).of_le (by exact_mod_cast le_top)
  tangentBundleCore localModelI (Space B)

theorem tangentCore_baseSet (h : B.SmoothGluing) (e : atlas LocalModel (Space B)) :
    (tangentCore h).baseSet e = e.1.source := rfl

namespace SmoothTangentSolderData

variable {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}
  (E : SmoothTangentSolderData B S)

/-- **NEWLY DEFINED (Task 35).**  The fibrewise equivalence attached to a regular solder: the
solder frame of the piece that the internal bundle's index function selects.  Its source is
the internal Lorentz fibre in its own canonical coordinates, its target is the tangent fibre
in the canonical coordinates of Mathlib's tangent bundle. -/
def fiberEquiv (h : B.SmoothGluing) (x : Space B) : LocalModel ≃L[ℝ] LocalModel :=
  E.localFrame h (coverIndex B x) (mem_coverIndex x)

/-- The atlas membership of the chart of the piece selected at a point: it is the Mathlib
chart at that point. -/
theorem pieceChart_outIndex_mem_atlas (x : Space B) :
    B.pieceChart (B.outIndex x) ⟨(Quotient.out (s := B.setoid) x).2⟩
      ∈ atlas LocalModel (Space B) := ⟨x, rfl⟩

/-- **DERIVED (Task 35), PRINCIPAL — the local representative of the solder equivalence is
the solder comparison itself.**  In the trivialization of the internal Lorentz bundle over
the piece `i` and the trivialization of the tangent bundle attached to the chart of the same
piece, the local representative of the fibrewise solder equivalence is exactly `A i`, read at
the chart coordinate of the point.  In particular it is `C^∞`. -/
theorem coreRep_eq (h : B.SmoothGluing) (i : ι) (hi : Nonempty (B.D i : Set LocalModel))
    (mi : B.pieceChart i hi ∈ atlas LocalModel (Space B)) {x : Space B}
    (hx : x ∈ B.chartRange i) (v : LocalModel) :
    coreRep (internalLorentzBundleCore S) (tangentCore h) (E.fiberEquiv h) i
        ⟨B.pieceChart i hi, mi⟩ x v
      = E.A i (B.pieceCoord i x) v := by
  haveI : IsManifold localModelI 1 (Space B) :=
    (isManifold_of_smoothGluing h).of_le (by exact_mod_cast le_top)
  set c := coverIndex B x with hc
  set k := B.outIndex x with hk
  have hxc : x ∈ B.chartRange c := mem_coverIndex x
  have hxk : x ∈ B.chartRange k := B.mem_chartRange_outIndex x
  -- the internal coordinate change
  have hint : (internalLorentzBundleCore S).coordChange i
      ((internalLorentzBundleCore S).indexAt x) x v
      = projectedLorentzTransition S c i x v := rfl
  -- the tangent coordinate change from the Mathlib chart at `x` to the chart of the piece `i`
  have hidx : (tangentCore h).indexAt x
      = ⟨B.pieceChart k ⟨(Quotient.out (s := B.setoid) x).2⟩,
          pieceChart_outIndex_mem_atlas x⟩ := by
    apply Subtype.ext
    rfl
  have htan : ∀ w : LocalModel, (tangentCore h).coordChange ((tangentCore h).indexAt x)
      ⟨B.pieceChart i hi, mi⟩ x w
      = B.tangentTransitionMap k i (B.outCoord x) w := by
    intro w
    rw [hidx]
    have hy : B.outCoord x ∈ B.W k i := B.outCoord_mem_W hx
    have hpt : B.chart k ⟨B.outCoord x, B.W_subset k i hy⟩ = x := B.chart_outCoord x
    have := BaseGluingData.tangentTransition_eq_derivative_baseTransition B h
      (i := k) (j := i) ⟨(Quotient.out (s := B.setoid) x).2⟩ hi
      (pieceChart_outIndex_mem_atlas x) mi hy
    rw [hpt] at this
    rw [show (tangentCore h) = tangentBundleCore localModelI (Space B) from rfl, this]
  -- the fibrewise map
  have hfib : ∀ u : LocalModel, E.fiberEquiv h x u
      = B.tangentTransitionMap c k (B.pieceCoord c x) (E.A c (B.pieceCoord c x) u) := fun _ => rfl
  -- put the three together
  show (tangentCore h).coordChange ((tangentCore h).indexAt x) ⟨B.pieceChart i hi, mi⟩ x
      (E.fiberEquiv h x ((internalLorentzBundleCore S).coordChange i
        ((internalLorentzBundleCore S).indexAt x) x v)) = _
  rw [hint, hfib, htan]
  -- chain rule: D(φ_{k,i}) ∘ D(φ_{c,k}) = D(φ_{c,i})
  have hck : B.pieceCoord c x ∈ B.W c k := B.pieceCoord_mem_W_of_mem hxc hxk
  have hφck : B.φ c k (B.pieceCoord c x) = B.outCoord x := by
    rw [B.φ_pieceCoord hxc hxk, B.pieceCoord_outIndex]
  have hki : B.φ c k (B.pieceCoord c x) ∈ B.W k i := by
    rw [hφck]; exact B.outCoord_mem_W hx
  have hcomp := BaseGluingData.tangentTransitionMap_comp h hck hki
    (E.A c (B.pieceCoord c x) (projectedLorentzTransition S c i x v))
  rw [hφck] at hcomp
  rw [hcomp]
  -- and the intertwining law of the datum
  have hci : B.pieceCoord c x ∈ B.W c i := B.pieceCoord_mem_W_of_mem hxc hx
  have hpt : B.chart c ⟨B.pieceCoord c x, B.W_subset c i hci⟩ = x := B.chart_pieceCoord hxc
  have hlaw := E.intertwine c i (B.pieceCoord c x) hci v
  rw [hpt, B.φ_pieceCoord hxc hx] at hlaw
  exact hlaw.symm

/-- **DERIVED (Task 35).**  The inverse local representative is `A i⁻¹`. -/
theorem coreRep_inv_eq (h : B.SmoothGluing) (i : ι) (hi : Nonempty (B.D i : Set LocalModel))
    (mi : B.pieceChart i hi ∈ atlas LocalModel (Space B)) {x : Space B}
    (hx : x ∈ B.chartRange i) (v : LocalModel) :
    coreRep (tangentCore h) (internalLorentzBundleCore S)
        (fun y => (E.fiberEquiv h y).symm) ⟨B.pieceChart i hi, mi⟩ i x v
      = (E.A i (B.pieceCoord i x)).symm v := by
  have hx' : x ∈ (tangentCore h).baseSet ⟨B.pieceChart i hi, mi⟩ := by
    rw [tangentCore_baseSet]
    show x ∈ (B.pieceChart i hi).source
    rw [pieceChart_source hi]
    exact hx
  have hxi : x ∈ (internalLorentzBundleCore S).baseSet i := hx
  have hcomp := coreRep_symm_comp (Z₁ := internalLorentzBundleCore S) (Z₂ := tangentCore h)
    (E.fiberEquiv h) i ⟨B.pieceChart i hi, mi⟩ hxi hx'
    ((E.A i (B.pieceCoord i x)).symm v)
  rw [E.coreRep_eq h i hi mi hx, ContinuousLinearEquiv.apply_symm_apply] at hcomp
  exact hcomp

/-- **DERIVED (Task 35).**  The local representative is continuous — indeed `C^∞` — on the
chart domain. -/
theorem continuousOn_coreRep (h : B.SmoothGluing) (i : ι)
    (hi : Nonempty (B.D i : Set LocalModel))
    (mi : B.pieceChart i hi ∈ atlas LocalModel (Space B)) :
    ContinuousOn (coreRep (internalLorentzBundleCore S) (tangentCore h) (E.fiberEquiv h) i
        ⟨B.pieceChart i hi, mi⟩)
      ((internalLorentzBundleCore S).baseSet i ∩ (tangentCore h).baseSet
        ⟨B.pieceChart i hi, mi⟩) := by
  have hsub : ((internalLorentzBundleCore S).baseSet i ∩ (tangentCore h).baseSet
      ⟨B.pieceChart i hi, mi⟩) ⊆ B.chartRange i := fun x hx => hx.1
  have hA : ContinuousOn (fun y : LocalModel => ((E.A i y : LocalModel →L[ℝ] LocalModel)))
      (B.D i) := (E.contDiffOn_A i).continuousOn
  have hcoord : ContinuousOn (B.pieceCoord i) (B.chartRange i) :=
    B.continuousOn_pieceCoord i hi
  have hmaps : Set.MapsTo (B.pieceCoord i) (B.chartRange i) (B.D i) :=
    fun x hx => B.pieceCoord_mem_D hx
  refine ((hA.comp hcoord hmaps).mono hsub).congr fun x hx => ?_
  refine ContinuousLinearMap.ext fun v => ?_
  exact E.coreRep_eq h i hi mi (hsub hx) v

/-- **DERIVED (Task 35).**  The inverse local representative is continuous on the chart
domain. -/
theorem continuousOn_coreRep_inv (h : B.SmoothGluing) (i : ι)
    (hi : Nonempty (B.D i : Set LocalModel))
    (mi : B.pieceChart i hi ∈ atlas LocalModel (Space B)) :
    ContinuousOn (coreRep (tangentCore h) (internalLorentzBundleCore S)
        (fun y => (E.fiberEquiv h y).symm) ⟨B.pieceChart i hi, mi⟩ i)
      ((tangentCore h).baseSet ⟨B.pieceChart i hi, mi⟩ ∩
        (internalLorentzBundleCore S).baseSet i) := by
  have hsub : ((tangentCore h).baseSet ⟨B.pieceChart i hi, mi⟩ ∩
      (internalLorentzBundleCore S).baseSet i) ⊆ B.chartRange i := fun x hx => hx.2
  have hA : ContinuousOn
      (fun y : LocalModel => (((E.A i y).symm : LocalModel →L[ℝ] LocalModel))) (B.D i) :=
    (E.contDiffOn_A_symm i).continuousOn
  have hcoord : ContinuousOn (B.pieceCoord i) (B.chartRange i) :=
    B.continuousOn_pieceCoord i hi
  have hmaps : Set.MapsTo (B.pieceCoord i) (B.chartRange i) (B.D i) :=
    fun x hx => B.pieceCoord_mem_D hx
  refine ((hA.comp hcoord hmaps).mono hsub).congr fun x hx => ?_
  refine ContinuousLinearMap.ext fun v => ?_
  exact E.coreRep_inv_eq h i hi mi (hsub hx) v

/-- **DERIVED (Task 35), PRINCIPAL — a regular solder is a topological bundle equivalence.**
The internal Lorentz bundle of the native Spin seed and Mathlib's tangent bundle of the
Task-33 emergent smooth manifold are equivalent as topological vector bundles over the
emergent base, by an equivalence covering the identity, linear on every fibre, with `C^∞`
local representatives (`coreRep_eq`). -/
def toCoreBundleEquiv (h : B.SmoothGluing) :
    CoreBundleEquiv (internalLorentzBundleCore S) (tangentCore h) where
  L := E.fiberEquiv h
  continuous_toTotal := by
    refine continuous_coreTotalMap _ fun x => ?_
    refine ⟨B.outIndex x, ⟨B.pieceChart (B.outIndex x)
      ⟨(Quotient.out (s := B.setoid) x).2⟩, pieceChart_outIndex_mem_atlas x⟩, ?_, ?_, ?_⟩
    · exact B.mem_chartRange_outIndex x
    · rw [tangentCore_baseSet]
      show x ∈ (B.pieceChart (B.outIndex x) ⟨(Quotient.out (s := B.setoid) x).2⟩).source
      rw [pieceChart_source]
      exact B.mem_chartRange_outIndex x
    · exact E.continuousOn_coreRep h _ _ _
  continuous_invTotal := by
    refine continuous_coreTotalMap _ fun x => ?_
    refine ⟨⟨B.pieceChart (B.outIndex x) ⟨(Quotient.out (s := B.setoid) x).2⟩,
      pieceChart_outIndex_mem_atlas x⟩, B.outIndex x, ?_, ?_, ?_⟩
    · rw [tangentCore_baseSet]
      show x ∈ (B.pieceChart (B.outIndex x) ⟨(Quotient.out (s := B.setoid) x).2⟩).source
      rw [pieceChart_source]
      exact B.mem_chartRange_outIndex x
    · exact B.mem_chartRange_outIndex x
    · exact E.continuousOn_coreRep_inv h _ _ _

/-- **DERIVED (Task 35).**  The total spaces of the internal Lorentz bundle and of the
tangent bundle of the emergent manifold are homeomorphic, by a homeomorphism covering the
identity of the base and linear on every fibre. -/
def toTangentHomeomorph (h : B.SmoothGluing) :
    (internalLorentzBundleCore S).TotalSpace ≃ₜ (tangentCore h).TotalSpace :=
  (E.toCoreBundleEquiv h).toHomeomorph

/-- **DERIVED (Task 35).**  The target of the equivalence really is Mathlib's tangent bundle
of the emergent manifold. -/
theorem tangentCore_totalSpace_eq (h : B.SmoothGluing) :
    (tangentCore h).TotalSpace = TangentBundle localModelI (Space B) := rfl

end SmoothTangentSolderData

/-! ## The converse: a regular bundle equivalence gives a regular solder -/

/-- **DERIVED (Task 35), the converse direction.**  A fibrewise linear equivalence of the
internal Lorentz bundle with the tangent bundle whose local representative in the chart of
every piece is a `C^∞` family `A i` *is* a regular solder datum: the intertwining law is
forced by the two coordinate-change systems.  No further hypothesis is used. -/
def smoothTangentSolderData_of_localRep {S : NativeSpinTransitionData ↥SpinGroup
      (emergentCover B)} (h : B.SmoothGluing)
    (L : Space B → (LocalModel ≃L[ℝ] LocalModel))
    (A : ι → LocalModel → (LocalModel ≃L[ℝ] LocalModel))
    (hA : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => ((A i y : LocalModel →L[ℝ] LocalModel))) (B.D i))
    (hL : ∀ i : ι, ∀ x ∈ B.chartRange i, ∀ v : LocalModel,
      L x v = B.tangentTransitionMap i (B.outIndex x) (B.pieceCoord i x)
        (A i (B.pieceCoord i x) (projectedLorentzTransition S i (coverIndex B x) x v))) :
    SmoothTangentSolderData B S where
  A := A
  contDiffOn_A := hA
  intertwine i j y hy v := by
    set x := B.chart i ⟨y, B.W_subset i j hy⟩ with hxdef
    have hxi : x ∈ B.chartRange i := ⟨_, rfl⟩
    have hxj : x ∈ B.chartRange j := by
      rw [hxdef, B.chart_eq_chart_of_mem_W i j hy]
      exact ⟨_, rfl⟩
    have hyi : B.pieceCoord i x = y := by
      have h1 : B.chart i ⟨B.pieceCoord i x, B.pieceCoord_mem_D hxi⟩ = x :=
        B.chart_pieceCoord hxi
      exact congrArg Subtype.val (B.injective_chart i (h1.trans hxdef))
    have hyj : B.pieceCoord j x = B.φ i j y := by
      rw [← B.φ_pieceCoord hxi hxj, hyi]
    set c := coverIndex B x with hc
    set k := B.outIndex x with hk
    have hxc : x ∈ B.chartRange c := mem_coverIndex x
    have hxk : x ∈ B.chartRange k := B.mem_chartRange_outIndex x
    have hikW : B.pieceCoord i x ∈ B.W i k := B.pieceCoord_mem_W_of_mem hxi hxk
    have hjkW : B.pieceCoord j x ∈ B.W j k := B.pieceCoord_mem_W_of_mem hxj hxk
    have hik_eq : B.φ i k (B.pieceCoord i x) = B.pieceCoord k x := B.φ_pieceCoord hxi hxk
    have hjk_eq : B.φ j k (B.pieceCoord j x) = B.pieceCoord k x := B.φ_pieceCoord hxj hxk
    have hkj : B.pieceCoord k x ∈ B.W k j := B.pieceCoord_mem_W_of_mem hxk hxj
    -- the two chart expressions of `L x` agree, and the common tangent transition cancels
    have hcancel : ∀ w : LocalModel,
        A j (B.pieceCoord j x) (projectedLorentzTransition S j c x w)
          = B.tangentTransitionMap i j (B.pieceCoord i x)
              (A i (B.pieceCoord i x) (projectedLorentzTransition S i c x w)) := by
      intro w
      have hkey : B.tangentTransitionMap j k (B.pieceCoord j x)
            (A j (B.pieceCoord j x) (projectedLorentzTransition S j c x w))
          = B.tangentTransitionMap i k (B.pieceCoord i x)
              (A i (B.pieceCoord i x) (projectedLorentzTransition S i c x w)) := by
        rw [← hL j x hxj w, hL i x hxi w]
      have hlhs := BaseGluingData.tangentTransitionMap_left_inv h hjkW
        (A j (B.pieceCoord j x) (projectedLorentzTransition S j c x w))
      rw [hjk_eq] at hlhs
      have hrhs := BaseGluingData.tangentTransitionMap_comp h hikW
        (by rw [hik_eq]; exact hkj)
        (A i (B.pieceCoord i x) (projectedLorentzTransition S i c x w))
      rw [hik_eq] at hrhs
      rw [← hlhs, hkey, hrhs]
    -- the internal cocycle relates the two internal coordinate systems
    have hsymm := projectedLorentzTransition_symm S c j (x := x) ⟨hxc, hxj⟩ v
    have hcoc := projectedLorentzTransition_cocycle S i c j (x := x) ⟨⟨hxi, hxc⟩, hxj⟩ v
    have hfin := hcancel (projectedLorentzTransition S c j x v)
    rw [hsymm, hcoc, hyi, hyj] at hfin
    exact hfin

/-- **DERIVED (Task 35), THE PRINCIPAL TASK-35 EQUIVALENCE.**  For the Task-33 emergent
smooth manifold and an emergent Spin seed, the following are equivalent:

1. a **regular solder datum** `SmoothTangentSolderData B S` exists;
2. there is a **regular bundle equivalence** of the internal Lorentz bundle with the genuine
   tangent bundle: a fibrewise continuous linear equivalence `L` whose induced total-space
   maps are continuous in both directions, and whose local representative in the chart of
   each piece is a `C^∞` family `A i` of automorphisms of the local model.

So the missing regular coupling of Task 34 *is exactly* a bundle-level equivalence
`InternalLorentzBundle(S) ≃ TM`; there is no further geometric primitive hidden between the
two notions.  (The regularity level is stated exactly: a total-space homeomorphism covering
the identity, fibrewise linear, with `C^∞` local representatives.  See the module docstring
for why a *smooth* bundle equivalence is not available for a merely continuous Spin
cocycle.) -/
theorem smooth_solder_iff_regular_bundle_equivalence
    {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)} (h : B.SmoothGluing) :
    Nonempty (SmoothTangentSolderData B S) ↔
      ∃ (L : Space B → (LocalModel ≃L[ℝ] LocalModel))
        (A : ι → LocalModel → (LocalModel ≃L[ℝ] LocalModel)),
        (∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
            (fun y => ((A i y : LocalModel →L[ℝ] LocalModel))) (B.D i)) ∧
        Continuous (coreTotalMap (internalLorentzBundleCore S) (tangentCore h) L) ∧
        Continuous (coreTotalMap (tangentCore h) (internalLorentzBundleCore S)
          fun x => (L x).symm) ∧
        (∀ i : ι, ∀ x ∈ B.chartRange i, ∀ v : LocalModel,
          L x v = B.tangentTransitionMap i (B.outIndex x) (B.pieceCoord i x)
            (A i (B.pieceCoord i x) (projectedLorentzTransition S i (coverIndex B x) x v))) := by
  constructor
  · rintro ⟨E⟩
    refine ⟨E.fiberEquiv h, E.A, E.contDiffOn_A,
      (E.toCoreBundleEquiv h).continuous_toTotal,
      (E.toCoreBundleEquiv h).continuous_invTotal, fun i x hx v => ?_⟩
    have hcompat := E.localFrame_compat h i (coverIndex B x) hx (mem_coverIndex x) v
    exact hcompat
  · rintro ⟨L, A, hA, -, -, hL⟩
    exact ⟨smoothTangentSolderData_of_localRep h L A hA hL⟩

end SpinNative

end

/-! ## Axiom audit -/

#print axioms SolderBundle.continuous_coreTotalMap
#print axioms SolderBundle.CoreBundleEquiv.toHomeomorph
#print axioms SpinNative.SmoothTangentSolderData.coreRep_eq
#print axioms SpinNative.SmoothTangentSolderData.toCoreBundleEquiv
#print axioms SpinNative.SmoothTangentSolderData.toTangentHomeomorph
#print axioms SpinNative.smoothTangentSolderData_of_localRep
#print axioms SpinNative.smooth_solder_iff_regular_bundle_equivalence
