import RequestProject.Spine.Comparison.CanonicalSpinSeed
import RequestProject.Spine.Cech.FullNerve
import RequestProject.Spine.Emergent.CoverAdapter
import RequestProject.Spine.Emergent.NonDerivability

/-!
# Spine / Comparison : the canonical Spin seed over an *emergent* base

**Comparison module of the Task-32 manifold-emergence layer.**  It is the only place where
the emergent base of `RequestProject.Spine.Emergent.*` and the Spin-native uniqueness layer
of Task 31 are seen together; like every module of `Spine.Comparison` it is a leaf of the
production DAG.

## What it establishes

1. **The external base disappears from the seed.**  `SpinNative.emergentSeed` produces a
   `SpinNative.CanonicalSpinSeed` whose base is `EmergentBase.Space B`, *constructed* from a
   base-gluing datum `B`, and whose cover is the emergent cover of that construction.  The
   parameters `X`, `[TopologicalSpace X]` and `𝓤` of the Task-31 package are therefore no
   longer external inputs: they are outputs of the reconstruction.  What remains external is
   exactly the base-gluing datum `B` — the explicit base-gluing primitive isolated in
   `RequestProject.Spine.Emergent.BaseGluing`, whose cross-piece incidence layer is proved
   irreducibly additional (and *not* proved minimal; see
   `RequestProject.Spine.Emergent.LocalPieceData`).

2. **The symmetric sector closes the Task-31 kernel/`Ȟ¹` gate.**  On the neutral
   (maximally symmetric) emergent base the emergent cover has all members equal to the whole
   base, so its nerve is full and its double overlaps are preconnected; hence
   `Ȟ¹(𝓤;ℤ₂) = 0` by `CechZ2.cohomology_one_eq_zero_of_fullNerve`, and the Task-31 gate
   `SpinNative.KernelTwistsGaugeTrivial` holds.  Consequently there is exactly **one Spin
   gauge class** over such a base: `SpinNative.symmetric_emergent_spin_unique_up_to_gauge`.

   **Scope (Task-33 audit).**  This vanishing is a *fixed-cover* statement about the
   *specific* maximally-overlapping emergent cover of the *symmetric* sector, whose nerve is
   full.  Nothing here says that `Ȟ¹` vanishes for an arbitrary emergent base, for an
   arbitrary cover of the symmetric base, or that the singular/Čech `H¹(M;ℤ₂)` of an
   emergent manifold vanishes.  No such statement is proved anywhere in this project.

3. **Spin data do not determine the base.**  `SpinNative.spin_data_do_not_determine_base`
   exhibits two base-gluing data whose Spin transition laws over their respective emergent
   covers are *both pointwise trivial* — `g_ij(x) = 1` on each cover — while their emergent
   bases are not homeomorphic.  (The two cocycles are not literally the same typed object:
   they live over different covers of different bases.  Task-33 correction of the earlier
   "literally the same" wording.)

The standard top-down control branch is untouched: the seed still carries the Task-30
statement that the standard obstruction of the projected data is trivial, now over the
emergent base.  The comparison of the emergent base with `TM` and `P_SO(TM)` is *not* claimed
here: it would need a solder form identifying the local model with the tangent spaces, which
this project does not have.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace SpinNative

open CechSpinLift CechZ2 CechSpinZ2 NullSectorTask28 EmergentBase EmergentBase.BaseGluingData

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {V : Type w} [TopologicalSpace V] {ι : Type t}

/-! ## The canonical Spin seed over an emergent base -/

/-- **NEWLY DEFINED (Task 32), principal.**  The canonical Spin seed carried by an emergent
base: the base and its cover are *constructed* from the base-gluing datum, not supplied. -/
def emergentSeed (B : BaseGluingData V ι) (P : InternalProjection L G)
    (S : NativeSpinTransitionData L (emergentCover B)) :
    CanonicalSpinSeed L G (Space B) ι where
  cover := emergentCover B
  proj := P
  native := S

@[simp] theorem emergentSeed_cover (B : BaseGluingData V ι) (P : InternalProjection L G)
    (S : NativeSpinTransitionData L (emergentCover B)) :
    (emergentSeed B P S).cover = emergentCover B := rfl

@[simp] theorem emergentSeed_native (B : BaseGluingData V ι) (P : InternalProjection L G)
    (S : NativeSpinTransitionData L (emergentCover B)) :
    (emergentSeed B P S).native = S := rfl

/-- **DERIVED (Task 32).**  Every base-gluing datum carries at least one Spin seed: the
trivial Spin gluing datum.  (This is also the reason the base cannot be recovered from the
Spin side — see `spin_data_do_not_determine_base`.) -/
def emergentSeedTrivial (B : BaseGluingData V ι) (P : InternalProjection L G) :
    CanonicalSpinSeed L G (Space B) ι :=
  emergentSeed B P (trivialCocycle L (emergentCover B))

/-! ## The symmetric emergent base closes the Task-31 gate -/

variable {D : Set V} (hD : IsOpen D)

/-- **DERIVED (Task 32).**  The nerve of the emergent cover of the neutral sector is full. -/
theorem symmetricCover_fullNerve (hne : D.Nonempty) (i₀ : ι) :
    CechZ2.FullNerve (emergentCover (symmetricGluing ι hD)).U := by
  haveI : Nonempty ι := ⟨i₀⟩
  haveI : Nonempty (Space (symmetricGluing ι hD)) := symmetricGluing.nonempty hD hne
  exact CechZ2.fullNerve_of_eq_univ (symmetricCover_U_eq_univ hD)

/-- **DERIVED (Task 32), principal.**  The fixed-cover Čech `Ȟ¹(𝓤;ℤ₂)` of the emergent cover
of the neutral sector vanishes.  This is a statement about *this* cover of *this* (symmetric,
full-overlap) emergent base only; no `Ȟ¹` statement about an arbitrary emergent base, an
arbitrary cover, or the space-level `H¹(M;ℤ₂)` is claimed or proved. -/
theorem symmetric_emergent_H1_trivial (hne : D.Nonempty) (i₀ : ι)
    (h : CechZ2.H1 (emergentCover (symmetricGluing ι hD)).U) : h = 0 :=
  CechZ2.cohomology_one_eq_zero_of_fullNerve i₀ (symmetricCover_fullNerve hD hne i₀) h

/-- **DERIVED (Task 32), PRINCIPAL — the Task-31 kernel-twist gate is closed on the
symmetric emergent base.**  On the neutral emergent base over a nonempty preconnected local
domain, every kernel-valued Čech 1-cocycle of the emergent cover is gauge trivial. -/
theorem kernelTwistsGaugeTrivial_symmetric_emergent {P : InternalProjection L G}
    (S : KernelSign P) (hne : D.Nonempty) (hconn : IsPreconnected D) (i₀ : ι) :
    KernelTwistsGaugeTrivial P (emergentCover (symmetricGluing ι hD)) := by
  haveI : Nonempty ι := ⟨i₀⟩
  exact kernelTwistsGaugeTrivial_of_cover_H1_trivial S
    (symmetricCover_isPreconnected_overlap₂ hD hconn)
    (symmetric_emergent_H1_trivial hD hne i₀)

/-- **DERIVED (Task 32), PRINCIPAL — exactly one Spin gauge class over the symmetric
emergent base.**  Any two Spin structures over the same visible transition data on the
neutral emergent base are gauge equivalent, and the gauge quotient is a subsingleton. -/
theorem symmetric_emergent_spin_unique_up_to_gauge {P : InternalProjection L G}
    (S : KernelSign P) (hne : D.Nonempty) (hconn : IsPreconnected D) (i₀ : ι)
    (T : VisibleCocycle G (emergentCover (symmetricGluing ι hD))) :
    (∀ C C' : SpinStructureOver P T, GaugeEquiv P C.data C'.data) ∧
      Subsingleton (GaugeClass P T) :=
  ⟨fun C C' => gaugeEquiv_of_kernelTwistsGaugeTrivial
      (kernelTwistsGaugeTrivial_symmetric_emergent hD S hne hconn i₀) C C',
    subsingleton_gaugeClass (kernelTwistsGaugeTrivial_symmetric_emergent hD S hne hconn i₀) T⟩

/-- **DERIVED (Task 32), the packaged endpoint.**  For a canonical Spin seed over the
*neutral emergent base*:

1. the canonical Spin structure carries exactly the primitive Spin datum (Task 31, U1/U2);
2. the standard Spin-lift obstruction of the projected data is trivial for every family of
   local lifts (Task 30) — the standard control branch survives the change of base;
3. every competitor over the same projected data is a kernel twist (Task 31);
4. all of them are gauge equivalent and the gauge quotient is a subsingleton: **one** Spin
   gauge class, with no assumed `Ȟ¹`-vanishing hypothesis — it is proved for this base. -/
theorem emergent_seed_certificate {P : InternalProjection L G} (S : KernelSign P)
    (hne : D.Nonempty) (hconn : IsPreconnected D) (i₀ : ι)
    (N : NativeSpinTransitionData L (emergentCover (symmetricGluing ι hD))) :
    (emergentSeed (symmetricGluing ι hD) P N).canonical.data = N ∧
    (∀ D' : SpinLiftFamily P (emergentSeed (symmetricGluing ι hD) P N).projected,
        D'.obstruction = trivialClass P (emergentCover (symmetricGluing ι hD))) ∧
    (∀ C : SpinStructureOver P (emergentSeed (symmetricGluing ι hD) P N).projected,
        ∃ ε : KerCocycle P (emergentCover (symmetricGluing ι hD)), twist N ε = C.data) ∧
    (∀ C : SpinStructureOver P (emergentSeed (symmetricGluing ι hD) P N).projected,
        GaugeEquiv P N C.data) ∧
    Subsingleton (GaugeClass P (emergentSeed (symmetricGluing ι hD) P N).projected) := by
  refine ⟨rfl, fun D' => (emergentSeed (symmetricGluing ι hD) P N).obstruction_trivial D',
    fun C => (emergentSeed (symmetricGluing ι hD) P N).residual_freedom C, ?_, ?_⟩
  · exact fun C => (emergentSeed (symmetricGluing ι hD) P N).unique_up_to_gauge_of_gate
      (kernelTwistsGaugeTrivial_symmetric_emergent hD S hne hconn i₀) C
  · exact subsingleton_gaugeClass
      (kernelTwistsGaugeTrivial_symmetric_emergent hD S hne hconn i₀) _

/-! ## Spin data do not determine the base -/

omit [IsTopologicalGroup L] in
/-- **DERIVED (Task 32), PRINCIPAL — the provenance discriminator.**  There are two
base-gluing data over the same local domain whose Spin transition laws over their respective
emergent covers are both the *pointwise trivial* one, `g_ij(x) = 1`, and whose emergent bases
are not homeomorphic.  Fibre gluing is therefore not base gluing: no base incidence
information can be reconstructed from the Spin transition law.

The two transition data are *not* one and the same typed Lean object — they are cocycles over
different covers of different bases — and no type-erasing wrapper is manufactured to say
otherwise; the statement below is exactly the pointwise triviality of both, together with the
non-homeomorphy of the bases (Task-33 wording correction). -/
theorem spin_data_do_not_determine_base (hne : D.Nonempty) (hconn : IsPreconnected D) :
    (∀ (i j : Bool) (x : Space (symmetricGluing Bool hD)),
        (trivialCocycle L (emergentCover (symmetricGluing Bool hD))).g i j x = 1) ∧
    (∀ (i j : Bool) (x : Space (disjointGluing Bool hD)),
        (trivialCocycle L (emergentCover (disjointGluing Bool hD))).g i j x = 1) ∧
    (symmetricGluing Bool hD).D = (disjointGluing Bool hD).D ∧
    ¬ Nonempty (Space (symmetricGluing Bool hD) ≃ₜ Space (disjointGluing Bool hD)) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl,
    (base_not_determined_by_local_pieces hD hne hconn).1,
    (base_not_determined_by_local_pieces hD hne hconn).2⟩

end SpinNative

end

/-! ## Axiom audit of the Task-32 comparison endpoints -/

#print axioms EmergentBase.LocalModel
#print axioms EmergentBase.finrank_localModel
#print axioms EmergentBase.spin_acts_on_localModel
#print axioms EmergentBase.BaseGluingData
#print axioms EmergentBase.BaseGluingData.atlas_coherence
#print axioms EmergentBase.BaseGluingData.setoid
#print axioms EmergentBase.BaseGluingData.isOpenMap_mk
#print axioms EmergentBase.BaseGluingData.chartedSpace
#print axioms EmergentBase.BaseGluingData.t2Space_of_closedGluingGraph
#print axioms EmergentBase.BaseGluingData.secondCountableTopology_space
#print axioms EmergentBase.BaseGluingData.emergentManifold
#print axioms EmergentBase.BaseGluingData.emergentManifoldCertificate
#print axioms EmergentBase.symmetric_emergent_manifold
#print axioms EmergentBase.symmetric_emergent_base_unique
#print axioms EmergentBase.base_not_determined_by_local_pieces
#print axioms EmergentBase.emergentCover
#print axioms CechZ2.cohomology_one_eq_zero_of_fullNerve
#print axioms SpinNative.emergentSeed
#print axioms SpinNative.symmetric_emergent_H1_trivial
#print axioms SpinNative.kernelTwistsGaugeTrivial_symmetric_emergent
#print axioms SpinNative.symmetric_emergent_spin_unique_up_to_gauge
#print axioms SpinNative.emergent_seed_certificate
#print axioms SpinNative.spin_data_do_not_determine_base
