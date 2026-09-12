import RequestProject.Spine.E2.Global.ConditionalGlobalInterface

/-!
# Task 30, Package R: independence of the glued object from the presentation of the
compatible transition system

Items 122–128.  Two compatible internal transition systems over the *same* ordinary
transitions may differ.  Item 125 asks for the exact condition under which they give
canonically equivalent global objects; the answer proved here is that pair-overlap data are
**not** enough: what is needed is a *chart-indexed* change

`ε_i : U i → Lift`

(the exact representative-change class already formalized in Tasks XXVIII–XXIX, read on whole
chart domains rather than on pair overlaps), acting on the transitions by

`u'_ij(b) = ε_j(b) · u_ij(b) · ε_i(b)⁻¹`.

Under such a gauge — and with `ε_i` kernel valued, so that the ordinary transitions are
untouched — the two glued carriers are **equivariantly homeomorphic over the ordinary frame
total space** (item 127): `gaugeHomeo` is a homeomorphism, commutes with the base projections,
intertwines the two global right `Lift`-actions, and commutes with the two maps to
`FrameTotal`.

Item 126 is respected: no claim is made that two *arbitrary* compatible systems yield the
same global object.  Only the gauge-related ones are compared, so the general classification
question is left open (the `PARTIAL` verdict of item 128).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask30

open NullSectorTask28 NullSectorTask29 Topology

universe u v w t y z

section Gauge

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {P : InternalProjection L G} {S : TransitionSystem B ι G}

/-- **PACKAGE R (items 122, 125), principal definition.**  A chart-indexed change of local
representatives relating two compatible internal transition systems.  It is *not* a
pair-overlap datum: `ε` is indexed by single chart domains, which is exactly the extra
condition isolated by item 125. -/
structure InternalTransitionGauge (T T' : CompatibleContinuousInternalTransitions P S) where
  /-- The chart-indexed change of representative. -/
  eps : ∀ i : ι, ↥(S.U i) → L
  /-- Continuity. -/
  continuous_eps : ∀ i, Continuous (eps i)
  /-- It is kernel valued, so the ordinary transitions are unchanged. -/
  ker_eps : ∀ (i : ι) (b : ↥(S.U i)), eps i b ∈ P.Ker
  /-- The transformation law of the transitions. -/
  law : ∀ (i j : ι) (b : B) (hi : b ∈ S.U i) (hj : b ∈ S.U j),
    uu T' i j b hi hj = eps j ⟨b, hj⟩ * uu T i j b hi hj * (eps i ⟨b, hi⟩)⁻¹

namespace InternalTransitionGauge

variable {T T' : CompatibleContinuousInternalTransitions P S} (E : InternalTransitionGauge T T')

/-- The reversed gauge. -/
def symmGauge : InternalTransitionGauge T' T where
  eps i b := (E.eps i b)⁻¹
  continuous_eps i := (E.continuous_eps i).inv
  ker_eps i b := Subgroup.inv_mem _ (E.ker_eps i b)
  law i j b hi hj := by
    rw [E.law i j b hi hj, inv_inv]
    group

/-- **PACKAGE R.**  The gauge map on tagged local representatives. -/
def preMap (x : InternalPre S L) : InternalTotal T' :=
  ipsi T' x.1 (x.2.1, E.eps x.1 x.2.1 * x.2.2)

theorem preMap_glueRel {x y : InternalPre S L} (h : InternalGlueRel T x y) :
    E.preMap x = E.preMap y := by
  obtain ⟨i, ⟨b, hi⟩, a⟩ := x
  obtain ⟨j, ⟨b', hj⟩, a'⟩ := y
  have hb : b' = b := glueRel_pt_eq T h
  subst hb
  rw [glueRel_iff_of_pt] at h
  show ipsi T' i ((⟨b', hi⟩ : ↥(S.U i)), E.eps i ⟨b', hi⟩ * a)
      = ipsi T' j ((⟨b', hj⟩ : ↥(S.U j)), E.eps j ⟨b', hj⟩ * a')
  have hstep := ipsi_trans T' i j b' hi hj (E.eps i ⟨b', hi⟩ * a)
  rw [← hstep]
  refine ipsi_congr T' j hj hj _ _ rfl ?_
  rw [E.law i j b' hi hj, h]
  group

/-- **PACKAGE R (item 123), principal definition.**  The gauge map between the two glued
carriers. -/
def map : InternalTotal T → InternalTotal T' :=
  Quotient.lift E.preMap fun _ _ h => E.preMap_glueRel h

@[simp] theorem map_ipsi (i : ι) (p : ↥(S.U i) × L) :
    E.map (ipsi T i p) = ipsi T' i (p.1, E.eps i p.1 * p.2) := rfl

@[simp] theorem internalBase_map (x : InternalTotal T) :
    internalBase T' (E.map x) = internalBase T x := by
  induction x using iq_inductionOn with
  | h y => rfl

theorem continuous_map : Continuous E.map := by
  rw [continuous_internalTotal_iff]
  intro i
  exact (continuous_ipsi T' i).comp
    (continuous_fst.prodMk (((E.continuous_eps i).comp continuous_fst).mul continuous_snd))

theorem symmGauge_map_map (x : InternalTotal T) : E.symmGauge.map (E.map x) = x := by
  induction x using iq_inductionOn with
  | h y =>
    obtain ⟨i, ⟨b, hi⟩, a⟩ := y
    show ipsi T i ((⟨b, hi⟩ : ↥(S.U i)),
        (E.eps i ⟨b, hi⟩)⁻¹ * (E.eps i ⟨b, hi⟩ * a)) = _
    rw [inv_mul_cancel_left]
    rfl

theorem map_symmGauge_map (x : InternalTotal T') : E.map (E.symmGauge.map x) = x := by
  induction x using iq_inductionOn with
  | h y =>
    obtain ⟨i, ⟨b, hi⟩, a⟩ := y
    show ipsi T' i ((⟨b, hi⟩ : ↥(S.U i)),
        E.eps i ⟨b, hi⟩ * ((E.eps i ⟨b, hi⟩)⁻¹ * a)) = _
    rw [mul_inv_cancel_left]
    rfl

/-- **PACKAGE R (items 123, 127), principal.**  Gauge-related compatible presentations give
**homeomorphic** glued carriers. -/
def gaugeHomeo : InternalTotal T ≃ₜ InternalTotal T' where
  toFun := E.map
  invFun := E.symmGauge.map
  left_inv := E.symmGauge_map_map
  right_inv := E.map_symmGauge_map
  continuous_toFun := E.continuous_map
  continuous_invFun := E.symmGauge.continuous_map

@[simp] theorem gaugeHomeo_apply (x : InternalTotal T) : E.gaugeHomeo x = E.map x := rfl

/-- **PACKAGE R (item 127).**  The homeomorphism lies over the base. -/
theorem gaugeHomeo_over_base (x : InternalTotal T) :
    internalBase T' (E.gaugeHomeo x) = internalBase T x := E.internalBase_map x

/-- **PACKAGE R (item 127).**  The homeomorphism is equivariant for the two global right
`Lift`-actions. -/
theorem gaugeHomeo_equivariant (x : InternalTotal T) (h : L) :
    E.gaugeHomeo (ismul T x h) = ismul T' (E.gaugeHomeo x) h := by
  induction x using iq_inductionOn with
  | h y =>
    obtain ⟨i, ⟨b, hi⟩, a⟩ := y
    show ipsi T' i ((⟨b, hi⟩ : ↥(S.U i)), E.eps i ⟨b, hi⟩ * (a * h))
        = ipsi T' i ((⟨b, hi⟩ : ↥(S.U i)), E.eps i ⟨b, hi⟩ * a * h)
    rw [mul_assoc]

variable {Fm : Type z} [TopologicalSpace Fm] [MulAction G Fm] {M : OrdinaryFrameModel G Fm}
  {Tot : Type y} [TopologicalSpace Tot]

/-- **PACKAGE R (item 127), REQUIRED STRONG ENDPOINT.**  The homeomorphism commutes with the
two projections to the already reconstructed ordinary frame total space: the glued objects
are equivariantly homeomorphic **over** `FrameTotal`.  This is where the kernel-valuedness of
the gauge is used. -/
theorem gaugeHomeo_over_frame (F : OrdinaryFrameSide S M Tot) (x : InternalTotal T) :
    internalToFrame T' F (E.gaugeHomeo x) = internalToFrame T F x := by
  induction x using iq_inductionOn with
  | h y =>
    obtain ⟨i, ⟨b, hi⟩, a⟩ := y
    show F.psi i ((⟨b, hi⟩ : ↥(S.U i)), P.proj (E.eps i ⟨b, hi⟩ * a) • M.ref)
        = F.psi i ((⟨b, hi⟩ : ↥(S.U i)), P.proj a • M.ref)
    rw [map_mul, (P.mem_Ker_iff).1 (E.ker_eps i ⟨b, hi⟩), one_mul]

end InternalTransitionGauge

/-- **PACKAGE R (item 126), negative control.**  No claim is made that *arbitrary* compatible
systems produce the same global object: the comparison above is available exactly when a
chart-indexed kernel-valued gauge relating the two systems exists.  Recorded as the explicit
hypothesis of the comparison theorem. -/
theorem gauge_needed_for_comparison
    {T T' : CompatibleContinuousInternalTransitions P S}
    (E : InternalTransitionGauge T T') :
    ∀ (i j : ι) (b : B) (hi : b ∈ S.U i) (hj : b ∈ S.U j),
      uu T' i j b hi hj = E.eps j ⟨b, hj⟩ * uu T i j b hi hj * (E.eps i ⟨b, hi⟩)⁻¹ :=
  E.law

end Gauge

end NullSectorTask30
