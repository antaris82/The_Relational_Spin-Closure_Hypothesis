import RequestProject.Spine.E2.Global.InternalGlueRelation

/-!
# Task 30, Packages D and E: the global quotient carrier and the set-level local charts

**Hard target A, second half.**

Package D (items 36–41) forms the quotient carrier

`InternalTotal T := Quotient (InternalGlueSetoid T)`,

its quotient map `iq`, the local parametrizations `ipsi i : U i × Lift → InternalTotal`, the
base projection `internalBase`, and proves that the base projection is well defined,
computes correctly on representatives and is surjective.  **No topology is used in Package
D** (item 42): the topological instance carried by the quotient is only *named* in the next
module.

Package E (items 43–49) constructs, before any topology, the local coordinate map

`icoord i : InternalTotal T → Lift`,

by transporting the internal coordinate of *any* representative to chart `i` with the
inherited transition `u_ji`, proves independence of the representative, and assembles the
required set-level equivalence

`internal_local_equiv_i : internalBase⁻¹(U i) ≃ U i × Lift`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask30

open NullSectorTask28 NullSectorTask29

universe u v w t

section Quotient

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {P : InternalProjection L G} {S : TransitionSystem B ι G}
  (T : CompatibleContinuousInternalTransitions P S)

/-! ## Package D — the quotient carrier -/

/-- **PACKAGE D (item 36), principal definition.**  The global quotient carrier obtained by
gluing the local products along the derived transition convention. -/
abbrev InternalTotal : Type max u w t := Quotient (InternalGlueSetoid T)

/-- **PACKAGE D (item 37).**  The quotient map. -/
def iq (x : InternalPre S L) : InternalTotal T := Quotient.mk (InternalGlueSetoid T) x

theorem iq_surjective : Function.Surjective (iq T) := Quotient.mk_surjective

theorem iq_eq_iff {x y : InternalPre S L} : iq T x = iq T y ↔ InternalGlueRel T x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

@[elab_as_elim]
theorem iq_inductionOn {motive : InternalTotal T → Prop} (x : InternalTotal T)
    (h : ∀ y : InternalPre S L, motive (iq T y)) : motive x :=
  Quotient.inductionOn x h

/-- **PACKAGE D.**  The local parametrization of the quotient carrier attached to `U i`. -/
def ipsi (i : ι) (p : ↥(S.U i) × L) : InternalTotal T := iq T ⟨i, p⟩

theorem ipsi_eq_iq (i : ι) (p : ↥(S.U i) × L) : ipsi T i p = iq T ⟨i, p⟩ := rfl

/-- **PACKAGE D (item 38), principal definition.**  The base projection of the quotient
carrier. -/
def internalBase : InternalTotal T → B :=
  Quotient.lift prePt fun _ _ h => (glueRel_pt_eq T h).symm

/-- **PACKAGE D (item 39).**  Well-definedness of the base projection, in the form in which
it is used: it is computed by any representative. -/
@[simp] theorem internalBase_iq (x : InternalPre S L) :
    internalBase T (iq T x) = prePt x := rfl

/-- **PACKAGE D (item 40), principal.**  `internalBase (q (i,b,a)) = b`. -/
@[simp] theorem internalBase_ipsi (i : ι) (p : ↥(S.U i) × L) :
    internalBase T (ipsi T i p) = (p.1 : B) := rfl

theorem ipsi_mem (i : ι) (p : ↥(S.U i) × L) : internalBase T (ipsi T i p) ∈ S.U i := p.1.2

/-- **PACKAGE D (item 41), principal.**  The base projection is surjective. -/
theorem internalBase_surjective : Function.Surjective (internalBase T) := by
  intro b
  obtain ⟨i, hi⟩ := S.cover b
  exact ⟨ipsi T i (⟨b, hi⟩, 1), rfl⟩

/-- **PACKAGE D.**  The local parametrizations are injective (a local product is not
collapsed). -/
theorem ipsi_injective (i : ι) : Function.Injective (ipsi T i) := by
  rintro ⟨⟨b, hb⟩, a⟩ ⟨⟨b', hb'⟩, a'⟩ h
  obtain ⟨rfl, rfl⟩ := glueRel_same_chart T ((iq_eq_iff T).1 h)
  rfl

/-- **PACKAGE D, principal — the exact gluing identity between two charts.**  This is the
derived convention `a_j = u_ij(b) * a_i`, read on the quotient. -/
theorem ipsi_trans (i j : ι) (b : B) (hi : b ∈ S.U i) (hj : b ∈ S.U j) (a : L) :
    ipsi T j (⟨b, hj⟩, uu T i j b hi hj * a) = ipsi T i (⟨b, hi⟩, a) :=
  (iq_eq_iff T).2 (glueRel_symm T (glueRel_mk T hi hj a))

/-! ## Package E — the local coordinate maps, before any topology -/

open Classical in
/-- **PACKAGE E (item 44).**  The internal coordinate of a *tagged representative*, read in
chart `i`: transport by the inherited transition `u_ji`.  Outside `U i` the value is the
neutral element; that branch is never used, the chart being always applied over `U i`. -/
noncomputable def icoordPre (i : ι) (x : InternalPre S L) : L :=
  if h : prePt x ∈ S.U i then uu T (preIdx x) i (prePt x) (prePt_mem x) h * preElt x else 1

/-- **PACKAGE E (item 45), principal.**  The transported coordinate does not depend on the
representative: this is exactly the triple law `u_kj * u_ik = u_ij`. -/
theorem icoordPre_glueRel (i : ι) {x y : InternalPre S L} (h : InternalGlueRel T x y) :
    icoordPre T i x = icoordPre T i y := by
  obtain ⟨j, ⟨b, hj⟩, a⟩ := x
  obtain ⟨k, ⟨b', hk⟩, a'⟩ := y
  have hb : b' = b := glueRel_pt_eq T h
  subst hb
  rw [glueRel_iff_of_pt] at h
  by_cases hi : b' ∈ S.U i
  · simp only [icoordPre, prePt_mk, dif_pos hi, preIdx_mk, preElt_mk, h, ← mul_assoc,
      uu_trans T j k i b' hj hk hi]
  · simp only [icoordPre, prePt_mk, dif_neg hi]

open Classical in
/-- **PACKAGE E (item 43), principal.**  The local coordinate map on the quotient carrier. -/
noncomputable def icoord (i : ι) : InternalTotal T → L :=
  Quotient.lift (icoordPre T i) fun _ _ h => icoordPre_glueRel T i h

theorem icoord_iq_of_mem (i j : ι) (b : B) (hj : b ∈ S.U j) (hi : b ∈ S.U i) (a : L) :
    icoord T i (iq T ⟨j, ⟨b, hj⟩, a⟩) = uu T j i b hj hi * a := by
  show icoordPre T i (⟨j, ⟨b, hj⟩, a⟩ : InternalPre S L) = _
  simp only [icoordPre, prePt_mk, preIdx_mk, preElt_mk]
  rw [dif_pos hi]

@[simp] theorem icoord_ipsi (i : ι) (p : ↥(S.U i) × L) : icoord T i (ipsi T i p) = p.2 := by
  obtain ⟨⟨b, hb⟩, a⟩ := p
  rw [ipsi_eq_iq, icoord_iq_of_mem T i i b hb hb, uu_self, one_mul]

/-- **PACKAGE E (item 47), principal.**  The local parametrization recovers every point over
`U i` from its transported coordinate. -/
theorem ipsi_icoord (i : ι) (x : InternalTotal T) (h : internalBase T x ∈ S.U i) :
    ipsi T i (⟨internalBase T x, h⟩, icoord T i x) = x := by
  induction x using iq_inductionOn with
  | h y =>
    obtain ⟨j, ⟨b, hj⟩, a⟩ := y
    have hi : b ∈ S.U i := h
    refine Eq.trans ?_ (ipsi_trans T j i b hj hi a)
    congr 1
    exact Prod.ext (Subtype.ext rfl) (icoord_iq_of_mem T i j b hj hi a)

/-- **PACKAGE E (item 48), REQUIRED ENDPOINT (set level, item 49).**  Over every chart domain
the quotient carrier is in bijection with the local product. -/
noncomputable def internalLocalEquiv (i : ι) :
    {x : InternalTotal T // internalBase T x ∈ S.U i} ≃ ↥(S.U i) × L where
  toFun x := (⟨internalBase T x.1, x.2⟩, icoord T i x.1)
  invFun p := ⟨ipsi T i p, ipsi_mem T i p⟩
  left_inv x := Subtype.ext (ipsi_icoord T i x.1 x.2)
  right_inv p := by
    refine Prod.ext (Subtype.ext ?_) ?_
    · exact internalBase_ipsi T i p
    · exact icoord_ipsi T i p

@[simp] theorem internalLocalEquiv_apply (i : ι)
    (x : {x : InternalTotal T // internalBase T x ∈ S.U i}) :
    internalLocalEquiv T i x = (⟨internalBase T x.1, x.2⟩, icoord T i x.1) := rfl

@[simp] theorem internalLocalEquiv_symm_apply (i : ι) (p : ↥(S.U i) × L) :
    (internalLocalEquiv T i).symm p = ⟨ipsi T i p, ipsi_mem T i p⟩ := rfl

/-- **PACKAGE E.**  Every point over `U i` has a (unique) representative in chart `i`. -/
theorem exists_ipsi_rep (i : ι) (x : InternalTotal T) (h : internalBase T x ∈ S.U i) :
    ∃! a : L, x = ipsi T i (⟨internalBase T x, h⟩, a) := by
  refine ⟨icoord T i x, (ipsi_icoord T i x h).symm, fun a ha => ?_⟩
  have := congrArg (icoord T i) ha
  rw [icoord_ipsi] at this
  exact this.symm

end Quotient

end NullSectorTask30
