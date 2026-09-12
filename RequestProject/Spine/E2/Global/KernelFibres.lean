import RequestProject.Spine.E2.Global.GlobalFrameProjection

/-!
# Task 30, Packages O and P: the exact fibres of the global projection

Package O (items 104–110) proves that two points of the glued carrier have the same ordinary
frame image **iff** they differ by a unique element of the kernel `P.Ker` of the frozen
internal projection (the inherited `KerSign` in the certified instance):

`internalToFrame_fibre_kerSign_torsor`.

Both directions are proved: kernel elements act trivially after `internalToFrame` (item 107),
and equality of ordinary images forces the transport element to lie in the kernel and to be
unique (items 105, 106).  Hence every fibre of `internalToFrame` is a free transitive
`P.Ker`-set (item 108).

Package P (items 111–115) is deliberately limited.  The **exact fibre theorem** is proved in
the strongest cheap form: an explicit bijection of every fibre with `P.Ker`
(`internalToFrame_fibre_equiv_ker`), whence a two-element fibre as soon as the kernel has two
elements (`internalToFrame_fibre_card_two`).  A covering-map statement for `internalToFrame`
is **not attempted** — that is a separate topology branch, and item 115 explicitly permits
stopping at the exact local two-element fibre theorem (negative control 154: a two-element
fibre theorem is weaker than a covering-map theorem).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask30

open NullSectorTask28 NullSectorTask29 Topology

universe u v w t y z

section KernelFibres

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {P : InternalProjection L G} {S : TransitionSystem B ι G}
  {Fm : Type z} [TopologicalSpace Fm] [MulAction G Fm] {M : OrdinaryFrameModel G Fm}
  {Tot : Type y} [TopologicalSpace Tot]

namespace OrdinaryFrameSide

variable (F : OrdinaryFrameSide S M Tot)

/-- **PACKAGE K, derived.**  The inherited ordinary right action is trivial at the identity
of the visible group. -/
theorem ract_one_of_chart (x : Tot) (i : ι) (hi : F.base x ∈ S.U i) : F.ract x 1 = x := by
  have hb : F.base (F.ract x 1) = F.base x := F.base_ract x 1
  have h' : F.base (F.ract x 1) ∈ S.U i := by rw [hb]; exact hi
  have e1 : (F.chart i ⟨F.ract x 1, h'⟩).2 = (F.chart i ⟨x, hi⟩).2 := by
    rw [F.chart_ract i x 1 hi h', M.ract_one]
  have e2 : (F.chart i ⟨F.ract x 1, h'⟩).1 = (F.chart i ⟨x, hi⟩).1 :=
    Subtype.ext ((F.chart_base i _).trans (hb.trans (F.chart_base i ⟨x, hi⟩).symm))
  have hpair : F.chart i ⟨F.ract x 1, h'⟩ = F.chart i ⟨x, hi⟩ := Prod.ext e2 e1
  exact congrArg Subtype.val ((F.chart i).injective hpair)

/-- **PACKAGE K, derived.**  The inherited ordinary right action is free. -/
theorem ract_left_cancel (x : Tot) (i : ι) (hi : F.base x ∈ S.U i) {k l : G}
    (h : F.ract x k = F.ract x l) : k = l := by
  have hk : F.base (F.ract x k) ∈ S.U i := by rw [F.base_ract]; exact hi
  have hl : F.base (F.ract x l) ∈ S.U i := by rw [F.base_ract]; exact hi
  have e3 : F.chart i ⟨F.ract x k, hk⟩ = F.chart i ⟨F.ract x l, hl⟩ :=
    congrArg (F.chart i) (Subtype.ext h)
  have e4 := congrArg Prod.snd e3
  rw [F.chart_ract i x k hi hk, F.chart_ract i x l hi hl] at e4
  exact M.ract_right_injective _ e4

end OrdinaryFrameSide

variable (T : CompatibleContinuousInternalTransitions P S) (F : OrdinaryFrameSide S M Tot)

/-- **PACKAGE O (item 107), principal.**  The kernel acts trivially after
`internalToFrame`. -/
theorem internalToFrame_ismul_ker (x : InternalTotal T) {a : L} (ha : a ∈ P.Ker) :
    internalToFrame T F (ismul T x a) = internalToFrame T F x := by
  obtain ⟨i, hi⟩ := S.cover (internalBase T x)
  have hbi : F.base (internalToFrame T F x) ∈ S.U i := by
    rw [internalToFrame_over_base]; exact hi
  rw [internalToFrame_equivariant, (P.mem_Ker_iff).1 ha,
    F.ract_one_of_chart (internalToFrame T F x) i hbi]

/-- **PACKAGE O (items 104–108), REQUIRED ENDPOINT
`internalToFrame_fibre_kerSign_torsor`.**  Two points with the same ordinary frame image
differ by a **unique** element of the kernel of the frozen internal projection. -/
theorem internalToFrame_fibre_kerSign_torsor (x y : InternalTotal T)
    (h : internalToFrame T F x = internalToFrame T F y) :
    ∃! z : P.Ker, ismul T x (z : L) = y := by
  have hb : internalBase T x = internalBase T y := by
    rw [← internalToFrame_over_base T F x, ← internalToFrame_over_base T F y, h]
  obtain ⟨a, ha, huniq⟩ := internal_fibre_existsUnique_groupTransport T x y hb
  obtain ⟨i, hi⟩ := S.cover (internalBase T x)
  have hbi : F.base (internalToFrame T F x) ∈ S.U i := by
    rw [internalToFrame_over_base]; exact hi
  have hract : F.ract (internalToFrame T F x) (P.proj a)
      = F.ract (internalToFrame T F x) 1 := by
    rw [← internalToFrame_equivariant, ha, ← h,
      F.ract_one_of_chart (internalToFrame T F x) i hbi]
  have hproj : P.proj a = 1 := F.ract_left_cancel (internalToFrame T F x) i hbi hract
  refine ⟨⟨a, (P.mem_Ker_iff).2 hproj⟩, ha, ?_⟩
  intro z hz
  exact Subtype.ext (huniq (z : L) hz)

/-- **PACKAGE O (item 105).**  The existence half, stated separately. -/
theorem exists_ker_of_internalToFrame_eq (x y : InternalTotal T)
    (h : internalToFrame T F x = internalToFrame T F y) :
    ∃ z : P.Ker, ismul T x (z : L) = y :=
  (internalToFrame_fibre_kerSign_torsor T F x y h).exists

/-- **PACKAGE O.**  The exact two-way characterization of the fibres of the global
projection. -/
theorem internalToFrame_eq_iff_ker (x y : InternalTotal T) :
    internalToFrame T F x = internalToFrame T F y ↔ ∃ z : P.Ker, ismul T x (z : L) = y := by
  constructor
  · exact exists_ker_of_internalToFrame_eq T F x y
  · rintro ⟨z, rfl⟩
    exact (internalToFrame_ismul_ker T F x z.2).symm

/-- **PACKAGE P (items 111, 112), the exact fibre theorem.**  Every fibre of the global
projection is in explicit bijection with the kernel of the frozen internal projection. -/
noncomputable def internalToFrame_fibre_equiv_ker (x : InternalTotal T) :
    {y : InternalTotal T // internalToFrame T F y = internalToFrame T F x} ≃ P.Ker where
  toFun y := (internalToFrame_fibre_kerSign_torsor T F x y.1 y.2.symm).choose
  invFun z := ⟨ismul T x (z : L), internalToFrame_ismul_ker T F x z.2⟩
  left_inv y := Subtype.ext
    (internalToFrame_fibre_kerSign_torsor T F x y.1 y.2.symm).choose_spec.1
  right_inv z := by
    obtain ⟨_, huniq⟩ :=
      (internalToFrame_fibre_kerSign_torsor T F x (ismul T x (z : L))
        (internalToFrame_ismul_ker T F x z.2).symm).choose_spec
    exact (huniq z rfl).symm

/-- **PACKAGE P (item 109).**  If the kernel has exactly two elements — as the inherited
sign kernel does — then every fibre of the global projection has exactly two points.  This is
strictly weaker than a covering-map statement (negative control 154). -/
theorem internalToFrame_fibre_card_two (x : InternalTotal T) (hker : Nat.card P.Ker = 2) :
    Nat.card {y : InternalTotal T // internalToFrame T F y = internalToFrame T F x} = 2 := by
  rw [Nat.card_congr (internalToFrame_fibre_equiv_ker T F x)]
  exact hker

end KernelFibres

end NullSectorTask30
