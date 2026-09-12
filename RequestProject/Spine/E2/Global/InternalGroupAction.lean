import RequestProject.Spine.E2.Global.InternalTopology

/-!
# Task 30, Packages H, I and J: fibres, the global internal-group action, freeness and
fibrewise transitivity

**Hard target C, first half.**

**Package I (items 72–75) — the side of the action is *derived*, not chosen for
convenience.**  The gluing convention derived in Package C makes the transitions act on the
**left**, `a_j = u_ij(b) * a_i`.  Consequently only a **right** multiplication
`a ↦ a * h` commutes with the gluing and descends to the quotient; a left global action would
require the gluing convention to use right multiplication, which contradicts the inherited
ordinary chart transition law.  So the global internal-group action is a *right* action, and
the inherited one-fibre *left* coordinate convention survives untouched inside each chart
(item 74): in chart `i` the point `ipsi i (b,a)` is moved to `ipsi i (b, a * h)`, while the
chart-to-chart comparison is still left multiplication by `u_ij(b)`.

**Package H (items 66–71).**  Fibres are identified with `Lift` chart by chart; the
identification is *not* canonical (item 69) — changing the chart changes it by the left
translation `u_ij(b)`.

**Package J (items 81–85).**  The action is free and transitive on every fibre, with the
required endpoint `internal_fibre_existsUnique_groupTransport`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask30

open NullSectorTask28 NullSectorTask29 Topology

universe u v w t

section Action

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {P : InternalProjection L G} {S : TransitionSystem B ι G}
  (T : CompatibleContinuousInternalTransitions P S)

/-! ## An extensionality principle for the glued carrier -/

/-- **DERIVED.**  Congruence for the local parametrizations. -/
theorem ipsi_congr (i : ι) {b b' : B} (hb : b ∈ S.U i) (hb' : b' ∈ S.U i) (a a' : L)
    (h : b = b') (h2 : a = a') :
    ipsi T i ((⟨b, hb⟩ : ↥(S.U i)), a) = ipsi T i ((⟨b', hb'⟩ : ↥(S.U i)), a') := by
  subst h
  subst h2
  rfl

/-- **DERIVED.**  Two points of the glued carrier lying over the same base point inside one
chart, with the same coordinate in that chart, are equal. -/
theorem internalTotal_ext (i : ι) {x y : InternalTotal T} (hx : internalBase T x ∈ S.U i)
    (hbase : internalBase T x = internalBase T y) (hc : icoord T i x = icoord T i y) : x = y := by
  have hy : internalBase T y ∈ S.U i := by rw [← hbase]; exact hx
  refine Eq.trans (ipsi_icoord T i x hx).symm (Eq.trans ?_ (ipsi_icoord T i y hy))
  exact ipsi_congr T i hx hy _ _ hbase hc

/-! ## Package I — the pre-quotient action and its descent -/

/-- **PACKAGE I (item 72), principal definition.**  The right action of the internal group on
the tagged local carrier. -/
def smulPre (x : InternalPre S L) (h : L) : InternalPre S L := ⟨x.1, x.2.1, x.2.2 * h⟩

omit [TopologicalSpace L] [IsTopologicalGroup L] in
@[simp] theorem smulPre_mk (i : ι) (b : ↥(S.U i)) (a h : L) :
    smulPre (⟨i, b, a⟩ : InternalPre S L) h = ⟨i, b, a * h⟩ := rfl

/-- **PACKAGE I (item 76), principal.**  The pre-quotient right action preserves the gluing
relation.  This is exactly the compatibility of right multiplication with the left
multiplication by the transitions. -/
theorem glueRel_smulPre {x y : InternalPre S L} (hr : InternalGlueRel T x y) (h : L) :
    InternalGlueRel T (smulPre x h) (smulPre y h) := by
  obtain ⟨i, ⟨b, hi⟩, a⟩ := x
  obtain ⟨j, ⟨b', hj⟩, a'⟩ := y
  have hb : b' = b := glueRel_pt_eq T hr
  subst hb
  rw [glueRel_iff_of_pt] at hr
  rw [smulPre_mk, smulPre_mk, glueRel_iff_of_pt, hr, mul_assoc]

/-- **PACKAGE I (item 77), principal definition.**  The descended global right action of the
internal group on the glued carrier. -/
def ismul (x : InternalTotal T) (h : L) : InternalTotal T :=
  Quotient.liftOn x (fun y => iq T (smulPre y h))
    fun _ _ hab => (iq_eq_iff T).2 (glueRel_smulPre T hab h)

@[simp] theorem ismul_iq (y : InternalPre S L) (h : L) :
    ismul T (iq T y) h = iq T (smulPre y h) := rfl

@[simp] theorem ismul_ipsi (i : ι) (p : ↥(S.U i) × L) (h : L) :
    ismul T (ipsi T i p) h = ipsi T i (p.1, p.2 * h) := rfl

/-- **PACKAGE I (item 78).**  Action identity law. -/
@[simp] theorem ismul_one (x : InternalTotal T) : ismul T x 1 = x := by
  induction x using iq_inductionOn with
  | h y => simp [smulPre]

/-- **PACKAGE I (item 78).**  Action composition law. -/
theorem ismul_mul (x : InternalTotal T) (h h' : L) :
    ismul T (ismul T x h) h' = ismul T x (h * h') := by
  induction x using iq_inductionOn with
  | h y => simp [smulPre, mul_assoc]

/-- **PACKAGE I (item 80), principal.**  The action preserves the base fibres. -/
@[simp] theorem internalBase_ismul (x : InternalTotal T) (h : L) :
    internalBase T (ismul T x h) = internalBase T x := by
  induction x using iq_inductionOn with
  | h y => rfl

@[simp] theorem icoord_ismul (i : ι) (x : InternalTotal T) (h : L)
    (hx : internalBase T x ∈ S.U i) :
    icoord T i (ismul T x h) = icoord T i x * h := by
  induction x using iq_inductionOn with
  | h y =>
    obtain ⟨j, ⟨b, hj⟩, a⟩ := y
    have hb : b ∈ S.U i := hx
    show icoord T i (iq T (⟨j, ⟨b, hj⟩, a * h⟩ : InternalPre S L))
        = icoord T i (iq T (⟨j, ⟨b, hj⟩, a⟩ : InternalPre S L)) * h
    rw [icoord_iq_of_mem T i j b hj hb, icoord_iq_of_mem T i j b hj hb, mul_assoc]

/-- **PACKAGE I (item 79), principal.**  The global action is continuous. -/
theorem continuous_ismul : Continuous fun p : InternalTotal T × L => ismul T p.1 p.2 := by
  have hq : IsQuotientMap fun p : InternalPre S L × L => (iq T p.1, p.2) :=
    IsOpenMap.isQuotientMap ((isOpenMap_iq T).prodMap IsOpenMap.id)
      ((continuous_iq T).prodMap continuous_id)
      (Function.Surjective.prodMap (iq_surjective T) Function.surjective_id)
  rw [hq.continuous_iff]
  have key : Continuous fun q : Σ i : ι, (↥(S.U i) × L) × L =>
      ipsi T q.1 (q.2.1.1, q.2.1.2 * q.2.2) := by
    refine continuous_sigma fun i => ?_
    exact (continuous_ipsi T i).comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).mul continuous_snd))
  exact key.comp
    (Homeomorph.sigmaProdDistrib (X := fun i : ι => ↥(S.U i) × L) (Y := L)).continuous

/-! ## Package H — the fibres -/

/-- **PACKAGE H (item 66), principal definition.**  The fibre of the glued carrier over a
base point. -/
def InternalFiber (b : B) : Set (InternalTotal T) := {x | internalBase T x = b}

theorem mem_internalFiber {b : B} {x : InternalTotal T} :
    x ∈ InternalFiber T b ↔ internalBase T x = b := Iff.rfl

/-- **PACKAGE H (item 70), principal.**  Every fibre is nonempty. -/
theorem internalFiber_nonempty (b : B) : (InternalFiber T b).Nonempty := by
  obtain ⟨i, hi⟩ := S.cover b
  exact ⟨ipsi T i (⟨b, hi⟩, 1), rfl⟩

/-- **PACKAGE H, principal — the chart comparison of coordinates in one fibre.**  The
coordinate read in chart `j` is the coordinate read in chart `i` multiplied on the left by
the inherited transition. -/
theorem icoord_chart_change (i j : ι) (x : InternalTotal T)
    (hi : internalBase T x ∈ S.U i) (hj : internalBase T x ∈ S.U j) :
    icoord T j x = uu T i j (internalBase T x) hi hj * icoord T i x := by
  induction x using iq_inductionOn with
  | h y =>
    obtain ⟨k, ⟨c, hk⟩, a⟩ := y
    have hci : c ∈ S.U i := hi
    have hcj : c ∈ S.U j := hj
    show icoord T j (iq T (⟨k, ⟨c, hk⟩, a⟩ : InternalPre S L))
        = uu T i j c hci hcj * icoord T i (iq T (⟨k, ⟨c, hk⟩, a⟩ : InternalPre S L))
    rw [icoord_iq_of_mem T j k c hk hcj, icoord_iq_of_mem T i k c hk hci, ← mul_assoc,
      uu_trans T k i j c hk hci hcj]

/-- **PACKAGE H, principal.**  The same statement at a named base point. -/
theorem icoord_chart_change_at (i j : ι) (b : B) (hi : b ∈ S.U i) (hj : b ∈ S.U j)
    (x : InternalTotal T) (hx : internalBase T x = b) :
    icoord T j x = uu T i j b hi hj * icoord T i x := by
  subst hx
  exact icoord_chart_change T i j x hi hj

/-- **PACKAGE H (item 67), principal.**  For any chart containing `b`, the fibre over `b` is
in bijection with the internal group.  **This identification is not canonical** (item 69): it
depends on the chart, see `fiberEquiv_chart_change`. -/
noncomputable def fiberEquiv (i : ι) (b : B) (hb : b ∈ S.U i) :
    ↥(InternalFiber T b) ≃ L where
  toFun x := icoord T i x.1
  invFun a := ⟨ipsi T i (⟨b, hb⟩, a), rfl⟩
  left_inv := by
    rintro ⟨x, hx⟩
    have hxb : internalBase T x = b := hx
    refine Subtype.ext ?_
    have hxi : internalBase T x ∈ S.U i := by rw [hxb]; exact hb
    exact Eq.trans (ipsi_congr T i hb hxi _ _ hxb.symm rfl) (ipsi_icoord T i x hxi)
  right_inv a := icoord_ipsi T i (⟨b, hb⟩, a)

@[simp] theorem fiberEquiv_apply (i : ι) (b : B) (hb : b ∈ S.U i) (x : ↥(InternalFiber T b)) :
    fiberEquiv T i b hb x = icoord T i x.1 := rfl

/-- **PACKAGE H (item 68), principal.**  Changing the chart changes the fibre identification
by the left translation determined by `u_ij(b)`. -/
theorem fiberEquiv_chart_change (i j : ι) (b : B) (hi : b ∈ S.U i) (hj : b ∈ S.U j)
    (x : ↥(InternalFiber T b)) :
    fiberEquiv T j b hj x = uu T i j b hi hj * fiberEquiv T i b hi x :=
  icoord_chart_change_at T i j b hi hj x.1 x.2

/-- **PACKAGE H (item 71), principal.**  Every fibre is a right `Lift`-set of the same
structural form as the one-fibre internal model: the fibre identification transports the
global action to right multiplication in `Lift`. -/
theorem fiberEquiv_ismul (i : ι) (b : B) (hb : b ∈ S.U i) (x : ↥(InternalFiber T b)) (h : L) :
    icoord T i (ismul T x.1 h) = fiberEquiv T i b hb x * h := by
  have hxb : internalBase T x.1 = b := x.2
  have hxi : internalBase T x.1 ∈ S.U i := by rw [hxb]; exact hb
  exact icoord_ismul T i x.1 h hxi

/-! ## Package J — freeness and fibrewise transitivity -/

/-- **PACKAGE J (items 83, 84), REQUIRED ENDPOINT
`internal_fibre_existsUnique_groupTransport`.**  Two points of the glued carrier over the
same base point differ by exactly one element of the internal group. -/
theorem internal_fibre_existsUnique_groupTransport (x y : InternalTotal T)
    (hxy : internalBase T x = internalBase T y) : ∃! a : L, ismul T x a = y := by
  obtain ⟨i, hi⟩ := S.cover (internalBase T x)
  refine ⟨(icoord T i x)⁻¹ * icoord T i y, ?_, ?_⟩
  · refine internalTotal_ext T i ?_ ?_ ?_
    · rw [internalBase_ismul]; exact hi
    · rw [internalBase_ismul]; exact hxy
    · rw [icoord_ismul T i x _ hi, mul_inv_cancel_left]
  · intro a ha
    have hc := congrArg (icoord T i) ha
    rw [icoord_ismul T i x a hi] at hc
    rw [← hc, inv_mul_cancel_left]

/-- **PACKAGE J (item 81), principal.**  The global action is free. -/
theorem ismul_free {x : InternalTotal T} {a : L} (h : ismul T x a = x) : a = 1 := by
  obtain ⟨_, _, huniq⟩ := internal_fibre_existsUnique_groupTransport T x x rfl
  exact (huniq a h).trans (huniq 1 (ismul_one T x)).symm

/-- **PACKAGE J (item 81), principal.**  Equivalent form: the action is injective in the
group variable. -/
theorem ismul_injective (x : InternalTotal T) : Function.Injective (ismul T x) := by
  intro a a' h
  obtain ⟨_, _, huniq⟩ :=
    internal_fibre_existsUnique_groupTransport T x (ismul T x a) (internalBase_ismul T x a).symm
  exact (huniq a rfl).trans (huniq a' h.symm).symm

/-- **PACKAGE J (item 82), principal.**  The action is transitive on every fibre. -/
theorem ismul_transitive_on_fiber (b : B) (x y : ↥(InternalFiber T b)) :
    ∃ a : L, ismul T x.1 a = y.1 := by
  have hxb : internalBase T x.1 = b := x.2
  have hyb : internalBase T y.1 = b := y.2
  exact (internal_fibre_existsUnique_groupTransport T x.1 y.1 (hxb.trans hyb.symm)).exists

/-- **NEGATIVE CONTROL (item 152).**  Freeness of the *local* model is not what is proved
here: the statement above is freeness of the descended action on the quotient, obtained from
the quotient-compatible transport in a chart. -/
theorem ismul_stabilizer_trivial (x : InternalTotal T) :
    {a : L | ismul T x a = x} = {1} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ⟨fun h => ismul_free T h, fun h => by rw [h, ismul_one]⟩

end Action

end NullSectorTask30
