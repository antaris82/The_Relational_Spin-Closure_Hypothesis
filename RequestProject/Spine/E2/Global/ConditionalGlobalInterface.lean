import RequestProject.Spine.E2.Global.LocalComparison

/-!
# Task 30, Packages S, T, U and V: the conditional global interface, the construction
theorem, the converse extraction test, and the exact conditionality statement

**Package S (items 129–131).**  `GluedInternalFrameSystem` packages the completed object.
Every field is a property that has been *independently proved* in the preceding modules
(item 131), and the name is deliberately neutral: no conventional global structure name is
used inside the intrinsic reconstruction (items 17, 130).

**Package T (items 132–135).**  `compatibleTransitions_construct_globalInternalFrameLift`:
from a `CompatibleContinuousInternalTransitions` input a `GluedInternalFrameSystem` is
constructed.  Nothing is claimed about absolute uniqueness (item 135).

**Package U (items 136–140).**  The converse extraction test.  From a
`GluedInternalFrameSystem` **plus** the extra chart datum that its internal charts are
adapted to the inherited ordinary frame charts through the one-fibre map, continuous internal
transitions are recovered and proved to satisfy all four inherited laws.  The extra datum is
*necessary* and is stated explicitly (item 139): the interface alone fixes the internal
transitions only up to the choice of the local frame reference, so the projection identity
`proj (w_ij) = g_ij` is not available without it.

**Package V (items 141–144), mandatory.**  The whole of Task XXX is conditional on
`Nonempty (CompatibleContinuousInternalTransitions P S)`.  Nothing here derives that
assumption from the ordinary frame family; the exact boundary is recorded in
`task30_conditionality`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask30

open NullSectorTask28 NullSectorTask29 Topology

universe u v w t y z e

section Interface

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {Fm : Type z} [TopologicalSpace Fm] [MulAction G Fm]

/-- **PACKAGE S (items 129–131), principal interface.**  The completed conditional global
object.  Neutral name on purpose (items 17, 130): no conventional global structure name is
introduced, and no field is asserted that has not been independently proved. -/
structure GluedInternalFrameSystem (P : InternalProjection L G) (S : TransitionSystem B ι G)
    (M : OrdinaryFrameModel G Fm) {Tot : Type y} [TopologicalSpace Tot]
    (F : OrdinaryFrameSide S M Tot) (E : Type e) [TopologicalSpace E] where
  /-- The projection to the base. -/
  base : E → B
  /-- It is continuous. -/
  continuous_base : Continuous base
  /-- It is surjective. -/
  base_surjective : Function.Surjective base
  /-- The local product charts. -/
  chart : ∀ i : ι, {x : E // base x ∈ S.U i} ≃ₜ ↥(S.U i) × L
  /-- The charts are charts over the base. -/
  chart_base : ∀ (i : ι) (x : {x : E // base x ∈ S.U i}), ((chart i x).1 : B) = base (x : E)
  /-- The global internal-group action (a right action, as derived in Package I). -/
  act : E → L → E
  /-- Action identity law. -/
  act_one : ∀ x : E, act x 1 = x
  /-- Action composition law. -/
  act_mul : ∀ (x : E) (h h' : L), act (act x h) h' = act x (h * h')
  /-- The action preserves fibres. -/
  base_act : ∀ (x : E) (h : L), base (act x h) = base x
  /-- The action is continuous. -/
  continuous_act : Continuous fun p : E × L => act p.1 p.2
  /-- In every chart the action is right multiplication. -/
  chart_act : ∀ (i : ι) (x : E) (h : L) (hx : base x ∈ S.U i) (hx' : base (act x h) ∈ S.U i),
    (chart i ⟨act x h, hx'⟩).2 = (chart i ⟨x, hx⟩).2 * h
  /-- The action is free and transitive on every fibre. -/
  act_existsUnique : ∀ x y : E, base x = base y → ∃! h : L, act x h = y
  /-- The global map to the ordinary frame total space. -/
  toFrame : E → Tot
  /-- It is continuous. -/
  continuous_toFrame : Continuous toFrame
  /-- It lies over the base. -/
  toFrame_base : ∀ x : E, F.base (toFrame x) = base x
  /-- It is equivariant along `proj`. -/
  toFrame_equivariant : ∀ (x : E) (h : L),
    toFrame (act x h) = F.ract (toFrame x) (P.proj h)
  /-- Its fibres are exactly the kernel orbits, freely and transitively. -/
  toFrame_fibre : ∀ x y : E, toFrame x = toFrame y → ∃! z : P.Ker, act x (z : L) = y

variable {P : InternalProjection L G} {S : TransitionSystem B ι G}
  {M : OrdinaryFrameModel G Fm} {Tot : Type y} [TopologicalSpace Tot]

/-! ## Package T — the conditional construction theorem -/

/-- **PACKAGE T (items 132, 133), REQUIRED ENDPOINT
`compatibleTransitions_construct_globalInternalFrameLift`.**  Given the conditional
Task-XXIX input, the glued carrier with all its structure is a `GluedInternalFrameSystem`.
Every field is one of the theorems proved in the preceding modules. -/
noncomputable def compatibleTransitions_construct_globalInternalFrameLift
    (T : CompatibleContinuousInternalTransitions P S) (F : OrdinaryFrameSide S M Tot) :
    GluedInternalFrameSystem P S M F (InternalTotal T) where
  base := internalBase T
  continuous_base := continuous_internalBase T
  base_surjective := internalBase_surjective T
  chart := internalChart T
  chart_base := fun _ _ => rfl
  act := ismul T
  act_one := ismul_one T
  act_mul := ismul_mul T
  base_act := internalBase_ismul T
  continuous_act := continuous_ismul T
  chart_act := fun i x h hx _ => icoord_ismul T i x h hx
  act_existsUnique := internal_fibre_existsUnique_groupTransport T
  toFrame := internalToFrame T F
  continuous_toFrame := continuous_internalToFrame T F
  toFrame_base := internalToFrame_over_base T F
  toFrame_equivariant := internalToFrame_equivariant T F
  toFrame_fibre := internalToFrame_fibre_kerSign_torsor T F

/-- **PACKAGE T (item 132), existence form.**  From the conditional input a global object
exists. -/
theorem exists_gluedInternalFrameSystem_of_compatibleTransitions
    (F : OrdinaryFrameSide S M Tot)
    (h : Nonempty (CompatibleContinuousInternalTransitions P S)) :
    ∃ (E : Type max u w t) (_ : TopologicalSpace E),
      Nonempty (GluedInternalFrameSystem P S M F E) := by
  obtain ⟨T⟩ := h
  exact ⟨InternalTotal T, inferInstance,
    ⟨compatibleTransitions_construct_globalInternalFrameLift T F⟩⟩

/-! ## Package U — the converse extraction test -/

variable {E : Type e} [TopologicalSpace E] {F : OrdinaryFrameSide S M Tot}

namespace GluedInternalFrameSystem

variable (Q : GluedInternalFrameSystem P S M F E)

/-- The chart coordinate of a point in a chart containing its base point. -/
def coord (i : ι) (x : E) (hx : Q.base x ∈ S.U i) : L := (Q.chart i ⟨x, hx⟩).2

/-- The distinguished local point of chart `i` over a point of `U i`: the one whose `i`-th
coordinate is the neutral element. -/
def localUnit (i : ι) (b : ↥(S.U i)) : E := ((Q.chart i).symm (b, 1) : E)

theorem base_localUnit (i : ι) (b : ↥(S.U i)) : Q.base (Q.localUnit i b) = (b : B) := by
  have h := Q.chart_base i ((Q.chart i).symm (b, 1))
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

theorem localUnit_mem (i : ι) (b : ↥(S.U i)) : Q.base (Q.localUnit i b) ∈ S.U i := by
  rw [Q.base_localUnit]; exact b.2

theorem coord_localUnit (i : ι) (b : ↥(S.U i)) :
    Q.coord i (Q.localUnit i b) (Q.localUnit_mem i b) = 1 := by
  have : (⟨Q.localUnit i b, Q.localUnit_mem i b⟩ : {x : E // Q.base x ∈ S.U i})
      = (Q.chart i).symm (b, 1) := rfl
  show (Q.chart i ⟨Q.localUnit i b, Q.localUnit_mem i b⟩).2 = 1
  rw [this, Homeomorph.apply_symm_apply]

/-- Two points over the same base point with the same coordinate in one chart are equal. -/
theorem eq_of_coord_eq (i : ι) {x y : E} (hx : Q.base x ∈ S.U i) (hy : Q.base y ∈ S.U i)
    (hb : Q.base x = Q.base y) (hc : Q.coord i x hx = Q.coord i y hy) : x = y := by
  have hpair : Q.chart i ⟨x, hx⟩ = Q.chart i ⟨y, hy⟩ := by
    refine Prod.ext (Subtype.ext ?_) hc
    rw [Q.chart_base i ⟨x, hx⟩, Q.chart_base i ⟨y, hy⟩]
    exact hb
  exact congrArg Subtype.val ((Q.chart i).injective hpair)

/-- Every point over `U i` is obtained from the distinguished local point by the action. -/
theorem act_localUnit_coord (i : ι) (x : E) (hx : Q.base x ∈ S.U i) :
    Q.act (Q.localUnit i ⟨Q.base x, hx⟩) (Q.coord i x hx) = x := by
  set y := Q.localUnit i ⟨Q.base x, hx⟩ with hy
  have hby : Q.base y = Q.base x := Q.base_localUnit i ⟨Q.base x, hx⟩
  have hyi : Q.base y ∈ S.U i := by rw [hby]; exact hx
  have hact : Q.base (Q.act y (Q.coord i x hx)) ∈ S.U i := by rw [Q.base_act]; exact hyi
  refine Q.eq_of_coord_eq i hact hx ?_ ?_
  · rw [Q.base_act]; exact hby
  · show (Q.chart i ⟨Q.act y (Q.coord i x hx), hact⟩).2 = Q.coord i x hx
    rw [Q.chart_act i y (Q.coord i x hx) hyi hact]
    show Q.coord i y hyi * Q.coord i x hx = Q.coord i x hx
    have : Q.coord i y hyi = 1 := Q.coord_localUnit i ⟨Q.base x, hx⟩
    rw [this, one_mul]

/-- **PACKAGE U (item 136), the recovered internal transition maps.** -/
def extractedTransition (i j : ι) (x : ↥(S.U i ∩ S.U j)) : L :=
  Q.coord j (Q.localUnit i ⟨(x : B), x.2.1⟩)
    (by rw [Q.base_localUnit]; exact x.2.2)

/-- **PACKAGE U.**  The recovered maps do describe the chart change. -/
theorem coord_eq_extracted_mul (i j : ι) (x : E) (hi : Q.base x ∈ S.U i)
    (hj : Q.base x ∈ S.U j) :
    Q.coord j x hj
      = Q.extractedTransition i j ⟨Q.base x, hi, hj⟩ * Q.coord i x hi := by
  have hx := Q.act_localUnit_coord i x hi
  set y := Q.localUnit i ⟨Q.base x, hi⟩ with hy
  have hby : Q.base y = Q.base x := Q.base_localUnit i ⟨Q.base x, hi⟩
  have hyj : Q.base y ∈ S.U j := by rw [hby]; exact hj
  have hact : Q.base (Q.act y (Q.coord i x hi)) ∈ S.U j := by rw [Q.base_act]; exact hyj
  have hchart := Q.chart_act j y (Q.coord i x hi) hyj hact
  have hsub : (⟨x, hj⟩ : {z : E // Q.base z ∈ S.U j})
      = ⟨Q.act y (Q.coord i x hi), hact⟩ := Subtype.ext hx.symm
  have hxj : Q.coord j x hj = Q.coord j (Q.act y (Q.coord i x hi)) hact := by
    show (Q.chart j ⟨x, hj⟩).2 = (Q.chart j ⟨Q.act y (Q.coord i x hi), hact⟩).2
    rw [hsub]
  rw [hxj]
  exact hchart

/-- **PACKAGE U (item 137).**  Identity law of the recovered transitions. -/
theorem extractedTransition_self (i : ι) (x : ↥(S.U i ∩ S.U i)) :
    Q.extractedTransition i i x = 1 :=
  Q.coord_localUnit i ⟨(x : B), x.2.1⟩

/-- **PACKAGE U (item 137).**  The exact triple-overlap law of the recovered
transitions. -/
theorem extractedTransition_trans (i j k : ι) (b : B) (hi : b ∈ S.U i) (hj : b ∈ S.U j)
    (hk : b ∈ S.U k) :
    Q.extractedTransition j k ⟨b, hj, hk⟩ * Q.extractedTransition i j ⟨b, hi, hj⟩
      = Q.extractedTransition i k ⟨b, hi, hk⟩ := by
  set y := Q.localUnit i ⟨b, hi⟩ with hy
  have hby : Q.base y = b := Q.base_localUnit i ⟨b, hi⟩
  have hyj : Q.base y ∈ S.U j := by rw [hby]; exact hj
  have hyk : Q.base y ∈ S.U k := by rw [hby]; exact hk
  have hmain := Q.coord_eq_extracted_mul j k y hyj hyk
  have h1 : (⟨Q.base y, hyj, hyk⟩ : ↥(S.U j ∩ S.U k)) = ⟨b, hj, hk⟩ := Subtype.ext hby
  rw [h1] at hmain
  have h2 : Q.coord j y hyj = Q.extractedTransition i j ⟨b, hi, hj⟩ := rfl
  have h3 : Q.coord k y hyk = Q.extractedTransition i k ⟨b, hi, hk⟩ := rfl
  rw [h2, h3] at hmain
  exact hmain.symm

/-- **PACKAGE U (item 137).**  Inverse law of the recovered transitions. -/
theorem extractedTransition_symm (i j : ι) (b : B) (hi : b ∈ S.U i) (hj : b ∈ S.U j) :
    Q.extractedTransition j i ⟨b, hj, hi⟩ = (Q.extractedTransition i j ⟨b, hi, hj⟩)⁻¹ := by
  have h := Q.extractedTransition_trans i j i b hi hj hi
  rw [Q.extractedTransition_self i ⟨b, hi, hi⟩] at h
  exact eq_inv_of_mul_eq_one_left h

/-- **PACKAGE U (item 137).**  Continuity of the recovered transitions. -/
theorem continuous_extractedTransition (i j : ι) : Continuous (Q.extractedTransition i j) := by
  have h1 : Continuous fun x : ↥(S.U i ∩ S.U j) => ((⟨(x : B), x.2.1⟩ : ↥(S.U i)), (1 : L)) :=
    (continuous_subtype_val.subtype_mk _).prodMk continuous_const
  have h2 : Continuous fun x : ↥(S.U i ∩ S.U j) => Q.localUnit i ⟨(x : B), x.2.1⟩ :=
    continuous_subtype_val.comp ((Q.chart i).symm.continuous.comp h1)
  have h3 : Continuous fun x : ↥(S.U i ∩ S.U j) =>
      (⟨Q.localUnit i ⟨(x : B), x.2.1⟩,
        (by rw [Q.base_localUnit]; exact x.2.2 :
          Q.base (Q.localUnit i ⟨(x : B), x.2.1⟩) ∈ S.U j)⟩ :
        {z : E // Q.base z ∈ S.U j}) := h2.subtype_mk _
  exact continuous_snd.comp ((Q.chart j).continuous.comp h3)

/-- **PACKAGE U (item 139), the extra chart datum, stated explicitly.**  The interface alone
does not determine the projection of the recovered transitions: one must also know that the
internal charts are *adapted* to the inherited ordinary frame charts through the certified
one-fibre map `a ↦ proj(a) • ref`. -/
def AdaptedCharts (Q : GluedInternalFrameSystem P S M F E) : Prop :=
  ∀ (i : ι) (x : E) (hx : Q.base x ∈ S.U i) (hb : F.base (Q.toFrame x) ∈ S.U i),
    (F.chart i ⟨Q.toFrame x, hb⟩).2 = P.proj (Q.coord i x hx) • M.ref

/-- **PACKAGE U (item 137).**  With the extra chart datum, the recovered transitions project
onto the inherited ordinary transitions. -/
theorem proj_extractedTransition (hA : Q.AdaptedCharts) (i j : ι) (x : ↥(S.U i ∩ S.U j)) :
    P.proj (Q.extractedTransition i j x) = S.g i j x := by
  set y := Q.localUnit i ⟨(x : B), x.2.1⟩ with hy
  have hby : Q.base y = (x : B) := Q.base_localUnit i ⟨(x : B), x.2.1⟩
  have hyi : Q.base y ∈ S.U i := by rw [hby]; exact x.2.1
  have hyj : Q.base y ∈ S.U j := by rw [hby]; exact x.2.2
  have hfb : F.base (Q.toFrame y) = (x : B) := (Q.toFrame_base y).trans hby
  have hfi : F.base (Q.toFrame y) ∈ S.U i := by rw [hfb]; exact x.2.1
  have hfj : F.base (Q.toFrame y) ∈ S.U j := by rw [hfb]; exact x.2.2
  have hci : Q.coord i y hyi = 1 := Q.coord_localUnit i ⟨(x : B), x.2.1⟩
  have hei := hA i y hyi hfi
  have hej := hA j y hyj hfj
  rw [hci, map_one, one_smul] at hei
  have htrans := F.chart_trans i j (Q.toFrame y) hfi hfj
  rw [hei, hej] at htrans
  have hpt : (⟨F.base (Q.toFrame y), hfi, hfj⟩ : ↥(S.U i ∩ S.U j)) = x := Subtype.ext hfb
  rw [hpt] at htrans
  have hcj : Q.coord j y hyj = Q.extractedTransition i j x := rfl
  rw [hcj] at htrans
  exact M.smul_left_injective htrans

/-- **PACKAGE U (item 138), the converse extraction theorem.**  A global object satisfying
the frozen interface, **together with the extra adapted-chart datum**, recovers a compatible
normalized continuous internal transition system — the Task-XXIX input. -/
def extractedTransitions (hA : Q.AdaptedCharts) :
    CompatibleContinuousInternalTransitions P S where
  v := Q.extractedTransition
  continuous_v := Q.continuous_extractedTransition
  proj_v := Q.proj_extractedTransition hA
  v_self := Q.extractedTransition_self
  v_symm := fun i j x => Q.extractedTransition_symm i j (x : B) x.2.1 x.2.2
  v_trans := fun i j k x => Q.extractedTransition_trans i j k (x : B) x.2.1.1 x.2.1.2 x.2.2

end GluedInternalFrameSystem

/-! ## Package V — the exact conditionality statement -/

/-- **PACKAGE V (items 141–144), MANDATORY.**  The exact conditionality boundary of Task XXX,
recorded formally.

*Proved conditionally*: a compatible normalized continuous internal transition system yields a
global glued internal object over the inherited ordinary frame total space.

*Still open*: whether the ordinary transition system admits such a compatible internal
transition system at all.  Nothing in Task XXX derives the assumption; it appears as the
hypothesis `Nonempty (CompatibleContinuousInternalTransitions P S)` and nowhere else. -/
theorem task30_conditionality (F : OrdinaryFrameSide S M Tot)
    (h : Nonempty (CompatibleContinuousInternalTransitions P S)) :
    ∃ (E : Type max u w t) (_ : TopologicalSpace E),
      Nonempty (GluedInternalFrameSystem P S M F E) :=
  exists_gluedInternalFrameSystem_of_compatibleTransitions F h

/-- **PACKAGE V.**  The two-way reading of the Task-XXIX boundary, imported unchanged: the
conditional input of Task XXX is exactly the solvability of the internally derived kernel
equations.  Task XXX proves *neither* side of this equivalence; it only consumes the right
one. -/
theorem task30_input_is_task29_boundary (C : InternalTransitionCandidate P S) :
    CanTrivialiseSimultaneously P S C ↔
      Nonempty (CompatibleContinuousInternalTransitions P S) :=
  canTrivialiseSimultaneously_iff_exists_compatible_transitions C

end Interface

end NullSectorTask30
