import RequestProject.Spine.E2.Defect.LiftabilityPredicate

/-!
# Task 31, Packages A and B: the frozen Task-XXX global object and the surjectivity of `Π`

**HARD TARGET A (items 22–29).**

Package A (items 22, 23) contains **no new mathematics**: the Task-XXX conditional global
object is re-exposed exactly as it was frozen there, through the interface
`GluedInternalFrameSystem`, whose fields are the base projection, the local product charts,
the right `Lift` action upstairs, the right visible action downstairs, the map
`Π = toFrame`, its equivariance through `proj`, the fibrewise free transitive action and the
exact kernel-orbit characterization of equal `Π` images.  `globalObject_frozen_interface`
lists them in one statement.

Package B (items 24–29) is the first hard target:

* `OrdinaryFrameModel.ract_existsUnique` and `OrdinaryFrameSide.ract_existsUnique_fibre` —
  the *ordinary* fibrewise right action is free and transitive (derived from the inherited
  chart data, not assumed);
* `GluedInternalFrameSystem.toFrame_surjective` (REQUIRED ENDPOINT
  `internalToFrame_surjective`) — the preferred proof route of item 24 is followed literally:
  base surjectivity upstairs, transitivity of the ordinary action, surjectivity of
  `proj : Lift → GvisModel`, equivariance.  No cardinality argument is used (item 24.7);
* `toFrame_fibre_nonempty` (item 27) — every ordinary frame has a nonempty upstairs fibre;
* `toFrameFibreEquivKer`, `toFrame_fibre_torsor` (item 28) — the Task-XXX fibre theorem is
  strengthened from *points in the image* to **every** point of `FrameTotal`;
* `toFrame_fibre_card_two` (item 29) — two points per fibre for the certified two-element
  kernel.

Negative control 111 is respected: exact two-point fibres are *not* used to obtain
surjectivity; surjectivity is proved separately and first.

The new theorems about the inherited interfaces are placed in the inherited namespaces so
that they are available by dot notation.  **No Task-XXX source file is modified**: these are
new declarations in a new Task-XXXI module.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask30

open NullSectorTask28 NullSectorTask29

universe u v w t y z e

section Hardening

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {Fm : Type z} [TopologicalSpace Fm] [MulAction G Fm]

/-! ## The ordinary fibrewise action is free and transitive -/

namespace OrdinaryFrameModel

variable (M : OrdinaryFrameModel G Fm)

/-- **TASK-XXXI PACKAGE B, derived.**  The inherited right action on the model frame space is
transitive. -/
theorem ract_transitive (w w' : Fm) : ∃ k : G, M.ract w k = w' := by
  obtain ⟨l, rfl⟩ := M.exists_smul M.ref w
  obtain ⟨l', rfl⟩ := M.exists_smul M.ref w'
  refine ⟨l⁻¹ * l', ?_⟩
  calc M.ract (l • M.ref) (l⁻¹ * l') = l • M.ract M.ref (l⁻¹ * l') := M.ract_smul _ _ _
    _ = l • ((l⁻¹ * l') • M.ref) := by rw [M.ract_ref]
    _ = l' • M.ref := by rw [← mul_smul, mul_inv_cancel_left]

/-- **TASK-XXXI PACKAGE B, derived.**  The inherited right action on the model frame space is
free and transitive. -/
theorem ract_existsUnique (w w' : Fm) : ∃! k : G, M.ract w k = w' := by
  obtain ⟨k, hk⟩ := M.ract_transitive w w'
  exact ⟨k, hk, fun k' hk' => M.ract_right_injective w (hk'.trans hk.symm)⟩

end OrdinaryFrameModel

namespace OrdinaryFrameSide

variable {S : TransitionSystem B ι G} {M : OrdinaryFrameModel G Fm} {Tot : Type y}
  [TopologicalSpace Tot] (F : OrdinaryFrameSide S M Tot)

/-- **TASK-XXXI PACKAGE B, derived.**  Two ordinary frames over the same base point with the
same chart coordinate coincide. -/
theorem eq_of_chart (i : ι) {x y : Tot} (hx : F.base x ∈ S.U i) (hy : F.base y ∈ S.U i)
    (hb : F.base x = F.base y)
    (hc : (F.chart i ⟨x, hx⟩).2 = (F.chart i ⟨y, hy⟩).2) : x = y := by
  have hpair : F.chart i ⟨x, hx⟩ = F.chart i ⟨y, hy⟩ := by
    refine Prod.ext (Subtype.ext ?_) hc
    rw [F.chart_base i ⟨x, hx⟩, F.chart_base i ⟨y, hy⟩]
    exact hb
  exact congrArg Subtype.val ((F.chart i).injective hpair)

/-- **TASK-XXXI PACKAGE B (item 24.4), principal.**  The inherited fibrewise right action of
the visible group on the ordinary frame total space is free and transitive on every fibre. -/
theorem ract_existsUnique_fibre (x y : Tot) (hb : F.base x = F.base y) :
    ∃! k : G, F.ract x k = y := by
  obtain ⟨i, hi⟩ := S.cover (F.base x)
  have hyi : F.base y ∈ S.U i := by rw [← hb]; exact hi
  obtain ⟨k, hk, huniq⟩ :=
    M.ract_existsUnique (F.chart i ⟨x, hi⟩).2 (F.chart i ⟨y, hyi⟩).2
  have hcoord : ∀ k' : G, F.ract x k' = y →
      M.ract (F.chart i ⟨x, hi⟩).2 k' = (F.chart i ⟨y, hyi⟩).2 := by
    intro k' hk'
    have hbk : F.base (F.ract x k') ∈ S.U i := by rw [F.base_ract]; exact hi
    have hch := F.chart_ract i x k' hi hbk
    have hsub : (⟨F.ract x k', hbk⟩ : {z : Tot // F.base z ∈ S.U i}) = ⟨y, hyi⟩ :=
      Subtype.ext hk'
    rw [hsub] at hch
    exact hch.symm
  refine ⟨k, ?_, fun k' hk' => huniq k' (hcoord k' hk')⟩
  have hbk : F.base (F.ract x k) ∈ S.U i := by rw [F.base_ract]; exact hi
  refine F.eq_of_chart i hbk hyi ?_ ?_
  · rw [F.base_ract]; exact hb
  · rw [F.chart_ract i x k hi hbk]; exact hk

/-- **TASK-XXXI PACKAGE B.**  Transitivity of the ordinary fibrewise action, stated
separately. -/
theorem exists_ract (x y : Tot) (hb : F.base x = F.base y) : ∃ k : G, F.ract x k = y :=
  (F.ract_existsUnique_fibre x y hb).exists

end OrdinaryFrameSide

/-! ## Package B — surjectivity of the global map -/

namespace GluedInternalFrameSystem

variable {P : InternalProjection L G} {S : TransitionSystem B ι G}
  {M : OrdinaryFrameModel G Fm} {Tot : Type y} [TopologicalSpace Tot]
  {F : OrdinaryFrameSide S M Tot} {E : Type e} [TopologicalSpace E]
  (Q : GluedInternalFrameSystem P S M F E)

/-- **TASK-XXXI PACKAGE A (items 22, 23), the frozen interface in one statement.**  Nothing
new: the Task-XXX conditional global object, listed field by field — base projection, local
product charts over the ordinary cover, the right internal action, its continuity, freeness
and fibrewise transitivity, the global map `Π`, its continuity, its position over the base,
its equivariance through `proj`, and the exact kernel-orbit characterization of its
fibres. -/
theorem globalObject_frozen_interface :
    Continuous Q.base ∧ Function.Surjective Q.base ∧
      (∀ (i : ι) (x : {x : E // Q.base x ∈ S.U i}), ((Q.chart i x).1 : B) = Q.base (x : E)) ∧
      (∀ x : E, Q.act x 1 = x) ∧
      (∀ (x : E) (h h' : L), Q.act (Q.act x h) h' = Q.act x (h * h')) ∧
      (∀ (x : E) (h : L), Q.base (Q.act x h) = Q.base x) ∧
      Continuous (fun p : E × L => Q.act p.1 p.2) ∧
      (∀ x y : E, Q.base x = Q.base y → ∃! h : L, Q.act x h = y) ∧
      Continuous Q.toFrame ∧
      (∀ x : E, F.base (Q.toFrame x) = Q.base x) ∧
      (∀ (x : E) (h : L), Q.toFrame (Q.act x h) = F.ract (Q.toFrame x) (P.proj h)) ∧
      (∀ x y : E, Q.toFrame x = Q.toFrame y → ∃! z : P.Ker, Q.act x (z : L) = y) :=
  ⟨Q.continuous_base, Q.base_surjective, Q.chart_base, Q.act_one, Q.act_mul, Q.base_act,
    Q.continuous_act, Q.act_existsUnique, Q.continuous_toFrame, Q.toFrame_base,
    Q.toFrame_equivariant, Q.toFrame_fibre⟩

/-- **TASK-XXXI PACKAGE B, derived.**  Acting by a kernel element does not move the ordinary
frame image. -/
theorem toFrame_act_ker (x : E) {z : L} (hz : z ∈ P.Ker) :
    Q.toFrame (Q.act x z) = Q.toFrame x := by
  obtain ⟨i, hi⟩ := S.cover (Q.base x)
  have hb : F.base (Q.toFrame x) ∈ S.U i := by rw [Q.toFrame_base]; exact hi
  rw [Q.toFrame_equivariant, (P.mem_Ker_iff).1 hz, F.ract_one_of_chart _ i hb]

/-- **TASK-XXXI PACKAGE B (items 24, 25), REQUIRED ENDPOINT `internalToFrame_surjective`.**
The global map of the Task-XXX object is surjective onto the *whole* ordinary frame total
space.

The proof follows the prescribed route exactly: pick a point upstairs over the base point of
the target (surjectivity of the internal base projection), compare it with the target inside
one ordinary fibre (transitivity of the inherited ordinary action), lift the comparing
visible element along `proj` (surjectivity of the frozen projection) and transport by
equivariance.  No cardinality argument occurs. -/
theorem toFrame_surjective : Function.Surjective Q.toFrame := by
  intro y
  obtain ⟨x, hx⟩ := Q.base_surjective (F.base y)
  have hbase : F.base (Q.toFrame x) = F.base y := by rw [Q.toFrame_base, hx]
  obtain ⟨k, hk⟩ := F.exists_ract (Q.toFrame x) y hbase
  obtain ⟨a, ha⟩ := P.surjective_proj k
  exact ⟨Q.act x a, by rw [Q.toFrame_equivariant, ha, hk]⟩

/-- **TASK-XXXI PACKAGE B (item 27), REQUIRED ENDPOINT.**  Every ordinary frame has a nonempty
upstairs fibre. -/
theorem toFrame_fibre_nonempty (y : Tot) : ∃ x : E, Q.toFrame x = y := Q.toFrame_surjective y

/-- **TASK-XXXI PACKAGE B (item 28), REQUIRED ENDPOINT — the strengthened fibre theorem.**
Over **every** point of the ordinary frame total space the upstairs fibre is a nonempty free
transitive `P.Ker`-set: it is nonempty, and any two of its points differ by a unique kernel
element. -/
theorem toFrame_fibre_torsor (y : Tot) :
    (∃ x : E, Q.toFrame x = y) ∧
      ∀ x x' : E, Q.toFrame x = y → Q.toFrame x' = y → ∃! z : P.Ker, Q.act x (z : L) = x' :=
  ⟨Q.toFrame_fibre_nonempty y,
    fun x x' hx hx' => Q.toFrame_fibre x x' (hx.trans hx'.symm)⟩

/-- **TASK-XXXI PACKAGE B (item 28).**  The kernel acts on every fibre. -/
theorem mem_fibre_act_ker {y : Tot} {x : E} (hx : Q.toFrame x = y) (z : P.Ker) :
    Q.toFrame (Q.act x (z : L)) = y := (Q.toFrame_act_ker x z.2).trans hx

/-- **TASK-XXXI PACKAGE B (items 28, 29), the exact fibre theorem over an arbitrary ordinary
frame.**  Every fibre of the global map is in explicit bijection with the kernel of the frozen
internal projection. -/
noncomputable def toFrameFibreEquivKer (y : Tot) : {x : E // Q.toFrame x = y} ≃ P.Ker where
  toFun x := (Q.toFrame_fibre (Q.toFrame_surjective y).choose x.1
    ((Q.toFrame_surjective y).choose_spec.trans x.2.symm)).choose
  invFun z := ⟨Q.act (Q.toFrame_surjective y).choose (z : L),
    Q.mem_fibre_act_ker (Q.toFrame_surjective y).choose_spec z⟩
  left_inv x := Subtype.ext (Q.toFrame_fibre (Q.toFrame_surjective y).choose x.1
    ((Q.toFrame_surjective y).choose_spec.trans x.2.symm)).choose_spec.1
  right_inv z := by
    obtain ⟨-, huniq⟩ := (Q.toFrame_fibre (Q.toFrame_surjective y).choose
      (Q.act (Q.toFrame_surjective y).choose (z : L))
      ((Q.toFrame_surjective y).choose_spec.trans
        (Q.mem_fibre_act_ker (Q.toFrame_surjective y).choose_spec z).symm)).choose_spec
    exact (huniq z rfl).symm

/-- **TASK-XXXI PACKAGE B (item 29).**  Consequently the fibre over every ordinary frame has
exactly as many points as the kernel. -/
theorem toFrame_fibre_card (y : Tot) :
    Nat.card {x : E // Q.toFrame x = y} = Nat.card P.Ker :=
  Nat.card_congr (Q.toFrameFibreEquivKer y)

/-- **TASK-XXXI PACKAGE B (item 29), REQUIRED ENDPOINT.**  For the certified two-element
kernel, every fibre of the global map over **every** ordinary frame has exactly two
points. -/
theorem toFrame_fibre_card_two (y : Tot) (hker : Nat.card P.Ker = 2) :
    Nat.card {x : E // Q.toFrame x = y} = 2 := (Q.toFrame_fibre_card y).trans hker

end GluedInternalFrameSystem

end Hardening

end NullSectorTask30

/-! ## The endpoints for the Task-XXX construction itself -/

namespace NullSectorTask31

open NullSectorTask28 NullSectorTask29 NullSectorTask30

universe u v w t y z

section Constructed

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {Fm : Type z} [TopologicalSpace Fm] [MulAction G Fm] {P : InternalProjection L G}
  {S : TransitionSystem B ι G} {M : OrdinaryFrameModel G Fm} {Tot : Type y}
  [TopologicalSpace Tot] (T : CompatibleContinuousInternalTransitions P S)
  (F : OrdinaryFrameSide S M Tot)

/-- **PACKAGE B, REQUIRED ENDPOINT `internalToFrame_surjective`, on the Task-XXX carrier.**
The Task-XXX global map `Π : InternalTotal → FrameTotal` is surjective. -/
theorem internalToFrame_surjective : Function.Surjective (internalToFrame T F) :=
  (compatibleTransitions_construct_globalInternalFrameLift T F).toFrame_surjective

/-- **PACKAGE B (item 27), on the Task-XXX carrier.** -/
theorem internalToFrame_fibre_nonempty_over_every_frame (y : Tot) :
    ∃ x : InternalTotal T, internalToFrame T F x = y :=
  internalToFrame_surjective T F y

/-- **PACKAGE B (item 28), on the Task-XXX carrier.**  The fibre over **every** ordinary
frame — not only over frames in the image — is a nonempty `P.Ker`-torsor. -/
theorem internalToFrame_fibre_torsor_over_every_frame (y : Tot) :
    (∃ x : InternalTotal T, internalToFrame T F x = y) ∧
      ∀ x x' : InternalTotal T, internalToFrame T F x = y → internalToFrame T F x' = y →
        ∃! z : P.Ker, ismul T x (z : L) = x' :=
  (compatibleTransitions_construct_globalInternalFrameLift T F).toFrame_fibre_torsor y

/-- **PACKAGE B (item 29), on the Task-XXX carrier.** -/
theorem internalToFrame_fibre_card_two_over_every_frame (y : Tot) (hker : Nat.card P.Ker = 2) :
    Nat.card {x : InternalTotal T // internalToFrame T F x = y} = 2 :=
  (compatibleTransitions_construct_globalInternalFrameLift T F).toFrame_fibre_card_two y hker

end Constructed

end NullSectorTask31
