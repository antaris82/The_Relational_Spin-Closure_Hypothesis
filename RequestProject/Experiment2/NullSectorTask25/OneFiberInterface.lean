import RequestProject.Experiment2.NullSectorTask25.ReferenceTransferHardening

/-!
# Task 25, Packages K and M: the frozen one-fibre interface, and the neutral future input

* Package K (items 71–75): a compact record `OneFiberLiftInterface` containing **only already
  proved data** — the carriers, the two actions, the projection, its equivariance, and the
  exact kernel description of its fibres.  The record contains *intrinsic* data only; the
  *temporary presentation* data (a chosen reference frame, a chosen lift of a reference
  change) are kept in separate records, so that the distinction required by item 72 is visible
  in the types.  Item 73 is the theorem that two temporary reference frames give equivalent
  interfaces; no quotient over all choices is attempted (item 74).

* Package M (items 79–85): a neutral record `FiberFamilyInput` naming the *minimum input* of a
  future varying-fibre problem.  It is deliberately **not instantiated**, no local triviality
  is proved, no bundle, no transition function and no topology is introduced; the record only
  makes the first missing node explicit.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask25

open NullSectorTask20 NullSectorTask21 NullSectorTask23 NullSectorTask24

/-! ## Package K — the intrinsic one-fibre interface -/

/-- **PACKAGE K (item 71), principal.**  The frozen one-fibre interface.  Every field is an
already proved Task-24/Task-25 statement; nothing new is asserted here.

*Intrinsic data* (item 72): the two carriers, the internal action, the projection, and the
kernel description of the fibres.  The *temporary presentation* data are **not** fields of
this record; they appear only in `ReferencePresentation` and `LiftChoice` below. -/
structure OneFiberLiftInterface where
  /-- The lifted carrier. -/
  Carrier : Type
  /-- The internal action upstairs. -/
  act : LiftGrp → Carrier → Carrier
  /-- The projection to the ordinary frame carrier. -/
  proj : Carrier → FramePlus
  nonempty : Nonempty Carrier
  act_one : ∀ x, act 1 x = x
  act_mul : ∀ a b x, act (a * b) x = act a (act b x)
  act_free : ∀ a x, act a x = x → a = 1
  act_transitive : ∀ x y, ∃ a, act a x = y
  proj_equivariant : ∀ a x, proj (act a x) = projCore a • proj x
  proj_surjective : Function.Surjective proj
  /-- The fibres of the projection are exactly the `KerSign`-orbits. -/
  kerSign_fibre : ∀ x y, proj x = proj y ↔ ∃ e : KerSign, act (e : LiftGrp) x = y
  /-- Downstairs, the visible action is free and transitive (the inherited Task-24 torsor
  statement, carried along in the interface). -/
  downstairs_free_transitive : ∀ F G : FramePlus, ∃! g : Gvis, g • F = G

/-- **DERIVED.**  The unique internal element between two elements of an interface carrier. -/
theorem OneFiberLiftInterface.existsUnique (I : OneFiberLiftInterface) (x y : I.Carrier) :
    ∃! a : LiftGrp, I.act a x = y := by
  obtain ⟨a, ha⟩ := I.act_transitive x y
  refine ⟨a, ha, fun b hb => ?_⟩
  have h : I.act (a⁻¹ * b) x = x := by
    rw [I.act_mul, hb, ← ha, ← I.act_mul, inv_mul_cancel, I.act_one]
  have := I.act_free _ _ h
  rw [inv_mul_eq_one] at this
  exact this.symm

/-- **PACKAGE K (item 72).**  *Temporary presentation data*, part one: a chosen reference
frame.  It is deliberately not a field of `OneFiberLiftInterface`. -/
structure ReferencePresentation where
  /-- The temporarily chosen reference frame. -/
  refFrame : FramePlus

/-- **PACKAGE K (item 72).**  *Temporary presentation data*, part two: a chosen lift of the
unique downstairs reference change between two reference frames. -/
structure LiftChoice (F₀ F₁ : FramePlus) where
  /-- The chosen internal lift. -/
  lift : LiftGrp
  /-- It lies over the unique downstairs reference change. -/
  isLift : projCore lift = frameHom F₀ F₁

/-- **DERIVED.**  A lift choice always exists — but it is never unique (there are exactly
two, by `liftsOf_reference_change_ncard`). -/
noncomputable def someLiftChoice (F₀ F₁ : FramePlus) : LiftChoice F₀ F₁ :=
  ⟨(projCore_surjective (frameHom F₀ F₁)).choose,
    (projCore_surjective (frameHom F₀ F₁)).choose_spec⟩

/-- **PACKAGE K (item 71), principal endpoint.**  The one-fibre interface attached to a
temporary reference frame.  All fields are the theorems proved in Packages B–F. -/
noncomputable def oneFiberInterface (F₀ : FramePlus) : OneFiberLiftInterface where
  Carrier := LiftedFrame F₀
  act a x := a • x
  proj x := liftedFrameProj F₀ x
  nonempty := ⟨NullSectorTask24.LiftedFrame.mk F₀ 1⟩
  act_one := liftSmul_one F₀
  act_mul := liftSmul_mul F₀
  act_free _ _ h := liftedFrameAction_free F₀ h
  act_transitive := liftedFrameAction_transitive F₀
  proj_equivariant := liftedFrameProj_equivariant F₀
  proj_surjective := liftedFrameProj_surjective F₀
  kerSign_fibre x y := by
    constructor
    · intro h
      obtain ⟨⟨e, he, -⟩, -⟩ := fibre_free_transitive_kerSign F₀ x y h
      exact ⟨e, he.symm⟩
    · rintro ⟨e, rfl⟩
      exact (kerSign_trivial_downstairs F₀ e x).symm
  downstairs_free_transitive := existsUnique_gvis_map_frame

@[simp] theorem oneFiberInterface_act (F₀ : FramePlus) (a : LiftGrp) (x : LiftedFrame F₀) :
    (oneFiberInterface F₀).act a x = a • x := rfl

@[simp] theorem oneFiberInterface_proj (F₀ : FramePlus) (x : LiftedFrame F₀) :
    (oneFiberInterface F₀).proj x = liftedFrameProj F₀ x := rfl

/-- **PACKAGE K.**  In the standard model, the restriction of the interface action to the
kernel is *exactly* the inherited Task-24 sign action.  (This is model-specific data, so it is
recorded as a theorem about `oneFiberInterface` rather than as an interface field.) -/
theorem oneFiberInterface_kerSign_eq_signSmul (F₀ : FramePlus) (e : KerSign)
    (x : LiftedFrame F₀) : (oneFiberInterface F₀).act (e : LiftGrp) x = signSmul F₀ e x :=
  liftSmul_restrict_kerSign_eq_signSmul F₀ e x

/-! ### Equivalence of interfaces and reference independence -/

/-- **PACKAGE K (item 73).**  An equivalence of one-fibre interfaces: an equivalence of
carriers intertwining the internal actions and commuting with the projections. -/
structure InterfaceEquiv (I J : OneFiberLiftInterface) where
  /-- The underlying equivalence of carriers. -/
  toEquiv : I.Carrier ≃ J.Carrier
  /-- It intertwines the two internal actions. -/
  map_act : ∀ (a : LiftGrp) (x : I.Carrier), toEquiv (I.act a x) = J.act a (toEquiv x)
  /-- It commutes with the two projections. -/
  map_proj : ∀ x : I.Carrier, J.proj (toEquiv x) = I.proj x

/-- **PACKAGE K (item 73), principal endpoint.**  Changing the temporary reference frame
yields an equivalent one-fibre interface.  The equivalence is built from a *chosen* lift of
the unique downstairs reference change: by Package J the two possible choices differ by
exactly one kernel sign, so the equivalence is canonical only up to that classified `Z₂`
ambiguity (item 75: a reference-independence theorem, not a quotient). -/
noncomputable def oneFiberInterfaceEquiv (F₀ F₁ : FramePlus) (c : LiftChoice F₀ F₁) :
    InterfaceEquiv (oneFiberInterface F₀) (oneFiberInterface F₁) where
  toEquiv := liftedTransfer F₀ F₁ c.lift c.isLift
  map_act := liftedTransfer_equivariant F₀ F₁ c.lift c.isLift
  map_proj := liftedTransfer_proj F₀ F₁ c.lift c.isLift

/-- **PACKAGE K (item 73), principal endpoint.**  Reference independence of the frozen
interface, in existential form. -/
theorem oneFiberInterface_reference_independent (F₀ F₁ : FramePlus) :
    Nonempty (InterfaceEquiv (oneFiberInterface F₀) (oneFiberInterface F₁)) :=
  ⟨oneFiberInterfaceEquiv F₀ F₁ (someLiftChoice F₀ F₁)⟩

/-- **PACKAGE K.**  The residual ambiguity of the interface equivalence, restated at
interface level: two lift choices give underlying maps differing by exactly one kernel
sign. -/
theorem oneFiberInterfaceEquiv_ambiguity (F₀ F₁ : FramePlus) (c d : LiftChoice F₀ F₁) :
    ∃! e : KerSign, ∀ x : LiftedFrame F₀,
      liftedTransfer F₀ F₁ d.lift d.isLift x
        = (e : LiftGrp) • liftedTransfer F₀ F₁ c.lift c.isLift x :=
  liftedTransfer_difference_unique_kerSign F₀ F₁ c.lift d.lift c.isLift d.isLift

/-- **PACKAGE K.**  The underlying map of the interface equivalence is the inherited transfer
map attached to the chosen lift. -/
theorem oneFiberInterfaceEquiv_toEquiv (F₀ F₁ : FramePlus) (c : LiftChoice F₀ F₁) :
    (oneFiberInterfaceEquiv F₀ F₁ c).toEquiv = liftedTransfer F₀ F₁ c.lift c.isLift := rfl

/-! ## Package M — the neutral statement of the first missing Task-XXVI node -/

/-- **PACKAGE M (item 79).**  A neutral record naming the *minimum input* of a future
varying-fibre problem: a base type, a fibre assignment, and fibrewise metric and orientation
data.  It is **not instantiated** anywhere (item 80), no local triviality is claimed (item
81), no bundle (item 82), no transition function (item 83), and no topology (item 84): the
record exists only to make the first missing node explicit (item 85). -/
structure FiberFamilyInput where
  /-- The base type. -/
  B : Type
  /-- The fibre assignment. -/
  Fib : B → Type
  /-- Fibrewise metric data. -/
  metric : ∀ b, Fib b → Fib b → ℝ
  /-- Fibrewise orientation data, as a predicate on ordered triples. -/
  orientation : ∀ b, (Fin 3 → Fib b) → Prop

/-- **PACKAGE M (item 85).**  The dependency statement attached to the record: what Task 25
has frozen is exactly the one-fibre situation, i.e. the degenerate case of a fibre family
over a one-point base with *no* additional structure recorded.  This theorem asserts only
that the Task-25 interface data exist for every reference frame; it does **not** construct a
family over a nontrivial base, a total space, a projection to a base, a trivialization or a
transition function. -/
theorem one_fibre_only (F₀ : FramePlus) :
    Nonempty ((oneFiberInterface F₀).Carrier) ∧
      (∀ x y : (oneFiberInterface F₀).Carrier, ∃! a : LiftGrp,
        (oneFiberInterface F₀).act a x = y) :=
  ⟨(oneFiberInterface F₀).nonempty, (oneFiberInterface F₀).existsUnique⟩

end NullSectorTask25
