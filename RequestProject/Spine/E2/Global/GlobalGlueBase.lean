import RequestProject.Spine.E2.Descent.Task29

/-!
# Task 30, Package A: the frozen conditional input and the frozen ordinary frame side

**IMPORT LAYER (items 19–22).  No Task-XXIX (or earlier) source is edited and no inherited
statement is changed.**

Task XXX proceeds *conditionally*.  Everything below takes as given:

* a topological base `B` and an index type `ι`;
* an ordinary continuous transition system `S : TransitionSystem B ι G` (the Task-XXVII
  endpoint, re-exposed through the Task-XXVIII packaging);
* a frozen internal projection `P : InternalProjection L G` of topological groups, with its
  central discrete kernel `P.Ker` (the inherited `KerSign` in the certified instance);
* **the conditional input**: an object
  `T : CompatibleContinuousInternalTransitions P S` of the certified Task-XXIX type.

Task XXX **never** proves that such a `T` exists (items 5, 141–146).

This module only

* re-exposes the four inherited transition laws in the pointwise form used throughout
  (`uu_proj`, `uu_self`, `uu_symm`, `uu_trans`);
* records the elementary continuity statement for the internal transitions;
* freezes the *ordinary frame side* as two interfaces, `OrdinaryFrameModel` and
  `OrdinaryFrameSide`, whose fields are exactly the Task-XXVII data that Task XXX consumes:
  a local product chart over every `U i`, the ordinary transition law between two charts, and
  the inherited fibrewise right action of the visible group.

No new mathematics appears in Package A (item 22).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask30

open NullSectorTask28 NullSectorTask29

universe u v w t y z

section FrozenInput

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {P : InternalProjection L G} {S : TransitionSystem B ι G}

/-! ## The conditional input, read pointwise -/

/-- **PACKAGE A (item 20).**  The inherited internal transition map, read at a point of the
base together with the two membership proofs.  This is only a notational convenience: it is
literally `T.v i j` applied to the corresponding point of the subtype `↥(S.U i ∩ S.U j)`. -/
def uu (T : CompatibleContinuousInternalTransitions P S) (i j : ι) (b : B)
    (hi : b ∈ S.U i) (hj : b ∈ S.U j) : L :=
  T.v i j ⟨b, hi, hj⟩

variable (T : CompatibleContinuousInternalTransitions P S)

/-- **PACKAGE A (item 20), inherited law.**  `proj (u_ij) = g_ij`. -/
theorem uu_proj (i j : ι) (b : B) (hi : b ∈ S.U i) (hj : b ∈ S.U j) :
    P.proj (uu T i j b hi hj) = S.g i j ⟨b, hi, hj⟩ :=
  T.proj_v i j ⟨b, hi, hj⟩

/-- **PACKAGE A (item 20), inherited law.**  `u_ii = 1`. -/
theorem uu_self (i : ι) (b : B) (hi hi' : b ∈ S.U i) : uu T i i b hi hi' = 1 :=
  T.v_self i ⟨b, hi, hi'⟩

/-- **PACKAGE A (item 20), inherited law.**  `u_ji = u_ij⁻¹`. -/
theorem uu_symm (i j : ι) (b : B) (hi : b ∈ S.U i) (hj : b ∈ S.U j) :
    uu T j i b hj hi = (uu T i j b hi hj)⁻¹ :=
  T.v_symm i j ⟨b, hi, hj⟩

/-- **PACKAGE A (item 20), inherited law.**  `u_jk * u_ij = u_ik`, with the exact inherited
orientation of the indices. -/
theorem uu_trans (i j k : ι) (b : B) (hi : b ∈ S.U i) (hj : b ∈ S.U j) (hk : b ∈ S.U k) :
    uu T j k b hj hk * uu T i j b hi hj = uu T i k b hi hk :=
  T.v_trans i j k ⟨b, ⟨hi, hj⟩, hk⟩

/-- **PACKAGE A.**  Continuity of the internal transition maps, in the subtype form in which
Task XXIX proved it. -/
theorem continuous_uu (i j : ι) : Continuous (T.v i j) := T.continuous_v i j

end FrozenInput

/-! ## The frozen ordinary frame side -/

section FrameSide

variable {G : Type v} [Group G] [TopologicalSpace G]

/-- **PACKAGE K (items 86–88), frozen interface, no new mathematics.**  The *ordinary frame
model*: the fixed model frame space on which the visible group acts.  Its fields are exactly
the inherited Task-XXVI/XXVII facts about the model frame space:

* the visible group acts continuously on the left (this is the side on which the ordinary
  chart transitions act, `frameTrivAt j = g_ij • frameTrivAt i`);
* that action is free and transitive;
* the inherited *right* action of the visible group on frames;
* a reference model frame `ref` for which the two actions agree, `ract ref k = k • ref`.

Nothing here is constructed by Task XXX. -/
structure OrdinaryFrameModel (G : Type v) [Group G] [TopologicalSpace G] (Fm : Type z)
    [TopologicalSpace Fm] [MulAction G Fm] where
  /-- The left action of the visible group on the model frame space is continuous. -/
  continuous_smul : Continuous fun p : G × Fm => p.1 • p.2
  /-- The left action is free and transitive. -/
  smul_existsUnique : ∀ w w' : Fm, ∃! k : G, k • w = w'
  /-- The inherited right action of the visible group on the model frame space. -/
  ract : Fm → G → Fm
  /-- Right-action identity law. -/
  ract_one : ∀ w : Fm, ract w 1 = w
  /-- Right-action composition law. -/
  ract_mul : ∀ (w : Fm) (k l : G), ract (ract w k) l = ract w (k * l)
  /-- The reference model frame. -/
  ref : Fm
  /-- At the reference frame the two actions agree. -/
  ract_ref : ∀ k : G, ract ref k = k • ref

namespace OrdinaryFrameModel

variable {Fm : Type z} [TopologicalSpace Fm] [MulAction G Fm]

/-- **DERIVED.**  The left action is transitive. -/
theorem exists_smul (M : OrdinaryFrameModel G Fm) (w w' : Fm) : ∃ k : G, k • w = w' :=
  (M.smul_existsUnique w w').exists

/-- **DERIVED.**  The left action is free. -/
theorem smul_left_injective (M : OrdinaryFrameModel G Fm) {w : Fm} {k l : G}
    (h : k • w = l • w) : k = l := by
  obtain ⟨_, _, huniq⟩ := M.smul_existsUnique w (k • w)
  exact (huniq k rfl).trans (huniq l h.symm).symm

/-- **DERIVED (items 73, 100) — the exact conversion between the two actions.**  The right
action commutes with the left action.  This is *derived*, not assumed: every model frame is
`k • ref`, and on `ref` the two actions agree. -/
theorem ract_smul (M : OrdinaryFrameModel G Fm) (k : G) (w : Fm) (h : G) :
    M.ract (k • w) h = k • M.ract w h := by
  obtain ⟨l, rfl⟩ := M.exists_smul M.ref w
  have hl : M.ract (l • M.ref) h = (l * h) • M.ref := by
    rw [← M.ract_ref l, M.ract_mul, M.ract_ref]
  have hkl : M.ract ((k * l) • M.ref) h = (k * l * h) • M.ref := by
    rw [← M.ract_ref (k * l), M.ract_mul, M.ract_ref]
  rw [← mul_smul, hkl, hl, ← mul_smul, mul_assoc]

/-- **DERIVED.**  The right action is free. -/
theorem ract_right_injective (M : OrdinaryFrameModel G Fm) (w : Fm) {k l : G}
    (h : M.ract w k = M.ract w l) : k = l := by
  obtain ⟨m, rfl⟩ := M.exists_smul M.ref w
  rw [M.ract_smul, M.ract_smul, M.ract_ref, M.ract_ref, ← mul_smul, ← mul_smul] at h
  exact mul_left_cancel (M.smul_left_injective h)

end OrdinaryFrameModel

/-! ### The ordinary frame total space -/

variable {B : Type u} [TopologicalSpace B] {ι : Type t}

/-- **PACKAGE K (items 86–88), frozen interface, no new mathematics.**  The *ordinary frame
side*: the already reconstructed ordinary frame total space, exactly as Task XXVII left it —
a topological total space over the base, one local product chart over each domain of the
inherited cover, the inherited transition law between two charts, and the inherited fibrewise
right action of the visible group.  Task XXX only *consumes* these fields. -/
structure OrdinaryFrameSide (S : TransitionSystem B ι G) {Fm : Type z} [TopologicalSpace Fm]
    [MulAction G Fm] (M : OrdinaryFrameModel G Fm) (Tot : Type y) [TopologicalSpace Tot] where
  /-- The ordinary base projection. -/
  base : Tot → B
  /-- It is continuous. -/
  continuous_base : Continuous base
  /-- The inherited local product chart over `U i`. -/
  chart : ∀ i : ι, {x : Tot // base x ∈ S.U i} ≃ₜ ↥(S.U i) × Fm
  /-- The chart is a chart *over the base*. -/
  chart_base : ∀ (i : ι) (x : {x : Tot // base x ∈ S.U i}),
    ((chart i x).1 : B) = base (x : Tot)
  /-- The inherited ordinary transition law between two charts. -/
  chart_trans : ∀ (i j : ι) (x : Tot) (hi : base x ∈ S.U i) (hj : base x ∈ S.U j),
    (chart j ⟨x, hj⟩).2 = S.g i j ⟨base x, hi, hj⟩ • (chart i ⟨x, hi⟩).2
  /-- The inherited fibrewise right action of the visible group. -/
  ract : Tot → G → Tot
  /-- It preserves the base point. -/
  base_ract : ∀ (x : Tot) (k : G), base (ract x k) = base x
  /-- In every chart it is the model right action on the fibre coordinate. -/
  chart_ract : ∀ (i : ι) (x : Tot) (k : G) (h : base x ∈ S.U i)
    (h' : base (ract x k) ∈ S.U i),
    (chart i ⟨ract x k, h'⟩).2 = M.ract (chart i ⟨x, h⟩).2 k

namespace OrdinaryFrameSide

variable {S : TransitionSystem B ι G} {Fm : Type z} [TopologicalSpace Fm] [MulAction G Fm]
  {M : OrdinaryFrameModel G Fm} {Tot : Type y} [TopologicalSpace Tot]
  (F : OrdinaryFrameSide S M Tot)

/-- The local product parametrization of the ordinary frame total space attached to `U i`. -/
def psi (i : ι) (p : ↥(S.U i) × Fm) : Tot := ((F.chart i).symm p : Tot)

theorem continuous_psi (i : ι) : Continuous (F.psi i) :=
  continuous_subtype_val.comp (F.chart i).symm.continuous

theorem base_psi (i : ι) (p : ↥(S.U i) × Fm) : F.base (F.psi i p) = (p.1 : B) := by
  have h := F.chart_base i ((F.chart i).symm p)
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

theorem psi_mem (i : ι) (p : ↥(S.U i) × Fm) : F.base (F.psi i p) ∈ S.U i := by
  rw [F.base_psi]; exact p.1.2

/-- **DERIVED.**  The chart inverts the local parametrization. -/
theorem chart_psi (i : ι) (p : ↥(S.U i) × Fm) (h : F.base (F.psi i p) ∈ S.U i) :
    F.chart i ⟨F.psi i p, h⟩ = p := by
  have : (⟨F.psi i p, h⟩ : {x : Tot // F.base x ∈ S.U i}) = (F.chart i).symm p := rfl
  rw [this, Homeomorph.apply_symm_apply]

/-- **DERIVED.**  Every point over `U i` is in the image of the `i`-th parametrization. -/
theorem psi_chart (i : ι) (x : Tot) (h : F.base x ∈ S.U i) :
    F.psi i (F.chart i ⟨x, h⟩) = x := by
  show ((F.chart i).symm (F.chart i ⟨x, h⟩) : Tot) = x
  rw [Homeomorph.symm_apply_apply]

/-- **DERIVED.**  The parametrizations are injective. -/
theorem psi_injective (i : ι) : Function.Injective (F.psi i) := by
  intro p q hpq
  have h1 : ((F.chart i).symm p : Tot) = ((F.chart i).symm q : Tot) := hpq
  have h2 : (F.chart i).symm p = (F.chart i).symm q := Subtype.ext h1
  simpa using congrArg (F.chart i) h2

end OrdinaryFrameSide

end FrameSide

end NullSectorTask30
