import RequestProject.Experiment2.NullSectorTask24.ReferenceIndependence

/-!
# Task 24, Packages G, H, I: the lifted frame carrier

**Hard target C.**

The lifted frame carrier is built from the already certified projection `projCore : Lift →
Gvis` of Task 21/23 and the intrinsic frame carrier of Package B.  It is *not* identified
definitionally with the internal carrier: an element is a pair (internal element, frame)
subject to the compatibility condition of item 48, using a temporary reference frame `F₀`.

* Package G (items 48–53): the carrier, its projection to `FramePlus`, surjectivity, exactly
  two representatives per frame, the exact `{±1}` relation between them, freeness of the
  kernel-sign action, and the quotient by that action recovered as `FramePlus` at the
  set/equivalence level.
* Package H (items 54–58): the construction repeated with a second reference frame, an
  explicit equivalence between the two lifted carriers, and its compatibility with the
  projection and with the kernel-sign action.
* Package I (items 59–64): the direct action of the internal carrier on `FramePlus`, its
  transitivity, its stabilizer (exactly the kernel signs) and the exact description of when
  two internal elements move a frame to the same place.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask24

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21 NullSectorTask23

/-! ## Kernel signs, restated in the packaged group -/

theorem mem_KerSign_iff' {e : LiftGrp} : e ∈ KerSign ↔ (e = 1 ∨ e = lNegOne) := by
  have h : e ∈ (KerSign : Set LiftG) ↔
      e ∈ ({⟨1, LiftG.one_mem⟩, ⟨WG.negOne, negOne_mem_LiftG⟩} : Set LiftG) := by
    rw [KerSign_eq]
  simpa [lNegOne] using h

theorem lNegOne_mem_KerSign : lNegOne ∈ KerSign := mem_KerSign_iff'.2 (Or.inr rfl)

theorem lNegOne_ne_one : lNegOne ≠ 1 := by
  intro h
  exact WG.negOne_ne_one (congrArg (fun u : LiftG => (u : WG)) h)

theorem lNegOne_central (u : LiftGrp) : lNegOne * u = u * lNegOne := by
  refine Subtype.ext (WG.ext ?_)
  show (-w1) ⋆ (u : WG).val = (u : WG).val ⋆ (-w1)
  rw [neg_mul_W, one_mul_W, mul_neg_W, mul_one_W]

theorem KerSign_central {e : LiftGrp} (he : e ∈ KerSign) (u : LiftGrp) : e * u = u * e := by
  rcases mem_KerSign_iff'.1 he with rfl | rfl
  · rw [one_mul, mul_one]
  · exact lNegOne_central u

theorem projCore_lNegOne : projCore lNegOne = 1 := MonoidHom.mem_ker.1 lNegOne_mem_KerSign

/-- **DERIVED.**  Two internal elements have the same visible image exactly when they differ
by a kernel sign.  This is the packaged form of the certified fibre description. -/
theorem projCore_eq_iff {u v : LiftGrp} :
    projCore u = projCore v ↔ ∃ e : LiftGrp, e ∈ KerSign ∧ v = e * u := by
  constructor
  · intro h
    refine ⟨v * u⁻¹, ?_, by group⟩
    show v * u⁻¹ ∈ projCore.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← h, mul_inv_cancel]
  · rintro ⟨e, he, rfl⟩
    rw [map_mul, MonoidHom.mem_ker.1 he, one_mul]

/-! ## Package G — the lifted frame carrier -/

/-- **NEWLY DEFINED (item 48), principal.**  The lifted frame carrier attached to a temporary
reference frame: pairs consisting of an internal element and a frame, subject to the exact
compatibility condition.  It is deliberately *not* the internal carrier by definition. -/
def LiftedFrame (F₀ : FramePlus) : Type :=
  {p : LiftGrp × FramePlus // projCore p.1 • F₀ = p.2}

namespace LiftedFrame

variable {F₀ : FramePlus}

/-- The internal component of a lifted frame. -/
def elt (x : LiftedFrame F₀) : LiftGrp := x.1.1

/-- The frame component of a lifted frame. -/
def frame (x : LiftedFrame F₀) : FramePlus := x.1.2

theorem spec (x : LiftedFrame F₀) : projCore x.elt • F₀ = x.frame := x.2

@[ext] theorem ext {x y : LiftedFrame F₀} (h : x.elt = y.elt) : x = y := by
  refine Subtype.ext (Prod.ext h ?_)
  show x.frame = y.frame
  rw [← x.spec, ← y.spec, show x.elt = y.elt from h]

/-- The lifted frame determined by an internal element. -/
noncomputable def mk (F₀ : FramePlus) (u : LiftGrp) : LiftedFrame F₀ :=
  ⟨(u, projCore u • F₀), rfl⟩

@[simp] theorem mk_elt (F₀ : FramePlus) (u : LiftGrp) : (mk F₀ u).elt = u := rfl

@[simp] theorem mk_frame (F₀ : FramePlus) (u : LiftGrp) :
    (mk F₀ u).frame = projCore u • F₀ := rfl

theorem mk_elt_self (x : LiftedFrame F₀) : mk F₀ x.elt = x := ext rfl

end LiftedFrame

/-- **PACKAGE G (item 49).**  The lifted frame projection onto the intrinsic frame carrier. -/
def liftedFrameProj (F₀ : FramePlus) (x : LiftedFrame F₀) : FramePlus := x.frame

@[simp] theorem liftedFrameProj_eq (F₀ : FramePlus) (x : LiftedFrame F₀) :
    liftedFrameProj F₀ x = x.frame := rfl

/-- **PACKAGE G, principal.**  The lifted frame projection is surjective. -/
theorem liftedFrameProj_surjective (F₀ : FramePlus) :
    Function.Surjective (liftedFrameProj F₀) := by
  intro F
  obtain ⟨u, hu⟩ := projCore_surjective (frameHom F₀ F)
  refine ⟨LiftedFrame.mk F₀ u, ?_⟩
  rw [liftedFrameProj_eq, LiftedFrame.mk_frame, hu, frameHom_smul]

theorem liftedFrameProj_eq_iff (F₀ : FramePlus) (x y : LiftedFrame F₀) :
    liftedFrameProj F₀ x = liftedFrameProj F₀ y ↔
      ∃ e : LiftGrp, e ∈ KerSign ∧ y.elt = e * x.elt := by
  rw [← projCore_eq_iff]
  simp only [liftedFrameProj_eq]
  constructor
  · intro h
    refine frameAction_cancel (F := F₀) ?_
    rw [x.spec, y.spec]
    exact h
  · intro h
    rw [← x.spec, ← y.spec, h]

/-! ### The kernel-sign action on lifted frames -/

/-- **NEWLY DEFINED (item 51).**  The action of a kernel sign on the lifted frame carrier:
it multiplies the internal component and leaves the frame unchanged. -/
def signSmul (F₀ : FramePlus) (e : KerSign) (x : LiftedFrame F₀) : LiftedFrame F₀ :=
  ⟨((e : LiftGrp) * x.elt, x.frame), by
    show projCore ((e : LiftGrp) * x.elt) • F₀ = x.frame
    rw [map_mul, MonoidHom.mem_ker.1 e.2, one_mul]
    exact x.spec⟩

instance (F₀ : FramePlus) : SMul KerSign (LiftedFrame F₀) := ⟨signSmul F₀⟩

@[simp] theorem signSmul_elt (F₀ : FramePlus) (e : KerSign) (x : LiftedFrame F₀) :
    (e • x).elt = (e : LiftGrp) * x.elt := rfl

@[simp] theorem signSmul_frame (F₀ : FramePlus) (e : KerSign) (x : LiftedFrame F₀) :
    (e • x).frame = x.frame := rfl

instance (F₀ : FramePlus) : MulAction KerSign (LiftedFrame F₀) where
  one_smul x := LiftedFrame.ext (by simp)
  mul_smul e f x := LiftedFrame.ext (by simp [mul_assoc])

/-- **PACKAGE G (item 52), principal.**  The kernel-sign action is free. -/
theorem signSmul_free (F₀ : FramePlus) {e : KerSign} {x : LiftedFrame F₀} (h : e • x = x) :
    e = 1 := by
  have hval : (e : LiftGrp) * x.elt = x.elt := congrArg LiftedFrame.elt h
  refine Subtype.ext ?_
  have h2 := congrArg (fun u : LiftGrp => u * x.elt⁻¹) hval
  simpa [mul_assoc] using h2

/-- **PACKAGE G (item 51), principal.**  Two lifted frames project to the same frame exactly
when they differ by a unique kernel sign. -/
theorem liftedFrame_eq_iff_sign (F₀ : FramePlus) (x y : LiftedFrame F₀) :
    liftedFrameProj F₀ x = liftedFrameProj F₀ y ↔ ∃! e : KerSign, y = e • x := by
  constructor
  · intro h
    obtain ⟨e, he, hy⟩ := (liftedFrameProj_eq_iff F₀ x y).1 h
    refine ⟨⟨e, he⟩, LiftedFrame.ext (by simpa using hy), fun f hf => ?_⟩
    have h1 : (f : LiftGrp) * x.elt = e * x.elt := by
      rw [← hy]
      exact (congrArg LiftedFrame.elt hf).symm
    refine Subtype.ext ?_
    have h2 := congrArg (fun u : LiftGrp => u * x.elt⁻¹) h1
    simpa [mul_assoc] using h2
  · rintro ⟨e, rfl, -⟩
    simp

/-- **PACKAGE G (item 50), principal.**  Every frame has exactly two lifted representatives:
they are exchanged by the nontrivial kernel sign. -/
theorem two_lifts (F₀ F : FramePlus) :
    ∃ x y : LiftedFrame F₀, x ≠ y ∧
      ∀ z : LiftedFrame F₀, liftedFrameProj F₀ z = F ↔ (z = x ∨ z = y) := by
  obtain ⟨x, hx⟩ := liftedFrameProj_surjective F₀ F
  refine ⟨x, (⟨lNegOne, lNegOne_mem_KerSign⟩ : KerSign) • x, ?_, ?_⟩
  · intro h
    exact lNegOne_ne_one (congrArg Subtype.val (signSmul_free F₀ h.symm))
  · intro z
    constructor
    · intro hz
      have hzx : liftedFrameProj F₀ x = liftedFrameProj F₀ z := by rw [hx, hz]
      obtain ⟨e, he, hze⟩ := (liftedFrameProj_eq_iff F₀ x z).1 hzx
      rcases mem_KerSign_iff'.1 he with rfl | rfl
      · exact Or.inl (LiftedFrame.ext (by simpa using hze))
      · exact Or.inr (LiftedFrame.ext (by simpa using hze))
    · rintro (rfl | rfl)
      · exact hx
      · simpa using hx

/-- **PACKAGE G (item 50).**  The same statement in cardinality form: every fibre of the
lifted frame projection has exactly two elements. -/
theorem lifted_fibre_ncard (F₀ F : FramePlus) :
    {x : LiftedFrame F₀ | liftedFrameProj F₀ x = F}.ncard = 2 := by
  obtain ⟨x, y, hxy, hz⟩ := two_lifts F₀ F
  have hset : {x' : LiftedFrame F₀ | liftedFrameProj F₀ x' = F} = {x, y} := by
    ext z
    simpa using hz z
  rw [hset, Set.ncard_pair hxy]

/-! ### The quotient by the kernel sign (item 53) -/

/-- The relation identifying the two lifted representatives of a frame. -/
def liftedSetoid (F₀ : FramePlus) : Setoid (LiftedFrame F₀) where
  r x y := liftedFrameProj F₀ x = liftedFrameProj F₀ y
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

theorem liftedSetoid_iff_sign (F₀ : FramePlus) (x y : LiftedFrame F₀) :
    (liftedSetoid F₀).r x y ↔ ∃ e : KerSign, y = e • x := by
  constructor
  · intro h
    obtain ⟨e, he, -⟩ := (liftedFrame_eq_iff_sign F₀ x y).1 h
    exact ⟨e, he⟩
  · rintro ⟨e, rfl⟩
    exact rfl

/-- **PACKAGE G (item 53), principal.**  The quotient of the lifted frame carrier by the
kernel-sign relation is exactly the intrinsic frame carrier, at the set/equivalence level. -/
noncomputable def liftedQuotientEquiv (F₀ : FramePlus) :
    Quotient (liftedSetoid F₀) ≃ FramePlus := by
  refine Equiv.ofBijective (Quotient.lift (liftedFrameProj F₀) fun _ _ h => h) ⟨?_, ?_⟩
  · refine fun a b => Quotient.inductionOn₂ a b ?_
    intro x y h
    exact Quotient.sound h
  · intro F
    obtain ⟨x, hx⟩ := liftedFrameProj_surjective F₀ F
    exact ⟨Quotient.mk _ x, hx⟩

/-- **PACKAGE I (items 63, 64).**  After a reference frame has been fixed, the lifted frame
carrier is in explicit bijection with the certified internal carrier: the internal component
is a complete invariant.  This is the strongest correct comparison — note that the *frame*
component alone is not, since the projection is two-to-one. -/
noncomputable def liftedEltEquiv (F₀ : FramePlus) : LiftedFrame F₀ ≃ LiftGrp where
  toFun := LiftedFrame.elt
  invFun := LiftedFrame.mk F₀
  left_inv x := LiftedFrame.mk_elt_self x
  right_inv _ := rfl

/-! ## Package H — removing the temporary reference frame -/

section Transfer

variable (F₀ F₁ : FramePlus) (u₀ : LiftGrp)

theorem inv_frameHom_smul : (frameHom F₀ F₁)⁻¹ • F₁ = F₀ := by
  rw [inv_smul_eq_iff]
  exact (frameHom_smul F₀ F₁).symm

/-- **NEWLY DEFINED (items 54, 55).**  The comparison map between the lifted frame carriers
built from two reference frames, given an internal element over the unique visible
transformation carrying the first reference frame to the second. -/
noncomputable def liftedTransfer (h₀ : projCore u₀ = frameHom F₀ F₁) :
    LiftedFrame F₀ ≃ LiftedFrame F₁ where
  toFun x := ⟨(x.elt * u₀⁻¹, x.frame), by
    show projCore (x.elt * u₀⁻¹) • F₁ = x.frame
    rw [map_mul, map_inv, h₀, mul_smul, inv_frameHom_smul]
    exact x.spec⟩
  invFun y := ⟨(y.elt * u₀, y.frame), by
    show projCore (y.elt * u₀) • F₀ = y.frame
    rw [map_mul, h₀, mul_smul, frameHom_smul]
    exact y.spec⟩
  left_inv x := LiftedFrame.ext (by
    show x.elt * u₀⁻¹ * u₀ = x.elt
    group)
  right_inv y := LiftedFrame.ext (by
    show y.elt * u₀ * u₀⁻¹ = y.elt
    group)

@[simp] theorem liftedTransfer_elt (h₀ : projCore u₀ = frameHom F₀ F₁) (x : LiftedFrame F₀) :
    (liftedTransfer F₀ F₁ u₀ h₀ x).elt = x.elt * u₀⁻¹ := rfl

/-- **PACKAGE H (item 56).**  The comparison map is compatible with the projections onto the
intrinsic frame carrier. -/
theorem liftedTransfer_proj (h₀ : projCore u₀ = frameHom F₀ F₁) (x : LiftedFrame F₀) :
    liftedFrameProj F₁ (liftedTransfer F₀ F₁ u₀ h₀ x) = liftedFrameProj F₀ x := by
  have h1 := (liftedTransfer F₀ F₁ u₀ h₀ x).spec
  rw [liftedTransfer_elt] at h1
  rw [liftedFrameProj_eq, liftedFrameProj_eq, ← h1, ← x.spec, map_mul, map_inv, h₀, mul_smul,
    inv_frameHom_smul]

/-- **PACKAGE H (item 57).**  The comparison map is compatible with the kernel-sign action. -/
theorem liftedTransfer_sign (h₀ : projCore u₀ = frameHom F₀ F₁) (e : KerSign)
    (x : LiftedFrame F₀) :
    liftedTransfer F₀ F₁ u₀ h₀ (e • x) = e • liftedTransfer F₀ F₁ u₀ h₀ x :=
  LiftedFrame.ext (by
    show (e : LiftGrp) * x.elt * u₀⁻¹ = (e : LiftGrp) * (x.elt * u₀⁻¹)
    rw [mul_assoc])

/-- **PACKAGE H (item 58).**  The comparison map depends on the chosen internal element over
the change-of-reference transformation only through a kernel sign: two choices give
comparison maps differing by the kernel-sign action. -/
theorem liftedTransfer_choice (u₀' : LiftGrp) (h₀ : projCore u₀ = frameHom F₀ F₁)
    (h₀' : projCore u₀' = frameHom F₀ F₁) :
    ∃ e : KerSign, ∀ x : LiftedFrame F₀,
      liftedTransfer F₀ F₁ u₀' h₀' x = e • liftedTransfer F₀ F₁ u₀ h₀ x := by
  obtain ⟨e, he, hu⟩ := projCore_eq_iff.1 (h₀.trans h₀'.symm)
  have hinvKer : e⁻¹ ∈ KerSign := Subgroup.inv_mem _ he
  have hee : e⁻¹ = e := by
    rcases mem_KerSign_iff'.1 he with rfl | rfl
    · simp
    · refine inv_eq_of_mul_eq_one_right (Subtype.ext (WG.ext ?_))
      show (-w1) ⋆ (-w1) = w1
      rw [neg_mul_W, mul_neg_W, one_mul_W, neg_neg]
  refine ⟨⟨e, he⟩, fun x => LiftedFrame.ext ?_⟩
  show x.elt * u₀'⁻¹ = e * (x.elt * u₀⁻¹)
  calc x.elt * u₀'⁻¹ = x.elt * (u₀⁻¹ * e⁻¹) := by rw [hu, mul_inv_rev]
    _ = (x.elt * u₀⁻¹) * e⁻¹ := (mul_assoc _ _ _).symm
    _ = e⁻¹ * (x.elt * u₀⁻¹) := (KerSign_central hinvKer _).symm
    _ = e * (x.elt * u₀⁻¹) := by rw [hee]

end Transfer

/-! ## Package I — the internal carrier acting directly on frames -/

/-- **NEWLY DEFINED (item 59).**  The action of the internal carrier on the intrinsic frame
carrier, through the certified projection. -/
noncomputable def lact (u : LiftGrp) (F : FramePlus) : FramePlus := projCore u • F

noncomputable instance : SMul LiftGrp FramePlus := ⟨lact⟩

@[simp] theorem lact_apply (u : LiftGrp) (F : FramePlus) : u • F = projCore u • F := rfl

noncomputable instance : MulAction LiftGrp FramePlus where
  one_smul F := by rw [lact_apply, map_one, one_smul]
  mul_smul u v F := by rw [lact_apply, lact_apply, lact_apply, map_mul, mul_smul]

/-- **PACKAGE I (item 60), principal.**  The internal action on frames is transitive. -/
theorem lact_transitive (F G : FramePlus) : ∃ u : LiftGrp, u • F = G := by
  obtain ⟨u, hu⟩ := projCore_surjective (frameHom F G)
  exact ⟨u, by rw [lact_apply, hu, frameHom_smul]⟩

/-- **PACKAGE I (item 61), principal.**  The stabilizer of any frame under the internal
action is exactly the kernel signs. -/
theorem lact_stabilizer (F : FramePlus) : MulAction.stabilizer LiftGrp F = KerSign := by
  ext u
  rw [MulAction.mem_stabilizer_iff, lact_apply]
  constructor
  · intro h
    show u ∈ projCore.ker
    exact MonoidHom.mem_ker.2 (frameAction_free h)
  · intro h
    rw [MonoidHom.mem_ker.1 h, one_smul]

/-- **PACKAGE I (item 62), principal.**  Two internal elements move a frame to the same place
exactly when they differ by a unique kernel sign. -/
theorem lact_eq_iff (u v : LiftGrp) (F : FramePlus) :
    u • F = v • F ↔ ∃! e : KerSign, v = (e : LiftGrp) * u := by
  constructor
  · intro h
    have hp : projCore u = projCore v := by
      refine frameAction_cancel (F := F) ?_
      rw [← lact_apply, ← lact_apply]
      exact h
    obtain ⟨e, he, hv⟩ := projCore_eq_iff.1 hp
    refine ⟨⟨e, he⟩, hv, fun f hf => ?_⟩
    refine Subtype.ext ?_
    have h1 : (f : LiftGrp) * u = e * u := by rw [← hf, hv]
    have h2 := congrArg (fun w : LiftGrp => w * u⁻¹) h1
    simpa [mul_assoc] using h2
  · rintro ⟨e, rfl, -⟩
    rw [lact_apply, lact_apply, map_mul, MonoidHom.mem_ker.1 e.2, one_mul]

/-- **PACKAGE I (item 64), negative control.**  The internal action on frames is *not* free:
the nontrivial kernel sign acts trivially on every frame.  Hence the strongest correct
formulation is the stabilizer statement above; the internal carrier is *not* a free
transitive object over the frame carrier. -/
theorem lact_not_free : ∃ u : LiftGrp, u ≠ 1 ∧ ∀ F : FramePlus, u • F = F :=
  ⟨lNegOne, lNegOne_ne_one, fun F => by rw [lact_apply, projCore_lNegOne, one_smul]⟩

end NullSectorTask24
