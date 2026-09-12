import RequestProject.Experiment2.NullSectorTask25.LiftedFrameAction

/-!
# Task 25, Packages E, F, G: equivariance, the kernel restriction, and the carrier equivalence

**Hard target B**, together with the strengthening of the Task-24 carrier equivalence.

* Package E (items 36–39): the lifted frame projection is equivariant along `projCore`, and
  the commuting square is recorded as a plain theorem equality — no categorical machinery.
* Package F (items 40–46): restricting the new internal action to the kernel gives *exactly*
  the inherited Task-24 kernel-sign action; kernel signs act trivially downstairs and freely
  upstairs.  The two-element fibre theorem of Task 24 is **not** rebuilt: it is used as a
  black box and only recombined with the restriction theorem.
* Package G (items 47–51): the inherited carrier equivalence `liftedEltEquiv : LiftedFrame F₀
  ≃ LiftGrp` is proved equivariant for the new action and left multiplication, so that the
  free/transitive structure upstairs is *compatible with* the intrinsic action rather than
  merely transported along a bijection.

The negative controls of items 86–88 are proved at the end of the file.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask25

open NullSectorTask20 NullSectorTask21 NullSectorTask23 NullSectorTask24

/-! ## Package E — projection equivariance (items 36–39) -/

/-- **PACKAGE E (item 37), principal endpoint.**  The lifted frame projection is equivariant:
acting upstairs by `a` and projecting is the same as projecting and acting downstairs by
`projCore a`. -/
theorem liftedFrameProj_equivariant (F₀ : FramePlus) (a : LiftGrp) (x : LiftedFrame F₀) :
    liftedFrameProj F₀ (a • x) = projCore a • liftedFrameProj F₀ x := rfl

/-- **PACKAGE E (item 38).**  The commuting square

```
LiftGrp × LiftedFrame F₀ --action--> LiftedFrame F₀
      |                                    |
 projCore × π                              π
      |                                    |
      v                                    v
Gvis × FramePlus         --action-->     FramePlus
```

as a plain equality of the two composites. -/
theorem liftedFrame_commuting_square (F₀ : FramePlus) :
    (fun p : LiftGrp × LiftedFrame F₀ => liftedFrameProj F₀ (p.1 • p.2))
      = fun p : LiftGrp × LiftedFrame F₀ => projCore p.1 • liftedFrameProj F₀ p.2 :=
  funext fun p => liftedFrameProj_equivariant F₀ p.1 p.2

/-- **PACKAGE E.**  The same statement in the notation of the inherited internal action on
ordinary frames (`u • F = projCore u • F`). -/
theorem liftedFrameProj_equivariant' (F₀ : FramePlus) (a : LiftGrp) (x : LiftedFrame F₀) :
    liftedFrameProj F₀ (a • x) = a • liftedFrameProj F₀ x := rfl

/-! ## Package F — the kernel restriction is exactly the inherited sign action -/

/-- **PACKAGE F (item 42), principal endpoint.**  Restricting the new internal action to the
kernel `KerSign` gives exactly the inherited Task-24 kernel-sign action. -/
theorem liftSmul_restrict_kerSign_eq_signSmul (F₀ : FramePlus) (e : KerSign)
    (x : LiftedFrame F₀) : (e : LiftGrp) • x = signSmul F₀ e x :=
  NullSectorTask24.LiftedFrame.ext rfl

/-- **PACKAGE F (item 42).**  The same statement with the inherited `KerSign`-scalar
notation. -/
theorem liftSmul_coe_kerSign (F₀ : FramePlus) (e : KerSign) (x : LiftedFrame F₀) :
    (e : LiftGrp) • x = e • x :=
  NullSectorTask24.LiftedFrame.ext rfl

/-- **PACKAGE F (item 45), principal endpoint.**  Kernel signs act trivially after projection
to the ordinary frame carrier. -/
theorem kerSign_trivial_downstairs (F₀ : FramePlus) (e : KerSign) (x : LiftedFrame F₀) :
    liftedFrameProj F₀ ((e : LiftGrp) • x) = liftedFrameProj F₀ x := by
  rw [liftedFrameProj_equivariant, MonoidHom.mem_ker.1 e.2, one_smul]

/-- **PACKAGE F (item 46), principal endpoint.**  No nontrivial kernel sign acts trivially
upstairs.  Together with the previous theorem this is the exact algebraic distinction between
the ordinary and the lifted frame carriers. -/
theorem kerSign_free_upstairs (F₀ : FramePlus) {e : KerSign} {x : LiftedFrame F₀}
    (h : (e : LiftGrp) • x = x) : e = 1 :=
  Subtype.ext (liftedFrameAction_free F₀ h)

/-- **PACKAGE F (item 46).**  In particular the nontrivial kernel sign moves every lifted
frame, while it fixes every ordinary frame. -/
theorem lNegOne_moves_liftedFrame (F₀ : FramePlus) (x : LiftedFrame F₀) :
    lNegOne • x ≠ x ∧ ∀ F : FramePlus, lNegOne • F = F := by
  refine ⟨fun h => lNegOne_ne_one (liftedFrameAction_free F₀ h), fun F => ?_⟩
  rw [lact_apply, projCore_lNegOne, one_smul]

/-- **PACKAGE F (item 43), corollary — *not* a new construction.**  Every fibre of the lifted
frame projection is a free and transitive `KerSign`-set.  Transitivity on the fibre is the
inherited Task-24 fibre theorem, read through the restriction theorem above; freeness is the
restriction of the new freeness upstairs. -/
theorem fibre_free_transitive_kerSign (F₀ : FramePlus) (x y : LiftedFrame F₀)
    (h : liftedFrameProj F₀ x = liftedFrameProj F₀ y) :
    (∃! e : KerSign, y = (e : LiftGrp) • x) ∧
      (∀ e : KerSign, (e : LiftGrp) • x = x → e = 1) := by
  obtain ⟨e, he, huniq⟩ := (liftedFrame_eq_iff_sign F₀ x y).1 h
  refine ⟨⟨e, ?_, fun f hf => huniq f ?_⟩, fun e he' => kerSign_free_upstairs F₀ he'⟩
  · show y = (e : LiftGrp) • x
    rw [liftSmul_restrict_kerSign_eq_signSmul]
    exact he
  · show y = signSmul F₀ f x
    rw [← liftSmul_restrict_kerSign_eq_signSmul]
    exact hf

/-! ## Package G — the inherited carrier equivalence is equivariant -/

/-- **PACKAGE G (item 49), principal endpoint.**  The inherited Task-24 equivalence
`liftedEltEquiv F₀ : LiftedFrame F₀ ≃ LiftGrp` is equivariant with respect to the new
internal action upstairs and left multiplication on `LiftGrp`. -/
theorem liftedEltEquiv_equivariant (F₀ : FramePlus) (a : LiftGrp) (x : LiftedFrame F₀) :
    liftedEltEquiv F₀ (a • x) = a * liftedEltEquiv F₀ x := rfl

/-- **PACKAGE G.**  The inverse direction. -/
theorem liftedEltEquiv_symm_equivariant (F₀ : FramePlus) (a u : LiftGrp) :
    (liftedEltEquiv F₀).symm (a * u) = a • (liftedEltEquiv F₀).symm u := by
  refine (liftedEltEquiv F₀).injective ?_
  rw [Equiv.apply_symm_apply, liftedEltEquiv_equivariant, Equiv.apply_symm_apply]

/-- **PACKAGE G (items 50, 51), principal endpoint.**  The packaged statement: the inherited
carrier equivalence is an equivalence of `LiftGrp`-sets.  The free/transitive structure
upstairs is therefore *compatible with* the intrinsic action, not merely inferred from a
bijection of carriers. -/
theorem liftedEltEquiv_equivariant_pair (F₀ : FramePlus) :
    (∀ (a : LiftGrp) (x : LiftedFrame F₀), liftedEltEquiv F₀ (a • x) = a * liftedEltEquiv F₀ x)
      ∧ ∀ (a u : LiftGrp),
        (liftedEltEquiv F₀).symm (a * u) = a • (liftedEltEquiv F₀).symm u :=
  ⟨liftedEltEquiv_equivariant F₀, liftedEltEquiv_symm_equivariant F₀⟩

/-! ## Negative controls (items 86–88) -/

/-- **AUXILIARY.**  There is an internal element outside the kernel; equivalently, the
projection is not trivial.  (Both facts are inherited: nontriviality of the visible carrier
and surjectivity of the certified projection.) -/
theorem exists_notMem_kerSign : ∃ u : LiftGrp, u ∉ KerSign := by
  obtain ⟨g, hg⟩ := exists_nontrivial_gvis
  obtain ⟨u, hu⟩ := projCore_surjective g
  exact ⟨u, fun hmem => hg (by rw [← hu, MonoidHom.mem_ker.1 hmem])⟩

/-- **NEGATIVE CONTROL (item 86).**  Non-freeness of the internal action on the *ordinary*
frame carrier does not propagate upstairs: the same group acts freely on the lifted carrier
and non-freely downstairs, and both statements are proved here side by side. -/
theorem free_upstairs_not_free_downstairs (F₀ : FramePlus) :
    (∀ (a : LiftGrp) (x : LiftedFrame F₀), a • x = x → a = 1) ∧
      ¬ ∀ (a : LiftGrp) (F : FramePlus), a • F = F → a = 1 := by
  refine ⟨fun _ _ h => liftedFrameAction_free F₀ h, fun hfree => ?_⟩
  obtain ⟨a, ha, hfix⟩ := lact_not_free
  exact ha (hfree a coordFrame (hfix coordFrame))

open scoped Classical in
/-- **NEGATIVE CONTROL (item 87).**  A bijection of carriers `LiftedFrame F₀ ≃ LiftGrp` does
*not* by itself prove equivariance: there is an explicit bijection between the same two
carriers which fails the equivariance identity satisfied by `liftedEltEquiv`. -/
theorem exists_nonequivariant_carrier_equiv (F₀ : FramePlus) :
    ∃ f : LiftedFrame F₀ ≃ LiftGrp,
      ¬ ∀ (a : LiftGrp) (x : LiftedFrame F₀), f (a • x) = a * f x := by
  obtain ⟨u, hu⟩ := exists_notMem_kerSign
  have hu1 : u ≠ 1 := fun h => hu (h ▸ Subgroup.one_mem _)
  have huneg : lNegOne ≠ u := fun h => hu (h ▸ lNegOne_mem_KerSign)
  refine ⟨(liftedEltEquiv F₀).trans (Equiv.swap 1 u), fun hall => ?_⟩
  have h := hall lNegOne (NullSectorTask24.LiftedFrame.mk F₀ 1)
  have hlhs : Equiv.swap (1 : LiftGrp) u (lNegOne * 1) = lNegOne := by
    rw [mul_one]
    exact Equiv.swap_apply_of_ne_of_ne lNegOne_ne_one huneg
  have hrhs : Equiv.swap (1 : LiftGrp) u 1 = u := Equiv.swap_apply_left 1 u
  rw [show ((liftedEltEquiv F₀).trans (Equiv.swap 1 u))
        (lNegOne • NullSectorTask24.LiftedFrame.mk F₀ 1)
      = Equiv.swap (1 : LiftGrp) u (lNegOne * 1) from rfl, hlhs,
    show ((liftedEltEquiv F₀).trans (Equiv.swap 1 u)) (NullSectorTask24.LiftedFrame.mk F₀ 1)
      = Equiv.swap (1 : LiftGrp) u 1 from rfl, hrhs] at h
  exact hu1 (by simpa using h.symm)

/-- **NEGATIVE CONTROL (item 88).**  A two-element fibre is not by itself a torsor statement:
the full internal action does not even preserve the fibres of the lifted frame projection, so
the fibre theorem of Task 24 says nothing about the `LiftGrp`-action.  Only the kernel
restriction preserves fibres. -/
theorem exists_liftSmul_changes_fibre (F₀ : FramePlus) :
    ∃ (a : LiftGrp) (x : LiftedFrame F₀),
      liftedFrameProj F₀ (a • x) ≠ liftedFrameProj F₀ x := by
  obtain ⟨u, hu⟩ := exists_notMem_kerSign
  refine ⟨u, NullSectorTask24.LiftedFrame.mk F₀ 1, fun h => hu ?_⟩
  rw [liftedFrameProj_equivariant] at h
  exact MonoidHom.mem_ker.2 (frameAction_free h)

end NullSectorTask25
