import RequestProject.Spine.E2.Lift.LocalInternalRepresentatives

/-!
# Spine / Controls : a native central double cover of a topological group

**CONTROL — NATIVE MODEL.**  This module builds, from Mathlib alone and the generic Spine
interface `NullSectorTask28.InternalProjection`, two instances of that interface:

* `SpineControls.trivialDoubleCover G` — the split double cover `G × ℤ/2 → G`.  It is a
  **POSITIVE CONTROL**: the interface is inhabited over every topological group, so no
  theorem quantified over `InternalProjection` is vacuous;
* `SpineControls.circleDoubleCover` — the squaring map of the circle group,
  `Circle → Circle`, `z ↦ z²`.  It is a **NEGATIVE CONTROL**: it is a genuine two-to-one
  central cover which admits **no** global continuous section
  (`SpineControls.circle_no_global_section`), so the conditional hypotheses of the generic
  lift theory ("`P` has no whole-domain internal representative of the identity") are
  satisfiable and not vacuous either.

Nothing here is imported by any production module: the dependency direction is
`production core → controls`.

No declaration of this file depends on the historical experiment trees.
-/

namespace SpineControls

open NullSectorTask28

universe u

/-! ## The split double cover of an arbitrary topological group -/

section Trivial

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The carrier of the split double cover: `G × ℤ/2`, with the product topology. -/
abbrev SplitCover : Type u := G × Multiplicative (ZMod 2)

/-- **POSITIVE CONTROL.**  The split (trivial) central double cover `G × ℤ/2 → G`.  Its
kernel is the two-element central subgroup `1 × ℤ/2`; it has a *global* continuous section,
so it is a positive, not a negative, control. -/
def trivialDoubleCover : InternalProjection (SplitCover G) G where
  proj := MonoidHom.fst G (Multiplicative (ZMod 2))
  continuous_proj := continuous_fst
  surjective_proj := fun g => ⟨(g, 1), rfl⟩
  hasLocalSection := fun k =>
    ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun g => (g, 1),
      (continuous_id.prodMk continuous_const).continuousOn, fun _ _ => rfl⟩
  ker_central := by
    rintro ⟨z₁, z₂⟩ hz ⟨l₁, l₂⟩
    have hz1 : z₁ = 1 := hz
    refine Prod.ext ?_ (mul_comm _ _)
    show z₁ * l₁ = l₁ * z₁
    rw [hz1, one_mul, mul_one]
  ker_discrete := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun z : ((MonoidHom.fst G (Multiplicative (ZMod 2))).ker) =>
        (z : SplitCover G).2) (by fun_prop) ?_
    intro a b hab
    have ha : (a : SplitCover G).1 = 1 := a.2
    have hb : (b : SplitCover G).1 = 1 := b.2
    exact Subtype.ext (Prod.ext (ha.trans hb.symm) hab)

/-- The split cover has a global continuous section. -/
theorem trivialDoubleCover_hasGlobalSection :
    (trivialDoubleCover G).HasContinuousInternalRep (id : G → G) Set.univ :=
  ⟨fun g => (g, 1), (continuous_id.prodMk continuous_const).continuousOn, fun _ _ => rfl⟩

end Trivial

/-! ## The circle, squared: a native two-to-one central cover with no global section -/

/-- The nontrivial element of the kernel of the squaring map of the circle. -/
noncomputable def negOneCircle : Circle :=
  ⟨-1, by simp [Submonoid.unitSphere, mem_sphere_iff_norm]⟩

theorem negOneCircle_ne_one : negOneCircle ≠ 1 := by
  intro h
  have : (-1 : ℂ) = 1 := congrArg (fun w : Circle => (w : ℂ)) h
  norm_num at this

@[simp] theorem negOneCircle_sq : negOneCircle ^ 2 = 1 := by
  apply Circle.ext
  show (-1 : ℂ) ^ 2 = 1
  norm_num

/-- The square roots of `1` in the circle group are exactly `±1`. -/
theorem circle_sq_eq_one_iff (z : Circle) : z ^ 2 = 1 ↔ z = 1 ∨ z = negOneCircle := by
  constructor
  · intro h
    have hz : (z : ℂ) * z = 1 := by
      have := congrArg (fun w : Circle => (w : ℂ)) h
      simpa [pow_two] using this
    have hfac : ((z : ℂ) - 1) * ((z : ℂ) + 1) = 0 := by linear_combination hz
    rcases mul_eq_zero.1 hfac with h1 | h1
    · exact Or.inl (Circle.ext (sub_eq_zero.1 h1))
    · exact Or.inr (Circle.ext (by show (z : ℂ) = -1; linear_combination h1))
  · rintro (rfl | rfl)
    · exact one_pow 2
    · exact negOneCircle_sq

/-- The circle group is preconnected: it is the continuous image of `ℝ` under `Circle.exp`. -/
instance circle_preconnectedSpace : PreconnectedSpace Circle := by
  have hr : Set.range (fun t : ℝ => Circle.exp t) = Set.univ := by
    ext z
    simp only [Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨Complex.arg z, Circle.exp_arg z⟩
  have h := isPreconnected_range (f := fun t : ℝ => Circle.exp t) (by fun_prop)
  rw [hr] at h
  exact ⟨h⟩

/-- Squaring is surjective on the circle. -/
theorem circle_sq_surjective : Function.Surjective (fun z : Circle => z ^ 2) := by
  intro z
  refine ⟨Circle.exp (Complex.arg z / 2), ?_⟩
  show Circle.exp (Complex.arg z / 2) ^ 2 = z
  rw [← Circle.exp_nsmul]
  norm_num
  rw [mul_div_cancel₀ _ two_ne_zero]
  exact Circle.exp_arg z

/-- The kernel of squaring is the two-element set `{1, -1}`. -/
theorem circle_ker_eq :
    ((powMonoidHom 2 : Circle →* Circle).ker : Set Circle) = {1, negOneCircle} := by
  ext z
  simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact circle_sq_eq_one_iff z

instance circle_ker_finite : Finite ((powMonoidHom 2 : Circle →* Circle).ker) := by
  have hfin : ((powMonoidHom 2 : Circle →* Circle).ker : Set Circle).Finite := by
    rw [circle_ker_eq]; exact (Set.finite_singleton _).insert _
  exact hfin

/-- Squaring on the circle has a continuous section on a neighbourhood of every point: it is
a covering map. -/
theorem circle_hasLocalSection (k : Circle) :
    ∃ V : Set Circle, IsOpen V ∧ k ∈ V ∧ ∃ s : Circle → Circle,
      ContinuousOn s V ∧ ∀ y ∈ V, (s y) ^ 2 = y := by
  have hcov : IsCoveringMap (fun z : Circle => z ^ 2) :=
    (Circle.isQuotientCoveringMap_npow 2).isCoveringMap
  obtain ⟨l, hl⟩ := circle_sq_surjective k
  obtain ⟨e, hle, he⟩ := hcov.isLocalHomeomorph l
  refine ⟨e.target, e.open_target, ?_, e.symm, e.continuousOn_symm, ?_⟩
  · rw [show k = e l from by rw [← hl, he]]
    exact e.map_source hle
  · intro y hy
    have h1 : (fun z : Circle => z ^ 2) (e.symm y) = e (e.symm y) := by rw [he]
    rw [show (e.symm y) ^ 2 = (fun z : Circle => z ^ 2) (e.symm y) from rfl, h1, e.right_inv hy]

/-- **NEGATIVE CONTROL, NATIVE MODEL.**  The squaring map of the circle group, as an internal
projection: a continuous surjective homomorphism with continuous local sections and a
two-element central discrete kernel. -/
noncomputable def circleDoubleCover : InternalProjection Circle Circle where
  proj := powMonoidHom 2
  continuous_proj := by
    show Continuous fun z : Circle => z ^ 2
    fun_prop
  surjective_proj := circle_sq_surjective
  hasLocalSection := circle_hasLocalSection
  ker_central := fun _ _ _ => mul_comm _ _
  ker_discrete := inferInstance

@[simp] theorem circleDoubleCover_proj (z : Circle) : circleDoubleCover.proj z = z ^ 2 := rfl

/-- **COUNTEREXAMPLE.**  The circle double cover has **no** global continuous section: there
is no continuous square root on the whole circle.

Proof: if `s` were such a section then `f z = s (z²) · z⁻¹` is continuous with `f z ² = 1`,
hence takes values in the two-point set `{1, -1}`; the circle is preconnected, so `f` is
constant; but `f 1 = s 1` and `f (-1) = s 1 · (-1)`, forcing `-1 = 1`. -/
theorem circle_no_global_section :
    ¬ ∃ s : Circle → Circle, Continuous s ∧ ∀ y, (s y) ^ 2 = y := by
  rintro ⟨s, hs, hsec⟩
  set f : Circle → Circle := fun z => s (z ^ 2) * z⁻¹ with hf
  have hfc : Continuous f := by fun_prop
  have hfsq : ∀ z, f z ^ 2 = 1 := by
    intro z
    have h1 : s (z ^ 2) ^ 2 = z ^ 2 := hsec _
    have h2 : f z ^ 2 = s (z ^ 2) ^ 2 * (z ^ 2)⁻¹ := by rw [hf, mul_pow, inv_pow]
    rw [h2, h1, mul_inv_cancel]
  have hval : ∀ z, f z = 1 ∨ f z = negOneCircle := fun z => (circle_sq_eq_one_iff _).1 (hfsq z)
  have hclosed : IsClosed (f ⁻¹' {1}) := IsClosed.preimage hfc isClosed_singleton
  have hcompl : f ⁻¹' {1} = (f ⁻¹' {negOneCircle})ᶜ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff]
    constructor
    · intro h hc
      exact negOneCircle_ne_one (hc ▸ h ▸ rfl)
    · intro h
      rcases hval z with h1 | h1
      · exact h1
      · exact absurd h1 h
  have hopen : IsOpen (f ⁻¹' {1}) := by
    rw [hcompl]
    exact (IsClosed.preimage hfc isClosed_singleton).isOpen_compl
  have hA : IsClopen (f ⁻¹' {1}) := ⟨hclosed, hopen⟩
  have hconst : f 1 = f negOneCircle := by
    rcases isClopen_iff.mp hA with h | h
    · have h1 : f 1 ≠ 1 := fun hc => by
        have : (1 : Circle) ∈ f ⁻¹' {1} := hc
        rw [h] at this
        exact this.elim
      have h2 : f negOneCircle ≠ 1 := fun hc => by
        have : negOneCircle ∈ f ⁻¹' {1} := hc
        rw [h] at this
        exact this.elim
      rcases hval 1 with hz | hz
      · exact absurd hz h1
      rcases hval negOneCircle with hw | hw
      · exact absurd hw h2
      rw [hz, hw]
    · have h1 : f 1 = 1 := by
        have : (1 : Circle) ∈ f ⁻¹' {1} := by rw [h]; trivial
        exact this
      have h2 : f negOneCircle = 1 := by
        have : negOneCircle ∈ f ⁻¹' {1} := by rw [h]; trivial
        exact this
      rw [h1, h2]
  rw [hf] at hconst
  simp only [one_pow, inv_one, mul_one, negOneCircle_sq] at hconst
  have hcancel : (1 : Circle) = negOneCircle⁻¹ :=
    mul_left_cancel (a := s 1) (by rw [mul_one]; exact hconst)
  exact negOneCircle_ne_one (inv_eq_one.1 hcancel.symm)

/-- **COUNTEREXAMPLE, in the language of the generic interface.**  The native circle double
cover has no continuous internal representative of the identity over the whole group: it
satisfies the standing hypothesis of the generic non-liftability theorems. -/
theorem circleDoubleCover_no_whole_domain_rep :
    ¬ circleDoubleCover.HasContinuousInternalRep (id : Circle → Circle) Set.univ := by
  rintro ⟨u, hu, hproj⟩
  exact circle_no_global_section
    ⟨u, continuousOn_univ.1 hu, fun y => hproj y (Set.mem_univ y)⟩

end SpineControls
