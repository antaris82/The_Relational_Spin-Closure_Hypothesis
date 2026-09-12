import RequestProject.Spine.Geometry.SpinStructure

/-!
# Task 4, WP7 : the canonical `ℤ₂`-valued Čech presentation of the frame obstruction

The Task-3 obstruction takes its values in the intrinsic kernel `{1, negOneSpin}` of the
native Spin projection.  This module transports it, along the **canonical** group
isomorphism `{±1} ≅ ℤ/2`, into the conventional additive `ℤ₂`-valued Čech language, in which
the classical second Stiefel–Whitney obstruction of a tangent bundle is usually written:

* `LorentzFrames.zdefect D` — the additive `ℤ₂`-valued triple-overlap cochain;
* `LorentzFrames.zdefect_cocycle₂` — the additive Čech 2-cocycle law on quadruple overlaps;
* `LorentzFrames.zdefect_change_of_lift` — the additive coboundary law: changing the local
  Spin representatives changes the cochain by `δa`;
* `LorentzFrames.zdefect_isCoboundary_iff_spinStructure` — the additive vanishing criterion:
  the cochain is a Čech 1-coboundary **iff** the Lorentz frame data admits a Spin structure.

**What this does and does not achieve.**  It makes the carrier of the obstruction a
recognizable `ℤ₂`-valued Čech object on the chosen cover.  It does **not** identify the
class with the Stiefel–Whitney class `w₂(TM)`: the pinned library contains no
Stiefel–Whitney classes, no classifying spaces and no cohomology of a topological space with
`ℤ₂` coefficients, so that identification cannot even be stated.  See `TASK04_AUDIT.md`,
where the status is classified as `VANISHING_EQUIVALENCE_ONLY` plus a canonical `ℤ₂`-Čech
presentation, with literal equality `BLOCKED` at library level.
-/

noncomputable section

namespace LorentzFrames

open SpinCore CechSpinLift NullSectorTask28

universe u v t

/-! ## The canonical identification `{±1} ≅ ℤ/2` -/

open scoped Classical in
/-- The canonical sign of an element of the intrinsic kernel, as an element of `ℤ/2`. -/
def spinSign (u : ↥SpinGroup) : ZMod 2 := if u = negOneSpin then 1 else 0

/-- The inverse identification. -/
def zToSpin (z : ZMod 2) : ↥SpinGroup := if z = 1 then negOneSpin else 1

@[simp] theorem spinSign_negOneSpin : spinSign negOneSpin = 1 := by
  classical
  simp [spinSign]

@[simp] theorem spinSign_one : spinSign 1 = 0 := by
  classical
  simp [spinSign, Ne.symm negOneSpin_ne_one]

@[simp] theorem zToSpin_zero : zToSpin 0 = 1 := by
  simp [zToSpin, (by decide : (0 : ZMod 2) ≠ 1)]

@[simp] theorem zToSpin_one : zToSpin 1 = negOneSpin := by simp [zToSpin]

theorem zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by revert z; decide

@[simp] theorem spinSign_zToSpin (z : ZMod 2) : spinSign (zToSpin z) = z := by
  rcases zmod2_cases z with h | h <;> simp [h]

theorem zToSpin_mem_ker (z : ZMod 2) : zToSpin z ∈ internalSpinProjection.Ker := by
  rcases zmod2_cases z with h | h
  · simp only [h, zToSpin_zero]
    exact Subgroup.one_mem _
  · simp only [h, zToSpin_one]
    exact (mem_ker_spinCover_iff _).2 (Or.inr rfl)

theorem zToSpin_spinSign {u : ↥SpinGroup} (hu : u ∈ internalSpinProjection.Ker) :
    zToSpin (spinSign u) = u := by
  rcases (mem_ker_spinCover_iff u).1 hu with h | h <;> simp [h]

theorem spinSign_injOn_ker {u v : ↥SpinGroup} (hu : u ∈ internalSpinProjection.Ker)
    (hv : v ∈ internalSpinProjection.Ker) (h : spinSign u = spinSign v) : u = v := by
  rw [← zToSpin_spinSign hu, ← zToSpin_spinSign hv, h]

theorem negOneSpin_mul_negOneSpin : negOneSpin * negOneSpin = 1 := by
  have h := negOneSpin_sq
  rwa [pow_two] at h

/-- Every element of the intrinsic kernel is an involution. -/
theorem ker_mul_self {u : ↥SpinGroup} (hu : u ∈ internalSpinProjection.Ker) : u * u = 1 := by
  rcases (mem_ker_spinCover_iff u).1 hu with h | h
  · rw [h, one_mul]
  · rw [h, negOneSpin_mul_negOneSpin]

/-- **CANONICAL_IDENTIFICATION (WP7).**  On the intrinsic kernel the sign is a group
homomorphism onto `ℤ/2`. -/
theorem spinSign_mul {u v : ↥SpinGroup} (hu : u ∈ internalSpinProjection.Ker)
    (hv : v ∈ internalSpinProjection.Ker) :
    spinSign (u * v) = spinSign u + spinSign v := by
  rcases (mem_ker_spinCover_iff u).1 hu with hu' | hu' <;>
    rcases (mem_ker_spinCover_iff v).1 hv with hv' | hv' <;> rw [hu', hv']
  · simp
  · simp
  · simp
  · rw [negOneSpin_mul_negOneSpin, spinSign_one, spinSign_negOneSpin]
    decide

theorem spinSign_inv {u : ↥SpinGroup} (hu : u ∈ internalSpinProjection.Ker) :
    spinSign u⁻¹ = spinSign u := by
  rcases (mem_ker_spinCover_iff u).1 hu with h | h
  · simp [h]
  · rw [h, inv_eq_of_mul_eq_one_right negOneSpin_mul_negOneSpin]

/-! ## The additive `ℤ₂`-valued cochains of the Lorentz frame data -/

variable {M : Type u} [TopologicalSpace M] {Fib : M → Type v}
  [∀ x, AddCommGroup (Fib x)] [∀ x, Module ℝ (Fib x)] {ι : Type t}
  {Φ : LorentzFrameData M Fib ι}

/-- **NEWLY DEFINED (WP7), principal.**  The additive `ℤ₂`-valued triple-overlap cochain of
the Lorentz frame data — the Lorentz-frame Spin-lift obstruction written in the conventional
Čech language. -/
def zdefect (D : FrameSpinLifts Φ) (i j k : ι) (x : M) : ZMod 2 :=
  spinSign (D.defect i j k x)

/-- The additive Čech coboundary of a `ℤ₂`-valued 1-cochain. -/
def deltaZ (a : ι → ι → (M → ZMod 2)) (i j k : ι) (x : M) : ZMod 2 :=
  a i j x + a j k x - a i k x

/-- **NEWLY DEFINED (WP7).**  Regularity of a `ℤ₂`-valued Čech 1-cochain: the associated
`{±1}`-valued function is continuous on each double overlap.  (Since the kernel is discrete
this says exactly that the cochain is locally constant there.) -/
def IsZ2Cochain₁ (Φ : LorentzFrameData M Fib ι) (a : ι → ι → (M → ZMod 2)) : Prop :=
  ∀ i j, ContinuousOn (fun x => zToSpin (a i j x)) (Φ.cover.overlap₂ i j)

theorem zdefect_eq_zero_iff (D : FrameSpinLifts Φ) (i j k : ι) {x : M}
    (hx : x ∈ Φ.cover.overlap₃ i j k) :
    zdefect D i j k x = 0 ↔ D.defect i j k x = 1 := by
  constructor
  · intro h
    have := zToSpin_spinSign (D.defect_mem_ker i j k hx)
    rw [zdefect] at h
    rw [← this, h, zToSpin_zero]
  · intro h
    rw [zdefect, h, spinSign_one]

/-- **DERIVED_NATIVE (WP7).**  The additive Čech 2-cocycle law on quadruple overlaps. -/
theorem zdefect_cocycle₂ (D : FrameSpinLifts Φ) (i j k l : ι) {x : M}
    (hx : x ∈ Φ.cover.overlap₄ i j k l) :
    zdefect D j k l x + zdefect D i k l x + zdefect D i j l x + zdefect D i j k x = 0 := by
  have hjkl := D.defect_mem_ker j k l (Φ.cover.overlap₄_subset_jkl i j k l hx)
  have hikl := D.defect_mem_ker i k l (Φ.cover.overlap₄_subset_ikl i j k l hx)
  have hijl := D.defect_mem_ker i j l (Φ.cover.overlap₄_subset_ijl i j k l hx)
  have hijk := D.defect_mem_ker i j k (Φ.cover.overlap₄_subset_ijk i j k l hx)
  have hprod := D.defect_delta_eq_one i j k l hx
  have h1 : spinSign (D.defect j k l x * (D.defect i k l x)⁻¹ * D.defect i j l x
      * (D.defect i j k x)⁻¹) = 0 := by rw [hprod, spinSign_one]
  rw [spinSign_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ hjkl (Subgroup.inv_mem _ hikl))
      hijl) (Subgroup.inv_mem _ hijk),
    spinSign_mul (Subgroup.mul_mem _ hjkl (Subgroup.inv_mem _ hikl)) hijl,
    spinSign_mul hjkl (Subgroup.inv_mem _ hikl), spinSign_inv hikl, spinSign_inv hijk] at h1
  exact h1

/-- **DERIVED_NATIVE (WP7).**  Changing the local Spin representatives changes the additive
cochain by an additive Čech 1-coboundary: the class in the additive language is
well defined. -/
theorem zdefect_change_of_lift (D D' : FrameSpinLifts Φ) :
    ∃ a : ι → ι → (M → ZMod 2), IsZ2Cochain₁ Φ a ∧
      ∀ i j k, ∀ x ∈ Φ.cover.overlap₃ i j k,
        zdefect D' i j k x = deltaZ a i j k x + zdefect D i j k x := by
  obtain ⟨ε, hε, _, hdef⟩ := D.defect_change_of_lift D'
  refine ⟨fun i j x => spinSign (ε i j x), ?_, ?_⟩
  · intro i j
    refine ((hε i j).1).congr fun x hx => ?_
    exact zToSpin_spinSign ((hε i j).2 x hx)
  · intro i j k x hx
    have hij := (hε i j).2 x (Φ.cover.overlap₃_subset_ij i j k hx)
    have hjk := (hε j k).2 x (Φ.cover.overlap₃_subset_jk i j k hx)
    have hik := (hε i k).2 x (Φ.cover.overlap₃_subset_ik i j k hx)
    have hc := D.defect_mem_ker i j k hx
    rw [zdefect, hdef i j k x hx, delta₁_apply,
      spinSign_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ hij hjk)
        (Subgroup.inv_mem _ hik)) hc,
      spinSign_mul (Subgroup.mul_mem _ hij hjk) (Subgroup.inv_mem _ hik),
      spinSign_mul hij hjk, spinSign_inv hik]
    have hsub : ∀ y z : ZMod 2, y - z = y + z := by decide
    simp only [deltaZ, zdefect, hsub]

/-- **DERIVED_NATIVE (WP7), principal endpoint.**  The additive vanishing criterion in the
conventional Čech language: the `ℤ₂`-valued triple-overlap cochain of the Lorentz frame data
is a Čech 1-coboundary **iff** the frame data admits a Spin structure.

This is the strongest form of the `w₂`-type statement available in the pinned library: the
class lives in the native fixed-cover `ℤ₂` Čech quotient, and its vanishing is equivalent to
Spin-liftability.  It is **not** asserted to be `w₂(TM)`. -/
theorem zdefect_isCoboundary_iff_spinStructure (D : FrameSpinLifts Φ) :
    (∃ a : ι → ι → (M → ZMod 2), IsZ2Cochain₁ Φ a ∧
        ∀ i j k, ∀ x ∈ Φ.cover.overlap₃ i j k, zdefect D i j k x = deltaZ a i j k x) ↔
      Nonempty (SpinFrameStructure Φ) := by
  constructor
  · rintro ⟨a, ha, hrel⟩
    set ε : ι → ι → (M → ↥SpinGroup) := fun i j x => zToSpin (a i j x)
    have hε : IsKerCochain₁ internalSpinProjection Φ.cover ε :=
      fun i j => ⟨ha i j, fun x _ => zToSpin_mem_ker _⟩
    have hdelta : ∀ i j k, ∀ x ∈ Φ.cover.overlap₃ i j k,
        delta₁ ε i j k x = D.defect i j k x := by
      intro i j k x hx
      have hmem : delta₁ ε i j k x ∈ internalSpinProjection.Ker :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (zToSpin_mem_ker _) (zToSpin_mem_ker _))
          (Subgroup.inv_mem _ (zToSpin_mem_ker _))
      refine spinSign_injOn_ker hmem (D.defect_mem_ker i j k hx) ?_
      rw [delta₁_apply,
        spinSign_mul (Subgroup.mul_mem _ (zToSpin_mem_ker _) (zToSpin_mem_ker _))
          (Subgroup.inv_mem _ (zToSpin_mem_ker _)),
        spinSign_mul (zToSpin_mem_ker _) (zToSpin_mem_ker _),
        spinSign_inv (zToSpin_mem_ker (a i k x))]
      have hsub : ∀ y z : ZMod 2, y - z = y + z := by decide
      show _ = zdefect D i j k x
      rw [hrel i j k x hx]
      simp only [spinSign_zToSpin, deltaZ, hsub]
    refine ⟨SpinFrameStructure.ofCoherent (D := D.twist ε hε) ?_⟩
    refine ((D.twist ε hε).isCoherent_iff_defect_one).2 fun i j k x hx => ?_
    rw [D.defect_twist ε hε i j k hx, hdelta i j k x hx]
    exact ker_mul_self (D.defect_mem_ker i j k hx)
  · rintro ⟨S⟩
    obtain ⟨a, ha, hrel⟩ := zdefect_change_of_lift S.toSpinLifts D
    refine ⟨a, ha, fun i j k x hx => ?_⟩
    have hzero : zdefect S.toSpinLifts i j k x = 0 := by
      rw [zdefect_eq_zero_iff _ _ _ _ hx]
      exact (S.toSpinLifts.isCoherent_iff_defect_one).1 S.toSpinLifts_isCoherent i j k x hx
    have hthis := hrel i j k x hx
    rw [hzero] at hthis
    simpa using hthis

end LorentzFrames
