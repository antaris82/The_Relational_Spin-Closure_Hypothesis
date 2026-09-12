import RequestProject.Spine.Solder.RegularExamples

/-!
# Task 36 / Adversarial : the periodic ("one loop") four-dimensional gluing models

**First module of the Task-36 adversarial battery.**

Task 35 closed the bottom-up chain `R³ → Clifford/Spin core → base gluing → smooth M →
regular solder → TM`.  Every positive control used so far (`symmetricGluing`,
`rescaleGluing`) has a *globally trivial* incidence pattern: all overlaps are the whole local
model, and the emergent base is a single chart image.  Nothing global can be tested on them.

This module builds the first genuinely non-trivial gluing of the project: two four-dimensional
slabs of the local model, glued along **two disjoint incidence components**, one of which is a
"wrap-around".  This is the **periodic fixed-cover loop model** with a **two-component
periodic overlap**, and *nothing else about the project changes*: the construction uses only
the Task-32 primitive `EmergentBase.BaseGluingData`.

**Wording correction (Task 37 §6).**  Earlier documentation described the emergent base as
"a model of `S¹ × ℝ³`" carrying "a genuine noncontractible loop".  Neither
`Space B ≅ S¹ × ℝ³` nor `π₁(Space B) ≠ 0` is proved anywhere in this project, and neither is
used in any proof; proving them would require fundamental-group and product-space
infrastructure that the project has not built.  The exact proved content is the
**two-component periodic overlap pattern of the fixed cover** and its consequences, and that
is what every theorem below uses.

## The parameter

The wrap-around identification is allowed to carry a linear involution `T` of the local model
that fixes the first (loop) coordinate:

* `T = id` gives the **orientable one-loop model** (`Task36.loopGluing`), used for the
  Spin-lift freedom tests of §§7–8;
* `T = (u, s) ↦ (u, -s)` gives the **orientation-reversing (Möbius-type) model**
  (`Task36.moebiusGluing`), used for the negative control of §9.  Its wrap-around tangent
  transition has determinant `-1` (`Task36.det_flipEquiv`).

The label type `κ` indexes *independent copies* of the loop: the pieces of different labels
are never incident, so the emergent base is the disjoint union of `κ` loop models.  `κ = Unit`
is the one-loop model; `κ = Fin 2` is the two-independent-loop model used for the `H¹`-like
multiplicity control of §8.

## What is *not* claimed

No metric, transport form, curvature or loop-transport datum occurs here; `loopGluingOf` is a
base-gluing datum and nothing more.  In particular the periodic wrap-around is a statement
about the *incidence pattern of the primitive*, not about any geometry and not about the
homotopy type of the emergent base: see `TASK36_AUDIT.md` §15 (claim firewall) and the Task-37
wording correction above.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task36

open EmergentBase EmergentBase.BaseGluingData SpinCore

/-! ## Slabs of the local model -/

/-- The open slab `{x : a < x₀ < b}` of the four-dimensional local model, cut out by the
first (loop) coordinate. -/
def slab (a b : ℝ) : Set LocalModel := (fun x : LocalModel => x.1) ⁻¹' Set.Ioo a b

theorem mem_slab {a b : ℝ} {x : LocalModel} : x ∈ slab a b ↔ a < x.1 ∧ x.1 < b := Iff.rfl

theorem isOpen_slab (a b : ℝ) : IsOpen (slab a b) :=
  isOpen_Ioo.preimage continuous_fst

theorem convex_slab (a b : ℝ) : Convex ℝ (slab a b) :=
  (convex_Ioo a b).linear_preimage (LinearMap.fst ℝ ℝ (Fin 3 → ℝ))

theorem isPreconnected_slab (a b : ℝ) : IsPreconnected (slab a b) :=
  (convex_slab a b).isPreconnected

theorem slab_mono {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') : slab a b ⊆ slab a' b' :=
  fun _ hx => ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩

/-! ## The twist parameter -/

/-- A **loop twist**: a linear involution of the local model fixing the loop coordinate.  It
is the datum by which the wrap-around identification of the periodic model may be composed
with an internal linear symmetry. -/
structure LoopTwist where
  /-- The linear involution. -/
  T : LocalModel ≃L[ℝ] LocalModel
  /-- It fixes the loop (first) coordinate. -/
  fst_eq : ∀ x : LocalModel, (T x).1 = x.1
  /-- It is an involution. -/
  invol : ∀ x : LocalModel, T (T x) = x

namespace LoopTwist

/-- The identity twist: the orientable periodic model. -/
def id' : LoopTwist where
  T := ContinuousLinearEquiv.refl ℝ LocalModel
  fst_eq _ := rfl
  invol _ := rfl

/-- The spatial flip `(u, s) ↦ (u, -s)`, as a continuous linear equivalence of the local
model. -/
def flipEquiv : LocalModel ≃L[ℝ] LocalModel :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.id ℝ ℝ).prodMap (-ContinuousLinearMap.id ℝ (Fin 3 → ℝ)))
    ((ContinuousLinearMap.id ℝ ℝ).prodMap (-ContinuousLinearMap.id ℝ (Fin 3 → ℝ)))
    (fun x => Prod.ext rfl (neg_neg x.2)) (fun x => Prod.ext rfl (neg_neg x.2))

@[simp] theorem flipEquiv_apply (x : LocalModel) : flipEquiv x = (x.1, -x.2) := rfl

/-- The orientation-reversing twist. -/
def flip : LoopTwist where
  T := flipEquiv
  fst_eq _ := rfl
  invol x := Prod.ext rfl (neg_neg x.2)

end LoopTwist

/-- **The determinant of the spatial flip is `-1`.**  This is the exact point at which the
Möbius-type model becomes orientation-reversing: it is a statement about the *tangent*
transition of the base gluing, not about any Spin datum. -/
theorem det_flipEquiv :
    LinearMap.det ((LoopTwist.flipEquiv : LocalModel ≃L[ℝ] LocalModel) :
      LocalModel →ₗ[ℝ] LocalModel) = -1 := by
  have hmap : ((LoopTwist.flipEquiv : LocalModel ≃L[ℝ] LocalModel) :
      LocalModel →ₗ[ℝ] LocalModel)
      = LinearMap.prodMap (LinearMap.id (R := ℝ) (M := ℝ))
          ((-1 : ℝ) • LinearMap.id (R := ℝ) (M := Fin 3 → ℝ)) := by
    refine LinearMap.ext fun x => ?_
    refine Prod.ext rfl ?_
    funext k
    show -x.2 k = -1 * x.2 k
    ring
  rw [hmap, LinearMap.det_prodMap, LinearMap.det_id, LinearMap.det_smul, LinearMap.det_id,
    Module.finrank_pi]
  norm_num

/-! ## The Bool-level periodic gluing -/

section Periodic

variable (t : LoopTwist)

/-- The translation vector of the wrap-around identification: one period in the loop
coordinate. -/
def wrapVec : LocalModel := ((4 : ℝ), 0)

/-- The wrap-around identification map: the twist followed by one period of translation. -/
def wrap (x : LocalModel) : LocalModel := t.T x + wrapVec

/-- The inverse wrap-around identification. -/
def unwrap (y : LocalModel) : LocalModel := t.T (y - wrapVec)

@[simp] theorem wrap_fst (x : LocalModel) : (wrap t x).1 = x.1 + 4 := by
  show (t.T x).1 + (4 : ℝ) = x.1 + 4
  rw [t.fst_eq]

@[simp] theorem unwrap_fst (y : LocalModel) : (unwrap t y).1 = y.1 - 4 := by
  show (t.T (y - wrapVec)).1 = y.1 - 4
  rw [t.fst_eq]
  rfl

theorem unwrap_wrap (x : LocalModel) : unwrap t (wrap t x) = x := by
  show t.T (t.T x + wrapVec - wrapVec) = x
  rw [add_sub_cancel_right, t.invol]

theorem wrap_unwrap (y : LocalModel) : wrap t (unwrap t y) = y := by
  show t.T (t.T (y - wrapVec)) + wrapVec = y
  rw [t.invol, sub_add_cancel]

/-- The local domains of the two pieces of the periodic model. -/
def Db : Bool → Set LocalModel
  | false => slab 0 3
  | true => slab 2 5

/-- The incidence domains of the two pieces: the diagonal ones are the whole pieces, the
cross ones have **two components** — the ordinary overlap component `2 < u < 3` and the
wrap-around component. -/
def Wb : Bool → Bool → Set LocalModel
  | false, false => slab 0 3
  | true, true => slab 2 5
  | false, true => slab 0 1 ∪ slab 2 3
  | true, false => slab 4 5 ∪ slab 2 3

/-- The identification maps of the periodic model. -/
def φb : Bool → Bool → LocalModel → LocalModel
  | false, false => id
  | true, true => id
  | false, true => fun x => if x.1 < 1.5 then wrap t x else x
  | true, false => fun y => if 3.5 < y.1 then unwrap t y else y

theorem isOpen_Db (b : Bool) : IsOpen (Db b) := by
  cases b
  · exact isOpen_slab 0 3
  · exact isOpen_slab 2 5

theorem isOpen_Wb (b c : Bool) : IsOpen (Wb b c) := by
  cases b <;> cases c
  · exact isOpen_slab 0 3
  · exact (isOpen_slab 0 1).union (isOpen_slab 2 3)
  · exact (isOpen_slab 4 5).union (isOpen_slab 2 3)
  · exact isOpen_slab 2 5

theorem Wb_subset (b c : Bool) : Wb b c ⊆ Db b := by
  cases b <;> cases c
  · exact fun _ hx => hx
  · rintro x (hx | hx)
    · exact slab_mono (le_refl 0) (by norm_num) hx
    · exact slab_mono (by norm_num) (by norm_num) hx
  · rintro x (hx | hx)
    · exact slab_mono (by norm_num) (le_refl 5) hx
    · exact slab_mono (le_refl 2) (by norm_num) hx
  · exact fun _ hx => hx

theorem Wb_self (b : Bool) : Wb b b = Db b := by cases b <;> rfl

theorem φb_self (b : Bool) (x : LocalModel) : φb t b b x = x := by cases b <;> rfl

/-! ### The two branches of the cross identification -/

theorem φb_ft_of_lt {x : LocalModel} (hx : x.1 < 1.5) : φb t false true x = wrap t x :=
  if_pos hx

theorem φb_ft_of_gt {x : LocalModel} (hx : 1.5 < x.1) : φb t false true x = x :=
  if_neg (not_lt.2 (le_of_lt hx))

theorem φb_tf_of_gt {y : LocalModel} (hy : 3.5 < y.1) : φb t true false y = unwrap t y :=
  if_pos hy

theorem φb_tf_of_lt {y : LocalModel} (hy : y.1 < 3.5) : φb t true false y = y :=
  if_neg (not_lt.2 (le_of_lt hy))

theorem mapsTo_φb (b c : Bool) : Set.MapsTo (φb t b c) (Wb b c) (Wb c b) := by
  cases b <;> cases c
  · intro x hx; rw [φb_self]; exact hx
  · rintro x (hx | hx)
    · rw [φb_ft_of_lt t (lt_trans hx.2 (by norm_num))]
      refine Or.inl (mem_slab.2 ⟨?_, ?_⟩)
      · rw [wrap_fst]; linarith [hx.1]
      · rw [wrap_fst]; linarith [hx.2]
    · rw [φb_ft_of_gt t (lt_trans (by norm_num) hx.1)]
      exact Or.inr hx
  · rintro y (hy | hy)
    · rw [φb_tf_of_gt t (lt_trans (by norm_num) hy.1)]
      refine Or.inl (mem_slab.2 ⟨?_, ?_⟩)
      · rw [unwrap_fst]; linarith [hy.1]
      · rw [unwrap_fst]; linarith [hy.2]
    · rw [φb_tf_of_lt t (lt_trans hy.2 (by norm_num))]
      exact Or.inr hy
  · intro y hy; rw [φb_self]; exact hy

theorem φb_inv (b c : Bool) : ∀ x ∈ Wb b c, φb t c b (φb t b c x) = x := by
  cases b <;> cases c
  · intro x _; rw [φb_self, φb_self]
  · rintro x (hx | hx)
    · rw [φb_ft_of_lt t (lt_trans hx.2 (by norm_num)),
        φb_tf_of_gt t (by rw [wrap_fst]; linarith [hx.1])]
      exact unwrap_wrap t x
    · rw [φb_ft_of_gt t (lt_trans (by norm_num) hx.1)]
      exact φb_tf_of_lt t (lt_trans hx.2 (by norm_num))
  · rintro y (hy | hy)
    · rw [φb_tf_of_gt t (lt_trans (by norm_num) hy.1),
        φb_ft_of_lt t (by rw [unwrap_fst]; linarith [hy.2])]
      exact wrap_unwrap t y
    · rw [φb_tf_of_lt t (lt_trans hy.2 (by norm_num))]
      exact φb_ft_of_gt t (lt_trans (by norm_num) hy.1)
  · intro y _; rw [φb_self, φb_self]

theorem φb_cocycle (b c d : Bool) : ∀ x ∈ Wb b c, φb t b c x ∈ Wb c d →
    x ∈ Wb b d ∧ φb t c d (φb t b c x) = φb t b d x := by
  cases b <;> cases c <;> cases d
  · intro x hx _; exact ⟨hx, by rw [φb_self, φb_self]⟩
  · intro x _ hx'; rw [φb_self] at hx' ⊢; exact ⟨hx', rfl⟩
  · intro x hx _
    exact ⟨Wb_subset false true hx, by rw [φb_inv t false true x hx, φb_self]⟩
  · intro x hx _; exact ⟨hx, by rw [φb_self]⟩
  · intro y hy _; exact ⟨hy, by rw [φb_self]⟩
  · intro y hy _
    exact ⟨Wb_subset true false hy, by rw [φb_inv t true false y hy, φb_self]⟩
  · intro y _ hy'; rw [φb_self] at hy' ⊢; exact ⟨hy', rfl⟩
  · intro y hy _; exact ⟨hy, by rw [φb_self, φb_self]⟩

/-! ### Smoothness of the identification maps -/

theorem contDiff_wrap : ContDiff ℝ (⊤ : ℕ∞) (wrap t) :=
  ((t.T : LocalModel →L[ℝ] LocalModel).contDiff).add contDiff_const

theorem contDiff_unwrap : ContDiff ℝ (⊤ : ℕ∞) (unwrap t) :=
  (t.T : LocalModel →L[ℝ] LocalModel).contDiff.comp (contDiff_id.sub contDiff_const)

theorem contDiffOn_φb (b c : Bool) : ContDiffOn ℝ (⊤ : ℕ∞) (φb t b c) (Wb b c) := by
  cases b <;> cases c
  · exact contDiffOn_id
  · rintro x (hx | hx)
    · refine ContDiffAt.contDiffWithinAt ?_
      refine ((contDiff_wrap t).contDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_slab (-1) 1.5).mem_nhds
        (show x ∈ slab (-1) 1.5 from ⟨by linarith [hx.1], by linarith [hx.2]⟩)] with z hz
      exact φb_ft_of_lt t hz.2
    · refine ContDiffAt.contDiffWithinAt ?_
      refine (contDiff_id.contDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_slab 1.5 4).mem_nhds
        (show x ∈ slab 1.5 4 from ⟨by linarith [hx.1], by linarith [hx.2]⟩)] with z hz
      exact φb_ft_of_gt t hz.1
  · rintro y (hy | hy)
    · refine ContDiffAt.contDiffWithinAt ?_
      refine ((contDiff_unwrap t).contDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_slab 3.5 6).mem_nhds
        (show y ∈ slab 3.5 6 from ⟨by linarith [hy.1], by linarith [hy.2]⟩)] with z hz
      exact φb_tf_of_gt t hz.1
    · refine ContDiffAt.contDiffWithinAt ?_
      refine (contDiff_id.contDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_slab 1 3.5).mem_nhds
        (show y ∈ slab 1 3.5 from ⟨by linarith [hy.1], by linarith [hy.2]⟩)] with z hz
      exact φb_tf_of_lt t hz.2
  · exact contDiffOn_id

end Periodic

/-! ## The `κ`-indexed family of independent loops -/

section Family

variable (κ : Type) [DecidableEq κ] (t : LoopTwist)

/-- **NEWLY DEFINED (Task 36), principal adversarial base.**  `κ` independent copies of the
periodic four-dimensional model: pieces are indexed by `κ × Bool`, pieces with different
labels are never incident, and each label carries the two-piece periodic gluing with the
wrap-around twist `t`. -/
def loopGluingOf : BaseGluingData LocalModel (κ × Bool) where
  D p := Db p.2
  isOpen_D p := isOpen_Db p.2
  W p q := if p.1 = q.1 then Wb p.2 q.2 else ∅
  isOpen_W p q := by
    by_cases h : p.1 = q.1
    · rw [if_pos h]; exact isOpen_Wb p.2 q.2
    · rw [if_neg h]; exact isOpen_empty
  W_subset p q := by
    by_cases h : p.1 = q.1
    · rw [if_pos h]; exact Wb_subset p.2 q.2
    · rw [if_neg h]; exact Set.empty_subset _
  W_self p := by rw [if_pos rfl]; exact Wb_self p.2
  φ p q := φb t p.2 q.2
  continuousOn_φ p q := by
    by_cases h : p.1 = q.1
    · rw [if_pos h]; exact (contDiffOn_φb t p.2 q.2).continuousOn
    · rw [if_neg h]; exact continuousOn_empty _
  φ_mapsTo p q := by
    by_cases h : p.1 = q.1
    · rw [if_pos h, if_pos h.symm]; exact mapsTo_φb t p.2 q.2
    · rw [if_neg h]; exact Set.mapsTo_empty _ _
  φ_self p x _ := φb_self t p.2 x
  φ_inv p q x hx := by
    by_cases h : p.1 = q.1
    · rw [if_pos h] at hx; exact φb_inv t p.2 q.2 x hx
    · rw [if_neg h] at hx; exact absurd hx (Set.notMem_empty x)
  φ_cocycle p q r x hx hx' := by
    by_cases h : p.1 = q.1
    · rw [if_pos h] at hx
      by_cases h' : q.1 = r.1
      · rw [if_pos h'] at hx'
        obtain ⟨hmem, heq⟩ := φb_cocycle t p.2 q.2 r.2 x hx hx'
        exact ⟨by rw [if_pos (h.trans h')]; exact hmem, heq⟩
      · rw [if_neg h'] at hx'; exact absurd hx' (Set.notMem_empty _)
    · rw [if_neg h] at hx; exact absurd hx (Set.notMem_empty x)

@[simp] theorem loopGluingOf_D (p : κ × Bool) : (loopGluingOf κ t).D p = Db p.2 := rfl

@[simp] theorem loopGluingOf_φ (p q : κ × Bool) : (loopGluingOf κ t).φ p q = φb t p.2 q.2 := rfl

theorem loopGluingOf_W_same {n : κ} (b c : Bool) :
    (loopGluingOf κ t).W (n, b) (n, c) = Wb b c := if_pos rfl

theorem loopGluingOf_W_ne {p q : κ × Bool} (h : p.1 ≠ q.1) :
    (loopGluingOf κ t).W p q = ∅ := if_neg h

/-- **DERIVED (Task 36).**  The adversarial base gluing is smooth, so the whole Task-33
smooth-manifold layer applies to it: the emergent base is a `C^∞` four-manifold. -/
theorem loopGluingOf_smoothGluing : (loopGluingOf κ t).SmoothGluing := by
  intro p q
  by_cases h : p.1 = q.1
  · rw [show (loopGluingOf κ t).W p q = Wb p.2 q.2 from if_pos h]
    exact contDiffOn_φb t p.2 q.2
  · rw [loopGluingOf_W_ne κ t h]
    exact contDiffOn_empty

theorem loopGluingOf_isManifold :
    IsManifold localModelI (⊤ : ℕ∞) (Space (loopGluingOf κ t)) :=
  isManifold_of_smoothGluing (loopGluingOf_smoothGluing κ t)

end Family

/-! ## The two named instantiations -/

/-- **The orientable periodic fixed-cover loop model** (`κ = Unit`, trivial twist): two slabs
glued along a two-component periodic overlap whose wrap-around component carries the identity
twist, so all tangent transitions are the identity and the model is orientable.

(Task-37 wording correction: no homeomorphism with `S¹ × ℝ³` and no statement about `π₁` is
proved or used.) -/
def loopGluing : BaseGluingData LocalModel (Unit × Bool) := loopGluingOf Unit LoopTwist.id'

/-- **The orientation-reversing (Möbius-type) model** (`κ = Unit`, spatial-flip twist): the
wrap-around identification reverses orientation, so the tangent transition of the wrap
component has determinant `-1`. -/
def moebiusGluing : BaseGluingData LocalModel (Unit × Bool) := loopGluingOf Unit LoopTwist.flip

theorem loopGluing_smoothGluing : loopGluing.SmoothGluing :=
  loopGluingOf_smoothGluing Unit LoopTwist.id'

theorem moebiusGluing_smoothGluing : moebiusGluing.SmoothGluing :=
  loopGluingOf_smoothGluing Unit LoopTwist.flip

/-! ## The tangent transitions of the periodic models -/

section Tangent

variable {κ : Type} [DecidableEq κ] (t : LoopTwist)

/-- **DERIVED (Task 36).**  On the wrap-around component the tangent transition of the
periodic gluing is the twist `T` itself. -/
theorem tangentTransitionMap_wrap {n : κ} {y : LocalModel} (hy : y ∈ slab 0 1) :
    (loopGluingOf κ t).tangentTransitionMap (n, false) (n, true) y
      = (t.T : LocalModel →L[ℝ] LocalModel) := by
  have hmem : y ∈ (loopGluingOf κ t).W (n, false) (n, true) := by
    rw [loopGluingOf_W_same]; exact Or.inl hy
  have hderiv : HasFDerivAt (fun x : LocalModel => φb t false true x)
      (t.T : LocalModel →L[ℝ] LocalModel) y := by
    have hw : HasFDerivAt (wrap t) (t.T : LocalModel →L[ℝ] LocalModel) y :=
      ((t.T : LocalModel →L[ℝ] LocalModel).hasFDerivAt).add_const wrapVec
    refine hw.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_slab (-1) 1.5).mem_nhds
      (show y ∈ slab (-1) 1.5 from ⟨by linarith [hy.1], by linarith [hy.2]⟩)] with z hz
    exact φb_ft_of_lt t hz.2
  rw [BaseGluingData.tangentTransitionMap,
    fderivWithin_of_isOpen ((loopGluingOf κ t).isOpen_W _ _) hmem]
  exact hderiv.fderiv

/-- **DERIVED (Task 36).**  On the ordinary overlap component the tangent transition of the
periodic gluing is the identity. -/
theorem tangentTransitionMap_overlap {n : κ} {y : LocalModel} (hy : y ∈ slab 2 3) :
    (loopGluingOf κ t).tangentTransitionMap (n, false) (n, true) y
      = ContinuousLinearMap.id ℝ LocalModel := by
  have hmem : y ∈ (loopGluingOf κ t).W (n, false) (n, true) := by
    rw [loopGluingOf_W_same]; exact Or.inr hy
  have hderiv : HasFDerivAt (fun x : LocalModel => φb t false true x)
      (ContinuousLinearMap.id ℝ LocalModel) y := by
    refine (hasFDerivAt_id y).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_slab 1.5 4).mem_nhds
      (show y ∈ slab 1.5 4 from ⟨by linarith [hy.1], by linarith [hy.2]⟩)] with z hz
    exact φb_ft_of_gt t hz.1
  rw [BaseGluingData.tangentTransitionMap,
    fderivWithin_of_isOpen ((loopGluingOf κ t).isOpen_W _ _) hmem]
  exact hderiv.fderiv

/-- **DERIVED (Task 36).**  On the wrap-around component, read from the second piece, the
tangent transition of the periodic gluing is again the twist `T`. -/
theorem tangentTransitionMap_unwrap {n : κ} {y : LocalModel} (hy : y ∈ slab 4 5) :
    (loopGluingOf κ t).tangentTransitionMap (n, true) (n, false) y
      = (t.T : LocalModel →L[ℝ] LocalModel) := by
  have hmem : y ∈ (loopGluingOf κ t).W (n, true) (n, false) := by
    rw [loopGluingOf_W_same]; exact Or.inl hy
  have hderiv : HasFDerivAt (fun x : LocalModel => φb t true false x)
      (t.T : LocalModel →L[ℝ] LocalModel) y := by
    have h0 : HasFDerivAt (fun x : LocalModel => x - wrapVec)
        (ContinuousLinearMap.id ℝ LocalModel) y := (hasFDerivAt_id y).sub_const wrapVec
    have hw : HasFDerivAt (unwrap t)
        ((t.T : LocalModel →L[ℝ] LocalModel).comp (ContinuousLinearMap.id ℝ LocalModel)) y :=
      ((t.T : LocalModel →L[ℝ] LocalModel).hasFDerivAt).comp y h0
    rw [ContinuousLinearMap.comp_id] at hw
    refine hw.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_slab 3.5 6).mem_nhds
      (show y ∈ slab 3.5 6 from ⟨by linarith [hy.1], by linarith [hy.2]⟩)] with z hz
    exact φb_tf_of_gt t hz.1
  rw [BaseGluingData.tangentTransitionMap,
    fderivWithin_of_isOpen ((loopGluingOf κ t).isOpen_W _ _) hmem]
  exact hderiv.fderiv

/-- **DERIVED (Task 36).**  On the ordinary overlap component, read from the second piece,
the tangent transition of the periodic gluing is the identity. -/
theorem tangentTransitionMap_overlap' {n : κ} {y : LocalModel} (hy : y ∈ slab 2 3) :
    (loopGluingOf κ t).tangentTransitionMap (n, true) (n, false) y
      = ContinuousLinearMap.id ℝ LocalModel := by
  have hmem : y ∈ (loopGluingOf κ t).W (n, true) (n, false) := by
    rw [loopGluingOf_W_same]; exact Or.inr hy
  have hderiv : HasFDerivAt (fun x : LocalModel => φb t true false x)
      (ContinuousLinearMap.id ℝ LocalModel) y := by
    refine (hasFDerivAt_id y).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_slab 1 3.5).mem_nhds
      (show y ∈ slab 1 3.5 from ⟨by linarith [hy.1], by linarith [hy.2]⟩)] with z hz
    exact φb_tf_of_lt t hz.2
  rw [BaseGluingData.tangentTransitionMap,
    fderivWithin_of_isOpen ((loopGluingOf κ t).isOpen_W _ _) hmem]
  exact hderiv.fderiv

end Tangent

/-! ## Two test points, one in each incidence component -/

section TestPoints

variable {κ : Type} [DecidableEq κ] (t : LoopTwist) (n : κ)

/-- A point of the wrap-around incidence component. -/
def pWrap : LocalModel := ((0.5 : ℝ), 0)

/-- A point of the ordinary incidence component. -/
def pOver : LocalModel := ((2.5 : ℝ), 0)

theorem pWrap_fst : pWrap.1 = (0.5 : ℝ) := rfl

theorem pOver_fst : pOver.1 = (2.5 : ℝ) := rfl

theorem pWrap_mem_slab : pWrap ∈ slab 0 1 :=
  mem_slab.2 ⟨by rw [pWrap_fst]; norm_num, by rw [pWrap_fst]; norm_num⟩

theorem pOver_mem_slab : pOver ∈ slab 2 3 :=
  mem_slab.2 ⟨by rw [pOver_fst]; norm_num, by rw [pOver_fst]; norm_num⟩

theorem pWrap_mem_D : pWrap ∈ (loopGluingOf κ t).D (n, false) :=
  slab_mono (le_refl 0) (by norm_num) pWrap_mem_slab

theorem pOver_mem_D : pOver ∈ (loopGluingOf κ t).D (n, false) :=
  slab_mono (by norm_num) (by norm_num) pOver_mem_slab

theorem pOver_mem_D' : pOver ∈ (loopGluingOf κ t).D (n, true) :=
  slab_mono (le_refl 2) (by norm_num) pOver_mem_slab

theorem pWrap_mem_W : pWrap ∈ (loopGluingOf κ t).W (n, false) (n, true) := by
  rw [loopGluingOf_W_same]
  exact Or.inl pWrap_mem_slab

theorem pOver_mem_W : pOver ∈ (loopGluingOf κ t).W (n, false) (n, true) := by
  rw [loopGluingOf_W_same]
  exact Or.inr pOver_mem_slab

theorem φ_pOver : (loopGluingOf κ t).φ (n, false) (n, true) pOver = pOver :=
  φb_ft_of_gt t (by rw [pOver_fst]; norm_num)

theorem isPreconnected_D (p : κ × Bool) : IsPreconnected ((loopGluingOf κ t).D p) := by
  obtain ⟨-, b⟩ := p
  cases b
  · exact isPreconnected_slab 0 3
  · exact isPreconnected_slab 2 5

end TestPoints

end Task36

end

/-! ## Axiom audit -/

#print axioms Task36.loopGluingOf
#print axioms Task36.loopGluingOf_smoothGluing
#print axioms Task36.loopGluingOf_isManifold
#print axioms Task36.det_flipEquiv
#print axioms Task36.tangentTransitionMap_wrap
#print axioms Task36.tangentTransitionMap_overlap
