import RequestProject.Spine.Cech.CoverNerve
import RequestProject.Spine.Cech.KernelSign
import RequestProject.Spine.E2.Cech.Core

/-!
# Task 6, WP6–WP8, WP10 : the Spin-lift defect as a genuine Čech 2-cocycle

This module transports the **existing** Task-3 Spin-lift defect into the Spin-independent Čech
complex of WP2–WP4.  Nothing about the defect is redefined: every statement below consumes
`CechSpinLift.SpinLiftFamily.defect` and the Task-3 theorems about it.

## The one extra hypothesis, stated honestly

A Task-3 defect `c_ijk : X → ker ρ` is a *function on the triple overlap*; a Čech cochain with
**constant** coefficients in `ℤ₂` is a single value per overlap.  A translation therefore needs
the defect to be constant on each triple overlap.  That is not automatic and it is not assumed
silently: it is the explicit datum

`CechSpinZ2.ConstOn₃ 𝓤 D.defect`,

and likewise `ConstOn₂` for kernel-valued 1-cochains.  Both are *constructed* — not postulated
— from the Task-3 local-constancy theorem as soon as the relevant overlaps are preconnected
(`ConstOn₃.ofPreconnectedDefect`, `ConstOn₂.ofPreconnected`).  Preconnected overlaps are a
genuinely weaker hypothesis than a good cover: no contractibility, no acyclicity and nothing
about higher homotopy is used or assumed anywhere.

## Contents

* WP6 `zCochain` — the Task-3 defect pushed through `ker ρ ≅ ℤ₂` into `Č²(𝓤;ℤ₂)`, with
  `zCochain_apply` exhibiting the translation pointwise;
* WP7 `d_zCochain` — `δ_Č z = 0`, derived from the multiplicative quadruple-overlap identity
  `CechSpinLift.SpinLiftFamily.defect_delta_eq_one` (`c_jkl c_ikl⁻¹ c_ijl c_ijk⁻¹ = 1`);
* WP8 `zCochain_change_of_lift` — `z' = z + δ_Č a`, the additive form of the Task-3
  change-of-lift law, and `spinCechClass_lift_independent`;
* WP10 `spinCechClass_eq_zero_iff_exists_coherent` — the vanishing criterion in standard Čech
  language.

**Interpretation boundary.**  `[z]` is a topological Spin-lift obstruction on a fixed cover and
nothing else: not curvature, not torsion, not holonomy, not a synchronization mismatch, not a
matter/antimatter sign, not a dynamical state; and it is not claimed to be `w₂(TM)`.
-/

namespace CechSpinZ2

open CechSpinLift CechZ2 NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}
  {𝓤 : CechCover X ι} {P : InternalProjection L G} {T : VisibleCocycle G 𝓤}

/-! ## Constancy data -/

/-- A kernel-valued Čech 1-cochain of Task 3 that is *constant on each double overlap*,
together with its constant values. -/
structure ConstOn₂ (𝓤 : CechCover X ι) (e : ι → ι → (X → L)) where
  /-- The constant value on the double overlap. -/
  val : ι → ι → L
  /-- The value is attained everywhere on the double overlap. -/
  spec : ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, e i j x = val i j

/-- A Task-3 2-cochain that is *constant on each triple overlap*, together with its constant
values. -/
structure ConstOn₃ (𝓤 : CechCover X ι) (c : ι → ι → ι → (X → L)) where
  /-- The constant value on the triple overlap. -/
  val : ι → ι → ι → L
  /-- The value is attained everywhere on the triple overlap. -/
  spec : ∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k, c i j k x = val i j k

/-- **Constructed, not assumed.**  On preconnected double overlaps a continuous kernel-valued
1-cochain *is* constant: this is the Task-3 local-constancy theorem
`NullSectorTask28.InternalProjection.toKerFun_const_of_connected`. -/
noncomputable def ConstOn₂.ofPreconnected (P : InternalProjection L G) {e : ι → ι → (X → L)}
    (he : IsKerCochain₁ P 𝓤 e) (hpre : ∀ i j, IsPreconnected (𝓤.overlap₂ i j)) :
    ConstOn₂ 𝓤 e := by
  classical
  refine ⟨fun i j => if h : (𝓤.overlap₂ i j).Nonempty then e i j h.choose else 1, ?_⟩
  intro i j x hx
  have hne : (𝓤.overlap₂ i j).Nonempty := ⟨x, hx⟩
  show e i j x = if h : (𝓤.overlap₂ i j).Nonempty then e i j h.choose else 1
  rw [dif_pos hne]
  exact P.toKerFun_const_of_connected (he i j) (hpre i j) hx hne.choose_spec

/-- **Constructed, not assumed.**  On preconnected triple overlaps the Task-3 defect is
constant. -/
noncomputable def ConstOn₃.ofPreconnectedDefect (D : SpinLiftFamily P T)
    (hpre : ∀ i j k, IsPreconnected (𝓤.overlap₃ i j k)) : ConstOn₃ 𝓤 D.defect := by
  classical
  refine ⟨fun i j k => if h : (𝓤.overlap₃ i j k).Nonempty then D.defect i j k h.choose else 1,
    ?_⟩
  intro i j k x hx
  have hne : (𝓤.overlap₃ i j k).Nonempty := ⟨x, hx⟩
  show D.defect i j k x
      = if h : (𝓤.overlap₃ i j k).Nonempty then D.defect i j k h.choose else 1
  rw [dif_pos hne]
  exact D.defect_const_of_preconnected i j k (hpre i j k) hx hne.choose_spec

/-- The constant value of a defect lies in the kernel (as soon as the overlap is nonempty). -/
theorem ConstOn₃.val_mem_ker {D : SpinLiftFamily P T} (V : ConstOn₃ 𝓤 D.defect) (i j k : ι)
    {x : X} (hx : x ∈ 𝓤.overlap₃ i j k) : V.val i j k ∈ P.Ker := by
  rw [← V.spec i j k x hx]
  exact D.defect_mem_ker i j k hx

/-- The constant value of a kernel-valued 1-cochain lies in the kernel. -/
theorem ConstOn₂.val_mem_ker {e : ι → ι → (X → L)} (he : IsKerCochain₁ P 𝓤 e)
    (E : ConstOn₂ 𝓤 e) (i j : ι) {x : X} (hx : x ∈ 𝓤.overlap₂ i j) : E.val i j ∈ P.Ker := by
  rw [← E.spec i j x hx]
  exact (he i j).2 x hx

/-! ## WP6 — the defect as a Čech 2-cochain -/

/-- **WP6, principal.**  The Task-3 triple-overlap defect, pushed through the canonical
isomorphism `ker ρ ≅ ℤ₂`, as a genuine element of `Č²(𝓤;ℤ₂)`. -/
def zCochain (S : KernelSign P) {D : SpinLiftFamily P T} (V : ConstOn₃ 𝓤 D.defect) :
    Cochain 𝓤.U 2 :=
  fun σ => S.sgn (V.val (σ.idx 0) (σ.idx 1) (σ.idx 2))

/-- A kernel-valued Čech 1-cochain of Task 3, pushed to `Č¹(𝓤;ℤ₂)`. -/
def aCochain (S : KernelSign P) {e : ι → ι → (X → L)} (E : ConstOn₂ 𝓤 e) : Cochain 𝓤.U 1 :=
  fun σ => S.sgn (E.val (σ.idx 0) (σ.idx 1))

@[simp] theorem zCochain_idx (S : KernelSign P) {D : SpinLiftFamily P T}
    (V : ConstOn₃ 𝓤 D.defect) (σ : Nerve 𝓤.U 2) :
    zCochain S V σ = S.sgn (V.val (σ.idx 0) (σ.idx 1) (σ.idx 2)) := rfl

@[simp] theorem aCochain_idx (S : KernelSign P) {e : ι → ι → (X → L)} (E : ConstOn₂ 𝓤 e)
    (σ : Nerve 𝓤.U 1) : aCochain S E σ = S.sgn (E.val (σ.idx 0) (σ.idx 1)) := rfl

/-- **WP6, the translation, pointwise.**  On any point of the triple overlap the value of the
Čech cochain is the sign of the Task-3 defect at that point. -/
theorem zCochain_apply (S : KernelSign P) {D : SpinLiftFamily P T} (V : ConstOn₃ 𝓤 D.defect)
    (σ : Nerve 𝓤.U 2) {x : X} (hx : x ∈ 𝓤.overlap₃ (σ.idx 0) (σ.idx 1) (σ.idx 2)) :
    zCochain S V σ = S.sgn (D.defect (σ.idx 0) (σ.idx 1) (σ.idx 2) x) := by
  rw [zCochain_idx, V.spec _ _ _ x hx]

/-- The Čech cochain does not depend on which constancy datum is used. -/
theorem zCochain_indep_of_values (S : KernelSign P) {D : SpinLiftFamily P T}
    (V V' : ConstOn₃ 𝓤 D.defect) : zCochain S V = zCochain S V' := by
  funext σ
  obtain ⟨x, hx⟩ := nonempty₃ σ
  rw [zCochain_apply S V σ hx, zCochain_apply S V' σ hx]

/-! ## WP7 — the Čech 2-cocycle law -/

/-- **WP7, principal endpoint.**  `δ_Č z = 0`: the translated defect is a genuine Čech
2-cocycle.

The proof consumes the multiplicative Task-3 identity `c_jkl · c_ikl⁻¹ · c_ijl · c_ijk⁻¹ = 1`
on the quadruple overlap (`CechSpinLift.SpinLiftFamily.defect_delta_eq_one`) and maps it
through the kernel dictionary: `sgn` turns the product into the sum
`sgn c_jkl + sgn c_ikl + sgn c_ijl + sgn c_ijk` (the two inverses are invisible because
`sgn u⁻¹ = sgn u`), which is exactly the value of the additive Čech coboundary on the
quadruple. -/
theorem d_zCochain (S : KernelSign P) {D : SpinLiftFamily P T} (V : ConstOn₃ 𝓤 D.defect) :
    d 𝓤.U 2 (zCochain S V) = 0 := by
  funext σ
  obtain ⟨x, hx⟩ := nonempty₄ σ
  have hjkl : x ∈ 𝓤.overlap₃ (σ.idx 1) (σ.idx 2) (σ.idx 3) :=
    𝓤.overlap₄_subset_jkl _ _ _ _ hx
  have hikl : x ∈ 𝓤.overlap₃ (σ.idx 0) (σ.idx 2) (σ.idx 3) :=
    𝓤.overlap₄_subset_ikl _ _ _ _ hx
  have hijl : x ∈ 𝓤.overlap₃ (σ.idx 0) (σ.idx 1) (σ.idx 3) :=
    𝓤.overlap₄_subset_ijl _ _ _ _ hx
  have hijk : x ∈ 𝓤.overlap₃ (σ.idx 0) (σ.idx 1) (σ.idx 2) :=
    𝓤.overlap₄_subset_ijk _ _ _ _ hx
  have m1 : D.defect (σ.idx 1) (σ.idx 2) (σ.idx 3) x ∈ P.Ker := D.defect_mem_ker _ _ _ hjkl
  have m2 : D.defect (σ.idx 0) (σ.idx 2) (σ.idx 3) x ∈ P.Ker := D.defect_mem_ker _ _ _ hikl
  have m3 : D.defect (σ.idx 0) (σ.idx 1) (σ.idx 3) x ∈ P.Ker := D.defect_mem_ker _ _ _ hijl
  have m4 : D.defect (σ.idx 0) (σ.idx 1) (σ.idx 2) x ∈ P.Ker := D.defect_mem_ker _ _ _ hijk
  have hkey := D.defect_delta_eq_one (σ.idx 0) (σ.idx 1) (σ.idx 2) (σ.idx 3) hx
  have hsgn : S.sgn (D.defect (σ.idx 1) (σ.idx 2) (σ.idx 3) x)
      + S.sgn (D.defect (σ.idx 0) (σ.idx 2) (σ.idx 3) x)
      + S.sgn (D.defect (σ.idx 0) (σ.idx 1) (σ.idx 3) x)
      + S.sgn (D.defect (σ.idx 0) (σ.idx 1) (σ.idx 2) x) = 0 := by
    have e1 : S.sgn (D.defect (σ.idx 1) (σ.idx 2) (σ.idx 3) x
        * (D.defect (σ.idx 0) (σ.idx 2) (σ.idx 3) x)⁻¹
        * D.defect (σ.idx 0) (σ.idx 1) (σ.idx 3) x
        * (D.defect (σ.idx 0) (σ.idx 1) (σ.idx 2) x)⁻¹) = 0 := by
      rw [hkey, S.sgn_one]
    rw [S.sgn_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 (Subgroup.inv_mem _ m2)) m3)
        (Subgroup.inv_mem _ m4),
      S.sgn_mul (Subgroup.mul_mem _ m1 (Subgroup.inv_mem _ m2)) m3,
      S.sgn_mul m1 (Subgroup.inv_mem _ m2), S.sgn_inv m2, S.sgn_inv m4] at e1
    exact e1
  show (∑ t : Fin 4, zCochain S V (face t σ)) = 0
  rw [Fin.sum_univ_four]
  have f0 : zCochain S V (face 0 σ)
      = S.sgn (D.defect (σ.idx 1) (σ.idx 2) (σ.idx 3) x) := by
    rw [show zCochain S V (face 0 σ)
      = S.sgn (V.val ((face (0 : Fin 4) σ).idx 0) ((face (0 : Fin 4) σ).idx 1)
        ((face (0 : Fin 4) σ).idx 2)) from rfl]
    exact congrArg S.sgn (V.spec _ _ _ x hjkl).symm
  have f1 : zCochain S V (face 1 σ)
      = S.sgn (D.defect (σ.idx 0) (σ.idx 2) (σ.idx 3) x) := by
    rw [show zCochain S V (face 1 σ)
      = S.sgn (V.val ((face (1 : Fin 4) σ).idx 0) ((face (1 : Fin 4) σ).idx 1)
        ((face (1 : Fin 4) σ).idx 2)) from rfl]
    exact congrArg S.sgn (V.spec _ _ _ x hikl).symm
  have f2 : zCochain S V (face 2 σ)
      = S.sgn (D.defect (σ.idx 0) (σ.idx 1) (σ.idx 3) x) := by
    rw [show zCochain S V (face 2 σ)
      = S.sgn (V.val ((face (2 : Fin 4) σ).idx 0) ((face (2 : Fin 4) σ).idx 1)
        ((face (2 : Fin 4) σ).idx 2)) from rfl]
    exact congrArg S.sgn (V.spec _ _ _ x hijl).symm
  have f3 : zCochain S V (face 3 σ)
      = S.sgn (D.defect (σ.idx 0) (σ.idx 1) (σ.idx 2) x) := by
    rw [show zCochain S V (face 3 σ)
      = S.sgn (V.val ((face (3 : Fin 4) σ).idx 0) ((face (3 : Fin 4) σ).idx 1)
        ((face (3 : Fin 4) σ).idx 2)) from rfl]
    exact congrArg S.sgn (V.spec _ _ _ x hijk).symm
  rw [f0, f1, f2, f3]
  exact hsgn

/-- The translated defect as an element of `Ž²(𝓤;ℤ₂)`. -/
def spinCechCocycle (S : KernelSign P) {D : SpinLiftFamily P T} (V : ConstOn₃ 𝓤 D.defect) :
    cocycles 𝓤.U 2 :=
  cocycleOf (zCochain S V) (d_zCochain S V)

/-- **The Spin-lift Čech class** `[z] ∈ Ȟ²(𝓤;ℤ₂)`. -/
def spinCechClass (S : KernelSign P) {D : SpinLiftFamily P T} (V : ConstOn₃ 𝓤 D.defect) :
    H2 𝓤.U :=
  mk (spinCechCocycle S V)

theorem spinCechClass_indep_of_values (S : KernelSign P) {D : SpinLiftFamily P T}
    (V V' : ConstOn₃ 𝓤 D.defect) : spinCechClass S V = spinCechClass S V' :=
  congrArg mk (Subtype.ext (zCochain_indep_of_values S V V'))

/-! ## WP8 — change of lift is a Čech coboundary -/

/-- **WP8, principal endpoint.**  Changing the local Spin lifts changes the Čech 2-cochain by
the coboundary of a genuine Čech 1-cochain:  `z' = z + δ_Č a`, where `a` is the translation of
the kernel-valued comparison cochain `ε = g̃' g̃⁻¹` of Task 3. -/
theorem zCochain_change_of_lift (S : KernelSign P) (D D' : SpinLiftFamily P T)
    (V : ConstOn₃ 𝓤 D.defect) (V' : ConstOn₃ 𝓤 D'.defect)
    (E : ConstOn₂ 𝓤 (SpinLiftFamily.liftRatio D D')) :
    zCochain S V' = zCochain S V + d 𝓤.U 1 (aCochain S E) := by
  funext σ
  obtain ⟨x, hx⟩ := nonempty₃ σ
  have hε : IsKerCochain₁ P 𝓤 (SpinLiftFamily.liftRatio D D') := D.liftRatio_isKerCochain₁ D'
  have hij : x ∈ 𝓤.overlap₂ (σ.idx 0) (σ.idx 1) := 𝓤.overlap₃_subset_ij _ _ _ hx
  have hjk : x ∈ 𝓤.overlap₂ (σ.idx 1) (σ.idx 2) := 𝓤.overlap₃_subset_jk _ _ _ hx
  have hik : x ∈ 𝓤.overlap₂ (σ.idx 0) (σ.idx 2) := 𝓤.overlap₃_subset_ik _ _ _ hx
  have mij : SpinLiftFamily.liftRatio D D' (σ.idx 0) (σ.idx 1) x ∈ P.Ker := (hε _ _).2 x hij
  have mjk : SpinLiftFamily.liftRatio D D' (σ.idx 1) (σ.idx 2) x ∈ P.Ker := (hε _ _).2 x hjk
  have mik : SpinLiftFamily.liftRatio D D' (σ.idx 0) (σ.idx 2) x ∈ P.Ker := (hε _ _).2 x hik
  have mc : D.defect (σ.idx 0) (σ.idx 1) (σ.idx 2) x ∈ P.Ker := D.defect_mem_ker _ _ _ hx
  -- the Task-3 coboundary law, pointwise
  have hrel : D'.defect (σ.idx 0) (σ.idx 1) (σ.idx 2) x
      = delta₁ (SpinLiftFamily.liftRatio D D') (σ.idx 0) (σ.idx 1) (σ.idx 2) x
        * D.defect (σ.idx 0) (σ.idx 1) (σ.idx 2) x :=
    SpinLiftFamily.defect_eq_delta₁_mul D D' hε
      (fun p q y => congrFun (D.lift_eq_liftRatio_mul D' p q) y) _ _ _ hx
  have hsgn : S.sgn (D'.defect (σ.idx 0) (σ.idx 1) (σ.idx 2) x)
      = S.sgn (SpinLiftFamily.liftRatio D D' (σ.idx 0) (σ.idx 1) x)
        + S.sgn (SpinLiftFamily.liftRatio D D' (σ.idx 1) (σ.idx 2) x)
        + S.sgn (SpinLiftFamily.liftRatio D D' (σ.idx 0) (σ.idx 2) x)
        + S.sgn (D.defect (σ.idx 0) (σ.idx 1) (σ.idx 2) x) := by
    rw [hrel, delta₁_apply,
      S.sgn_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ mij mjk) (Subgroup.inv_mem _ mik)) mc,
      S.sgn_mul (Subgroup.mul_mem _ mij mjk) (Subgroup.inv_mem _ mik),
      S.sgn_mul mij mjk, S.sgn_inv mik]
  -- the three faces of `σ`
  have hd : d 𝓤.U 1 (aCochain S E) σ
      = S.sgn (E.val (σ.idx 1) (σ.idx 2)) + S.sgn (E.val (σ.idx 0) (σ.idx 2))
        + S.sgn (E.val (σ.idx 0) (σ.idx 1)) := by
    show (∑ t : Fin 3, aCochain S E (face t σ)) = _
    rw [Fin.sum_univ_three]
    rfl
  rw [Cochain.add_apply, hd, zCochain_apply S V σ hx, zCochain_apply S V' σ hx, hsgn,
    ← E.spec _ _ x hij, ← E.spec _ _ x hjk, ← E.spec _ _ x hik]
  ring

/-- **WP8, principal endpoint.**  The Čech class is independent of the chosen family of local
Spin lifts (given the constancy data required to write the class down at all). -/
theorem spinCechClass_lift_independent (S : KernelSign P) (D D' : SpinLiftFamily P T)
    (V : ConstOn₃ 𝓤 D.defect) (V' : ConstOn₃ 𝓤 D'.defect)
    (E : ConstOn₂ 𝓤 (SpinLiftFamily.liftRatio D D')) :
    spinCechClass S V' = spinCechClass S V := by
  rw [spinCechClass, spinCechClass, mk_eq_mk_iff]
  refine ⟨aCochain S E, ?_⟩
  show d 𝓤.U 1 (aCochain S E) = zCochain S V' - zCochain S V
  rw [zCochain_change_of_lift S D D' V V' E]
  abel

/-- **WP8, corollary under preconnected double overlaps.**  If every double overlap is
preconnected, the comparison cochain is automatically constant, so no extra datum is needed. -/
theorem spinCechClass_lift_independent_of_preconnected (S : KernelSign P)
    (hpre : ∀ i j, IsPreconnected (𝓤.overlap₂ i j)) (D D' : SpinLiftFamily P T)
    (V : ConstOn₃ 𝓤 D.defect) (V' : ConstOn₃ 𝓤 D'.defect) :
    spinCechClass S V' = spinCechClass S V :=
  spinCechClass_lift_independent S D D' V V'
    (ConstOn₂.ofPreconnected P (D.liftRatio_isKerCochain₁ D') hpre)

/-! ## WP10 — the vanishing criterion in standard Čech language -/

open scoped Classical in
/-- A Čech 1-cochain, read back as a kernel-valued Task-3 1-cochain: on each nonempty double
overlap it is the *constant* kernel element with the prescribed sign. -/
noncomputable def kerCochainOf (S : KernelSign P) (𝓤 : CechCover X ι) (a : Cochain 𝓤.U 1) :
    ι → ι → (X → L) :=
  fun i j _ => if h : (𝓤.overlap₂ i j).Nonempty then S.ofZ (a (nerve₁ 𝓤 i j h)) else 1

theorem kerCochainOf_apply_of_mem (S : KernelSign P) (a : Cochain 𝓤.U 1) (i j : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₂ i j) (y : X) :
    kerCochainOf S 𝓤 a i j y = S.ofZ (a (nerve₁ 𝓤 i j ⟨x, hx⟩)) := by
  simp only [kerCochainOf]
  rw [dif_pos ⟨x, hx⟩]

theorem kerCochainOf_isKerCochain₁ (S : KernelSign P) (a : Cochain 𝓤.U 1) :
    IsKerCochain₁ P 𝓤 (kerCochainOf S 𝓤 a) := by
  intro i j
  refine ⟨continuousOn_const, fun x hx => ?_⟩
  rw [kerCochainOf_apply_of_mem S a i j hx x]
  exact S.ofZ_mem _

theorem sgn_kerCochainOf (S : KernelSign P) (a : Cochain 𝓤.U 1) (i j : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₂ i j) :
    S.sgn (kerCochainOf S 𝓤 a i j x) = a (nerve₁ 𝓤 i j ⟨x, hx⟩) := by
  rw [kerCochainOf_apply_of_mem S a i j hx x, S.sgn_ofZ]

/-- **WP10, first half.**  If the Čech class vanishes — i.e. `z = δ_Č a` for a genuine Čech
1-cochain `a` — then the constant kernel-valued twist attached to `a` turns the chosen local
lifts into a **coherent** family: the lifted transition data then satisfies the exact cocycle
law on every triple overlap. -/
theorem isCoherent_twist_of_zCochain_eq_coboundary (S : KernelSign P)
    {D : SpinLiftFamily P T} (V : ConstOn₃ 𝓤 D.defect) (a : Cochain 𝓤.U 1)
    (h : zCochain S V = d 𝓤.U 1 a) :
    (D.twist (kerCochainOf S 𝓤 a) (kerCochainOf_isKerCochain₁ S a)).IsCoherent := by
  classical
  have hε : IsKerCochain₁ P 𝓤 (kerCochainOf S 𝓤 a) := kerCochainOf_isKerCochain₁ S a
  refine ((D.twist (kerCochainOf S 𝓤 a) hε).isCoherent_iff_defect_one).2 ?_
  intro i j k x hx
  have hij : x ∈ 𝓤.overlap₂ i j := 𝓤.overlap₃_subset_ij i j k hx
  have hjk : x ∈ 𝓤.overlap₂ j k := 𝓤.overlap₃_subset_jk i j k hx
  have hik : x ∈ 𝓤.overlap₂ i k := 𝓤.overlap₃_subset_ik i j k hx
  have mij : kerCochainOf S 𝓤 a i j x ∈ P.Ker := (hε i j).2 x hij
  have mjk : kerCochainOf S 𝓤 a j k x ∈ P.Ker := (hε j k).2 x hjk
  have mik : kerCochainOf S 𝓤 a i k x ∈ P.Ker := (hε i k).2 x hik
  have mc : D.defect i j k x ∈ P.Ker := D.defect_mem_ker i j k hx
  have hmem : (D.twist (kerCochainOf S 𝓤 a) hε).defect i j k x ∈ P.Ker :=
    (D.twist (kerCochainOf S 𝓤 a) hε).defect_mem_ker i j k hx
  refine (S.sgn_eq_zero_iff hmem).1 ?_
  rw [D.defect_twist (kerCochainOf S 𝓤 a) hε i j k hx, delta₁_apply,
    S.sgn_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ mij mjk) (Subgroup.inv_mem _ mik)) mc,
    S.sgn_mul (Subgroup.mul_mem _ mij mjk) (Subgroup.inv_mem _ mik), S.sgn_mul mij mjk,
    S.sgn_inv mik]
  -- the defect sign, read off the hypothesis `z = δa`
  have hz : zCochain S V (nerve₂ 𝓤 i j k ⟨x, hx⟩) = S.sgn (D.defect i j k x) := by
    have hval : zCochain S V (nerve₂ 𝓤 i j k ⟨x, hx⟩) = S.sgn (V.val i j k) := rfl
    rw [hval, ← V.spec i j k x hx]
  have hda : d 𝓤.U 1 a (nerve₂ 𝓤 i j k ⟨x, hx⟩)
      = a (nerve₁ 𝓤 j k ⟨x, hjk⟩) + a (nerve₁ 𝓤 i k ⟨x, hik⟩)
        + a (nerve₁ 𝓤 i j ⟨x, hij⟩) := by
    show (∑ t : Fin 3, a (face t (nerve₂ 𝓤 i j k ⟨x, hx⟩))) = _
    rw [Fin.sum_univ_three, face_nerve₂_zero 𝓤 i j k _ ⟨x, hjk⟩,
      face_nerve₂_one 𝓤 i j k _ ⟨x, hik⟩, face_nerve₂_two 𝓤 i j k _ ⟨x, hij⟩]
  have hkey : S.sgn (D.defect i j k x)
      = a (nerve₁ 𝓤 j k ⟨x, hjk⟩) + a (nerve₁ 𝓤 i k ⟨x, hik⟩)
        + a (nerve₁ 𝓤 i j ⟨x, hij⟩) := by
    rw [← hz, h, hda]
  rw [sgn_kerCochainOf S a i j hij, sgn_kerCochainOf S a j k hjk,
    sgn_kerCochainOf S a i k hik, hkey]
  generalize a (nerve₁ 𝓤 j k ⟨x, hjk⟩) = A
  generalize a (nerve₁ 𝓤 i k ⟨x, hik⟩) = B
  generalize a (nerve₁ 𝓤 i j ⟨x, hij⟩) = C
  have key : ∀ A B C : ZMod 2, C + A + B + (A + B + C) = 0 := by decide
  exact key A B C

/-- **WP10, second half.**  Conversely, if some family of local lifts is coherent then — on a
cover with preconnected double overlaps, so that the comparison cochain is constant — the Čech
cochain of any lift family is a genuine Čech coboundary. -/
theorem exists_coboundary_of_isCoherent (S : KernelSign P)
    (hpre : ∀ i j, IsPreconnected (𝓤.overlap₂ i j)) {D : SpinLiftFamily P T}
    (V : ConstOn₃ 𝓤 D.defect) {D' : SpinLiftFamily P T} (hD' : D'.IsCoherent) :
    ∃ a : Cochain 𝓤.U 1, zCochain S V = d 𝓤.U 1 a := by
  classical
  have hdef' : ∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k, D'.defect i j k x = 1 :=
    (D'.isCoherent_iff_defect_one).1 hD'
  let V' : ConstOn₃ 𝓤 D'.defect := ⟨fun _ _ _ => 1, hdef'⟩
  have hzero : zCochain S V' = 0 := by
    funext σ
    show S.sgn (V'.val (σ.idx 0) (σ.idx 1) (σ.idx 2)) = 0
    exact S.sgn_one
  have E : ConstOn₂ 𝓤 (SpinLiftFamily.liftRatio D D') :=
    ConstOn₂.ofPreconnected P (D.liftRatio_isKerCochain₁ D') hpre
  have hchange := zCochain_change_of_lift S D D' V V' E
  refine ⟨aCochain S E, ?_⟩
  funext σ
  have hσ := congrFun hchange σ
  rw [hzero] at hσ
  have key : ∀ p q : ZMod 2, 0 = p + q → p = q := by decide
  exact key _ _ hσ

/-- **WP10, principal endpoint — the vanishing criterion in standard Čech language.**  On a
cover with preconnected double overlaps,

`[z] = 0 ∈ Ȟ²(𝓤;ℤ₂)  ↔  the visible transition cocycle admits coherent Spin lifts`.

The right-hand side is exactly the Task-3 notion: a family of local internal representatives
satisfying the exact cocycle law `g̃_ij g̃_jk = g̃_ik` on every triple overlap.  The statement
consumes the *new* Čech quotient, not the custom Task-3 quotient. -/
theorem spinCechClass_eq_zero_iff_exists_coherent (S : KernelSign P)
    (hpre : ∀ i j, IsPreconnected (𝓤.overlap₂ i j)) {D : SpinLiftFamily P T}
    (V : ConstOn₃ 𝓤 D.defect) :
    spinCechClass S V = 0 ↔ ∃ D' : SpinLiftFamily P T, D'.IsCoherent := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (mk_eq_zero_iff_exists (spinCechCocycle S V)).1 h
    exact ⟨D.twist (kerCochainOf S 𝓤 a) (kerCochainOf_isKerCochain₁ S a),
      isCoherent_twist_of_zCochain_eq_coboundary S V a ha.symm⟩
  · rintro ⟨D', hD'⟩
    obtain ⟨a, ha⟩ := exists_coboundary_of_isCoherent S hpre V hD'
    exact (mk_eq_zero_iff_exists (spinCechCocycle S V)).2 ⟨a, ha.symm⟩

end CechSpinZ2
