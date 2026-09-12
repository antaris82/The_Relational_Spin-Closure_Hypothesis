import RequestProject.Spine.SpinNative.Rigidity
import RequestProject.Spine.Cech.SpinCocycle

/-!
# Spine / Comparison : the kernel-twist freedom as a Čech `Ȟ¹(𝓤;ℤ₂)`-type gate

This module identifies the rigidity gate of
`RequestProject.Spine.SpinNative.Rigidity` — "every continuous kernel-valued Čech 1-cocycle
of the cover is a coboundary" — with a **cohomological** condition expressed in the *only*
cohomology object the project actually formalises at this point: the nerve-level Čech
cohomology `CechZ2.H1 𝓤.U = Ȟ¹(𝓤;ℤ₂)` of `RequestProject.Spine.Cech.Cohomology`, on the
**same fixed cover**.

It is a comparison module: it is the only place where the Spin-native uniqueness layer and
the Čech/ℤ₂ machinery of the standard branch are seen together, and no production module
imports it.

## What is proved

* `SpinNative.kerCocycleCochain` — on a cover whose double overlaps are preconnected, a
  continuous kernel-valued Čech 1-cocycle is constant on each overlap (the inherited
  `CechSpinZ2.ConstOn₂.ofPreconnected`) and therefore defines an honest element of
  `Č¹(𝓤;ℤ₂)` through the kernel dictionary `ker ρ ≅ ℤ₂`;
* `SpinNative.d_kerCocycleCochain` — it is a Čech **1-cocycle**: `δ a = 0`;
* `SpinNative.kernelTwistsGaugeTrivial_of_cover_H1_trivial` — **the gate**: if
  `Ȟ¹(𝓤;ℤ₂) = 0` then every kernel twist is gauge trivial, i.e.
  `SpinNative.KernelTwistsGaugeTrivial` holds;
* `SpinNative.spinStructure_unique_up_to_gauge_of_cover_H1_trivial` — consequently every two
  Spin structures over the same visible transition data are gauge equivalent.

## The gap that remains — stated explicitly

`Ȟ¹(𝓤;ℤ₂)` here is the cohomology of the **nerve of the given cover** with constant `ℤ₂`
coefficients.  It is *not* proved anywhere in this project to be the singular cohomology
`H¹(X;ℤ₂)` of the base: the Čech-to-singular comparison exists in the project only as an
explicit *specification* (`RequestProject.Spine.Cech.SingularBridgeSpec`,
`RequestProject.Spine.GoodCover.SingularComparisonSpec`,
`RequestProject.Spine.Cohomology.CechBridgeSpec`) and is not discharged.  Accordingly no
statement here mentions `H¹(X;ℤ₂)`, and `TASK31_PROVENANCE.md` records the missing step.

Two further hypotheses are visible in the statements and are not hidden:

* preconnectedness of the double overlaps (needed to pass from a *continuous kernel-valued
  function* on an overlap to a *single* `ℤ₂` per overlap; it is automatic on a good cover, by
  `GoodCoverZ2.isPreconnected_overlap₂`);
* a `CechSpinZ2.KernelSign P`, i.e. the identification `ker ρ ≅ ℤ₂` — for the intrinsic Spin
  projection this is the frozen `CechSpinZ2.spinKernelSign`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace SpinNative

open CechSpinLift CechZ2 CechSpinZ2 NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}
  {𝓤 : CechCover X ι} {P : InternalProjection L G}

/-! ## A kernel 1-cocycle as a Čech 1-cochain -/

/-- On preconnected double overlaps a kernel 1-cocycle is constant on each overlap.  This is
the inherited constancy theorem, not a new one. -/
def kerCocycleConst (ε : KerCocycle P 𝓤)
    (hpre : ∀ i j, IsPreconnected (𝓤.overlap₂ i j)) : ConstOn₂ 𝓤 ε.e :=
  ConstOn₂.ofPreconnected P (fun i j => ε.isKer i j) hpre

/-- **NEWLY DEFINED (Task 31).**  A kernel-valued Čech 1-cocycle, pushed through the kernel
dictionary `ker ρ ≅ ℤ₂` into `Č¹(𝓤;ℤ₂)`. -/
def kerCocycleCochain (S : KernelSign P) (ε : KerCocycle P 𝓤)
    (hpre : ∀ i j, IsPreconnected (𝓤.overlap₂ i j)) : Cochain 𝓤.U 1 :=
  aCochain S (kerCocycleConst ε hpre)

theorem kerCocycleCochain_apply (S : KernelSign P) (ε : KerCocycle P 𝓤)
    (hpre : ∀ i j, IsPreconnected (𝓤.overlap₂ i j)) (i j : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₂ i j) :
    kerCocycleCochain S ε hpre (nerve₁ 𝓤 i j ⟨x, hx⟩) = S.sgn (ε.e i j x) := by
  show S.sgn ((kerCocycleConst ε hpre).val i j) = _
  rw [(kerCocycleConst ε hpre).spec i j x hx]

/-- **DERIVED_NATIVE (Task 31), principal.**  The translated kernel 1-cocycle is a genuine
Čech 1-cocycle: `δ a = 0`.  The proof is the multiplicative cocycle law
`ε_ij ε_jk = ε_ik` read through the sign dictionary. -/
theorem d_kerCocycleCochain (S : KernelSign P) (ε : KerCocycle P 𝓤)
    (hpre : ∀ i j, IsPreconnected (𝓤.overlap₂ i j)) :
    d 𝓤.U 1 (kerCocycleCochain S ε hpre) = 0 := by
  funext σ
  obtain ⟨i, j, k, h₃, rfl⟩ :
      ∃ i j k, ∃ h : (𝓤.overlap₃ i j k).Nonempty, σ = nerve₂ 𝓤 i j k h := by
    obtain ⟨y, hy⟩ := nonempty₃ σ
    exact ⟨_, _, _, ⟨y, hy⟩, (nerve₂_self σ ⟨y, hy⟩).symm⟩
  obtain ⟨x, hx⟩ := h₃
  have hij : x ∈ 𝓤.overlap₂ i j := 𝓤.overlap₃_subset_ij i j k hx
  have hjk : x ∈ 𝓤.overlap₂ j k := 𝓤.overlap₃_subset_jk i j k hx
  have hik : x ∈ 𝓤.overlap₂ i k := 𝓤.overlap₃_subset_ik i j k hx
  have hcoc : S.sgn (ε.e i k x) = S.sgn (ε.e i j x) + S.sgn (ε.e j k x) := by
    rw [← ε.cocycle i j k x hx, S.sgn_mul ((ε.isKer i j).2 x hij) ((ε.isKer j k).2 x hjk)]
  show (∑ t : Fin 3, kerCocycleCochain S ε hpre (face t (nerve₂ 𝓤 i j k ⟨x, hx⟩))) = 0
  rw [Fin.sum_univ_three, face_nerve₂_zero 𝓤 i j k _ ⟨x, hjk⟩,
    face_nerve₂_one 𝓤 i j k _ ⟨x, hik⟩, face_nerve₂_two 𝓤 i j k _ ⟨x, hij⟩,
    kerCocycleCochain_apply S ε hpre j k hjk, kerCocycleCochain_apply S ε hpre i k hik,
    kerCocycleCochain_apply S ε hpre i j hij, hcoc]
  generalize S.sgn (ε.e i j x) = A
  generalize S.sgn (ε.e j k x) = B
  have key : ∀ A B : ZMod 2, B + (A + B) + A = 0 := by decide
  exact key A B

/-! ## The gate -/

open scoped Classical in
/-- **DERIVED_NATIVE (Task 31), PRINCIPAL — the `Ȟ¹(𝓤;ℤ₂)` gate.**  On a cover with
preconnected double overlaps, if the first Čech cohomology of the cover with `ℤ₂`
coefficients vanishes, then every continuous kernel-valued Čech 1-cocycle is a coboundary:
the rigidity condition `SpinNative.KernelTwistsGaugeTrivial` holds.

This is a statement about the **fixed cover**: `CechZ2.H1 𝓤.U` is the cohomology of the nerve
of `𝓤`, and is not identified anywhere in this project with `H¹(X;ℤ₂)`. -/
theorem kernelTwistsGaugeTrivial_of_cover_H1_trivial (S : KernelSign P)
    (hpre : ∀ i j, IsPreconnected (𝓤.overlap₂ i j)) (hH1 : ∀ h : H1 𝓤.U, h = 0) :
    KernelTwistsGaugeTrivial P 𝓤 := by
  classical
  intro ε
  obtain ⟨b, hb⟩ :=
    (mk_eq_zero_iff_exists
      (cocycleOf (kerCocycleCochain S ε hpre) (d_kerCocycleCochain S ε hpre))).1 (hH1 _)
  have hb' : ∀ (i j : ι) (x : X) (hx : x ∈ 𝓤.overlap₂ i j),
      d 𝓤.U 0 b (nerve₁ 𝓤 i j ⟨x, hx⟩) = S.sgn (ε.e i j x) := by
    intro i j x hx
    rw [hb]
    exact kerCocycleCochain_apply S ε hpre i j hx
  refine ⟨⟨fun i _ => if h : (𝓤.U i).Nonempty then S.ofZ (b (nerve₀ 𝓤 i h)) else 1,
    fun i => ⟨continuousOn_const, fun x hx => ?_⟩⟩, fun i j x hx => ?_⟩
  · show (if h : (𝓤.U i).Nonempty then S.ofZ (b (nerve₀ 𝓤 i h)) else 1) ∈ P.Ker
    rw [dif_pos ⟨x, hx⟩]
    exact S.ofZ_mem _
  · have hi : (𝓤.U i).Nonempty := ⟨x, hx.1⟩
    have hj : (𝓤.U j).Nonempty := ⟨x, hx.2⟩
    have hli : (if h : (𝓤.U i).Nonempty then S.ofZ (b (nerve₀ 𝓤 i h)) else 1)
        = S.ofZ (b (nerve₀ 𝓤 i hi)) := dif_pos hi
    have hlj : (if h : (𝓤.U j).Nonempty then S.ofZ (b (nerve₀ 𝓤 j h)) else 1)
        = S.ofZ (b (nerve₀ 𝓤 j hj)) := dif_pos hj
    show ε.e i j x = (if h : (𝓤.U i).Nonempty then S.ofZ (b (nerve₀ 𝓤 i h)) else 1)
        * (if h : (𝓤.U j).Nonempty then S.ofZ (b (nerve₀ 𝓤 j h)) else 1)⁻¹
    rw [hli, hlj]
    -- both sides lie in the kernel, so it is enough to compare their signs
    refine S.sgn_injOn ((ε.isKer i j).2 x hx)
      (Subgroup.mul_mem _ (S.ofZ_mem _) (Subgroup.inv_mem _ (S.ofZ_mem _))) ?_
    rw [S.sgn_mul (S.ofZ_mem _) (Subgroup.inv_mem _ (S.ofZ_mem _)),
      S.sgn_inv (S.ofZ_mem _), S.sgn_ofZ, S.sgn_ofZ, ← hb' i j x hx]
    show _ = b (nerve₀ 𝓤 i hi) + b (nerve₀ 𝓤 j hj)
    have hd : d 𝓤.U 0 b (nerve₁ 𝓤 i j ⟨x, hx⟩)
        = b (nerve₀ 𝓤 j hj) + b (nerve₀ 𝓤 i hi) := by
      show (∑ t : Fin 2, b (face t (nerve₁ 𝓤 i j ⟨x, hx⟩))) = _
      rw [Fin.sum_univ_two, face_nerve₁_zero 𝓤 i j _ hj, face_nerve₁_one 𝓤 i j _ hi]
    rw [hd, add_comm]

/-- **DERIVED_NATIVE (Task 31), PRINCIPAL endpoint of the cohomological gate.**  On a cover
with preconnected double overlaps whose first Čech `ℤ₂`-cohomology vanishes, any two Spin
structures over the same visible transition data are gauge equivalent, and the gauge quotient
is a subsingleton. -/
theorem spinStructure_unique_up_to_gauge_of_cover_H1_trivial (S : KernelSign P)
    (hpre : ∀ i j, IsPreconnected (𝓤.overlap₂ i j)) (hH1 : ∀ h : H1 𝓤.U, h = 0)
    (T : VisibleCocycle G 𝓤) :
    (∀ C C' : SpinStructureOver P T, GaugeEquiv P C.data C'.data) ∧
      Subsingleton (GaugeClass P T) :=
  ⟨fun C C' => gaugeEquiv_of_kernelTwistsGaugeTrivial
      (kernelTwistsGaugeTrivial_of_cover_H1_trivial S hpre hH1) C C',
   subsingleton_gaugeClass (kernelTwistsGaugeTrivial_of_cover_H1_trivial S hpre hH1) T⟩

end SpinNative
