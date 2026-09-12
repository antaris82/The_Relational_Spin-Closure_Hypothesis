import RequestProject.Spine.AlgebraicTopology.DirectSumComplex

/-!
# Homology of a direct sum of chain complexes, over an arbitrary index type

The homology of an `α`-indexed direct sum of copies of a chain complex `C` of `ℤ₂`-modules is
the `α`-indexed direct sum of the homology of `C`, for an **arbitrary** index type `α`:

`H_q(⊕_{α} C) ≅ ⊕_{α} H_q(C)`,

the comparison being the map `sumHomologyMap` of
`RequestProject.Spine.AlgebraicTopology.DirectSumComplex`, i.e. the map sending
`Finsupp.single s m` to the class `H_q(ι_s) m` of the `s`-summand inclusion.

## Contents

* `isIso_sumHomologyMap_of_splitting` — **the general splitting criterion.**  A family of chain
  maps `Ι s : C ⟶ K` with retractions `P s : K ⟶ C` satisfying `Ι s ≫ P s = 𝟙`,
  `Ι s ≫ P t = 0` for `s ≠ t` and the *local finiteness* condition that every chain of `K` is
  the sum of its finitely many nonzero components, induces an isomorphism
  `(α →₀ H_q(C)) ≅ H_q(K)`.  No finiteness of `α` is assumed.
* `isIso_sumHomologyMap` — the special case of a finite index type, where local finiteness is
  the identity `∑ s, P s ≫ Ι s = 𝟙 K`.
* `finsuppCx_sum_support_single` — local finiteness for the `Finsupp`-model `finsuppCx α C` of
  the direct sum: a chain `x : α →₀ C_q` is the sum over its (finite) support of the chains
  `Finsupp.single s (x s)`.  This is the only place where the finite-support property of the
  direct sum is used, and it replaces any finiteness assumption on `α`.
* `isIso_sumHomologyMap_finsuppCxι` — the arbitrary-index direct-sum homology theorem itself.
* `isIso_sumHomologyMap_of_iso` — its transported form: if some isomorphism of chain complexes
  `Θ : finsuppCx α C ⟶ K` is given, the comparison built from the composites
  `finsuppCxι s ≫ Θ` is an isomorphism.

## The argument

Injectivity is formal: applying `H_q(P t)` to the image of `c : α →₀ H_q(C)` returns `c t`,
because the retractions are orthogonal idempotents on homology.

Surjectivity is where finite support enters.  A class `y ∈ H_q(K)` is `π z` for a cycle `z`
(`homologyπ` is an epimorphism), and the underlying chain `i z ∈ K_q` is, by local finiteness,
fixed by the idempotent `e_S = ∑_{s ∈ S} P s ≫ Ι s` for some *finite* `S`.  Since `iCycles` is
a monomorphism, `e_S` fixes `z`, hence fixes `y`; and additivity of the homology functor turns
`H_q(e_S) y = y` into the required expression of `y` as the finite sum
`∑_{s ∈ S} H_q(Ι s) (H_q(P s) y)`.

Decidable equality of `α` is used classically for ordinary `Finset`/`Finsupp` manipulations
only; it carries no finiteness information.

Nothing here is specific to singular homology.
-/

noncomputable section

open CategoryTheory Limits

universe u

namespace SpineTask23

section Splitting

variable {α : Type u} {C K : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ}

/-- The comparison map evaluated on an arbitrary element: a finite sum over the support. -/
theorem sumHomologyMap_apply (Ι : α → (C ⟶ K)) (q : ℕ) (c : α →₀ ↥(C.homology q)) :
    (sumHomologyMap Ι q).hom c
      = ∑ s ∈ c.support, (HomologicalComplex.homologyMap (Ι s) q).hom (c s) := rfl

/-- The retraction `P t` recovers the `t`-th coefficient from the image of the comparison
map.  This is the formal half of the splitting criterion and needs no finiteness. -/
theorem homologyMap_retraction_sumHomologyMap (Ι : α → (C ⟶ K)) (P : α → (K ⟶ C))
    (h1 : ∀ s, Ι s ≫ P s = 𝟙 C) (h2 : ∀ s t, s ≠ t → Ι s ≫ P t = 0) (q : ℕ) (t : α)
    (c : α →₀ ↥(C.homology q)) :
    (HomologicalComplex.homologyMap (P t) q).hom ((sumHomologyMap Ι q).hom c) = c t := by
  classical
  have hba : ∀ (s : α) (m : ↥(C.homology q)),
      (HomologicalComplex.homologyMap (P s) q).hom
        ((HomologicalComplex.homologyMap (Ι s) q).hom m) = m := by
    intro s m
    rw [homologyMap_comp_apply, h1, HomologicalComplex.homologyMap_id]
    rfl
  have hba0 : ∀ (s t : α), s ≠ t → ∀ m : ↥(C.homology q),
      (HomologicalComplex.homologyMap (P t) q).hom
        ((HomologicalComplex.homologyMap (Ι s) q).hom m) = 0 := by
    intro s t hst m
    rw [homologyMap_comp_apply, h2 s t hst, HomologicalComplex.homologyMap_zero]
    rfl
  rw [sumHomologyMap_apply, map_sum]
  by_cases ht : t ∈ c.support
  · rw [Finset.sum_eq_single_of_mem t ht (fun s _ hst => hba0 s t hst (c s))]
    exact hba t (c t)
  · rw [Finset.sum_eq_zero (fun s hs => hba0 s t (fun h => ht (h ▸ hs)) (c s))]
    exact (Finsupp.notMem_support_iff.1 ht).symm

/-- A finite sum of chain maps acts degreewise as the sum of the actions. -/
theorem hom_finset_sum_f_apply {β : Type*} (f : β → (K ⟶ K)) (S : Finset β) (q : ℕ)
    (x : K.X q) : ((∑ s ∈ S, f s).f q).hom x = ∑ s ∈ S, ((f s).f q).hom x := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      simp [HomologicalComplex.add_f_apply]

/-- **The local-finiteness step.**  If the chain `x` underlying a cycle is fixed by the finite
partial idempotent `∑_{s ∈ S} P s ≫ Ι s`, then so is the homology class of that cycle. -/
theorem homologyMap_finset_idem (Ι : α → (C ⟶ K)) (P : α → (K ⟶ C)) (q : ℕ) (S : Finset α)
    (z : ↥(K.cycles q)) (hz : ∑ s ∈ S, ((P s ≫ Ι s).f q).hom ((K.iCycles q).hom z)
      = (K.iCycles q).hom z) :
    (HomologicalComplex.homologyMap (∑ s ∈ S, P s ≫ Ι s) q).hom ((K.homologyπ q).hom z)
      = (K.homologyπ q).hom z := by
  have hcy : (HomologicalComplex.cyclesMap (∑ s ∈ S, P s ≫ Ι s) q).hom z = z := by
    refine (ModuleCat.mono_iff_injective (K.iCycles q)).1 inferInstance ?_
    have h := congrArg (fun g : K.cycles q ⟶ K.X q => g.hom z)
      (HomologicalComplex.cyclesMap_i (∑ s ∈ S, P s ≫ Ι s) q)
    refine h.trans ?_
    show ((∑ s ∈ S, P s ≫ Ι s).f q).hom ((K.iCycles q).hom z) = _
    rw [hom_finset_sum_f_apply, hz]
  have hnat : (HomologicalComplex.homologyMap (∑ s ∈ S, P s ≫ Ι s) q).hom
        ((K.homologyπ q).hom z)
      = (K.homologyπ q).hom
        ((HomologicalComplex.cyclesMap (∑ s ∈ S, P s ≫ Ι s) q).hom z) :=
    congrArg (fun g : K.cycles q ⟶ K.homology q => g.hom z)
      (HomologicalComplex.homologyπ_naturality (∑ s ∈ S, P s ≫ Ι s) q)
  rw [hnat, hcy]

/-- **The general splitting criterion, arbitrary index type.**  A family `Ι` of chain maps
`C ⟶ K` with orthogonal retractions `P` which is *locally finite* — every chain of `K` is the
sum of its finitely many nonzero components — induces an isomorphism `(α →₀ H_q C) ≅ H_q K`.
No finiteness assumption is placed on the index type `α`. -/
theorem isIso_sumHomologyMap_of_splitting (Ι : α → (C ⟶ K)) (P : α → (K ⟶ C))
    (h1 : ∀ s, Ι s ≫ P s = 𝟙 C) (h2 : ∀ s t, s ≠ t → Ι s ≫ P t = 0)
    (h3 : ∀ (q : ℕ) (x : K.X q), ∃ S : Finset α, ∑ s ∈ S, ((P s ≫ Ι s).f q).hom x = x)
    (q : ℕ) : IsIso (sumHomologyMap Ι q) := by
  classical
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, ?_⟩
  · intro c c' hcc
    refine Finsupp.ext fun t => ?_
    have h := congrArg (HomologicalComplex.homologyMap (P t) q).hom hcc
    rwa [homologyMap_retraction_sumHomologyMap Ι P h1 h2 q t c,
      homologyMap_retraction_sumHomologyMap Ι P h1 h2 q t c'] at h
  · intro y
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ q)).1 inferInstance y
    obtain ⟨S, hS⟩ := h3 q ((K.iCycles q).hom z)
    have hfix : (HomologicalComplex.homologyMap (∑ s ∈ S, P s ≫ Ι s) q).hom y = y := by
      rw [← hz]; exact homologyMap_finset_idem Ι P q S z hS
    refine ⟨∑ s ∈ S, Finsupp.single s ((HomologicalComplex.homologyMap (P s) q).hom y), ?_⟩
    rw [map_sum]
    calc ∑ s ∈ S, (sumHomologyMap Ι q).hom
            (Finsupp.single s ((HomologicalComplex.homologyMap (P s) q).hom y))
        = ∑ s ∈ S, (HomologicalComplex.homologyMap (P s ≫ Ι s) q).hom y := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [sumHomologyMap_single]
          exact homologyMap_comp_apply (P s) (Ι s) q y
      _ = (HomologicalComplex.homologyMap (∑ s ∈ S, P s ≫ Ι s) q).hom y :=
          (homologyMap_sum_apply (fun s => P s ≫ Ι s) S q y).symm
      _ = y := hfix

/-- **The finite splitting criterion.**  If the family `Ι` of chain maps `C ⟶ K` admits
retractions exhibiting `K` as the finite direct sum of the images, then the comparison map on
homology is an isomorphism.  A special case of `isIso_sumHomologyMap_of_splitting`: over a
finite index type the local finiteness condition is the completeness identity
`∑ s, P s ≫ Ι s = 𝟙 K`. -/
theorem isIso_sumHomologyMap [Fintype α] [DecidableEq α] (Ι : α → (C ⟶ K)) (P : α → (K ⟶ C))
    (h1 : ∀ s, Ι s ≫ P s = 𝟙 C) (h2 : ∀ s t, s ≠ t → Ι s ≫ P t = 0)
    (h3 : ∑ s : α, P s ≫ Ι s = 𝟙 K) (q : ℕ) : IsIso (sumHomologyMap Ι q) := by
  refine isIso_sumHomologyMap_of_splitting Ι P h1 h2 (fun q x => ⟨Finset.univ, ?_⟩) q
  rw [← hom_finset_sum_f_apply (fun s => P s ≫ Ι s) Finset.univ q x, h3]
  rfl

end Splitting

section FinsuppCx

variable {α : Type u} {C : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ}

/-- **Finite support.**  A chain of the direct sum is the sum, over its finite support, of its
components.  This is the substitute for a finiteness assumption on the index type. -/
theorem finsuppCx_sum_support_single (q : ℕ) (x : (finsuppCx α C).X q) :
    ∑ s ∈ (show α →₀ ↥(C.X q) from x).support,
        ((finsuppCxπ α C s ≫ finsuppCxι α C s).f q).hom x = x := by
  show ∑ s ∈ (show α →₀ ↥(C.X q) from x).support,
    (Finsupp.single s ((show α →₀ ↥(C.X q) from x) s) : α →₀ ↥(C.X q)) = x
  exact Finsupp.sum_single _

/-- **The arbitrary-index direct-sum homology theorem.**
`H_q(⊕_{s : α} C) ≅ ⊕_{s : α} H_q(C)`, the comparison being the map determined by the summand
inclusions.  The index type `α` is arbitrary; only the finite support of the chains of the
direct sum is used. -/
theorem isIso_sumHomologyMap_finsuppCxι (q : ℕ) :
    IsIso (sumHomologyMap (finsuppCxι α C) q) :=
  isIso_sumHomologyMap_of_splitting _ (finsuppCxπ α C)
    (fun _ => finsuppCxι_π_self _) (fun _ _ hst => finsuppCxι_π_ne hst)
    (fun q x => ⟨_, finsuppCx_sum_support_single q x⟩) q

/-- Postcomposing the whole family with a fixed chain map postcomposes the comparison with the
induced map on homology. -/
theorem sumHomologyMap_comp_right {K L : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ}
    (Ι : α → (C ⟶ K)) (Θ : K ⟶ L) (q : ℕ) :
    sumHomologyMap (fun s => Ι s ≫ Θ) q
      = sumHomologyMap Ι q ≫ HomologicalComplex.homologyMap Θ q := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext fun s m => ?_)
  show (sumHomologyMap (fun s => Ι s ≫ Θ) q).hom (Finsupp.single s m)
    = (HomologicalComplex.homologyMap Θ q).hom ((sumHomologyMap Ι q).hom (Finsupp.single s m))
  rw [sumHomologyMap_single, sumHomologyMap_single, homologyMap_comp_apply]

/-- **The transported form.**  If some isomorphism of chain complexes identifies `K` with the
`α`-fold direct sum of `C`, then the comparison map on homology built from the composites of
the summand inclusions with that isomorphism is an isomorphism.  The index type `α` is
arbitrary. -/
theorem isIso_sumHomologyMap_of_iso {K : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ}
    (Θ : finsuppCx α C ⟶ K) [IsIso Θ] (q : ℕ) :
    IsIso (sumHomologyMap (fun s => finsuppCxι α C s ≫ Θ) q) := by
  haveI := isIso_sumHomologyMap_finsuppCxι (α := α) (C := C) q
  haveI : IsIso (HomologicalComplex.homologyMap Θ q) := by
    change IsIso ((HomologicalComplex.homologyFunctor (ModuleCat.{u} (ZMod 2))
      (ComplexShape.down ℕ) q).map Θ)
    infer_instance
  rw [sumHomologyMap_comp_right]
  infer_instance

end FinsuppCx

end SpineTask23
