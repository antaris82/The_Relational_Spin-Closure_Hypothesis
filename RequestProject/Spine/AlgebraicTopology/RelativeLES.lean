import RequestProject.Spine.AlgebraicTopology.RelativeChains
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Task 14, WP8 and WP13 : the pair long exact sequence, and the middle five-lemma step

## WP8 — the long exact sequence of a pair

The pinned Mathlib supplies the long exact homology sequence of a short exact sequence of
homological complexes (`ShortComplex.ShortExact.δ`, `homology_exact₁/₂/₃`,
`HomologicalComplex.HomologySequence.δ_naturality`).  Combined with WP7
(`SpineTask14.relSC_shortExact`) this gives the pair sequence

`⋯ → H_q(S) → H_q(T) → H_q(T,S) → H_{q-1}(S) → ⋯`

for any degreewise injective `f : S ⟶ T`, in particular for a topological pair and for a
simplicial subcomplex pair.  Nothing beyond the pinned machinery is needed; the content of
this section is the instantiation, including naturality (`pairDelta_naturality`).

## WP13 — the middle five-lemma step

For the one-skeleton-step comparison one needs the implication

`τ₁ quasi-iso  ∧  τ₃ quasi-iso  ⟹  τ₂ quasi-iso`

for a morphism `φ : S₁ ⟶ S₂` of short exact sequences of chain complexes.  The pin proves only
the `τ₃` version (`HomologicalComplex.HomologySequence.quasiIso_τ₃`); the `τ₁` and `τ₂`
versions are explicitly left as a TODO there.  `isIso_homologyMap_τ₂` and `quasiIso_τ₂` below
supply the missing `τ₂` version for `ℕ`-indexed chain complexes, following exactly the proof
architecture of the pinned `τ₃` version (four lemmas applied to the six-term exact sequences of
`composableArrows₅`), with the extra bottom-degree case `i = 0` — where the chain complex has
no further differential — handled by the pinned short-complex four lemma
`ShortComplex.epi_of_epi_of_epi_of_epi`.

This step is *pure homological algebra*: it does not depend on the topological blocker recorded
in `TASK14_SPECIALIZED_CELL_ATTACHMENT.md`.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial AlgebraicTopology ComposableArrows
open NerveGeom SpineTask13

universe u

namespace SpineTask14

/-! ## WP8 : the pair sequence -/

section Pair

variable {S T : SSet.{u}} (f : S ⟶ T)

/-- The homology of a simplicial set with `ℤ₂`-coefficients (unnormalized complex). -/
abbrev sSetHomology (S : SSet.{u}) (q : ℕ) : ModuleCat.{u} (ZMod 2) :=
  (sSetChainComplexFunctor.obj S).homology q

/-- **Relative homology of a pair**, `H_q(T,S;ℤ₂)`. -/
abbrev relHomology (q : ℕ) : ModuleCat.{u} (ZMod 2) := (relChainCx f).homology q

variable (hf : ∀ n, Function.Injective (f.app n))

include hf

/-- The map `H_q(S) → H_q(T)`. -/
abbrev pairIota (q : ℕ) : sSetHomology S q ⟶ sSetHomology T q :=
  HomologicalComplex.homologyMap (sSetChainComplexFunctor.map f) q

/-- The map `H_q(T) → H_q(T,S)`. -/
abbrev pairProj (q : ℕ) : sSetHomology T q ⟶ relHomology f q :=
  HomologicalComplex.homologyMap (relProj f) q

/-- **WP8, the connecting homomorphism** `∂ : H_{q+1}(T,S) → H_q(S)`. -/
def pairDelta (q : ℕ) : relHomology f (q + 1) ⟶ sSetHomology S q :=
  (relSC_shortExact f hf).δ (q + 1) q (by simp)

/-- **WP8, exactness at `H_q(S)`**: `H_{q+1}(T,S) → H_q(S) → H_q(T)`. -/
theorem pair_exact₁ (q : ℕ) :
    (ShortComplex.mk _ _ ((relSC_shortExact f hf).δ_comp (q + 1) q (by simp))).Exact :=
  (relSC_shortExact f hf).homology_exact₁ (q + 1) q (by simp)

/-- **WP8, exactness at `H_q(T)`**: `H_q(S) → H_q(T) → H_q(T,S)`. -/
theorem pair_exact₂ (q : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (relSC f).f q)
      (HomologicalComplex.homologyMap (relSC f).g q) (by
        rw [← HomologicalComplex.homologyMap_comp, (relSC f).zero,
          HomologicalComplex.homologyMap_zero])).Exact :=
  (relSC_shortExact f hf).homology_exact₂ q

/-- **WP8, exactness at `H_{q+1}(T,S)`**: `H_{q+1}(T) → H_{q+1}(T,S) → H_q(S)`. -/
theorem pair_exact₃ (q : ℕ) :
    (ShortComplex.mk _ _ ((relSC_shortExact f hf).comp_δ (q + 1) q (by simp))).Exact :=
  (relSC_shortExact f hf).homology_exact₃ (q + 1) q (by simp)

end Pair

/-! ## Naturality of the pair sequence -/

/-- A commuting square of degreewise injective maps induces a morphism of the two short exact
sequences of WP7. -/
def relSCMap {S T S' T' : SSet.{u}} (f : S ⟶ T) (f' : S' ⟶ T')
    (u : S ⟶ S') (v : T ⟶ T') (hsq : f ≫ v = u ≫ f') : relSC f ⟶ relSC f' where
  τ₁ := sSetChainComplexFunctor.map u
  τ₂ := sSetChainComplexFunctor.map v
  τ₃ := relChainCxMap f f' u v hsq
  comm₁₂ := by
    show sSetChainComplexFunctor.map u ≫ sSetChainComplexFunctor.map f'
      = sSetChainComplexFunctor.map f ≫ sSetChainComplexFunctor.map v
    rw [← sSetChainComplexFunctor.map_comp, ← sSetChainComplexFunctor.map_comp, hsq]
  comm₂₃ := relChainCxMap_relProj f f' u v hsq

/-- **WP8, naturality of the connecting map.** -/
theorem pairDelta_naturality {S T S' T' : SSet.{u}} (f : S ⟶ T) (f' : S' ⟶ T')
    (u : S ⟶ S') (v : T ⟶ T') (hsq : f ≫ v = u ≫ f')
    (hf : ∀ n, Function.Injective (f.app n)) (hf' : ∀ n, Function.Injective (f'.app n)) (q : ℕ) :
    pairDelta f hf q ≫ HomologicalComplex.homologyMap (sSetChainComplexFunctor.map u) q
      = HomologicalComplex.homologyMap (relChainCxMap f f' u v hsq) (q + 1)
          ≫ pairDelta f' hf' q :=
  HomologicalComplex.HomologySequence.δ_naturality (relSCMap f f' u v hsq)
    (relSC_shortExact f hf) (relSC_shortExact f' hf') (q + 1) q (by simp)

/-! ## WP13 : the missing `τ₂` four/five-lemma -/

section FiveLemma

open HomologicalComplex HomologicalComplex.HomologySequence

variable {C : Type*} [Category* C] [Abelian C]
  {S₁ S₂ : ShortComplex (ChainComplex C ℕ)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

include hS₁ hS₂

/-- **Mono half of the middle four lemma.**  If `H_{i+1}(X₃) → H_{i+1}(Y₃)` is epi and
`H_i(X₁) → H_i(Y₁)`, `H_i(X₃) → H_i(Y₃)` are mono, then `H_i(X₂) → H_i(Y₂)` is mono. -/
theorem mono_homologyMap_τ₂ (i : ℕ)
    (h₀ : Epi (homologyMap φ.τ₃ (i + 1)))
    (h₁ : Mono (homologyMap φ.τ₁ i))
    (h₃ : Mono (homologyMap φ.τ₃ i)) :
    Mono (homologyMap φ.τ₂ i) := by
  have hij : (ComplexShape.down ℕ).Rel (i + 1) i := by simp
  exact Abelian.mono_of_epi_of_mono_of_mono
    ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ (i + 1) i hij))
    (composableArrows₅_exact hS₁ (i + 1) i hij).δ₀.δ₀
    (composableArrows₅_exact hS₂ (i + 1) i hij).δ₀.δ₀ h₀ h₁ h₃

/-- **Epi half of the middle four lemma.** -/
theorem epi_homologyMap_τ₂ (i : ℕ)
    (h₀ : Epi (homologyMap φ.τ₁ i))
    (h₂ : Epi (homologyMap φ.τ₃ i))
    (h₃ : ∀ j, (ComplexShape.down ℕ).Rel i j → Mono (homologyMap φ.τ₁ j)) :
    Epi (homologyMap φ.τ₂ i) := by
  by_cases hi : ∃ j, (ComplexShape.down ℕ).Rel i j
  · obtain ⟨j, hij⟩ := hi
    exact Abelian.epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
      (composableArrows₅_exact hS₁ i j hij).δlast.δlast
      (composableArrows₅_exact hS₂ i j hij).δlast.δlast h₀ h₂ (h₃ j hij)
  · have _ := hS₁.epi_g
    have hg : Epi (homologyMap S₁.g i) :=
      epi_homologyMap_of_epi_of_not_rel S₁.g i (fun j hij => hi ⟨j, hij⟩)
    exact Abelian.epi_of_epi_of_epi_of_epi (mapComposableArrows₂ φ i)
      (composableArrows₂_exact hS₂ i) hg h₀ h₂

/-- **WP13, the middle five lemma.**  For a morphism of short exact sequences of `ℕ`-indexed
chain complexes, if the outer two morphisms are isomorphisms on homology in every degree, so is
the middle one. -/
theorem isIso_homologyMap_τ₂
    (h₁ : ∀ i, IsIso (homologyMap φ.τ₁ i)) (h₃ : ∀ i, IsIso (homologyMap φ.τ₃ i)) (i : ℕ) :
    IsIso (homologyMap φ.τ₂ i) := by
  have hm : Mono (homologyMap φ.τ₂ i) := by
    have := h₃ (i + 1); have := h₁ i; have := h₃ i
    exact mono_homologyMap_τ₂ φ hS₁ hS₂ i inferInstance inferInstance inferInstance
  have he : Epi (homologyMap φ.τ₂ i) := by
    have := h₁ i; have := h₃ i
    exact epi_homologyMap_τ₂ φ hS₁ hS₂ i inferInstance inferInstance
      (fun j _ => by have := h₁ j; infer_instance)
  exact isIso_of_mono_of_epi _

/-- **WP13, quasi-isomorphism form.** -/
theorem quasiIso_τ₂ (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  refine isIso_homologyMap_τ₂ φ hS₁ hS₂ (fun j => ?_) (fun j => ?_) i
  · rw [← quasiIsoAt_iff_isIso_homologyMap]; infer_instance
  · rw [← quasiIsoAt_iff_isIso_homologyMap]; infer_instance

end FiveLemma

end SpineTask14
