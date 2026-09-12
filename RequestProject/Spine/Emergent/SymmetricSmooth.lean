import RequestProject.Spine.Emergent.SmoothStructure
import RequestProject.Spine.Emergent.SymmetricCanonical

/-!
# Spine / Emergent : the symmetric sector in the smooth category

**Tenth module of the manifold-emergence layer (Task 33, §7).**

Once the smooth gate of `RequestProject.Spine.Emergent.SmoothStructure` is closed, the
canonical identifications of `RequestProject.Spine.Emergent.SymmetricCanonical` can be
upgraded from homeomorphisms to Mathlib `Diffeomorph`s, because the coordinate changes of
the symmetric sector are identities.  No new assumption is needed: the symmetric datum
satisfies `SmoothGluing` already (Task 32).

* `EmergentBase.symmetricGluing.isManifold` — the symmetric emergent base is a `C^∞`
  manifold over the local model.
* `EmergentBase.symmetricGluing.chartAt_apply`,
  `EmergentBase.symmetricGluing.chartAt_symm_apply` — in the symmetric sector *every* chart
  of the reconstructed atlas is the intrinsic quotient coordinate, whatever representative
  the quotient machinery selects.  This is the fact that makes the comparison smooth.
* `EmergentBase.symmetricCanonicalDiffeomorph` — the canonical comparison of two
  presentations, in the smooth category, together with the identity/inverse/composition
  coherence laws.

**Boundary.**  The statement `Space (symmetricGluing ι hD) ≃ₘ D` is *not* formulated here:
it would require fixing a charted-space structure on the subtype `D` and proving its
compatibility, which is a different (and purely conventional) comparison.  The canonicity
content asked for — *the same symmetric primitive determines a canonical diffeomorphism
class of emergent bases* — is exactly what `symmetricCanonicalDiffeomorph` and its
coherence laws express.
-/

noncomputable section

namespace EmergentBase

universe t t' t''

open BaseGluingData symmetricGluing

variable {D : Set LocalModel} (hD : IsOpen D)

namespace symmetricGluing

/-- **DERIVED (Task 33).**  The symmetric emergent base is a `C^∞` manifold over the local
model: it satisfies the Task-32 smoothness condition, and the Task-33 smooth gate applies. -/
theorem isManifold (ι : Type t) :
    IsManifold (modelWithCornersSelf ℝ LocalModel) (⊤ : ℕ∞) (Space (symmetricGluing ι hD)) :=
  BaseGluingData.isManifold_of_smoothGluing (symmetricGluing.smoothGluing hD)

/-- **DERIVED (Task 33).**  In the symmetric sector the chart of *any* index is the
intrinsic quotient coordinate. -/
theorem pieceChart_eq_coordinate {ι : Type t} (i : ι)
    (hne : Nonempty ((symmetricGluing ι hD).D i : Set LocalModel))
    (p : Space (symmetricGluing ι hD)) :
    (symmetricGluing ι hD).pieceChart i hne p = ((coordinate hD p : LocalModel)) := by
  obtain ⟨q, rfl⟩ := (symmetricGluing ι hD).mk_surjective p
  have hq : (symmetricGluing ι hD).quotMk q
      = (symmetricGluing ι hD).chart i ⟨(q.2 : LocalModel), q.2.2⟩ :=
    chart_independent_of_index hD q.1 i _
  rw [hq, BaseGluingData.pieceChart_apply]
  rfl

/-- **DERIVED (Task 33).**  Consequently the chart selected at *any* point of the symmetric
emergent base is the intrinsic quotient coordinate: the representative chosen by the
quotient machinery is irrelevant. -/
theorem chartAt_apply {ι : Type t} (x p : Space (symmetricGluing ι hD)) :
    (chartAt LocalModel x) p = ((coordinate hD p : LocalModel)) :=
  pieceChart_eq_coordinate hD _ _ p

@[simp] theorem chartAt_source {ι : Type t} (x : Space (symmetricGluing ι hD)) :
    (chartAt LocalModel x).source = Set.univ := by
  change ((symmetricGluing ι hD).chartOfPoint x).source = Set.univ
  rw [(symmetricGluing ι hD).chartOfPoint_eq_pieceChart x, BaseGluingData.pieceChart_source]
  exact chartRange_eq_univ hD _

@[simp] theorem chartAt_target {ι : Type t} (x : Space (symmetricGluing ι hD)) :
    (chartAt LocalModel x).target = D := by
  change ((symmetricGluing ι hD).chartOfPoint x).target = D
  rw [(symmetricGluing ι hD).chartOfPoint_eq_pieceChart x, BaseGluingData.pieceChart_target]
  rfl

theorem chartAt_symm_apply {ι : Type t} [Nonempty ι] (x : Space (symmetricGluing ι hD))
    {v : LocalModel} (hv : v ∈ D) :
    (chartAt LocalModel x).symm v = (baseHomeomorph ι hD).symm ⟨v, hv⟩ := by
  change ((symmetricGluing ι hD).chartOfPoint x).symm v = _
  rw [(symmetricGluing ι hD).chartOfPoint_eq_pieceChart x,
    BaseGluingData.pieceChart_symm_apply _ hv]
  exact (baseHomeomorph_symm_apply hD ι _ ⟨v, hv⟩).symm

end symmetricGluing

/-! ## The canonical comparison is smooth -/

/-- **DERIVED (Task 33), PRINCIPAL — the canonical symmetric comparison is smooth.**  In the
symmetric sector every chart is the intrinsic coordinate, so the canonical comparison of two
presentations is, in charts, the identity. -/
theorem contMDiff_symmetricCanonicalHomeomorph (ι : Type t) (κ : Type t')
    [Nonempty ι] [Nonempty κ] :
    ContMDiff (modelWithCornersSelf ℝ LocalModel) (modelWithCornersSelf ℝ LocalModel)
      (⊤ : ℕ∞) (symmetricCanonicalHomeomorph ι κ hD) := by
  haveI := symmetricGluing.isManifold hD ι
  haveI := symmetricGluing.isManifold hD κ
  intro x
  have hsrc : (chartAt LocalModel x).source ∈ nhds x := by
    rw [symmetricGluing.chartAt_source hD x]
    exact Filter.univ_mem
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ LocalModel) (modelWithCornersSelf ℝ LocalModel)
      (⊤ : ℕ∞) (chartAt LocalModel x) x := contMDiffOn_chart.contMDiffAt hsrc
  have hcoord : ((coordinate hD x : LocalModel)) ∈ D := (coordinate hD x).2
  have htgt : (chartAt LocalModel (symmetricCanonicalHomeomorph ι κ hD x)).target
      ∈ nhds ((chartAt LocalModel x) x) := by
    rw [symmetricGluing.chartAt_target hD, symmetricGluing.chartAt_apply hD x x]
    exact hD.mem_nhds hcoord
  have h2 : ContMDiffAt (modelWithCornersSelf ℝ LocalModel) (modelWithCornersSelf ℝ LocalModel)
      (⊤ : ℕ∞) (chartAt LocalModel (symmetricCanonicalHomeomorph ι κ hD x)).symm
      ((chartAt LocalModel x) x) := contMDiffOn_chart_symm.contMDiffAt htgt
  refine (h2.comp x h1).congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)
  rw [Function.comp_apply, symmetricGluing.chartAt_apply hD x p,
    symmetricGluing.chartAt_symm_apply hD _ (coordinate hD p).2]
  rfl

/-- **NEWLY DEFINED (Task 33), PRINCIPAL — the canonical comparison in the smooth
category.**  Two presentations of the symmetric sector on the same local domain are
canonically *diffeomorphic*, by the intrinsic-coordinate comparison of
`symmetricCanonicalHomeomorph`. -/
def symmetricCanonicalDiffeomorph (ι : Type t) (κ : Type t') [Nonempty ι] [Nonempty κ]
    {D : Set LocalModel} (hD : IsOpen D) :
    Diffeomorph (modelWithCornersSelf ℝ LocalModel) (modelWithCornersSelf ℝ LocalModel)
      (Space (symmetricGluing ι hD)) (Space (symmetricGluing κ hD)) (⊤ : ℕ∞) where
  toEquiv := (symmetricCanonicalHomeomorph ι κ hD).toEquiv
  contMDiff_toFun := contMDiff_symmetricCanonicalHomeomorph hD ι κ
  contMDiff_invFun := contMDiff_symmetricCanonicalHomeomorph hD κ ι

@[simp] theorem symmetricCanonicalDiffeomorph_apply (ι : Type t) (κ : Type t')
    [Nonempty ι] [Nonempty κ] (p : Space (symmetricGluing ι hD)) :
    symmetricCanonicalDiffeomorph ι κ hD p = symmetricCanonicalHomeomorph ι κ hD p := rfl

/-- **DERIVED (Task 33), smooth coherence law 1.** -/
theorem symmetricCanonicalDiffeomorph_refl (ι : Type t) [Nonempty ι] :
    ⇑(symmetricCanonicalDiffeomorph ι ι hD) = id := by
  funext p
  simp only [symmetricCanonicalDiffeomorph_apply]
  exact congrFun (congrArg (fun e : Space (symmetricGluing ι hD) ≃ₜ
      Space (symmetricGluing ι hD) => ⇑e) (symmetricCanonicalHomeomorph_refl ι hD)) p

/-- **DERIVED (Task 33), smooth coherence law 2.** -/
theorem symmetricCanonicalDiffeomorph_symm (ι : Type t) (κ : Type t')
    [Nonempty ι] [Nonempty κ] :
    ⇑(symmetricCanonicalDiffeomorph ι κ hD).symm = ⇑(symmetricCanonicalDiffeomorph κ ι hD) :=
  rfl

/-- **DERIVED (Task 33), smooth coherence law 3.** -/
theorem symmetricCanonicalDiffeomorph_trans (ι : Type t) (κ : Type t') (μ : Type t'')
    [Nonempty ι] [Nonempty κ] [Nonempty μ] :
    ⇑((symmetricCanonicalDiffeomorph ι κ hD).trans (symmetricCanonicalDiffeomorph κ μ hD))
      = ⇑(symmetricCanonicalDiffeomorph ι μ hD) := by
  funext p
  exact congrArg (baseHomeomorph μ hD).symm ((baseHomeomorph κ hD).apply_symm_apply _)

/-- **DERIVED (Task 33), PRINCIPAL — the smooth canonicity certificate of the symmetric
sector.**  The same symmetric primitive determines a canonical *diffeomorphism* class of
emergent bases: the comparison maps are the intrinsic-coordinate identifications, they are
smooth with smooth inverses, and they satisfy the identity, inverse and composition laws. -/
theorem symmetric_emergent_base_canonical_smooth (ι : Type t) (κ : Type t') (μ : Type t'')
    [Nonempty ι] [Nonempty κ] [Nonempty μ] :
    IsManifold (modelWithCornersSelf ℝ LocalModel) (⊤ : ℕ∞) (Space (symmetricGluing ι hD)) ∧
    (∀ p, symmetricCanonicalDiffeomorph ι κ hD p = symmetricCanonicalHomeomorph ι κ hD p) ∧
    ⇑(symmetricCanonicalDiffeomorph ι ι hD) = id ∧
    ⇑(symmetricCanonicalDiffeomorph ι κ hD).symm = ⇑(symmetricCanonicalDiffeomorph κ ι hD) ∧
    ⇑((symmetricCanonicalDiffeomorph ι κ hD).trans (symmetricCanonicalDiffeomorph κ μ hD))
      = ⇑(symmetricCanonicalDiffeomorph ι μ hD) :=
  ⟨symmetricGluing.isManifold hD ι, fun _ => rfl, symmetricCanonicalDiffeomorph_refl hD ι,
    symmetricCanonicalDiffeomorph_symm hD ι κ, symmetricCanonicalDiffeomorph_trans hD ι κ μ⟩

end EmergentBase

end

/-! ## Axiom audit of the Task-33 smooth-closure and canonicity endpoints -/

#print axioms EmergentBase.BaseGluingData.pieceChart
#print axioms EmergentBase.BaseGluingData.chartOfPoint_eq_pieceChart
#print axioms EmergentBase.BaseGluingData.transition_source
#print axioms EmergentBase.BaseGluingData.transition_apply
#print axioms EmergentBase.BaseGluingData.contDiffOn_transition
#print axioms EmergentBase.BaseGluingData.hasGroupoid_of_smoothGluing
#print axioms EmergentBase.BaseGluingData.isManifold_of_smoothGluing
#print axioms EmergentBase.BaseGluingData.smoothEmergentManifoldCertificate
#print axioms EmergentBase.not_smoothGluing_nonSmoothGluing
#print axioms EmergentBase.nonSmoothGluing_topological_reconstruction
#print axioms EmergentBase.symmetricGluing.coordinate
#print axioms EmergentBase.symmetricGluing.coordinate_chart
#print axioms EmergentBase.symmetricGluing.chart_coordinate
#print axioms EmergentBase.symmetricGluing.chart_independent_of_index
#print axioms EmergentBase.symmetricGluing.baseHomeomorph
#print axioms EmergentBase.symmetricGluing.baseHomeomorph_symm_apply
#print axioms EmergentBase.symmetricCanonicalHomeomorph
#print axioms EmergentBase.symmetricCanonicalHomeomorph_refl
#print axioms EmergentBase.symmetricCanonicalHomeomorph_symm
#print axioms EmergentBase.symmetricCanonicalHomeomorph_trans
#print axioms EmergentBase.symmetric_emergent_base_canonical
#print axioms EmergentBase.symmetricGluing.isManifold
#print axioms EmergentBase.contMDiff_symmetricCanonicalHomeomorph
#print axioms EmergentBase.symmetricCanonicalDiffeomorph
#print axioms EmergentBase.symmetric_emergent_base_canonical_smooth
