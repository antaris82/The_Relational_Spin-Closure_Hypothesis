import RequestProject.Spine.E2.Descent.DefectFreeHardening

/-!
# Task 29, Packages C, D and E: the same-pair discrepancy `κ`, the descent verdict, and
conditional gluing

**HARD TARGET A, second half (items 30–46).**

Package C (items 30–34) isolates the *same-pair* datum.  Two refinement patches `V_ijα`,
`V_ijβ` of one fixed ordinary transition `g_ij` carry representatives `u_ijα`, `u_ijβ`; on
their intersection the inherited comparison convention gives

`κ_ijαβ = u_ijβ * u_ijα⁻¹`,

which is exactly the inherited `relFactor` of the two representatives — kernel-valued,
continuous and locally constant — together with the patch identities

`κ_ijαα = 1`,  `κ_ijβα = κ_ijαβ⁻¹`,  `κ_ijαγ = κ_ijβγ * κ_ijαβ`.

`κ` is *not* the Task-XXVIII triple defect (items 33, 34): `δ` compares the composition of
three different ordinary transitions on a triple overlap, `κ` compares two representatives of
one fixed ordinary transition on an intersection of refinement patches.  They are kept
formally distinct throughout.

Package D (items 35–40) settles the central question of hard target A.  **Verdict: PROVED.**
For the inherited defect-free predicate — which quantifies over *all* index triples,
including repeated ones, and all patches — triple-defect freeness *does* force same-pair
agreement:

`tripleDefectFree_imp_pairwiseRefinementCoherent`.

The mechanism is the repeated-index triple `(i,i,j)` together with the identity
normalization `u_ii = 1` of Package B.  The repeated indices are load-bearing: the negative
control `TripleDefectFreeDistinct` (defect-freeness for pairwise *distinct* index triples
only) does **not** imply same-pair agreement, and an explicit counterexample is preserved in
`Counterexample.lean`.

Package E (items 41–46) is the conditional gluing theorem: agreeing refined representatives
glue to one continuous representative on the whole original pair overlap.  It is stated
conditionally on `PairwiseRefinementCoherent` and nothing asserts that this condition always
holds (item 46).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask29

universe u v w t

open NullSectorTask28
open NullSectorTask28.InternalProjection

section Kappa

variable {L : Type w} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {P : InternalProjection L G} {B : Type u}
  [TopologicalSpace B] {ι : Type t} {S : TransitionSystem B ι G}

/-! ## Package C — the same-pair refinement discrepancy -/

/-- **NEWLY DEFINED (item 30), principal.**  The relative kernel factor of two refinement
patches carrying representatives of the *same* ordinary transition `g_ij`, in the exact
inherited convention: `κ_ijαβ = u_ijβ * u_ijα⁻¹`, so that `u_ijβ = κ_ijαβ * u_ijα`. -/
def kappa (C : InternalTransitionCandidate P S) (i j : ι) (a b : C.Idx i j) :
    ↥(S.U i ∩ S.U j) → L :=
  relFactor (C.u i j a) (C.u i j b)

/-- The domain of the same-pair discrepancy: the intersection of the two refinement
patches. -/
def kappaDom (C : InternalTransitionCandidate P S) (i j : ι) (a b : C.Idx i j) :
    Set ↥(S.U i ∩ S.U j) :=
  C.V i j a ∩ C.V i j b

@[simp] theorem kappa_apply (C : InternalTransitionCandidate P S) (i j : ι) (a b : C.Idx i j)
    (x : ↥(S.U i ∩ S.U j)) : kappa C i j a b x = C.u i j b x * (C.u i j a x)⁻¹ := rfl

/-- **PACKAGE C (item 31), principal.**  The same-pair discrepancy is a continuous
kernel-valued function on the intersection of the two patches.  This is the inherited
kernel-ambiguity theorem for two representatives of one ordinary map. -/
theorem kappa_isKerFunOn (C : InternalTransitionCandidate P S) (i j : ι) (a b : C.Idx i j) :
    P.IsKerFunOn (kappaDom C i j a b) (kappa C i j a b) :=
  C.kerAmbiguity i j a b

/-- **PACKAGE C (item 31).**  `κ` is kernel-valued.  For a two-to-one projection the kernel
is the inherited `KerSign`, so `κ` is `KerSign`-valued. -/
theorem kappa_mem_ker (C : InternalTransitionCandidate P S) (i j : ι) (a b : C.Idx i j)
    {x : ↥(S.U i ∩ S.U j)} (hx : x ∈ kappaDom C i j a b) : kappa C i j a b x ∈ P.Ker :=
  (kappa_isKerFunOn C i j a b).2 x hx

/-- **PACKAGE C (item 31).**  `κ` is continuous on its domain. -/
theorem kappa_continuousOn (C : InternalTransitionCandidate P S) (i j : ι) (a b : C.Idx i j) :
    ContinuousOn (kappa C i j a b) (kappaDom C i j a b) :=
  (kappa_isKerFunOn C i j a b).1

/-- **PACKAGE C (item 31), principal.**  `κ` is locally constant: the kernel carries the
inherited discrete topology. -/
theorem kappa_isLocallyConstant (C : InternalTransitionCandidate P S) (i j : ι)
    (a b : C.Idx i j) :
    IsLocallyConstant (P.toKerFun (kappa_isKerFunOn C i j a b)) :=
  P.isLocallyConstant_toKerFun _

/-- **PACKAGE C (item 30).**  The defining identity: `u_ijβ = κ_ijαβ * u_ijα`. -/
theorem kappa_mul (C : InternalTransitionCandidate P S) (i j : ι) (a b : C.Idx i j)
    (x : ↥(S.U i ∩ S.U j)) : kappa C i j a b x * C.u i j a x = C.u i j b x :=
  relFactor_mul_self _ _ x

/-- **PACKAGE C (item 32), patch identity.**  `κ_ijαα = 1`. -/
@[simp] theorem kappa_self (C : InternalTransitionCandidate P S) (i j : ι) (a : C.Idx i j)
    (x : ↥(S.U i ∩ S.U j)) : kappa C i j a a x = 1 := by
  simp [kappa, relFactor]

/-- **PACKAGE C (item 32), patch inverse law.**  `κ_ijβα = κ_ijαβ⁻¹`. -/
theorem kappa_swap (C : InternalTransitionCandidate P S) (i j : ι) (a b : C.Idx i j)
    (x : ↥(S.U i ∩ S.U j)) : kappa C i j b a x = (kappa C i j a b x)⁻¹ := by
  simp [kappa, relFactor, mul_inv_rev]

/-- **PACKAGE C (item 32), patch composition law, in the exact order.**
`κ_ijαγ = κ_ijβγ * κ_ijαβ` on triple intersections of refinement patches. -/
theorem kappa_comp (C : InternalTransitionCandidate P S) (i j : ι) (a b c : C.Idx i j)
    (x : ↥(S.U i ∩ S.U j)) :
    kappa C i j a c x = kappa C i j b c x * kappa C i j a b x := by
  simp only [kappa_apply]
  group

/-- **PACKAGE C.**  The discrepancy is trivial exactly when the two representatives
agree. -/
theorem kappa_eq_one_iff (C : InternalTransitionCandidate P S) (i j : ι) (a b : C.Idx i j)
    (x : ↥(S.U i ∩ S.U j)) : kappa C i j a b x = 1 ↔ C.u i j b x = C.u i j a x := by
  simp [kappa, relFactor, mul_inv_eq_one]

/-! ## Package D — does `δ = 1` force same-pair descent? -/

/-- **NEWLY DEFINED (item 35), principal.**  Representatives of the same ordinary transition
`g_ij` stored on two refinement patches agree on the intersection of those patches. -/
def PairwiseRefinementCoherent (C : InternalTransitionCandidate P S) : Prop :=
  ∀ (i j : ι) (a b : C.Idx i j), ∀ x ∈ kappaDom C i j a b, C.u i j a x = C.u i j b x

/-- **PACKAGE D.**  Pairwise coherence is exactly triviality of every same-pair
discrepancy. -/
theorem pairwiseRefinementCoherent_iff_kappa_trivial (C : InternalTransitionCandidate P S) :
    PairwiseRefinementCoherent C ↔
      ∀ (i j : ι) (a b : C.Idx i j), ∀ x ∈ kappaDom C i j a b, kappa C i j a b x = 1 := by
  constructor
  · intro h i j a b x hx
    exact (kappa_eq_one_iff C i j a b x).2 (h i j a b x hx).symm
  · intro h i j a b x hx
    exact ((kappa_eq_one_iff C i j a b x).1 (h i j a b x hx)).symm

/-- **PACKAGE D (items 36–40), principal endpoint — THE VERDICT: PROVED.**
`tripleDefectFree_imp_pairwiseRefinementCoherent`: for the inherited defect-free predicate,
which quantifies over **all** index triples (repeated ones included) and all refinement
patches, triviality of every triple defect *does* force representatives of one fixed ordinary
transition on two refinement patches to agree on the intersection of those patches.

The derivation uses the repeated-index triple `(i,i,j)`, whose defect is
`u_ijβ * u_ii^p * u_ijα⁻¹`, together with the Package-B identity normalization `u_ii^p = 1`.
Consequently `κ` is *controlled by* `δ` and is not an independent descent datum, **provided**
the repeated-index instances of defect-freeness are available; see
`Counterexample.lean` for the negative control showing that the distinct-index instances
alone are insufficient. -/
theorem tripleDefectFree_imp_pairwiseRefinementCoherent {C : InternalTransitionCandidate P S}
    (h : TripleDefectFree C) : PairwiseRefinementCoherent C := by
  intro i j a b x hx
  obtain ⟨p, hp⟩ := C.covers i i (diagPt S x)
  have hmem : liftIIJ S x ∈ C.defectDom i i j p b a := ⟨⟨hp, hx.2⟩, hx.1⟩
  have hd := h.defect_eq_one i i j p b a hmem
  have hval : C.defect i i j p b a (liftIIJ S x)
      = (C.u i j b x * C.u i i p (diagPt S x)) * (C.u i j a x)⁻¹ := rfl
  rw [hval, defectFree_identity_normalisation h i p hp, mul_one, mul_inv_eq_one] at hd
  exact hd.symm

/-- **PACKAGE D, negative control (item 38).**  Defect-freeness restricted to *pairwise
distinct* index triples.  This weaker hypothesis does **not** imply
`PairwiseRefinementCoherent`; the counterexample is preserved in `Counterexample.lean`. -/
def TripleDefectFreeDistinct (C : InternalTransitionCandidate P S) : Prop :=
  ∀ (i j k : ι), i ≠ j → j ≠ k → i ≠ k → ∀ (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k),
    ∀ x ∈ C.defectDom i j k a b c, C.defect i j k a b c x = 1

/-- **PACKAGE D.**  The full inherited predicate is at least as strong as its distinct-index
restriction. -/
theorem TripleDefectFree.distinct {C : InternalTransitionCandidate P S}
    (h : TripleDefectFree C) : TripleDefectFreeDistinct C :=
  fun i j k _ _ _ a b c x hx => h i j k a b c x hx

/-! ## Package E — conditional gluing on a pair overlap -/

/-- **PACKAGE E (item 42).**  The glued map: at each point of the original overlap it is the
value of the representative stored on some patch containing that point.  Well-definedness is
proved below, under the coherence hypothesis. -/
noncomputable def gluedRep (C : InternalTransitionCandidate P S) (i j : ι)
    (x : ↥(S.U i ∩ S.U j)) : L :=
  C.u i j (Classical.choose (C.covers i j x)) x

/-- **PACKAGE E (item 44), well-definedness.**  Under pairwise coherence the glued map agrees
on each patch with the representative stored there. -/
theorem gluedRep_eq (C : InternalTransitionCandidate P S)
    (hco : PairwiseRefinementCoherent C) (i j : ι) (a : C.Idx i j)
    {x : ↥(S.U i ∩ S.U j)} (hx : x ∈ C.V i j a) : gluedRep C i j x = C.u i j a x :=
  hco i j (Classical.choose (C.covers i j x)) a x
    ⟨Classical.choose_spec (C.covers i j x), hx⟩

/-- **PACKAGE E (item 44), continuity.** -/
theorem continuous_gluedRep (C : InternalTransitionCandidate P S)
    (hco : PairwiseRefinementCoherent C) (i j : ι) : Continuous (gluedRep C i j) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨a, hxa⟩ := C.covers i j x
  have hVn : C.V i j a ∈ nhds x := (C.isOpen_V i j a).mem_nhds hxa
  have hcont : ContinuousAt (C.u i j a) x := ((C.u_isRep i j a).1).continuousAt hVn
  refine hcont.congr ?_
  filter_upwards [hVn] with y hy
  exact (gluedRep_eq C hco i j a hy).symm

/-- **PACKAGE E (item 44), projection.**  The glued map projects to the ordinary
transition. -/
theorem proj_gluedRep (C : InternalTransitionCandidate P S)
    (hco : PairwiseRefinementCoherent C) (i j : ι) (x : ↥(S.U i ∩ S.U j)) :
    P.proj (gluedRep C i j x) = S.g i j x := by
  obtain ⟨a, hxa⟩ := C.covers i j x
  rw [gluedRep_eq C hco i j a hxa]
  exact (C.u_isRep i j a).2 x hxa

/-- **PACKAGE E (items 42–45), principal endpoint — `pairwise_refined_reps_glue`.**
*Conditional* gluing: if the stored representatives of one ordinary transition agree on every
mutual overlap of their refined domains, then there is a **unique** map on the whole original
pair overlap restricting to each of them; it is continuous and projects onto the ordinary
transition.  Nothing here asserts that the hypothesis always holds (item 46). -/
theorem pairwise_refined_reps_glue (C : InternalTransitionCandidate P S)
    (hco : PairwiseRefinementCoherent C) (i j : ι) :
    ∃! v : ↥(S.U i ∩ S.U j) → L,
      ∀ (a : C.Idx i j) (x : ↥(S.U i ∩ S.U j)), x ∈ C.V i j a → v x = C.u i j a x := by
  refine ⟨gluedRep C i j, fun a x hx => gluedRep_eq C hco i j a hx, ?_⟩
  intro v hv
  funext x
  obtain ⟨a, hxa⟩ := C.covers i j x
  rw [hv a x hxa, gluedRep_eq C hco i j a hxa]

/-- **PACKAGE E (item 45), packaged.**  The glued representative is continuous, restricts to
every stored representative, projects onto the ordinary transition, and is the only map with
the restriction property. -/
theorem pairwise_refined_reps_glue_full (C : InternalTransitionCandidate P S)
    (hco : PairwiseRefinementCoherent C) (i j : ι) :
    ∃ v : ↥(S.U i ∩ S.U j) → L,
      Continuous v ∧
      (∀ (a : C.Idx i j) (x : ↥(S.U i ∩ S.U j)), x ∈ C.V i j a → v x = C.u i j a x) ∧
      (∀ x, P.proj (v x) = S.g i j x) ∧
      (∀ v' : ↥(S.U i ∩ S.U j) → L,
        (∀ (a : C.Idx i j) (x : ↥(S.U i ∩ S.U j)), x ∈ C.V i j a → v' x = C.u i j a x) →
          v' = v) := by
  refine ⟨gluedRep C i j, continuous_gluedRep C hco i j,
    fun a x hx => gluedRep_eq C hco i j a hx, proj_gluedRep C hco i j, fun v' hv' => ?_⟩
  funext x
  obtain ⟨a, hxa⟩ := C.covers i j x
  rw [hv' a x hxa, gluedRep_eq C hco i j a hxa]

end Kappa

end NullSectorTask29
