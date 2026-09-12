import RequestProject.Spine.Emergent.Reconstruction

/-!
# Spine / Emergent : the symmetric ("null") base-gluing sector

**Fourth module of the manifold-emergence layer (Task 32, §8).**

The maximally symmetric neutral sector of base gluings, defined at the level of the
*base-gluing primitive* only — no connection, transport or holonomy is involved, and none is
in the import closure:

* one and the same local domain `D` (an open subset of the local model) for every index;
* every pair of pieces incident along the whole of `D` (maximally symmetric overlap
  pattern);
* the identity as base-point identification map;
* no further discrete identification and no quotient inserted by hand.

The results proved here:

* `EmergentBase.symmetricGluing` — the neutral datum;
* `EmergentBase.symmetricGluing.homeomorph` — its emergent base is homeomorphic to `D`
  itself by the chart of any index, so the neutral sector inserts nothing.  That these chart
  maps all coincide, and that the resulting identification is choice-independent, is *not*
  proved here but in `RequestProject.Spine.Emergent.SymmetricCanonical` (Task 33);
* `EmergentBase.symmetric_chartRange_eq_univ` — every chart image is the whole base, i.e.
  the emergent cover of the neutral sector is the maximally symmetric one;
* Hausdorffness, second countability, connectedness and local Euclidean-ness of the emergent
  base, all *derived* (the first from the closed-graph condition, which the neutral datum is
  shown to satisfy over a Hausdorff local model);
* `EmergentBase.symmetric_emergent_manifold` — the packaged emergent-manifold statement for
  the neutral sector over the four-dimensional Clifford/Lorentz local model.
-/

noncomputable section

namespace EmergentBase

universe u t

open BaseGluingData

variable {V : Type u} [TopologicalSpace V] {ι : Type t}

/-- **NEWLY DEFINED (Task 32).**  The symmetric ("null") base-gluing datum on a fixed open
local domain `D`: identical pieces, complete incidence pattern, identity identifications. -/
def symmetricGluing (ι : Type t) {D : Set V} (hD : IsOpen D) : BaseGluingData V ι where
  D _ := D
  isOpen_D _ := hD
  W _ _ := D
  isOpen_W _ _ := hD
  W_subset _ _ := subset_rfl
  W_self _ := rfl
  φ _ _ x := x
  continuousOn_φ _ _ := continuousOn_id
  φ_mapsTo _ _ := Set.mapsTo_id D
  φ_self _ _ _ := rfl
  φ_inv _ _ _ _ := rfl
  φ_cocycle _ _ _ _ hx _ := ⟨hx, rfl⟩

namespace symmetricGluing

variable {D : Set V} (hD : IsOpen D)

@[simp] theorem D_eq (i : ι) : (symmetricGluing ι hD).D i = D := rfl

@[simp] theorem W_eq (i j : ι) : (symmetricGluing ι hD).W i j = D := rfl

theorem rel_iff {p q : Total (symmetricGluing ι hD)} :
    (symmetricGluing ι hD).Rel p q ↔ (p.2 : V) = (q.2 : V) := by
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨p.2.2, h⟩

/-- **DERIVED (Task 32).**  In the neutral sector every chart covers the whole emergent
base: the emergent cover is maximally symmetric. -/
theorem chartRange_eq_univ (i : ι) : (symmetricGluing ι hD).chartRange i = Set.univ := by
  ext p
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  obtain ⟨q, rfl⟩ := (symmetricGluing ι hD).mk_surjective p
  exact ⟨⟨(q.2 : V), q.2.2⟩, ((symmetricGluing ι hD).mk_eq_mk_iff).2 ((rel_iff hD).2 rfl)⟩

theorem chart_surjective (i : ι) :
    Function.Surjective ((symmetricGluing ι hD).chart i) :=
  Set.range_eq_univ.1 (chartRange_eq_univ hD i)

/-- **DERIVED (Task 32), principal.**  The emergent base of the neutral sector is
homeomorphic to the local domain `D` by the chart of the index `i`: nothing is added and
nothing is identified.  (Choice-independence of this identification — that all indices give
the same map, and that the inverse is the intrinsic quotient coordinate — is proved in
`RequestProject.Spine.Emergent.SymmetricCanonical`.) -/
def homeomorph (i : ι) : (D : Set V) ≃ₜ Space (symmetricGluing ι hD) :=
  (Equiv.ofBijective ((symmetricGluing ι hD).chart i)
      ⟨(symmetricGluing ι hD).injective_chart i, chart_surjective hD i⟩).toHomeomorphOfContinuousOpen
    ((symmetricGluing ι hD).continuous_chart i) ((symmetricGluing ι hD).isOpenMap_chart i)

@[simp] theorem homeomorph_apply (i : ι) (x : (D : Set V)) :
    homeomorph hD i x = (symmetricGluing ι hD).chart i x := rfl

/-- **DERIVED (Task 32).**  The neutral datum satisfies the closed-graph separation
condition over a Hausdorff local model. -/
theorem closedGluingGraph [T2Space V] : (symmetricGluing ι hD).ClosedGluingGraph := by
  have hval : Continuous fun p : Total (symmetricGluing ι hD) => (p.2 : V) :=
    continuous_sigma fun _ => continuous_subtype_val
  have hcont : Continuous fun p : Total (symmetricGluing ι hD) × Total (symmetricGluing ι hD) =>
      (((p.1.2 : V)), ((p.2.2 : V))) :=
    (hval.comp continuous_fst).prodMk (hval.comp continuous_snd)
  have hset : {p : Total (symmetricGluing ι hD) × Total (symmetricGluing ι hD) |
      (symmetricGluing ι hD).Rel p.1 p.2}
      = (fun p => (((p.1.2 : V)), ((p.2.2 : V)))) ⁻¹' Set.diagonal V := by
    ext p
    exact rel_iff hD
  rw [ClosedGluingGraph, hset]
  exact (isClosed_diagonal).preimage hcont

theorem t2Space [T2Space V] : T2Space (Space (symmetricGluing ι hD)) :=
  (symmetricGluing ι hD).t2Space_of_closedGluingGraph (closedGluingGraph hD)

theorem secondCountableTopology [Countable ι] [SecondCountableTopology V] :
    SecondCountableTopology (Space (symmetricGluing ι hD)) :=
  (symmetricGluing ι hD).secondCountableTopology_space

/-- **DERIVED (Task 32).**  The emergent base of the neutral sector is connected exactly when
the local domain is: no connectivity is created or destroyed by the gluing. -/
theorem preconnectedSpace [Nonempty ι] (h : IsPreconnected D) :
    PreconnectedSpace (Space (symmetricGluing ι hD)) := by
  haveI : PreconnectedSpace (D : Set V) := Subtype.preconnectedSpace h
  have e := homeomorph hD (Classical.arbitrary ι)
  exact ⟨by
    simpa [Set.image_univ] using
      (isPreconnected_univ (α := (D : Set V))).image e e.continuous.continuousOn⟩

/-- **DERIVED (Task 32).**  The emergent base of the neutral sector is nonempty exactly when
the local domain is. -/
theorem nonempty [Nonempty ι] (h : D.Nonempty) : Nonempty (Space (symmetricGluing ι hD)) :=
  ⟨(symmetricGluing ι hD).chart (Classical.arbitrary ι) ⟨h.choose, h.choose_spec⟩⟩

end symmetricGluing

/-! ## The neutral sector over the Clifford/Lorentz local model -/

/-- **DERIVED (Task 32), PRINCIPAL — the symmetric emergent manifold.**  Over the canonical
four-dimensional local model of the Clifford–Spin core, the neutral base-gluing sector on a
nonempty, preconnected, open local domain has an emergent base which is

1. Hausdorff, 2. second countable, 3. connected, 4. nonempty,
5. a charted space over the four-dimensional local model, and
6. homeomorphic to the local domain itself.

The base is `Space (symmetricGluing ι hD)`, constructed from the datum; it is not an external
parameter.

**Exact strength of item 6 (Task-34 documentation repair).**  What this theorem provides is
the *existence* of a homeomorphism, produced from the chart of an arbitrary index
(`Classical.arbitrary ι`); the earlier word "canonically" overstated it.  The distinguished,
choice-independent comparison — with identity, inverse and composition coherence — is
`EmergentBase.symmetricCanonicalHomeomorph`
(`RequestProject.Spine.Emergent.SymmetricCanonical`, Task 33), and it is upgraded to a
canonical diffeomorphism in `RequestProject.Spine.Emergent.SymmetricSmooth`. -/
theorem symmetric_emergent_manifold {D : Set LocalModel} (hD : IsOpen D) (hne : D.Nonempty)
    (hconn : IsPreconnected D) (ι : Type t) [Nonempty ι] [Countable ι] :
    T2Space (Space (symmetricGluing ι hD)) ∧
    SecondCountableTopology (Space (symmetricGluing ι hD)) ∧
    PreconnectedSpace (Space (symmetricGluing ι hD)) ∧
    Nonempty (Space (symmetricGluing ι hD)) ∧
    Nonempty (ChartedSpace LocalModel (Space (symmetricGluing ι hD))) ∧
    Nonempty ((D : Set LocalModel) ≃ₜ Space (symmetricGluing ι hD)) ∧
    Module.finrank ℝ LocalModel = 4 :=
  ⟨symmetricGluing.t2Space hD, symmetricGluing.secondCountableTopology hD,
    symmetricGluing.preconnectedSpace hD hconn, symmetricGluing.nonempty hD hne,
    ⟨(symmetricGluing ι hD).chartedSpace⟩,
    ⟨symmetricGluing.homeomorph hD (Classical.arbitrary ι)⟩, finrank_localModel⟩

/-- **DERIVED (Task 32), existence of a comparison homeomorphism.**  For the same primitive
input any two index types give homeomorphic emergent bases, both identified with the local
domain by the chart maps.  (Literal equality of the quotient presentations is not claimed,
and is not the correct statement: the presentations have different carriers.)

**Exact strength (Task-33 correction).**  This statement is *existence* of a homeomorphism,
obtained by choosing an index in each presentation; on its own it does not justify the word
"canonical".  The choice-independent, coherent version — a named comparison map with the
identity, inverse and composition laws — is
`EmergentBase.symmetricCanonicalHomeomorph` together with
`EmergentBase.symmetric_emergent_base_canonical` in
`RequestProject.Spine.Emergent.SymmetricCanonical`, upgraded to a diffeomorphism in
`RequestProject.Spine.Emergent.SymmetricSmooth`. -/
theorem symmetric_emergent_base_unique {D : Set V} (hD : IsOpen D) {ι ι' : Type t}
    [Nonempty ι] [Nonempty ι'] :
    Nonempty (Space (symmetricGluing ι hD) ≃ₜ Space (symmetricGluing ι' hD)) :=
  ⟨(symmetricGluing.homeomorph hD (Classical.arbitrary ι)).symm.trans
    (symmetricGluing.homeomorph hD (Classical.arbitrary ι'))⟩

end EmergentBase

end
