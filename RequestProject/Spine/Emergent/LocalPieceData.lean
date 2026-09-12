import RequestProject.Spine.Emergent.NonDerivability

/-!
# Spine / Emergent : exactly which part of the gluing primitive is irreducible

**Ninth module of the manifold-emergence layer (Task 33, §8).**

Task 32 called `BaseGluingData` "the minimal missing primitive".  Its negative theorem
`EmergentBase.base_not_determined_by_local_pieces` proves less than that phrase suggests:
it exhibits two data with the *same local pieces* and *different incidence data* whose
emergent bases are not homeomorphic.  What that establishes is

> the indexed local pieces do not determine the emergent base; some cross-piece
> incidence/identification information is irreducibly additional,

and **not** that every individual field of `BaseGluingData` is separately necessary, nor
that `BaseGluingData` is the unique minimal presentation of the missing information.

This module makes the distinction formal by introducing the transparent forgetful
projection which contains exactly the data the two countermodels share:

* `EmergentBase.LocalPieceData` — the indexed open local domains, and nothing else: no
  incidence relation, no identification maps, no coherence laws;
* `EmergentBase.BaseGluingData.toLocalPieceData` — the forgetful projection;
* `EmergentBase.base_incidence_not_determined_by_local_piece_data` — the symmetric and the
  disjoint gluing data have *equal* local-piece data and non-homeomorphic emergent bases.

## Precisely what is proved and what is not

Proved: `LocalPieceData` is a strictly insufficient primitive — the reconstruction functor
does not factor through it, even up to homeomorphism of the result.

Not proved (and not claimed anywhere in this project): that each of the fields `W` and `φ`
is individually irreducible given the others; that no primitive smaller than
`BaseGluingData` carries the missing information; that `BaseGluingData` is a minimal or
universal object in any category of presentations.  The correct description of
`BaseGluingData` is therefore *an explicit sufficient base-gluing primitive whose
cross-piece incidence layer is irreducibly additional*, not "the minimal missing
primitive".
-/

noncomputable section

namespace EmergentBase

universe u t

open BaseGluingData

/-- **NEWLY DEFINED (Task 33), the forgetful layer.**  The purely local part of a base-gluing
datum: an indexed family of open local domains in the local model, with no cross-piece
information whatsoever. -/
structure LocalPieceData (V : Type u) [TopologicalSpace V] (ι : Type t) where
  /-- The local domain of the piece `i`. -/
  D : ι → Set V
  /-- Local domains are open. -/
  isOpen_D : ∀ i, IsOpen (D i)

variable {V : Type u} [TopologicalSpace V] {ι : Type t}

/-- **NEWLY DEFINED (Task 33).**  The forgetful projection: it keeps the local pieces and
discards the incidence relation, the identification maps and their coherence laws. -/
def BaseGluingData.toLocalPieceData (B : BaseGluingData V ι) : LocalPieceData V ι where
  D := B.D
  isOpen_D := B.isOpen_D

@[simp] theorem BaseGluingData.toLocalPieceData_D (B : BaseGluingData V ι) :
    B.toLocalPieceData.D = B.D := rfl

/-- **DERIVED (Task 33), PRINCIPAL — the exact irreducibility statement.**  The symmetric
and the disjoint gluing data have *literally equal* local-piece data, yet their emergent
bases are not homeomorphic.  Hence the reconstruction does not factor through
`LocalPieceData`: the cross-piece incidence/identification layer is irreducibly additional
information.

This is the precise content behind the informal phrase "a base-gluing primitive is missing".
It does **not** say that every field of `BaseGluingData` is separately necessary, nor that
`BaseGluingData` is the unique minimal such primitive. -/
theorem base_incidence_not_determined_by_local_piece_data {D : Set V} (hD : IsOpen D)
    (hne : D.Nonempty) (hconn : IsPreconnected D) :
    (symmetricGluing Bool hD).toLocalPieceData = (disjointGluing Bool hD).toLocalPieceData ∧
      ¬ Nonempty (Space (symmetricGluing Bool hD) ≃ₜ Space (disjointGluing Bool hD)) :=
  ⟨rfl, (base_not_determined_by_local_pieces hD hne hconn).2⟩

/-- **DERIVED (Task 33), the packaged negative control.**  No function from local-piece data
to topological spaces can reproduce the emergent base up to homeomorphism: any such
assignment would have to give homeomorphic answers for the two data above. -/
theorem no_reconstruction_from_local_piece_data {D : Set V} (hD : IsOpen D)
    (hne : D.Nonempty) (hconn : IsPreconnected D) :
    ¬ ∃ F : LocalPieceData V Bool → TopCat.{u},
        ∀ B : BaseGluingData V Bool,
          Nonempty (Space B ≃ₜ F B.toLocalPieceData) := by
  rintro ⟨F, hF⟩
  obtain ⟨e⟩ := hF (symmetricGluing Bool hD)
  obtain ⟨e'⟩ := hF (disjointGluing Bool hD)
  refine (base_incidence_not_determined_by_local_piece_data hD hne hconn).2 ⟨e.trans ?_⟩
  have hEq : (symmetricGluing Bool hD).toLocalPieceData
      = (disjointGluing Bool hD).toLocalPieceData := rfl
  rw [hEq]
  exact e'.symm

end EmergentBase

end

/-! ## Axiom audit of the Task-33 irreducibility endpoints -/

#print axioms EmergentBase.LocalPieceData
#print axioms EmergentBase.BaseGluingData.toLocalPieceData
#print axioms EmergentBase.base_incidence_not_determined_by_local_piece_data
#print axioms EmergentBase.no_reconstruction_from_local_piece_data
