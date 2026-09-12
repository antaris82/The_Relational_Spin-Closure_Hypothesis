import RequestProject.Spine.E2.AtlasChange.Task32

/-!
# Spine / E2 : the principal endpoint of the family / lift / defect core

This module is the **principal production endpoint** of the experiment-2 half of the
spine.  It adds no mathematics; it names the layer boundaries and records the axiom audit
of the principal endpoints.

Layers, in dependency order:

1. `RequestProject.Spine.E2.Family.*` — a varying family of metric, oriented, real rank-three
   fibres over an arbitrary base, its fibrewise frame carriers, the fibrewise visible
   isometry group, local trivializations and the transition data with the triple-overlap
   law.  Root module `Family.FamilyBase` imports `Mathlib` only.
2. `RequestProject.Spine.E2.Topology.*` — the topological frame family: chart topologies,
   continuity of the transitions, the right action, the reverse reconstruction.
3. `RequestProject.Spine.E2.CentralDoubleCover` — the **generic** central double-cover /
   transition-lift interface (`NullSectorTask28.InternalProjection`), depending on
   `Mathlib` alone.
4. `RequestProject.Spine.E2.Lift.*` — local internal representatives, the exact
   kernel-valued ambiguity and the triple-overlap defect, for an arbitrary interface of
   layer 3.
5. `RequestProject.Spine.E2.Lift.TransitionSystem`, `…Lift.LiftLevels` — transition
   systems, internal transition candidates and the Level A/B/C frontier, again for an
   arbitrary interface of layer 3.  No concrete projection is fixed anywhere in the
   production layer, and no module of this half reaches a historical experiment module.
6. `RequestProject.Spine.E2.Descent.*` — descent of the defect, compatible transitions and
   refinement behaviour.
7. `RequestProject.Spine.E2.Global.*` — the glued internal object, its topology and the
   conditional global interface.
8. `RequestProject.Spine.E2.Defect.*` — the intrinsic defect state and the liftability
   classification for a fixed presentation.
9. `RequestProject.Spine.E2.AtlasChange.*` — atlas change, and the **family-level**
   classification `FamilyLiftable F ↔ FamilyKernelDefectNeutral F`.

## What is deliberately *not* claimed

* The rank-three oriented family of layer 1 is **not** the tangent bundle of a Lorentzian
  manifold: it is an abstract family of fibres carrying an inner product and an
  orientation, over an arbitrary topological base.
* Consequently the kernel-valued triple-overlap defect of layers 4–8 is **not** identified
  with the second Stiefel–Whitney class, and no module of this project makes that
  identification.  Neither `w₁` nor `w₂` occurs anywhere in the spine.
* No spin structure, spinor bundle, connection or curvature is constructed.

## Presentation level versus family level

The distinction proved upstream is preserved and is now visible in the module structure:
`AtlasChange.FamilyDefectNeutrality` proves the *family-level* theory with no access to the
good/bad atlas, while the regression control showing that the *presentation-level*
statement is not family-invariant lives in `RequestProject.Spine.Controls.E2.FamilyDefectControl`,
which no production module imports.
-/

namespace NullSectorTask32

/-! ## Axiom audit of the principal production endpoints -/

#print axioms NullSectorTask28.InternalProjection
#print axioms NullSectorTask32.FamilyLiftable
#print axioms NullSectorTask32.FamilyKernelDefectNeutral
#print axioms NullSectorTask32.familyLiftable_iff_familyKernelDefectNeutral
#print axioms NullSectorTask32.task32_verdictC_classification
#print axioms NullSectorTask32.task32_ordinary_presentation_layer
#print axioms NullSectorTask32.task32_family_level_classification

end NullSectorTask32
