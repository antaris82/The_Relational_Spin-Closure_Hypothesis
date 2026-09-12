import RequestProject.Spine.E2.Cech.SpinInstance

/-!
# Spine / E2 / Cech : the Task-3 endpoint — the ℤ₂ Spin-lift obstruction

This module is the production endpoint of the Task-3 layer.  It adds no mathematics; it names
the layer boundaries and records the interpretation boundary.

Layers, in dependency order:

1. `RequestProject.Spine.E2.Cech.Cover` — abstract open covers of an abstract topological
   base, visible `G`-valued transition data with the exact Čech 1-cocycle law (the unit and
   inverse laws are *derived*), refinement maps and the pullback of transition data.
2. `RequestProject.Spine.E2.Cech.LocalLifts` — the sufficient condition for a continuous lift
   on a whole overlap, unconditional local liftability, families of local lifts and the
   lift-admissibility hypothesis.  Global liftability on full overlaps is never assumed.
3. `RequestProject.Spine.E2.Cech.Defect` — the triple-overlap defect, its kernel-valuedness,
   continuity, local constancy and the exact Čech 2-cocycle law.
4. `RequestProject.Spine.E2.Cech.Coboundary` — kernel-valued Čech cochains, the coboundary
   `δ`, and the change-of-local-representative law `c' = (δε) c`.
5. `RequestProject.Spine.E2.Cech.Obstruction` — the lightweight native quotient by
   1-coboundaries, the fixed-cover class, its independence of the chosen lifts, and the
   vanishing criterion `[c] = 1 ↔ coherent Spin-valued transition data exists`.
6. `RequestProject.Spine.E2.Cech.Refinement` — pullback of lifts, defects and classes,
   refinement naturality `[c_𝓥] = r*[c_𝓤]`, functoriality of the restriction map, and
   independence of the restricted class from the chosen refinement index map.
7. `RequestProject.Spine.E2.Cech.SpinInstance` — instantiation with the native intrinsic
   `SpinCore.internalSpinProjection`, giving `c_ijk ∈ {±1}`.

## Interpretation boundary (mandatory)

* **Topological layer.**  `[c] ≠ 1` means exactly that a globally coherent Spin-valued lift
  of the *given* visible transition data on the *given* cover is obstructed.
* **Future dynamical layer.**  Even when `[c] = 1`, a connection built later may have
  nonzero curvature or torsion, and any later relational/synchronization structure may be
  nontrivial.  `[c] = 1` must therefore **not** be read as flat spacetime, zero curvature,
  zero gravitational field, synchronization equilibrium or absolute rest.
* The defect is **not** curvature, torsion, holonomy, a synchronization imbalance, a field
  strength, a matter/antimatter sign or a preferred frame.  Kernel signs are group elements
  of `{±1} = ker ρ` and carry no physical reading here.

## Not claimed

* The class is **not** identified with `w₂(TM)`.  There is no manifold, no tangent bundle, no
  metric, no orientation, no frame bundle and no frame transition cocycle in this layer, so
  the comparison cannot even be stated.  At most: the object constructed here is an abstract
  `ℤ₂`-valued Spin-lift obstruction of the correct formal type for such a later comparison.
* No spin structure, spinor bundle, connection, curvature or torsion is constructed.
* No cover-independent direct-limit Čech cohomology group is constructed; Task 3 stops at
  exact refinement naturality (see `TASK03_AUDIT.md`).
-/

namespace CechSpinLift

/-! ## Axiom audit of the principal Task-3 endpoints -/

#print axioms CechSpinLift.CechCover
#print axioms CechSpinLift.VisibleCocycle
#print axioms CechSpinLift.VisibleCocycle.visible_transition_laws
#print axioms CechSpinLift.SpinLiftFamily
#print axioms CechSpinLift.exists_lift_nhdsWithin
#print axioms CechSpinLift.SpinLiftFamily.defect_mem_ker
#print axioms CechSpinLift.SpinLiftFamily.defect_isLocallyConstant
#print axioms CechSpinLift.SpinLiftFamily.defect_delta_eq_one
#print axioms CechSpinLift.SpinLiftFamily.defect_change_of_lift
#print axioms CechSpinLift.ObstructionClass
#print axioms CechSpinLift.SpinLiftFamily.obstruction_lift_independent
#print axioms CechSpinLift.SpinLiftFamily.obstruction_eq_trivialClass_iff_exists_coherent
#print axioms CechSpinLift.SpinLiftFamily.obstruction_pullLift
#print axioms CechSpinLift.SpinLiftFamily.obstruction_pullLift_indep_of_map

end CechSpinLift
