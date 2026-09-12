import Mathlib

/-!
# Spine / E2 : the generic central double-cover / transition-lift interface

This is the **reusable local-lift layer** of the experiment-2 half of the spine.  It is
completely generic: it depends on `Mathlib` only, and on no frame family, no atlas, no
topology of a base space and no experiment-specific model group.

`InternalProjection L G` is the interface of a certified central covering-style projection:

* a continuous group homomorphism `proj : L →* G`;
* surjectivity (pointwise representability);
* a continuous local section of `proj` around every point of `G`;
* centrality of `ker proj`;
* discreteness of `ker proj`.

Every later transition-lift construction of the spine (local internal representatives, the
kernel-valued ambiguity, the triple-overlap defect, descent and the global gluing) is
carried out for an *arbitrary* such interface.  No concrete instance is fixed anywhere in the
production layer; native instances — the split cover `G × ℤ/2 → G` and the circle squaring
cover — live in `RequestProject.Spine.Controls.CircleDoubleCover`.

No global section is chosen and no global section theorem is asserted here.

**Provenance.**  Upstream experiment 2, module `NullSectorTask28.TransitionLiftBase`,
Package B.  The statements are unchanged; only the module boundary is new — upstream this
interface sat behind an import of the whole Task-27 topology endpoint, so it could not be
reused without it.  The declaration namespace `NullSectorTask28` is kept so that the
dot-notation API of the interface is unchanged; `CentralDoubleCover.InternalProjection` is
an alias for discoverability.
-/

namespace NullSectorTask28

universe u v

/-! ## Package B — the frozen internal projection interface (items 25–27) -/

/-- **NEWLY DEFINED (items 25–27), principal interface.**  The data of an already certified
two-to-one style internal projection, frozen as an interface:

* a continuous homomorphism `proj : L →* G` of topological groups;
* surjectivity of `proj` (pointwise representability, Level A);
* a continuous section of `proj` on an open neighbourhood of every point of `G`
  (the inherited local-section atlas of the group projection);
* centrality of the kernel;
* discreteness of the kernel.

No global section is chosen and no global section theorem is asserted. -/
structure InternalProjection (L : Type u) (G : Type v) [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] [Group G] [TopologicalSpace G] where
  /-- The projection, as a group homomorphism. -/
  proj : L →* G
  /-- The projection is continuous. -/
  continuous_proj : Continuous proj
  /-- The projection is surjective: every ordinary element is pointwise representable. -/
  surjective_proj : Function.Surjective proj
  /-- Around every ordinary element there is an open set carrying a continuous section. -/
  hasLocalSection : ∀ k : G, ∃ V : Set G, IsOpen V ∧ k ∈ V ∧ ∃ s : G → L,
    ContinuousOn s V ∧ ∀ y ∈ V, proj (s y) = y
  /-- The kernel is central. -/
  ker_central : ∀ z ∈ proj.ker, ∀ l : L, z * l = l * z
  /-- The kernel carries the discrete topology. -/
  ker_discrete : DiscreteTopology (proj.ker : Subgroup L)

namespace InternalProjection

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] (P : InternalProjection L G)

/-- **NEUTRAL NOTATION.**  The kernel of the frozen projection.  In the certified instance it
is the inherited two-element sign kernel. -/
def Ker : Subgroup L := P.proj.ker

theorem mem_Ker_iff {z : L} : z ∈ P.Ker ↔ P.proj z = 1 := MonoidHom.mem_ker

theorem proj_ker (z : P.Ker) : P.proj (z : L) = 1 := z.2

instance : DiscreteTopology (P.Ker) := P.ker_discrete

theorem ker_comm {z : L} (hz : z ∈ P.Ker) (l : L) : z * l = l * z := P.ker_central z hz l

/-- **DERIVED (Level A, item 108).**  Pointwise representability: every ordinary element has
an internal representative.  This is the inherited surjectivity, restated. -/
theorem exists_internal_rep_pointwise (k : G) : ∃ l : L, P.proj l = k := P.surjective_proj k

/-- **DERIVED.**  Two internal elements have the same projection exactly when they differ by
a kernel element on the left. -/
theorem proj_eq_iff_mul_ker {a b : L} : P.proj a = P.proj b ↔ b * a⁻¹ ∈ P.Ker := by
  rw [Ker, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one, eq_comm]

end InternalProjection

end NullSectorTask28

/-! ## Namespace alias for the generic interface -/
namespace CentralDoubleCover

export NullSectorTask28 (InternalProjection)

end CentralDoubleCover
