import RequestProject.Spine.AlgebraicTopology.SphereCover
import RequestProject.Spine.Nerve.Geometry.BoundarySphere

/-!
# Task 19, WP7 (geometry) : transporting the sphere cover to `|∂Δ[r]|`

Task 17 supplies the homeomorphism `|∂Δ[r]| ≃ₜ S^{r-1}`.  This module pulls the WP4 cover of
the sphere back along it, so that the Mayer–Vietoris comparison of WP3 can be applied directly
to the realized boundary, in the universe in which the project's chain complexes live.

* `SpineTask19.Bd r` — the realized boundary `|∂Δ[r]|` as an object of `TopCat`;
* `SpineTask19.bdU`, `SpineTask19.bdV` — the pulled-back cover of `Bd (n+2)`;
* `SpineTask19.bdInterHomotopyEquiv` — `bdU ∩ bdV ≃ₕ Bd (n+1)`.
-/

noncomputable section

open CategoryTheory Metric Simplicial SSet

universe u

namespace SpineTask19

/-! ## Elementary transport lemmas -/

/-- A homeomorphism restricts to a homeomorphism between a preimage and a set. -/
def preimageSubtypeHomeo {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (h : A ≃ₜ B) (S : Set B) : ↥(h ⁻¹' S) ≃ₜ ↥S where
  toFun x := ⟨h x, x.2⟩
  invFun y := ⟨h.symm y, by
    show h (h.symm y) ∈ S
    rw [h.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext (h.symm_apply_apply x)
  right_inv y := Subtype.ext (h.apply_symm_apply y)
  continuous_toFun := Continuous.subtype_mk (h.continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (h.symm.continuous.comp continuous_subtype_val) _

theorem pathConnectedSpace_of_homeo {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (h : A ≃ₜ B) [PathConnectedSpace B] : PathConnectedSpace A := by
  refine pathConnectedSpace_iff_univ.2 ?_
  have himg := (pathConnectedSpace_iff_univ.1 ‹PathConnectedSpace B›).image h.symm.continuous
  rwa [Set.image_univ, h.symm.surjective.range_eq] at himg

theorem totallyDisconnectedSpace_of_homeo {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (h : A ≃ₜ B) [TotallyDisconnectedSpace B] : TotallyDisconnectedSpace A := by
  refine ⟨fun s _ hs => ?_⟩
  have himg : (h '' s).Subsingleton := (hs.image h h.continuous.continuousOn).subsingleton
  intro a ha b hb
  exact h.injective (himg ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)

/-! ## The realized boundary -/

/-- The realized boundary `|∂Δ[r]|`. -/
abbrev Bd (r : ℕ) : TopCat.{u} :=
  SSet.toTop.{u}.obj (((∂Δ[r] : (Δ[r] : SSet.{u}).Subcomplex)) : SSet.{u})

/-- Task 17's homeomorphism `|∂Δ[r]| ≃ₜ S^{r-1}`. -/
def bdSphere (r : ℕ) : ↥(Bd.{u} r) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin r)) 1 :=
  SpineTask17.boundaryRealizationSphereHomeo.{u} r

/-! ## The cover -/

variable (n : ℕ)

/-- The unit vector used to cut the sphere `S^{n+1}` in two. -/
theorem hstd : ‖stdUnit (n + 1)‖ = 1 := norm_stdUnit (n + 1)

/-- The first open set of the cover of `|∂Δ[n+2]|`. -/
def bdU : Set ↥(Bd.{u} (n + 2)) := (bdSphere.{u} (n + 2)) ⁻¹' (Uset (hstd n))

/-- The second open set of the cover of `|∂Δ[n+2]|`. -/
def bdV : Set ↥(Bd.{u} (n + 2)) := (bdSphere.{u} (n + 2)) ⁻¹' (Vset (hstd n))

theorem isOpen_bdU : IsOpen (bdU.{u} n) :=
  (isOpen_Uset (hstd n)).preimage (bdSphere.{u} (n + 2)).continuous

theorem isOpen_bdV : IsOpen (bdV.{u} n) :=
  (isOpen_Vset (hstd n)).preimage (bdSphere.{u} (n + 2)).continuous

theorem bdU_union_bdV : bdU.{u} n ∪ bdV.{u} n = Set.univ := by
  rw [bdU, bdV, ← Set.preimage_union, Uset_union_Vset, Set.preimage_univ]

theorem bdU_inter_bdV :
    bdU.{u} n ∩ bdV.{u} n = (bdSphere.{u} (n + 2)) ⁻¹' (Uset (hstd n) ∩ Vset (hstd n)) := by
  rw [bdU, bdV, Set.preimage_inter]

instance contractibleSpace_bdU : ContractibleSpace ↥(bdU.{u} n) :=
  haveI := contractibleSpace_Uset (hstd n)
  (preimageSubtypeHomeo (bdSphere.{u} (n + 2)) _).contractibleSpace

instance contractibleSpace_bdV : ContractibleSpace ↥(bdV.{u} n) :=
  haveI := contractibleSpace_Vset (hstd n)
  (preimageSubtypeHomeo (bdSphere.{u} (n + 2)) _).contractibleSpace

/-- **WP7, geometry.**  The intersection of the cover of `|∂Δ[n+2]|` is homotopy equivalent to
`|∂Δ[n+1]|`. -/
def bdInterHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ↥(bdU.{u} n ∩ bdV.{u} n) ↥(Bd.{u} (n + 1)) :=
  ((Homeomorph.setCongr (bdU_inter_bdV.{u} n)).trans
      (preimageSubtypeHomeo (bdSphere.{u} (n + 2)) _)).toHomotopyEquiv.trans
    ((interSphereHomotopyEquiv (hstd n)).trans (bdSphere.{u} (n + 1)).symm.toHomotopyEquiv)

end SpineTask19
