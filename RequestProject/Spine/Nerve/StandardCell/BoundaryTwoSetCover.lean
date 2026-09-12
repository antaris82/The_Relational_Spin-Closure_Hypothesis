import RequestProject.Spine.Nerve.Geometry.BarycentricRetraction
import RequestProject.Spine.Nerve.StandardCell.FaceMaps

/-!
# Task 20, the cover : two open sets of `|∂Δ[n+2]|` and the retraction of their intersection

`|∂Δ[n+2]|` is covered by the complements of two of its points:

* `SpineTask20.Uset n` — the complement of the barycentre of the `0`-th face; it contains all
  the codimension-one faces except the `0`-th one;
* `SpineTask20.Vset n` — the complement of the `0`-th vertex; it contains the `0`-th face.

Their intersection *retracts* onto the boundary of the `0`-th face, i.e. onto the image of
`|∂Δ[n+1]|`.  That retraction — and not a homotopy equivalence — is what the Task-20 argument
uses: it makes the map `H_n(|∂Δ[n+1]|) → H_n(U ∩ V)` injective.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet NerveGeom SpineTask14
  SpineTask18 SpineTask19

universe u

namespace SpineTask20

variable (n : ℕ)

/-- The complement of the barycentre of the `0`-th face. -/
def Uset : Set ↥(Bd.{u} (n + 2)) := {y | SpineTask16.bdCoord.{u} (n + 2) y ≠ barPt n}

/-- The complement of the `0`-th vertex. -/
def Vset : Set ↥(Bd.{u} (n + 2)) := {y | SpineTask16.bdCoord.{u} (n + 2) y ≠ vtx0 n}

theorem isOpen_Uset : IsOpen (Uset.{u} n) :=
  (isOpen_compl_singleton (x := barPt n)).preimage
    (SpineTask17.continuous_subCoord (∂Δ[n + 2] : (Δ[n + 2] : SSet.{u}).Subcomplex))

theorem isOpen_Vset : IsOpen (Vset.{u} n) :=
  (isOpen_compl_singleton (x := vtx0 n)).preimage
    (SpineTask17.continuous_subCoord (∂Δ[n + 2] : (Δ[n + 2] : SSet.{u}).Subcomplex))

theorem Uset_union_Vset : Uset.{u} n ∪ Vset.{u} n = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  by_cases h : SpineTask16.bdCoord.{u} (n + 2) y = barPt n
  · refine Or.inr fun hv => ?_
    exact barPt_ne_vtx0 n (h ▸ hv)
  · exact Or.inl h

/-- The codimension-one faces other than the `0`-th one avoid the barycentre of the `0`-th
face. -/
theorem carrier_bdFaceSimp_subset_Uset (i : Fin (n + 3)) (hi : i ≠ 0) :
    carrier (bdFaceSimp.{u} (n + 1) i) ⊆ Uset.{u} n := by
  intro y hy
  have h0 := bdCoord_carrier_bdFaceSimp (n + 1) i hy
  obtain ⟨k, rfl⟩ : ∃ k : Fin (n + 2), i = k.succ :=
    (Fin.eq_zero_or_eq_succ i).resolve_left hi
  intro hc
  rw [hc, barPt_apply_succ] at h0
  have hpos : (0:ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  exact hpos.ne' h0

/-- The `0`-th face avoids the `0`-th vertex. -/
theorem carrier_bdFaceSimp_subset_Vset :
    carrier (bdFaceSimp.{u} (n + 1) 0) ⊆ Vset.{u} n := by
  intro y hy
  have h0 := bdCoord_carrier_bdFaceSimp (n + 1) 0 hy
  intro hc
  rw [hc, vtx0_apply_zero] at h0
  exact one_ne_zero h0

/-- Every point of `|∂Δ[m]|` has a vanishing barycentric coordinate. -/
theorem exists_bdCoord_eq_zero (m : ℕ) (y : ↥(Bd.{u} m)) :
    ∃ i, (SpineTask16.bdCoord.{u} m y : Fin (m + 1) → ℝ) i = 0 := by
  have h : SpineTask16.bdCoord.{u} m y ∈ Set.range (SpineTask16.bdCoord.{u} m) := ⟨y, rfl⟩
  rw [SpineTask16.range_bdCoord] at h
  exact h

/-- The boundary of the `0`-th face lies in the intersection of the cover. -/
theorem bdFaceTop_mem_inter (y : ↥(Bd.{u} (n + 1))) :
    (bdFaceTop.{u} (n + 1) y : ↥(Bd.{u} (n + 2))) ∈ Uset.{u} n ∩ Vset.{u} n := by
  obtain ⟨k, hk⟩ := exists_bdCoord_eq_zero.{u} (n + 1) y
  constructor
  · intro hc
    have h := bdCoord_bdFaceTop_succ.{u} (n + 1) y k
    rw [hc, barPt_apply_succ, hk] at h
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    exact hpos.ne' h
  · intro hc
    have h := bdCoord_bdFaceTop_zero.{u} (n + 1) y
    rw [hc, vtx0_apply_zero] at h
    exact one_ne_zero h

/-- The `0`-th face map, corestricted to the intersection of the cover. -/
def gIn : Bd.{u} (n + 1) ⟶ subTop (Uset.{u} n ∩ Vset.{u} n) :=
  TopCat.ofHom ⟨fun y => ⟨bdFaceTop.{u} (n + 1) y, bdFaceTop_mem_inter n y⟩,
    Continuous.subtype_mk (bdFaceTop.{u} (n + 1)).hom.continuous _⟩

theorem gIn_comp_subInc :
    gIn.{u} n ≫ subInc (Uset.{u} n ∩ Vset.{u} n) = bdFaceTop.{u} (n + 1) := rfl

/-- The barycentric coordinates of a point of the intersection of the cover, as a point of the
punctured boundary locus. -/
def toWc (y : ↥(Uset.{u} n ∩ Vset.{u} n)) : ↥(Wc n) :=
  ⟨SpineTask16.bdCoord.{u} (n + 2) y.1, exists_bdCoord_eq_zero.{u} (n + 2) y.1, y.2.1, y.2.2⟩

theorem continuous_toWc : Continuous (toWc.{u} n) :=
  Continuous.subtype_mk
    ((SpineTask17.continuous_subCoord (∂Δ[n + 2] : (Δ[n + 2] : SSet.{u}).Subcomplex)).comp
      continuous_subtype_val) _

/-- The retraction of the intersection of the cover onto the boundary of the `0`-th face. -/
def retr : subTop (Uset.{u} n ∩ Vset.{u} n) ⟶ Bd.{u} (n + 1) :=
  TopCat.ofHom ⟨fun y => (SpineTask17.boundaryHomeo.{u} (n + 1)).symm
      ⟨coordRetr (toWc.{u} n y), coordRetr_mem_bdLocus _⟩,
    (SpineTask17.boundaryHomeo.{u} (n + 1)).symm.continuous.comp
      (Continuous.subtype_mk (continuous_coordRetr.comp (continuous_toWc.{u} n)) _)⟩

/-- **The retraction property.**  The `0`-th face map is a section of `retr`; in particular the
map it induces on homology is a split monomorphism. -/
theorem gIn_comp_retr : gIn.{u} n ≫ retr.{u} n = 𝟙 (Bd.{u} (n + 1)) := by
  refine TopCat.hom_ext (ContinuousMap.ext fun y => ?_)
  show (SpineTask17.boundaryHomeo.{u} (n + 1)).symm
      ⟨coordRetr (toWc.{u} n ⟨bdFaceTop.{u} (n + 1) y, bdFaceTop_mem_inter n y⟩), _⟩ = y
  have hv : coordRetr (toWc.{u} n ⟨bdFaceTop.{u} (n + 1) y, bdFaceTop_mem_inter n y⟩)
      = SpineTask16.bdCoord.{u} (n + 1) y := by
    refine coordRetr_of_face _ _ ?_ ?_ (exists_bdCoord_eq_zero.{u} (n + 1) y)
    · exact bdCoord_bdFaceTop_zero.{u} (n + 1) y
    · exact fun k => bdCoord_bdFaceTop_succ.{u} (n + 1) y k
  rw [Homeomorph.symm_apply_eq]
  exact Subtype.ext (by rw [SpineTask17.coe_boundaryHomeo]; exact hv)

end SpineTask20
