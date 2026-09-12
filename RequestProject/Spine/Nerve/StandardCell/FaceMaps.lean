import RequestProject.Spine.Nerve.StandardCell.Generator

/-!
# Task 20, face maps : the codimension-one faces of the identity simplex

Task 19 introduced the characteristic singular simplices `bdFaceSimp m i` of the codimension-one
faces of `Δ[m+1]`, living on `|∂Δ[m+1]|`, and their sum `bdFaceChain m`.  This module records
what Task 20 needs about them:

* `SpineTask20.faceHom m i : Δ[m] ⟶ ∂Δ[m+1]` — the simplicial map of the `i`-th face, so that
  `bdFaceSimp m i` is the image of the characteristic top simplex of `Δ[m]`
  (`bdFaceSimp_eq`);
* `SpineTask20.bdCoord_carrier_bdFaceSimp` — every point of the image of the `i`-th face has
  vanishing `i`-th barycentric coordinate;
* `SpineTask20.bdFaceTop m : |∂Δ[m]| ⟶ |∂Δ[m+1]|` — the realization of the `0`-th face map
  restricted to boundaries, with its coordinate description `bdCoord_bdFaceTop`;
* `SpineTask20.bdFaceChain_mem_Zc` — the face sum is a cycle;
* `SpineTask20.boundary_single_bdFaceSimp_zero` — the boundary of the `0`-th face is the image
  of the face sum one dimension down.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet NerveGeom SpineTask14
  SpineTask18 SpineTask19

universe u

namespace SpineTask20

/-! ## The simplicial face maps -/

/-- A coface map is not surjective. -/
theorem delta_not_surjective (m : ℕ) (i : Fin (m + 2)) :
    ¬ Function.Surjective (SimplexCategory.δ (n := m) i).toOrderHom := by
  intro h
  obtain ⟨j, hj⟩ := h i
  exact (Fin.succAbove_ne i j) hj

/-- The simplicial map `Δ[m] ⟶ ∂Δ[m+1]` given by the `i`-th face. -/
def faceHom (m : ℕ) (i : Fin (m + 2)) :
    (Δ[m] : SSet.{u}) ⟶ ((∂Δ[m + 1] : (Δ[m + 1] : SSet.{u}).Subcomplex) : SSet.{u}) :=
  SpineTask16.faceMap.{u} (SimplexCategory.δ i) (delta_not_surjective m i)

theorem faceHom_comp_ι (m : ℕ) (i : Fin (m + 2)) :
    faceHom.{u} m i ≫ (∂Δ[m + 1] : (Δ[m + 1] : SSet.{u}).Subcomplex).ι
      = SSet.stdSimplex.map (SimplexCategory.δ i) :=
  SpineTask16.faceMap_comp_ι _ _

theorem faceHom_app_topSimp (m : ℕ) (i : Fin (m + 2)) :
    (faceHom.{u} m i).app (op (SimplexCategory.mk m)) (topSimp.{u} m) = faceSimp.{u} m i := rfl

/-- The characteristic simplex of the `i`-th face is the image of the characteristic top
simplex of `Δ[m]` under the realization of `faceHom m i`. -/
theorem bdFaceSimp_eq (m : ℕ) (i : Fin (m + 2)) :
    bdFaceSimp.{u} m i
      = (TopCat.toSSet.map (SSet.toTop.map (faceHom.{u} m i))).app
          (op (SimplexCategory.mk m)) (charSimp.{u} m) := by
  have hnat := congrFun (congrArg (fun φ => NatTrans.app φ (op (SimplexCategory.mk m)))
    ((sSetTopAdj.unit).naturality (faceHom.{u} m i))) (topSimp.{u} m)
  show ((faceHom.{u} m i ≫ sSetTopAdj.unit.app
      (((∂Δ[m + 1] : (Δ[m + 1] : SSet.{u}).Subcomplex)) : SSet.{u})).app
        (op (SimplexCategory.mk m)) (topSimp.{u} m)) = _
  exact hnat

/-- Barycentric coordinates of a point in the image of the `i`-th face. -/
theorem bdCoord_faceHom (m : ℕ) (i : Fin (m + 2)) (t : SpineTask16.Rz.{u}.obj (Δ[m] : SSet.{u})) :
    SpineTask16.bdCoord.{u} (m + 1) (SpineTask16.Rz.map (faceHom.{u} m i) t)
      = stdSimplex.map (SimplexCategory.δ (n := m) i).toOrderHom
          (SpineTask16.coord (SimplexCategory.mk m) t) := by
  have h := SpineTask16.bdCoord_faceMap.{u} (r := m + 1) (SimplexCategory.δ (n := m) i)
    (delta_not_surjective m i) (SpineTask16.coord (SimplexCategory.mk m) t)
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- The image of the `i`-th face map consists of points with vanishing `i`-th coordinate. -/
theorem bdCoord_range_faceHom (m : ℕ) (i : Fin (m + 2))
    (t : SpineTask16.Rz.{u}.obj (Δ[m] : SSet.{u})) :
    (SpineTask16.bdCoord.{u} (m + 1) (SpineTask16.Rz.map (faceHom.{u} m i) t)
      : Fin (m + 2) → ℝ) i = 0 := by
  classical
  rw [bdCoord_faceHom, SpineTask16.map_apply]
  refine Finset.sum_eq_zero fun a ha => ?_
  exact absurd (Finset.mem_filter.1 ha).2 (Fin.succAbove_ne i a)

/-- Every point of the image of the `i`-th face has vanishing `i`-th coordinate. -/
theorem bdCoord_carrier_bdFaceSimp (m : ℕ) (i : Fin (m + 2)) {y : ↥(Bd.{u} (m + 1))}
    (hy : y ∈ carrier (bdFaceSimp.{u} m i)) :
    (SpineTask16.bdCoord.{u} (m + 1) y : Fin (m + 2) → ℝ) i = 0 := by
  rw [← carrierAt_eq_carrier, bdFaceSimp_eq, carrierAt_toSSet_map] at hy
  obtain ⟨t, -, rfl⟩ := hy
  exact bdCoord_range_faceHom m i t

/-! ## The boundary face map -/

/-- The simplicial map `∂Δ[m] ⟶ ∂Δ[m+1]` given by the `0`-th face. -/
def bdFaceHom (m : ℕ) :
    ((∂Δ[m] : (Δ[m] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶
      ((∂Δ[m + 1] : (Δ[m + 1] : SSet.{u}).Subcomplex) : SSet.{u}) :=
  (∂Δ[m] : (Δ[m] : SSet.{u}).Subcomplex).ι ≫ faceHom.{u} m 0

/-- Its realization `|∂Δ[m]| ⟶ |∂Δ[m+1]|`. -/
def bdFaceTop (m : ℕ) : Bd.{u} m ⟶ Bd.{u} (m + 1) := SSet.toTop.map (bdFaceHom.{u} m)

/-- In barycentric coordinates the `0`-th face map is `stdSimplex.map δ₀`. -/
theorem bdCoord_bdFaceTop (m : ℕ) (y : ↥(Bd.{u} m)) :
    SpineTask16.bdCoord.{u} (m + 1) (bdFaceTop.{u} m y)
      = stdSimplex.map (SimplexCategory.δ (n := m) 0).toOrderHom
          (SpineTask16.bdCoord.{u} m y) := by
  have h : (bdFaceTop.{u} m) y
      = SpineTask16.Rz.map (faceHom.{u} m 0)
          (SpineTask16.Rz.map (∂Δ[m] : (Δ[m] : SSet.{u}).Subcomplex).ι y) := by
    show SpineTask16.Rz.map (bdFaceHom.{u} m) y = _
    rw [bdFaceHom, Functor.map_comp]
    rfl
  rw [h, bdCoord_faceHom]
  rfl

/-- In barycentric coordinates the `0`-th face map inserts a vanishing `0`-th coordinate. -/
theorem bdCoord_bdFaceTop_zero (m : ℕ) (y : ↥(Bd.{u} m)) :
    (SpineTask16.bdCoord.{u} (m + 1) (bdFaceTop.{u} m y) : Fin (m + 2) → ℝ) 0 = 0 := by
  classical
  rw [bdCoord_bdFaceTop, SpineTask16.map_apply]
  refine Finset.sum_eq_zero fun a ha => ?_
  exact absurd (Finset.mem_filter.1 ha).2 (Fin.succAbove_ne 0 a)

theorem bdCoord_bdFaceTop_succ (m : ℕ) (y : ↥(Bd.{u} m)) (k : Fin (m + 1)) :
    (SpineTask16.bdCoord.{u} (m + 1) (bdFaceTop.{u} m y) : Fin (m + 2) → ℝ) k.succ
      = (SpineTask16.bdCoord.{u} m y : Fin (m + 1) → ℝ) k := by
  classical
  rw [bdCoord_bdFaceTop, SpineTask16.map_apply]
  refine Finset.sum_eq_single_of_mem k (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    (fun b _ hbk => absurd (Finset.mem_filter.1 ‹b ∈ _›).2 ?_)
  · show Fin.succAbove 0 k = k.succ
    rw [Fin.succAbove_zero]
  · show Fin.succAbove 0 b ≠ k.succ
    rw [Fin.succAbove_zero]
    exact fun h => hbk (Fin.succ_injective _ h)

/-! ## Chain-level statements -/

theorem sSetChainMap_injective {S T : SSet.{u}} (f : S ⟶ T) (k : ℕ)
    (hf : Function.Injective (f.app (op (SimplexCategory.mk k)))) :
    Function.Injective (sSetChainMap f k) := Finsupp.mapDomain_injective hf

theorem sSetChainMap_comp {S T W : SSet.{u}} (f : S ⟶ T) (g : T ⟶ W) (k : ℕ)
    (c : SSetChain S k) :
    sSetChainMap g k (sSetChainMap f k c) = sSetChainMap (f ≫ g) k c := by
  show Finsupp.mapDomain _ (Finsupp.mapDomain _ c) = Finsupp.mapDomain _ c
  rw [← Finsupp.mapDomain_comp]
  rfl

/-- The face sum is a cycle. -/
theorem bdFaceChain_mem_Zc (m : ℕ) :
    bdFaceChain.{u} m ∈ Zc (singCx (Bd.{u} (m + 1))) m := by
  match m with
  | 0 => exact mem_Zc_zero _
  | (k + 1) =>
      rw [mem_Zc_succ, show ((singCx (Bd.{u} (k + 2))).d (k + 1) k).hom
          = sSetBoundary (TopCat.toSSet.obj (Bd.{u} (k + 2))) k from
        sSetChainComplexFunctor_d (TopCat.toSSet.obj (Bd.{u} (k + 2))) k]
      refine sSetChainMap_injective (stdCellPair.{u} (k + 2)) k
        (stdCellPair_injective.{u} (k + 2) _) ?_
      have hnat := congrFun (congrArg DFunLike.coe
        (sSetBoundary_naturality (stdCellPair.{u} (k + 2)) k)) (bdFaceChain.{u} (k + 1))
      have hdd := congrFun (congrArg DFunLike.coe
        (SpineTask13.sSetBoundary_comp_sSetBoundary (TopCat.toSSet.obj (Cell.{u} (k + 2))) k))
          (charChain.{u} (k + 2))
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hnat hdd
      rw [map_zero]
      refine hnat.trans ?_
      rw [← charChain_boundary.{u} (k + 1)]
      exact hdd

/-- The singular boundary of the `0`-th face of the identity `(m+2)`-simplex is the image, under
the `0`-th face map, of the face sum of the identity `(m+1)`-simplex. -/
theorem boundary_single_bdFaceSimp_zero (m : ℕ) :
    sSetBoundary (TopCat.toSSet.obj (Bd.{u} (m + 2))) m
        (Finsupp.single (bdFaceSimp.{u} (m + 1) 0) 1)
      = sSetChainMap (TopCat.toSSet.map (bdFaceTop.{u} (m + 1))) m (bdFaceChain.{u} m) := by
  have h1 : Finsupp.single (bdFaceSimp.{u} (m + 1) 0) 1
      = sSetChainMap (TopCat.toSSet.map (SSet.toTop.map (faceHom.{u} (m + 1) 0))) (m + 1)
          (charChain.{u} (m + 1)) := by
    rw [charChain, sSetChainMap_single, bdFaceSimp_eq]
  have hnat := congrFun (congrArg DFunLike.coe
    (sSetBoundary_naturality (TopCat.toSSet.map (SSet.toTop.map (faceHom.{u} (m + 1) 0))) m))
    (charChain.{u} (m + 1))
  simp only [LinearMap.comp_apply] at hnat
  rw [h1, ← hnat, charChain_boundary.{u} m, sSetChainMap_comp]
  congr 1
  rw [show stdCellPair.{u} (m + 1) = TopCat.toSSet.map (SSet.toTop.map
      (∂Δ[m + 1] : (Δ[m + 1] : SSet.{u}).Subcomplex).ι) from rfl,
    ← TopCat.toSSet.map_comp, ← SSet.toTop.map_comp]
  rfl

end SpineTask20
