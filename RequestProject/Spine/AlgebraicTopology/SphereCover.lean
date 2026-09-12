import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Task 19, WP4 : the two-set open cover of a sphere

For a unit vector `v` of a real inner product space `E` we take the standard cover of the unit
sphere by the two punctured spheres

* `SpineTask19.Uset hv = S \ {v}`,
* `SpineTask19.Vset hv = S \ {-v}`.

Both are open, they cover, both are **contractible** (stereographic projection identifies each
with an orthogonal complement, a vector space), and their intersection **deformation retracts
onto the unit sphere of `(ℝ ∙ v)ᗮ`** along the orthogonal decomposition
`x = ⟪v,x⟫ v + P x`.

Nothing is assumed from a picture: the retraction, its homotopy and all the memberships are
constructed.
-/

noncomputable section

open Metric RealInnerProductSpace

universe u

namespace SpineTask19

section Cover

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The orthogonal component of `x` relative to the unit vector `v`. -/
def ocomp (v : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (innerSL ℝ v).smulRight v

@[simp] theorem ocomp_apply (v x : E) : ocomp v x = x - ⟪v, x⟫ • v := rfl

theorem ocomp_eq_self_of_mem {v y : E} (hy : y ∈ (ℝ ∙ v)ᗮ) : ocomp v y = y := by
  rw [ocomp_apply, Submodule.mem_orthogonal_singleton_iff_inner_right.1 hy, zero_smul, sub_zero]

theorem norm_nrm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {w : E} (hw : w ≠ 0) :
    ‖‖w‖⁻¹ • w‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]

variable {v : E} (hv : ‖v‖ = 1)

include hv

theorem inner_self_v : ⟪v, v⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, hv, one_pow]

@[simp] theorem ocomp_v : ocomp v v = 0 := by
  rw [ocomp_apply, inner_self_v hv, one_smul, sub_self]

@[simp] theorem inner_ocomp (x : E) : ⟪v, ocomp v x⟫ = 0 := by
  rw [ocomp_apply, inner_sub_right, real_inner_smul_right, inner_self_v hv, mul_one, sub_self]

theorem ocomp_mem_orth (x : E) : ocomp v x ∈ (ℝ ∙ v)ᗮ :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.2 (inner_ocomp hv x)

/-- On the unit sphere, the orthogonal component vanishes exactly at the two poles. -/
theorem ocomp_eq_zero_iff {x : E} (hx : ‖x‖ = 1) : ocomp v x = 0 ↔ x = v ∨ x = -v := by
  constructor
  · intro h
    have hxv : x = ⟪v, x⟫ • v := sub_eq_zero.1 h
    have habs : |⟪v, x⟫| = 1 := by
      have hn := congrArg norm hxv
      rw [hx, norm_smul, hv, mul_one, Real.norm_eq_abs] at hn
      exact hn.symm
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).1 habs with h1 | h1
    · exact Or.inl (by rw [hxv, h1, one_smul])
    · exact Or.inr (by rw [hxv, h1]; module)
  · rintro (rfl | rfl)
    · exact ocomp_v hv
    · rw [map_neg, ocomp_v hv, neg_zero]

/-! ## The cover -/

/-- The "north pole" of the unit sphere determined by `v`. -/
def nPole : sphere (0 : E) 1 := ⟨v, mem_sphere_zero_iff_norm.2 hv⟩

/-- The "south pole". -/
def sPole : sphere (0 : E) 1 := ⟨-v, by rw [mem_sphere_zero_iff_norm, norm_neg, hv]⟩

/-- The sphere minus the north pole. -/
def Uset : Set (sphere (0 : E) 1) := {nPole hv}ᶜ

/-- The sphere minus the south pole. -/
def Vset : Set (sphere (0 : E) 1) := {sPole hv}ᶜ

omit [InnerProductSpace ℝ E] in
theorem isOpen_Uset : IsOpen (Uset hv) := isOpen_compl_singleton

omit [InnerProductSpace ℝ E] in
theorem isOpen_Vset : IsOpen (Vset hv) := isOpen_compl_singleton

theorem nPole_ne_sPole : nPole hv ≠ sPole hv := by
  intro h
  have hvv : v = -v := congrArg Subtype.val h
  have hz : v = 0 := by
    have h2 : (2 : ℝ) • v = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hvv]
      rw [add_neg_cancel]
    simpa using h2
  rw [hz, norm_zero] at hv
  exact zero_ne_one hv

theorem Uset_union_Vset : Uset hv ∪ Vset hv = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  by_cases h : x = nPole hv
  · exact Or.inr (fun hx => nPole_ne_sPole hv (h ▸ Set.eq_of_mem_singleton hx))
  · exact Or.inl h

/-- Stereographic projection identifies the punctured sphere with `(ℝ ∙ v)ᗮ`. -/
def UsetHomeo : ↑(Uset hv) ≃ₜ ((ℝ ∙ v)ᗮ) :=
  ((stereographic hv).toHomeomorphSourceTarget).trans
    ((Homeomorph.setCongr (stereographic_target hv)).trans (Homeomorph.Set.univ _))

/-- Stereographic projection from the south pole. -/
def VsetHomeo : ↑(Vset hv) ≃ₜ ((ℝ ∙ (-v))ᗮ) :=
  ((stereographic (v := -v) (by rw [norm_neg, hv])).toHomeomorphSourceTarget).trans
    ((Homeomorph.setCongr (stereographic_target (v := -v) (by rw [norm_neg, hv]))).trans
      (Homeomorph.Set.univ _))

/-- **WP4.**  The sphere minus a point is contractible. -/
theorem contractibleSpace_Uset : ContractibleSpace ↑(Uset hv) :=
  (UsetHomeo hv).contractibleSpace

/-- **WP4.**  The sphere minus the opposite point is contractible. -/
theorem contractibleSpace_Vset : ContractibleSpace ↑(Vset hv) :=
  (VsetHomeo hv).contractibleSpace

/-! ## The intersection deformation-retracts onto the equator -/

/-- A point of the intersection has nonzero orthogonal component. -/
theorem ocomp_ne_zero_of_mem_inter {x : sphere (0 : E) 1} (hx : x ∈ Uset hv ∩ Vset hv) :
    ocomp v (x : E) ≠ 0 := by
  intro h
  rcases (ocomp_eq_zero_iff hv (mem_sphere_zero_iff_norm.1 x.2)).1 h with h1 | h1
  · exact hx.1 (Subtype.ext h1)
  · exact hx.2 (Subtype.ext h1)

/-- The equator: the unit sphere of the orthogonal complement. -/
abbrev Equat (v : E) : Type _ := sphere (0 : ((ℝ ∙ v)ᗮ)) 1

/-- The retraction of the doubly punctured sphere onto the equator. -/
def retr : C(↑(Uset hv ∩ Vset hv), Equat v) where
  toFun x := ⟨‖ocomp v (x : E)‖⁻¹ • ⟨ocomp v (x : E), ocomp_mem_orth hv _⟩, by
    rw [mem_sphere_zero_iff_norm]
    show ‖‖ocomp v (x : E)‖⁻¹ • ocomp v (x : E)‖ = 1
    exact norm_nrm (ocomp_ne_zero_of_mem_inter hv x.2)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.smul ?_ ?_) _
    · refine Continuous.inv₀ ?_ (fun x => norm_ne_zero_iff.2 (ocomp_ne_zero_of_mem_inter hv x.2))
      exact ((ocomp v).continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val)).norm
    · exact Continuous.subtype_mk ((ocomp v).continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val)) _

/-- A point of the equator, viewed in the ambient sphere. -/
def equatPt (y : Equat v) : sphere (0 : E) 1 :=
  ⟨((y : ((ℝ ∙ v)ᗮ)) : E), by
    rw [mem_sphere_zero_iff_norm]
    exact mem_sphere_zero_iff_norm.1 y.2⟩

omit hv in
theorem ocomp_equatPt (y : Equat v) : ocomp v ((equatPt y : sphere (0:E) 1) : E)
    = ((y : ((ℝ ∙ v)ᗮ)) : E) :=
  ocomp_eq_self_of_mem (y : ((ℝ ∙ v)ᗮ)).2

omit hv in
theorem ocomp_equatPt_ne_zero (y : Equat v) :
    ocomp v ((equatPt y : sphere (0:E) 1) : E) ≠ 0 := by
  rw [ocomp_equatPt]
  intro h0
  have hn : ‖((y : ((ℝ ∙ v)ᗮ)) : E)‖ = 1 := mem_sphere_zero_iff_norm.1 y.2
  rw [h0, norm_zero] at hn
  exact zero_ne_one hn

theorem equatPt_mem (y : Equat v) : equatPt y ∈ Uset hv ∩ Vset hv := by
  refine ⟨fun hc => ocomp_equatPt_ne_zero y ?_, fun hc => ocomp_equatPt_ne_zero y ?_⟩
  · rw [show ((equatPt y : sphere (0:E) 1) : E) = v from
      congrArg Subtype.val (Set.eq_of_mem_singleton hc)]
    exact ocomp_v hv
  · rw [show ((equatPt y : sphere (0:E) 1) : E) = -v from
      congrArg Subtype.val (Set.eq_of_mem_singleton hc), map_neg, ocomp_v hv, neg_zero]

/-- The equator sits inside the doubly punctured sphere. -/
def equatInc : C(Equat v, ↑(Uset hv ∩ Vset hv)) where
  toFun y := ⟨equatPt y, equatPt_mem hv y⟩
  continuous_toFun :=
    Continuous.subtype_mk (Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val) _) _

theorem retr_equatInc (y : Equat v) : retr hv (equatInc hv y) = y := by
  refine Subtype.ext (Subtype.ext ?_)
  show ‖ocomp v ((equatPt y : sphere (0:E) 1) : E)‖⁻¹
      • ocomp v ((equatPt y : sphere (0:E) 1) : E) = ((y : ((ℝ ∙ v)ᗮ)) : E)
  have hn : ‖((y : ((ℝ ∙ v)ᗮ)) : E)‖ = 1 := mem_sphere_zero_iff_norm.1 y.2
  rw [ocomp_equatPt, hn, inv_one, one_smul]


theorem mem_inter_of_ocomp_ne_zero {x : sphere (0 : E) 1} (h : ocomp v (x : E) ≠ 0) :
    x ∈ Uset hv ∩ Vset hv := by
  refine ⟨fun hc => h ?_, fun hc => h ?_⟩
  · rw [show ((x : sphere (0:E) 1) : E) = v from
      congrArg Subtype.val (Set.eq_of_mem_singleton hc)]
    exact ocomp_v hv
  · rw [show ((x : sphere (0:E) 1) : E) = -v from
      congrArg Subtype.val (Set.eq_of_mem_singleton hc), map_neg, ocomp_v hv, neg_zero]

/-- The straight-line path, in the ambient space, from a point of the doubly punctured sphere
towards its orthogonal component. -/
def wvec (t : ℝ) (x : ↑(Uset hv ∩ Vset hv)) : E :=
  ((x : sphere (0:E) 1) : E) - (t * ⟪v, ((x : sphere (0:E) 1) : E)⟫) • v

theorem ocomp_wvec (t : ℝ) (x : ↑(Uset hv ∩ Vset hv)) :
    ocomp v (wvec hv t x) = ocomp v ((x : sphere (0:E) 1) : E) := by
  rw [wvec, map_sub, map_smul, ocomp_v hv, smul_zero, sub_zero]

theorem wvec_ne_zero (t : ℝ) (x : ↑(Uset hv ∩ Vset hv)) : wvec hv t x ≠ 0 := by
  intro h
  refine ocomp_ne_zero_of_mem_inter hv x.2 ?_
  rw [← ocomp_wvec hv t x, h, map_zero]

theorem wvec_zero (x : ↑(Uset hv ∩ Vset hv)) : wvec hv 0 x = ((x : sphere (0:E) 1) : E) := by
  rw [wvec, zero_mul, zero_smul, sub_zero]

theorem wvec_one (x : ↑(Uset hv ∩ Vset hv)) :
    wvec hv 1 x = ocomp v ((x : sphere (0:E) 1) : E) := by
  rw [wvec, one_mul, ocomp_apply]

theorem continuous_wvec :
    Continuous (fun p : ↑unitInterval × ↑(Uset hv ∩ Vset hv) => wvec hv (p.1 : ℝ) p.2) := by
  have hx : Continuous (fun p : ↑unitInterval × ↑(Uset hv ∩ Vset hv) =>
      ((p.2 : sphere (0:E) 1) : E)) :=
    (continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd
  exact hx.sub ((((continuous_subtype_val.comp continuous_fst)).mul
    ((innerSL ℝ v).continuous.comp hx)).smul continuous_const)

/-- The deformation retraction of the doubly punctured sphere onto the equator. -/
def interHomotopy : ContinuousMap.Homotopy
    (ContinuousMap.id ↑(Uset hv ∩ Vset hv)) ((equatInc hv).comp (retr hv)) where
  toFun p := ⟨⟨‖wvec hv (p.1 : ℝ) p.2‖⁻¹ • wvec hv (p.1 : ℝ) p.2,
      by rw [mem_sphere_zero_iff_norm]; exact norm_nrm (wvec_ne_zero hv _ _)⟩, by
    refine mem_inter_of_ocomp_ne_zero hv ?_
    show ocomp v (‖wvec hv (p.1 : ℝ) p.2‖⁻¹ • wvec hv (p.1 : ℝ) p.2) ≠ 0
    rw [map_smul, ocomp_wvec]
    refine smul_ne_zero ?_ (ocomp_ne_zero_of_mem_inter hv p.2.2)
    exact inv_ne_zero (norm_ne_zero_iff.2 (wvec_ne_zero hv _ _))⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.smul ?_ ?_) _) _
    · exact Continuous.inv₀ (continuous_wvec hv).norm
        (fun p => norm_ne_zero_iff.2 (wvec_ne_zero hv _ _))
    · exact continuous_wvec hv
  map_zero_left x := by
    refine Subtype.ext (Subtype.ext ?_)
    show ‖wvec hv ((0 : unitInterval) : ℝ) x‖⁻¹ • wvec hv ((0 : unitInterval) : ℝ) x
      = ((x : sphere (0:E) 1) : E)
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, wvec_zero,
      mem_sphere_zero_iff_norm.1 (x : sphere (0:E) 1).2, inv_one, one_smul]
  map_one_left x := by
    refine Subtype.ext (Subtype.ext ?_)
    show ‖wvec hv ((1 : unitInterval) : ℝ) x‖⁻¹ • wvec hv ((1 : unitInterval) : ℝ) x
      = ‖ocomp v ((x : sphere (0:E) 1) : E)‖⁻¹ • ocomp v ((x : sphere (0:E) 1) : E)
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, wvec_one]

/-- **WP4.**  The intersection of the two punctured spheres is homotopy equivalent to the
equator, the unit sphere of `(ℝ ∙ v)ᗮ`. -/
def interEquatHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ↑(Uset hv ∩ Vset hv) (Equat v) where
  toFun := retr hv
  invFun := equatInc hv
  left_inv := ⟨(interHomotopy hv).symm⟩
  right_inv := by
    have h : (retr hv).comp (equatInc hv) = ContinuousMap.id (Equat v) :=
      ContinuousMap.ext (retr_equatInc hv)
    rw [h]

end Cover



/-! ## The Euclidean model -/

/-- A linear isometry equivalence induces a homeomorphism of unit spheres. -/
def sphereCongr {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (e : F ≃ₗᵢ[ℝ] G) :
    sphere (0 : F) 1 ≃ₜ sphere (0 : G) 1 where
  toFun x := ⟨e x, by
    rw [mem_sphere_zero_iff_norm, e.norm_map]
    exact mem_sphere_zero_iff_norm.1 x.2⟩
  invFun y := ⟨e.symm y, by
    rw [mem_sphere_zero_iff_norm, e.symm.norm_map]
    exact mem_sphere_zero_iff_norm.1 y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  continuous_toFun := Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) _

section EuclideanModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] {v : E} (hv : ‖v‖ = 1)

include hv

omit [InnerProductSpace ℝ E] in
theorem unit_ne_zero : v ≠ 0 := by
  intro h
  rw [h, norm_zero] at hv
  exact zero_ne_one hv

/-- The equator is homeomorphic to the standard sphere `S^{n-1}` in `ℝⁿ`. -/
def equatEuclideanHomeo : Equat v ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  sphereCongr (OrthonormalBasis.fromOrthogonalSpanSingleton n (unit_ne_zero hv)).repr

/-- **WP4, the packaged statement.**  The intersection of the two punctured spheres is
homotopy equivalent to the standard sphere one dimension down. -/
def interSphereHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ↑(Uset hv ∩ Vset hv) (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  (interEquatHomotopyEquiv hv).trans (equatEuclideanHomeo hv).toHomotopyEquiv

end EuclideanModel

/-! ## The standard Euclidean sphere -/

/-- The first standard basis vector of `ℝ^{n+1}`. -/
def stdUnit (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1

theorem norm_stdUnit (n : ℕ) : ‖stdUnit n‖ = 1 := by
  rw [stdUnit, EuclideanSpace.norm_single, norm_one]

instance factFinrankEuclidean (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨by simp⟩


end SpineTask19
