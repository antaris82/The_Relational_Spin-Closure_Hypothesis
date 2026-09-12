import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Task 19, WP1 : an element-level description of the homology of the project's chain complexes

Tasks 14–18 work with the categorical `HomologicalComplex.homology`.  The low-degree
computations required by Task 19 (`H₀` of a point, of a contractible space, of a two-point
space, and the explicit kernel of a collapse map) are *element* statements, so this module
supplies the missing dictionary, once and for all, for `ℕ`-indexed chain complexes of
`ZMod 2`-modules:

* `SpineTask19.Zc K q` — the submodule of `q`-cycles;
* `SpineTask19.hIso K q` — the isomorphism `H_q(K) ≅ Z_q/B_q`, obtained from Mathlib's
  `ShortComplex.moduleCatHomologyIso`;
* `SpineTask19.hcls` — the class of a cycle, with `hcls_surjective`, `hcls_eq_zero_iff`,
  `hcls_add`, `hcls_smul` and `homologyMap_hcls` (naturality).

No new homology theory is introduced: `hIso` is an isomorphism onto the *existing*
`HomologicalComplex.homology`.
-/

noncomputable section

open CategoryTheory Limits

universe u

namespace SpineTask19

/-- `ℕ`-indexed chain complexes of `ZMod 2`-modules: the ambient category of the whole
project. -/
abbrev Cx : Type _ := ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ

theorem next_eq (q : ℕ) : (ComplexShape.down ℕ).next q = q - 1 := by
  cases q with
  | zero => exact ChainComplex.next_nat_zero
  | succ m => exact ChainComplex.next_nat_succ m

variable (K L : Cx.{u}) (q : ℕ)

/-- The short complex `C_{q+1} → C_q → C_{q-1}` computing `H_q`. -/
abbrev scN : ShortComplex (ModuleCat.{u} (ZMod 2)) := K.sc' (q + 1) q (q - 1)

/-- `H_q(K)` is computed by `scN K q`. -/
def hIsoSc : K.homology q ≅ (scN K q).homology :=
  K.homologyIsoSc' (q + 1) q (q - 1) (ChainComplex.prev ℕ q) (next_eq q)

/-- The `q`-cycles of `K`. -/
def Zc : Submodule (ZMod 2) (K.X q) := LinearMap.ker (K.d q (q - 1)).hom

variable {K L q}

theorem mem_Zc_succ {z : K.X (q + 1)} :
    z ∈ Zc K (q + 1) ↔ (K.d (q + 1) q).hom z = 0 := Iff.rfl

theorem mem_Zc_zero (z : K.X 0) : z ∈ Zc K 0 := by
  show (K.d 0 0).hom z = 0
  rw [K.shape 0 0 (by simp)]
  rfl

theorem d_mem_Zc (w : K.X (q + 1)) : (K.d (q + 1) q).hom w ∈ Zc K q := by
  cases q with
  | zero => exact mem_Zc_zero _
  | succ m =>
    rw [mem_Zc_succ]
    exact congrFun (congrArg DFunLike.coe (congrArg ModuleCat.Hom.hom
      (K.d_comp_d (m + 2) (m + 1) m))) w

variable (K q)

/-- The explicit `Z/B` model of homology. -/
abbrev HQuot : Type u := Zc K q ⧸ LinearMap.range ((scN K q).moduleCatToCycles)

/-- The comparison of the categorical homology with the explicit `Z/B` model. -/
def hIso : K.homology q ≅ ModuleCat.of (ZMod 2) (HQuot K q) :=
  hIsoSc K q ≪≫ (scN K q).moduleCatHomologyIso

variable {K q}

theorem hIso_inv_injective : Function.Injective ((hIso K q).inv.hom) :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

/-- The homology class of a cycle. -/
def hcls (z : K.X q) (hz : z ∈ Zc K q) : K.homology q :=
  (hIso K q).inv.hom (Submodule.Quotient.mk ⟨z, hz⟩)

theorem hIso_hom_hcls (z : K.X q) (hz : z ∈ Zc K q) :
    (hIso K q).hom.hom (hcls z hz) = Submodule.Quotient.mk ⟨z, hz⟩ := by
  rw [hcls]
  exact congrFun (congrArg DFunLike.coe (congrArg ModuleCat.Hom.hom (hIso K q).inv_hom_id)) _

theorem hcls_add (z w : K.X q) (hz : z ∈ Zc K q) (hw : w ∈ Zc K q) :
    hcls (z + w) (Submodule.add_mem _ hz hw) = hcls z hz + hcls w hw := by
  rw [hcls, hcls, hcls, ← map_add]
  rfl

theorem hcls_smul (a : ZMod 2) (z : K.X q) (hz : z ∈ Zc K q) :
    hcls (a • z) (Submodule.smul_mem _ a hz) = a • hcls z hz := by
  rw [hcls, hcls, ← map_smul]
  rfl

theorem hcls_zero (hz : (0 : K.X q) ∈ Zc K q) : hcls (0 : K.X q) hz = 0 := by
  have h : (⟨(0 : K.X q), hz⟩ : Zc K q) = 0 := rfl
  rw [hcls, h, Submodule.Quotient.mk_zero, map_zero]

theorem hcls_congr {z w : K.X q} (hz : z ∈ Zc K q) (hw : w ∈ Zc K q) (h : z = w) :
    hcls z hz = hcls w hw := by subst h; rfl

theorem hcls_surjective (x : K.homology q) : ∃ (z : K.X q) (hz : z ∈ Zc K q), hcls z hz = x := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ ((hIso K q).hom.hom x)
  refine ⟨y.1, y.2, ?_⟩
  rw [hcls, show (⟨y.1, y.2⟩ : Zc K q) = y from rfl, hy]
  exact congrFun (congrArg DFunLike.coe (congrArg ModuleCat.Hom.hom (hIso K q).hom_inv_id)) x

theorem hcls_eq_zero_iff (z : K.X q) (hz : z ∈ Zc K q) :
    hcls z hz = 0 ↔ ∃ w : K.X (q + 1), (K.d (q + 1) q).hom w = z := by
  constructor
  · intro h
    have h0 : (Submodule.Quotient.mk (p := LinearMap.range ((scN K q).moduleCatToCycles))
        ⟨z, hz⟩) = 0 := by
      refine hIso_inv_injective ?_
      rw [← hcls, h, map_zero]
    rw [Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨w, hw⟩ := h0
    exact ⟨w, congrArg Subtype.val hw⟩
  · rintro ⟨w, rfl⟩
    rw [hcls, show (Submodule.Quotient.mk (p := LinearMap.range ((scN K q).moduleCatToCycles))
      ⟨(K.d (q + 1) q).hom w, hz⟩) = 0 from ?_, map_zero]
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨w, Subtype.ext rfl⟩

/-! ## Naturality -/

section Naturality

theorem map_mem_Zc (q : ℕ) (φ : K ⟶ L) {z : K.X q} (hz : z ∈ Zc K q) :
    (φ.f q).hom z ∈ Zc L q := by
  have hc := congrFun (congrArg DFunLike.coe (congrArg ModuleCat.Hom.hom (φ.comm q (q - 1)))) z
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
  show (L.d q (q - 1)).hom ((φ.f q).hom z) = 0
  rw [hc, show (K.d q (q - 1)).hom z = 0 from hz, map_zero]

theorem comm_apply (q : ℕ) (φ : K ⟶ L) (x : K.X (q + 1)) :
    (φ.f q).hom ((K.d (q + 1) q).hom x) = (L.d (q + 1) q).hom ((φ.f (q + 1)).hom x) := by
  have hc := congrFun (congrArg DFunLike.coe (congrArg ModuleCat.Hom.hom (φ.comm (q + 1) q))) x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
  exact hc.symm

/-- The morphism of short complexes induced by `φ`. -/
abbrev scNMap (q : ℕ) (φ : K ⟶ L) : scN K q ⟶ scN L q :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} (ZMod 2)) (ComplexShape.down ℕ)
    (q + 1) q (q - 1)).map φ

/-- The left-homology map data realising `scNMap` on the explicit `Z/B` models. -/
def lhmd (q : ℕ) (φ : K ⟶ L) : ShortComplex.LeftHomologyMapData (scNMap q φ)
    (scN K q).moduleCatLeftHomologyData (scN L q).moduleCatLeftHomologyData where
  φK := ModuleCat.ofHom (LinearMap.restrict (φ.f q).hom (fun _ hx => map_mem_Zc q φ hx))
  φH := ModuleCat.ofHom (Submodule.mapQ _ _
    (LinearMap.restrict (φ.f q).hom (fun _ hx => map_mem_Zc q φ hx)) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨(φ.f (q + 1)).hom x, Subtype.ext ?_⟩
      exact (comm_apply q φ x).symm))
  commi := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  commf' := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact comm_apply q φ x
  commπ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem homologyMap_comm_hIso (q : ℕ) (φ : K ⟶ L) :
    HomologicalComplex.homologyMap φ q ≫ (hIso L q).hom
      = (hIso K q).hom ≫ (lhmd q φ).φH := by
  have h1 : HomologicalComplex.homologyMap φ q ≫ (hIsoSc L q).hom
      = (hIsoSc K q).hom ≫ ShortComplex.homologyMap (scNMap q φ) := by
    rw [hIsoSc, hIsoSc, HomologicalComplex.homologyIsoSc', HomologicalComplex.homologyIsoSc',
      show HomologicalComplex.homologyMap φ q
        = ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor
            (ModuleCat.{u} (ZMod 2)) (ComplexShape.down ℕ) q).map φ) from rfl]
    rw [ShortComplex.homologyMapIso, ShortComplex.homologyMapIso,
      ← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
    congr 1
    exact ((HomologicalComplex.natIsoSc' (ModuleCat.{u} (ZMod 2)) (ComplexShape.down ℕ)
      (q + 1) q (q - 1) (ChainComplex.prev ℕ q) (next_eq q)).hom.naturality φ)
  have h2 := (lhmd q φ).homologyMap_comm
  rw [hIso, hIso, Iso.trans_hom, Iso.trans_hom, ← Category.assoc, h1, Category.assoc,
    show (scN L q).moduleCatHomologyIso.hom
      = (scN L q).moduleCatLeftHomologyData.homologyIso.hom from rfl, h2,
    show (scN K q).moduleCatLeftHomologyData.homologyIso.hom
      = (scN K q).moduleCatHomologyIso.hom from rfl, Category.assoc]

/-- **Naturality of the class of a cycle.** -/
theorem homologyMap_hcls (q : ℕ) (φ : K ⟶ L) {z : K.X q} (hz : z ∈ Zc K q) :
    (HomologicalComplex.homologyMap φ q).hom (hcls z hz)
      = hcls ((φ.f q).hom z) (map_mem_Zc q φ hz) := by
  have hinj : Function.Injective ((hIso L q).hom.hom) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  refine hinj ?_
  have h := congrFun (congrArg DFunLike.coe (congrArg ModuleCat.Hom.hom
    (homologyMap_comm_hIso q φ))) (hcls z hz)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [hIso_hom_hcls, h, hIso_hom_hcls]
  rfl

end Naturality

end SpineTask19
