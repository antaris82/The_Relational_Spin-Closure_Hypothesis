import RequestProject.Spine.AlgebraicTopology.HomologyElements

/-!
# Naive (element-level) homology of a chain complex, and its comparison with the categorical one

The categorical homology `HomologicalComplex.homology` of a chain complex of `ModuleCat R` is
the object the rest of the project works with, but the cochain-level layer of the Spine is
written with honest submodules and quotients.  This module supplies the dictionary.

For an `ℕ`-indexed family of `R`-modules `M` with differentials `d n : M (n+1) →ₗ M n`:

* `SpineNaiveHomology.cycles d n` — `ker (d (n-1))`, with the convention `cycles d 0 = ⊤`;
* `SpineNaiveHomology.boundaries d n` — `range (d n)`;
* `SpineNaiveHomology.Homology d n` — the quotient `Z_n / B_n`;
* `SpineNaiveHomology.homologyMap` — the map induced by a chain map.

The comparison theorem is `SpineNaiveHomology.bijective_homologyMap_of_isIso`: if the
*categorical* homology map of a chain map of `ChainComplex (ModuleCat R) ℕ` is an isomorphism
in some degree, then the naive homology map is bijective in that degree.  The differentials and
the degreewise maps are taken as parameters together with equations identifying them with the
data of the complexes, so that the theorem can be applied to a complex whose differentials are
only *equal* (not definitionally equal) to the maps at hand.

Nothing here is specific to simplicial sets, nerves or geometry.
-/

noncomputable section

open CategoryTheory

universe u v

namespace SpineNaiveHomology

variable {R : Type v} [Ring R] {M N : ℕ → Type u}
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

/-! ## Cycles, boundaries and homology -/

/-- The cycles in degree `n`: the kernel of the differential leaving degree `n`.  In degree `0`
there is no such differential, so every chain is a cycle. -/
def cycles (d : ∀ n, M (n + 1) →ₗ[R] M n) : (n : ℕ) → Submodule R (M n)
  | 0 => ⊤
  | n + 1 => LinearMap.ker (d n)

/-- The boundaries in degree `n`: the image of the differential entering degree `n`. -/
def boundaries (d : ∀ n, M (n + 1) →ₗ[R] M n) (n : ℕ) : Submodule R (M n) :=
  LinearMap.range (d n)

variable (d : ∀ n, M (n + 1) →ₗ[R] M n) (e : ∀ n, N (n + 1) →ₗ[R] N n)

theorem boundaries_le_cycles (hdd : ∀ n, (d n).comp (d (n + 1)) = 0) (n : ℕ) :
    boundaries d n ≤ cycles d n := by
  cases n with
  | zero => exact le_top
  | succ m =>
      rintro _ ⟨x, rfl⟩
      exact congrFun (congrArg DFunLike.coe (hdd m)) x

/-- The boundaries, viewed inside the cycles. -/
def boundariesIn (n : ℕ) : Submodule R (cycles d n) :=
  Submodule.comap (cycles d n).subtype (boundaries d n)

/-- **Naive homology** `H_n = Z_n / B_n`. -/
def Homology (n : ℕ) : Type u := (cycles d n) ⧸ (boundariesIn d n)

instance (n : ℕ) : AddCommGroup (Homology d n) :=
  inferInstanceAs (AddCommGroup ((cycles d n) ⧸ (boundariesIn d n)))

instance (n : ℕ) : Module R (Homology d n) :=
  inferInstanceAs (Module R ((cycles d n) ⧸ (boundariesIn d n)))

/-- The homology class of a cycle. -/
def cls {n : ℕ} (z : cycles d n) : Homology d n :=
  Submodule.Quotient.mk (p := boundariesIn d n) z

theorem cls_surjective (n : ℕ) : Function.Surjective (cls d (n := n)) :=
  Submodule.Quotient.mk_surjective _

theorem cls_eq_zero_iff {n : ℕ} (z : cycles d n) :
    cls d z = 0 ↔ (z : M n) ∈ boundaries d n := by
  rw [cls, Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

theorem cls_eq_iff {n : ℕ} (z w : cycles d n) :
    cls d z = cls d w ↔ (z : M n) - (w : M n) ∈ boundaries d n := by
  rw [← sub_eq_zero (a := cls d z)]
  have h : cls d z - cls d w = cls d (z - w) := rfl
  rw [h]
  exact cls_eq_zero_iff d (z - w)

/-! ## The map induced by a chain map -/

variable (f : ∀ n, M n →ₗ[R] N n)
  (hf : ∀ n, (e n).comp (f (n + 1)) = (f n).comp (d n))

include hf

theorem mapsTo_cycles (n : ℕ) : ∀ z ∈ cycles d n, f n z ∈ cycles e n := by
  cases n with
  | zero => intro z _; exact Submodule.mem_top
  | succ m =>
      intro z hz
      have h := congrFun (congrArg DFunLike.coe (hf m)) z
      simp only [LinearMap.comp_apply] at h
      show e m (f (m + 1) z) = 0
      rw [h, show d m z = 0 from hz, map_zero]

/-- The map of cycles induced by a chain map. -/
def cyclesMap (n : ℕ) : cycles d n →ₗ[R] cycles e n :=
  (f n).restrict (mapsTo_cycles d e f hf n)

theorem cyclesMap_coe (n : ℕ) (z : cycles d n) :
    ((cyclesMap d e f hf n z : cycles e n) : N n) = f n z := rfl

theorem mapsTo_boundariesIn (n : ℕ) :
    ∀ z ∈ boundariesIn d n, cyclesMap d e f hf n z ∈ boundariesIn e n := by
  rintro z hz
  obtain ⟨x, hx⟩ := hz
  refine ⟨f (n + 1) x, ?_⟩
  have h := congrFun (congrArg DFunLike.coe (hf n)) x
  simp only [LinearMap.comp_apply] at h
  rw [h, hx]
  rfl

/-- **The map induced on naive homology by a chain map.** -/
def homologyMap (n : ℕ) : Homology d n →ₗ[R] Homology e n :=
  Submodule.mapQ (boundariesIn d n) (boundariesIn e n) (cyclesMap d e f hf n)
    (mapsTo_boundariesIn d e f hf n)

@[simp] theorem homologyMap_cls (n : ℕ) (z : cycles d n) :
    homologyMap d e f hf n (cls d z) = cls e (cyclesMap d e f hf n z) := rfl

end SpineNaiveHomology

/-! ## Comparison with the categorical homology -/

namespace SpineNaiveHomology

open SpineChainElements

variable {R : Type v} [Ring R]

/-- The graded family of modules underlying a chain complex. -/
abbrev cxMod (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) : Type u := (K.X n : Type u)

/-- The differentials of a chain complex, as maps of modules. -/
abbrev cxD (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) : cxMod K (n + 1) →ₗ[R] cxMod K n :=
  (K.d (n + 1) n).hom

variable {K L : ChainComplex (ModuleCat.{u} R) ℕ}

/-- The cycles of the complex, computed from `d (n+1) n`, are the kernel of the differential
leaving degree `n`. -/
theorem cycles_eq_ker_dFrom (n : ℕ) :
    cycles (cxD K) n = LinearMap.ker ((K.sc n).g).hom := by
  have hg : (K.sc n).g = K.dFrom n := rfl
  rw [hg]
  cases n with
  | zero =>
      refine le_antisymm (fun x _ => ?_) le_top
      exact dFrom_zero_eq_zero x
  | succ m =>
      refine le_antisymm (fun x hx => dFrom_eq_zero_of_d m x hx) (fun x hx => ?_)
      have hxx : (K.dFrom (m + 1)).hom x = 0 := hx
      rw [K.dFrom_eq (j := m) rfl] at hxx
      have hxx' : (K.xNextIso (i := m + 1) (j := m) rfl).inv.hom ((K.d (m + 1) m).hom x) = 0 := hxx
      have hinj : Function.Injective (K.xNextIso (i := m + 1) (j := m) rfl).inv.hom :=
        (ModuleCat.mono_iff_injective _).1 inferInstance
      show (K.d (m + 1) m).hom x = 0
      apply hinj
      rw [hxx', map_zero]

/-- The canonical linear map from the cycles to the categorical homology. -/
def zeta (n : ℕ) : cycles (cxD K) n →ₗ[R] (K.homology n) :=
  (K.homologyπ n).hom ∘ₗ ((K.sc n).moduleCatCyclesIso.inv).hom ∘ₗ
    (Submodule.inclusion (le_of_eq (cycles_eq_ker_dFrom (K := K) n)))

theorem zeta_iCycles (n : ℕ) (z : cycles (cxD K) n) :
    (K.iCycles n).hom (((K.sc n).moduleCatCyclesIso.inv).hom
        (Submodule.inclusion (le_of_eq (cycles_eq_ker_dFrom (K := K) n)) z))
      = (z : cxMod K n) :=
  ShortComplex.moduleCatCyclesIso_inv_iCycles_apply (K.sc n) _

theorem mem_cycles_iCycles (n : ℕ) (c : (K.sc n).cycles) :
    (K.iCycles n).hom c ∈ cycles (cxD K) n := by
  rw [cycles_eq_ker_dFrom (K := K) n]
  show ((K.sc n).g).hom ((K.iCycles n).hom c) = 0
  have h := congrArg ModuleCat.Hom.hom (K.sc n).iCycles_g
  have := congrFun (congrArg DFunLike.coe h) c
  simpa using this

theorem zeta_surjective (n : ℕ) : Function.Surjective (zeta (K := K) n) := by
  intro y
  obtain ⟨c, hc⟩ := homologyπ_surjective (K := K) n y
  refine ⟨⟨(K.iCycles n).hom c, mem_cycles_iCycles (K := K) n c⟩, ?_⟩
  show (K.homologyπ n).hom (((K.sc n).moduleCatCyclesIso.inv).hom _) = y
  have hcc : ((K.sc n).moduleCatCyclesIso.inv).hom
      (Submodule.inclusion (le_of_eq (cycles_eq_ker_dFrom (K := K) n))
        ⟨(K.iCycles n).hom c, mem_cycles_iCycles (K := K) n c⟩) = c := by
    apply iCycles_injective (K := K) n
    exact zeta_iCycles (K := K) n ⟨(K.iCycles n).hom c, mem_cycles_iCycles (K := K) n c⟩
  exact (congrArg (K.homologyπ n).hom hcc).trans hc

theorem zeta_eq_zero_iff (n : ℕ) (z : cycles (cxD K) n) :
    zeta n z = 0 ↔ (z : cxMod K n) ∈ boundaries (cxD K) n := by
  rw [zeta]
  show (K.homologyπ n).hom (((K.sc n).moduleCatCyclesIso.inv).hom _) = 0 ↔ _
  rw [homologyπ_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb.trans (zeta_iCycles (K := K) n z)⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, hb.trans (zeta_iCycles (K := K) n z).symm⟩

theorem zeta_naturality (F : K ⟶ L) (n : ℕ)
    (hf : ∀ m, (cxD L m).comp ((F.f (m + 1)).hom) = ((F.f m).hom).comp (cxD K m))
    (z : cycles (cxD K) n) :
    (HomologicalComplex.homologyMap F n).hom (zeta n z)
      = zeta n (cyclesMap (cxD K) (cxD L) (fun m => (F.f m).hom) hf n z) := by
  set cK := ((K.sc n).moduleCatCyclesIso.inv).hom
    (Submodule.inclusion (le_of_eq (cycles_eq_ker_dFrom (K := K) n)) z) with hcK
  set cL := ((L.sc n).moduleCatCyclesIso.inv).hom
    (Submodule.inclusion (le_of_eq (cycles_eq_ker_dFrom (K := L) n))
      (cyclesMap (cxD K) (cxD L) (fun m => (F.f m).hom) hf n z)) with hcL
  have hstep : (HomologicalComplex.cyclesMap F n).hom cK = cL := by
    apply iCycles_injective (K := L) n
    have h1 : (L.iCycles n).hom ((HomologicalComplex.cyclesMap F n).hom cK)
        = (F.f n).hom ((K.iCycles n).hom cK) := by
      have := congrArg ModuleCat.Hom.hom (HomologicalComplex.cyclesMap_i F n)
      exact congrFun (congrArg DFunLike.coe this) cK
    rw [h1, zeta_iCycles (K := K) n z, hcL, zeta_iCycles (K := L) n _]
    rfl
  show (HomologicalComplex.homologyMap F n).hom ((K.homologyπ n).hom cK) = _
  have hcomp : ∀ {M₁ M₂ M₃ : ModuleCat.{u} R} (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃) (x : M₁),
      (a ≫ b).hom x = b.hom (a.hom x) := fun _ _ _ => rfl
  have hnat := congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyπ_naturality F n)
  have hnat' := congrFun (congrArg DFunLike.coe hnat) cK
  rw [hcomp, hcomp] at hnat'
  show _ = (L.homologyπ n).hom cL
  rw [← hstep]
  exact hnat'

/-- **Categorical homology isomorphism implies naive homology bijectivity.**  The differentials
and the degreewise maps are parameters, identified with the data of the complexes by the
equations `hd`, `he`, `hfeq`; this makes the theorem applicable to complexes whose
differentials are only propositionally equal to the maps of interest. -/
theorem bijective_homologyMap_of_isIso (F : K ⟶ L)
    (d : ∀ n, cxMod K (n + 1) →ₗ[R] cxMod K n) (e : ∀ n, cxMod L (n + 1) →ₗ[R] cxMod L n)
    (f : ∀ n, cxMod K n →ₗ[R] cxMod L n)
    (hd : ∀ n, d n = cxD K n) (he : ∀ n, e n = cxD L n)
    (hfeq : ∀ n, f n = (F.f n).hom)
    (hf : ∀ n, (e n).comp (f (n + 1)) = (f n).comp (d n)) (n : ℕ)
    (hiso : IsIso (HomologicalComplex.homologyMap F n)) :
    Function.Bijective (homologyMap d e f hf n) := by
  have hd' : d = cxD K := funext hd
  have he' : e = cxD L := funext he
  have hf' : f = fun m => (F.f m).hom := funext hfeq
  subst hd'
  subst he'
  subst hf'
  have hcat : Function.Bijective (HomologicalComplex.homologyMap F n).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 hiso
  constructor
  · refine (injective_iff_map_eq_zero _).2 ?_
    intro ξ hξ
    obtain ⟨z, rfl⟩ := cls_surjective (cxD K) n ξ
    rw [homologyMap_cls, cls_eq_zero_iff] at hξ
    rw [cls_eq_zero_iff]
    have h0 : zeta (K := L) n (cyclesMap (cxD K) (cxD L) (fun m => (F.f m).hom) hf n z) = 0 :=
      (zeta_eq_zero_iff n _).2 hξ
    have h1 : (HomologicalComplex.homologyMap F n).hom (zeta n z) = 0 := by
      rw [zeta_naturality F n hf z]; exact h0
    have h2 : zeta (K := K) n z = 0 := hcat.1 (by rw [h1, map_zero])
    exact (zeta_eq_zero_iff n z).1 h2
  · intro ξ
    obtain ⟨w, rfl⟩ := cls_surjective (cxD L) n ξ
    obtain ⟨h, hh⟩ := hcat.2 (zeta (K := L) n w)
    obtain ⟨z, rfl⟩ := zeta_surjective (K := K) n h
    refine ⟨cls (cxD K) z, ?_⟩
    rw [homologyMap_cls, cls_eq_iff]
    have hz : zeta (K := L) n
        (cyclesMap (cxD K) (cxD L) (fun m => (F.f m).hom) hf n z - w) = 0 := by
      rw [map_sub, ← zeta_naturality F n hf z, hh, sub_self]
    exact (zeta_eq_zero_iff n _).1 hz

end SpineNaiveHomology
