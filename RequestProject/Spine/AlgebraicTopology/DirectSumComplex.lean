import RequestProject.Spine.AlgebraicTopology.RelativeChains

/-!
# Direct sums of chain complexes

The purely algebraic model of a direct-sum decomposition of a chain complex of `ℤ₂`-modules:
the `α`-indexed direct sum of copies of a chain complex `C`, its summand inclusions and
projections, and the comparison map on homology attached to a family of chain maps.

* `finsuppCx α C` — the `α`-indexed direct sum of copies of `C` (levelwise `α →₀ C.X q`,
  differential applied componentwise), with its summand inclusions `finsuppCxι` and
  projections `finsuppCxπ`, which satisfy the orthogonality relations `finsuppCxι_π_self` and
  `finsuppCxι_π_ne`.
* `sumHomologyMap Ι q` — for a family `Ι : α → (C ⟶ K)` of chain maps, the comparison
  `(α →₀ H_q(C)) ⟶ H_q(K)`, `single s m ↦ H_q(Ι s) m`.
* `homologyMap_comp_apply`, `homologyMap_sum_apply` — functoriality and additivity of the
  homology functor, in the elementwise form used to compute with the comparison map.

Nothing here is specific to singular homology, and no finiteness is assumed anywhere: the
index type `α` is arbitrary.  That the comparison map is an isomorphism is
`RequestProject.Spine.AlgebraicTopology.DirectSumHomology`.
-/

noncomputable section

open CategoryTheory Limits

universe u

namespace SpineTask23

/-! ## The comparison map attached to a family of chain maps -/

section Splitting

variable {α : Type u} {C K : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ}

/-- The comparison `(α →₀ H_q(C)) ⟶ H_q(K)` attached to a family of chain maps `C ⟶ K`. -/
def sumHomologyMap (Ι : α → (C ⟶ K)) (q : ℕ) :
    ModuleCat.of (ZMod 2) (α →₀ ↥(C.homology q)) ⟶ K.homology q :=
  ModuleCat.ofHom
    (Finsupp.lsum (ZMod 2) fun s => (HomologicalComplex.homologyMap (Ι s) q).hom)

theorem sumHomologyMap_single (Ι : α → (C ⟶ K)) (q : ℕ) (s : α) (m : ↥(C.homology q)) :
    (sumHomologyMap Ι q).hom (Finsupp.single s m)
      = (HomologicalComplex.homologyMap (Ι s) q).hom m := by
  show Finsupp.sum (Finsupp.single s m)
    (fun s m => (HomologicalComplex.homologyMap (Ι s) q).hom m) = _
  exact Finsupp.sum_single_index (map_zero _)

theorem homologyMap_comp_apply {C' : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ}
    (f : C ⟶ K) (g : K ⟶ C') (q : ℕ) (m : ↥(C.homology q)) :
    (HomologicalComplex.homologyMap g q).hom ((HomologicalComplex.homologyMap f q).hom m)
      = (HomologicalComplex.homologyMap (f ≫ g) q).hom m := by
  rw [HomologicalComplex.homologyMap_comp]; rfl

theorem homologyMap_sum_apply {ι : Type*} (f : ι → (C ⟶ K)) (s : Finset ι) (q : ℕ)
    (m : ↥(C.homology q)) :
    (HomologicalComplex.homologyMap (∑ a ∈ s, f a) q).hom m
      = ∑ a ∈ s, (HomologicalComplex.homologyMap (f a) q).hom m := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      show (HomologicalComplex.homologyMap (0 : C ⟶ K) q).hom m = 0
      rw [HomologicalComplex.homologyMap_zero]
      rfl
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      show (HomologicalComplex.homologyMap
        (f a + ∑ b ∈ s, f b) q).hom m = _
      rw [show HomologicalComplex.homologyMap (f a + ∑ b ∈ s, f b) q
          = HomologicalComplex.homologyMap (f a) q
            + HomologicalComplex.homologyMap (∑ b ∈ s, f b) q from
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} (ZMod 2))
          (ComplexShape.down ℕ) q).map_add]
      rfl

end Splitting

/-! ## The `α`-indexed direct sum of copies of a chain complex -/

section FinsuppCx

variable (α : Type u) (C : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ)

/-- The direct sum of `α` copies of the chain complex `C`. -/
def finsuppCx : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ :=
  ChainComplex.of (fun q => ModuleCat.of (ZMod 2) (α →₀ ↥(C.X q)))
    (fun q => ModuleCat.ofHom (Finsupp.mapRange.linearMap (C.d (q + 1) q).hom))
    (fun q => by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      refine Finsupp.ext fun s => ?_
      show (C.d (q + 1) q).hom ((C.d (q + 1 + 1) (q + 1)).hom (x s)) = (0 : α →₀ ↥(C.X q)) s
      have hdd := C.d_comp_d (q + 1 + 1) (q + 1) q
      have hz : (C.d (q + 1) q).hom ((C.d (q + 1 + 1) (q + 1)).hom (x s)) = 0 := by
        rw [show (C.d (q + 1) q).hom ((C.d (q + 1 + 1) (q + 1)).hom (x s))
            = (C.d (q + 1 + 1) (q + 1) ≫ C.d (q + 1) q).hom (x s) from rfl, hdd]
        rfl
      rw [hz]
      rfl)

theorem finsuppCx_X (q : ℕ) :
    (finsuppCx α C).X q = ModuleCat.of (ZMod 2) (α →₀ ↥(C.X q)) := rfl

theorem finsuppCx_d (q : ℕ) :
    (finsuppCx α C).d (q + 1) q
      = ModuleCat.ofHom (Finsupp.mapRange.linearMap (C.d (q + 1) q).hom) :=
  ChainComplex.of_d _ _ _ q

/-- The inclusion of the `s`-summand. -/
def finsuppCxι (s : α) : C ⟶ finsuppCx α C where
  f q := ModuleCat.ofHom (Finsupp.lsingle s)
  comm' i j hij := by
    obtain rfl : i = j + 1 := SpineTask14.down_rel hij
    rw [finsuppCx_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    show Finsupp.mapRange _ (map_zero _) (Finsupp.single s x)
      = Finsupp.single s ((C.d (j + 1) j).hom x)
    rw [Finsupp.mapRange_single]

/-- The projection to the `s`-summand. -/
def finsuppCxπ (s : α) : finsuppCx α C ⟶ C where
  f q := ModuleCat.ofHom (Finsupp.lapply s)
  comm' i j hij := by
    obtain rfl : i = j + 1 := SpineTask14.down_rel hij
    rw [finsuppCx_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

variable {α C}

theorem finsuppCxι_π_self (s : α) : finsuppCxι α C s ≫ finsuppCxπ α C s = 𝟙 C := by
  refine HomologicalComplex.hom_ext _ _ fun q => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show (Finsupp.single s x : α →₀ ↥(C.X q)) s = x
  rw [Finsupp.single_eq_same]

theorem finsuppCxι_π_ne {s t : α} (hst : s ≠ t) :
    finsuppCxι α C s ≫ finsuppCxπ α C t = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun q => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show (Finsupp.single s x : α →₀ ↥(C.X q)) t = 0
  rw [Finsupp.single_eq_of_ne (Ne.symm hst)]

end FinsuppCx

end SpineTask23
