import RequestProject.Spine.AlgebraicTopology.DirectSumComplex
import RequestProject.Spine.AlgebraicTopology.Excision

/-!
# Chain maps out of a direct sum indexed by a family of simplicial maps

Generic homological algebra over `ℤ₂`, with no Nerve-specific input.  For a family
`φ : α → (S ⟶ T)` of maps of simplicial sets:

* `finsuppCxDesc` — the map out of the `α`-fold direct sum of a chain complex determined by a
  family of chain maps, with `finsuppCxι_desc : finsuppCxι α C s ≫ finsuppCxDesc F = F s`;
* `famSimp φ q : α × S_q → T_q` — the total map on `q`-simplices;
* `famChainMap φ : ⊕_α C_*(S) ⟶ C_*(T)` — the induced comparison.  It is a chain map because
  each component is: the differential compatibility is the naturality of the linearised
  boundary operator.  `isIso_famChainMap`: it is an isomorphism as soon as every `famSimp φ q`
  is bijective;
* `famRelChainMap` — the same construction for a family of maps of *pairs*, with
  `isIso_famRelChainMap`: an isomorphism as soon as, in addition, a `q`-simplex `(φ s) x` of
  `T` lies in the subobject exactly when `x` does.

The Nerve-specific application — the open cells of a realized skeletal pushout — is
`RequestProject.Spine.Nerve.CellFamily.RelativeChainDecomposition`.  The declarations keep
their historical `SpineTask24` namespace: moving them did not change a single statement.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet NerveGeom SpineTask13 SpineTask14
  SpineTask23

universe u

namespace SpineTask24

/-! ## The map out of a direct sum determined by a family of chain maps -/

section Desc

variable {α : Type u} {C K : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ}

/-- The degreewise component of `finsuppCxDesc`. -/
def finsuppCxDescMap (F : α → (C ⟶ K)) (q : ℕ) : (finsuppCx α C).X q ⟶ K.X q :=
  ModuleCat.ofHom (Finsupp.lsum (ZMod 2) fun s => ((F s).f q).hom)

theorem finsuppCxDescMap_single (F : α → (C ⟶ K)) (q : ℕ) (s : α) (x : C.X q) :
    (finsuppCxDescMap F q).hom (Finsupp.single s x) = ((F s).f q).hom x :=
  Finsupp.sum_single_index (map_zero _)

/-- The chain map out of the `α`-fold direct sum of `C` determined by a family of chain maps
`F s : C ⟶ K`.  (No finiteness: `Finsupp.lsum` is a finite sum on every element.) -/
def finsuppCxDesc (F : α → (C ⟶ K)) : finsuppCx α C ⟶ K where
  f q := finsuppCxDescMap F q
  comm' i j hij := by
    obtain rfl : i = j + 1 := down_rel hij
    rw [finsuppCx_d]
    refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun s => LinearMap.ext fun x => ?_)
    show (K.d (j + 1) j).hom ((finsuppCxDescMap F (j + 1)).hom (Finsupp.single s x))
      = (finsuppCxDescMap F j).hom
          (Finsupp.mapRange (C.d (j + 1) j).hom (map_zero _) (Finsupp.single s x))
    rw [Finsupp.mapRange_single, finsuppCxDescMap_single, finsuppCxDescMap_single]
    exact congrArg (fun (g : C.X (j + 1) ⟶ K.X j) => g.hom x) ((F s).comm (j + 1) j)

theorem finsuppCxDesc_f_single (F : α → (C ⟶ K)) (q : ℕ) (s : α) (x : C.X q) :
    ((finsuppCxDesc F).f q).hom (Finsupp.single s x) = ((F s).f q).hom x :=
  finsuppCxDescMap_single F q s x

theorem finsuppCxι_desc (F : α → (C ⟶ K)) (s : α) :
    finsuppCxι α C s ≫ finsuppCxDesc F = F s := by
  refine HomologicalComplex.hom_ext _ _ fun q => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact finsuppCxDesc_f_single F q s x

end Desc

/-! ## Free chains on a family of maps of simplicial sets -/

section Family

variable {α : Type u} {S T : SSet.{u}} (φ : α → (S ⟶ T))

/-- The total map on `q`-simplices attached to the family `φ`. -/
def famSimp (q : ℕ) (p : α × S.obj (op (SimplexCategory.mk q))) :
    T.obj (op (SimplexCategory.mk q)) :=
  (φ p.1).app (op (SimplexCategory.mk q)) p.2

/-- **WP1/WP2, absolute.**  The comparison `⊕_α C_*(S) ⟶ C_*(T)` attached to a family of maps
of simplicial sets.  It is a map of *chain complexes*: each component is the chain map induced
by a simplicial map, so it commutes with the boundary. -/
def famChainMap :
    finsuppCx α (sSetChainComplexFunctor.obj S) ⟶ sSetChainComplexFunctor.obj T :=
  finsuppCxDesc fun s => sSetChainComplexFunctor.map (φ s)

/-- The degreewise comparison, on the nose as a map of free `ℤ₂`-modules. -/
def famChainMapDeg (q : ℕ) : (α →₀ SSetChain S q) →ₗ[ZMod 2] SSetChain T q :=
  Finsupp.lsum (ZMod 2) fun s => sSetChainMap (φ s) q

theorem famChainMap_f_hom (q : ℕ) :
    ⇑((famChainMap φ).f q).hom = ⇑(famChainMapDeg φ q) := rfl

theorem famChainMapDeg_single (q : ℕ) (s : α) (c : SSetChain S q) :
    famChainMapDeg φ q (Finsupp.single s c) = sSetChainMap (φ s) q c :=
  Finsupp.sum_single_index (map_zero _)

theorem famSimp_injective_component (hinj : ∀ q, Function.Injective (famSimp φ q)) (q : ℕ)
    (s : α) : Function.Injective (fun y => famSimp φ q (s, y)) := fun y z h =>
  congrArg Prod.snd (hinj q (h : famSimp φ q (s, y) = famSimp φ q (s, z)))

/-- **The coordinate formula.**  On the `s`-th block the comparison is the identity. -/
theorem famChainMapDeg_apply (hinj : ∀ q, Function.Injective (famSimp φ q)) (q : ℕ)
    (d : α →₀ SSetChain S q) (s : α) (x : S.obj (op (SimplexCategory.mk q))) :
    famChainMapDeg φ q d (famSimp φ q (s, x)) = d s x := by
  classical
  have hval : famChainMapDeg φ q d
      = ∑ a ∈ d.support, Finsupp.mapDomain (fun y => famSimp φ q (a, y)) (d a) := rfl
  rw [hval, Finsupp.finset_sum_apply]
  by_cases hs : s ∈ d.support
  · rw [Finset.sum_eq_single_of_mem s hs ?_]
    · exact Finsupp.mapDomain_apply (famSimp_injective_component φ hinj q s) _ _
    · intro a _ has
      refine Finsupp.mapDomain_notin_range _ _ ?_
      rintro ⟨y, hy⟩
      exact has (congrArg Prod.fst (hinj q hy))
  · rw [Finsupp.notMem_support_iff.1 hs]
    refine (Finset.sum_eq_zero ?_).trans rfl
    intro a ha
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨y, hy⟩
    have has : a = s := congrArg Prod.fst (hinj q hy)
    exact hs (has ▸ ha)

theorem injective_famChainMapDeg (hinj : ∀ q, Function.Injective (famSimp φ q)) (q : ℕ) :
    Function.Injective (famChainMapDeg φ q) := by
  intro d d' h
  refine Finsupp.ext fun s => Finsupp.ext fun x => ?_
  rw [← famChainMapDeg_apply φ hinj q d s x, ← famChainMapDeg_apply φ hinj q d' s x, h]

theorem surjective_famChainMapDeg (hsurj : ∀ q, Function.Surjective (famSimp φ q)) (q : ℕ) :
    Function.Surjective (famChainMapDeg φ q) := by
  classical
  intro c
  refine LinearMap.mem_range.1 (SpineTask18.mem_of_single LinearMap.id
    (LinearMap.range (famChainMapDeg φ q)) c fun t _ => ?_)
  obtain ⟨⟨s, x⟩, rfl⟩ := hsurj q t
  exact ⟨Finsupp.single s (Finsupp.single x 1),
    (famChainMapDeg_single φ q s (Finsupp.single x 1)).trans (sSetChainMap_single _ _ _)⟩

theorem bijective_famChainMapDeg (hb : ∀ q, Function.Bijective (famSimp φ q)) (q : ℕ) :
    Function.Bijective (famChainMapDeg φ q) :=
  ⟨injective_famChainMapDeg φ (fun q => (hb q).1) q,
    surjective_famChainMapDeg φ (fun q => (hb q).2) q⟩

theorem isIso_famChainMap (hb : ∀ q, Function.Bijective (famSimp φ q)) :
    IsIso (famChainMap φ) := by
  have h : ∀ q, IsIso ((famChainMap φ).f q) := by
    intro q
    refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
    rw [famChainMap_f_hom]
    exact bijective_famChainMapDeg φ hb q
  exact HomologicalComplex.Hom.isIso_of_components _

end Family

/-! ## The relative version -/

section RelFamily

variable {α : Type u} {S₀ S T₀ T : SSet.{u}} (f : S₀ ⟶ S) (f' : T₀ ⟶ T)
  (φ : α → (S ⟶ T)) (ψ : α → (S₀ ⟶ T₀)) (hsq : ∀ s, f ≫ φ s = ψ s ≫ f')

/-- **WP3.**  The comparison `⊕_α C_*(S, S₀) ⟶ C_*(T, T₀)` attached to a family of maps of
pairs. -/
def famRelChainMap : finsuppCx α (relChainCx f) ⟶ relChainCx f' :=
  finsuppCxDesc fun s => relChainCxMap f f' (ψ s) (φ s) (hsq s)

/-- Its degreewise component, on the nose as a map of `ℤ₂`-modules. -/
def famRelChainMapDeg (q : ℕ) : (α →₀ RelChainMod f q) →ₗ[ZMod 2] RelChainMod f' q :=
  Finsupp.lsum (ZMod 2) fun s => ((relChainCxMap f f' (ψ s) (φ s) (hsq s)).f q).hom

theorem famRelChainMap_f_hom (q : ℕ) :
    ⇑((famRelChainMap f f' φ ψ hsq).f q).hom = ⇑(famRelChainMapDeg f f' φ ψ hsq q) := rfl

theorem famRelChainMapDeg_single (q : ℕ) (s : α) (c : SSetChain S q) :
    famRelChainMapDeg f f' φ ψ hsq q (Finsupp.single s (Submodule.Quotient.mk c))
      = Submodule.Quotient.mk (sSetChainMap (φ s) q c) :=
  Finsupp.sum_single_index (map_zero _)

/-- The componentwise quotient map `⊕_α C_*(S) ⟶ ⊕_α C_*(S, S₀)`. -/
def mapRangeMk (q : ℕ) : (α →₀ SSetChain S q) →ₗ[ZMod 2] (α →₀ RelChainMod f q) :=
  Finsupp.mapRange.linearMap (LinearMap.range (sSetChainMap f q)).mkQ

theorem mapRangeMk_single (q : ℕ) (s : α) (c : SSetChain S q) :
    mapRangeMk f q (Finsupp.single s c) = Finsupp.single s (Submodule.Quotient.mk c) := by
  show Finsupp.mapRange _ (map_zero _) (Finsupp.single s c) = _
  rw [Finsupp.mapRange_single]
  rfl

theorem mapRangeMk_apply (q : ℕ) (d : α →₀ SSetChain S q) (s : α) :
    mapRangeMk f q d s = Submodule.Quotient.mk (d s) := rfl

/-- The relative comparison is the absolute one, followed by the quotient maps. -/
theorem famRelChainMapDeg_mapRangeMk (q : ℕ) (d : α →₀ SSetChain S q) :
    famRelChainMapDeg f f' φ ψ hsq q (mapRangeMk f q d)
      = Submodule.Quotient.mk (famChainMapDeg φ q d) := by
  classical
  refine Finsupp.induction_linear d ?_ ?_ ?_
  · rw [map_zero, map_zero, map_zero]
    rfl
  · intro a b ha hb
    rw [map_add, map_add, ha, hb, map_add, Submodule.Quotient.mk_add]
  · intro s c
    rw [mapRangeMk_single, famRelChainMapDeg_single, famChainMapDeg_single]

theorem mapRangeMk_surjective (q : ℕ) :
    Function.Surjective (mapRangeMk (α := α) f q) := by
  classical
  intro y
  refine Finsupp.induction_linear y ?_ ?_ ?_
  · exact ⟨0, map_zero _⟩
  · rintro a b ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨c + d, map_add _ _ _⟩
  · intro s z
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Finsupp.single s c, mapRangeMk_single f q s c⟩

variable (hfinj : ∀ n, Function.Injective (f.app n))
  (hf'inj : ∀ n, Function.Injective (f'.app n))

include hfinj hf'inj in
theorem injective_famRelChainMapDeg (hinj : ∀ q, Function.Injective (famSimp φ q))
    (hrange : ∀ (q : ℕ) (s : α) (x : S.obj (op (SimplexCategory.mk q))),
      famSimp φ q (s, x) ∈ Set.range (f'.app (op (SimplexCategory.mk q)))
        ↔ x ∈ Set.range (f.app (op (SimplexCategory.mk q))))
    (q : ℕ) : Function.Injective (famRelChainMapDeg f f' φ ψ hsq q) := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨d, rfl⟩ := mapRangeMk_surjective f q y
  rw [famRelChainMapDeg_mapRangeMk] at hy
  have hmem := (SpineTask18.mem_range_sSetChainMap f' q (hf'inj _) _).1
    ((Submodule.Quotient.mk_eq_zero _).1 hy)
  refine Finsupp.ext fun s => ?_
  rw [mapRangeMk_apply]
  show (Submodule.Quotient.mk (d s) : RelChainMod f q) = 0
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  refine (SpineTask18.mem_range_sSetChainMap f q (hfinj _) (d s)).2 fun x hx => ?_
  refine (hrange q s x).1 (hmem _ (Finsupp.mem_support_iff.2 ?_))
  rw [famChainMapDeg_apply φ hinj q d s x]
  exact Finsupp.mem_support_iff.1 hx

theorem surjective_famRelChainMapDeg (hsurj : ∀ q, Function.Surjective (famSimp φ q)) (q : ℕ) :
    Function.Surjective (famRelChainMapDeg f f' φ ψ hsq q) := by
  intro y
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨d, rfl⟩ := surjective_famChainMapDeg φ hsurj q c
  exact ⟨_, famRelChainMapDeg_mapRangeMk f f' φ ψ hsq q d⟩

include hfinj hf'inj in
theorem isIso_famRelChainMap (hb : ∀ q, Function.Bijective (famSimp φ q))
    (hrange : ∀ (q : ℕ) (s : α) (x : S.obj (op (SimplexCategory.mk q))),
      famSimp φ q (s, x) ∈ Set.range (f'.app (op (SimplexCategory.mk q)))
        ↔ x ∈ Set.range (f.app (op (SimplexCategory.mk q)))) :
    IsIso (famRelChainMap f f' φ ψ hsq) := by
  have h : ∀ q, IsIso ((famRelChainMap f f' φ ψ hsq).f q) := by
    intro q
    refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
    rw [famRelChainMap_f_hom]
    exact ⟨injective_famRelChainMapDeg f f' φ ψ hsq hfinj hf'inj (fun q => (hb q).1) hrange q,
      surjective_famRelChainMapDeg f f' φ ψ hsq (fun q => (hb q).2) q⟩
  exact HomologicalComplex.Hom.isIso_of_components _

end RelFamily
end SpineTask24
