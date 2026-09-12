import RequestProject.Spine.Cohomology.Prism
import RequestProject.Spine.GoodCover.PointCohomology

/-!
# Task 8, WP5–WP9 : homotopy invariance of the native singular mod-2 cohomology

The prism operator of `Prism.lean` is a genuine cochain homotopy between the two pullbacks of a
homotopy.  This module takes it to cohomology.

```
    f ≃ g   ⟹   Hmap f n = Hmap g n
    X ≃ₕ Y  ⟹   Hⁿ(Y;ℤ₂) ≅ Hⁿ(X;ℤ₂)         (the isomorphism *is* `Hmap` of the equivalence)
    X ≃ₕ *  ⟹   Hⁿ⁺¹(X;ℤ₂) = 0
```

## Contents

* **WP5** `Mod2Cohomology.cochainHomotopy` / `Mod2Cohomology.cochainHomotopy_zero` — the
  cochain-homotopy relation `g* + f* = δK + Kδ`, in the exact Task-5 coboundary convention;
* **WP6** `Mod2Cohomology.pullback_add_pullback_mem_coboundaries` — on a *cocycle* the sum
  `g*α + f*α` is a coboundary; the proof consumes `δα = 0`;
* **WP7** `Mod2Cohomology.Hmap_eq_of_homotopy`, `Mod2Cohomology.Hmap_eq_of_homotopic` — the main
  theorem, **in every degree**;
* **WP8** `Mod2Cohomology.homotopyEquivCohomology` — the induced isomorphism of a homotopy
  equivalence, whose forward map is *definitionally* `Hmap` of the equivalence and whose
  inverse is `Hmap` of the homotopy inverse; `homotopyEquivCohomology_apply` records this;
* **WP9** `Mod2Cohomology.cohomology_succ_eq_zero_of_contractible` — contractible spaces have
  vanishing positive-degree cohomology, with the two degrees the certification path needs.

No transport is postulated anywhere: every map in this file is `Mod2Cohomology.Hmap` of an
actual continuous map.
-/

noncomputable section

namespace Mod2Cohomology

open CategoryTheory Opposite

universe u

variable {X Y : TopCat.{u}} {f g : X ⟶ Y}

/-! ## WP5 : the cochain homotopy -/

/-- **WP5.**  The cochain-homotopy relation in positive degree, written in the direction
`g* + f* = δK + Kδ`.  It is the prism identity `Mod2Cohomology.prismK_identity` read backwards;
the coboundary `δ` is the Task-5 one, and `K = prismK` lowers degree by one exactly as required
of a cochain homotopy. -/
theorem cochainHomotopy (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ)
    (c : Cochain Y (n + 1)) :
    pullback g (n + 1) c + pullback f (n + 1) c
      = d X n (prismK H n c) + prismK H (n + 1) (d Y (n + 1) c) :=
  (prismK_identity H n c).symm

/-- **WP5, degree zero.**  There is no `K` in degree `-1`, so the relation degenerates to
`g* + f* = Kδ`. -/
theorem cochainHomotopy_zero (H : ContinuousMap.Homotopy f.hom g.hom) (c : Cochain Y 0) :
    pullback g 0 c + pullback f 0 c = prismK H 0 (d Y 0 c) :=
  (prismK_identity_zero H c).symm

/-! ## WP6 : the consequence on cocycles -/

/-- **WP6.**  For a *cocycle* `α` the cochain `g*α + f*α` is a coboundary.  The hypothesis
`δα = 0` is what kills the term `K(δα)` of the cochain homotopy; in degree zero it kills the
whole right-hand side, so `g*α = f*α` on the nose. -/
theorem pullback_add_pullback_mem_coboundaries (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ)
    {c : Cochain Y n} (hc : d Y n c = 0) :
    pullback g n c + pullback f n c ∈ coboundaries X n := by
  cases n with
  | zero =>
      rw [cochainHomotopy_zero H c, hc, map_zero, coboundaries_zero, Submodule.mem_bot]
  | succ m =>
      rw [cochainHomotopy H m c, hc, map_zero, add_zero, coboundaries_succ]
      exact ⟨prismK H m c, rfl⟩

/-! ## WP7 : the main theorem -/

/-- **WP7, the principal theorem of Task 8.**  Homotopic continuous maps induce the *same*
pullback on the native singular mod-2 cohomology, in every degree.

The proof is the genuine prism/chain-homotopy argument: the two representing cocycles differ by
`δ(Kα)` with `K` the prism operator, so they define the same class in the Task-5 quotient. -/
theorem Hmap_eq_of_homotopy (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) :
    Hmap f n = Hmap g n := by
  ext x
  obtain ⟨z, rfl⟩ := mk_surjective x
  rw [Hmap_mk, Hmap_mk, mk_eq_mk_iff]
  show pullback f n (z : Cochain Y n) - pullback g n (z : Cochain Y n) ∈ coboundaries X n
  rw [CharTwo.sub_cochain, add_comm]
  exact pullback_add_pullback_mem_coboundaries H n z.2

/-- **WP7, homotopy-class form.**  `f ≃ g ⟹ f* = g*` on `Hⁿ(·;ℤ₂)`. -/
theorem Hmap_eq_of_homotopic (h : (f.hom).Homotopic (g.hom)) (n : ℕ) :
    Hmap f n = Hmap g n :=
  h.elim fun H => Hmap_eq_of_homotopy H n

/-! ## WP8 : homotopy equivalences -/

section HomotopyEquiv

variable (e : ContinuousMap.HomotopyEquiv (X : Type u) (Y : Type u))

/-- The forward map of a homotopy equivalence, as a morphism of `TopCat`. -/
def hequivFwd : X ⟶ Y := TopCat.ofHom e.toFun

/-- The homotopy inverse of a homotopy equivalence, as a morphism of `TopCat`. -/
def hequivInv : Y ⟶ X := TopCat.ofHom e.invFun

/-- `Hmap` of the homotopy inverse is a left inverse of `Hmap` of the equivalence. -/
theorem Hmap_hequivInv_comp (n : ℕ) (q : Cohomology Y n) :
    Hmap (hequivInv e) n (Hmap (hequivFwd e) n q) = q := by
  have hcomp : Hmap (hequivInv e ≫ hequivFwd e) n
      = (Hmap (hequivInv e) n).comp (Hmap (hequivFwd e) n) :=
    Hmap_comp _ _ n
  have hhom : Hmap (hequivInv e ≫ hequivFwd e) n = Hmap (𝟙 Y) n :=
    Hmap_eq_of_homotopic (f := hequivInv e ≫ hequivFwd e) (g := 𝟙 Y) e.right_inv n
  have := congrArg (fun p : Cohomology Y n →ₗ[ZMod 2] Cohomology Y n => p q) (hcomp.symm.trans hhom)
  simpa [Hmap_id] using this

/-- `Hmap` of the homotopy inverse is a right inverse of `Hmap` of the equivalence. -/
theorem Hmap_hequivFwd_comp (n : ℕ) (q : Cohomology X n) :
    Hmap (hequivFwd e) n (Hmap (hequivInv e) n q) = q := by
  have hcomp : Hmap (hequivFwd e ≫ hequivInv e) n
      = (Hmap (hequivFwd e) n).comp (Hmap (hequivInv e) n) :=
    Hmap_comp _ _ n
  have hhom : Hmap (hequivFwd e ≫ hequivInv e) n = Hmap (𝟙 X) n :=
    Hmap_eq_of_homotopic (f := hequivFwd e ≫ hequivInv e) (g := 𝟙 X) e.left_inv n
  have := congrArg (fun p : Cohomology X n →ₗ[ZMod 2] Cohomology X n => p q) (hcomp.symm.trans hhom)
  simpa [Hmap_id] using this

/-- **WP8.**  A homotopy equivalence induces an isomorphism of the native singular mod-2
cohomology.  The forward map is *definitionally* `Hmap` of the equivalence's own continuous map
(`homotopyEquivCohomology_apply`) and the inverse is `Hmap` of its homotopy inverse
(`homotopyEquivCohomology_symm_apply`); nothing is chosen, and no free-standing transport is
introduced. -/
def homotopyEquivCohomology (n : ℕ) : Cohomology Y n ≃ₗ[ZMod 2] Cohomology X n where
  toFun := Hmap (hequivFwd e) n
  map_add' := (Hmap (hequivFwd e) n).map_add
  map_smul' := (Hmap (hequivFwd e) n).map_smul
  invFun := Hmap (hequivInv e) n
  left_inv := Hmap_hequivInv_comp e n
  right_inv := Hmap_hequivFwd_comp e n

@[simp] theorem homotopyEquivCohomology_apply (n : ℕ) (q : Cohomology Y n) :
    homotopyEquivCohomology e n q = Hmap (hequivFwd e) n q := rfl

@[simp] theorem homotopyEquivCohomology_symm_apply (n : ℕ) (q : Cohomology X n) :
    (homotopyEquivCohomology e n).symm q = Hmap (hequivInv e) n q := rfl

end HomotopyEquiv

/-! ## WP9 : contractible spaces -/

/-- **WP9.**  A contractible space has vanishing singular mod-2 cohomology in every positive
degree.  The class is transported to a one-point space by the *proved* homotopy invariance and
killed there by the *proved* point computation
`Mod2Cohomology.cohomology_succ_eq_zero_of_subsingleton`. -/
theorem cohomology_succ_eq_zero_of_contractible (Z : TopCat.{u}) [ContractibleSpace Z] (n : ℕ)
    (q : Cohomology Z (n + 1)) : q = 0 := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit (Z : Type u)
  let P : TopCat.{u} := TopCat.of PUnit.{u + 1}
  have hu : (Unit : Type) ≃ₜ (P : Type u) := Homeomorph.homeomorphOfUnique _ _
  let e' : ContinuousMap.HomotopyEquiv (Z : Type u) (P : Type u) := e.trans hu.toHomotopyEquiv
  haveI : Subsingleton (P : Type u) := inferInstanceAs (Subsingleton PUnit.{u + 1})
  haveI : Nonempty (P : Type u) := inferInstanceAs (Nonempty PUnit.{u + 1})
  have hzero : (homotopyEquivCohomology e' (n + 1)).symm q = 0 :=
    cohomology_succ_eq_zero_of_subsingleton n _
  exact (homotopyEquivCohomology e' (n + 1)).symm.map_eq_zero_iff.mp hzero

/-- Degree one, the first degree the good-cover programme needs. -/
theorem cohomology_one_eq_zero_of_contractible (Z : TopCat.{u}) [ContractibleSpace Z]
    (q : Cohomology Z 1) : q = 0 :=
  cohomology_succ_eq_zero_of_contractible Z 0 q

/-- Degree two, the degree carrying the Spin-lift obstruction. -/
theorem cohomology_two_eq_zero_of_contractible (Z : TopCat.{u}) [ContractibleSpace Z]
    (q : Cohomology Z 2) : q = 0 :=
  cohomology_succ_eq_zero_of_contractible Z 1 q

end Mod2Cohomology
