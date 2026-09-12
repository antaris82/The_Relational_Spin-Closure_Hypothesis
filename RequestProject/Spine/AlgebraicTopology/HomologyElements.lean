import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Elements of cycles and of the homology of a chain complex of modules

The homology API of `HomologicalComplex` is categorical: `K.cycles q`, `K.homologyπ q`,
`K.iCycles q`.  For a complex of `R`-modules those objects have elements, and the three
statements below are the element-level dictionary that an ordinary "diagram chase" needs.
They are stated once here, for an arbitrary ring `R`, and are used by the assembly of a
homology isomorphism out of an exhaustive family of subcomplexes.

* `exists_cycle` — an element of `K.X q` killed by the differential out of `q` is the
  underlying chain of a cycle;
* `homologyπ_eq_zero_iff` — a cycle has zero homology class exactly when its underlying chain
  is a boundary;
* `homologyπ_surjective` / `iCycles_injective` — the two formal facts (`homologyπ` is an
  epimorphism, `iCycles` a monomorphism) in element form.

Nothing here is specific to singular or simplicial homology.
-/

noncomputable section

open CategoryTheory Limits

universe u v

namespace SpineChainElements

variable {R : Type v} [Ring R] {K : ChainComplex (ModuleCat.{u} R) ℕ}

/-- `homologyπ` is an epimorphism, hence surjective on elements: every homology class is the
class of a cycle. -/
theorem homologyπ_surjective (q : ℕ) : Function.Surjective (K.homologyπ q).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- `iCycles` is a monomorphism, hence injective on elements: a cycle is determined by its
underlying chain. -/
theorem iCycles_injective (q : ℕ) : Function.Injective (K.iCycles q).hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

/-- **Cycle constructor.**  A chain killed by the differential going out of degree `q` is the
underlying chain of a cycle. -/
theorem exists_cycle (q : ℕ) (x : K.X q) (hx : (K.dFrom q).hom x = 0) :
    ∃ z : K.cycles q, (K.iCycles q).hom z = x :=
  ⟨(K.sc q).moduleCatCyclesIso.inv ⟨x, hx⟩,
    ShortComplex.moduleCatCyclesIso_inv_iCycles_apply (K.sc q) ⟨x, hx⟩⟩

/-- A chain in degree `q` of a chain complex indexed by `ℕ` is killed by the differential going
out of `q` as soon as it is killed by `d q (q - 1)`; in degree `0` there is nothing to check. -/
theorem dFrom_eq_zero_of_d (q : ℕ) (x : K.X (q + 1)) (hx : (K.d (q + 1) q).hom x = 0) :
    (K.dFrom (q + 1)).hom x = 0 := by
  rw [K.dFrom_eq (j := q) rfl]
  show (K.xNextIso (i := q + 1) (j := q) rfl).inv.hom ((K.d (q + 1) q).hom x) = 0
  rw [hx, map_zero]

/-- In degree `0` the differential going out is zero. -/
theorem dFrom_zero_eq_zero (x : K.X 0) : (K.dFrom 0).hom x = 0 := by
  have h : K.dFrom 0 = 0 := K.dFrom_eq_zero (by simp)
  rw [h]
  rfl

/-- **The boundary criterion.**  A cycle has zero homology class exactly when its underlying
chain is the image of a chain of degree `q + 1`. -/
theorem homologyπ_eq_zero_iff (q : ℕ) (z : K.cycles q) :
    (K.homologyπ q).hom z = 0 ↔
      ∃ b : K.X (q + 1), (K.d (q + 1) q).hom b = (K.iCycles q).hom z := by
  have key := ShortComplex.π_moduleCatCyclesIso_hom_apply (K.sc q) z
  have hi := ShortComplex.moduleCatCyclesIso_hom_i_apply (K.sc q) z
  have hdTo : ∀ b : K.X ((ComplexShape.down ℕ).prev q),
      (K.dTo q).hom b = (K.d (q + 1) q).hom ((K.xPrevIso (i := q + 1) rfl).hom.hom b) := by
    intro b
    rw [K.dTo_eq (i := q + 1) rfl]
    rfl
  constructor
  · intro h
    have h0 : (ConcreteCategory.hom (K.sc q).moduleCatHomologyIso.hom)
        ((ConcreteCategory.hom (K.homologyπ q)) z) = 0 := by
      have h' : (ConcreteCategory.hom (K.homologyπ q)) z = 0 := h
      rw [h']
      exact map_zero _
    obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 (key.symm.trans h0)
    exact ⟨(K.xPrevIso (i := q + 1) rfl).hom.hom b,
      ((hdTo b).symm.trans (congrArg Subtype.val hb)).trans hi⟩
  · rintro ⟨b, hb⟩
    have hmono : Function.Injective
        ⇑(ConcreteCategory.hom (C := ModuleCat R) (K.sc q).moduleCatHomologyIso.hom) :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    apply hmono
    rw [map_zero]
    refine key.trans ((Submodule.Quotient.mk_eq_zero _).2
      ⟨(K.xPrevIso (i := q + 1) rfl).inv.hom b, Subtype.ext ?_⟩)
    have hb' : (K.dTo q).hom ((K.xPrevIso (i := q + 1) rfl).inv.hom b)
        = (K.d (q + 1) q).hom b := by
      rw [hdTo]
      congr 1
      exact ConcreteCategory.congr_hom (K.xPrevIso (i := q + 1) rfl).inv_hom_id b
    exact (hb'.trans hb).trans hi.symm

/-- A cycle whose underlying chain is a boundary has zero homology class. -/
theorem homologyπ_eq_zero (q : ℕ) (z : K.cycles q) (b : K.X (q + 1))
    (hb : (K.d (q + 1) q).hom b = (K.iCycles q).hom z) :
    (K.homologyπ q).hom z = 0 :=
  (homologyπ_eq_zero_iff q z).2 ⟨b, hb⟩

end SpineChainElements
