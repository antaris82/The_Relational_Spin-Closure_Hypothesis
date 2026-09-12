import RequestProject.Spine.AlgebraicTopology.NaiveHomology
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

/-!
# Duality: a homology isomorphism of free `ℤ₂`-complexes is a cohomology isomorphism

The Spine's chain groups are free `ℤ₂`-modules `Cₙ = (n-simplices →₀ ℤ₂)` and its cochain
groups are the function types `Cⁿ = (n-simplices → ℤ₂)`, which over the field `ℤ₂` is the dual
of the former (`freeDualEquiv`, i.e. `Finsupp.llift`).  Every `ℤ₂`-linear map of free modules
therefore has a transpose `dualOf`, and the whole cochain-level Spine is the transpose of the
chain-level Spine (`dualOf ∂ = δ`, `dualOf J = J*`).

This module proves the corresponding statement in cohomology:

**if a chain map of free `ℤ₂`-complexes induces a bijection on homology in every degree, then
its transpose induces a bijection on the cohomology of the dual (function-type) complexes in
every degree.**

This is `SpineDualCohomology.bijective_Hmap`.  Only two facts about the field `ℤ₂` are used:
a linear functional defined on a subspace extends to the whole space
(`LinearMap.exists_extend`), and a functional vanishing on a kernel factors through the image.
No universal-coefficient theorem, no finite dimensionality and no chain homotopy is used.

The cochain-level data (the coboundaries `δ`, `ε` and the comparison `φ`) are *parameters*,
tied to the chain-level data only by the equations `hδ`, `hε`, `hφmap`; this lets the theorem
be applied to cochain complexes that were defined independently and are only propositionally
equal to the transposed chain complexes.

Nothing here is specific to simplicial sets, nerves, covers or geometry.
-/

noncomputable section

namespace SpineDualCohomology

universe u

/-! ## The predual identification and the transpose -/

variable {A B C : Type u}

/-- `(A → ℤ₂)` is the `ℤ₂`-dual of the free module `(A →₀ ℤ₂)`; this is Mathlib's
`Finsupp.llift`, recorded with the coefficient ring `ℤ₂`. -/
def freeDualEquiv (A : Type u) : (A → ZMod 2) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (A →₀ ZMod 2) :=
  Finsupp.llift (ZMod 2) (ZMod 2) (ZMod 2) A

theorem freeDualEquiv_apply (g : A → ZMod 2) (x : A →₀ ZMod 2) :
    freeDualEquiv A g x = Finsupp.linearCombination (ZMod 2) g x := by
  simp [freeDualEquiv, Finsupp.llift, Finsupp.linearCombination_apply]

theorem freeDualEquiv_symm_apply (φ : Module.Dual (ZMod 2) (A →₀ ZMod 2)) (a : A) :
    (freeDualEquiv A).symm φ a = φ (Finsupp.single a 1) := by
  simp [freeDualEquiv, Finsupp.llift]

/-- **The transpose of a `ℤ₂`-linear map of free modules**, as a map of the corresponding
function-type cochain modules. -/
def dualOf (f : (A →₀ ZMod 2) →ₗ[ZMod 2] (B →₀ ZMod 2)) :
    (B → ZMod 2) →ₗ[ZMod 2] (A → ZMod 2) :=
  (freeDualEquiv A).symm.toLinearMap ∘ₗ f.dualMap ∘ₗ (freeDualEquiv B).toLinearMap

theorem dualOf_apply (f : (A →₀ ZMod 2) →ₗ[ZMod 2] (B →₀ ZMod 2)) (g : B → ZMod 2) (a : A) :
    dualOf f g a = Finsupp.linearCombination (ZMod 2) g (f (Finsupp.single a 1)) := by
  simp [dualOf, freeDualEquiv_symm_apply, freeDualEquiv_apply, LinearMap.dualMap_apply]

/-- **The defining adjunction property**: pairing a chain against a dualised cochain is the
same as pairing its image against the cochain. -/
theorem linearCombination_dualOf (f : (A →₀ ZMod 2) →ₗ[ZMod 2] (B →₀ ZMod 2))
    (g : B → ZMod 2) (x : A →₀ ZMod 2) :
    Finsupp.linearCombination (ZMod 2) g (f x)
      = Finsupp.linearCombination (ZMod 2) (dualOf f g) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single a c =>
      have hs : (Finsupp.single a c : A →₀ ZMod 2) = c • Finsupp.single a 1 := by
        simp [Finsupp.smul_single]
      rw [hs]
      simp only [map_smul]
      congr 1
      rw [Finsupp.linearCombination_single, one_smul, dualOf_apply]

/-! ## Functoriality of dualisation -/

@[simp] theorem dualOf_id : dualOf (LinearMap.id : (A →₀ ZMod 2) →ₗ[ZMod 2] (A →₀ ZMod 2))
    = LinearMap.id := by
  ext g a
  simp [dualOf_apply]

theorem dualOf_comp (f : (A →₀ ZMod 2) →ₗ[ZMod 2] (B →₀ ZMod 2))
    (g : (B →₀ ZMod 2) →ₗ[ZMod 2] (C →₀ ZMod 2)) :
    dualOf (g.comp f) = (dualOf f).comp (dualOf g) := by
  ext h a
  simp only [LinearMap.comp_apply, dualOf_apply]
  exact linearCombination_dualOf g h (f (Finsupp.single a 1))

theorem dualOf_add (f f' : (A →₀ ZMod 2) →ₗ[ZMod 2] (B →₀ ZMod 2)) :
    dualOf (f + f') = dualOf f + dualOf f' := by
  ext g a
  simp [dualOf_apply]

theorem dualOf_sum {γ : Type*} (s : Finset γ)
    (F : γ → (A →₀ ZMod 2) →ₗ[ZMod 2] (B →₀ ZMod 2)) :
    dualOf (∑ i ∈ s, F i) = ∑ i ∈ s, dualOf (F i) := by
  classical
  induction s using Finset.induction with
  | empty => ext g a; simp [dualOf_apply]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, dualOf_add, ih]

/-- The transpose of a linearised map of index sets is precomposition. -/
@[simp] theorem dualOf_lmapDomain (φ : A → B) :
    dualOf (Finsupp.lmapDomain (ZMod 2) (ZMod 2) φ)
      = LinearMap.funLeft (ZMod 2) (ZMod 2) φ := by
  ext g a
  simp [dualOf_apply, Finsupp.mapDomain_single]

/-- A cochain is determined by its pairings with the chains. -/
theorem cochain_ext {g h : A → ZMod 2}
    (hgh : ∀ x : A →₀ ZMod 2, Finsupp.linearCombination (ZMod 2) g x
      = Finsupp.linearCombination (ZMod 2) h x) : g = h := by
  funext a
  have := hgh (Finsupp.single a 1)
  simpa using this

/-! ## Cohomology of a function-type cochain complex -/

variable {α β : ℕ → Type u}

/-- The free `ℤ₂`-module on the `n`-th index type of a family; the chain module of a free
complex.  A reducible abbreviation, so that it unfolds against any concrete chain module. -/
abbrev FreeMod (α : ℕ → Type u) (n : ℕ) : Type u := α n →₀ ZMod 2

/-- The cocycles `Zⁿ = ker δⁿ`. -/
def cocycles (δ : ∀ n, (α n → ZMod 2) →ₗ[ZMod 2] (α (n + 1) → ZMod 2)) (n : ℕ) :
    Submodule (ZMod 2) (α n → ZMod 2) :=
  LinearMap.ker (δ n)

variable (δ : ∀ n, (α n → ZMod 2) →ₗ[ZMod 2] (α (n + 1) → ZMod 2))
  (ε : ∀ n, (β n → ZMod 2) →ₗ[ZMod 2] (β (n + 1) → ZMod 2))
  (BdA : ∀ n, Submodule (ZMod 2) (α n → ZMod 2))
  (BdB : ∀ n, Submodule (ZMod 2) (β n → ZMod 2))

/-- The coboundaries, viewed inside the cocycles. -/
def coboundariesIn (n : ℕ) : Submodule (ZMod 2) (cocycles δ n) :=
  Submodule.comap (cocycles δ n).subtype (BdA n)

/-- The cohomology `Hⁿ = Zⁿ/Bⁿ` of the cochain complex.  The coboundaries are a parameter,
tied to `δ` by the equations `BdA 0 = ⊥` and `BdA (n+1) = range (δ n)`; this keeps the type
definitionally equal to a cohomology defined independently with the same convention. -/
def Cohomology (n : ℕ) : Type u := (cocycles δ n) ⧸ (coboundariesIn δ BdA n)

instance (n : ℕ) : AddCommGroup (Cohomology δ BdA n) :=
  inferInstanceAs (AddCommGroup ((cocycles δ n) ⧸ (coboundariesIn δ BdA n)))

instance (n : ℕ) : Module (ZMod 2) (Cohomology δ BdA n) :=
  inferInstanceAs (Module (ZMod 2) ((cocycles δ n) ⧸ (coboundariesIn δ BdA n)))

/-- The cohomology class of a cocycle. -/
def cochainClass {n : ℕ} (z : cocycles δ n) : Cohomology δ BdA n :=
  Submodule.Quotient.mk (p := coboundariesIn δ BdA n) z

theorem cochainClass_surjective (n : ℕ) :
    Function.Surjective (cochainClass δ BdA (n := n)) :=
  Submodule.Quotient.mk_surjective _

theorem cochainClass_eq_zero_iff {n : ℕ} (z : cocycles δ n) :
    cochainClass δ BdA z = 0 ↔ (z : α n → ZMod 2) ∈ BdA n := by
  rw [cochainClass, Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

/-! ## The map induced by a map of cochain complexes -/

variable (φ : ∀ n, (β n → ZMod 2) →ₗ[ZMod 2] (α n → ZMod 2))

theorem map_mem_cocycles
    (hφ : ∀ (n : ℕ) (c : β n → ZMod 2), φ (n + 1) (ε n c) = δ n (φ n c))
    (n : ℕ) {c : β n → ZMod 2} (hc : c ∈ cocycles ε n) :
    φ n c ∈ cocycles δ n := by
  have hc' : ε n c = 0 := hc
  show δ n (φ n c) = 0
  rw [← hφ n c, hc', map_zero]

/-- The induced map on cocycles. -/
def cocyclesMap (hφ : ∀ (n : ℕ) (c : β n → ZMod 2), φ (n + 1) (ε n c) = δ n (φ n c))
    (n : ℕ) : cocycles ε n →ₗ[ZMod 2] cocycles δ n :=
  (φ n).restrict (fun _ hc => map_mem_cocycles δ ε φ hφ n hc)

theorem map_mem_coboundaries
    (hφ : ∀ (n : ℕ) (c : β n → ZMod 2), φ (n + 1) (ε n c) = δ n (φ n c))
    (hA0 : BdA 0 = ⊥) (hAS : ∀ n, BdA (n + 1) = LinearMap.range (δ n))
    (hB0 : BdB 0 = ⊥) (hBS : ∀ n, BdB (n + 1) = LinearMap.range (ε n))
    (n : ℕ) {c : β n → ZMod 2} (hc : c ∈ BdB n) :
    φ n c ∈ BdA n := by
  cases n with
  | zero =>
      rw [hB0, Submodule.mem_bot] at hc
      rw [hA0, Submodule.mem_bot, hc, map_zero]
  | succ m =>
      rw [hBS m] at hc
      obtain ⟨g, rfl⟩ := hc
      rw [hAS m]
      exact ⟨φ m g, (hφ m g).symm⟩

/-- **The induced map on cohomology.** -/
def Hmap (hφ : ∀ (n : ℕ) (c : β n → ZMod 2), φ (n + 1) (ε n c) = δ n (φ n c))
    (hA0 : BdA 0 = ⊥) (hAS : ∀ n, BdA (n + 1) = LinearMap.range (δ n))
    (hB0 : BdB 0 = ⊥) (hBS : ∀ n, BdB (n + 1) = LinearMap.range (ε n))
    (n : ℕ) : Cohomology ε BdB n →ₗ[ZMod 2] Cohomology δ BdA n :=
  Submodule.mapQ (coboundariesIn ε BdB n) (coboundariesIn δ BdA n) (cocyclesMap δ ε φ hφ n)
    (fun _ hz => map_mem_coboundaries δ ε BdA BdB φ hφ hA0 hAS hB0 hBS n hz)

/-! ## The duality theorem -/

variable (dA : ∀ n, FreeMod α (n + 1) →ₗ[ZMod 2] FreeMod α n)
  (dB : ∀ n, FreeMod β (n + 1) →ₗ[ZMod 2] FreeMod β n)

/-- Pairing a cocycle with a boundary gives zero. -/
theorem pairing_cocycle_boundary (hδ : ∀ n, δ n = dualOf (dA n)) (n : ℕ)
    {g : α n → ZMod 2} (hg : g ∈ cocycles δ n) (x : (α (n + 1) →₀ ZMod 2)) :
    Finsupp.linearCombination (ZMod 2) g (dA n x) = 0 := by
  rw [linearCombination_dualOf, ← hδ n]
  have : δ n g = 0 := hg
  rw [this]
  simp

/-- **A cocycle is a coboundary exactly when it annihilates the cycles.** -/
theorem mem_coboundaries_iff (hδ : ∀ n, δ n = dualOf (dA n))
    (hA0 : BdA 0 = ⊥) (hAS : ∀ n, BdA (n + 1) = LinearMap.range (δ n)) (n : ℕ)
    {g : α n → ZMod 2} (hg : g ∈ cocycles δ n) :
    g ∈ BdA n ↔
      ∀ z ∈ SpineNaiveHomology.cycles dA n,
        Finsupp.linearCombination (ZMod 2) g z = 0 := by
  cases n with
  | zero =>
      constructor
      · intro hgb z _
        rw [hA0, Submodule.mem_bot] at hgb
        subst hgb
        simp
      · intro hz
        have hg0 : g = 0 := by
          refine cochain_ext (h := (0 : α 0 → ZMod 2)) ?_
          intro x
          rw [hz x (by exact Submodule.mem_top)]
          simp
        rw [hA0, Submodule.mem_bot]
        exact hg0
  | succ m =>
      rw [hAS m, hδ m]
      constructor
      · rintro ⟨h, rfl⟩ z hz
        have hz' : dA m z = 0 := hz
        rw [← linearCombination_dualOf, hz']
        simp
      · intro hz
        -- `ℤ₂` is a field: a functional on a subspace extends to the whole space
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        -- the functional attached to `g` kills `ker (dA m)`, hence factors through the image
        set φg : Module.Dual (ZMod 2) (α (m + 1) →₀ ZMod 2) := freeDualEquiv _ g with hφg
        have hker : LinearMap.ker (dA m) ≤ LinearMap.ker φg := by
          intro x hx
          show φg x = 0
          rw [hφg, freeDualEquiv_apply]
          exact hz x hx
        set q := (LinearMap.ker (dA m)).liftQ φg hker with hq
        set ψ₀ := q ∘ₗ ((dA m).quotKerEquivRange.symm.toLinearMap) with hψ₀
        obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_extend (K := ZMod 2) (V := (α m →₀ ZMod 2))
          (V' := ZMod 2) ψ₀
        refine ⟨(freeDualEquiv (α m)).symm Ψ, ?_⟩
        refine cochain_ext ?_
        intro x
        rw [← linearCombination_dualOf]
        have hval : ∀ y : α m →₀ ZMod 2,
            Finsupp.linearCombination (ZMod 2) ((freeDualEquiv (α m)).symm Ψ) y = Ψ y := by
          intro y
          rw [← freeDualEquiv_apply, LinearEquiv.apply_symm_apply]
        rw [hval]
        have hmem : (dA m) x ∈ LinearMap.range (dA m) := ⟨x, rfl⟩
        have h1 : Ψ ((dA m) x) = ψ₀ ⟨(dA m) x, hmem⟩ := by
          have := congrFun (congrArg DFunLike.coe hΨ) (⟨(dA m) x, hmem⟩ :
            LinearMap.range (dA m))
          exact this
        rw [h1, hψ₀]
        show q ((dA m).quotKerEquivRange.symm ⟨(dA m) x, hmem⟩) = _
        rw [LinearMap.quotKerEquivRange_symm_apply_image (dA m) x hmem]
        show q (Submodule.Quotient.mk x) = _
        rw [hq]
        rw [Submodule.liftQ_apply, hφg, freeDualEquiv_apply]

/-- **Every functional annihilating the boundaries is realised by a cocycle.** -/
theorem exists_cocycle_of_functional (hδ : ∀ n, δ n = dualOf (dA n)) (n : ℕ)
    (χ : Module.Dual (ZMod 2) (α n →₀ ZMod 2)) (hχ : ∀ x, χ (dA n x) = 0) :
    ∃ g, g ∈ cocycles δ n ∧ ∀ x : α n →₀ ZMod 2,
      Finsupp.linearCombination (ZMod 2) g x = χ x := by
  refine ⟨(freeDualEquiv (α n)).symm χ, ?_, ?_⟩
  · show δ n ((freeDualEquiv (α n)).symm χ) = 0
    rw [hδ n]
    funext a
    rw [dualOf_apply]
    have : Finsupp.linearCombination (ZMod 2) ((freeDualEquiv (α n)).symm χ)
        (dA n (Finsupp.single a 1)) = χ (dA n (Finsupp.single a 1)) := by
      rw [← freeDualEquiv_apply, LinearEquiv.apply_symm_apply]
    rw [this, hχ]
    rfl
  · intro x
    rw [← freeDualEquiv_apply, LinearEquiv.apply_symm_apply]

variable (f : ∀ n, FreeMod α n →ₗ[ZMod 2] FreeMod β n)

set_option maxHeartbeats 1000000 in
/-- **The duality theorem.**  A chain map of free `ℤ₂`-complexes which is an isomorphism on
homology in every degree induces, by transposition, an isomorphism on the cohomology of the
dual function-type complexes in every degree. -/
theorem bijective_Hmap
    (hφ : ∀ (n : ℕ) (c : β n → ZMod 2), φ (n + 1) (ε n c) = δ n (φ n c))
    (hA0 : BdA 0 = ⊥) (hAS : ∀ n, BdA (n + 1) = LinearMap.range (δ n))
    (hB0 : BdB 0 = ⊥) (hBS : ∀ n, BdB (n + 1) = LinearMap.range (ε n))
    (hfc : ∀ n, (dB n).comp (f (n + 1)) = (f n).comp (dA n))
    (hdB : ∀ n, (dB n).comp (dB (n + 1)) = 0)
    (hδ : ∀ n, δ n = dualOf (dA n)) (hε : ∀ n, ε n = dualOf (dB n))
    (hφmap : ∀ n, φ n = dualOf (f n))
    (hbij : ∀ n, Function.Bijective (SpineNaiveHomology.homologyMap dA dB f hfc n))
    (n : ℕ) : Function.Bijective (Hmap δ ε BdA BdB φ hφ hA0 hAS hB0 hBS n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- the pairing of a cochain with a chain
  have hpairA : ∀ (g : α n → ZMod 2) (x : α n →₀ ZMod 2),
      freeDualEquiv (α n) g x = Finsupp.linearCombination (ZMod 2) g x :=
    fun g x => freeDualEquiv_apply g x
  constructor
  · -- **injectivity**
    refine (injective_iff_map_eq_zero _).2 ?_
    intro ξ hξ
    obtain ⟨z, rfl⟩ := cochainClass_surjective ε BdB n ξ
    have hξ' : φ n (z : β n → ZMod 2) ∈ BdA n := by
      have : Hmap δ ε BdA BdB φ hφ hA0 hAS hB0 hBS n (cochainClass ε BdB z)
          = cochainClass δ BdA (cocyclesMap δ ε φ hφ n z) := rfl
      rw [this, cochainClass_eq_zero_iff] at hξ
      exact hξ
    have hzero := (mem_coboundaries_iff δ BdA dA hδ hA0 hAS n
      (map_mem_cocycles δ ε φ hφ n z.2)).1 hξ'
    rw [cochainClass_eq_zero_iff]
    refine (mem_coboundaries_iff ε BdB dB hε hB0 hBS n z.2).2 ?_
    intro w hw
    -- lift the cycle `w` through the homology isomorphism
    obtain ⟨η, hη⟩ := (hbij n).2 (SpineNaiveHomology.cls dB ⟨w, hw⟩)
    obtain ⟨y, rfl⟩ := SpineNaiveHomology.cls_surjective dA n η
    rw [SpineNaiveHomology.homologyMap_cls, SpineNaiveHomology.cls_eq_iff] at hη
    obtain ⟨u, hu⟩ := hη
    have hw' : w = f n (y : α n →₀ ZMod 2) - dB n u := by
      rw [hu, SpineNaiveHomology.cyclesMap_coe]
      abel
    rw [hw', map_sub]
    have h1 : Finsupp.linearCombination (ZMod 2) (z : β n → ZMod 2)
        (f n (y : α n →₀ ZMod 2)) = 0 := by
      rw [linearCombination_dualOf, ← hφmap n]
      exact hzero _ y.2
    have h2 : Finsupp.linearCombination (ZMod 2) (z : β n → ZMod 2) (dB n u) = 0 := by
      rw [linearCombination_dualOf, ← hε n]
      have hz0 : ε n (z : β n → ZMod 2) = 0 := z.2
      rw [hz0]
      simp
    rw [h1, h2, sub_zero]
  · -- **surjectivity**
    intro ξ
    obtain ⟨g, rfl⟩ := cochainClass_surjective δ BdA n ξ
    -- the functional determined by the cocycle `g` on the homology of the source
    have hle : SpineNaiveHomology.boundariesIn dA n ≤
        LinearMap.ker ((freeDualEquiv (α n) (g : α n → ZMod 2)).comp
          (SpineNaiveHomology.cycles dA n).subtype) := by
      rintro ⟨x, hx⟩ hxb
      obtain ⟨t, ht⟩ := hxb
      have ht' : dA n t = x := ht
      show freeDualEquiv (α n) (g : α n → ZMod 2) x = 0
      rw [hpairA, ← ht']
      exact pairing_cocycle_boundary δ dA hδ n g.2 t
    set χA := Submodule.liftQ (SpineNaiveHomology.boundariesIn dA n)
      ((freeDualEquiv (α n) (g : α n → ZMod 2)).comp
        (SpineNaiveHomology.cycles dA n).subtype) hle with hχA
    set eH := LinearEquiv.ofBijective
      (SpineNaiveHomology.homologyMap dA dB f hfc n) (hbij n) with heH
    set ψ := (χA ∘ₗ eH.symm.toLinearMap) ∘ₗ
      (Submodule.mkQ (SpineNaiveHomology.boundariesIn dB n)) with hψ
    obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_extend (K := ZMod 2) (V := (β n →₀ ZMod 2))
      (V' := ZMod 2) ψ
    have hΨsub : ∀ (w : β n →₀ ZMod 2) (hw : w ∈ SpineNaiveHomology.cycles dB n),
        Ψ w = χA (eH.symm (SpineNaiveHomology.cls dB ⟨w, hw⟩)) :=
      fun w hw => congrFun (congrArg DFunLike.coe hΨ) (⟨w, hw⟩ :
        SpineNaiveHomology.cycles dB n)
    -- `Ψ` annihilates the boundaries, so it is a cocycle
    have hbd : ∀ u, Ψ (dB n u) = 0 := by
      intro u
      have hmem : dB n u ∈ SpineNaiveHomology.cycles dB n :=
        SpineNaiveHomology.boundaries_le_cycles dB hdB n ⟨u, rfl⟩
      have hcls : SpineNaiveHomology.cls dB ⟨dB n u, hmem⟩ = 0 :=
        (SpineNaiveHomology.cls_eq_zero_iff dB ⟨dB n u, hmem⟩).2 ⟨u, rfl⟩
      rw [hΨsub _ hmem, hcls, map_zero, map_zero]
    obtain ⟨h, hhc, hhval⟩ := exists_cocycle_of_functional ε dB hε n Ψ hbd
    refine ⟨cochainClass ε BdB ⟨h, hhc⟩, ?_⟩
    have hmapeq : Hmap δ ε BdA BdB φ hφ hA0 hAS hB0 hBS n (cochainClass ε BdB ⟨h, hhc⟩)
        = cochainClass δ BdA (cocyclesMap δ ε φ hφ n ⟨h, hhc⟩) := rfl
    rw [hmapeq]
    -- the two cocycles differ by a coboundary
    have hdiff : (φ n h - (g : α n → ZMod 2)) ∈ BdA n := by
      have hcoc : (φ n h - (g : α n → ZMod 2)) ∈ cocycles δ n :=
        Submodule.sub_mem _ (map_mem_cocycles δ ε φ hφ n hhc) g.2
      refine (mem_coboundaries_iff δ BdA dA hδ hA0 hAS n hcoc).2 ?_
      intro y hy
      have hy' : f n y ∈ SpineNaiveHomology.cycles dB n :=
        SpineNaiveHomology.mapsTo_cycles dA dB f hfc n y hy
      have hkey : Finsupp.linearCombination (ZMod 2) (φ n h) y
          = Finsupp.linearCombination (ZMod 2) (g : α n → ZMod 2) y := by
        have e1 : Finsupp.linearCombination (ZMod 2) (φ n h) y
            = Finsupp.linearCombination (ZMod 2) h (f n y) := by
          rw [linearCombination_dualOf, hφmap n]
        have e2 : Finsupp.linearCombination (ZMod 2) h (f n y) = Ψ (f n y) := hhval _
        have e3 : Ψ (f n y)
            = χA (eH.symm (SpineNaiveHomology.cls dB ⟨f n y, hy'⟩)) := hΨsub _ hy'
        have e4 : SpineNaiveHomology.cls dB ⟨f n y, hy'⟩
            = eH (SpineNaiveHomology.cls dA ⟨y, hy⟩) := rfl
        have e5 : χA (eH.symm (eH (SpineNaiveHomology.cls dA ⟨y, hy⟩)))
            = Finsupp.linearCombination (ZMod 2) (g : α n → ZMod 2) y := by
          rw [LinearEquiv.symm_apply_apply]
          show (freeDualEquiv (α n) (g : α n → ZMod 2)) y = _
          rw [hpairA]
        rw [e1, e2, e3, e4, e5]
      have hsub : Finsupp.linearCombination (ZMod 2) (φ n h - (g : α n → ZMod 2)) y = 0 := by
        have := congrArg (fun t : Module.Dual (ZMod 2) (α n →₀ ZMod 2) => t y)
          (map_sub (freeDualEquiv (α n)) (φ n h) (g : α n → ZMod 2))
        simp only [LinearMap.sub_apply] at this
        rw [hpairA] at this
        rw [this]
        show freeDualEquiv (α n) (φ n h) y - freeDualEquiv (α n) (g : α n → ZMod 2) y = 0
        rw [hpairA, hpairA, hkey, sub_self]
      exact hsub
    -- hence they have the same class
    have : cochainClass δ BdA (cocyclesMap δ ε φ hφ n ⟨h, hhc⟩) - cochainClass δ BdA g = 0 := by
      have hsub : cochainClass δ BdA (cocyclesMap δ ε φ hφ n ⟨h, hhc⟩) - cochainClass δ BdA g
          = cochainClass δ BdA (cocyclesMap δ ε φ hφ n ⟨h, hhc⟩ - g) := rfl
      rw [hsub, cochainClass_eq_zero_iff]
      exact hdiff
    exact sub_eq_zero.1 this

end SpineDualCohomology
