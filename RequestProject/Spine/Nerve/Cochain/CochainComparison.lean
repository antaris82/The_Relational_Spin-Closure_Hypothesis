import RequestProject.Spine.Nerve.Basic.Cover

/-!
# Task 9, WP3 : the full simplicial nerve and the existing Task-6 cochain complex

Task 6 built `CechZ2.Cochain U n = CechZ2.Nerve U n → ZMod 2` with the coboundary
`δc(σ) = ∑ₜ c(dₜ σ)`, and Task 7 proved that this is the simplicial cochain complex of the
*presimplicial* nerve `NerveZ2.coverNerve U`.

This module answers the WP3 audit question and connects the new full simplicial set of WP2 to
that existing complex **without replacing it**.

## Which convention did Task 6 use?

`CechZ2.Nerve U n` is the type of **all ordered `(n+1)`-tuples** of indices with nonempty
total intersection.  In particular:

* it is *not* restricted to strictly increasing tuples (there is no order on `ι` at all);
* it is *not* restricted to injective tuples;
* repeated vertices are allowed, and the degenerate simplices of WP2 are literally elements of
  it (`degenerate_mem`, `isDegenerate_degen`).

So Task 6 used the **unnormalized** simplicial cochain complex of the nerve.  Consequently
**no normalization bridge is needed**: the cochain carrier of the full simplicial set of WP2
is, degreewise and definitionally, the Task-6 carrier.  The relevant theorem is
`underlyingPresimplicial_coverNerveSSet`, which states that forgetting the degeneracies of
`NerveGeom.coverNerveSSet U` returns *exactly* the Task-7 presimplicial set
`NerveZ2.coverNerve U` — the same simplices, the same faces, hence the same cochains, the
same coboundary, the same cocycles, the same coboundaries and the same cohomology.

Combined with the Task-7 identity `NerveZ2.cechCohomologyEquiv` this gives the WP3 endpoint

```
   Ȟⁿ(𝓤;ℤ₂)  =  Hⁿ_simp(N(𝓤);ℤ₂)
```

for the *full* simplicial nerve, with the identity as the comparison map
(`cechCohomologyEquivSSet`).

## Degenerate simplices, explicitly

`NerveGeom.IsDegenerate σ` says that two *adjacent* vertices of `σ` coincide.  The theorem
`isDegenerate_iff_exists_degen` proves that this happens exactly when `σ` is in the image of
one of the degeneracy operators of WP2, so the simplicial notion of degeneracy and the
combinatorial notion "a repeated adjacent index" agree for the cover nerve.  This is the
precise sense in which "the definition makes explicit how repeated vertices are handled".
-/

noncomputable section

namespace NerveGeom

open CategoryTheory Opposite CechZ2 SimplexCategory

universe w u

variable {X : Type w} {ι : Type u}

/-! ## Forgetting the degeneracies of a simplicial set -/

/-- The presimplicial set underlying a simplicial set: same simplices, faces given by the
simplicial face maps.  The presimplicial identity is `SimplicialObject.δ_comp_δ`. -/
def underlyingPresimplicial (S : SSet.{u}) : NerveZ2.Presimplicial.{u} where
  obj n := S.obj (op (SimplexCategory.mk n))
  face t x := S.δ t x
  face_comm _ _ h x := congrFun (SimplicialObject.δ_comp_δ S h) x

/-- **WP3, structural.**  Forgetting the degeneracies of the full simplicial cover nerve
returns *exactly* the Task-7 presimplicial cover nerve — not an isomorphic copy of it. -/
theorem underlyingPresimplicial_coverNerveSSet (U : ι → Set X) :
    underlyingPresimplicial (coverNerveSSet U) = NerveZ2.coverNerve U := rfl

/-! ## The cochain complexes agree, degreewise and definitionally -/

/-- The simplicial `ℤ₂`-cochains of the full nerve are the Task-6 Čech cochains. -/
theorem cochain_eq (U : ι → Set X) (n : ℕ) :
    (underlyingPresimplicial (coverNerveSSet U)).Cochain n = CechZ2.Cochain U n := rfl

/-- The coboundaries agree, as linear maps. -/
theorem d_eq (U : ι → Set X) (n : ℕ) :
    (underlyingPresimplicial (coverNerveSSet U)).d n = CechZ2.d U n := rfl

/-- The cocycle submodules agree. -/
theorem cocycles_eq (U : ι → Set X) (n : ℕ) :
    (underlyingPresimplicial (coverNerveSSet U)).cocycles n = CechZ2.cocycles U n := rfl

/-- The coboundary submodules agree. -/
theorem coboundaries_eq (U : ι → Set X) (n : ℕ) :
    (underlyingPresimplicial (coverNerveSSet U)).coboundaries n = CechZ2.coboundaries U n := by
  cases n <;> rfl

/-- **WP3, principal.**  Fixed-cover Čech cohomology of `𝓤` *is* the simplicial cohomology of
the **full simplicial** nerve of `𝓤`, the comparison being the identity.  This is the Task-7
theorem, unchanged; no parallel theory is created. -/
def cechCohomologyEquivSSet (U : ι → Set X) (n : ℕ) :
    (underlyingPresimplicial (coverNerveSSet U)).Cohomology n ≃ₗ[ZMod 2]
      CechZ2.Cohomology U n :=
  NerveZ2.cechCohomologyEquiv U n

@[simp] theorem cechCohomologyEquivSSet_apply (U : ι → Set X) (n : ℕ)
    (q : (underlyingPresimplicial (coverNerveSSet U)).Cohomology n) :
    cechCohomologyEquivSSet U n q = NerveZ2.cechCohomologyEquiv U n q := rfl

/-! ## Degenerate simplices of the cover nerve -/

/-- A nerve simplex is **degenerate** when two adjacent vertices coincide. -/
def IsDegenerate {U : ι → Set X} {n : ℕ} (σ : Nerve U (n + 1)) : Prop :=
  ∃ i : Fin (n + 1), σ.idx i.castSucc = σ.idx i.succ

/-- Every simplex in the image of a degeneracy operator is degenerate. -/
theorem isDegenerate_degen {U : ι → Set X} {n : ℕ} (i : Fin (n + 1)) (σ : Nerve U n) :
    IsDegenerate (degen i σ) :=
  ⟨i, degen_repeats_vertex i σ⟩

/-- Conversely, a simplex with a repeated adjacent vertex *is* a degeneracy: it is
`sᵢ` applied to its own `i`-th face. -/
theorem degen_face_of_repeat {U : ι → Set X} {n : ℕ} {σ : Nerve U (n + 1)} {i : Fin (n + 1)}
    (h : σ.idx i.castSucc = σ.idx i.succ) :
    degen i (CechZ2.face i.castSucc σ) = σ := by
  apply Nerve.ext
  funext x
  show σ.idx (i.castSucc.succAbove (i.predAbove x)) = σ.idx x
  rcases lt_or_ge (i.castSucc) x with hx | hx
  · have hpred : (i.predAbove x : ℕ) = (x : ℕ) - 1 := by
      simp [Fin.predAbove, hx]
    have hx1 : 1 ≤ (x : ℕ) := by
      have := hx
      simp only [Fin.lt_def, Fin.val_castSucc] at this
      omega
    have : i.castSucc.succAbove (i.predAbove x) = x := by
      apply Fin.ext
      have hnot : ¬ ((i.predAbove x).castSucc < i.castSucc) := by
        simp only [Fin.lt_def, Fin.val_castSucc, hpred]
        have := hx
        simp only [Fin.lt_def, Fin.val_castSucc] at this
        omega
      simp only [Fin.succAbove, hnot, if_false, Fin.val_succ, hpred]
      omega
    rw [this]
  · rcases eq_or_lt_of_le hx with heq | hlt
    · -- `x = i.castSucc`: the composite lands on `i.succ`, and the two values agree
      subst heq
      have hpred : i.predAbove i.castSucc = i := by
        apply Fin.ext
        simp [Fin.predAbove]
      rw [hpred]
      have hsa : i.castSucc.succAbove i = i.succ := by
        apply Fin.ext
        simp [Fin.succAbove]
      rw [hsa]
      exact h.symm
    · have hpred : (i.predAbove x : ℕ) = (x : ℕ) := by
        have : ¬ (i.castSucc < x) := not_lt.mpr hx
        simp [Fin.predAbove, this]
      have : i.castSucc.succAbove (i.predAbove x) = x := by
        apply Fin.ext
        have hlt' : ((i.predAbove x).castSucc : ℕ) < (i.castSucc : ℕ) := by
          rw [Fin.val_castSucc, hpred]
          have := hlt
          simp only [Fin.lt_def, Fin.val_castSucc] at this
          omega
        have hlt'' : (i.predAbove x).castSucc < i.castSucc := hlt'
        simp only [Fin.succAbove, hlt'', if_true, Fin.val_castSucc, hpred]
      rw [this]

/-- **The combinatorial and the simplicial notions of degeneracy agree** for the cover
nerve: a simplex has a repeated adjacent vertex iff it is in the image of a degeneracy. -/
theorem isDegenerate_iff_exists_degen {U : ι → Set X} {n : ℕ} (σ : Nerve U (n + 1)) :
    IsDegenerate σ ↔ ∃ (i : Fin (n + 1)) (τ : Nerve U n), degen i τ = σ := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, CechZ2.face i.castSucc σ, degen_face_of_repeat hi⟩
  · rintro ⟨i, τ, rfl⟩
    exact isDegenerate_degen i τ

/-- **The Task-6 complex is the unnormalized one.**  The normalized (nondegenerate) cochains
form the submodule of cochains vanishing on every degeneracy; the Task-6 carrier is the *full*
function type, so the two agree only when there are no degenerate simplices at all. -/
def normalizedCochains (U : ι → Set X) (n : ℕ) :
    Submodule (ZMod 2) (CechZ2.Cochain U (n + 1)) where
  carrier := {c | ∀ (i : Fin (n + 1)) (σ : Nerve U n), c (degen i σ) = 0}
  add_mem' hc hd i σ := by simp [hc i σ, hd i σ]
  zero_mem' _ _ := rfl
  smul_mem' r _ hc i σ := by simp [hc i σ]

/-- The Task-6 cochain complex is *not* the normalized one: as soon as the nerve has a
degenerate simplex, the constant cochain `1` is not normalized. -/
theorem one_not_mem_normalizedCochains {U : ι → Set X} {n : ℕ} (i : Fin (n + 1))
    (σ : Nerve U n) : (fun _ => 1 : CechZ2.Cochain U (n + 1)) ∉ normalizedCochains U n := by
  intro h
  exact one_ne_zero (h i σ)

end NerveGeom
