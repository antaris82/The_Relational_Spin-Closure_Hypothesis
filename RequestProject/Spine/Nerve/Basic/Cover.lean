import RequestProject.Spine.GoodCover.NerveIdentification

/-!
# Task 9, WP2 : the canonical cover nerve as a **full simplicial set**

Task 6 built the fixed-cover Čech complex on the type

`CechZ2.Nerve U n = {σ : Fin (n+1) → ι // (⋂ s, U (σ s)).Nonempty}`

of ordered `(n+1)`-tuples of cover indices with nonempty total intersection, and Task 7
exhibited this family, with the face operators `CechZ2.face`, as a *presimplicial* set
`NerveZ2.coverNerve U` (faces only, **no degeneracies**).

This module upgrades that presimplicial set to a genuine simplicial set

`NerveGeom.coverNerveSSet U : SSet.{u}`,

i.e. an actual functor `SimplexCategoryᵒᵖ ⥤ Type u`.

## The construction

The key observation is that the nerve condition is *monotone under reindexing*: for **any**
map `f : Fin (m+1) → Fin (n+1)` one has `⋂ s, U (σ s) ⊆ ⋂ s, U (σ (f s))`
(`CechZ2.inter_subset_comp`), so a nonempty total intersection stays nonempty.  Hence the
assignment

`σ ↦ σ ∘ f`

is defined for every morphism of the simplex category, not just for the cofaces, and it is
strictly functorial (composition of functions).  So the nerve *is* a simplicial set, on the
nose, with

* `n`-simplices = ordered `(n+1)`-tuples of indices with nonempty intersection,
  **repetitions of vertices explicitly allowed** — this is what makes degeneracies exist;
* face maps `dᵢ` = deletion of the vertex in position `i` (`CechZ2.face`, precomposition with
  `Fin.succAbove i`);
* degeneracy maps `sᵢ` = **repetition of the vertex in position `i`**
  (`NerveGeom.degen`, precomposition with `Fin.predAbove i`).

Because the structure is a genuine functor, **all** simplicial identities are supplied by
Mathlib's `CategoryTheory.SimplicialObject` API (`δ_comp_δ`, `σ_comp_σ`, `δ_comp_σ_self`,
`δ_comp_σ_succ`, `δ_comp_σ_of_le`, `δ_comp_σ_of_gt`); they are *restated* below in the
concrete nerve notation, each proved from the functorial structure rather than by hand.

## Relation to the earlier representation

`coverNerveSSet_obj` and `coverNerveSSet_delta` prove that the simplices and the faces of the
new simplicial set are **definitionally** those of the Task-7 presimplicial set
`NerveZ2.coverNerve U`, hence those of the Task-6 Čech complex.  Nothing is replaced.
-/

noncomputable section

namespace NerveGeom

open CategoryTheory Opposite CechZ2 SimplexCategory

universe w u

variable {X : Type w} {ι : Type u}

/-! ## Reindexing of nerve simplices along an arbitrary map -/

/-- Reindex a nerve simplex along an **arbitrary** map of finite index sets.  Deleting,
repeating or permuting vertices can only enlarge the total intersection, so the result is
again a nerve simplex.  This is the single construction from which both face and degeneracy
operators are obtained. -/
def reindex {U : ι → Set X} {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (σ : Nerve U n) :
    Nerve U m :=
  ⟨σ.idx ∘ f, σ.nonempty.mono (inter_subset_comp U σ.idx f)⟩

@[simp] theorem reindex_idx {U : ι → Set X} {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (σ : Nerve U n) : (reindex f σ).idx = σ.idx ∘ f := rfl

theorem reindex_id {U : ι → Set X} {n : ℕ} (σ : Nerve U n) : reindex id σ = σ := rfl

theorem reindex_comp {U : ι → Set X} {m n k : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (g : Fin (n + 1) → Fin (k + 1)) (σ : Nerve U k) :
    reindex f (reindex g σ) = reindex (g ∘ f) σ := rfl

/-- The face operator of Task 6/7 is reindexing along `Fin.succAbove`. -/
theorem face_eq_reindex {U : ι → Set X} {n : ℕ} (t : Fin (n + 2)) (σ : Nerve U (n + 1)) :
    CechZ2.face t σ = reindex t.succAbove σ := rfl

/-! ## Degeneracies : repetition of a vertex -/

/-- The **degeneracy operator** of the cover nerve: `degen i σ` repeats the vertex in
position `i` of `σ`.  Formally it is reindexing along `Fin.predAbove i`. -/
def degen {U : ι → Set X} {n : ℕ} (i : Fin (n + 1)) (σ : Nerve U n) : Nerve U (n + 1) :=
  reindex i.predAbove σ

@[simp] theorem degen_idx {U : ι → Set X} {n : ℕ} (i : Fin (n + 1)) (σ : Nerve U n) :
    (degen i σ).idx = σ.idx ∘ i.predAbove := rfl

/-- **Degeneracies repeat a vertex, first copy.** -/
@[simp] theorem degen_idx_castSucc {U : ι → Set X} {n : ℕ} (i : Fin (n + 1)) (σ : Nerve U n) :
    (degen i σ).idx i.castSucc = σ.idx i := by
  simp [degen, Fin.predAbove]

/-- **Degeneracies repeat a vertex, second copy.** -/
@[simp] theorem degen_idx_succ {U : ι → Set X} {n : ℕ} (i : Fin (n + 1)) (σ : Nerve U n) :
    (degen i σ).idx i.succ = σ.idx i := by
  simp [degen, Fin.predAbove]

/-- The two adjacent vertices created by `degen i` really are equal: this is the precise sense
in which "repeated vertices" are the image of the degeneracy operators. -/
theorem degen_repeats_vertex {U : ι → Set X} {n : ℕ} (i : Fin (n + 1)) (σ : Nerve U n) :
    (degen i σ).idx i.castSucc = (degen i σ).idx i.succ := by
  simp

/-! ## The simplicial set -/

/-- **The canonical cover nerve as a simplicial set** `N(𝓤) : Δᵒᵖ ⥤ Set`.

An `n`-simplex is an ordered `(n+1)`-tuple of cover indices whose total intersection is
nonempty; repetitions are allowed.  A morphism `[m] ⟶ [n]` of the simplex category acts by
precomposition of the index tuple with the underlying monotone map. -/
def coverNerveSSet (U : ι → Set X) : SSet.{u} where
  obj k := Nerve U k.unop.len
  map {_ _} f σ := reindex (fun s => f.unop.toOrderHom s) σ
  map_id _ := by funext σ; apply Nerve.ext; rfl
  map_comp _ _ := by funext σ; apply Nerve.ext; rfl

/-- The `n`-simplices of the simplicial nerve are exactly the Task-6/Task-7 nerve simplices. -/
theorem coverNerveSSet_obj (U : ι → Set X) (n : ℕ) :
    (coverNerveSSet U).obj (op (SimplexCategory.mk n)) = Nerve U n := rfl

theorem coverNerveSSet_map (U : ι → Set X) {k l : SimplexCategoryᵒᵖ} (f : k ⟶ l)
    (σ : (coverNerveSSet U).obj k) :
    (coverNerveSSet U).map f σ = reindex (fun s => f.unop.toOrderHom s) σ := rfl

/-- **The simplicial face maps are the Task-6 Čech face operators**, definitionally. -/
theorem coverNerveSSet_delta (U : ι → Set X) {n : ℕ} (i : Fin (n + 2))
    (σ : Nerve U (n + 1)) : (coverNerveSSet U).δ i σ = CechZ2.face i σ := rfl

/-- **The simplicial degeneracy maps are vertex repetition**, definitionally. -/
theorem coverNerveSSet_sigma (U : ι → Set X) {n : ℕ} (i : Fin (n + 1)) (σ : Nerve U n) :
    (coverNerveSSet U).σ i σ = degen i σ := rfl

/-- The simplicial set presents the Task-7 presimplicial nerve: same simplices, same faces. -/
theorem coverNerveSSet_presimplicial (U : ι → Set X) {n : ℕ} (i : Fin (n + 2))
    (σ : Nerve U (n + 1)) :
    (coverNerveSSet U).δ i σ = (NerveZ2.coverNerve U).face i σ := rfl

/-! ## The simplicial identities

All of them are consequences of functoriality: they are Mathlib's identities for an arbitrary
simplicial object, applied to `coverNerveSSet U` and read off in the concrete notation. -/

variable (U : ι → Set X)

/-- `dᵢ ∘ d_{j+1} = dⱼ ∘ d_{i}` for `i ≤ j` (the presimplicial identity). -/
theorem face_face_comm {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) (σ : Nerve U (n + 2)) :
    CechZ2.face i (CechZ2.face j.succ σ) = CechZ2.face j (CechZ2.face i.castSucc σ) :=
  congrFun (SimplicialObject.δ_comp_δ (coverNerveSSet U) h) σ

/-- `sᵢ ∘ sⱼ = s_{j+1} ∘ sᵢ` for `i ≤ j`, in the composition order of Mathlib's
`SimplicialObject.σ_comp_σ`. -/
theorem degen_degen_comm {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) (σ : Nerve U n) :
    degen i.castSucc (degen j σ) = degen j.succ (degen i σ) :=
  congrFun (SimplicialObject.σ_comp_σ (coverNerveSSet U) h) σ

/-- `d_{i} ∘ sᵢ = id` (first mixed identity). -/
theorem face_castSucc_degen {n : ℕ} (i : Fin (n + 1)) (σ : Nerve U n) :
    CechZ2.face i.castSucc (degen i σ) = σ :=
  congrFun (SimplicialObject.δ_comp_σ_self (coverNerveSSet U)) σ

/-- `d_{i+1} ∘ sᵢ = id` (second mixed identity). -/
theorem face_succ_degen {n : ℕ} (i : Fin (n + 1)) (σ : Nerve U n) :
    CechZ2.face i.succ (degen i σ) = σ :=
  congrFun (SimplicialObject.δ_comp_σ_succ (coverNerveSSet U)) σ

/-- `d_{i} ∘ s_{j} = s_{j-1} ∘ d_{i}` in the low range (`i ≤ j`). -/
theorem face_degen_of_le {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (h : i ≤ j.castSucc)
    (σ : Nerve U (n + 1)) :
    CechZ2.face i.castSucc (degen j.succ σ) = degen j (CechZ2.face i σ) :=
  congrFun (SimplicialObject.δ_comp_σ_of_le (coverNerveSSet U) h) σ

/-- `d_{i} ∘ s_{j} = s_{j} ∘ d_{i-1}` in the high range (`j < i`). -/
theorem face_degen_of_gt {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (h : j.castSucc < i)
    (σ : Nerve U (n + 1)) :
    CechZ2.face i.succ (degen j.castSucc σ) = degen j (CechZ2.face i σ) :=
  congrFun (SimplicialObject.δ_comp_σ_of_gt (coverNerveSSet U) h) σ

end NerveGeom
