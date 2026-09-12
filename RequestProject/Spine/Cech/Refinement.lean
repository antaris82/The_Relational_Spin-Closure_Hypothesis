import RequestProject.Spine.Cech.Cohomology

/-!
# Task 6, WP11 (Čech half) : refinement pullback on fixed-cover Čech cohomology

A refinement of the family `U : ι → Set X` by the family `V : ι' → Set X` is an index map
`r : ι' → ι` with `V a ⊆ U (r a)` for every `a` — exactly the data of the Task-3 structure
`CechSpinLift.CoverRefinement` (whose fields are `r` and `le`), which is how it is fed in from
the Spin side.  Here the two ingredients are taken as plain parameters, so this file stays
independent of the Task-3 layer.

Because `V a ⊆ U (r a)`, a nonempty overlap of the refined family maps to a nonempty overlap of
the original one, giving a map of nerves `Nerve V n → Nerve U n`, hence a pullback of cochains
`r* : Čⁿ(U;ℤ₂) → Čⁿ(V;ℤ₂)`.  The pullback is a cochain map (`pull_d`), so it descends to

`r* : Ȟⁿ(U;ℤ₂) → Ȟⁿ(V;ℤ₂)`,

which is `CechZ2.Hmap`.  Functoriality in the refinement map is proved (`Hmap_id`,
`Hmap_comp`).  Nothing here is Spin-specific.
-/

namespace CechZ2

universe w t

variable {X : Type w} {ι ι' ι'' : Type t}

/-! ## The induced map of nerves -/

/-- The map of nerves induced by a refinement `r` with `V a ⊆ U (r a)`. -/
def nerveMap {V : ι' → Set X} {U : ι → Set X} {r : ι' → ι} (hr : ∀ a, V a ⊆ U (r a))
    {n : ℕ} (σ : Nerve V n) : Nerve U n :=
  ⟨r ∘ σ.idx, σ.nonempty.mono (by
    intro x hx
    rw [mem_inter_iff] at hx ⊢
    exact fun s => hr (σ.idx s) (hx s))⟩

@[simp] theorem nerveMap_idx {V : ι' → Set X} {U : ι → Set X} {r : ι' → ι}
    (hr : ∀ a, V a ⊆ U (r a)) {n : ℕ} (σ : Nerve V n) :
    (nerveMap hr σ).idx = r ∘ σ.idx := rfl

/-- The nerve map commutes with the face operators. -/
theorem nerveMap_face {V : ι' → Set X} {U : ι → Set X} {r : ι' → ι}
    (hr : ∀ a, V a ⊆ U (r a)) {n : ℕ} (t : Fin (n + 2)) (σ : Nerve V (n + 1)) :
    nerveMap hr (face t σ) = face t (nerveMap hr σ) := by
  apply Nerve.ext
  rfl

/-! ## Pullback of cochains -/

/-- The pullback `r*` of Čech cochains along a refinement, as a `ZMod 2`-linear map. -/
def pull {V : ι' → Set X} {U : ι → Set X} {r : ι' → ι} (hr : ∀ a, V a ⊆ U (r a))
    (n : ℕ) : Cochain U n →ₗ[ZMod 2] Cochain V n where
  toFun c := fun σ => c (nerveMap hr σ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pull_apply {V : ι' → Set X} {U : ι → Set X} {r : ι' → ι}
    (hr : ∀ a, V a ⊆ U (r a)) {n : ℕ} (c : Cochain U n) (σ : Nerve V n) :
    pull hr n c σ = c (nerveMap hr σ) := rfl

/-- **The pullback is a cochain map**: `r* ∘ δ = δ ∘ r*`. -/
theorem pull_d {V : ι' → Set X} {U : ι → Set X} {r : ι' → ι} (hr : ∀ a, V a ⊆ U (r a))
    (n : ℕ) (c : Cochain U n) :
    pull hr (n + 1) (d U n c) = d V n (pull hr n c) := by
  funext σ
  simp only [pull_apply, d_apply_nerve]
  exact Finset.sum_congr rfl fun t _ => by rw [nerveMap_face hr t σ]

theorem pull_mem_cocycles {V : ι' → Set X} {U : ι → Set X} {r : ι' → ι}
    (hr : ∀ a, V a ⊆ U (r a)) {n : ℕ} {c : Cochain U n} (hc : c ∈ cocycles U n) :
    pull hr n c ∈ cocycles V n := by
  have : d U n c = 0 := hc
  show d V n (pull hr n c) = 0
  rw [← pull_d hr n c, this, map_zero]

/-! ## The induced map on cohomology -/

/-- The pullback on cocycles. -/
def pullCocycles {V : ι' → Set X} {U : ι → Set X} {r : ι' → ι} (hr : ∀ a, V a ⊆ U (r a))
    (n : ℕ) : cocycles U n →ₗ[ZMod 2] cocycles V n where
  toFun z := ⟨pull hr n (z : Cochain U n), pull_mem_cocycles hr z.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pullCocycles_coe {V : ι' → Set X} {U : ι → Set X} {r : ι' → ι}
    (hr : ∀ a, V a ⊆ U (r a)) {n : ℕ} (z : cocycles U n) :
    (pullCocycles hr n z : Cochain V n) = pull hr n (z : Cochain U n) := rfl

/-- **The refinement pullback on Čech cohomology** `r* : Ȟⁿ(U;ℤ₂) → Ȟⁿ(V;ℤ₂)`. -/
def Hmap {V : ι' → Set X} {U : ι → Set X} {r : ι' → ι} (hr : ∀ a, V a ⊆ U (r a))
    (n : ℕ) : Cohomology U n →ₗ[ZMod 2] Cohomology V n := by
  refine Submodule.mapQ _ _ (pullCocycles hr n) ?_
  intro z hz
  cases n with
  | zero =>
      have : (z : Cochain U 0) ∈ (⊥ : Submodule (ZMod 2) (Cochain U 0)) := hz
      rw [Submodule.mem_bot] at this
      show (pullCocycles hr 0 z : Cochain V 0) ∈ coboundaries V 0
      rw [coboundaries_zero, Submodule.mem_bot]
      simp [pullCocycles_coe, this, map_zero]
  | succ n =>
      obtain ⟨b, hb⟩ : ∃ b : Cochain U n, d U n b = (z : Cochain U (n + 1)) := hz
      show (pullCocycles hr (n + 1) z : Cochain V (n + 1)) ∈ coboundaries V (n + 1)
      exact ⟨pull hr n b, by rw [← pull_d hr n b, hb, pullCocycles_coe]⟩

@[simp] theorem Hmap_mk {V : ι' → Set X} {U : ι → Set X} {r : ι' → ι}
    (hr : ∀ a, V a ⊆ U (r a)) {n : ℕ} (z : cocycles U n) :
    Hmap hr n (mk z) = mk (pullCocycles hr n z) := rfl

/-- Functoriality: the identity refinement induces the identity. -/
theorem Hmap_id {U : ι → Set X} (n : ℕ) :
    Hmap (V := U) (U := U) (r := _root_.id) (fun _ => subset_rfl) n = LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨z, rfl⟩ := mk_surjective z
  rfl

/-- Functoriality: a composite of refinements induces the composite pullback. -/
theorem Hmap_comp {W : ι'' → Set X} {V : ι' → Set X} {U : ι → Set X} {r : ι' → ι}
    {s : ι'' → ι'} (hr : ∀ a, V a ⊆ U (r a)) (hs : ∀ a, W a ⊆ V (s a)) (n : ℕ) :
    Hmap (r := r ∘ s) (fun a => (hs a).trans (hr (s a))) n
      = (Hmap hs n).comp (Hmap hr n) := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨z, rfl⟩ := mk_surjective z
  rfl

end CechZ2
