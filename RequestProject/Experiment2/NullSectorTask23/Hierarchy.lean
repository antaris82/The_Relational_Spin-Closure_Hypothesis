import RequestProject.Experiment2.NullSectorTask23.OldBridges

/-!
# Task 23, Package K: the minimal reconstruction hierarchy

**RECONSTRUCTION LAYER.**

Four levels of data are tested separately (item 81).

* **Level 1 — the visible carrier alone.**  Insufficient, and this is *proved*, not assumed:
  the product of the visible carrier with the two-element sign carrier is a surjection with
  two-element fibres onto the same base, and there is **no** continuous map from it to the
  certified carrier commuting with the projections.
* **Level 2 — visible carrier plus continuous local representatives.**  Still insufficient:
  the same local data (continuous local representatives on the same open cover) are carried
  by the product object, whose overlap transitions are all `+1`.
* **Level 3 — visible carrier, local representatives and the `{+1,-1}` overlap
  transitions.**  Sufficient: this is Package G.
* **Level 4 — the extended carrier.**  The two-valued data cannot reconstruct it: the fibre
  of the extended projection is infinite, whereas the core fibre has exactly two elements.

A negative control is proved as well (item 99): a continuous surjection with exactly
two-element fibres need not admit any local product decomposition.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask23

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21

open Quaternion Topology

/-! ## The core fibre -/

/-- **PACKAGE K.**  Every fibre of the certified projection has exactly two elements. -/
theorem core_fibre_two (g : GvisT) :
    ∃ u v : LiftT, u ≠ v ∧ pr u = g ∧ pr v = g ∧ ∀ w : LiftT, pr w = g → w = u ∨ w = v := by
  obtain ⟨u, hu⟩ := pr_surjective g
  refine ⟨u, sact Sgn.negOne u, fun h => sact_free u h.symm, hu, by rw [pr_sact, hu], ?_⟩
  intro w hw
  obtain ⟨e, rfl⟩ := (pr_eq_iff u w).1 (by rw [hu, hw])
  rcases Sgn.eq_one_or_negOne e with rfl | rfl
  · exact Or.inl (sact_one u)
  · exact Or.inr rfl

/-! ## Level 1 — the visible carrier alone -/

/-- The product object over the visible carrier. -/
abbrev TrivTotal : Type := GvisT × Sgn

theorem trivTotal_proj_surjective : Function.Surjective (Prod.fst : TrivTotal → GvisT) :=
  fun g => ⟨(g, 1), rfl⟩

theorem trivTotal_fibre_two (g : GvisT) :
    ∃ p q : TrivTotal, p ≠ q ∧ p.1 = g ∧ q.1 = g ∧
      ∀ r : TrivTotal, r.1 = g → r = p ∨ r = q := by
  refine ⟨(g, 1), (g, Sgn.negOne), ?_, rfl, rfl, ?_⟩
  · intro h
    exact Sgn.negOne_ne_one (congrArg Prod.snd h).symm
  · rintro ⟨g', e⟩ h
    have hg : g' = g := h
    subst hg
    rcases Sgn.eq_one_or_negOne e with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- **PACKAGE K, Level 1 (item 81), principal negative result.**  The visible carrier alone
does not reconstruct the certified carrier: there is no continuous map over the base from the
product object — which has the same base and the same two-element fibres — to the certified
carrier. -/
theorem level1_insufficient :
    ¬ ∃ f : TrivTotal → LiftT, Continuous f ∧ ∀ p : TrivTotal, pr (f p) = p.1 := by
  rintro ⟨f, hcont, hf⟩
  refine no_continuous_global_rep ⟨fun g => f (g, 1), ?_, fun g => ?_⟩
  · exact hcont.comp (continuous_id.prodMk continuous_const)
  · exact hf (g, 1)

/-! ## Level 2 — adding the local representatives -/

/-- **PACKAGE K, Level 2.**  The product object carries continuous local representatives on
exactly the same open cover, and all of its overlap transitions are `+1`. -/
theorem trivTotal_local_sections :
    ∃ t : ∀ i : Fin 4, ↥(Vset i) → TrivTotal,
      (∀ i, Continuous (t i)) ∧ (∀ i g, (t i g).1 = (g : GvisT)) ∧
      (∀ (i j : Fin 4) (g : GvisT) (hi : g ∈ Vset i) (hj : g ∈ Vset j),
        t j ⟨g, hj⟩ = t i ⟨g, hi⟩) := by
  refine ⟨fun _ g => ((g : GvisT), 1), fun i => ?_, fun i g => rfl, fun i j g hi hj => rfl⟩
  exact continuous_subtype_val.prodMk continuous_const

/-- **PACKAGE K, Level 2 (item 81), principal negative result.**  Continuous local
representatives on the chosen cover do not reconstruct the certified carrier either: the
product object has them, with all transitions `+1`, and is still not mapped continuously over
the base into the certified carrier.  What distinguishes the two objects is exactly the
overlap sign data. -/
theorem level2_insufficient :
    (∃ t : ∀ i : Fin 4, ↥(Vset i) → TrivTotal,
      (∀ i, Continuous (t i)) ∧ (∀ i g, (t i g).1 = (g : GvisT)) ∧
      (∀ (i j : Fin 4) (g : GvisT) (hi : g ∈ Vset i) (hj : g ∈ Vset j),
        t j ⟨g, hj⟩ = t i ⟨g, hi⟩)) ∧
    ¬ ∃ f : TrivTotal → LiftT, Continuous f ∧ ∀ p : TrivTotal, pr (f p) = p.1 :=
  ⟨trivTotal_local_sections, level1_insufficient⟩

/-! ## Level 3 — the sign data suffice -/

/-- **PACKAGE K, Level 3 (item 82), principal.**  The visible carrier, the continuous local
representatives and the `{+1,-1}` overlap transitions reconstruct the certified carrier
exactly, together with its projection.  This is the minimal sufficient level. -/
theorem level3_sufficient :
    ∃ e : LiftLocal ≃ₜ LiftT, ∀ z : LiftLocal, pr (e z) = prLocal z :=
  ⟨liftLocalHomeo, fun z => pr_toLift z⟩

/-! ## Level 4 — the extended carrier -/

theorem zexp_mem_LiftZ (t : ℝ) : zexp 1 0 t ∈ LiftZ :=
  CUnit_subset_LiftZ (kernel_full_continuum.2.2 t).1

/-- **PACKAGE K (item 83), principal.**  The fibre of the extended projection is infinite:
no two-valued datum can reconstruct the extended carrier. -/
theorem extended_fibre_infinite :
    Set.Infinite {z : W | z ∈ LiftZ ∧ proj z = LinearMap.id} := by
  refine Set.infinite_of_injective_forall_mem (f := fun t : ℝ => zexp 1 0 t) ?_ ?_
  · exact kernel_full_continuum.2.1
  · intro t
    exact ⟨zexp_mem_LiftZ t, (kernel_full_continuum.2.2 t).2⟩

/-- **PACKAGE K (item 83).**  The exact contrast: the core fibre has two elements, the
extended fibre is infinite. -/
theorem core_two_extended_infinite :
    (∀ g : GvisT, ∃ u v : LiftT, u ≠ v ∧ pr u = g ∧ pr v = g ∧
        ∀ w : LiftT, pr w = g → w = u ∨ w = v) ∧
      Set.Infinite {z : W | z ∈ LiftZ ∧ proj z = LinearMap.id} :=
  ⟨core_fibre_two, extended_fibre_infinite⟩

/-! ## Negative control (item 99): a two-element fibre alone is not enough -/

/-- A total object with exactly two-element fibres over the reals, whose topology is pulled
back from the base. -/
def BadTotal : Type := ℝ × Bool

instance : TopologicalSpace BadTotal :=
  TopologicalSpace.induced (Prod.fst : ℝ × Bool → ℝ) inferInstance

/-- Its projection. -/
def badProj (z : BadTotal) : ℝ := (z : ℝ × Bool).1

theorem continuous_badProj : Continuous badProj := continuous_induced_dom

theorem badProj_surjective : Function.Surjective badProj := fun x => ⟨(x, true), rfl⟩

theorem badProj_fibre_two (x : ℝ) :
    ∀ z : BadTotal, badProj z = x → z = ((x, true) : ℝ × Bool) ∨ z = ((x, false) : ℝ × Bool) := by
  rintro ⟨y, b⟩ h
  have hy : y = x := h
  subst hy
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **PACKAGE K (item 99), negative control.**  A continuous surjection with exactly
two-element fibres need not have any local product decomposition: for this object the two
points of a fibre cannot be separated by any open set, so no map to a product with the
discrete two-element carrier can be a homeomorphism over the base. -/
theorem no_local_product_of_two_element_fibre :
    ¬ ∃ e : BadTotal ≃ₜ (ℝ × Sgn), ∀ z : BadTotal, (e z).1 = badProj z := by
  rintro ⟨e, he⟩
  have hopenA : IsOpen {p : ℝ × Sgn | p.2 = 1} := by
    have h1 : IsOpen ({(1 : Sgn)} : Set Sgn) := isOpen_discrete _
    exact h1.preimage continuous_snd
  have hopen : IsOpen (e ⁻¹' {p : ℝ × Sgn | p.2 = 1}) := hopenA.preimage e.continuous
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.1 hopen
  set z₁ : BadTotal := ((0, true) : ℝ × Bool) with hz₁
  set z₂ : BadTotal := ((0, false) : ℝ × Bool) with hz₂
  have hne : e z₁ ≠ e z₂ := by
    intro h
    have : z₁ = z₂ := e.injective h
    exact Bool.noConfusion (congrArg Prod.snd this)
  have hfst : (e z₁).1 = (e z₂).1 := by
    rw [he z₁, he z₂]
    rfl
  have hmem : ∀ z : BadTotal, z ∈ e ⁻¹' {p : ℝ × Sgn | p.2 = 1} ↔ (z : ℝ × Bool).1 ∈ V := by
    intro z
    rw [← hVeq]
    exact Iff.rfl
  have hsame : (z₁ ∈ e ⁻¹' {p : ℝ × Sgn | p.2 = 1}) ↔ (z₂ ∈ e ⁻¹' {p : ℝ × Sgn | p.2 = 1}) := by
    rw [hmem z₁, hmem z₂]
  have hsnd : (e z₁).2 ≠ (e z₂).2 := by
    intro h
    exact hne (Prod.ext hfst h)
  rcases Sgn.eq_one_or_negOne (e z₁).2 with h1 | h1
  · have hz1mem : z₁ ∈ e ⁻¹' {p : ℝ × Sgn | p.2 = 1} := h1
    have hz2mem : z₂ ∈ e ⁻¹' {p : ℝ × Sgn | p.2 = 1} := hsame.1 hz1mem
    exact hsnd (by rw [h1]; exact hz2mem.symm)
  · have hz1notmem : z₁ ∉ e ⁻¹' {p : ℝ × Sgn | p.2 = 1} := by
      intro hcon
      have : (e z₁).2 = 1 := hcon
      rw [h1] at this
      exact Sgn.negOne_ne_one this
    have hz2notmem : z₂ ∉ e ⁻¹' {p : ℝ × Sgn | p.2 = 1} := fun hcon => hz1notmem (hsame.2 hcon)
    have h2 : (e z₂).2 = Sgn.negOne := by
      rcases Sgn.eq_one_or_negOne (e z₂).2 with h2 | h2
      · exact absurd h2 (fun hh => hz2notmem hh)
      · exact h2
    exact hsnd (by rw [h1, h2])

end NullSectorTask23
