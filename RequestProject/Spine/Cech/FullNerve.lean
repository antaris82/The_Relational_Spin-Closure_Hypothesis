import RequestProject.Spine.Cech.Cohomology

/-!
# Spine / Cech : vanishing of `Ȟ¹` on a cover whose nerve is a full simplex

A small addition to the existing fixed-cover Čech `ℤ₂`-machinery, needed by the Task-32
manifold-emergence layer and stated for an arbitrary indexed family `U : ι → Set X`.

If **every** finite tuple of indices has nonempty overlap — the nerve of `U` is the full
simplex on `ι` — and `ι` is inhabited, then `Ȟ¹(U;ℤ₂) = 0`: a 1-cocycle `z` is the coboundary
of the 0-cochain `i ↦ z(i₀ i)` for any fixed base index `i₀`.  This is the elementary
"cone contraction" of a simplex, in the one degree in which it is used.

No Spin, group, projection or manifold notion occurs here; the module extends only
`RequestProject.Spine.Cech.Cohomology`.
-/

namespace CechZ2

universe w t

variable {X : Type w} {ι : Type t} {U : ι → Set X}

/-- **NEWLY DEFINED (Task 32).**  The nerve of `U` is *full* when every finite tuple of
indices has nonempty overlap.  It holds, in particular, when every member of the family is
the whole of a nonempty `X`. -/
def FullNerve (U : ι → Set X) : Prop := ∀ (n : ℕ) (σ : Fin n → ι), (inter U σ).Nonempty

theorem fullNerve_of_eq_univ [Nonempty X] (h : ∀ i, U i = Set.univ) : FullNerve U := by
  intro n σ
  refine ⟨Classical.arbitrary X, ?_⟩
  rw [mem_inter_iff]
  intro s
  rw [h (σ s)]
  trivial

/-- **DERIVED (Task 32), principal.**  On a cover with a full nerve and an inhabited index
type the first fixed-cover Čech `ℤ₂`-cohomology vanishes. -/
theorem cohomology_one_eq_zero_of_fullNerve (i₀ : ι) (hfull : FullNerve U) (h : H1 U) :
    h = 0 := by
  obtain ⟨z, rfl⟩ := mk_surjective h
  rw [mk_eq_zero_iff_exists]
  refine ⟨fun τ => (z : Cochain U 1) ⟨![i₀, τ.idx 0], hfull 2 _⟩, ?_⟩
  funext σ
  set a := σ.idx 0 with ha
  set b := σ.idx 1 with hb
  have hz : d U 1 (z : Cochain U 1) = 0 := z.2
  have hzσ := congrFun hz (⟨![i₀, a, b], hfull 3 _⟩ : Nerve U 2)
  have e0 : face 0 (⟨![i₀, a, b], hfull 3 _⟩ : Nerve U 2) = σ := by
    refine Subtype.ext ?_
    funext u
    fin_cases u <;> simp [face, Nerve.idx, ha, hb]
  have e1 : face 1 (⟨![i₀, a, b], hfull 3 _⟩ : Nerve U 2)
      = (⟨![i₀, b], hfull 2 _⟩ : Nerve U 1) := by
    refine Subtype.ext ?_
    funext u
    fin_cases u <;> simp [face, Nerve.idx, Fin.succAbove]
  have e2 : face 2 (⟨![i₀, a, b], hfull 3 _⟩ : Nerve U 2)
      = (⟨![i₀, a], hfull 2 _⟩ : Nerve U 1) := by
    refine Subtype.ext ?_
    funext u
    fin_cases u <;> simp [face, Nerve.idx, Fin.succAbove]
  have hsum : (z : Cochain U 1) σ + (z : Cochain U 1) ⟨![i₀, b], hfull 2 _⟩
      + (z : Cochain U 1) ⟨![i₀, a], hfull 2 _⟩ = 0 := by
    have : (∑ t : Fin 3, (z : Cochain U 1)
        (face t (⟨![i₀, a, b], hfull 3 _⟩ : Nerve U 2))) = 0 := hzσ
    rwa [Fin.sum_univ_three, e0, e1, e2] at this
  show (∑ t : Fin 2, (z : Cochain U 1) ⟨![i₀, (face t σ).idx 0], hfull 2 _⟩)
      = (z : Cochain U 1) σ
  have f0 : (face 0 σ).idx 0 = b := by simp [face, Nerve.idx, hb]
  have f1 : (face 1 σ).idx 0 = a := by simp [face, Nerve.idx, ha]
  rw [Fin.sum_univ_two, f0, f1]
  have key : ∀ A B C : ZMod 2, A + B + C = 0 → B + C = A := by decide
  exact key _ _ _ hsum

end CechZ2
