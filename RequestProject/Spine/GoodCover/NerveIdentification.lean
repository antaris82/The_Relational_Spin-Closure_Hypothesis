import RequestProject.Spine.GoodCover.Presimplicial
import RequestProject.Spine.Cech.Cohomology

/-!
# Task 7, WP5 (b) : the Čech complex of a cover *is* the simplicial complex of its nerve

`RequestProject.Spine.GoodCover.Presimplicial` defines, independently of any cover, the
simplicial `ℤ₂` cochain complex of an abstract presimplicial set.  This module exhibits the
**nerve of a cover** `N(𝓤)` as such a presimplicial set:

* a `k`-simplex of `NerveZ2.coverNerve U` is a `(k+1)`-tuple of indices with
  `U i₀ ∩ ⋯ ∩ U i_k ≠ ∅` (`CechZ2.Nerve`);
* the face operators delete one index (`CechZ2.face`);
* the presimplicial identity is the `Fin.succAbove` commutation `CechZ2.succAbove_comm`.

and then proves that the Task-6 Čech complex is *literally* the simplicial cochain complex of
this nerve: the cochain modules, the coboundaries, the cocycles, the coboundary submodules and
the cohomology quotients agree **definitionally**, so the comparison isomorphism is the
identity, not a chosen map.

```
    Ȟⁿ(𝓤;ℤ₂)  =  Hⁿ_simp(N(𝓤);ℤ₂)          (`NerveZ2.cechCohomologyEquiv`, `rfl`)
```

This settles WP5 in the strongest possible form ("expose the fact cleanly rather than rebuild
it"), and in particular fixes the meaning of `Ȟ²(𝓤;ℤ₂)` for the rest of Task 7: it is nerve
cohomology, with one `ℤ₂` per nonempty finite overlap and no component information.
-/

namespace NerveZ2

open CechZ2

universe w t

variable {X : Type w} {ι : Type t}

/-- **The nerve of a cover as a presimplicial set.**  Simplices are the nonempty finite
overlaps (as index tuples), faces delete an index. -/
def coverNerve (U : ι → Set X) : Presimplicial.{t} where
  obj := Nerve U
  face := fun {_} t σ => CechZ2.face t σ
  face_comm := by
    intro n i j hij x
    apply Nerve.ext
    funext u
    exact congrArg x.idx (CechZ2.succAbove_comm hij u)

@[simp] theorem coverNerve_obj (U : ι → Set X) (n : ℕ) :
    (coverNerve U).obj n = Nerve U n := rfl

@[simp] theorem coverNerve_face (U : ι → Set X) {n : ℕ} (t : Fin (n + 2))
    (σ : Nerve U (n + 1)) : (coverNerve U).face t σ = CechZ2.face t σ := rfl

/-! ## The two complexes coincide -/

/-- The cochain modules agree. -/
theorem coverNerve_cochain (U : ι → Set X) (n : ℕ) :
    (coverNerve U).Cochain n = CechZ2.Cochain U n := rfl

/-- The coboundaries agree, as functions. -/
theorem coverNerve_coboundary (U : ι → Set X) (n : ℕ) (c : CechZ2.Cochain U n) :
    (coverNerve U).coboundary n c = CechZ2.coboundary n c := rfl

/-- The coboundaries agree, as linear maps. -/
theorem coverNerve_d (U : ι → Set X) (n : ℕ) :
    (coverNerve U).d n = CechZ2.d U n := rfl

/-- The cocycle submodules agree. -/
theorem coverNerve_cocycles (U : ι → Set X) (n : ℕ) :
    (coverNerve U).cocycles n = CechZ2.cocycles U n := rfl

/-- The coboundary submodules agree. -/
theorem coverNerve_coboundaries (U : ι → Set X) (n : ℕ) :
    (coverNerve U).coboundaries n = CechZ2.coboundaries U n := by
  cases n <;> rfl

/-- The cohomology carriers agree (after the case split that reduces `coboundaries`). -/
theorem coverNerve_cohomology (U : ι → Set X) (n : ℕ) :
    (coverNerve U).Cohomology n = CechZ2.Cohomology U n := by
  cases n <;> rfl

/-- **WP5, principal.**  Fixed-cover Čech cohomology of `𝓤` *is* the simplicial cohomology of
the nerve of `𝓤`, with the identity as the comparison isomorphism. -/
def cechCohomologyEquiv (U : ι → Set X) :
    (n : ℕ) → ((coverNerve U).Cohomology n ≃ₗ[ZMod 2] CechZ2.Cohomology U n)
  | 0 => LinearEquiv.refl (ZMod 2) _
  | _ + 1 => LinearEquiv.refl (ZMod 2) _

/-- The degree-two case, the only one Task 7 consumes. -/
def cechCohomologyEquiv₂ (U : ι → Set X) :
    (coverNerve U).Cohomology 2 ≃ₗ[ZMod 2] CechZ2.Cohomology U 2 :=
  cechCohomologyEquiv U 2

/-- In degree two the comparison is the identity on the (definitionally equal) carriers. -/
@[simp] theorem cechCohomologyEquiv₂_apply (U : ι → Set X)
    (q : (coverNerve U).Cohomology 2) : cechCohomologyEquiv₂ U q = q := rfl

/-- Classes of cocycles match under the identification, in degree two. -/
theorem cechCohomologyEquiv₂_cohomologyClass (U : ι → Set X)
    (z : (coverNerve U).cocycles 2) :
    cechCohomologyEquiv₂ U ((coverNerve U).cohomologyClass z) = CechZ2.mk z := rfl

end NerveZ2
