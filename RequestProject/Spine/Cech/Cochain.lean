import Mathlib

/-!
# Task 6, WP2 : native fixed-cover Čech cochains with constant `ℤ₂` coefficients

This is the first module of the Task-6 layer.  It is deliberately **independent of every
Spin-, Clifford- or lift-theoretic notion**: its only inputs are an indexed family of subsets
`U : ι → Set X` and the ring `ZMod 2`.  In particular the whole complex of this layer can be
elaborated without the Task-3 obstruction being in scope, which is what
"the Čech complex must exist independently of Spin geometry" requires.

## The cover model

The Task-3 layer already fixes a cover representation, `CechSpinLift.CechCover X ι`, whose
data is an indexed family `U : ι → Set X` of open sets together with the covering property.
No *new* cover model is introduced here.  Instead, everything below is stated for the
underlying family `U : ι → Set X`, so that a Task-3 cover `𝓤` is used simply as `𝓤.U`
(see `RequestProject.Spine.Cech.SpinCocycle`).  Neither openness nor the covering property is
needed for the cochain complex, so they are not assumed; the extra hypotheses of a
`CechCover` are of course still available when a cover is plugged in.

## The nerve and the cochains

* `CechZ2.inter U σ` — the intersection `⋂ s, U (σ s)` of a finite tuple of cover members.
* `CechZ2.Nerve U n` — the **nerve in degree `n`**: `(n+1)`-tuples of indices whose
  intersection is nonempty.  Only nonempty overlaps are used, as in the standard Čech
  complex; the empty ones carry no data at all.
* `CechZ2.face t σ` — the `t`-th face of a nerve simplex, obtained by deleting the index in
  position `t` (`Fin.succAbove`).  Deleting an index enlarges the intersection, so
  nonemptiness is preserved and the face is again a nerve simplex — this is a theorem, not an
  assumption.
* `CechZ2.Cochain U n = Nerve U n → ZMod 2` — degree-`n` Čech cochains.  This is a genuine
  function type: a cochain assigns a `ℤ₂`-value to every nonempty `(n+1)`-fold overlap, and
  its `AddCommGroup` / `Module (ZMod 2)` structures are the ones Mathlib derives for `Pi`
  types.  It is not a predicate wrapper and not an opaque carrier.

The definition is degree-generic, so degrees `n = 0, 1, 2, 3` (the minimum required) are all
covered; convenience constructors for these degrees are provided.
-/

namespace CechZ2

universe w t

variable {X : Type w} {ι : Type t}

/-! ## Overlaps -/

/-- The overlap `⋂ s, U (σ s)` associated with a finite tuple `σ` of indices. -/
def inter (U : ι → Set X) {n : ℕ} (σ : Fin n → ι) : Set X := ⋂ s, U (σ s)

theorem mem_inter_iff (U : ι → Set X) {n : ℕ} (σ : Fin n → ι) (x : X) :
    x ∈ inter U σ ↔ ∀ s, x ∈ U (σ s) := by
  simp [inter]

/-- Reindexing a tuple along any map can only enlarge its overlap: the overlap of a
subfamily contains the overlap of the whole family. -/
theorem inter_subset_comp (U : ι → Set X) {m n : ℕ} (σ : Fin n → ι) (f : Fin m → Fin n) :
    inter U σ ⊆ inter U (σ ∘ f) := by
  intro x hx
  rw [mem_inter_iff] at hx ⊢
  exact fun s => hx (f s)

/-! ## The nerve -/

/-- The **nerve of the cover in degree `n`**: tuples of `n+1` indices whose overlap is
nonempty.  These are exactly the overlaps a Čech `n`-cochain is evaluated on. -/
def Nerve (U : ι → Set X) (n : ℕ) : Type t :=
  {σ : Fin (n + 1) → ι // (inter U σ).Nonempty}

namespace Nerve

variable {U : ι → Set X} {n : ℕ}

/-- The underlying tuple of indices of a nerve simplex. -/
def idx (σ : Nerve U n) : Fin (n + 1) → ι := σ.1

theorem nonempty (σ : Nerve U n) : (inter U σ.idx).Nonempty := σ.2

@[ext] theorem ext {σ τ : Nerve U n} (h : σ.idx = τ.idx) : σ = τ := Subtype.ext h

/-- A nerve simplex from a tuple together with a point of its overlap. -/
def ofMem (σ : Fin (n + 1) → ι) {x : X} (hx : x ∈ inter U σ) : Nerve U n := ⟨σ, ⟨x, hx⟩⟩

@[simp] theorem idx_ofMem (σ : Fin (n + 1) → ι) {x : X} (hx : x ∈ inter U σ) :
    (ofMem σ hx).idx = σ := rfl

end Nerve

/-- The **`t`-th face** of a nerve simplex: delete the index in position `t`.  Nonemptiness
of the smaller overlap is inherited from the bigger one (`inter_subset_comp`). -/
def face {U : ι → Set X} {n : ℕ} (t : Fin (n + 2)) (σ : Nerve U (n + 1)) : Nerve U n :=
  ⟨σ.idx ∘ t.succAbove, σ.nonempty.mono (inter_subset_comp U σ.idx t.succAbove)⟩

@[simp] theorem face_idx {U : ι → Set X} {n : ℕ} (t : Fin (n + 2)) (σ : Nerve U (n + 1)) :
    (face t σ).idx = σ.idx ∘ t.succAbove := rfl

/-- Two successive faces delete two positions; this records the resulting index tuple. -/
theorem face_face {U : ι → Set X} {n : ℕ} (s : Fin (n + 3)) (t : Fin (n + 2))
    (σ : Nerve U (n + 2)) :
    (face t (face s σ)).idx = fun u => σ.idx (s.succAbove (t.succAbove u)) := rfl

/-! ## Cochains -/

/-- **Degree-`n` Čech cochains with constant coefficients in `ℤ/2`**: `ℤ/2`-valued functions
on the nonempty `(n+1)`-fold overlaps of the family `U`.  A genuine function type; its module
structure is the derived `Pi` structure. -/
abbrev Cochain (U : ι → Set X) (n : ℕ) : Type t := Nerve U n → ZMod 2

example (U : ι → Set X) (n : ℕ) : AddCommGroup (Cochain U n) := inferInstance
example (U : ι → Set X) (n : ℕ) : Module (ZMod 2) (Cochain U n) := inferInstance

@[simp] theorem Cochain.add_apply {U : ι → Set X} {n : ℕ} (a b : Cochain U n)
    (σ : Nerve U n) : (a + b) σ = a σ + b σ := rfl

@[simp] theorem Cochain.sub_apply {U : ι → Set X} {n : ℕ} (a b : Cochain U n)
    (σ : Nerve U n) : (a - b) σ = a σ - b σ := rfl

@[simp] theorem Cochain.zero_apply {U : ι → Set X} {n : ℕ} (σ : Nerve U n) :
    (0 : Cochain U n) σ = 0 := rfl

theorem Cochain.ext {U : ι → Set X} {n : ℕ} {a b : Cochain U n} (h : ∀ σ, a σ = b σ) :
    a = b := funext h

/-! ## Low degrees

The definition above is degree-generic.  For readability the required low degrees get
explicit nerve constructors: a `1`-cochain is evaluated on an ordered pair, a `2`-cochain on
an ordered triple and a `3`-cochain on an ordered quadruple — always restricted to tuples
with nonempty overlap. -/

/-- The pair `(i, j)` as a nerve simplex, given a point of `U i ∩ U j`. -/
def pair {U : ι → Set X} (i j : ι) {x : X} (hx : x ∈ U i ∩ U j) : Nerve U 1 :=
  Nerve.ofMem ![i, j] (by
    rw [mem_inter_iff]
    intro s
    fin_cases s
    · exact hx.1
    · exact hx.2)

/-- The triple `(i, j, k)` as a nerve simplex, given a point of `U i ∩ U j ∩ U k`. -/
def triple {U : ι → Set X} (i j k : ι) {x : X} (hx : x ∈ U i ∩ U j ∩ U k) : Nerve U 2 :=
  Nerve.ofMem ![i, j, k] (by
    rw [mem_inter_iff]
    intro s
    fin_cases s
    · exact hx.1.1
    · exact hx.1.2
    · exact hx.2)

/-- The quadruple `(i, j, k, l)` as a nerve simplex, given a point of the fourfold
overlap. -/
def quad {U : ι → Set X} (i j k l : ι) {x : X} (hx : x ∈ U i ∩ U j ∩ U k ∩ U l) :
    Nerve U 3 :=
  Nerve.ofMem ![i, j, k, l] (by
    rw [mem_inter_iff]
    intro s
    fin_cases s
    · exact hx.1.1.1
    · exact hx.1.1.2
    · exact hx.1.2
    · exact hx.2)

@[simp] theorem pair_idx {U : ι → Set X} (i j : ι) {x : X} (hx : x ∈ U i ∩ U j) :
    (pair (U := U) i j hx).idx = ![i, j] := rfl

@[simp] theorem triple_idx {U : ι → Set X} (i j k : ι) {x : X} (hx : x ∈ U i ∩ U j ∩ U k) :
    (triple (U := U) i j k hx).idx = ![i, j, k] := rfl

@[simp] theorem quad_idx {U : ι → Set X} (i j k l : ι) {x : X}
    (hx : x ∈ U i ∩ U j ∩ U k ∩ U l) : (quad (U := U) i j k l hx).idx = ![i, j, k, l] := rfl

end CechZ2
