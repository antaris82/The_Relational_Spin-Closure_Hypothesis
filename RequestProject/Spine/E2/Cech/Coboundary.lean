import RequestProject.Spine.E2.Cech.Defect

/-!
# Task 3, WP6 : change of local Spin representatives and the coboundary law

Two families of local lifts of the *same* visible transition cocycle differ, on the nose, by
kernel-valued functions:

`g̃'_ij = ε_ij * g̃_ij`,  `ε_ij : U_ij → ker ρ`.

This is the inherited relative-factor theorem of the E2 lift layer, not a new assumption.
The triple defect then transforms by the multiplicative Čech coboundary of `ε`:

`c'_ijk = (δε)_ijk * c_ijk`,  `(δε)_ijk = ε_ij * ε_jk * ε_ik⁻¹`.

Centrality of the kernel is used twice: to move `ε_jk` past `g̃_ij` in the product, and to
identify `δ(ε' ε) = δε' · δε` and `δ(ε⁻¹) = (δε)⁻¹` (`delta₁_mul`, `delta₁_inv`), which is
what makes "cohomologous" an equivalence relation in WP7.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace CechSpinLift

open NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}
  {𝓤 : CechCover X ι} {P : InternalProjection L G} {T : VisibleCocycle G 𝓤}

/-! ## Kernel-valued Čech cochains -/

/-- **NEWLY DEFINED (WP6).**  A kernel-valued Čech 1-cochain: a continuous kernel-valued
function on every double overlap. -/
def IsKerCochain₁ (P : InternalProjection L G) (𝓤 : CechCover X ι) (ε : ι → ι → (X → L)) :
    Prop :=
  ∀ i j, P.IsKerFunOn (𝓤.overlap₂ i j) (ε i j)

/-- **NEWLY DEFINED (WP6).**  A kernel-valued Čech 2-cochain: a continuous kernel-valued
function on every triple overlap. -/
def IsKerCochain₂ (P : InternalProjection L G) (𝓤 : CechCover X ι)
    (c : ι → ι → ι → (X → L)) : Prop :=
  ∀ i j k, P.IsKerFunOn (𝓤.overlap₃ i j k) (c i j k)

/-- **NEWLY DEFINED (WP6), principal.**  The multiplicative Čech coboundary of a 1-cochain,
in the convention fixed by `SpinLiftFamily.defect_apply`. -/
def delta₁ (ε : ι → ι → (X → L)) : ι → ι → ι → (X → L) :=
  fun i j k x => ε i j x * ε j k x * (ε i k x)⁻¹

omit [TopologicalSpace L] [IsTopologicalGroup L] [TopologicalSpace X] in
@[simp] theorem delta₁_apply (ε : ι → ι → (X → L)) (i j k : ι) (x : X) :
    delta₁ ε i j k x = ε i j x * ε j k x * (ε i k x)⁻¹ := rfl

/-- The trivial 1-cochain. -/
def one₁ : ι → ι → (X → L) := fun _ _ _ => 1

/-- The trivial 2-cochain. -/
def one₂ : ι → ι → ι → (X → L) := fun _ _ _ _ => 1

omit [TopologicalSpace L] [IsTopologicalGroup L] [TopologicalSpace X] in
@[simp] theorem delta₁_one : delta₁ (one₁ : ι → ι → (X → L)) = (one₂ : ι → ι → ι → (X → L)) := by
  funext i j k x
  simp [delta₁, one₁, one₂]

/-- Pointwise product of 1-cochains. -/
def mul₁ (ε ε' : ι → ι → (X → L)) : ι → ι → (X → L) := fun i j x => ε i j x * ε' i j x

/-- Pointwise inverse of a 1-cochain. -/
def inv₁ (ε : ι → ι → (X → L)) : ι → ι → (X → L) := fun i j x => (ε i j x)⁻¹

theorem isKerCochain₁_one : IsKerCochain₁ P 𝓤 (one₁ : ι → ι → (X → L)) :=
  fun _ _ => P.isKerFunOn_one _

theorem IsKerCochain₁.mul {ε ε' : ι → ι → (X → L)} (h : IsKerCochain₁ P 𝓤 ε)
    (h' : IsKerCochain₁ P 𝓤 ε') : IsKerCochain₁ P 𝓤 (mul₁ ε ε') :=
  fun i j => (h i j).mul P (h' i j)

theorem IsKerCochain₁.inv {ε : ι → ι → (X → L)} (h : IsKerCochain₁ P 𝓤 ε) :
    IsKerCochain₁ P 𝓤 (inv₁ ε) :=
  fun i j => (h i j).inv P

/-- **DERIVED (WP6).**  The coboundary of a kernel-valued 1-cochain is a kernel-valued
2-cochain. -/
theorem isKerCochain₂_delta₁ {ε : ι → ι → (X → L)} (h : IsKerCochain₁ P 𝓤 ε) :
    IsKerCochain₂ P 𝓤 (delta₁ ε) := by
  intro i j k
  refine ⟨?_, ?_⟩
  · exact ((((h i j).mono P (𝓤.overlap₃_subset_ij i j k)).mul P
      ((h j k).mono P (𝓤.overlap₃_subset_jk i j k))).mul P
      (((h i k).mono P (𝓤.overlap₃_subset_ik i j k)).inv P)).1
  · intro x hx
    exact ((((h i j).mono P (𝓤.overlap₃_subset_ij i j k)).mul P
      ((h j k).mono P (𝓤.overlap₃_subset_jk i j k))).mul P
      (((h i k).mono P (𝓤.overlap₃_subset_ik i j k)).inv P)).2 x hx

/-- **DERIVED (WP6), uses centrality.**  `δ` is multiplicative on kernel-valued 1-cochains. -/
theorem delta₁_mul {ε ε' : ι → ι → (X → L)} (h : IsKerCochain₁ P 𝓤 ε') (i j k : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₃ i j k) :
    delta₁ (mul₁ ε' ε) i j k x = delta₁ ε' i j k x * delta₁ ε i j k x := by
  have hjk : ε' j k x ∈ P.Ker := (h j k).2 x (𝓤.overlap₃_subset_jk i j k hx)
  have hik : ε' i k x ∈ P.Ker := (h i k).2 x (𝓤.overlap₃_subset_ik i j k hx)
  simpa [delta₁, mul₁] using
    InternalProjection.central_rearrange (b := ε' j k x) (c := ε' i k x)
      (P.ker_commute hjk) (P.ker_commute hik) (ε' i j x) (ε i j x) (ε j k x) (ε i k x)

/-- **DERIVED (WP6), uses centrality.**  `δ` inverts kernel-valued 1-cochains. -/
theorem delta₁_inv {ε : ι → ι → (X → L)} (h : IsKerCochain₁ P 𝓤 ε) (i j k : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₃ i j k) :
    delta₁ (inv₁ ε) i j k x = (delta₁ ε i j k x)⁻¹ := by
  have hmul := delta₁_mul (P := P) (ε := ε) (ε' := inv₁ ε) h.inv i j k hx
  have hone : delta₁ (mul₁ (inv₁ ε) ε) i j k x = 1 := by
    simp [delta₁, mul₁, inv₁]
  rw [hone] at hmul
  exact (eq_inv_of_mul_eq_one_left hmul.symm)

namespace SpinLiftFamily

/-! ## WP6 — the change of local representatives -/

/-- **NEWLY DEFINED (WP6), principal.**  The kernel-valued 1-cochain comparing two families
of local lifts: `ε_ij = g̃'_ij * g̃_ij⁻¹`. -/
def liftRatio (D D' : SpinLiftFamily P T) : ι → ι → (X → L) :=
  fun i j => InternalProjection.relFactor (D.lift i j) (D'.lift i j)

@[simp] theorem liftRatio_apply (D D' : SpinLiftFamily P T) (i j : ι) (x : X) :
    liftRatio D D' i j x = D'.lift i j x * (D.lift i j x)⁻¹ := rfl

/-- **DERIVED_NATIVE (WP6), principal.**  The comparison cochain is kernel-valued and
continuous: two lifts of the same visible map differ by a continuous kernel-valued
function. -/
theorem liftRatio_isKerCochain₁ (D D' : SpinLiftFamily P T) :
    IsKerCochain₁ P 𝓤 (liftRatio D D') :=
  fun i j => P.relFactor_isKerFunOn (D.isRep i j) (D'.isRep i j)

/-- **DERIVED (WP6), principal.**  `g̃'_ij = ε_ij * g̃_ij`, on the nose. -/
theorem lift_eq_liftRatio_mul (D D' : SpinLiftFamily P T) (i j : ι) :
    D'.lift i j = fun x => liftRatio D D' i j x * D.lift i j x := by
  funext x
  simp

/-- **NEWLY DEFINED (WP6).**  Modifying a family of local lifts by a kernel-valued 1-cochain
gives another family of local lifts of the *same* visible transition data. -/
def twist (D : SpinLiftFamily P T) (ε : ι → ι → (X → L)) (hε : IsKerCochain₁ P 𝓤 ε) :
    SpinLiftFamily P T where
  lift i j := fun x => ε i j x * D.lift i j x
  isRep i j := P.isInternalRepOn_kerFun_mul (D.isRep i j) (hε i j)

@[simp] theorem twist_lift (D : SpinLiftFamily P T) (ε : ι → ι → (X → L))
    (hε : IsKerCochain₁ P 𝓤 ε) (i j : ι) (x : X) :
    (D.twist ε hε).lift i j x = ε i j x * D.lift i j x := rfl

theorem liftRatio_twist (D : SpinLiftFamily P T) (ε : ι → ι → (X → L))
    (hε : IsKerCochain₁ P 𝓤 ε) (i j : ι) (x : X) :
    liftRatio D (D.twist ε hε) i j x = ε i j x := by
  simp [liftRatio, InternalProjection.relFactor]

/-- **DERIVED_NATIVE (WP6), principal — the Čech coboundary law in its primitive form.**  If
two families of local lifts are related pointwise by a kernel-valued cochain `ε`, their
triple defects differ by the coboundary `δε`.  Centrality of the kernel is used to move
`ε_jk` and `ε_ik` out of the product (the inherited `central_rearrange`). -/
theorem defect_eq_delta₁_mul (D D' : SpinLiftFamily P T) {ε : ι → ι → (X → L)}
    (hε : IsKerCochain₁ P 𝓤 ε) (hlift : ∀ i j x, D'.lift i j x = ε i j x * D.lift i j x)
    (i j k : ι) {x : X} (hx : x ∈ 𝓤.overlap₃ i j k) :
    D'.defect i j k x = delta₁ ε i j k x * D.defect i j k x := by
  have hjk : ε j k x ∈ P.Ker := (hε j k).2 x (𝓤.overlap₃_subset_jk i j k hx)
  have hik : ε i k x ∈ P.Ker := (hε i k).2 x (𝓤.overlap₃_subset_ik i j k hx)
  have hkey := InternalProjection.central_rearrange (b := ε j k x) (c := ε i k x)
    (P.ker_commute hjk) (P.ker_commute hik) (ε i j x) (D.lift i j x) (D.lift j k x)
    (D.lift i k x)
  simp only [defect_apply, delta₁_apply, hlift]
  simpa [mul_assoc] using hkey

/-- **DERIVED_NATIVE (WP6), principal endpoint — the Čech coboundary law.**  Changing the
local Spin representatives by the kernel-valued cochain `ε` multiplies the triple defect by
the coboundary `δε`:  `c'_ijk = (δε)_ijk * c_ijk`. -/
theorem defect_twist (D : SpinLiftFamily P T) (ε : ι → ι → (X → L))
    (hε : IsKerCochain₁ P 𝓤 ε) (i j k : ι) {x : X} (hx : x ∈ 𝓤.overlap₃ i j k) :
    (D.twist ε hε).defect i j k x = delta₁ ε i j k x * D.defect i j k x :=
  defect_eq_delta₁_mul D (D.twist ε hε) hε (fun _ _ _ => rfl) i j k hx

/-- **DERIVED_NATIVE (WP6), principal endpoint.**  For *any* two families of local lifts of
the same visible cocycle there is a kernel-valued 1-cochain `ε` with `g̃' = ε g̃` and
`c' = (δε) c`: the defect is well defined only up to a Čech 1-coboundary. -/
theorem defect_change_of_lift (D D' : SpinLiftFamily P T) :
    ∃ ε : ι → ι → (X → L), IsKerCochain₁ P 𝓤 ε ∧
      (∀ i j, D'.lift i j = fun x => ε i j x * D.lift i j x) ∧
      (∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k,
        D'.defect i j k x = delta₁ ε i j k x * D.defect i j k x) :=
  ⟨liftRatio D D', D.liftRatio_isKerCochain₁ D', D.lift_eq_liftRatio_mul D',
    fun i j k _ hx => defect_eq_delta₁_mul D D' (D.liftRatio_isKerCochain₁ D')
      (fun p q y => by
        simp [liftRatio, InternalProjection.relFactor])
      i j k hx⟩

end SpinLiftFamily

end CechSpinLift
