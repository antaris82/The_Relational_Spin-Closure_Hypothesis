import RequestProject.Spine.E2.Cech.LocalLifts

/-!
# Task 3, WP4–WP5 : the triple-overlap kernel defect and its Čech 2-cocycle law

Given a family of local lifts `g̃_ij` of the visible transition cocycle `g_ij`, the
triple-overlap defect is

`c_ijk x = g̃_ij x * g̃_jk x * (g̃_ik x)⁻¹`.

Nothing about it is postulated.  It is *defined* as the inherited relative factor of two
internal representatives of the **same** visible map `g_ik` — namely `g̃_ij * g̃_jk` and
`g̃_ik` — so that:

* kernel-valuedness (`defect_mem_ker`) is the inherited theorem
  `InternalProjection.tripleDefect_mem_ker`, whose proof consumes the visible cocycle law,
  the homomorphism property of the projection and the definition of its kernel;
* continuity and local constancy (`defect_isKerFunOn`, `defect_isLocallyConstant`) are the
  inherited theorems, local constancy coming from discreteness of the kernel;
* the Čech 2-cocycle law on quadruple overlaps (`defect_cocycle₂`) is the inherited
  quadruple-overlap consistency identity, whose proof is associativity in the internal group
  **plus centrality of the kernel**.

The index convention is fixed once and for all by `defect_apply` below, and the resulting
2-cocycle law is *read off* the inherited identity rather than hard-coded: the derived
identity is

`c_jkl * c_ijl = c_ijk * c_ikl`,

equivalently `c_jkl * c_ikl⁻¹ * c_ijl * c_ijk⁻¹ = 1`.

**Where centrality is needed.**  `defect_mem_ker` uses only that the kernel is a subgroup
(kernel-valuedness).  The 2-cocycle law is *not* available from kernel-valuedness alone: the
two bracketings of `g̃_ij * g̃_jk * g̃_kl` differ by moving a defect past a lift, which is
legitimate exactly because the kernel is central.  The same is true of the coboundary law of
WP6.  This distinction is recorded in `defect_cocycle₂_uses_centrality` below.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace CechSpinLift

open NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}
  {𝓤 : CechCover X ι} {P : InternalProjection L G} {T : VisibleCocycle G 𝓤}

namespace SpinLiftFamily

/-! ## The three local representatives of `g_ik` on a triple overlap -/

theorem isRep₃_ij (D : SpinLiftFamily P T) (i j k : ι) :
    P.IsInternalRepOn (T.g i j) (𝓤.overlap₃ i j k) (D.lift i j) :=
  (D.isRep i j).mono P (𝓤.overlap₃_subset_ij i j k)

theorem isRep₃_jk (D : SpinLiftFamily P T) (i j k : ι) :
    P.IsInternalRepOn (T.g j k) (𝓤.overlap₃ i j k) (D.lift j k) :=
  (D.isRep j k).mono P (𝓤.overlap₃_subset_jk i j k)

theorem isRep₃_ik (D : SpinLiftFamily P T) (i j k : ι) :
    P.IsInternalRepOn (T.g i k) (𝓤.overlap₃ i j k) (D.lift i k) :=
  (D.isRep i k).mono P (𝓤.overlap₃_subset_ik i j k)

/-! ## WP4 — the defect -/

/-- **NEWLY DEFINED (WP4), principal.**  The triple-overlap defect of a chosen family of
local lifts.  It is the inherited `tripleDefect` of the E2 lift layer, with the argument
order matching the Čech convention `g_ij * g_jk = g_ik`. -/
def defect (D : SpinLiftFamily P T) (i j k : ι) : X → L :=
  InternalProjection.tripleDefect (D.lift j k) (D.lift i j) (D.lift i k)

@[simp] theorem defect_apply (D : SpinLiftFamily P T) (i j k : ι) (x : X) :
    D.defect i j k x = D.lift i j x * D.lift j k x * (D.lift i k x)⁻¹ := rfl

/-- **DERIVED (WP4).**  The defining identity, in the fixed convention. -/
theorem lift_mul_lift (D : SpinLiftFamily P T) (i j k : ι) (x : X) :
    D.lift i j x * D.lift j k x = D.defect i j k x * D.lift i k x :=
  InternalProjection.tripleDefect_mul _ _ _ x

/-- **DERIVED_NATIVE (WP4), principal.**  `ρ (c_ijk) = 1`: the defect projects to the unit,
because `g̃_ij * g̃_jk` and `g̃_ik` are two internal representatives of the *same* visible map
`g_ik` — this is where the visible cocycle law and the homomorphism property are consumed. -/
theorem proj_defect (D : SpinLiftFamily P T) (i j k : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₃ i j k) : P.proj (D.defect i j k x) = 1 := by
  have h : D.defect i j k x ∈ P.Ker :=
    P.tripleDefect_mem_ker (D.isRep₃_jk i j k) (D.isRep₃_ij i j k) (D.isRep₃_ik i j k)
      (fun _ hy => T.cocycle' i j k hy) hx
  exact (P.mem_Ker_iff).1 h

/-- **DERIVED_NATIVE (WP4), principal.**  Kernel-valuedness: `c_ijk x ∈ ker ρ`.  Not
postulated — obtained from `proj_defect`. -/
theorem defect_mem_ker (D : SpinLiftFamily P T) (i j k : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₃ i j k) : D.defect i j k x ∈ P.Ker :=
  (P.mem_Ker_iff).2 (D.proj_defect i j k hx)

/-- **DERIVED_NATIVE (WP4).**  The defect is a continuous kernel-valued function on the
triple overlap. -/
theorem defect_isKerFunOn (D : SpinLiftFamily P T) (i j k : ι) :
    P.IsKerFunOn (𝓤.overlap₃ i j k) (D.defect i j k) :=
  P.tripleDefect_isKerFunOn (D.isRep₃_jk i j k) (D.isRep₃_ij i j k) (D.isRep₃_ik i j k)
    (fun _ hy => T.cocycle' i j k hy)

theorem defect_continuousOn (D : SpinLiftFamily P T) (i j k : ι) :
    ContinuousOn (D.defect i j k) (𝓤.overlap₃ i j k) :=
  (D.defect_isKerFunOn i j k).1

/-- **DERIVED_NATIVE (WP4), principal.**  Local constancy: a continuous function into a
*discrete* kernel is locally constant.  Discreteness of `ker ρ` is exactly the inherited
field `ker_discrete` of the projection interface. -/
theorem defect_isLocallyConstant (D : SpinLiftFamily P T) (i j k : ι) :
    IsLocallyConstant (P.toKerFun (D.defect_isKerFunOn i j k)) :=
  P.isLocallyConstant_toKerFun _

/-- **DERIVED_NATIVE (WP4).**  On a connected triple overlap the defect is constant. -/
theorem defect_const_of_preconnected (D : SpinLiftFamily P T) (i j k : ι)
    (hV : IsPreconnected (𝓤.overlap₃ i j k)) {x y : X} (hx : x ∈ 𝓤.overlap₃ i j k)
    (hy : y ∈ 𝓤.overlap₃ i j k) : D.defect i j k x = D.defect i j k y :=
  P.toKerFun_const_of_connected (D.defect_isKerFunOn i j k) hV hx hy

/-! ## WP5 — the Čech 2-cocycle law -/

theorem isRep₄ (D : SpinLiftFamily P T) (i j k l : ι) (p q : ι)
    (hp : 𝓤.overlap₄ i j k l ⊆ 𝓤.U p) (hq : 𝓤.overlap₄ i j k l ⊆ 𝓤.U q) :
    P.IsInternalRepOn (T.g p q) (𝓤.overlap₄ i j k l) (D.lift p q) :=
  (D.isRep p q).mono P fun _ hx => ⟨hp hx, hq hx⟩

/-- **DERIVED_NATIVE (WP5), principal.**  The exact Čech 2-cocycle identity on a quadruple
overlap, in the convention fixed by `defect_apply`:

`c_jkl * c_ijl = c_ijk * c_ikl`.

It is the inherited quadruple-overlap consistency identity of the E2 lift layer, whose proof
is associativity in the internal group together with **centrality of the kernel**. -/
theorem defect_cocycle₂ (D : SpinLiftFamily P T) (i j k l : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₄ i j k l) :
    D.defect j k l x * D.defect i j l x = D.defect i j k x * D.defect i k l x := by
  have hkl := D.isRep₄ i j k l k l (𝓤.overlap₄_subset_U₃ i j k l) (𝓤.overlap₄_subset_U₄ i j k l)
  have hjk := D.isRep₄ i j k l j k (𝓤.overlap₄_subset_U₂ i j k l) (𝓤.overlap₄_subset_U₃ i j k l)
  have hij := D.isRep₄ i j k l i j (𝓤.overlap₄_subset_U₁ i j k l) (𝓤.overlap₄_subset_U₂ i j k l)
  have hjl := D.isRep₄ i j k l j l (𝓤.overlap₄_subset_U₂ i j k l) (𝓤.overlap₄_subset_U₄ i j k l)
  have hik := D.isRep₄ i j k l i k (𝓤.overlap₄_subset_U₁ i j k l) (𝓤.overlap₄_subset_U₃ i j k l)
  exact P.quadruple_defect_consistency hkl hjk hij hjl hik
    (fun y hy => T.cocycle' j k l (𝓤.overlap₄_subset_jkl i j k l hy))
    (fun y hy => T.cocycle' i j k (𝓤.overlap₄_subset_ijk i j k l hy)) hx

/-- **DERIVED_NATIVE (WP5), principal endpoint.**  The multiplicative Čech 2-cocycle law in
alternating form:

`c_jkl * c_ikl⁻¹ * c_ijl * c_ijk⁻¹ = 1`.

The rearrangement from `defect_cocycle₂` uses centrality of the kernel a second time. -/
theorem defect_delta_eq_one (D : SpinLiftFamily P T) (i j k l : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₄ i j k l) :
    D.defect j k l x * (D.defect i k l x)⁻¹ * D.defect i j l x * (D.defect i j k x)⁻¹ = 1 := by
  have hikl : D.defect i k l x ∈ P.Ker :=
    D.defect_mem_ker i k l (𝓤.overlap₄_subset_ikl i j k l hx)
  have hijl : D.defect i j l x ∈ P.Ker :=
    D.defect_mem_ker i j l (𝓤.overlap₄_subset_ijl i j k l hx)
  have hcomm : (D.defect i k l x)⁻¹ * D.defect i j l x
      = D.defect i j l x * (D.defect i k l x)⁻¹ :=
    ((P.ker_commute hikl (D.defect i j l x)).inv_left).eq
  have hkey := D.defect_cocycle₂ i j k l hx
  calc D.defect j k l x * (D.defect i k l x)⁻¹ * D.defect i j l x * (D.defect i j k x)⁻¹
      = D.defect j k l x * D.defect i j l x * ((D.defect i k l x)⁻¹ * (D.defect i j k x)⁻¹) := by
        rw [mul_assoc (D.defect j k l x), hcomm]; group
    _ = D.defect i j k x * D.defect i k l x * ((D.defect i k l x)⁻¹ * (D.defect i j k x)⁻¹) := by
        rw [hkey]
    _ = 1 := by group

/-- **AUDIT (WP5).**  Where centrality is needed, made explicit: kernel-valuedness of the
three defects entering the identity is available from `defect_mem_ker` alone, but the
identity itself is proved from the inherited quadruple-overlap consistency theorem, whose
hypothesis list includes centrality of the kernel through `InternalProjection.ker_commute`.
This statement records the two ingredients side by side. -/
theorem defect_cocycle₂_uses_centrality (D : SpinLiftFamily P T) (i j k l : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₄ i j k l) :
    (D.defect i j k x ∈ P.Ker ∧ D.defect i k l x ∈ P.Ker ∧ D.defect i j l x ∈ P.Ker ∧
      D.defect j k l x ∈ P.Ker) ∧
    (∀ z ∈ P.Ker, ∀ y : L, z * y = y * z) ∧
    D.defect j k l x * D.defect i j l x = D.defect i j k x * D.defect i k l x :=
  ⟨⟨D.defect_mem_ker i j k (𝓤.overlap₄_subset_ijk i j k l hx),
    D.defect_mem_ker i k l (𝓤.overlap₄_subset_ikl i j k l hx),
    D.defect_mem_ker i j l (𝓤.overlap₄_subset_ijl i j k l hx),
    D.defect_mem_ker j k l (𝓤.overlap₄_subset_jkl i j k l hx)⟩,
   fun _ hz y => P.ker_comm hz y, D.defect_cocycle₂ i j k l hx⟩

/-- **WP4 + WP5, packaged endpoint.**  For a chosen family of local lifts of an exact visible
Čech 1-cocycle, the triple-overlap defect exists, is defined by the displayed formula, takes
values in the kernel of the projection, is continuous, is locally constant, and satisfies the
exact multiplicative Čech 2-cocycle law. -/
theorem spinLiftObstruction_defect (D : SpinLiftFamily P T) :
    (∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k,
        D.lift i j x * D.lift j k x = D.defect i j k x * D.lift i k x) ∧
    (∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k, D.defect i j k x ∈ P.Ker) ∧
    (∀ i j k, ContinuousOn (D.defect i j k) (𝓤.overlap₃ i j k)) ∧
    (∀ i j k, IsLocallyConstant (P.toKerFun (D.defect_isKerFunOn i j k))) ∧
    (∀ i j k l, ∀ x ∈ 𝓤.overlap₄ i j k l,
        D.defect j k l x * (D.defect i k l x)⁻¹ * D.defect i j l x * (D.defect i j k x)⁻¹ = 1) :=
  ⟨fun i j k x _ => D.lift_mul_lift i j k x,
   fun i j k _ hx => D.defect_mem_ker i j k hx,
   fun i j k => D.defect_continuousOn i j k,
   fun i j k => D.defect_isLocallyConstant i j k,
   fun i j k l _ hx => D.defect_delta_eq_one i j k l hx⟩

end SpinLiftFamily

end CechSpinLift
