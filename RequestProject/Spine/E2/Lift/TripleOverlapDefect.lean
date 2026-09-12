import RequestProject.Spine.E2.Lift.KernelAmbiguity

/-!
# Task 28, Packages H and I: the kernel-valued triple-overlap defect

**HARD TARGET C, first half.**

With the inherited convention `g_ik = g_jk * g_ij` the comparison of internal
representatives on a common refined triple overlap is

`u_jk * u_ij = δ_ijk * u_ik`,

which *defines* the defect

`δ_ijk x = (u_jk x * u_ij x) * (u_ik x)⁻¹`.

The defect is not postulated: it is the relative factor of the two internal representatives
`u_jk * u_ij` and `u_ik` of the *same* ordinary map `g_ik`, so Package E applies verbatim.
Proved here: kernel-valuedness (item 65), continuity (item 66), local constancy (item 67),
constancy on connected refined triple overlaps (item 68), the packaged endpoint
`triple_overlap_defect` (item 69), and the exact compatibility criterion
`exact_internal_transition_compatibility_iff_defect_trivial` (items 72–74).

The defect is **not** assumed trivial anywhere (item 70), and no cohomological reading of it
is introduced (item 71).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask28

universe u v w

namespace InternalProjection

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G]

variable {X : Type w} [TopologicalSpace X] (P : InternalProjection L G)

/-! ## The product representative on a triple overlap -/

/-- **DERIVED (item 62/63).**  If `u_ij` represents `g_ij` and `u_jk` represents `g_jk`, then
the product `u_jk * u_ij` represents `g_jk * g_ij`, which by the inherited triple-overlap law
is exactly `g_ik`. -/
theorem isInternalRepOn_mul {gij gjk : X → G} {V : Set X} {uij ujk : X → L}
    (hij : P.IsInternalRepOn gij V uij) (hjk : P.IsInternalRepOn gjk V ujk) :
    P.IsInternalRepOn (fun x => gjk x * gij x) V (fun x => ujk x * uij x) :=
  ⟨hjk.1.mul hij.1, fun x hx => by rw [map_mul, hij.2 x hx, hjk.2 x hx]⟩

/-! ## Package H — the triple-overlap defect (items 62–69) -/

/-- **NEWLY DEFINED (item 64), principal.**  The triple-overlap defect of three internal
representatives, defined by the inherited multiplication order:
`u_jk * u_ij = δ_ijk * u_ik`. -/
def tripleDefect (uij ujk uik : X → L) : X → L := fun x => (ujk x * uij x) * (uik x)⁻¹

omit [TopologicalSpace L] [IsTopologicalGroup L] [TopologicalSpace X] in
@[simp] theorem tripleDefect_apply (uij ujk uik : X → L) (x : X) :
    tripleDefect uij ujk uik x = (ujk x * uij x) * (uik x)⁻¹ := rfl

omit [TopologicalSpace L] [IsTopologicalGroup L] [TopologicalSpace X] in
/-- **PACKAGE H (item 64).**  The defining identity of the defect, in the exact inherited
order. -/
theorem tripleDefect_mul (uij ujk uik : X → L) (x : X) :
    ujk x * uij x = tripleDefect uij ujk uik x * uik x := by
  simp [tripleDefect]

/-- **PACKAGE H (item 65), principal.**  The defect takes values in the kernel. -/
theorem tripleDefect_mem_ker {gij gjk gik : X → G} {V : Set X} {uij ujk uik : X → L}
    (hij : P.IsInternalRepOn gij V uij) (hjk : P.IsInternalRepOn gjk V ujk)
    (hik : P.IsInternalRepOn gik V uik)
    (hlaw : ∀ x ∈ V, gik x = gjk x * gij x) {x : X} (hx : x ∈ V) :
    tripleDefect uij ujk uik x ∈ P.Ker := by
  have hprod : P.IsInternalRepOn gik V (fun y => ujk y * uij y) := by
    refine ⟨hjk.1.mul hij.1, fun y hy => ?_⟩
    rw [map_mul, hij.2 y hy, hjk.2 y hy, ← hlaw y hy]
  exact P.relFactor_mem_ker hik hprod hx

/-- **PACKAGE H (items 65, 66), principal.**  The defect is a continuous kernel-valued
function on the common refined triple overlap. -/
theorem tripleDefect_isKerFunOn {gij gjk gik : X → G} {V : Set X} {uij ujk uik : X → L}
    (hij : P.IsInternalRepOn gij V uij) (hjk : P.IsInternalRepOn gjk V ujk)
    (hik : P.IsInternalRepOn gik V uik) (hlaw : ∀ x ∈ V, gik x = gjk x * gij x) :
    P.IsKerFunOn V (tripleDefect uij ujk uik) :=
  ⟨(hjk.1.mul hij.1).mul hik.1.inv,
    fun _ hx => P.tripleDefect_mem_ker hij hjk hik hlaw hx⟩

/-- **PACKAGE H (item 67), principal.**  The defect is locally constant. -/
theorem tripleDefect_isLocallyConstant {gij gjk gik : X → G} {V : Set X} {uij ujk uik : X → L}
    (hij : P.IsInternalRepOn gij V uij) (hjk : P.IsInternalRepOn gjk V ujk)
    (hik : P.IsInternalRepOn gik V uik) (hlaw : ∀ x ∈ V, gik x = gjk x * gij x) :
    IsLocallyConstant (P.toKerFun (P.tripleDefect_isKerFunOn hij hjk hik hlaw)) :=
  P.isLocallyConstant_toKerFun _

/-- **PACKAGE H (item 68), principal.**  On a connected refined triple overlap the defect is
constant. -/
theorem tripleDefect_const_of_connected {gij gjk gik : X → G} {V : Set X} {uij ujk uik : X → L}
    (hij : P.IsInternalRepOn gij V uij) (hjk : P.IsInternalRepOn gjk V ujk)
    (hik : P.IsInternalRepOn gik V uik) (hlaw : ∀ x ∈ V, gik x = gjk x * gij x)
    (hV : IsPreconnected V) {x y : X} (hx : x ∈ V) (hy : y ∈ V) :
    tripleDefect uij ujk uik x = tripleDefect uij ujk uik y :=
  P.toKerFun_const_of_connected (P.tripleDefect_isKerFunOn hij hjk hik hlaw) hV hx hy

/-- **PACKAGE H (item 69), principal endpoint — HARD TARGET C.**  `triple_overlap_defect`:
on a common refined triple overlap, three continuous internal representatives of the three
ordinary transitions satisfying the inherited triple-overlap law are compared by a defect
which is defined by the inherited multiplication order, takes values in the kernel, is
continuous, and is locally constant.  Triviality of the defect is *not* asserted. -/
theorem triple_overlap_defect {gij gjk gik : X → G} {V : Set X} {uij ujk uik : X → L}
    (hij : P.IsInternalRepOn gij V uij) (hjk : P.IsInternalRepOn gjk V ujk)
    (hik : P.IsInternalRepOn gik V uik) (hlaw : ∀ x ∈ V, gik x = gjk x * gij x) :
    (∀ x ∈ V, ujk x * uij x = tripleDefect uij ujk uik x * uik x) ∧
      (∀ x ∈ V, tripleDefect uij ujk uik x ∈ P.Ker) ∧
      ContinuousOn (tripleDefect uij ujk uik) V ∧
      IsLocallyConstant (P.toKerFun (P.tripleDefect_isKerFunOn hij hjk hik hlaw)) :=
  ⟨fun x _ => tripleDefect_mul uij ujk uik x,
    fun _ hx => P.tripleDefect_mem_ker hij hjk hik hlaw hx,
    (P.tripleDefect_isKerFunOn hij hjk hik hlaw).1,
    P.tripleDefect_isLocallyConstant hij hjk hik hlaw⟩

omit [TopologicalSpace L] [IsTopologicalGroup L] [TopologicalSpace X] in
/-- **PACKAGE H.**  Uniqueness: the defect is the *only* kernel-valued function implementing
the comparison. -/
theorem tripleDefect_unique {V : Set X} {uij ujk uik d : X → L}
    (hd : ∀ x ∈ V, ujk x * uij x = d x * uik x) {x : X} (hx : x ∈ V) :
    d x = tripleDefect uij ujk uik x := by
  rw [tripleDefect_apply, hd x hx, mul_inv_cancel_right]

/-! ## Package I — the exact compatibility criterion (items 72–75) -/

omit [TopologicalSpace L] [IsTopologicalGroup L] [TopologicalSpace X] in
/-- **PACKAGE I (item 73), principal endpoint.**
`exact_internal_transition_compatibility_iff_defect_trivial`: the chosen internal
representatives satisfy the same exact triple-overlap multiplication law as the ordinary
transitions **iff** the defect is trivial pointwise.  This is the central theorem boundary of
Task XXVIII; no global existence statement is inferred from it (item 75). -/
theorem exact_internal_transition_compatibility_iff_defect_trivial {V : Set X}
    (uij ujk uik : X → L) :
    (∀ x ∈ V, ujk x * uij x = uik x) ↔ (∀ x ∈ V, tripleDefect uij ujk uik x = 1) := by
  constructor
  · intro h x hx
    rw [tripleDefect_apply, h x hx, mul_inv_cancel]
  · intro h x hx
    have := tripleDefect_mul uij ujk uik x
    rw [h x hx, one_mul] at this
    exact this

end InternalProjection

end NullSectorTask28
