import RequestProject.Spine.E2.Lift.LocalInternalRepresentatives

/-!
# Task 28, Packages E, F and G: the exact kernel-valued ambiguity

**HARD TARGET B.**

Two continuous internal representatives of the *same* ordinary map are compared.  With the
inherited multiplication convention the relative factor is taken on the left,

`ε x = v x * (u x)⁻¹`,   so that   `v x = ε x * u x`,

because the inherited triple-overlap law of Task XXVII is also written with the new factor
on the left (`g_ik = g_jk * g_ij`).

Proved here:

* the relative factor lies in the kernel (item 42) and is continuous (item 43);
* it is repackaged as a continuous kernel-valued map on the domain (item 44);
* `v = ε * u` (item 45) and `ε` is unique (items 46, 47);
* the converse: multiplying a representative by any continuous kernel-valued function gives
  another representative of the same ordinary map (item 48);
* consequently the continuous internal representatives of one ordinary map, when they
  exist at all, form a free and transitive space under continuous kernel-valued functions
  (item 49), stated elementarily, without torsor machinery;
* Package F (items 50–55): a continuous kernel-valued function is locally constant, is
  constant on a connected domain, and — the required negative control — need *not* be a
  single sign on a disconnected domain;
* Package G (items 56–61): the identity normalization `u_ii = 1` is always available, the
  inverse of a representative represents the inverse ordinary map, and an independently
  chosen representative of the inverse differs from it by a unique continuous kernel-valued
  function.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask28

universe u v w

namespace InternalProjection

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G]

/-! ## Kernel-valued functions on a domain -/

/-- **NEWLY DEFINED (item 44).**  A continuous kernel-valued function on the subset `V`,
stored as a map into `L` together with the two properties.  The repackaging into a genuine
map `V → Ker` is `toKerFun` below. -/
def IsKerFunOn {X : Type w} [TopologicalSpace X] (P : InternalProjection L G) (V : Set X)
    (e : X → L) : Prop :=
  ContinuousOn e V ∧ ∀ x ∈ V, e x ∈ P.Ker

variable {X : Type w} [TopologicalSpace X] (P : InternalProjection L G)

theorem IsKerFunOn.continuousOn {V : Set X} {e : X → L} (h : P.IsKerFunOn V e) :
    ContinuousOn e V := h.1

theorem IsKerFunOn.mem {V : Set X} {e : X → L} (h : P.IsKerFunOn V e) {x : X} (hx : x ∈ V) :
    e x ∈ P.Ker := h.2 x hx

theorem IsKerFunOn.mono {V V' : Set X} {e : X → L} (h : P.IsKerFunOn V e) (hsub : V' ⊆ V) :
    P.IsKerFunOn V' e :=
  ⟨h.1.mono hsub, fun x hx => h.2 x (hsub hx)⟩

theorem isKerFunOn_one (V : Set X) : P.IsKerFunOn V (fun _ => 1) :=
  ⟨continuousOn_const, fun _ _ => Subgroup.one_mem _⟩

theorem IsKerFunOn.mul {V : Set X} {e f : X → L} (he : P.IsKerFunOn V e)
    (hf : P.IsKerFunOn V f) : P.IsKerFunOn V (fun x => e x * f x) :=
  ⟨he.1.mul hf.1, fun x hx => Subgroup.mul_mem _ (he.2 x hx) (hf.2 x hx)⟩

theorem IsKerFunOn.inv {V : Set X} {e : X → L} (he : P.IsKerFunOn V e) :
    P.IsKerFunOn V (fun x => (e x)⁻¹) :=
  ⟨he.1.inv, fun x hx => Subgroup.inv_mem _ (he.2 x hx)⟩

/-- **PACKAGE E (item 44).**  The repackaging of a continuous kernel-valued function as a
continuous map into the kernel subgroup with its inherited subspace topology. -/
def toKerFun {V : Set X} {e : X → L} (h : P.IsKerFunOn V e) : V → P.Ker :=
  fun x => ⟨e (x : X), h.2 (x : X) x.2⟩

@[simp] theorem toKerFun_val {V : Set X} {e : X → L} (h : P.IsKerFunOn V e) (x : V) :
    ((P.toKerFun h x : P.Ker) : L) = e (x : X) := rfl

/-- **PACKAGE E (item 43/44).**  The repackaged kernel-valued function is continuous. -/
theorem continuous_toKerFun {V : Set X} {e : X → L} (h : P.IsKerFunOn V e) :
    Continuous (P.toKerFun h) := by
  exact Continuous.subtype_mk (continuousOn_iff_continuous_restrict.1 h.1) _

/-! ## Package E — the difference of two representatives (items 41–49) -/

/-- **NEWLY DEFINED (item 41).**  The pointwise relative factor of two internal
representatives, with the inherited left-multiplication convention. -/
def relFactor (u v : X → L) : X → L := fun x => v x * (u x)⁻¹

omit [TopologicalSpace L] [IsTopologicalGroup L] [TopologicalSpace X] in
@[simp] theorem relFactor_apply (u v : X → L) (x : X) : relFactor u v x = v x * (u x)⁻¹ := rfl

omit [TopologicalSpace L] [IsTopologicalGroup L] [TopologicalSpace X] in
/-- **PACKAGE E (item 45).**  The defining identity of the relative factor. -/
theorem relFactor_mul_self (u v : X → L) (x : X) : relFactor u v x * u x = v x := by
  simp [relFactor]

/-- **PACKAGE E (item 42), principal.**  The relative factor of two internal representatives
of the same ordinary map lies in the kernel. -/
theorem relFactor_mem_ker {g : X → G} {V : Set X} {u v : X → L}
    (hu : P.IsInternalRepOn g V u) (hv : P.IsInternalRepOn g V v) {x : X} (hx : x ∈ V) :
    relFactor u v x ∈ P.Ker := by
  have h : P.proj (v x * (u x)⁻¹) = 1 := by
    rw [map_mul, map_inv, hu.2 x hx, hv.2 x hx, mul_inv_cancel]
  exact h

/-- **PACKAGE E (items 42, 43), principal.**  The relative factor is a continuous
kernel-valued function on the common domain. -/
theorem relFactor_isKerFunOn {g : X → G} {V : Set X} {u v : X → L}
    (hu : P.IsInternalRepOn g V u) (hv : P.IsInternalRepOn g V v) :
    P.IsKerFunOn V (relFactor u v) :=
  ⟨hv.1.mul hu.1.inv, fun _ hx => P.relFactor_mem_ker hu hv hx⟩

omit [TopologicalSpace L] [IsTopologicalGroup L] [TopologicalSpace X] in
/-- **PACKAGE E (item 46).**  Uniqueness of the relative factor. -/
theorem relFactor_eq_of_mul {V : Set X} {u v e : X → L} (h : ∀ x ∈ V, v x = e x * u x)
    {x : X} (hx : x ∈ V) : e x = relFactor u v x := by
  rw [relFactor_apply, h x hx, mul_inv_cancel_right]

/-- **PACKAGE E (item 47), principal endpoint — HARD TARGET B.**
`continuous_internal_reps_difference_unique_kerSign`: two continuous internal
representatives of the same ordinary map differ by a *unique* continuous kernel-valued
function, on the nose. -/
theorem continuous_internal_reps_difference_unique_kerSign {g : X → G} {V : Set X}
    {u v : X → L} (hu : P.IsInternalRepOn g V u) (hv : P.IsInternalRepOn g V v) :
    ∃! e : V → P.Ker, Continuous e ∧ ∀ x : V, v (x : X) = ((e x : P.Ker) : L) * u (x : X) := by
  refine ⟨P.toKerFun (P.relFactor_isKerFunOn hu hv),
    ⟨P.continuous_toKerFun _, fun x => ?_⟩, ?_⟩
  · simp
  · rintro e ⟨-, he⟩
    funext x
    refine Subtype.ext ?_
    have hx : ((e x : P.Ker) : L) = relFactor u v (x : X) := by
      rw [relFactor_apply, he x, mul_inv_cancel_right]
    simpa [P.toKerFun_val] using hx

/-- **PACKAGE E (item 48), principal.**  Converse: modifying a continuous internal
representative by any continuous kernel-valued function gives another continuous internal
representative of the *same* ordinary map. -/
theorem isInternalRepOn_kerFun_mul {g : X → G} {V : Set X} {u e : X → L}
    (hu : P.IsInternalRepOn g V u) (he : P.IsKerFunOn V e) :
    P.IsInternalRepOn g V (fun x => e x * u x) := by
  refine ⟨he.1.mul hu.1, fun x hx => ?_⟩
  rw [map_mul, (P.mem_Ker_iff).1 (he.2 x hx), one_mul, hu.2 x hx]

/-- **PACKAGE E (item 49), principal.**  Freeness and transitivity, stated elementarily:
every two continuous internal representatives of one ordinary map are related by exactly one
continuous kernel-valued function, and every continuous kernel-valued function relates the
given representative to another one. -/
theorem internal_reps_free_transitive {g : X → G} {V : Set X} {u : X → L}
    (hu : P.IsInternalRepOn g V u) :
    (∀ v : X → L, P.IsInternalRepOn g V v →
        ∃ e : X → L, P.IsKerFunOn V e ∧ ∀ x ∈ V, v x = e x * u x) ∧
      (∀ e : X → L, P.IsKerFunOn V e → P.IsInternalRepOn g V (fun x => e x * u x)) ∧
      (∀ e f : X → L, P.IsKerFunOn V e → P.IsKerFunOn V f →
        (∀ x ∈ V, e x * u x = f x * u x) → ∀ x ∈ V, e x = f x) := by
  refine ⟨fun v hv => ⟨relFactor u v, P.relFactor_isKerFunOn hu hv, fun x _ =>
      (relFactor_mul_self u v x).symm⟩,
    fun e he => P.isInternalRepOn_kerFun_mul hu he, fun e f _ _ h x hx => ?_⟩
  exact mul_right_cancel (h x hx)

/-! ## Package F — local constancy of the ambiguity (items 50–55) -/

/-- **PACKAGE F (item 51), principal.**  A continuous kernel-valued function is locally
constant: the kernel carries the inherited discrete topology. -/
theorem isLocallyConstant_toKerFun {V : Set X} {e : X → L} (h : P.IsKerFunOn V e) :
    IsLocallyConstant (P.toKerFun h) :=
  (IsLocallyConstant.iff_continuous _).2 (P.continuous_toKerFun h)

/-- **PACKAGE F (item 52), principal.**  On a connected domain a continuous kernel-valued
function is constant. -/
theorem toKerFun_const_of_connected {V : Set X} {e : X → L} (h : P.IsKerFunOn V e)
    (hV : IsPreconnected V) {x y : X} (hx : x ∈ V) (hy : y ∈ V) : e x = e y := by
  haveI hconn : PreconnectedSpace V := Subtype.preconnectedSpace hV
  have := (P.isLocallyConstant_toKerFun h).apply_eq_of_preconnectedSpace
    (⟨x, hx⟩ : V) (⟨y, hy⟩ : V)
  exact congrArg (fun z : P.Ker => (z : L)) this

/-- **PACKAGE F (items 53–55), required negative control.**  On a disconnected domain the
kernel ambiguity need *not* be one single sign: whenever the kernel has a nontrivial element
and the domain is split by two disjoint open sets, there is a continuous kernel-valued
function taking different values.  Connectedness is therefore indispensable in the previous
theorem. -/
theorem exists_nonconstant_kerFun_of_disconnected {V A B : Set X} (hA : IsOpen A)
    (hB : IsOpen B) (hcover : V ⊆ A ∪ B) (hdisj : Disjoint A B) {a b : X}
    (ha : a ∈ V ∩ A) (hb : b ∈ V ∩ B) {z : L} (hz : z ∈ P.Ker) (hz1 : z ≠ 1) :
    ∃ e : X → L, P.IsKerFunOn V e ∧ e a ≠ e b := by
  classical
  refine ⟨fun x => if x ∈ A then z else 1, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    rcases hcover hx with hxA | hxB
    · refine ContinuousWithinAt.congr_of_eventuallyEq (f := fun _ : X => z)
        continuousWithinAt_const ?_ ?_
      · filter_upwards [nhdsWithin_le_nhds (hA.mem_nhds hxA)] with y hy
        simp [hy]
      · simp [hxA]
    · have hxA : x ∉ A := fun hxA => (Set.disjoint_left.1 hdisj) hxA hxB
      refine ContinuousWithinAt.congr_of_eventuallyEq (f := fun _ : X => (1 : L))
        continuousWithinAt_const ?_ ?_
      · filter_upwards [nhdsWithin_le_nhds (hB.mem_nhds hxB)] with y hy
        have : y ∉ A := fun hyA => (Set.disjoint_left.1 hdisj) hyA hy
        simp [this]
      · simp [hxA]
  · intro x _
    by_cases hxA : x ∈ A
    · simpa [hxA] using hz
    · simp [hxA]
  · have hbA : b ∉ A := fun hbA => (Set.disjoint_left.1 hdisj) hbA hb.2
    simp [ha.2, hbA, hz1]

/-! ## Package G — identity and inverse representatives (items 56–61) -/

/-- **PACKAGE G (item 56).**  The identity normalization is always available: on any domain
the constant unit is a continuous internal representative of the constant ordinary unit —
in particular of the inherited identity law `g_ii = 1`. -/
theorem isInternalRepOn_one (V : Set X) :
    P.IsInternalRepOn (fun _ : X => (1 : G)) V (fun _ => 1) :=
  ⟨continuousOn_const, fun _ _ => map_one P.proj⟩

/-- **PACKAGE G (items 57, 58), principal.**  The inverse of a continuous internal
representative of `g` is a continuous internal representative of `g⁻¹`; with the inherited
inverse law this is the representative of `g_ji` induced by a representative of `g_ij`. -/
theorem isInternalRepOn_inv {g : X → G} {V : Set X} {u : X → L}
    (hu : P.IsInternalRepOn g V u) :
    P.IsInternalRepOn (fun x => (g x)⁻¹) V (fun x => (u x)⁻¹) :=
  ⟨hu.1.inv, fun x hx => by rw [map_inv, hu.2 x hx]⟩

/-- **PACKAGE G (item 59), principal.**  An independently chosen continuous internal
representative of the inverse ordinary map differs from the inverse representative by a
unique continuous kernel-valued function. -/
theorem inv_rep_difference_unique {g : X → G} {V : Set X} {u w : X → L}
    (hu : P.IsInternalRepOn g V u) (hw : P.IsInternalRepOn (fun x => (g x)⁻¹) V w) :
    ∃! e : V → P.Ker, Continuous e ∧
      ∀ x : V, w (x : X) = ((e x : P.Ker) : L) * (u (x : X))⁻¹ :=
  P.continuous_internal_reps_difference_unique_kerSign (P.isInternalRepOn_inv hu) hw

end InternalProjection

end NullSectorTask28
