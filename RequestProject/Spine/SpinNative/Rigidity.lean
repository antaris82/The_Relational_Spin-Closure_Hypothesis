import RequestProject.Spine.SpinNative.Canonical

/-!
# Spine / SpinNative : the rigidity gate for uniqueness of the native Spin structure

Sixth and last module of the Spin-native uniqueness layer.  It states, with nothing hidden,
the **exact conditions** under which the canonical Spin structure of
`RequestProject.Spine.SpinNative.Canonical` is unique among *all* Spin structures over the
same projected visible data, and proves the corresponding implications.

Two conditions are introduced, and they are deliberately different.

* `SpinNative.NoNontrivialKernelTwist P 𝓤` — **every** continuous kernel-valued Čech
  1-cocycle of the cover is pointwise the unit.  This is the strictest condition; it forces
  literal equality of the gluing data on the overlaps.  It is *not* a mild hypothesis: by the
  control `RequestProject.Spine.Controls.SpinNative.KernelTwistControl` it fails as soon as
  the kernel is nontrivial and the cover has two patches with nonempty overlap.

* `SpinNative.KernelTwistsGaugeTrivial P 𝓤` — every continuous kernel-valued Čech 1-cocycle
  of the cover is a coboundary `(δλ)_ij = λ_i λ_j⁻¹`.  This is the mathematically correct,
  `H¹`-type condition: it is the **vanishing of the fixed-cover kernel-twist quotient**
  `Z¹(𝓤; ker ρ) / B¹(𝓤; ker ρ)`, and it gives uniqueness *up to gauge equivalence*, which is
  the strongest form of uniqueness available at the level of Čech gluing data.

**Naming discipline.**  Neither name asserts its own conclusion: each says exactly which
kernel-valued cocycles are being assumed away.  Neither is called `H¹(X;ℤ₂) = 0`: the
condition is about the *fixed cover* and about *continuous* kernel-valued cochains.  The
theorem-level relation to the project's own nerve-level Čech cohomology `Ȟ¹(𝓤;ℤ₂)` is proved
separately, under a connectedness hypothesis, in
`RequestProject.Spine.Comparison.KernelTwistCohomology`; the residual gap to a global
`H¹(X;ℤ₂)` is documented in `TASK31_PROVENANCE.md` and is *not* claimed anywhere.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace SpinNative

open CechSpinLift NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}
  {𝓤 : CechCover X ι} {P : InternalProjection L G}

/-! ## The two rigidity conditions -/

/-- **NEWLY DEFINED (Task 31).**  *No nontrivial kernel twist*: every continuous
kernel-valued Čech 1-cocycle of the cover is the unit at every point of every double
overlap. -/
def NoNontrivialKernelTwist (P : InternalProjection L G) (𝓤 : CechCover X ι) : Prop :=
  ∀ ε : KerCocycle P 𝓤, ε.IsPointwiseTrivial

/-- **NEWLY DEFINED (Task 31), principal — the fixed-cover `H¹`-type gate.**  Every
continuous kernel-valued Čech 1-cocycle of the cover is a coboundary: the fixed-cover
kernel-twist quotient `Z¹(𝓤; ker ρ)/B¹(𝓤; ker ρ)` is trivial. -/
def KernelTwistsGaugeTrivial (P : InternalProjection L G) (𝓤 : CechCover X ι) : Prop :=
  ∀ ε : KerCocycle P 𝓤, ε.IsGaugeTrivial

theorem KernelTwistsGaugeTrivial.of_noNontrivialKernelTwist
    (h : NoNontrivialKernelTwist P 𝓤) : KernelTwistsGaugeTrivial P 𝓤 :=
  fun ε => KerCocycle.isGaugeTrivial_of_isPointwiseTrivial (h ε)

/-! ### Non-vacuity of the conditions -/

/-- **DERIVED (Task 31), non-vacuity.**  A one-patch cover (more generally, a cover with a
subsingleton index type) admits no nontrivial kernel twist at all: the diagonal law
`ε_ii = 1` is already forced by the cocycle law. -/
theorem noNontrivialKernelTwist_of_subsingleton_index [Subsingleton ι] :
    NoNontrivialKernelTwist P 𝓤 := by
  intro ε i j x hx
  have hij : i = j := Subsingleton.elim i j
  subst hij
  exact ε.e_self i hx.1

/-- **DERIVED (Task 31), non-vacuity.**  If the projection is injective (trivial kernel) no
kernel twist exists either. -/
theorem noNontrivialKernelTwist_of_trivial_kernel (hker : ∀ z ∈ P.Ker, z = 1) :
    NoNontrivialKernelTwist P 𝓤 :=
  fun ε i j x hx => hker _ ((ε.isKer i j).2 x hx)

/-! ## §5.3 — uniqueness among all Spin structures over the same projected data -/

/-- **DERIVED_NATIVE (Task 31), PRINCIPAL — endpoint U3, strict form.**  Under the strict
rigidity condition, any Spin structure over the same visible data as the native one has the
*same gluing data on every double overlap*.

Literal equality of the two records is deliberately **not** asserted: the gluing maps are
unconstrained off the overlaps, where they carry no information. -/
theorem data_eq_on_overlaps_of_noNontrivialKernelTwist
    (hrig : NoNontrivialKernelTwist P 𝓤) {T : VisibleCocycle G 𝓤}
    (C C' : SpinStructureOver P T) (i j : ι) {x : X} (hx : x ∈ 𝓤.overlap₂ i j) :
    C'.data.g i j x = C.data.g i j x := by
  have hproj : ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j,
      P.proj (C'.data.g i j x) = P.proj (C.data.g i j x) := fun i j x hx => C.proj_eq C' i j hx
  have h := hrig (ratio P hproj) i j x hx
  have h' : C'.data.g i j x * (C.data.g i j x)⁻¹ = 1 := h
  exact mul_inv_eq_one.1 h'

/-- **DERIVED_NATIVE (Task 31), PRINCIPAL — endpoint U3, gauge form.**  Under the
fixed-cover `H¹`-type gate, *every* Spin structure over the same projected visible data is
gauge equivalent to every other one — in particular to the canonical native one. -/
theorem gaugeEquiv_of_kernelTwistsGaugeTrivial
    (hgate : KernelTwistsGaugeTrivial P 𝓤) {T : VisibleCocycle G 𝓤}
    (C C' : SpinStructureOver P T) : GaugeEquiv P C.data C'.data := by
  obtain ⟨ε, hε⟩ := C.exists_twist C'
  have hgt := hgate ε
  refine (gaugeEquiv_iff_twist_isGaugeTrivial C.data C'.data).2 ⟨ε, hgt, fun i j x _ => ?_⟩
  rw [hε]

/-- **DERIVED_NATIVE (Task 31), endpoint U3 for the native structure.**  Under the gate,
every Spin structure over the projection of coherent Spin-native data `S` is gauge
equivalent to the canonical native one. -/
theorem gaugeEquiv_canonical_of_kernelTwistsGaugeTrivial
    (hgate : KernelTwistsGaugeTrivial P 𝓤) (S : NativeSpinTransitionData L 𝓤)
    (C : SpinStructureOver P (project P S)) : GaugeEquiv P S C.data :=
  gaugeEquiv_of_kernelTwistsGaugeTrivial hgate (canonicalSpinStructure P S) C

/-! ## Endpoint U4 — the gauge quotient is a subsingleton -/

/-- **NEWLY DEFINED (Task 31).**  The set of Spin structures over fixed visible data, modulo
gauge equivalence of their gluing data.  This is the object whose triviality is the honest
form of "the Spin structure is unique". -/
def GaugeClass (P : InternalProjection L G) {𝓤 : CechCover X ι} (T : VisibleCocycle G 𝓤) :
    Type _ :=
  Quot (fun C C' : SpinStructureOver P T => GaugeEquiv P C.data C'.data)

/-- The gauge class of a Spin structure. -/
def gaugeClassOf {T : VisibleCocycle G 𝓤} (C : SpinStructureOver P T) : GaugeClass P T :=
  Quot.mk _ C

/-- **DERIVED_NATIVE (Task 31), PRINCIPAL — endpoint U4.**  Under the fixed-cover `H¹`-type
gate there is at most one Spin structure over given visible transition data, up to gauge
equivalence. -/
theorem subsingleton_gaugeClass (hgate : KernelTwistsGaugeTrivial P 𝓤)
    (T : VisibleCocycle G 𝓤) : Subsingleton (GaugeClass P T) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quot.ind with
  | _ C =>
    induction b using Quot.ind with
    | _ C' => exact Quot.sound (gaugeEquiv_of_kernelTwistsGaugeTrivial hgate C C')

/-- **DERIVED_NATIVE (Task 31), packaged endpoint of the uniqueness layer.**  For coherent
Spin-native gluing data `S`:

1. `S` determines a canonical Spin structure over its own projection, with no lift choice
   (U1) and with `S` recoverable from it (U2);
2. every Spin structure over the same projected data is a kernel twist of it — the residual
   freedom is exactly `Z¹(𝓤; ker ρ)` (the negative control);
3. under the strict rigidity condition the competitors coincide with it on every double
   overlap (U3, strict);
4. under the fixed-cover `H¹`-type gate all competitors are gauge equivalent to it, and the
   gauge quotient is a subsingleton (U3–U4). -/
theorem native_uniqueness_summary (P : InternalProjection L G)
    (S : NativeSpinTransitionData L 𝓤) :
    (canonicalSpinStructure P S).data = S ∧
    (∀ C : SpinStructureOver P (project P S), ∃ ε : KerCocycle P 𝓤, twist S ε = C.data) ∧
    (NoNontrivialKernelTwist P 𝓤 → ∀ C : SpinStructureOver P (project P S), ∀ i j,
        ∀ x ∈ 𝓤.overlap₂ i j, C.data.g i j x = S.g i j x) ∧
    (KernelTwistsGaugeTrivial P 𝓤 →
        (∀ C : SpinStructureOver P (project P S), GaugeEquiv P S C.data) ∧
        Subsingleton (GaugeClass P (project P S))) :=
  ⟨rfl,
   fun C => (canonicalSpinStructure P S).exists_twist C,
   fun hrig C i j _ hx =>
     data_eq_on_overlaps_of_noNontrivialKernelTwist hrig (canonicalSpinStructure P S) C i j hx,
   fun hgate =>
     ⟨fun C => gaugeEquiv_canonical_of_kernelTwistsGaugeTrivial hgate S C,
      subsingleton_gaugeClass hgate (project P S)⟩⟩

end SpinNative
