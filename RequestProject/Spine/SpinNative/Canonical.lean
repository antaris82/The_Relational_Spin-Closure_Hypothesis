import RequestProject.Spine.SpinNative.GaugeEquivalence

/-!
# Spine / SpinNative : the canonical Spin structure produced by the native constructor

Fifth module of the Spin-native branch.  It isolates the two *provenance* statements that
must not be confused with genuine uniqueness (Task 31, §5.1 and §5.2):

* **canonical production.**  Coherent Spin-native gluing data `S` determine, with no choice
  whatsoever, a Spin structure over their own projection: the underlying gluing data are `S`
  itself and the compatibility with the projected visible datum holds by `rfl`.  This is
  `SpinNative.canonicalSpinStructure`.  In particular no local `SO → Spin` lift is chosen,
  no local section of `ρ` is used, and `Classical.choice` does not occur.

* **native determinism.**  The constructor is a function of `S` alone, and among the Spin
  structures over `project P S` those whose underlying gluing datum *is* `S` form a
  subsingleton, whose unique element is the canonical one
  (`SpinNative.canonicalSpinStructure_unique`, `SpinNative.subsingleton_native_output`).

Neither statement says anything about competitors that carry a *different* underlying
gluing datum with the same projection; those are governed by the residual kernel freedom of
`RequestProject.Spine.SpinNative.KernelTwist` and by the rigidity gate of
`RequestProject.Spine.SpinNative.Rigidity`.

## The object produced

`SpinNative.SpinStructureOver P T` is *the Spin-native presentation* of a Spin structure over
visible transition data `T`: Spin-valued gluing data satisfying the exact Čech cocycle law,
projecting to `T` on the double overlaps.  It is the Spin-native reading of the standard
"coherent family of local Spin lifts"; the two are shown to be the same thing in the
comparison layer (`RequestProject.Spine.Comparison.SpinNativeVsSO`), so this is a
presentation of existing machinery, not a rival theory.  The point of stating it here is that
the field order is reversed: the Spin datum comes first and the visible datum is a derived
constraint, which is what makes the canonical constructor choice-free.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace SpinNative

open CechSpinLift NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}
  {𝓤 : CechCover X ι} {P : InternalProjection L G}

/-- **NEWLY DEFINED (Task 31), principal.**  A Spin structure over the visible transition
data `T`, in the Spin-native presentation: coherent Spin-valued gluing data together with the
proof that they project onto `T` on the double overlaps. -/
structure SpinStructureOver (P : InternalProjection L G) {𝓤 : CechCover X ι}
    (T : VisibleCocycle G 𝓤) where
  /-- The Spin-native gluing data. -/
  data : NativeSpinTransitionData L 𝓤
  /-- They project onto the given visible transition data. -/
  projects : ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, P.proj (data.g i j x) = T.g i j x

namespace SpinStructureOver

variable {T : VisibleCocycle G 𝓤}

/-- Two Spin structures over the same visible data with the same underlying gluing datum are
equal: the remaining field is a proposition. -/
theorem ext {C C' : SpinStructureOver P T} (h : C.data = C'.data) : C = C' := by
  cases C; cases C'; subst h; rfl

/-- **DERIVED (Task 31).**  Any two Spin structures over the *same* visible data have, by
definition, the same projection on the double overlaps.  This is the hypothesis of the
torsor theorem `SpinNative.exists_kerCocycle_twist_eq`. -/
theorem proj_eq (C C' : SpinStructureOver P T) (i j : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₂ i j) : P.proj (C'.data.g i j x) = P.proj (C.data.g i j x) := by
  rw [C.projects i j x hx, C'.projects i j x hx]

/-- **DERIVED_NATIVE (Task 31), the residual freedom in packaged form.**  Every Spin
structure over `T` is a kernel twist of every other one. -/
theorem exists_twist (C C' : SpinStructureOver P T) :
    ∃ ε : KerCocycle P 𝓤, twist C.data ε = C'.data :=
  exists_kerCocycle_twist_eq P C.data C'.data (fun i j _ hx => C.proj_eq C' i j hx)

end SpinStructureOver

/-! ## §5.1 — canonical production -/

/-- **NEWLY DEFINED (Task 31), PRINCIPAL — endpoint U1, canonical native selection.**
Coherent Spin-native gluing data determine a distinguished Spin structure over their own
projection.  No local `SO`-side lift is chosen: the underlying gluing datum is the given `S`
and the projection compatibility is `rfl`. -/
def canonicalSpinStructure (P : InternalProjection L G) (S : NativeSpinTransitionData L 𝓤) :
    SpinStructureOver P (project P S) where
  data := S
  projects _ _ _ _ := rfl

@[simp] theorem canonicalSpinStructure_data (P : InternalProjection L G)
    (S : NativeSpinTransitionData L 𝓤) : (canonicalSpinStructure P S).data = S := rfl

/-! ## §5.2 — native determinism -/

/-- **DERIVED (Task 31), endpoint U2.**  The native constructor is a function of its input:
equal primitive data give the *same* Spin structure. -/
theorem canonicalSpinStructure_congr (P : InternalProjection L G)
    {S S' : NativeSpinTransitionData L 𝓤} (h : S = S') :
    HEq (canonicalSpinStructure P S) (canonicalSpinStructure P S') := by
  subst h; rfl

/-- **DERIVED (Task 31), endpoint U2.**  Among the Spin structures over the projected datum,
the canonical one is the unique one whose underlying gluing datum is the given `S`.  Nothing
is added to `S` and nothing is chosen. -/
theorem canonicalSpinStructure_unique (P : InternalProjection L G)
    (S : NativeSpinTransitionData L 𝓤) (C : SpinStructureOver P (project P S))
    (h : C.data = S) : C = canonicalSpinStructure P S :=
  SpinStructureOver.ext h

/-- **DERIVED (Task 31), endpoint U2 in subsingleton form.**  The native output is
deterministic relative to its input: the Spin structures over `project P S` carrying the
primitive datum `S` form a subsingleton (and it is inhabited, by the canonical one). -/
theorem subsingleton_native_output (P : InternalProjection L G)
    (S : NativeSpinTransitionData L 𝓤) :
    Subsingleton {C : SpinStructureOver P (project P S) // C.data = S} :=
  ⟨fun C C' => Subtype.ext (by
    rw [canonicalSpinStructure_unique P S C.1 C.2, canonicalSpinStructure_unique P S C'.1 C'.2])⟩

/-- **DERIVED (Task 31).**  The native constructor is a retraction: the primitive datum is
recovered from the produced Spin structure.  No information is added and none is lost. -/
theorem canonicalSpinStructure_roundtrip (P : InternalProjection L G)
    (S : NativeSpinTransitionData L 𝓤) : (canonicalSpinStructure P S).data = S := rfl

/-- **DERIVED (Task 31), packaged.**  Conversely, every Spin structure over any visible datum
`T` arises from the canonical constructor applied to its own gluing datum, up to replacing
`T` by the projection: the two presentations agree on the double overlaps. -/
theorem projects_of_spinStructureOver {T : VisibleCocycle G 𝓤} (C : SpinStructureOver P T)
    (i j : ι) {x : X} (hx : x ∈ 𝓤.overlap₂ i j) :
    (project P C.data).g i j x = T.g i j x :=
  C.projects i j x hx

end SpinNative
