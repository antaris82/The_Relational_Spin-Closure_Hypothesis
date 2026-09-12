# Task 30 — Provenance audit: the Spin-native branch versus the standard SO-lift control path

Environment: Lean 4.28.0, Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (unchanged;
`lean-toolchain` and `lake-manifest.json` untouched).  Everything below is read off the actual
source tree; no arrow is inferred.

Arrow classification used throughout:

```
definition                    the arrow is a Lean definition
proved theorem                the arrow is a proved Lean theorem
assumption/data field         the arrow is a field of a structure (i.e. given data)
historical architecture only  the arrow exists only because of the order in which the
                              project was built; nothing mathematical forces it
open                          not present in the project
```

---

## 1. Outcome

**Outcome A.**  A coherent Spin-native branch is available independently of the standard
`SO`-lift branch; it was obtained by *exposing* an object that the project already contained
in group-agnostic form, plus one genuinely new arrow (the projection) and the comparison
theorems.  The projection of coherent Spin-native data has, at theorem level, a trivial
**existing** standard obstruction.  The standard branch is untouched.

---

## 2. Branch B — the Spin-native branch, as it now exists in the source

```
Spin group (local Spin fibre / core)
    SpinCore.SpinGroup                      RequestProject/Spine/E1/SpinGroup.lean:41
        ↓ definition
Spin-valued relational / gluing data on a cover
    SpinNative.NativeSpinTransitionData     RequestProject/Spine/SpinNative/TransitionData.lean
    (= CechSpinLift.VisibleCocycle L 𝓤,     RequestProject/Spine/E2/Cech/Cover.lean)
        ↓ assumption/data field   (fields `continuousOn_g`, `cocycle`)
Spin cocycle coherence
    the field `cocycle` : g̃_ij g̃_jk = g̃_ik on every triple overlap
        ↓ proved theorem
identity and inverse laws are *derived*, not assumed
    SpinNative.native_transition_laws       (re-export of VisibleCocycle.g_self / g_symm)
        ↓ definition
projection through ρ : Spin → SO
    SpinNative.project                      RequestProject/Spine/SpinNative/Projection.lean
        ↓ proved theorem   (field `cocycle` of the result)
standard SO-valued transition data
    CechSpinLift.VisibleCocycle G 𝓤
```

Information loss along the last arrow:

```
SpinNative.proj_ker_mul              proved theorem   ρ(z·u) = ρ(u) for z ∈ ker ρ
SpinNative.project_eq_of_ker_factor  proved theorem   kernel-valued factors are invisible
SpinCore.spinCover_negOneSpin_mul    proved theorem   ρ(−u) = ρ(u)   (inherited, Stage 1.2,
                                     RequestProject/Spine/E1/Topology/LocalSection.lean:506)
```

The Spin-native branch imports **only** `RequestProject.Spine.E2.Cech.Cover` (and, through
it, the Spin/Lorentz projection interface).  It imports no defect, coboundary, obstruction,
refinement or Spin-structure module; this is checked mechanically in
`RequestProject/Spine/Audit/ArchitectureDAG.lean` (check 7).

---

## 3. Branch A — the standard control branch, unchanged

```
SO(=GLor)-valued frame/transition data
    LorentzFrames.LorentzFrameData.transition / .frameCocycle
                                            RequestProject/Spine/Geometry/FrameField.lean:254
    CechSpinLift.VisibleCocycle G 𝓤         RequestProject/Spine/E2/Cech/Cover.lean
        ↓ assumption/data field  (the SO cocycle T is a *parameter* of the next structure)
local Spin lifts
    CechSpinLift.SpinLiftFamily P T         RequestProject/Spine/E2/Cech/LocalLifts.lean
    (existence on whole overlaps is a hypothesis: `IsLiftAdmissible`)
        ↓ definition
triple-overlap defect
    CechSpinLift.SpinLiftFamily.defect      RequestProject/Spine/E2/Cech/Defect.lean
        ↓ proved theorem   (kernel-valued, locally constant, Čech 2-cocycle law)
Čech obstruction class
    CechSpinLift.SpinLiftFamily.obstruction RequestProject/Spine/E2/Cech/Obstruction.lean
        ↓ proved theorem
[c] = 1 ↔ coherent Spin-valued transition data exist
    ...obstruction_eq_trivialClass_iff_exists_coherent
        ↓ proved theorem (Lorentz-frame instance)
[c]_frame = 0 ↔ Nonempty (SpinFrameStructure Φ)
    LorentzFrames.LorentzFrameData.frameObstruction_eq_trivial_iff_spinStructure
                                            RequestProject/Spine/Geometry/SpinStructure.lean
```

Not a single declaration of this branch was modified by Task 30.

---

## 4. The comparison layer (the only place the branches meet)

`RequestProject/Spine/Comparison/SpinNativeVsSO.lean`:

```
SpinNative.nativeLiftFamily                definition      Spin-native data are a family of
                                                           local lifts of their own projection
SpinNative.nativeLiftFamily_defect_eq_one  proved theorem  standard defect ≡ 1
SpinNative.nativeLiftFamily_isCoherent     proved theorem  coherence in the standard sense
SpinNative.projected_obstruction_trivial   proved theorem  [c] = 1 for the tautological family
SpinNative.projected_obstruction_trivial_of_lifts
                                           proved theorem  [c] = 1 for *every* lift family
SpinNative.native_projection_square        proved theorem  the packaged Task-30 square
SpinCore.spin_projected_obstruction_trivial
                                           proved theorem  intrinsic Spin/Lorentz instance
LorentzFrames.SpinFrameStructure.toNative  definition      forgetting the `projects` field
LorentzFrames.project_toNative_eq_transition
                                           proved theorem  projection = frame transition
                                                           (on the overlaps)
LorentzFrames.project_twist                proved theorem  project(ε·S) = project(S)
                                                           (on the overlaps)
LorentzFrames.native_spin_structure_projection
                                           proved theorem  packaged Lorentz-frame endpoint
```

---

## 5. The six provenance questions, answered from the code

### Q1 — Does the fundamental local object already begin on the Spin side?

**Partly yes, and precisely so.**  The earliest genuinely Spin-valued primitive is the
intrinsic spin group `SpinCore.SpinGroup` (`E1/SpinGroup.lean:41`), built inside the Clifford
algebra of the E1 layer, together with `SpinCore.spinCover : SpinGroup →* GLor`
(`E1/SpinCover.lean:42`).  These are *local fibre* data: a group of Spin elements.  They are
prior to, and independent of, every `SO`-valued transition object in the project.

What did **not** exist before Task 30 is a Spin-valued *relational/gluing* object stated
without reference to prior `SO`-data.  This is the distinction insisted on in §4 of the task:
a local Spin fibre is not gluing data, and gluing data are not global coherence.

### Q2 — Where does the standard branch first make `SO` data the primary gluing datum?

At exactly one architectural edge, and it is a *parameter* edge, not a theorem:

```
structure SpinLiftFamily (P : InternalProjection L G) (T : VisibleCocycle G 𝓤)
    RequestProject/Spine/E2/Cech/LocalLifts.lean
```

The visible (`SO`-side) cocycle `T` is a **parameter** of the structure and the Spin-side maps
are a dependent field constrained by `P.IsInternalRepOn (T.g i j) …`.  From this point on the
whole standard chain — `defect`, `Cohomologous`, `ObstructionClass`, `obstruction` — is
indexed by `T`.

The same pattern occurs, independently, in three further places:

* `LorentzFrames.SpinFrameStructure` (`Geometry/SpinStructure.lean`), whose field
  `projects` refers to `Φ.transition`;
* `NullSectorTask29.CompatibleContinuousInternalTransitions`
  (`E2/Descent/CompatibleTransitions.lean`), whose field `proj_v` refers to `S.g`;
* `NullSectorTask28.OrdinaryTransitionSystem` / `TransitionSystem B ι G`
  (`E2/Lift/TransitionSystem.lean:43`), which is `G`-valued by construction.

Before Task 30 these were the *only* Spin-valued gluing objects in the project, so every one
of them depended on prior `SO`-transition data.

### Q3 — Can the Spin-native branch reach coherent global Spin gluing without an `SO → Spin` reconstruction step?

**Yes, and this is now a theorem-level fact.**  `SpinNative.NativeSpinTransitionData` is
coherent Spin-valued gluing data by its own `cocycle` field; `SpinNative.nativeLiftFamily`
exhibits it as a family of local Spin lifts of its own projection, and
`SpinNative.nativeLiftFamily_isCoherent` proves coherence in the sense of the standard branch.

No local section of `ρ`, no lift-admissibility hypothesis (`IsLiftAdmissible`), no
paracompactness/good-cover hypothesis and no kernel adjustment is used.  The import closure
of the Spin-native modules is checked to contain none of the lift/defect/obstruction
machinery.

Caveat (kept explicit): this says the *branch* is available; it does **not** say that such
data exist over a given base.  Existence of a coherent Spin-native datum is an input, exactly
as the existence of a Lorentzian frame datum is an input in the standard branch.

### Q4 — If coherent Spin-native data are projected to `SO`, is the existing standard obstruction provably trivial?

**Yes.**

```lean
theorem SpinNative.projected_obstruction_trivial_of_lifts
    (P : InternalProjection L G) (S : NativeSpinTransitionData L 𝓤)
    (D : SpinLiftFamily P (project P S)) : D.obstruction = trivialClass P 𝓤
```

and its intrinsic instance `SpinCore.spin_projected_obstruction_trivial`.  The obstruction is
the **existing** `CechSpinLift.SpinLiftFamily.obstruction`, not an imitation; its definition
was not touched.  The statement holds for *every* family of local lifts of the projected
data, by the frozen choice-independence theorem `obstruction_lift_independent`.

### Q5 — What information is lost under the projection?

Separated as required, and only what is actually proved is claimed:

* **existence information — not lost.**  The projected data provably admit a coherent Spin
  lift (`native_projection_square`, last conjunct), so the projection retains everything the
  standard branch can detect.
* **choice / kernel-sign information — lost, and this is proved.**
  `SpinNative.project_eq_of_ker_factor`: Spin-native data differing on the overlaps by
  kernel-valued factors have equal projections; `LorentzFrames.project_twist`: the twist of a
  Spin structure by a `{±1}`-valued Čech 1-cocycle has the same projection on the overlaps;
  pointwise, `SpinCore.spinCover_negOneSpin_mul` (inherited): `ρ(−u) = ρ(u)`.
* **global H¹-type freedom — NOT claimed.**  Task 30 proves no classification.  What exists
  in the project is the fixed-cover torsor statement of Stage 1.2/1.3
  (`LorentzFrames.SpinFrameStructure.spinStructure_torsor`, `ratio`/`twist` mutually
  inverse); no H¹ group, no set of isomorphism classes and no bijection with H¹ is
  constructed anywhere, and none was added here.

Also **not** claimed: that a coherent Spin lift reconstructed by the standard branch from
`[c] = 1` is the Spin-native datum one started from.  The standard branch gives existence,
not provenance.

### Q6 — Does the current code accidentally make the `SO`-first path fundamental?

**Yes, but only as API packaging, and the exact edge is identifiable.**  The edge is the
parameter `(T : VisibleCocycle G 𝓤)` of `CechSpinLift.SpinLiftFamily`
(`E2/Cech/LocalLifts.lean`), mirrored by the `projects`/`proj_v` fields of
`SpinFrameStructure` and `CompatibleContinuousInternalTransitions`.

It is **historical architecture, not mathematical necessity**, and the proof is that the
underlying cocycle structure `CechSpinLift.VisibleCocycle` is stated for an *arbitrary*
topological group and never mentions `ρ`: instantiating it at the internal group gives the
Spin-native datum with no change to its definition.  Only the *name* ("visible") encodes the
`SO`-first reading.  Task 30 therefore added no competing structure: `NativeSpinTransitionData`
is an `abbrev` for the existing one, and the only genuinely new arrow is the projection
`SpinNative.project`, which runs `Spin → SO` and needs nothing from the obstruction layer.

The `SO`-first packaging remains mathematically necessary *inside Branch A*: there the whole
point is that the `SO` datum is given first and the Spin datum is being sought.

---

## 6. Stop-condition diagram, as validated

```
   coherent Spin-native data  ───────────────►  coherent Spin lift family
   (NativeSpinTransitionData)   nativeLiftFamily   (IsCoherent, proved)
             │                                            │
             │ ρ  (SpinNative.project)                    │  standard branch
             ▼                                            ▼
   SO-transition data  ─────────────────────────►  [c] = trivialClass  (proved)
   (VisibleCocycle G 𝓤)      obstruction
```

and the independent control branch `SO → local Spin lift → [c]` is unchanged and still
compiles, with all of its endpoints intact.

The genuine Nerve Theorem and the identification with `w₂(TM)` were **not** begun, as
required.
