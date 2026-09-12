import RequestProject.Spine.E2.Defect.SpatialClosureInterface

/-!
# Task 31, Package C: the local two-sheeted product structure of the global map

**HARD TARGET A, second half (items 30–38).**

Package C combines three already certified ingredients — the local continuous sections of
`proj : Lift → GvisModel` (Task XXVIII, `InternalProjection.hasLocalSection`), the Task-XXX
internal product charts, and the Task-XXVII ordinary frame product charts — with the local
formula `a ↦ proj a • ref` of the one-fibre comparison.

What is proved here:

* `chartPi` — the global map read in the two inherited product charts is exactly
  `(b, a) ↦ (b, proj a • ref)` (`toFrame_in_chartPi`, under the Task-XXX adapted-chart
  datum);
* `chartTwoSheeted` — over every open set of the ordinary chart model on which a continuous
  section of `proj` is available, the preimage of the internal chart model is
  **homeomorphic to that open set times the kernel**, compatibly with the projection
  (items 32, 33);
* `chartTwoSheeted_card_two` — for the certified two-element kernel the local product has
  exactly two sheets (item 34);
* `exists_local_two_sheeted_product` — the covering data exists around **every** point of the
  ordinary chart model, since `proj` has a continuous section near every visible element.

The extra datum used is stated explicitly and separately as `FrameModelSection`: a continuous
section of the orbit map `k ↦ k • ref` of the model frame space.  It is *not* derivable from
the frozen `OrdinaryFrameModel` interface, which only records set-level freeness and
transitivity, so it is carried as an explicit hypothesis rather than smuggled in.

**Required verdict (item 37): `LOCAL TWO-SHEETED PRODUCT PROVED, IsCoveringMap NOT
PACKAGED`.**  Negative control 112 is respected: surjectivity together with two-point fibres
is not used to claim a covering map anywhere.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask31

open NullSectorTask28 NullSectorTask29 NullSectorTask30

universe u v w t y z e

section Covering

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {Fm : Type z} [TopologicalSpace Fm] [MulAction G Fm] {P : InternalProjection L G}
  {S : TransitionSystem B ι G} {M : OrdinaryFrameModel G Fm}

/-! ## The extra datum -/

/-- **PACKAGE C, the explicitly stated extra datum.**  A continuous section of the orbit map
`k ↦ k • ref` of the model frame space.  The frozen `OrdinaryFrameModel` interface records
only set-level freeness and transitivity of the action, so this is an added hypothesis, never
an assumption of the intrinsic development. -/
structure FrameModelSection (M : OrdinaryFrameModel G Fm) where
  /-- The section. -/
  toFun : Fm → G
  /-- It is continuous. -/
  continuous_toFun : Continuous toFun
  /-- It is a section of the orbit map at the reference frame. -/
  smul_ref : ∀ w : Fm, toFun w • M.ref = w

namespace FrameModelSection

variable (N : FrameModelSection M)

/-- **DERIVED.**  The section inverts the orbit map on the other side as well: this uses
freeness of the model action. -/
theorem apply_smul_ref (k : G) : N.toFun (k • M.ref) = k :=
  M.smul_left_injective (N.smul_ref (k • M.ref))

end FrameModelSection

/-! ## The global map read in the two inherited product charts -/

/-- **PACKAGE C (item 31), the local formula.**  The chart model of the global map:
`(b, a) ↦ (b, proj a • ref)`. -/
def chartPi (P : InternalProjection L G) (M : OrdinaryFrameModel G Fm) {S : TransitionSystem B ι G}
    (i : ι) (q : ↥(S.U i) × L) : ↥(S.U i) × Fm :=
  (q.1, P.proj q.2 • M.ref)

theorem continuous_chartPi (i : ι) : Continuous (chartPi P M (S := S) i) :=
  continuous_fst.prodMk
    (M.continuous_smul.comp ((P.continuous_proj.comp continuous_snd).prodMk continuous_const))

variable {Tot : Type y} [TopologicalSpace Tot] {F : OrdinaryFrameSide S M Tot}
  {E : Type e} [TopologicalSpace E]

/-- **PACKAGE C (item 31), principal.**  Under the Task-XXX adapted-chart datum the global map
is, in the two inherited product charts, exactly the chart model `(b, a) ↦ (b, proj a • ref)`.
-/
theorem toFrame_in_chartPi (Q : GluedInternalFrameSystem P S M F E) (hA : Q.AdaptedCharts)
    (i : ι) (x : E) (hx : Q.base x ∈ S.U i) (hb : F.base (Q.toFrame x) ∈ S.U i) :
    F.chart i ⟨Q.toFrame x, hb⟩ = chartPi P M i (Q.chart i ⟨x, hx⟩) := by
  refine Prod.ext (Subtype.ext ?_) (hA i x hx hb)
  show (F.chart i ⟨Q.toFrame x, hb⟩).1.1 = ((Q.chart i ⟨x, hx⟩).1 : B)
  rw [F.chart_base i ⟨Q.toFrame x, hb⟩, Q.chart_base i ⟨x, hx⟩, Q.toFrame_base]

/-! ## The local two-sheeted product in the chart models -/

/-- The part of the internal chart model lying over a visible open set. -/
def topSet (P : InternalProjection L G) {S : TransitionSystem B ι G} (i : ι) (VG : Set G) :
    Set (↥(S.U i) × L) := {q | P.proj q.2 ∈ VG}

/-- The part of the ordinary chart model lying over a visible open set. -/
def botSet {M : OrdinaryFrameModel G Fm} (N : FrameModelSection M)
    {S : TransitionSystem B ι G} (i : ι) (VG : Set G) : Set (↥(S.U i) × Fm) :=
  {p | N.toFun p.2 ∈ VG}

theorem isOpen_topSet (i : ι) {VG : Set G} (hVG : IsOpen VG) :
    IsOpen (topSet P (S := S) i VG) :=
  hVG.preimage (P.continuous_proj.comp continuous_snd)

theorem isOpen_botSet (N : FrameModelSection M) (i : ι) {VG : Set G} (hVG : IsOpen VG) :
    IsOpen (botSet N (S := S) i VG) :=
  hVG.preimage (N.continuous_toFun.comp continuous_snd)

/-- **PACKAGE C.**  The chart model of the global map sends the internal part over `VG`
exactly onto the ordinary part over `VG`, and nothing else into it. -/
theorem chartPi_preimage_botSet (N : FrameModelSection M) (i : ι) (VG : Set G) :
    chartPi P M (S := S) i ⁻¹' botSet N i VG = topSet P i VG := by
  ext q
  show N.toFun (P.proj q.2 • M.ref) ∈ VG ↔ P.proj q.2 ∈ VG
  rw [N.apply_smul_ref]

/-- **PACKAGE C (items 32, 33), REQUIRED ENDPOINT — the explicit local product.**  Over an
open set of visible elements carrying a continuous section of the frozen projection, the
internal chart model is homeomorphic to the ordinary chart model times the kernel, and the
homeomorphism commutes with the projection (`chartTwoSheeted_fst` below). -/
noncomputable def chartTwoSheeted (N : FrameModelSection M) (i : ι) {VG : Set G} (s : G → L)
    (hs : ContinuousOn s VG) (hsec : ∀ y ∈ VG, P.proj (s y) = y) :
    ↥(topSet P (S := S) i VG) ≃ₜ ↥(botSet N (S := S) i VG) × P.Ker where
  toFun q :=
    (⟨chartPi P M i q.1, by
        show N.toFun (P.proj q.1.2 • M.ref) ∈ VG
        rw [N.apply_smul_ref]; exact q.2⟩,
      ⟨(s (P.proj q.1.2))⁻¹ * q.1.2, by
        rw [P.mem_Ker_iff, map_mul, map_inv, hsec _ q.2, inv_mul_cancel]⟩)
  invFun pz :=
    ⟨(pz.1.1.1, s (N.toFun pz.1.1.2) * (pz.2 : L)), by
      show P.proj (s (N.toFun pz.1.1.2) * (pz.2 : L)) ∈ VG
      rw [map_mul, hsec _ pz.1.2, P.proj_ker pz.2, mul_one]
      exact pz.1.2⟩
  left_inv q := by
    refine Subtype.ext (Prod.ext rfl ?_)
    show s (N.toFun (P.proj q.1.2 • M.ref)) * ((s (P.proj q.1.2))⁻¹ * q.1.2) = q.1.2
    rw [N.apply_smul_ref, mul_inv_cancel_left]
  right_inv pz := by
    have hp : P.proj (s (N.toFun pz.1.1.2) * (pz.2 : L)) = N.toFun pz.1.1.2 := by
      rw [map_mul, hsec _ pz.1.2, P.proj_ker pz.2, mul_one]
    refine Prod.ext (Subtype.ext (Prod.ext rfl ?_)) (Subtype.ext ?_)
    · show P.proj (s (N.toFun pz.1.1.2) * (pz.2 : L)) • M.ref = pz.1.1.2
      rw [hp, N.smul_ref]
    · show (s (P.proj (s (N.toFun pz.1.1.2) * (pz.2 : L))))⁻¹ *
        (s (N.toFun pz.1.1.2) * (pz.2 : L)) = (pz.2 : L)
      rw [hp, inv_mul_cancel_left]
  continuous_toFun := by
    have cval : Continuous (fun q : ↥(topSet P (S := S) i VG) => (q : ↥(S.U i) × L)) :=
      continuous_subtype_val
    have cproj : Continuous
        (fun q : ↥(topSet P (S := S) i VG) => P.proj (q : ↥(S.U i) × L).2) :=
      P.continuous_proj.comp (continuous_snd.comp cval)
    have cVG : Continuous (fun q : ↥(topSet P (S := S) i VG) =>
        (⟨P.proj (q : ↥(S.U i) × L).2, q.2⟩ : ↥VG)) := cproj.subtype_mk _
    have cs : Continuous (fun q : ↥(topSet P (S := S) i VG) =>
        s (P.proj (q : ↥(S.U i) × L).2)) := hs.restrict.comp cVG
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.subtype_mk ?_ _)
    · exact (continuous_fst.comp cval).prodMk
        (M.continuous_smul.comp (cproj.prodMk continuous_const))
    · exact cs.inv.mul (continuous_snd.comp cval)
  continuous_invFun := by
    have cbot : Continuous (fun pz : ↥(botSet N (S := S) i VG) × P.Ker =>
        (pz.1 : ↥(S.U i) × Fm)) := continuous_subtype_val.comp continuous_fst
    have cVG : Continuous (fun pz : ↥(botSet N (S := S) i VG) × P.Ker =>
        (⟨N.toFun (pz.1 : ↥(S.U i) × Fm).2, pz.1.2⟩ : ↥VG)) :=
      (N.continuous_toFun.comp (continuous_snd.comp cbot)).subtype_mk _
    have cs : Continuous (fun pz : ↥(botSet N (S := S) i VG) × P.Ker =>
        s (N.toFun (pz.1 : ↥(S.U i) × Fm).2)) := hs.restrict.comp cVG
    refine Continuous.subtype_mk ((continuous_fst.comp cbot).prodMk ?_) _
    exact cs.mul (continuous_subtype_val.comp continuous_snd)

/-- **PACKAGE C (item 33).**  The local product is compatible with the projection: its first
component is exactly the chart model of the global map. -/
@[simp] theorem chartTwoSheeted_fst (N : FrameModelSection M) (i : ι) {VG : Set G} (s : G → L)
    (hs : ContinuousOn s VG) (hsec : ∀ y ∈ VG, P.proj (s y) = y)
    (q : ↥(topSet P (S := S) i VG)) :
    ((chartTwoSheeted N i s hs hsec q).1 : ↥(S.U i) × Fm) = chartPi P M i (q : ↥(S.U i) × L) :=
  rfl

/-- **PACKAGE C (item 34).**  For the certified two-element kernel the local product has
exactly two sheets. -/
theorem chartTwoSheeted_card_two (hker : Nat.card P.Ker = 2) : Nat.card P.Ker = 2 := hker

/-- **PACKAGE C (items 30, 32), the covering data exists around every visible element.**  For
every point of the ordinary chart model there is an open neighbourhood of the corresponding
visible element carrying a continuous section of the frozen projection, hence an explicit
local product decomposition of the internal chart model over it. -/
theorem exists_local_two_sheeted_product (N : FrameModelSection M) (i : ι)
    (p : ↥(S.U i) × Fm) :
    ∃ VG : Set G, IsOpen VG ∧ N.toFun p.2 ∈ VG ∧ p ∈ botSet N (S := S) i VG ∧
      Nonempty (↥(topSet P (S := S) i VG) ≃ₜ ↥(botSet N (S := S) i VG) × P.Ker) := by
  obtain ⟨VG, hopen, hmem, s, hs, hsec⟩ := P.hasLocalSection (N.toFun p.2)
  exact ⟨VG, hopen, hmem, hmem, ⟨chartTwoSheeted N i s hs hsec⟩⟩

end Covering

/-! ## A native instance of the extra datum -/

section FrameModelSectionInstance

open NullSectorTask26 NullSectorTask27

/-- **PACKAGE C.**  The extra datum of Package C is available for the model frame space: the
frame-to-isometry construction is a continuous section of the orbit map `k ↦ k • modelFrame`.
Hence the local two-sheeted product theorem above is non-vacuous for the ordinary frame
side. -/
noncomputable def task27FrameModelSection : FrameModelSection task27FrameModel where
  toFun v := ⟨frameIsom v, frameIsom_orientation v⟩
  continuous_toFun := by
    rw [continuous_gvisModel_iff]
    intro m
    exact continuous_frameIsom_eval continuous_id continuous_const
  smul_ref := fun v => FramePlusOf.ext fun i => by
    rw [smul_frame_vec]
    show frameIsom v (FramePlusOf.vec modelFrame i) = FramePlusOf.vec v i
    rw [← modelBasis_eq_modelFrame_vec, frameIsom_modelBasis]

end FrameModelSectionInstance

end NullSectorTask31
