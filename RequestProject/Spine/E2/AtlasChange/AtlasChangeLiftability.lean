import RequestProject.Spine.E2.AtlasChange.FamilyLiftability

/-!
# Task 32, Packages G and J: direct liftability under an ordinary chart gauge, and the
transformation of the kernel defect

**HARD TARGET B (items 55–60, 74–78).**

The Task-XXXI control already warns that direct liftability need **not** be invariant under an
arbitrary ordinary chart gauge (item 55, negative control 115).  This module isolates the
exact extra hypothesis under which it *is* invariant, and computes the transformation of the
kernel defect.

* `gaugedSystem` — the ordinary transition system obtained from `S` by an arbitrary continuous
  `G`-valued chart gauge `h`, with the conjugation law `g'_ij = h_j · g_ij · h_i⁻¹` **built
  in** and the three transition laws *proved*, not assumed.
* `ofOrdinary_atlas_eq_gaugedSystem` — two presentations of a joint ordinary atlas really are
  related in exactly this way (this is where Package B's derived law is consumed).
* `InternallyLiftableOrdinaryGauge` (item 57) — the chart gauge itself admits continuous
  internal representatives compatible with `proj`.
* `internalLiftable_gaugedSystem` (item 58, REQUIRED ENDPOINT) — the strongest correct
  transfer theorem: an internally liftable ordinary chart gauge preserves direct liftability.
* Package J (items 75–78): the exact transformation of a triple defect under an internally
  lifted ordinary chart change (`tripleDefect_conjugation`: the defect is **unchanged**,
  because the kernel is central), and the exact effect of changing the auxiliary internal
  lifts of the gauge (`conjugation_kernel_change`: only by a kernel element).

Firewall item 8 is respected throughout: nowhere is it assumed that an ordinary chart gauge
has an internal lift.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask32

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask29 NullSectorTask31

universe u v w t s

/-! ## An extensionality lemma for abstract transition systems -/

section Ext

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G]

/-- Two ordinary transition systems with the same cover and the same transition maps are
equal; all remaining fields are propositions. -/
theorem transitionSystem_ext {S S' : TransitionSystem B ι G} (hU : S.U = S'.U)
    (hg : HEq S.g S'.g) : S = S' := by
  cases S with
  | mk U o c g cg gs gy gt =>
    cases S' with
    | mk U' o' c' g' cg' gs' gy' gt' =>
      cases hU
      cases hg
      rfl

end Ext

/-! ## The gauged ordinary transition system -/

section Gauged

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {L : Type w} [Group L] [TopologicalSpace L]
  [IsTopologicalGroup L]

/-- **PACKAGE G, principal definition.**  The ordinary transition system obtained from `S` by
an arbitrary continuous chart gauge `h`, following the derived Package-B law
`g'_ij(b) = h_j(b) · g_ij(b) · h_i(b)⁻¹`.  The identity, inverse and triple-overlap laws are
proved. -/
def gaugedSystem (S : TransitionSystem B ι G) (h : ∀ i, ↥(S.U i) → G)
    (hcont : ∀ i, Continuous (h i)) : TransitionSystem B ι G where
  U := S.U
  isOpen_U := S.isOpen_U
  cover := S.cover
  g := fun i j x => h j ⟨(x : B), x.2.2⟩ * S.g i j x * (h i ⟨(x : B), x.2.1⟩)⁻¹
  continuous_g := fun i j => by
    refine (((hcont j).comp (Continuous.subtype_mk continuous_subtype_val _)).mul
      (S.continuous_g i j)).mul ?_
    exact ((hcont i).comp (Continuous.subtype_mk continuous_subtype_val _)).inv
  g_self := fun i x => by
    show h i ⟨(x : B), x.2.2⟩ * S.g i i x * (h i ⟨(x : B), x.2.1⟩)⁻¹ = 1
    rw [S.g_self i x, mul_one, mul_inv_cancel]
  g_symm := fun i j b hh hh' => by
    show h i ⟨b, hh'.2⟩ * S.g j i ⟨b, hh'⟩ * (h j ⟨b, hh'.1⟩)⁻¹
      = (h j ⟨b, hh.2⟩ * S.g i j ⟨b, hh⟩ * (h i ⟨b, hh.1⟩)⁻¹)⁻¹
    rw [S.g_symm i j b hh hh']
    simp [mul_inv_rev, mul_assoc]
  g_trans := fun i j k b h₁ h₂ h₃ => by
    show h k ⟨b, h₁.2⟩ * S.g i k ⟨b, h₁⟩ * (h i ⟨b, h₁.1⟩)⁻¹
      = (h k ⟨b, h₂.2⟩ * S.g j k ⟨b, h₂⟩ * (h j ⟨b, h₂.1⟩)⁻¹) *
        (h j ⟨b, h₃.2⟩ * S.g i j ⟨b, h₃⟩ * (h i ⟨b, h₃.1⟩)⁻¹)
    rw [S.g_trans i j k b h₁ h₂ h₃]
    simp only [mul_assoc, inv_mul_cancel_left]

@[simp] theorem gaugedSystem_U (S : TransitionSystem B ι G) (h : ∀ i, ↥(S.U i) → G)
    (hcont : ∀ i, Continuous (h i)) (i : ι) : (gaugedSystem S h hcont).U i = S.U i := rfl

@[simp] theorem gaugedSystem_g (S : TransitionSystem B ι G) (h : ∀ i, ↥(S.U i) → G)
    (hcont : ∀ i, Continuous (h i)) (i j : ι) (x : ↥(S.U i ∩ S.U j)) :
    (gaugedSystem S h hcont).g i j x
      = h j ⟨(x : B), x.2.2⟩ * S.g i j x * (h i ⟨(x : B), x.2.1⟩)⁻¹ := rfl

/-- **PACKAGE G (item 57), principal definition.**  An ordinary chart gauge is *internally
liftable* when it admits continuous internal representatives compatible with `proj`.  Nothing
asserts that this holds; the Task-XXXI control shows that it can fail. -/
def InternallyLiftableOrdinaryGauge (P : InternalProjection L G) (S : TransitionSystem B ι G)
    (h : ∀ i, ↥(S.U i) → G) : Prop :=
  ∃ H : ∀ i, ↥(S.U i) → L, (∀ i, Continuous (H i)) ∧ ∀ (i : ι) (x : ↥(S.U i)),
    P.proj (H i x) = h i x

/-- **PACKAGE G (item 58), REQUIRED ENDPOINT — the strongest correct transfer theorem.**  If
the ordinary chart gauge itself admits suitable internal lifts, then direct liftability is
preserved: the internal transitions are conjugated by the internal lifts of the gauge. -/
theorem internalLiftable_gaugedSystem {P : InternalProjection L G} {S : TransitionSystem B ι G}
    {h : ∀ i, ↥(S.U i) → G} (hcont : ∀ i, Continuous (h i)) (hlift : InternalLiftable P S)
    (hgauge : InternallyLiftableOrdinaryGauge P S h) :
    InternalLiftable P (gaugedSystem S h hcont) := by
  obtain ⟨T⟩ := hlift
  obtain ⟨H, hHc, hHp⟩ := hgauge
  refine ⟨{ v := fun i j x => H j ⟨(x : B), x.2.2⟩ * T.v i j x * (H i ⟨(x : B), x.2.1⟩)⁻¹
            continuous_v := fun i j => ?_
            proj_v := fun i j x => ?_
            v_self := fun i x => ?_
            v_symm := fun i j x => ?_
            v_trans := fun i j k x => ?_ }⟩
  · refine (((hHc j).comp (Continuous.subtype_mk continuous_subtype_val _)).mul
      (T.continuous_v i j)).mul ?_
    exact ((hHc i).comp (Continuous.subtype_mk continuous_subtype_val _)).inv
  · rw [map_mul, map_mul, map_inv, hHp, hHp, T.proj_v]
    rfl
  · rw [T.v_self i x, mul_one, mul_inv_cancel]
  · show H i ⟨(x : B), x.2.1⟩ * T.v j i (swapPt S x) * (H j ⟨(x : B), x.2.2⟩)⁻¹
      = (H j ⟨(x : B), x.2.2⟩ * T.v i j x * (H i ⟨(x : B), x.2.1⟩)⁻¹)⁻¹
    rw [T.v_symm i j x]
    simp [mul_inv_rev, mul_assoc]
  · show (H k ⟨(x : B), _⟩ * T.v j k (S.incJK i j k x) * (H j ⟨(x : B), _⟩)⁻¹) *
        (H j ⟨(x : B), _⟩ * T.v i j (S.incIJ i j k x) * (H i ⟨(x : B), _⟩)⁻¹)
      = H k ⟨(x : B), _⟩ * T.v i k (S.incIK i j k x) * (H i ⟨(x : B), _⟩)⁻¹
    rw [← T.v_trans i j k x]
    simp only [mul_assoc, inv_mul_cancel_left]

end Gauged

/-! ## Package J: the exact transformation of the kernel defect -/

section DefectTransformation

variable {G : Type v} [Group G] [TopologicalSpace G] {L : Type w} [Group L]
  [TopologicalSpace L] [IsTopologicalGroup L] (P : InternalProjection L G)

/-- **PACKAGE J (items 75, 77), REQUIRED ENDPOINT.**  The exact transformation of a triple
defect under an ordinary chart change with auxiliary internal lifts `Hᵢ`.  The defect is
**unchanged** — the conjugating factors cancel and the kernel element commutes with
everything.  This law is *derived* from centrality of the kernel, not guessed from
conventional cohomology (item 75). -/
theorem tripleDefect_conjugation {uij ujk uik Hi Hj Hk d : L} (hd : d ∈ P.proj.ker)
    (hu : ujk * uij = d * uik) :
    (Hk * ujk * Hj⁻¹) * (Hj * uij * Hi⁻¹) = d * (Hk * uik * Hi⁻¹) := by
  have hcomm : d * Hk = Hk * d := P.ker_central d hd Hk
  calc (Hk * ujk * Hj⁻¹) * (Hj * uij * Hi⁻¹)
      = Hk * (ujk * uij) * Hi⁻¹ := by simp only [mul_assoc, inv_mul_cancel_left]
    _ = Hk * (d * uik) * Hi⁻¹ := by rw [hu]
    _ = (Hk * d) * uik * Hi⁻¹ := by simp only [mul_assoc]
    _ = (d * Hk) * uik * Hi⁻¹ := by rw [hcomm]
    _ = d * (Hk * uik * Hi⁻¹) := by simp only [mul_assoc]

/-- **PACKAGE J (item 78).**  Two auxiliary internal lifts of the *same* ordinary chart gauge
differ by kernel elements. -/
theorem gauge_lift_difference_mem_ker {H H' : L} (hproj : P.proj H' = P.proj H) :
    H' * H⁻¹ ∈ P.proj.ker := by
  simp [MonoidHom.mem_ker, map_mul, map_inv, hproj]

/-- **PACKAGE J (item 78), REQUIRED ENDPOINT.**  Changing the auxiliary internal lifts of an
ordinary chart gauge changes the conjugated internal transition only by the already-known
kernel equivalence: the comparison shifts by `z_j · z_i⁻¹` with `z_i, z_j` in the kernel. -/
theorem conjugation_kernel_change {u Hi Hj zi zj : L} (hzi : zi ∈ P.proj.ker) :
    (zj * Hj) * u * (zi * Hi)⁻¹ = (zj * zi⁻¹) * (Hj * u * Hi⁻¹) := by
  have hzi' : zi⁻¹ ∈ P.proj.ker := Subgroup.inv_mem _ hzi
  have hcomm : ∀ l : L, zi⁻¹ * l = l * zi⁻¹ := fun l => P.ker_central _ hzi' l
  calc (zj * Hj) * u * (zi * Hi)⁻¹
      = zj * (Hj * u * (Hi⁻¹ * zi⁻¹)) := by simp only [mul_assoc, mul_inv_rev]
    _ = zj * ((Hj * u * Hi⁻¹) * zi⁻¹) := by simp only [mul_assoc]
    _ = zj * (zi⁻¹ * (Hj * u * Hi⁻¹)) := by rw [hcomm]
    _ = (zj * zi⁻¹) * (Hj * u * Hi⁻¹) := by simp only [mul_assoc]

end DefectTransformation

/-! ## The joint-atlas specialization -/

section JointTransfer

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : BareMetricOrientedFamily B E} {ι : Type t}
  {σ : Type s} (J : JointOrdinaryAtlas F σ ι)
  {L' : Type} [Group L'] [TopologicalSpace L'] [IsTopologicalGroup L']
  (P : InternalProjection L' GvisModel)

/-- **PACKAGE G, the bridge.**  Two presentations of a joint ordinary atlas are related by
exactly the gauged-system construction, with the Package-B chart gauges. -/
theorem ofOrdinary_atlas_eq_gaugedSystem (s t : σ) :
    ofOrdinary (ordinarySystem (J.atlas t))
      = gaugedSystem (ofOrdinary (ordinarySystem (J.atlas s))) (J.gauge s t)
        (J.continuous_gauge s t) := by
  refine transitionSystem_ext rfl (heq_of_eq ?_)
  funext i j x
  exact J.transition_gauge_law s t i j (x : B) x.2

/-- **PACKAGE G (items 58, 24), REQUIRED ENDPOINT at presentation level.**  If one presentation
of a joint ordinary atlas is directly liftable and the ordinary chart gauge to a second
presentation is internally liftable, the second presentation is directly liftable too. -/
theorem directAtlasLiftable_gauge_transfer (s t : σ) (hs : DirectAtlasLiftable P (J.atlas s))
    (hgauge : InternallyLiftableOrdinaryGauge P
      (ofOrdinary (ordinarySystem (J.atlas s))) (J.gauge s t)) :
    DirectAtlasLiftable P (J.atlas t) := by
  rw [DirectAtlasLiftable, OrdinaryInternalLiftable, ofOrdinary_atlas_eq_gaugedSystem J s t]
  exact internalLiftable_gaugedSystem (J.continuous_gauge s t) hs hgauge

end JointTransfer

end NullSectorTask32
