import RequestProject.Spine.E2.Global.KernelFibres

/-!
# Task 30, Package Q: restriction to one fibre and comparison with the frozen one-fibre
interface

Items 116–121.  Fix a base point `b` and a chart `i` containing it.  Read through the two
charts, the whole global structure becomes *exactly* the inherited one-fibre picture:

| global object | its reading in the chart `i` over `b` |
| --- | --- |
| internal fibre | `Lift` (`fiberEquiv`) |
| ordinary frame fibre | the model frame space `Fm` |
| global right `Lift`-action | right multiplication in `Lift` |
| `internalToFrame` | the inherited one-fibre map `a ↦ proj(a) • ref` |
| kernel action | multiplication by an element of `P.Ker` |

The required principle (item 121) is `internalToFrame_in_chart`: the global projection is,
in every chart, the already certified one-fibre projection — the global construction varies
copies of the reconstructed one-fibre structure, it does not replace it by a new local model.

Chart independence (item 120) is the pair of inherited transformation laws: the internal
coordinate changes by `u_ij(b)` on the left and the ordinary frame coordinate by `g_ij(b)`,
and the two are intertwined by `proj (u_ij) = g_ij`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask30

open NullSectorTask28 NullSectorTask29 Topology

universe u v w t y z

section Comparison

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {P : InternalProjection L G} {S : TransitionSystem B ι G}
  {Fm : Type z} [TopologicalSpace Fm] [MulAction G Fm] {M : OrdinaryFrameModel G Fm}
  {Tot : Type y} [TopologicalSpace Tot]
  (T : CompatibleContinuousInternalTransitions P S) (F : OrdinaryFrameSide S M Tot)

/-- **PACKAGE Q (items 118, 121), principal.**  Read in the chart `i` on both sides, the
global projection is exactly the inherited one-fibre map `a ↦ proj(a) • ref`. -/
theorem internalToFrame_in_chart (i : ι) (x : InternalTotal T)
    (hi : internalBase T x ∈ S.U i)
    (hbi : F.base (internalToFrame T F x) ∈ S.U i) :
    (F.chart i ⟨internalToFrame T F x, hbi⟩).2 = P.proj (icoord T i x) • M.ref := by
  have hx : ipsi T i (⟨internalBase T x, hi⟩, icoord T i x) = x := ipsi_icoord T i x hi
  have himg : internalToFrame T F x
      = F.psi i ((⟨internalBase T x, hi⟩ : ↥(S.U i)), P.proj (icoord T i x) • M.ref) := by
    conv_lhs => rw [← hx]
    rfl
  have hmem : F.base (F.psi i ((⟨internalBase T x, hi⟩ : ↥(S.U i)),
      P.proj (icoord T i x) • M.ref)) ∈ S.U i := F.psi_mem i _
  have := F.chart_psi i ((⟨internalBase T x, hi⟩ : ↥(S.U i)),
    P.proj (icoord T i x) • M.ref) hmem
  have hsub : (⟨internalToFrame T F x, hbi⟩ :
      {t : Tot // F.base t ∈ S.U i}) = ⟨F.psi i ((⟨internalBase T x, hi⟩ : ↥(S.U i)),
        P.proj (icoord T i x) • M.ref), hmem⟩ := Subtype.ext himg
  rw [hsub, this]

/-- **PACKAGE Q (item 119), the fibre-level comparison.**  Over a fixed base point, in a
fixed chart, the internal fibre is `Lift`, the projection to the ordinary frame side is the
inherited one-fibre map, and the global right action is right multiplication. -/
theorem fibre_comparison (i : ι) (b : B) (hb : b ∈ S.U i) (x : ↥(InternalFiber T b))
    (h : L) (hbi : F.base (internalToFrame T F x.1) ∈ S.U i) :
    (F.chart i ⟨internalToFrame T F x.1, hbi⟩).2
        = P.proj (fiberEquiv T i b hb x) • M.ref ∧
      icoord T i (ismul T x.1 h) = fiberEquiv T i b hb x * h := by
  have hxb : internalBase T x.1 = b := x.2
  have hxi : internalBase T x.1 ∈ S.U i := by rw [hxb]; exact hb
  exact ⟨internalToFrame_in_chart T F i x.1 hxi hbi, fiberEquiv_ismul T i b hb x h⟩

/-- **PACKAGE Q (item 120), chart independence — internal side.**  The internal fibre
identification changes by the inherited transition `u_ij(b)`. -/
theorem fibre_chart_independence_internal (i j : ι) (b : B) (hi : b ∈ S.U i) (hj : b ∈ S.U j)
    (x : ↥(InternalFiber T b)) :
    fiberEquiv T j b hj x = uu T i j b hi hj * fiberEquiv T i b hi x :=
  fiberEquiv_chart_change T i j b hi hj x

/-- **PACKAGE Q (item 120), chart independence — ordinary side, inherited.**  The ordinary
frame coordinate changes by `g_ij(b)`. -/
theorem fibre_chart_independence_ordinary (i j : ι) (t : Tot)
    (hi : F.base t ∈ S.U i) (hj : F.base t ∈ S.U j) :
    (F.chart j ⟨t, hj⟩).2 = S.g i j ⟨F.base t, hi, hj⟩ • (F.chart i ⟨t, hi⟩).2 :=
  F.chart_trans i j t hi hj

/-- **PACKAGE Q (item 120), the two are intertwined.**  The internal chart change and the
ordinary chart change correspond exactly through `proj (u_ij) = g_ij`, on the inherited
one-fibre map. -/
theorem chart_change_intertwined (i j : ι) (b : B) (hi : b ∈ S.U i) (hj : b ∈ S.U j) (a : L) :
    P.proj (uu T i j b hi hj * a) • M.ref
      = S.g i j ⟨b, hi, hj⟩ • (P.proj a • M.ref) := by
  rw [map_mul, uu_proj T i j b hi hj, mul_smul]

/-- **PACKAGE Q (item 119), kernel comparison.**  In one fibre, the kernel of the frozen
projection acts by right multiplication and leaves the ordinary image unchanged; this is the
inherited one-fibre kernel action. -/
theorem fibre_kernel_comparison (b : B) (x : ↥(InternalFiber T b)) {a : L} (ha : a ∈ P.Ker) :
    internalBase T (ismul T x.1 a) = b ∧
      internalToFrame T F (ismul T x.1 a) = internalToFrame T F x.1 := by
  have hxb : internalBase T x.1 = b := x.2
  exact ⟨(internalBase_ismul T x.1 a).trans hxb, internalToFrame_ismul_ker T F x.1 ha⟩

end Comparison

end NullSectorTask30
