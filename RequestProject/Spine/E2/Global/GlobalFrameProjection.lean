import RequestProject.Spine.E2.Global.InternalGroupAction

/-!
# Task 30, Packages L, M and N: the global projection to the ordinary frame total space

**Hard target C, second half.**

Package L (items 89–95) defines the candidate local map

`localProj_i : U i × Lift → U i × FrameModel`, `(b, a) ↦ (b, proj(a) • ref)`,

with the *inherited* one-fibre map from the internal model to the ordinary frame model: the
projection `proj : Lift → Gvis` of the frozen internal projection acting on the inherited
reference model frame.  No new map is invented (item 89).

The compatibility proof uses **exactly** `proj (u_ij) = g_ij` (item 92): the internal chart
change `a ↦ u_ij(b) * a` is carried to the ordinary chart change `f ↦ g_ij(b) • f`.  Hence the
local maps descend to

`internalToFrame : InternalTotal → FrameTotal`,

which lies over the base (`internalToFrame_over_base`, item 95), is continuous
(`continuous_internalToFrame`, Package M, item 99) — proved chartwise, not by an opaque
quotient lemma (item 98) — and is equivariant (`internalToFrame_equivariant`, Package N,
item 102) for the *right* internal action upstairs and the inherited *right* visible action
downstairs, along `proj`.  The formula is the mathematically correct one for the derived
action convention; it has not been adjusted for cosmetic reasons (item 103).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask30

open NullSectorTask28 NullSectorTask29 Topology

universe u v w t y z

section FrameProjection

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {P : InternalProjection L G} {S : TransitionSystem B ι G}
  {Fm : Type z} [TopologicalSpace Fm] [MulAction G Fm] {M : OrdinaryFrameModel G Fm}
  {Tot : Type y} [TopologicalSpace Tot]

namespace OrdinaryFrameSide

variable (F : OrdinaryFrameSide S M Tot)

/-- **PACKAGE K (item 87), derived from the inherited chart transition law.**  Two ordinary
local parametrizations describe the same point exactly through the ordinary transition. -/
theorem psi_trans (i j : ι) (b : B) (hi : b ∈ S.U i) (hj : b ∈ S.U j) (f : Fm) :
    F.psi j (⟨b, hj⟩, S.g i j ⟨b, hi, hj⟩ • f) = F.psi i (⟨b, hi⟩, f) := by
  set x : Tot := F.psi i (⟨b, hi⟩, f) with hxdef
  have hbx : F.base x = b := F.base_psi i _
  have hxi : F.base x ∈ S.U i := hbx ▸ hi
  have hxj : F.base x ∈ S.U j := hbx ▸ hj
  have hci : F.chart i ⟨x, hxi⟩ = (⟨b, hi⟩, f) := F.chart_psi i _ hxi
  have hct := F.chart_trans i j x hxi hxj
  have hpt : (⟨F.base x, hxi, hxj⟩ : ↥(S.U i ∩ S.U j)) = ⟨b, hi, hj⟩ := Subtype.ext hbx
  rw [hpt, hci] at hct
  have hfst : (F.chart j ⟨x, hxj⟩).1 = (⟨b, hj⟩ : ↥(S.U j)) :=
    Subtype.ext ((F.chart_base j ⟨x, hxj⟩).trans hbx)
  have hchart : F.chart j ⟨x, hxj⟩ = (⟨b, hj⟩, S.g i j ⟨b, hi, hj⟩ • f) :=
    Prod.ext hfst hct
  have := F.psi_chart j x hxj
  rw [hchart] at this
  exact this

/-- **PACKAGE K.**  The inherited fibrewise right action, read in a local
parametrization. -/
theorem ract_psi (i : ι) (b : B) (hi : b ∈ S.U i) (f : Fm) (k : G) :
    F.ract (F.psi i (⟨b, hi⟩, f)) k = F.psi i (⟨b, hi⟩, M.ract f k) := by
  set x : Tot := F.psi i (⟨b, hi⟩, f) with hxdef
  have hbx : F.base x = b := F.base_psi i _
  have hxi : F.base x ∈ S.U i := hbx ▸ hi
  have hci : F.chart i ⟨x, hxi⟩ = (⟨b, hi⟩, f) := F.chart_psi i _ hxi
  have hbr : F.base (F.ract x k) = b := (F.base_ract x k).trans hbx
  have hri : F.base (F.ract x k) ∈ S.U i := hbr ▸ hi
  have hsnd : (F.chart i ⟨F.ract x k, hri⟩).2 = M.ract f k := by
    rw [F.chart_ract i x k hxi hri, hci]
  have hfst : (F.chart i ⟨F.ract x k, hri⟩).1 = (⟨b, hi⟩ : ↥(S.U i)) :=
    Subtype.ext ((F.chart_base i ⟨F.ract x k, hri⟩).trans hbr)
  have hchart : F.chart i ⟨F.ract x k, hri⟩ = (⟨b, hi⟩, M.ract f k) := Prod.ext hfst hsnd
  have := F.psi_chart i (F.ract x k) hri
  rw [hchart] at this
  exact this.symm

end OrdinaryFrameSide

variable (T : CompatibleContinuousInternalTransitions P S) (F : OrdinaryFrameSide S M Tot)

/-! ## Package L — the local candidate map and its descent -/

/-- **PACKAGE L (items 89, 90), principal definition.**  The candidate map on a tagged local
representative: the inherited one-fibre map `a ↦ proj(a) • ref` read in the ordinary chart of
the same index. -/
def toFramePre (x : InternalPre S L) : Tot :=
  F.psi (preIdx x) (⟨prePt x, prePt_mem x⟩, P.proj (preElt x) • M.ref)

/-- **PACKAGE L (items 91, 92), principal.**  Glue-equivalent internal representatives have
ordinary images representing the same point.  **The proof uses exactly `proj (u_ij) = g_ij`.**
-/
theorem toFramePre_glueRel {x y : InternalPre S L} (h : InternalGlueRel T x y) :
    toFramePre (P := P) F x = toFramePre (P := P) F y := by
  obtain ⟨i, ⟨b, hi⟩, a⟩ := x
  obtain ⟨j, ⟨b', hj⟩, a'⟩ := y
  have hb : b' = b := glueRel_pt_eq T h
  subst hb
  rw [glueRel_iff_of_pt] at h
  show F.psi i (⟨b', hi⟩, P.proj a • M.ref) = F.psi j (⟨b', hj⟩, P.proj a' • M.ref)
  rw [h, map_mul, uu_proj T i j b' hi hj, mul_smul]
  exact (F.psi_trans i j b' hi hj (P.proj a • M.ref)).symm

/-- **PACKAGE L (item 93), principal definition.**  The global map to the ordinary frame
total space. -/
def internalToFrame : InternalTotal T → Tot :=
  Quotient.lift (toFramePre (P := P) F) fun _ _ h => toFramePre_glueRel T F h

@[simp] theorem internalToFrame_ipsi (i : ι) (b : B) (hi : b ∈ S.U i) (a : L) :
    internalToFrame T F (ipsi T i (⟨b, hi⟩, a)) = F.psi i (⟨b, hi⟩, P.proj a • M.ref) := rfl

/-- **PACKAGE L (items 94, 95), REQUIRED ENDPOINT `internalToFrame_over_base`.**  The global
map lies over the base. -/
theorem internalToFrame_over_base (x : InternalTotal T) :
    F.base (internalToFrame T F x) = internalBase T x := by
  induction x using iq_inductionOn with
  | h y =>
    obtain ⟨i, ⟨b, hi⟩, a⟩ := y
    exact F.base_psi i _

/-! ## Package M — continuity -/

/-- **PACKAGE M (items 96–99), REQUIRED ENDPOINT `continuous_internalToFrame`.**  The global
map is continuous.  The proof is chartwise: in every chart it is the already continuous
one-fibre projection composed with the inherited ordinary parametrization. -/
theorem continuous_internalToFrame : Continuous (internalToFrame T F) := by
  rw [continuous_internalTotal_iff]
  intro i
  have hsmul : Continuous fun p : ↥(S.U i) × L => P.proj p.2 • M.ref :=
    M.continuous_smul.comp ((P.continuous_proj.comp continuous_snd).prodMk continuous_const)
  exact (F.continuous_psi i).comp (continuous_fst.prodMk hsmul)

/-! ## Package N — equivariance -/

/-- **PACKAGE N (items 100–103), REQUIRED ENDPOINT `internalToFrame_equivariant`.**

The derived global internal action is a **right** action; the corresponding ordinary action
is therefore the inherited **right** action of the visible group on the ordinary frame total
space, and the equivariance formula is

`internalToFrame (x • a) = internalToFrame x • proj a`.

This is the mathematically correct statement for the derived convention; it has not been
altered to obtain a left-action formula (item 103). -/
theorem internalToFrame_equivariant (x : InternalTotal T) (a : L) :
    internalToFrame T F (ismul T x a) = F.ract (internalToFrame T F x) (P.proj a) := by
  induction x using iq_inductionOn with
  | h y =>
    obtain ⟨i, ⟨b, hi⟩, c⟩ := y
    show F.psi i (⟨b, hi⟩, P.proj (c * a) • M.ref)
        = F.ract (F.psi i (⟨b, hi⟩, P.proj c • M.ref)) (P.proj a)
    rw [F.ract_psi i b hi (P.proj c • M.ref) (P.proj a), M.ract_smul, M.ract_ref, map_mul,
      mul_smul]

/-- **PACKAGE N.**  In particular the ordinary right action is induced through `proj`: the
image of a fibre orbit is the corresponding ordinary orbit. -/
theorem internalToFrame_ract_range (x : InternalTotal T) (k : G) :
    ∃ a : L, F.ract (internalToFrame T F x) k = internalToFrame T F (ismul T x a) := by
  obtain ⟨a, ha⟩ := P.surjective_proj k
  exact ⟨a, by rw [internalToFrame_equivariant, ha]⟩

end FrameProjection

end NullSectorTask30
