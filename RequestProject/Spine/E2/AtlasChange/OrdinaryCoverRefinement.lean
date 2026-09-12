import RequestProject.Spine.E2.AtlasChange.OrdinaryAtlasChange

/-!
# Task 32, Package D: ordinary cover refinement of an ordinary atlas presentation

**HARD TARGET A, second half (items 34–41).**

This is a refinement of the **ordinary frame atlas itself**, and is deliberately *not* the
Task-XXVIII internal-candidate refinement (negative control 118): its data are a new index
type, a reindexing map, smaller open sets, the inclusion proofs, and the *restricted local
trivializations* — no internal representative occurs anywhere.

Proved here:

* `restrictTriv` — restriction of an inherited local trivialization, and
  `transitionOn_restrictTriv`: the transition transformation is *unchanged* by restriction;
* `OrdinaryCoverRefinement.atlas` — the refined ordinary atlas presentation of the **same**
  bare family (item 36);
* `OrdinaryCoverRefinement.transitionFun_eq` — the exact restriction formula (item 37);
* `OrdinaryCoverRefinement.idRefinement` and `atlas_idRefinement` (item 38, identity);
* `OrdinaryCoverRefinement.comp` and `atlas_comp` (item 38, composition), together with
  compatibility of the transition law under repeated refinement;
* `commonRefinementLeft` / `commonRefinementRight` — the intersection construction
  `U i ∩ U' i'` (items 39, 40), exhibiting both atlases as ordinary presentations on one
  common ordinary refinement of the same underlying family.

No general bundle-atlas equivalence machinery is imported (item 41).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask32

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask31

universe u v t t' k k'

section Restrict

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : BareMetricOrientedFamily B E}

/-- **PACKAGE D (item 35).**  Restriction of an inherited local fibre trivialization to a
smaller set. -/
def restrictTriv {U V : Set B} (Φ : F.LocalFibreTriv U) (h : V ⊆ U) : F.LocalFibreTriv V where
  iso := fun b => Φ.iso ⟨(b : B), h b.2⟩
  orientation_preserving := fun b => Φ.orientation_preserving ⟨(b : B), h b.2⟩

omit [TopologicalSpace B] in
@[simp] theorem restrictTriv_iso {U V : Set B} (Φ : F.LocalFibreTriv U) (h : V ⊆ U)
    (b : ↥V) : (restrictTriv Φ h).iso b = Φ.iso ⟨(b : B), h b.2⟩ := rfl

omit [TopologicalSpace B] in
/-- **PACKAGE D (item 37).**  Restricting the charts does not change the transition
transformation. -/
theorem transitionOn_restrictTriv {U W V X : Set B} (Φ : F.LocalFibreTriv U)
    (Ψ : F.LocalFibreTriv W) (hV : V ⊆ U) (hX : X ⊆ W) (b : ↥(V ∩ X)) :
    transitionOn (restrictTriv Φ hV) (restrictTriv Ψ hX) b
      = transitionOn Φ Ψ ⟨(b : B), hV b.2.1, hX b.2.2⟩ := rfl

omit [TopologicalSpace B] in
theorem restrictTriv_self {U : Set B} (Φ : F.LocalFibreTriv U) :
    restrictTriv Φ (subset_refl U) = Φ := rfl

omit [TopologicalSpace B] in
theorem restrictTriv_comp {U V W : Set B} (Φ : F.LocalFibreTriv U) (h : V ⊆ U) (h' : W ⊆ V) :
    restrictTriv (restrictTriv Φ h) h' = restrictTriv Φ (h'.trans h) := rfl

end Restrict

/-! ## Ordinary cover refinements -/

section Refinement

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {F : BareMetricOrientedFamily B E} {ι : Type t}
  {κ : Type k} {κ' : Type k'}

/-- **PACKAGE D (items 34–35), principal definition.**  An *ordinary cover refinement* of an
ordinary atlas presentation: a new index type, a reindexing map, smaller open domains covering
the base, and the inclusion proofs.  The refined local trivializations are then *derived* by
restriction — they are not extra data. -/
structure OrdinaryCoverRefinement (A : OrdinaryAtlasPresentation F ι) (κ : Type k) where
  /-- The reindexing map. -/
  r : κ → ι
  /-- The refined domains. -/
  V : κ → Set B
  /-- Each refined domain is open. -/
  isOpen_V : ∀ a, IsOpen (V a)
  /-- The refined domains still cover the base. -/
  cover_V : ∀ b : B, ∃ a, b ∈ V a
  /-- Each refined domain sits inside the corresponding original domain. -/
  subset : ∀ a, V a ⊆ A.U (r a)

namespace OrdinaryCoverRefinement

variable {A : OrdinaryAtlasPresentation F ι} (R : OrdinaryCoverRefinement A κ)

/-- **PACKAGE D (item 36), principal construction.**  The refined ordinary atlas presentation
of the **same** bare family. -/
noncomputable def atlas : OrdinaryAtlasPresentation F κ where
  U := R.V
  isOpen_U := R.isOpen_V
  cover := R.cover_V
  triv := fun a => restrictTriv (A.triv (R.r a)) (R.subset a)
  continuousOn_overlap := by
    intro a c
    have horig := A.continuousOn_overlap (R.r a) (R.r c)
    have hincl : ContinuousOn
        (fun p : ↥(R.V a) × Model => ((⟨(p.1 : B), R.subset a p.1.2⟩ : ↥(A.U (R.r a))), p.2))
        {p : ↥(R.V a) × Model | (p.1 : B) ∈ R.V c} :=
      Continuous.continuousOn
        ((Continuous.subtype_mk (continuous_subtype_val.comp continuous_fst) _).prodMk
          continuous_snd)
    have hmaps : Set.MapsTo
        (fun p : ↥(R.V a) × Model => ((⟨(p.1 : B), R.subset a p.1.2⟩ : ↥(A.U (R.r a))), p.2))
        {p : ↥(R.V a) × Model | (p.1 : B) ∈ R.V c}
        {p : ↥(A.U (R.r a)) × Model | (p.1 : B) ∈ A.U (R.r c)} :=
      fun p hp => R.subset c hp
    refine ((horig.comp hincl hmaps).congr ?_)
    intro p hp
    have hp' : (p.1 : B) ∈ R.V c := hp
    have hp'' : (p.1 : B) ∈ A.U (R.r c) := R.subset c hp'
    rw [Function.comp_apply,
      ovMap_apply (U := A.U) (chart := fun i b => fibreChart (A.triv i) b)
        ((⟨(p.1 : B), R.subset a p.1.2⟩ : ↥(A.U (R.r a))), p.2) hp'',
      ovMap_apply (U := R.V)
        (chart := fun a b => fibreChart (restrictTriv (A.triv (R.r a)) (R.subset a)) b) p hp']
    rfl

@[simp] theorem atlas_U (a : κ) : R.atlas.U a = R.V a := rfl

@[simp] theorem atlas_triv (a : κ) :
    R.atlas.triv a = restrictTriv (A.triv (R.r a)) (R.subset a) := rfl

/-- **PACKAGE D (item 37), REQUIRED ENDPOINT — the exact restriction formula.**  The refined
ordinary transition maps are literally the original ones, read at the same base point. -/
theorem transitionFun_eq (a c : κ) (x : ↥(R.V a ∩ R.V c)) :
    R.atlas.transitionFun a c x
      = A.transitionFun (R.r a) (R.r c)
        ⟨(x : B), R.subset a x.2.1, R.subset c x.2.2⟩ := rfl

/-- **PACKAGE D (item 38), identity refinement. -/
def idRefinement (A : OrdinaryAtlasPresentation F ι) : OrdinaryCoverRefinement A ι where
  r := id
  V := A.U
  isOpen_V := A.isOpen_U
  cover_V := A.cover
  subset := fun _ => subset_refl _

@[simp] theorem atlas_idRefinement (A : OrdinaryAtlasPresentation F ι) :
    (idRefinement A).atlas = A := rfl

/-- **PACKAGE D (item 38), composition of refinements. -/
def comp (R₁ : OrdinaryCoverRefinement A κ) (R' : OrdinaryCoverRefinement R₁.atlas κ') :
    OrdinaryCoverRefinement A κ' where
  r := R₁.r ∘ R'.r
  V := R'.V
  isOpen_V := R'.isOpen_V
  cover_V := R'.cover_V
  subset := fun a => (R'.subset a).trans (R₁.subset (R'.r a))

@[simp] theorem atlas_comp (R₁ : OrdinaryCoverRefinement A κ)
    (R' : OrdinaryCoverRefinement R₁.atlas κ') : (R₁.comp R').atlas = R'.atlas := rfl

/-- **PACKAGE D (item 38), compatibility of the transition law under repeated refinement. -/
theorem transitionFun_comp (R₁ : OrdinaryCoverRefinement A κ)
    (R' : OrdinaryCoverRefinement R₁.atlas κ') (a c : κ') (x : ↥(R'.V a ∩ R'.V c)) :
    R'.atlas.transitionFun a c x
      = A.transitionFun (R₁.r (R'.r a)) (R₁.r (R'.r c))
        ⟨(x : B), (R₁.comp R').subset a x.2.1, (R₁.comp R').subset c x.2.2⟩ := rfl

end OrdinaryCoverRefinement

/-! ## Common ordinary refinement of two presentations -/

variable {ι' : Type t'}

/-- **PACKAGE D (item 39), the intersection construction.**  The first atlas, refined by the
intersections `U i ∩ U' i'`. -/
def commonRefinementLeft (A : OrdinaryAtlasPresentation F ι)
    (A' : OrdinaryAtlasPresentation F ι') : OrdinaryCoverRefinement A (ι × ι') where
  r := Prod.fst
  V := fun p => A.U p.1 ∩ A'.U p.2
  isOpen_V := fun p => (A.isOpen_U p.1).inter (A'.isOpen_U p.2)
  cover_V := fun b => by
    obtain ⟨i, hi⟩ := A.cover b
    obtain ⟨i', hi'⟩ := A'.cover b
    exact ⟨(i, i'), hi, hi'⟩
  subset := fun _ => Set.inter_subset_left

/-- **PACKAGE D (item 39).**  The second atlas, refined by the same intersections. -/
def commonRefinementRight (A : OrdinaryAtlasPresentation F ι)
    (A' : OrdinaryAtlasPresentation F ι') : OrdinaryCoverRefinement A' (ι × ι') where
  r := Prod.snd
  V := fun p => A.U p.1 ∩ A'.U p.2
  isOpen_V := fun p => (A.isOpen_U p.1).inter (A'.isOpen_U p.2)
  cover_V := fun b => by
    obtain ⟨i, hi⟩ := A.cover b
    obtain ⟨i', hi'⟩ := A'.cover b
    exact ⟨(i, i'), hi, hi'⟩
  subset := fun _ => Set.inter_subset_right

/-- **PACKAGE D (item 40), REQUIRED ENDPOINT.**  Two ordinary atlas presentations of one bare
family restrict to ordinary presentations on **one** common ordinary refinement, indexed by
the same type and with the same domains. -/
theorem commonRefinement_domains (A : OrdinaryAtlasPresentation F ι)
    (A' : OrdinaryAtlasPresentation F ι') (p : ι × ι') :
    (commonRefinementLeft A A').atlas.U p = (commonRefinementRight A A').atlas.U p := rfl

end Refinement

end NullSectorTask32
