import RequestProject.Spine.E2.Cech.Obstruction

/-!
# Task 3, WP9 : refinement naturality

The obstruction class of WP7 is attached to a *fixed* cover.  This module proves that it is
not an artifact of that choice, in the exact sense the present infrastructure supports:
along an explicit refinement map `r : 𝓥 → 𝓤` there is a restriction operation `r*` on
classes, and

`[c_𝓥] = r* [c_𝓤]`

where `c_𝓥` is the defect of the *pulled-back* lifts.  Concretely all four levels are pulled
back — visible transition data (`CoverRefinement.pullback`, WP2 module), chosen lifts
(`pullLift`), defects (`defect_pullLift`) and classes (`restrictClass`) — and the diagram
commutes definitionally.

**What is deliberately not built** (documented, not silently avoided): a cover-independent
direct-limit Čech class `Ȟ²(X; ℤ₂)`.  That needs a colimit over the refinement preorder and a
cofinality argument, i.e. a general Čech-cohomology library, which the task explicitly rules
out.  Task 3 therefore stops at exact refinement naturality; the remaining gap is recorded in
`TASK03_AUDIT.md`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace CechSpinLift

open NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι ι' : Type t}
  {𝓤 : CechCover X ι} {𝓥 : CechCover X ι'} {P : InternalProjection L G}
  {T : VisibleCocycle G 𝓤}

/-! ## Pullback of cochains -/

/-- **NEWLY DEFINED (WP9).**  The pullback of a 2-cochain along a refinement map. -/
def pullCochain₂ (R : CoverRefinement 𝓥 𝓤) (c : ι → ι → ι → (X → L)) :
    ι' → ι' → ι' → (X → L) :=
  fun a b d => c (R.r a) (R.r b) (R.r d)

/-- **NEWLY DEFINED (WP9).**  The pullback of a 1-cochain along a refinement map. -/
def pullCochain₁ (R : CoverRefinement 𝓥 𝓤) (ε : ι → ι → (X → L)) : ι' → ι' → (X → L) :=
  fun a b => ε (R.r a) (R.r b)

theorem isKerCochain₁_pull {ε : ι → ι → (X → L)} (R : CoverRefinement 𝓥 𝓤)
    (hε : IsKerCochain₁ P 𝓤 ε) : IsKerCochain₁ P 𝓥 (pullCochain₁ R ε) :=
  fun a b => (hε (R.r a) (R.r b)).mono P (R.overlap₂_le a b)

omit [TopologicalSpace L] [IsTopologicalGroup L] in
theorem delta₁_pull (R : CoverRefinement 𝓥 𝓤) (ε : ι → ι → (X → L)) :
    delta₁ (pullCochain₁ R ε) = pullCochain₂ R (delta₁ ε) := rfl

/-- **DERIVED_NATIVE (WP9).**  Cohomologous cochains stay cohomologous after refinement. -/
theorem cohomologous_pull {c c' : ι → ι → ι → (X → L)} (R : CoverRefinement 𝓥 𝓤)
    (h : Cohomologous P 𝓤 c c') :
    Cohomologous P 𝓥 (pullCochain₂ R c) (pullCochain₂ R c') := by
  obtain ⟨ε, hε, hrel⟩ := h
  exact ⟨pullCochain₁ R ε, isKerCochain₁_pull R hε,
    fun a b d x hx => hrel (R.r a) (R.r b) (R.r d) x (R.overlap₃_le a b d hx)⟩

/-- **NEWLY DEFINED (WP9), principal.**  The induced restriction map on obstruction
classes. -/
def restrictClass (P : InternalProjection L G) (R : CoverRefinement 𝓥 𝓤) :
    ObstructionClass P 𝓤 → ObstructionClass P 𝓥 :=
  Quot.lift (fun c => classOf P 𝓥 (pullCochain₂ R c))
    (fun _ _ h => Quot.sound (cohomologous_pull R h))

@[simp] theorem restrictClass_classOf (P : InternalProjection L G) (R : CoverRefinement 𝓥 𝓤)
    (c : ι → ι → ι → (X → L)) :
    restrictClass P R (classOf P 𝓤 c) = classOf P 𝓥 (pullCochain₂ R c) := rfl

@[simp] theorem restrictClass_trivialClass (P : InternalProjection L G)
    (R : CoverRefinement 𝓥 𝓤) : restrictClass P R (trivialClass P 𝓤) = trivialClass P 𝓥 := rfl

@[simp] theorem restrictClass_id (P : InternalProjection L G) (𝓤 : CechCover X ι) :
    restrictClass P (CoverRefinement.id 𝓤) = _root_.id := by
  funext z
  induction z using Quot.ind with
  | _ c => rfl

theorem restrictClass_comp {ι'' : Type t} {𝓦 : CechCover X ι''} (P : InternalProjection L G)
    (R' : CoverRefinement 𝓦 𝓥) (R : CoverRefinement 𝓥 𝓤) :
    restrictClass P (R'.comp R) = restrictClass P R' ∘ restrictClass P R := by
  funext z
  induction z using Quot.ind with
  | _ c => rfl

namespace SpinLiftFamily

/-! ## Pullback of the chosen lifts, of the defect and of the class -/

/-- **NEWLY DEFINED (WP9), principal.**  The pullback of a family of local lifts along a
refinement: `g̃^𝓥_ab := g̃_{r a, r b}`, a family of lifts of the pulled-back visible
transition data. -/
def pullLift (R : CoverRefinement 𝓥 𝓤) (D : SpinLiftFamily P T) :
    SpinLiftFamily P (R.pullback T) where
  lift a b := D.lift (R.r a) (R.r b)
  isRep a b := (D.isRep (R.r a) (R.r b)).mono P (R.overlap₂_le a b)

@[simp] theorem pullLift_lift (R : CoverRefinement 𝓥 𝓤) (D : SpinLiftFamily P T) (a b : ι') :
    (D.pullLift R).lift a b = D.lift (R.r a) (R.r b) := rfl

/-- **DERIVED_NATIVE (WP9).**  The defect of the pulled-back lifts is the pullback of the
defect — on the nose, not merely up to a coboundary. -/
@[simp] theorem defect_pullLift (R : CoverRefinement 𝓥 𝓤) (D : SpinLiftFamily P T) :
    (D.pullLift R).defect = pullCochain₂ R D.defect := rfl

/-- **DERIVED_NATIVE (WP9), principal endpoint — refinement naturality.**
`[c_𝓥] = r*[c_𝓤]`: the obstruction class of the refined data is the restriction of the
obstruction class of the original data. -/
theorem obstruction_pullLift (R : CoverRefinement 𝓥 𝓤) (D : SpinLiftFamily P T) :
    (D.pullLift R).obstruction = restrictClass P R D.obstruction := rfl

/-- **DERIVED_NATIVE (WP9).**  A vanishing obstruction stays vanishing after refinement.
(The converse is *not* claimed: it is exactly the direct-limit statement that Task 3 does not
prove.) -/
theorem obstruction_pullLift_eq_trivial (R : CoverRefinement 𝓥 𝓤) (D : SpinLiftFamily P T)
    (h : D.obstruction = trivialClass P 𝓤) :
    (D.pullLift R).obstruction = trivialClass P 𝓥 := by
  rw [obstruction_pullLift, h, restrictClass_trivialClass]

/-- **DERIVED_NATIVE (WP9).**  Coherence is inherited by the refined lifts. -/
theorem isCoherent_pullLift (R : CoverRefinement 𝓥 𝓤) {D : SpinLiftFamily P T}
    (h : D.IsCoherent) : (D.pullLift R).IsCoherent :=
  fun a b d x hx => h (R.r a) (R.r b) (R.r d) x (R.overlap₃_le a b d hx)

/-! ## Independence of the chosen refinement *map*

A refinement of covers usually admits many index maps `r`.  The construction below compares
two of them: the visible data pulled back along `r` and along `r'` are conjugate by the
visible 0-cochain `g_{r a, r' a}`, and lifting that conjugation produces a family of local
lifts of the `r'`-pullback whose defect is *literally equal* to the defect of the
`r`-pullback — because the defect is central.  Hence the two restricted classes agree. -/

/-- **NEWLY DEFINED (WP9).**  The conjugated family of local lifts
`B_ab = (g̃_{r a, r' a})⁻¹ · g̃_{r a, r b} · g̃_{r b, r' b}`, a family of lifts of the visible
data pulled back along `r'`. -/
def conjLift (R R' : CoverRefinement 𝓥 𝓤) (D : SpinLiftFamily P T) :
    SpinLiftFamily P (R'.pullback T) where
  lift a b := fun x =>
    (D.lift (R.r a) (R'.r a) x)⁻¹ * D.lift (R.r a) (R.r b) x * D.lift (R.r b) (R'.r b) x
  isRep a b := by
    have hVa : ∀ x ∈ 𝓥.overlap₂ a b, x ∈ 𝓥.U a := fun _ hx => hx.1
    have hVb : ∀ x ∈ 𝓥.overlap₂ a b, x ∈ 𝓥.U b := fun _ hx => hx.2
    have hla : 𝓥.overlap₂ a b ⊆ 𝓤.overlap₂ (R.r a) (R'.r a) :=
      fun x hx => ⟨R.le a (hVa x hx), R'.le a (hVa x hx)⟩
    have hlb : 𝓥.overlap₂ a b ⊆ 𝓤.overlap₂ (R.r b) (R'.r b) :=
      fun x hx => ⟨R.le b (hVb x hx), R'.le b (hVb x hx)⟩
    have hab : 𝓥.overlap₂ a b ⊆ 𝓤.overlap₂ (R.r a) (R.r b) := R.overlap₂_le a b
    refine ⟨(((D.isRep (R.r a) (R'.r a)).mono P hla).1.inv.mul
        ((D.isRep (R.r a) (R.r b)).mono P hab).1).mul
        ((D.isRep (R.r b) (R'.r b)).mono P hlb).1, fun x hx => ?_⟩
    have e1 : P.proj (D.lift (R.r a) (R'.r a) x) = T.g (R.r a) (R'.r a) x :=
      (D.isRep (R.r a) (R'.r a)).2 x (hla hx)
    have e2 : P.proj (D.lift (R.r a) (R.r b) x) = T.g (R.r a) (R.r b) x :=
      (D.isRep (R.r a) (R.r b)).2 x (hab hx)
    have e3 : P.proj (D.lift (R.r b) (R'.r b) x) = T.g (R.r b) (R'.r b) x :=
      (D.isRep (R.r b) (R'.r b)).2 x (hlb hx)
    have hsym : (T.g (R.r a) (R'.r a) x)⁻¹ = T.g (R'.r a) (R.r a) x :=
      (T.g_symm (R.r a) (R'.r a) (hla hx)).symm
    have h1 : T.g (R'.r a) (R.r a) x * T.g (R.r a) (R.r b) x = T.g (R'.r a) (R.r b) x :=
      T.cocycle (R'.r a) (R.r a) (R.r b) x
        ⟨⟨R'.le a (hVa x hx), R.le a (hVa x hx)⟩, R.le b (hVb x hx)⟩
    have h2 : T.g (R'.r a) (R.r b) x * T.g (R.r b) (R'.r b) x = T.g (R'.r a) (R'.r b) x :=
      T.cocycle (R'.r a) (R.r b) (R'.r b) x
        ⟨⟨R'.le a (hVa x hx), R.le b (hVb x hx)⟩, R'.le b (hVb x hx)⟩
    simp only [map_mul, map_inv, e1, e2, e3, CoverRefinement.pullback_g]
    rw [hsym, h1, h2]

/-- **DERIVED_NATIVE (WP9).**  The conjugated family has *the same* defect as the
`r`-pullback on every triple overlap.  This is exactly where centrality of the kernel is
used: conjugating a kernel element by a lift does nothing. -/
theorem defect_conjLift (R R' : CoverRefinement 𝓥 𝓤) (D : SpinLiftFamily P T) (a b c : ι')
    {x : X} (hx : x ∈ 𝓥.overlap₃ a b c) :
    (D.conjLift R R').defect a b c x = (D.pullLift R).defect a b c x := by
  set La := D.lift (R.r a) (R'.r a) x with hLa
  set Lb := D.lift (R.r b) (R'.r b) x with hLb
  set Lc := D.lift (R.r c) (R'.r c) x with hLc
  set Aab := D.lift (R.r a) (R.r b) x with hAab
  set Abc := D.lift (R.r b) (R.r c) x with hAbc
  set Aac := D.lift (R.r a) (R.r c) x with hAac
  have hker : Aab * Abc * Aac⁻¹ ∈ P.Ker := by
    have h := (D.pullLift R).defect_mem_ker a b c hx
    simpa [SpinLiftFamily.defect_apply, pullLift, hAab, hAbc, hAac] using h
  have hcomm := (P.ker_commute hker La).eq
  have hstep : (La⁻¹ * Aab * Lb) * (Lb⁻¹ * Abc * Lc) * (La⁻¹ * Aac * Lc)⁻¹
      = La⁻¹ * ((Aab * Abc * Aac⁻¹) * La) := by group
  simp only [SpinLiftFamily.defect_apply, conjLift, pullLift]
  rw [hstep, hcomm, hAab, hAbc, hAac]
  group

/-- **DERIVED_NATIVE (WP9), principal.**  The restricted obstruction class does not depend on
which index map realises the refinement. -/
theorem obstruction_pullLift_indep_of_map (R R' : CoverRefinement 𝓥 𝓤)
    (D : SpinLiftFamily P T) :
    (D.pullLift R).obstruction = (D.pullLift R').obstruction := by
  have h1 : (D.pullLift R).obstruction = (D.conjLift R R').obstruction := by
    refine (classOf_eq_iff _ _).2 ⟨one₁, isKerCochain₁_one, fun a b c x hx => ?_⟩
    rw [defect_conjLift R R' D a b c hx]
    simp [delta₁, one₁]
  rw [h1]
  exact (D.conjLift R R').obstruction_lift_independent (D.pullLift R')

end SpinLiftFamily

end CechSpinLift
