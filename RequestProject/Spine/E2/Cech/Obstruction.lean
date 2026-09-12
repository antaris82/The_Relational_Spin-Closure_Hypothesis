import RequestProject.Spine.E2.Cech.Coboundary

/-!
# Task 3, WP7–WP8 : the fixed-cover obstruction class and the vanishing criterion

WP7 asks for the *minimal* native quotient identifying two kernel-valued 2-cocycles that
differ by a 1-coboundary.  No general cohomology theory is imported: the relation

`Cohomologous P 𝓤 c c'  ↔  ∃ ε kernel-valued, c' = (δε) · c on every triple overlap`

is shown to be an equivalence relation (this is exactly where `delta₁_mul` and `delta₁_inv`,
hence centrality of the kernel, are used), and the class is the corresponding `Quot`.

The two layers are kept strictly apart:

* `SpinLiftFamily.defect` **depends on the chosen local lifts** (CHOICE_UP_TO_KERNEL);
* `SpinLiftFamily.obstruction` — its class — **does not** (`obstruction_lift_independent`).
  This is the first genuinely invariant output of Task 3.

WP8 is `obstruction_eq_trivialClass_iff_exists_coherent`: the class is trivial **iff** the
local lifts can be modified by kernel-valued functions so that the lifted transition data
satisfies the exact cocycle law `g̃_ij g̃_jk = g̃_ik` on every triple overlap, i.e. iff coherent
Spin-valued transition data projecting to the given visible cocycle exists.

**Interpretation boundary (mandatory).**  A nontrivial class means precisely that a globally
coherent lift of the *given transition data on the given cover* is obstructed.  It is a
topological lifting obstruction and nothing else: it is not curvature, torsion, holonomy of a
connection, a synchronization defect, a field strength, a matter/antimatter sign or a
preferred frame; and a *vanishing* class says nothing about flatness, curvature, or any
dynamical equilibrium — a coherent lift may perfectly well carry, at a later stage, a
connection with nonzero curvature or torsion.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace CechSpinLift

open NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}
  {𝓤 : CechCover X ι} {P : InternalProjection L G} {T : VisibleCocycle G 𝓤}

/-! ## WP7 — the cohomologous relation on kernel-valued 2-cochains -/

/-- **NEWLY DEFINED (WP7), principal.**  Two 2-cochains are cohomologous on the fixed cover
when they differ by the coboundary of a continuous kernel-valued 1-cochain. -/
def Cohomologous (P : InternalProjection L G) (𝓤 : CechCover X ι)
    (c c' : ι → ι → ι → (X → L)) : Prop :=
  ∃ ε : ι → ι → (X → L), IsKerCochain₁ P 𝓤 ε ∧
    ∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k, c' i j k x = delta₁ ε i j k x * c i j k x

theorem cohomologous_refl (c : ι → ι → ι → (X → L)) : Cohomologous P 𝓤 c c :=
  ⟨one₁, isKerCochain₁_one, fun i j k x _ => by simp [delta₁, one₁]⟩

theorem cohomologous_symm {c c' : ι → ι → ι → (X → L)} (h : Cohomologous P 𝓤 c c') :
    Cohomologous P 𝓤 c' c := by
  obtain ⟨ε, hε, hrel⟩ := h
  refine ⟨inv₁ ε, hε.inv, fun i j k x hx => ?_⟩
  rw [delta₁_inv hε i j k hx, hrel i j k x hx, ← mul_assoc, inv_mul_cancel, one_mul]

theorem cohomologous_trans {c c' c'' : ι → ι → ι → (X → L)} (h : Cohomologous P 𝓤 c c')
    (h' : Cohomologous P 𝓤 c' c'') : Cohomologous P 𝓤 c c'' := by
  obtain ⟨ε, hε, hrel⟩ := h
  obtain ⟨ε', hε', hrel'⟩ := h'
  refine ⟨mul₁ ε' ε, hε'.mul hε, fun i j k x hx => ?_⟩
  rw [delta₁_mul (ε := ε) (ε' := ε') hε' i j k hx, hrel' i j k x hx, hrel i j k x hx,
    mul_assoc]

theorem cohomologous_equivalence (P : InternalProjection L G) (𝓤 : CechCover X ι) :
    Equivalence (Cohomologous P 𝓤) :=
  ⟨cohomologous_refl, cohomologous_symm, cohomologous_trans⟩

/-! ## WP7 — the fixed-cover obstruction class -/

/-- **NEWLY DEFINED (WP7), principal.**  The minimal native quotient: kernel-valued
2-cochains on the fixed cover, modulo 1-coboundaries.  No general cohomology theory is
imported; this is the whole construction. -/
def ObstructionClass (P : InternalProjection L G) (𝓤 : CechCover X ι) : Type max u w t :=
  Quot (Cohomologous P 𝓤)

/-- The class of a 2-cochain. -/
def classOf (P : InternalProjection L G) (𝓤 : CechCover X ι) (c : ι → ι → ι → (X → L)) :
    ObstructionClass P 𝓤 :=
  Quot.mk _ c

/-- **DERIVED (WP7).**  Equality of classes is exactly the cohomologous relation.  Proved
directly from `Quot.sound` and a `Quot.lift` of the relation; no quotient library beyond
`Quot` is used. -/
theorem classOf_eq_iff (c c' : ι → ι → ι → (X → L)) :
    classOf P 𝓤 c = classOf P 𝓤 c' ↔ Cohomologous P 𝓤 c c' := by
  constructor
  · intro h
    have hwd : ∀ a b : ι → ι → ι → (X → L), Cohomologous P 𝓤 a b →
        (Cohomologous P 𝓤 c a = Cohomologous P 𝓤 c b) := fun a b hab =>
      propext ⟨fun hca => cohomologous_trans hca hab,
        fun hcb => cohomologous_trans hcb (cohomologous_symm hab)⟩
    have hcongr := congrArg (Quot.lift (fun d => Cohomologous P 𝓤 c d) hwd) h
    exact cast hcongr (cohomologous_refl c)
  · exact Quot.sound

/-- The class of the trivial 2-cochain — the neutral class, written `[c] = 0` in the task
statement (multiplicatively `[c] = 1`). -/
def trivialClass (P : InternalProjection L G) (𝓤 : CechCover X ι) : ObstructionClass P 𝓤 :=
  classOf P 𝓤 one₂

namespace SpinLiftFamily

/-- **NEWLY DEFINED (WP7), principal.**  The obstruction class of the visible transition data
on the fixed cover, computed from a chosen family of local lifts. -/
def obstruction (D : SpinLiftFamily P T) : ObstructionClass P 𝓤 := classOf P 𝓤 D.defect

/-- **DERIVED_NATIVE (WP7), principal endpoint — the first invariant output of Task 3.**
The obstruction class does not depend on the chosen family of local Spin lifts.  (The defect
itself does; see `defect_change_of_lift`.) -/
theorem obstruction_lift_independent (D D' : SpinLiftFamily P T) :
    D.obstruction = D'.obstruction := by
  obtain ⟨ε, hε, _, hdef⟩ := D.defect_change_of_lift D'
  exact (classOf_eq_iff _ _).2 ⟨ε, hε, hdef⟩

/-! ## WP8 — coherent lifted transition data and the vanishing criterion -/

/-- **NEWLY DEFINED (WP8).**  A family of local lifts is *coherent* when it satisfies the
exact Čech 1-cocycle law itself.  This is *not* called a spin structure: it is an abstract
coherent lift of transition data. -/
def IsCoherent (D : SpinLiftFamily P T) : Prop :=
  ∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k, D.lift i j x * D.lift j k x = D.lift i k x

/-- **DERIVED (WP8).**  Coherence is exactly pointwise triviality of the defect (the
inherited exact-compatibility criterion of the E2 lift layer). -/
theorem isCoherent_iff_defect_one (D : SpinLiftFamily P T) :
    D.IsCoherent ↔ ∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k, D.defect i j k x = 1 := by
  constructor
  · intro h i j k x hx
    exact (InternalProjection.exact_internal_transition_compatibility_iff_defect_trivial
      (V := 𝓤.overlap₃ i j k) (D.lift j k) (D.lift i j) (D.lift i k)).1
      (fun y hy => h i j k y hy) x hx
  · intro h i j k x hx
    exact (InternalProjection.exact_internal_transition_compatibility_iff_defect_trivial
      (V := 𝓤.overlap₃ i j k) (D.lift j k) (D.lift i j) (D.lift i k)).2
      (fun y hy => h i j k y hy) x hx

theorem obstruction_eq_trivialClass_of_isCoherent {D : SpinLiftFamily P T} (h : D.IsCoherent) :
    D.obstruction = trivialClass P 𝓤 := by
  refine (classOf_eq_iff _ _).2 ⟨one₁, isKerCochain₁_one, fun i j k x hx => ?_⟩
  rw [(D.isCoherent_iff_defect_one).1 h i j k x hx]
  simp [delta₁, one₁, one₂]

/-- **DERIVED_NATIVE (WP8), principal endpoint.**  The vanishing criterion in its explicit
form: the class is trivial iff the chosen local lifts can be corrected by continuous
kernel-valued functions into a coherent family. -/
theorem obstruction_eq_trivialClass_iff_kernel_adjustable (D : SpinLiftFamily P T) :
    D.obstruction = trivialClass P 𝓤 ↔
      ∃ ε : ι → ι → (X → L), ∃ hε : IsKerCochain₁ P 𝓤 ε, (D.twist ε hε).IsCoherent := by
  constructor
  · intro h
    obtain ⟨ε, hε, hrel⟩ := (classOf_eq_iff _ _).1 h
    refine ⟨ε, hε, ((D.twist ε hε).isCoherent_iff_defect_one).2 fun i j k x hx => ?_⟩
    have := D.defect_twist ε hε i j k hx
    rw [this, ← hrel i j k x hx]
    rfl
  · rintro ⟨ε, hε, hcoh⟩
    have := obstruction_eq_trivialClass_of_isCoherent hcoh
    rw [← this]
    exact (D.obstruction_lift_independent (D.twist ε hε))

/-- **DERIVED_NATIVE (WP8), principal endpoint — the central equivalence of Task 3.**  The
obstruction class of the visible transition data vanishes **iff** coherent Spin-valued
transition data projecting to it exists on the same cover.

Both directions are proved.  The right-hand side is an *abstract coherent lift of transition
data*: no manifold, no bundle and no spin structure is constructed. -/
theorem obstruction_eq_trivialClass_iff_exists_coherent (D : SpinLiftFamily P T) :
    D.obstruction = trivialClass P 𝓤 ↔ ∃ D' : SpinLiftFamily P T, D'.IsCoherent := by
  constructor
  · intro h
    obtain ⟨ε, hε, hcoh⟩ := (D.obstruction_eq_trivialClass_iff_kernel_adjustable).1 h
    exact ⟨D.twist ε hε, hcoh⟩
  · rintro ⟨D', hD'⟩
    rw [D.obstruction_lift_independent D']
    exact obstruction_eq_trivialClass_of_isCoherent hD'

/-- **WP8, packaged endpoint.**  Coherent lifted transition data is genuine Spin-valued
transition data: it projects onto the visible cocycle and satisfies the same exact cocycle
law. -/
theorem coherent_lift_projects {D' : SpinLiftFamily P T} (h : D'.IsCoherent) :
    (∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, P.proj (D'.lift i j x) = T.g i j x) ∧
    (∀ i j k, ∀ x ∈ 𝓤.overlap₃ i j k, D'.lift i j x * D'.lift j k x = D'.lift i k x) :=
  ⟨fun i j x hx => (D'.isRep i j).2 x hx, h⟩

end SpinLiftFamily

end CechSpinLift
