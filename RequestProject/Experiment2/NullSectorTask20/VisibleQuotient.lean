import RequestProject.Experiment2.NullSectorTask20.InternalProjection

/-!
# Task 20, Layer 3 (Package B): the exact quotient represented by visible equality

Phase A only.  The intrinsic parameter carrier is the pair (unit direction, real
transformation parameter).  The equivalence relation is defined *solely* by equality of the
visible transformations; reflexivity, symmetry and transitivity are proved explicitly, and
the quotient is constructed.  The module then settles, exactly:

* unique factorization of the visible map through the quotient (items 21);
* bijectivity of the induced map onto the visible image (item 22);
* the topological audit: with the inherited topologies, the quotient topology *agrees* with
  the subspace topology on the visible image (item 23);
* the algebraic audit: the visible image carries an inherited composition law and is closed
  under it, together with the identity and inverses — full closure holds, so no weaker
  structure has to be recorded (items 24, 25).
-/

namespace NullSectorTask20

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19

/-! ## The intrinsic parameter carrier and the visible map -/

/-- **NEUTRAL DEFINITION (item 17).**  The intrinsic parameter carrier: a unit direction
together with a real transformation parameter. -/
abbrev VisParam : Type := Sph × ℝ

/-- **NEUTRAL DEFINITION.**  The visible transformation attached to a parameter. -/
noncomputable def visMap (p : VisParam) : W →ₗ[ℝ] W := PhiGen (p.1 : Vec3) p.2

/-- **NEUTRAL DEFINITION (item 18).**  The intrinsic equivalence relation: equality of the
visible transformations. -/
def visRel (p q : VisParam) : Prop := visMap p = visMap q

/-! ## Item 19 — the three relation properties, proved explicitly -/

theorem visRel_refl (p : VisParam) : visRel p p := rfl

theorem visRel_symm {p q : VisParam} (h : visRel p q) : visRel q p := h.symm

theorem visRel_trans {p q r : VisParam} (h : visRel p q) (h' : visRel q r) : visRel p r :=
  h.trans h'

/-- **DERIVED.**  In inherited terms, the relation is exactly the inherited sign relation
between the two reference implementers. -/
theorem visRel_iff_signRelated (p q : VisParam) :
    visRel p q ↔ SignRelated (p.1 : Vec3) (q.1 : Vec3) p.2 q.2 :=
  coincidence_iff p.1.2 q.1.2 p.2 q.2

/-! ## The quotient -/

/-- **NEUTRAL DEFINITION (item 20).**  The quotient of the parameter carrier by visible
equality. -/
def visSetoid : Setoid VisParam where
  r := visRel
  iseqv := ⟨visRel_refl, visRel_symm, visRel_trans⟩

/-- **NEUTRAL DEFINITION.**  The intrinsic visible quotient object. -/
def VisQuot : Type := Quotient visSetoid

instance : TopologicalSpace VisQuot := instTopologicalSpaceQuotient

/-- The quotient projection. -/
def visClass (p : VisParam) : VisQuot := Quotient.mk visSetoid p

theorem visClass_eq_iff {p q : VisParam} : visClass p = visClass q ↔ visRel p q :=
  Quotient.eq (r := visSetoid)

theorem visClass_surjective : Function.Surjective visClass :=
  Quotient.mk_surjective

theorem continuous_visClass : Continuous visClass := continuous_quotient_mk'

/-! ## Item 21 — unique factorization through the quotient -/

/-- **PACKAGE B (item 21).**  The visible map factors through the quotient, and the
factorization is unique. -/
noncomputable def visLift : VisQuot → (W →ₗ[ℝ] W) :=
  Quotient.lift visMap fun _ _ h => h

@[simp] theorem visLift_visClass (p : VisParam) : visLift (visClass p) = visMap p := rfl

theorem visLift_unique (F : VisQuot → (W →ₗ[ℝ] W)) (hF : ∀ p, F (visClass p) = visMap p) :
    F = visLift := by
  funext q
  obtain ⟨p, rfl⟩ := visClass_surjective q
  rw [hF p, visLift_visClass]

/-! ## Item 22 — bijectivity onto the visible image -/

/-- **NEUTRAL DEFINITION.**  The visible image. -/
def visImage : Set (W →ₗ[ℝ] W) := Set.range visMap

theorem visLift_injective : Function.Injective visLift := by
  intro q q' h
  obtain ⟨p, rfl⟩ := visClass_surjective q
  obtain ⟨p', rfl⟩ := visClass_surjective q'
  exact visClass_eq_iff.2 h

/-- **PACKAGE B (item 22).**  The induced map from the quotient onto the visible image is a
bijection. -/
noncomputable def visToImage : VisQuot → visImage :=
  Quotient.lift (fun p : VisParam => (⟨visMap p, ⟨p, rfl⟩⟩ : visImage))
    fun _ _ h => Subtype.ext h

@[simp] theorem visToImage_visClass (p : VisParam) :
    (visToImage (visClass p) : W →ₗ[ℝ] W) = visMap p := rfl

theorem visToImage_bijective : Function.Bijective visToImage := by
  constructor
  · intro q q' h
    obtain ⟨p, rfl⟩ := visClass_surjective q
    obtain ⟨p', rfl⟩ := visClass_surjective q'
    exact visClass_eq_iff.2 (congrArg Subtype.val h)
  · rintro ⟨F, p, rfl⟩
    exact ⟨visClass p, Subtype.ext rfl⟩

/-! ## Item 23 — the topological audit -/

/-- The visible image, read inside the space of maps of the inherited carrier, where the
inherited product topology is available. -/
def visImageFun : Set (W → W) := Set.range fun p : VisParam => ⇑(visMap p)

noncomputable def visToImageFun : VisQuot → visImageFun :=
  Quotient.lift (fun p : VisParam => (⟨⇑(visMap p), ⟨p, rfl⟩⟩ : visImageFun))
    fun a b h => Subtype.ext (congrArg (fun F : W →ₗ[ℝ] W => (F : W → W))
      (h : visMap a = visMap b))

@[simp] theorem visToImageFun_visClass (p : VisParam) :
    (visToImageFun (visClass p) : W → W) = ⇑(visMap p) := rfl

theorem visToImageFun_bijective : Function.Bijective visToImageFun := by
  constructor
  · intro q q' h
    obtain ⟨p, rfl⟩ := visClass_surjective q
    obtain ⟨p', rfl⟩ := visClass_surjective q'
    refine visClass_eq_iff.2 ?_
    have : ⇑(visMap p) = ⇑(visMap p') := congrArg Subtype.val h
    exact DFunLike.coe_injective this
  · rintro ⟨F, p, rfl⟩
    exact ⟨visClass p, Subtype.ext rfl⟩

theorem continuous_visMapFun : Continuous fun p : VisParam => ⇑(visMap p) := by
  have hdir : Continuous fun p : VisParam => (p.1 : Vec3) :=
    continuous_subtype_val.comp continuous_fst
  have h1 : Continuous fun p : VisParam => Un (p.1 : Vec3) p.2 :=
    continuous_Un_comp hdir continuous_snd
  have h2 : Continuous fun p : VisParam => Un (p.1 : Vec3) (-p.2) :=
    continuous_Un_comp hdir (continuous_neg.comp continuous_snd)
  refine continuous_pi fun x => ?_
  have hrw : (fun p : VisParam => (visMap p) x)
      = fun p : VisParam => (Un (p.1 : Vec3) p.2 ⋆ x) ⋆ Un (p.1 : Vec3) (-p.2) := rfl
  rw [hrw]
  exact continuous_starW (continuous_starW h1 continuous_const) h2

theorem continuous_visToImageFun : Continuous visToImageFun :=
  (continuous_visMapFun.subtype_mk _).quotient_lift _

/-- **DERIVED.**  Every visible transformation is realized with a parameter in `[0, 2π]`. -/
theorem visClass_repr_Icc (p : VisParam) :
    ∃ q : VisParam, q.2 ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧ visClass q = visClass p := by
  obtain ⟨n, ψ, hn, h0, h2, hUn⟩ := Lift_repr_Icc (Un_mem_Lift p.1.2 p.2)
  refine ⟨(⟨n, hn⟩, ψ), ⟨h0, h2⟩, ?_⟩
  refine visClass_eq_iff.2 ?_
  exact phiGen_eq_of_signRelated ⟨1, Or.inl rfl, by rw [one_smul, ← hUn]⟩

instance : CompactSpace VisQuot := by
  constructor
  have hK : IsCompact ((Set.univ : Set Sph) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_univ.prod isCompact_Icc
  have himg : (Set.univ : Set VisQuot)
      = visClass '' ((Set.univ : Set Sph) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    ext q
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    obtain ⟨p, rfl⟩ := visClass_surjective q
    obtain ⟨r, hr, hrq⟩ := visClass_repr_Icc p
    exact ⟨r, ⟨trivial, hr⟩, hrq⟩
  rw [himg]
  exact hK.image continuous_visClass

/-- **PACKAGE B (item 23).**  The quotient topology and the subspace topology on the visible
image agree: the canonical bijection is a homeomorphism.  The only inputs are compactness of
the direction carrier, the bounded-parameter representation, and the Hausdorff property of
the inherited map space. -/
noncomputable def visHomeo : VisQuot ≃ₜ visImageFun :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ visToImageFun_bijective)
    continuous_visToImageFun

/-! ## Items 24, 25 — the inherited composition law on the visible image -/

theorem visImage_id : LinearMap.id ∈ visImage := by
  refine ⟨(⟨e1, e1_isUnitAxis⟩, 0), ?_⟩
  refine LinearMap.ext fun x => ?_
  rw [visMap, PhiGen_apply, neg_zero, Un_zero, one_mul_W, mul_one_W, LinearMap.id_apply]

theorem visMap_eq_proj (p : VisParam) : visMap p = proj (Un (p.1 : Vec3) p.2) :=
  (proj_Un p.1.2 p.2).symm

/-- **PACKAGE B (item 24).**  The visible image is closed under the inherited composition
law. -/
theorem visImage_comp_mem {F G : W →ₗ[ℝ] W} (hF : F ∈ visImage) (hG : G ∈ visImage) :
    F.comp G ∈ visImage := by
  obtain ⟨p, rfl⟩ := hF
  obtain ⟨q, rfl⟩ := hG
  have hmul : Un (p.1 : Vec3) p.2 ⋆ Un (q.1 : Vec3) q.2 ∈ Lift :=
    Lift_mul_mem (Un_mem_Lift p.1.2 p.2) (Un_mem_Lift q.1.2 q.2)
  obtain ⟨n, ψ, hn, hUn⟩ := (mem_Lift_iff_exists_Un _).1 hmul
  refine ⟨(⟨n, hn⟩, ψ), ?_⟩
  rw [visMap, ← proj_Un hn ψ, ← hUn,
    proj_mul (isInvertible_of_mem_Lift (Un_mem_Lift p.1.2 p.2))
      (isInvertible_of_mem_Lift (Un_mem_Lift q.1.2 q.2)),
    ← visMap_eq_proj p, ← visMap_eq_proj q]

/-- **PACKAGE B (item 24).**  The visible image is closed under inherited inversion. -/
theorem visImage_inv_mem {F : W →ₗ[ℝ] W} (hF : F ∈ visImage) :
    ∃ G ∈ visImage, F.comp G = LinearMap.id ∧ G.comp F = LinearMap.id := by
  obtain ⟨p, rfl⟩ := hF
  refine ⟨visMap (p.1, -p.2), ⟨(p.1, -p.2), rfl⟩, ?_, ?_⟩
  · rw [visMap_eq_proj p, visMap_eq_proj (p.1, -p.2),
      ← proj_mul (isInvertible_of_mem_Lift (Un_mem_Lift p.1.2 p.2))
        (isInvertible_of_mem_Lift (Un_mem_Lift p.1.2 (-p.2)))]
    rw [Un_mul_neg p.1.2 p.2, proj_w1]
  · rw [visMap_eq_proj p, visMap_eq_proj (p.1, -p.2),
      ← proj_mul (isInvertible_of_mem_Lift (Un_mem_Lift p.1.2 (-p.2)))
        (isInvertible_of_mem_Lift (Un_mem_Lift p.1.2 p.2))]
    rw [Un_neg_mul p.1.2 p.2, proj_w1]

/-- **PACKAGE B (items 24, 25), principal.**  Full closure holds: the visible image contains
the identity, is closed under composition, and is closed under inversion.  No weaker
algebraic structure has to be recorded. -/
theorem visImage_closed_law :
    LinearMap.id ∈ visImage ∧
      (∀ F ∈ visImage, ∀ G ∈ visImage, F.comp G ∈ visImage) ∧
      (∀ F ∈ visImage, ∃ G ∈ visImage, F.comp G = LinearMap.id ∧ G.comp F = LinearMap.id) :=
  ⟨visImage_id, fun _ hF _ hG => visImage_comp_mem hF hG, fun _ hF => visImage_inv_mem hF⟩

end NullSectorTask20
