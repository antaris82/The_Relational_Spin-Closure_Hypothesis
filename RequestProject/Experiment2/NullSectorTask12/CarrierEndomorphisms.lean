import RequestProject.Experiment2.NullSectorTask12.CentralAction

/-!
# Task 12, Layer 10: internal endomorphisms of a minimal carrier (§32, §33)

An *internal endomorphism* of a left carrier is a real-linear self-map commuting with the
left action of every algebra element.  Nothing is assumed about the outcome, and the
result is derived, not imported:

> the internal endomorphisms of a minimal left carrier are exactly the left
> multiplications by elements of the inherited central plane `Z`, the correspondence
> `z ↦ (ψ ↦ z ⋆ ψ)` is injective and multiplicative, and the resulting algebra therefore
> has real dimension exactly two.

The classification is stated with the inherited central plane only; no complex scalar
field, no commutant terminology, and no conventional lemma is used.
-/

namespace NullSectorTask12

open NullSectorTask08 NullSectorTask09 NullSectorTask10

variable {L : Submodule ℝ W}

/-! ## The left action on a carrier -/

/-- The left action of an algebra element on a left carrier. -/
noncomputable def lact (hL : IsLeftCarrier L) (x : W) : L →ₗ[ℝ] L where
  toFun ψ := ⟨x ⋆ (ψ : W), hL _ _ ψ.2⟩
  map_add' := by
    intro ψ φ
    apply Subtype.ext
    exact mul_add_W x (ψ : W) (φ : W)
  map_smul' := by
    intro c ψ
    apply Subtype.ext
    exact mul_smul_W c x (ψ : W)

@[simp] theorem lact_coe (hL : IsLeftCarrier L) (x : W) (ψ : L) :
    ((lact hL x ψ : L) : W) = x ⋆ (ψ : W) := rfl

/-- **§32.  NEUTRAL DEFINITION.**  A real-linear self-map of a left carrier commuting
with the left action of every algebra element. -/
def IsInternalEndo (hL : IsLeftCarrier L) (T : L →ₗ[ℝ] L) : Prop :=
  ∀ (x : W) (ψ : L), T (lact hL x ψ) = lact hL x (T ψ)

/-- **DERIVED.**  Left multiplication by a central element is an internal
endomorphism. -/
theorem isInternalEndo_central (hL : IsLeftCarrier L) {z : W} (hz : z ∈ Z) :
    IsInternalEndo hL (lact hL z) := by
  intro x ψ
  apply Subtype.ext
  show z ⋆ (x ⋆ (ψ : W)) = x ⋆ (z ⋆ (ψ : W))
  rw [← mul_assoc_W, Z_central hz x, mul_assoc_W]

/-! ## Every internal endomorphism is central -/

theorem mem_Lgen_mul_self {e : W} (he : IsSelfProduct e) {ψ : W} (hψ : ψ ∈ Lgen e) :
    ψ ⋆ e = ψ := by
  obtain ⟨x, rfl⟩ := (mem_Lgen_iff _ _).1 hψ
  rw [mul_assoc_W, he]

/-- **PRINCIPAL THEOREM (§33).**  Every internal endomorphism of a minimal left carrier
is left multiplication by an element of the inherited central plane. -/
theorem internalEndo_eq_central {e : W} (he : IsSelfProduct e) (hne : e ≠ 0)
    (h0 : e 0 = 1 / 2) (h7 : e 7 = 0) {T : Lgen e →ₗ[ℝ] Lgen e}
    (hT : IsInternalEndo (isLeftCarrier_Lgen e) T) :
    ∃ z ∈ Z, ∀ ψ : Lgen e, (T ψ : W) = z ⋆ (ψ : W) := by
  set hL := isLeftCarrier_Lgen e with hLdef
  set E : Lgen e := ⟨e, self_mem_Lgen e⟩ with hE
  have key : ∀ ψ : Lgen e, T ψ = lact hL (ψ : W) (T E) := by
    intro ψ
    have hψ : lact hL (ψ : W) E = ψ := by
      apply Subtype.ext
      show (ψ : W) ⋆ e = (ψ : W)
      exact mem_Lgen_mul_self he ψ.2
    calc T ψ = T (lact hL (ψ : W) E) := by rw [hψ]
      _ = lact hL (ψ : W) (T E) := hT _ _
  have ht1 : e ⋆ ((T E : Lgen e) : W) = ((T E : Lgen e) : W) := by
    have := key E
    have h2 := congrArg (fun y : Lgen e => (y : W)) this
    simpa using h2.symm
  have ht2 : ((T E : Lgen e) : W) ⋆ e = ((T E : Lgen e) : W) :=
    mem_Lgen_mul_self he (T E).2
  have ht : ((T E : Lgen e) : W) ∈ Zspan e := by
    have hcomp : e ⋆ (((T E : Lgen e) : W) ⋆ e) = ((T E : Lgen e) : W) := by
      rw [ht2, ht1]
    rw [← hcomp]
    exact compress_mem_Zspan he hne h0 h7 _
  obtain ⟨z, hz, hze⟩ := (mem_Zspan_iff_central _ _).1 ht
  refine ⟨z, hz, ?_⟩
  intro ψ
  have h1 := congrArg (fun y : Lgen e => (y : W)) (key ψ)
  simp only [lact_coe] at h1
  rw [h1, ← hze]
  calc (ψ : W) ⋆ (z ⋆ e) = (ψ : W) ⋆ (e ⋆ z) := by rw [Z_central hz e]
    _ = ((ψ : W) ⋆ e) ⋆ z := (mul_assoc_W _ _ _).symm
    _ = (ψ : W) ⋆ z := by rw [mem_Lgen_mul_self he ψ.2]
    _ = z ⋆ (ψ : W) := (Z_central hz _).symm

/-- **DERIVED (§33).**  The central element implementing an internal endomorphism is
unique. -/
theorem central_unique_on_Lgen {e : W} (hne : e ≠ 0) {z z' : W} (hz : z ∈ Z)
    (hz' : z' ∈ Z) (h : z ⋆ e = z' ⋆ e) : z = z' := by
  obtain ⟨a, b, rfl⟩ := (mem_Z_iff z).1 hz
  obtain ⟨a', b', rfl⟩ := (mem_Z_iff z').1 hz'
  rw [zsmul_mul, zsmul_mul] at h
  have hzero : (a - a') • e + (b - b') • (wS ⋆ e) = 0 := by
    calc (a - a') • e + (b - b') • (wS ⋆ e)
        = (a • e + b • (wS ⋆ e)) - (a' • e + b' • (wS ⋆ e)) := by module
      _ = 0 := by rw [h, sub_self]
  have hab : a - a' = 0 ∧ b - b' = 0 := by
    by_contra hcon
    exact central_smul_ne_zero hne hcon hzero
  have ha : a = a' := by linarith [hab.1]
  have hb : b = b' := by linarith [hab.2]
  rw [ha, hb]

/-! ## The internal endomorphism algebra -/

/-- The space of internal endomorphisms of a left carrier. -/
def EndoSpace (hL : IsLeftCarrier L) : Submodule ℝ (L →ₗ[ℝ] L) where
  carrier := {T | IsInternalEndo hL T}
  zero_mem' := by intro x ψ; simp
  add_mem' := by
    intro T T' hT hT' x ψ
    simp only [LinearMap.add_apply, hT x ψ, hT' x ψ, map_add]
  smul_mem' := by
    intro c T hT x ψ
    simp only [LinearMap.smul_apply, hT x ψ, map_smul]

theorem mem_EndoSpace_iff (hL : IsLeftCarrier L) (T : L →ₗ[ℝ] L) :
    T ∈ EndoSpace hL ↔ IsInternalEndo hL T := Iff.rfl

/-- The central plane, acting on a left carrier. -/
noncomputable def endoOfZ (hL : IsLeftCarrier L) :
    (Z : Submodule ℝ W) →ₗ[ℝ] (L →ₗ[ℝ] L) where
  toFun z := lact hL (z : W)
  map_add' := by
    intro z z'
    exact LinearMap.ext fun ψ => Subtype.ext (add_mul_W (z : W) (z' : W) (ψ : W))
  map_smul' := by
    intro c z
    exact LinearMap.ext fun ψ => Subtype.ext (smul_mul_W c (z : W) (ψ : W))

@[simp] theorem endoOfZ_apply (hL : IsLeftCarrier L) (z : (Z : Submodule ℝ W)) :
    endoOfZ hL z = lact hL (z : W) := rfl

/-- **DERIVED (§33).**  The correspondence is multiplicative: composition of the internal
endomorphisms is the product of the central elements. -/
theorem endoOfZ_comp (hL : IsLeftCarrier L) (z z' : (Z : Submodule ℝ W)) :
    (endoOfZ hL z).comp (endoOfZ hL z') = lact hL ((z : W) ⋆ (z' : W)) :=
  LinearMap.ext fun ψ => Subtype.ext (mul_assoc_W (z : W) (z' : W) (ψ : W)).symm

/-- **PRINCIPAL THEOREM (§33).**  The internal endomorphisms of a minimal left carrier
are exactly the central left multiplications. -/
theorem range_endoOfZ_eq_EndoSpace {e : W} (he : IsSelfProduct e) (hne : e ≠ 0)
    (h0 : e 0 = 1 / 2) (h7 : e 7 = 0) :
    LinearMap.range (endoOfZ (isLeftCarrier_Lgen e)) = EndoSpace (isLeftCarrier_Lgen e) := by
  apply le_antisymm
  · rintro T ⟨z, rfl⟩
    exact isInternalEndo_central _ z.2
  · intro T hT
    obtain ⟨z, hz, hzT⟩ := internalEndo_eq_central he hne h0 h7 hT
    exact ⟨⟨z, hz⟩, LinearMap.ext fun ψ => Subtype.ext (hzT ψ).symm⟩

theorem endoOfZ_injective {e : W} (hne : e ≠ 0) :
    Function.Injective (endoOfZ (isLeftCarrier_Lgen e)) := by
  intro z z' h
  have hE := congrArg (fun T : Lgen e →ₗ[ℝ] Lgen e => (T ⟨e, self_mem_Lgen e⟩ : W)) h
  simp only [endoOfZ_apply, lact_coe] at hE
  exact Subtype.ext (central_unique_on_Lgen hne z.2 z'.2 hE)

/-- **PRINCIPAL THEOREM (§33): the exact internal endomorphism algebra.**  For a minimal
left carrier the algebra of real-linear self-maps commuting with the left action of the
whole algebra is isomorphic, as a real algebra, to the inherited central plane, and has
real dimension exactly two. -/
theorem finrank_EndoSpace {e : W} (he : IsSelfProduct e) (hne : e ≠ 0) (h0 : e 0 = 1 / 2)
    (h7 : e 7 = 0) :
    Module.finrank ℝ (EndoSpace (isLeftCarrier_Lgen e)) = 2 := by
  rw [← range_endoOfZ_eq_EndoSpace he hne h0 h7,
    LinearMap.finrank_range_of_inj (endoOfZ_injective hne)]
  exact finrank_Z

/-- **PRINCIPAL SUMMARY (§32, §33).**  For every minimal left carrier: the internal
endomorphisms are exactly the central left multiplications, the correspondence is
injective and multiplicative, and the resulting algebra has real dimension two. -/
theorem carrier_endomorphism_classification {L : Submodule ℝ W}
    (hL : IsMinimalLeftCarrier L) :
    ∃ e : W, L = Lgen e ∧ IsSelfProduct e ∧ e ≠ 0 ∧
      LinearMap.range (endoOfZ (isLeftCarrier_Lgen e))
          = EndoSpace (isLeftCarrier_Lgen e) ∧
      Function.Injective (endoOfZ (isLeftCarrier_Lgen e)) ∧
      Module.finrank ℝ (EndoSpace (isLeftCarrier_Lgen e)) = 2 := by
  obtain ⟨e, he, hne, -, h0, h7, rfl⟩ := isMinimal_eq_Lgen_selfProduct hL
  exact ⟨e, rfl, he, hne, range_endoOfZ_eq_EndoSpace he hne h0 h7, endoOfZ_injective hne,
    finrank_EndoSpace he hne h0 h7⟩

end NullSectorTask12
