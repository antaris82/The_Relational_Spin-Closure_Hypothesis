import RequestProject.Experiment2.NullSectorTask18.BridgeFactors

/-!
# Task 18, Package E: bridge-normalized reconstruction

An indexed system of admissible local exact representatives covering the unit directions is
defined first (§35).  Every member carries its derived bridge to `refFam` (§36).
*Bridge-normalization* removes that factor while retaining it as data (§37):

```
bridgeNormalize U n θ := ovl refFam U n θ ⋆ U n θ .
```

Results:

* §38.  Every bridge-normalized local representative equals the **same** global
  sign-relaxed reference on its domain.  The answer is therefore **yes**; and the honest
  hypothesis is joint regularity alone — local exactness is not needed for the
  normalization to succeed, which is recorded separately.
* §39.  Existence **and** uniqueness of the global bridge-normalized reconstruction for an
  arbitrary indexed local system satisfying the stated hypotheses: the reconstruction is
  `refFam`, it is jointly regular and sign-relaxed, and any jointly regular family with the
  same restrictions coincides with it at every unit direction.
* The retained data are complete: the local representative is recovered from the
  reconstruction and its own bridge, and the bridge is central with a half-odd rate.
* §40.  The three failure modes are separated by theorems, not by prose:
  1. *ordinary literal gluing* can fail — an explicit two-member system with a nontrivial
     integer overlap factor has no literal global extension;
  2. *reconstruction into the sign-relaxed class by literal equality* fails even for the
     completely compatible Task-17 system (Package C);
  3. *bridge-normalized reconstruction* never fails.
  In particular the Task-17 system **does** have a sign-relaxed reconstruction with
  explicit central conversion factors.
-/

namespace NullSectorTask18

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17

/-! ## §35 — an indexed system of admissible local exact representatives -/

/-- **NEUTRAL DEFINITION (§35).**  An indexed system of admissible local exact
representatives whose domains cover the unit directions. -/
structure IsCoveringLocalSystem {ι : Type*} (D : ι → Set Vec3)
    (F : ι → Vec3 → ℝ → W) : Prop where
  /-- every domain consists of unit directions -/
  unit : ∀ i : ι, UnitSet (D i)
  /-- the domains cover the unit directions -/
  cover : ∀ n : Vec3, IsUnitAxis n → ∃ i : ι, n ∈ D i
  /-- every local representative is jointly regular -/
  regular : ∀ i : ι, IsJointlyRegularFamily (F i)
  /-- every local representative is exactly transformation-valued on its domain -/
  exact : ∀ i : ι, IsTransformationValuedOn (D i) (F i)

/-- **DERIVED (§35).**  The inherited Task-17 system is such a system. -/
theorem task17System_isCoveringLocalSystem : IsCoveringLocalSystem Dom task17System :=
  ⟨fun _ _ hn => hn.1, fun n hn => ⟨n, Dom_covers hn⟩, fun _ => locFam_jointlyRegular 0,
    fun v => locFam_transformationValuedOn 0 v⟩

/-! ## §37 — bridge-normalization -/

/-- **NEUTRAL DEFINITION (§37).**  Bridge-normalization: the local bridge factor is
explicitly removed from the left.  The removed factor is *not* discarded — it is exactly
`Bridge U`, which remains available as data. -/
noncomputable def bridgeNormalize (U : Vec3 → ℝ → W) (n : Vec3) (θ : ℝ) : W :=
  ovl refFam U n θ ⋆ U n θ

/-- **DERIVED (§37).**  The factor removed by bridge-normalization is exactly the inverse of
the bridge: composing the two gives the unit. -/
theorem bridge_removal {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U) {n : Vec3}
    (hn : IsUnitAxis n) (θ : ℝ) : ovl refFam U n θ ⋆ Bridge U n θ = w1 := by
  rw [Bridge, ovl_chain3 hU hn θ]
  exact Un_mul_neg hn θ

/-! ## §38 — every normalized representative is the same reference -/

/-- **PRINCIPAL THEOREM (§38).**  Bridge-normalization of an arbitrary jointly regular
family returns the global sign-relaxed reference, at every unit direction and every
parameter.  Local exactness is **not** used. -/
theorem bridgeNormalize_eq_refFam {U : Vec3 → ℝ → W} (hU : IsJointlyRegularFamily U)
    {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) : bridgeNormalize U n θ = refFam n θ := by
  have hinv : U n (-θ) ⋆ U n θ = w1 := (hU.lift n hn).neg_mul θ
  calc bridgeNormalize U n θ = refFam n θ ⋆ (U n (-θ) ⋆ U n θ) := by
        simp only [bridgeNormalize, ovl, mul_assoc_W]
    _ = refFam n θ := by rw [hinv, mul_one_W]

/-- **PRINCIPAL THEOREM (§38), for a system.**  Every bridge-normalized member of an
indexed local system equals one and the same global sign-relaxed reference on its own
domain. -/
theorem system_bridgeNormalize_eq_refFam {ι : Type*} {D : ι → Set Vec3}
    {F : ι → Vec3 → ℝ → W} (hS : IsCoveringLocalSystem D F) :
    ∀ i : ι, ∀ n ∈ D i, ∀ θ : ℝ, bridgeNormalize (F i) n θ = refFam n θ :=
  fun i n hn θ => bridgeNormalize_eq_refFam (hS.regular i) (hS.unit i n hn) θ

/-! ## §39 — existence and uniqueness of the bridge-normalized reconstruction -/

/-- **PRINCIPAL THEOREM (§39).**  For an arbitrary indexed system of admissible local exact
representatives covering the unit directions, the bridge-normalized reconstruction
**exists** — it is the unique global sign-relaxed family `refFam`, which is jointly regular
and sign-relaxed — and it is **unique**: any jointly regular family agreeing with all the
normalized local representatives coincides with it at every unit direction.  The retained
conversion data are complete: each local representative is recovered from the
reconstruction and its own central bridge. -/
theorem bridge_normalized_reconstruction {ι : Type*} {D : ι → Set Vec3}
    {F : ι → Vec3 → ℝ → W} (hS : IsCoveringLocalSystem D F) :
    (∀ i : ι, ∀ n ∈ D i, ∀ θ : ℝ, bridgeNormalize (F i) n θ = refFam n θ) ∧
      IsJointlyRegularFamily refFam ∧ IsSignTransformationValued refFam ∧
      (∀ G : Vec3 → ℝ → W, (∀ i : ι, ∀ n ∈ D i, ∀ θ : ℝ, bridgeNormalize (F i) n θ = G n θ) →
        ∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, G n θ = refFam n θ) ∧
      (∀ i : ι, ∀ n ∈ D i, ∀ θ : ℝ,
        F i n θ = Bridge (F i) n θ ⋆ refFam n θ ∧ Bridge (F i) n θ ∈ Z) := by
  refine ⟨system_bridgeNormalize_eq_refFam hS, refFam_jointlyRegular,
    reference_signTransformationValued, ?_, ?_⟩
  · intro G hG n hn θ
    obtain ⟨i, hi⟩ := hS.cover n hn
    rw [← hG i n hi θ, system_bridgeNormalize_eq_refFam hS i n hi θ]
  · intro i n hn θ
    exact ⟨bridge_factorization (hS.regular i) (hS.unit i n hn) θ,
      bridge_central (hS.regular i) (hS.unit i n hn) θ⟩

/-- **PRINCIPAL THEOREM (§22, §23, answered).**  The Task-17 system **does** have a
sign-relaxed global reconstruction with explicit central conversion factors: the global
family is `refFam` and the conversion factors are the derived bridges, retained as data. -/
theorem task17System_hasSignRelaxedReconstructionWithFactors :
    HasSignRelaxedReconstructionWithFactors Dom task17System := by
  refine ⟨refFam, refFam_jointlyRegular, reference_signTransformationValued,
    fun _ => Bridge (locFam 0), fun v n hn θ => ?_, fun v n hn θ => ?_⟩
  · exact bridge_central (locFam_jointlyRegular 0) hn.1 θ
  · exact bridge_factorization (locFam_jointlyRegular 0) hn.1 θ

/-! ## §40 — the three failure modes, separated -/

/-- **NEUTRAL DEFINITION.**  A two-member local system on one and the same inherited
domain, carrying the two labels `0` and `1`. -/
noncomputable def twoLabelSystem : Bool → Vec3 → ℝ → W :=
  fun b => if b then locFam 1 else locFam 0

/-- **PRINCIPAL THEOREM (§40), failure mode 1: REFUTATION of literal gluing.**  Ordinary
literal gluing fails as soon as the overlap factor is nontrivial: the two-member system
above consists of admissible local exact representatives, its overlap factor is the central
element of the integer `1`, and it has **no** unrestricted literal global extension. -/
theorem twoLabelSystem_no_literal_extension :
    (∀ b : Bool, IsJointlyRegularFamily (twoLabelSystem b)) ∧
      (∀ b : Bool, IsTransformationValuedOn (Dom e1) (twoLabelSystem b)) ∧
      (∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ,
        ovl (twoLabelSystem true) (twoLabelSystem false) n θ = zexp 0 (1 : ℝ) θ) ∧
      ¬ HasLiteralGlobalExtension (fun _ : Bool => Dom e1) twoLabelSystem := by
  have hreg : ∀ b : Bool, IsJointlyRegularFamily (twoLabelSystem b) := by
    intro b
    cases b
    · exact locFam_jointlyRegular 0
    · exact locFam_jointlyRegular 1
  have hex : ∀ b : Bool, IsTransformationValuedOn (Dom e1) (twoLabelSystem b) := by
    intro b
    cases b
    · exact locFam_transformationValuedOn 0 e1
    · exact locFam_transformationValuedOn 1 e1
  refine ⟨hreg, hex, ?_, ?_⟩
  · intro n hn θ
    have h1 : rateAlpha (locFam 1) n = 0 := (locFam_rates 1 hn).1
    have h0 : rateAlpha (locFam 0) n = 0 := (locFam_rates 0 hn).1
    have := ovl_explicit (locFam_jointlyRegular 1) (locFam_jointlyRegular 0) hn h1 h0 θ
    rw [(locFam_rates 1 hn).2, (locFam_rates 0 hn).2] at this
    show ovl (locFam 1) (locFam 0) n θ = zexp 0 1 θ
    rw [this]
    congr 1
    norm_num
  · rintro ⟨G, -, hres⟩
    have heq : ∀ n ∈ Dom e1, ∀ θ : ℝ, locFam 0 n θ = locFam 1 n θ := by
      intro n hn θ
      have hf : locFam 0 n θ = twoLabelSystem false n θ := rfl
      have ht : locFam 1 n θ = twoLabelSystem true n θ := rfl
      rw [hf, ht, ← hres false n hn θ, ← hres true n hn θ]
    have := locFam_injective_on_Dom e1_ne_zero heq
    exact absurd this (by norm_num)

/-- **PRINCIPAL THEOREM (§40).**  The three failure modes are distinguished, and only the
first two are failures: literal gluing can fail; literal sign-relaxed reconstruction fails
even for the completely compatible Task-17 system; bridge-normalized reconstruction never
fails, and the Task-17 system is reconstructible once the explicit central conversion
factors are retained. -/
theorem three_failure_modes_distinguished :
    (¬ HasLiteralGlobalExtension (fun _ : Bool => Dom e1) twoLabelSystem) ∧
      HasLiteralGlobalExtension Dom task17System ∧
      (¬ HasSignRelaxedReconstruction Dom task17System) ∧
      HasSignRelaxedReconstructionWithFactors Dom task17System :=
  ⟨(twoLabelSystem_no_literal_extension).2.2.2, task17System_hasLiteralGlobalExtension,
    task17System_no_signRelaxedReconstruction,
    task17System_hasSignRelaxedReconstructionWithFactors⟩

end NullSectorTask18
