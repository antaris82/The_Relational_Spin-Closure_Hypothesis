import RequestProject.Experiment2.NullSectorTask18.MaximalDomains

/-!
# Task 18, Package C: two reconstruction problems, kept apart

Task 17 proved a single negative statement about the system `F_v = locFam 0` on the
inherited domains `Dom v`.  That statement is about **one** of two different reconstruction
problems, and Task 18 must not conflate them.  Both are defined here as predicates on an
arbitrary indexed local system (§21, §22), and the Task-17 system is re-expressed under
both (§23):

* `HasLiteralGlobalExtension` — one jointly regular *global* family whose restriction
  equals every specified local family **exactly**.  Nothing about the sign-relaxed class is
  required.
* `HasSignRelaxedReconstruction` — one jointly regular global family which additionally
  lies in the sign-relaxed class, and which equals every local family by **literal
  equality**.
* `HasSignRelaxedReconstructionWithFactors` — one jointly regular sign-relaxed global
  family together with **explicit central conversion factors**, one per index, retained as
  data and not quotiented; the local families are recovered from the global one by
  multiplying by their factor.

Results:

* §24.  The Task-17 system **does** have an unrestricted literal global extension, namely
  the already global family `locFam 0`.
* §25.  The Task-17 system has **no** sign-relaxed reconstruction by literal equality
  (Task-17 endpoint, restated in the present vocabulary and kept independent).
* Consequently the two predicates are provably different (`literal_and_signRelaxed_differ`).

The third predicate is settled in Package E, after the bridge factor has been derived.
-/

namespace NullSectorTask18

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17

/-! ## §21, §22 — the three predicates -/

/-- **NEUTRAL DEFINITION (§21).**  An *unrestricted literal global extension* of an indexed
local system: one jointly regular global family whose restriction to each domain equals the
corresponding local family exactly.  No membership in the sign-relaxed class is
required. -/
def HasLiteralGlobalExtension {ι : Type*} (D : ι → Set Vec3) (F : ι → Vec3 → ℝ → W) : Prop :=
  ∃ G : Vec3 → ℝ → W, IsJointlyRegularFamily G ∧
    ∀ i : ι, ∀ n ∈ D i, ∀ θ : ℝ, G n θ = F i n θ

/-- **NEUTRAL DEFINITION (§22), literal version.**  A *sign-relaxed reconstruction by
literal equality*: the global family is additionally required to lie in the sign-relaxed
class. -/
def HasSignRelaxedReconstruction {ι : Type*} (D : ι → Set Vec3)
    (F : ι → Vec3 → ℝ → W) : Prop :=
  ∃ G : Vec3 → ℝ → W, IsJointlyRegularFamily G ∧ IsSignTransformationValued G ∧
    ∀ i : ι, ∀ n ∈ D i, ∀ θ : ℝ, G n θ = F i n θ

/-- **NEUTRAL DEFINITION (§22), conversion version.**  A *sign-relaxed global
reconstruction with explicit local conversion factors*: one jointly regular sign-relaxed
global family, together with one central factor per index, retained explicitly as data,
from which every local family is recovered.  Nothing is quotiented. -/
def HasSignRelaxedReconstructionWithFactors {ι : Type*} (D : ι → Set Vec3)
    (F : ι → Vec3 → ℝ → W) : Prop :=
  ∃ G : Vec3 → ℝ → W, IsJointlyRegularFamily G ∧ IsSignTransformationValued G ∧
    ∃ c : ι → Vec3 → ℝ → W,
      (∀ i : ι, ∀ n ∈ D i, ∀ θ : ℝ, c i n θ ∈ Z) ∧
      (∀ i : ι, ∀ n ∈ D i, ∀ θ : ℝ, F i n θ = c i n θ ⋆ G n θ)

/-! ## §23 — the Task-17 system -/

/-- **NEUTRAL DEFINITION (§23).**  The Task-17 reconstruction system: the inherited domains
indexed by the defining direction, each carrying the same explicit local model `locFam 0`.
Its overlap data are completely trivial. -/
noncomputable def task17System : Vec3 → Vec3 → ℝ → W := fun _ => locFam 0

/-! ## §24 — the literal problem is solvable -/

/-- **PRINCIPAL THEOREM (§24).**  The Task-17 system **does** have an unrestricted literal
global extension: the already global family `locFam 0` restricts to every member of the
system, by literal equality, on every inherited domain. -/
theorem task17System_hasLiteralGlobalExtension :
    HasLiteralGlobalExtension Dom task17System :=
  ⟨locFam 0, locFam_jointlyRegular 0, fun _ _ _ _ => rfl⟩

/-- **DERIVED (§24).**  The extension is unique at every unit direction, because the
inherited domains cover the unit directions. -/
theorem task17System_literal_extension_unique {G : Vec3 → ℝ → W}
    (h : ∀ v : Vec3, ∀ n ∈ Dom v, ∀ θ : ℝ, G n θ = task17System v n θ) :
    ∀ n : Vec3, IsUnitAxis n → ∀ θ : ℝ, G n θ = locFam 0 n θ := by
  intro n hn θ
  exact h n n (Dom_covers hn) θ

/-! ## §25 — the sign-relaxed problem is not solvable -/

/-- **PRINCIPAL THEOREM (§25), inherited refutation restated.**  The very same local system
has **no** sign-relaxed reconstruction by literal equality.  This is the Task-17 endpoint,
retained independently of §24. -/
theorem task17System_no_signRelaxedReconstruction :
    ¬ HasSignRelaxedReconstruction Dom task17System := by
  rintro ⟨G, hG, hsign, hres⟩
  have hexact : IsTransformationValuedOn (Dom e1) G := by
    intro a ha b hb θ φ hP
    rw [hres e1 a ha θ, hres e1 b hb φ]
    exact locFam_transformationValuedOn 0 e1 a ha b hb θ φ hP
  exact exact_local_not_signTransformationValued hG e1_ne_zero hexact hsign

/-- **PRINCIPAL THEOREM (§23–§25).**  The two reconstruction problems are genuinely
different: one and the same indexed local system solves the first and fails the second. -/
theorem literal_and_signRelaxed_differ :
    HasLiteralGlobalExtension Dom task17System ∧
      ¬ HasSignRelaxedReconstruction Dom task17System :=
  ⟨task17System_hasLiteralGlobalExtension, task17System_no_signRelaxedReconstruction⟩

end NullSectorTask18
