import RequestProject.Experiment2.NullSectorTask15.DifferentiableLift

/-!
# Task 15, Layer 3 (§IV): the exact finite central composition law

For an arbitrary choice of internal implementers `u` (with two-sided inverses `ui`) the
**central discrepancy** of a finite composition is defined intrinsically as

```
c g h := (u g ⋆ u h) ⋆ ui (g ∘ h) ,
```

an element of the carrier.  Nothing is quotiented, no equivalence of implementers is
imposed, and no cohomological vocabulary is used.

The results are

* `central_discrepancy_mem_Z` — `c g h` lies in the exact centre and is invertible there;
* `composition_law` — `u g ⋆ u h = c g h ⋆ u (g ∘ h)`, exactly as demanded in §IV;
* `central_discrepancy_assoc` — the only identity forced by associativity of the carrier,
  derived from associativity alone;
* `central_discrepancy_left_unit` / `_right_unit` — the two normalizations;
* `central_discrepancy_redefinition` — how `c` changes under a central redefinition of the
  implementer choice;
* the explicit regular split (`regular_word_factor`, `regular_word_defect_split`,
  `mixed_regular_product`, `mixed_regular_central_defect`): the part of the discrepancy
  that is fixed by the inherited `±1` reference-word defect is separated from the part
  produced by the residual central factor `z`.
-/

namespace NullSectorTask15

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14

/-! ## §IV — the central discrepancy of a lift choice -/

/-- **NEUTRAL DEFINITION (§IV).**  The central discrepancy of a finite composition for the
implementer choice `(u, ui)`. -/
noncomputable def cdisc (u ui : (W →ₗ[ℝ] W) → W) (g h : W →ₗ[ℝ] W) : W :=
  (u g ⋆ u h) ⋆ ui (g.comp h)

/-- **DERIVED (bookkeeping).**  Two central prefactors of a product may be collected. -/
theorem central_pair_shuffle {za zb : W} (hzb : zb ∈ Z) (x y : W) :
    (za ⋆ x) ⋆ (zb ⋆ y) = (za ⋆ zb) ⋆ (x ⋆ y) := by
  calc (za ⋆ x) ⋆ (zb ⋆ y) = za ⋆ ((x ⋆ zb) ⋆ y) := by simp only [mul_assoc_W]
    _ = za ⋆ ((zb ⋆ x) ⋆ y) := by rw [← Z_central hzb]
    _ = (za ⋆ zb) ⋆ (x ⋆ y) := by simp only [mul_assoc_W]

variable {u ui : (W →ₗ[ℝ] W) → W}

/-- **PRINCIPAL THEOREM (§IV).**  The discrepancy lies in the exact centre. -/
theorem central_discrepancy_mem_Z
    (hspec : ∀ g : W →ₗ[ℝ] W, IsImplementable g → Implements (u g) (ui g) g)
    {g h : W →ₗ[ℝ] W} (hg : IsImplementable g) (hh : IsImplementable h) :
    cdisc u ui g h ∈ Z :=
  implements_defect_mem_Z (Implements.mul (hspec g hg) (hspec h hh))
    (hspec (g.comp h) (isImplementable_comp hg hh))

/-- **PRINCIPAL THEOREM (§IV): the exact finite composition law.**  Two implementers
compose to the implementer of the composite up to the central discrepancy. -/
theorem composition_law
    (hspec : ∀ g : W →ₗ[ℝ] W, IsImplementable g → Implements (u g) (ui g) g)
    {g h : W →ₗ[ℝ] W} (hg : IsImplementable g) (hh : IsImplementable h) :
    u g ⋆ u h = cdisc u ui g h ⋆ u (g.comp h) := by
  rw [cdisc, mul_assoc_W, (hspec (g.comp h) (isImplementable_comp hg hh)).inv_left, mul_one_W]

/-- **DERIVED (§IV).**  The discrepancy is an invertible central element. -/
theorem central_discrepancy_unit
    (hspec : ∀ g : W →ₗ[ℝ] W, IsImplementable g → Implements (u g) (ui g) g)
    {g h : W →ₗ[ℝ] W} (hg : IsImplementable g) (hh : IsImplementable h) :
    IsCentralUnit (cdisc u ui g h) := by
  have hZ := central_discrepancy_mem_Z hspec hg hh
  have hI := Implements.mul (hspec g hg) (hspec h hh)
  have hJ := hspec (g.comp h) (isImplementable_comp hg hh)
  have h1 : cdisc u ui g h ⋆ (u (g.comp h) ⋆ (ui h ⋆ ui g)) = w1 := by
    calc cdisc u ui g h ⋆ (u (g.comp h) ⋆ (ui h ⋆ ui g))
        = (u g ⋆ u h) ⋆ ((ui (g.comp h) ⋆ u (g.comp h)) ⋆ (ui h ⋆ ui g)) := by
          simp only [cdisc, mul_assoc_W]
      _ = (u g ⋆ u h) ⋆ (ui h ⋆ ui g) := by rw [hJ.inv_left, one_mul_W]
      _ = w1 := hI.inv_right
  have h2 : (u (g.comp h) ⋆ (ui h ⋆ ui g)) ⋆ cdisc u ui g h = w1 := by
    calc (u (g.comp h) ⋆ (ui h ⋆ ui g)) ⋆ cdisc u ui g h
        = (u (g.comp h) ⋆ ((ui h ⋆ ui g) ⋆ (u g ⋆ u h))) ⋆ ui (g.comp h) := by
          simp only [cdisc, mul_assoc_W]
      _ = u (g.comp h) ⋆ ui (g.comp h) := by rw [hI.inv_left, mul_one_W]
      _ = w1 := hJ.inv_right
  exact ⟨hZ, u (g.comp h) ⋆ (ui h ⋆ ui g), central_inv_mem_Z hZ h1 h2, h1, h2⟩

/-- **PRINCIPAL THEOREM (§IV): the identity forced by associativity.**  Derived from
associativity of the carrier product and centrality of the discrepancy alone; no further
structure is used, and the identity is stated without any quotient. -/
theorem central_discrepancy_assoc
    (hspec : ∀ g : W →ₗ[ℝ] W, IsImplementable g → Implements (u g) (ui g) g)
    {g h k : W →ₗ[ℝ] W} (hg : IsImplementable g) (hh : IsImplementable h)
    (hk : IsImplementable k) :
    cdisc u ui g h ⋆ cdisc u ui (g.comp h) k = cdisc u ui h k ⋆ cdisc u ui g (h.comp k) := by
  have hghk : (g.comp h).comp k = g.comp (h.comp k) := rfl
  have hcgh := central_discrepancy_mem_Z hspec hg hh
  have hchk := central_discrepancy_mem_Z hspec hh hk
  -- expand the triple product in the two possible ways
  have h1 : (u g ⋆ u h) ⋆ u k
      = (cdisc u ui g h ⋆ cdisc u ui (g.comp h) k) ⋆ u ((g.comp h).comp k) := by
    rw [composition_law hspec hg hh, mul_assoc_W,
      composition_law hspec (isImplementable_comp hg hh) hk, ← mul_assoc_W]
  have h2 : u g ⋆ (u h ⋆ u k)
      = (cdisc u ui h k ⋆ cdisc u ui g (h.comp k)) ⋆ u (g.comp (h.comp k)) := by
    rw [composition_law hspec hh hk]
    calc u g ⋆ (cdisc u ui h k ⋆ u (h.comp k))
        = cdisc u ui h k ⋆ (u g ⋆ u (h.comp k)) := by
          rw [← mul_assoc_W, ← Z_central hchk, mul_assoc_W]
      _ = cdisc u ui h k ⋆ (cdisc u ui g (h.comp k) ⋆ u (g.comp (h.comp k))) := by
          rw [composition_law hspec hg (isImplementable_comp hh hk)]
      _ = (cdisc u ui h k ⋆ cdisc u ui g (h.comp k)) ⋆ u (g.comp (h.comp k)) :=
          (mul_assoc_W _ _ _).symm
  have h3 := (mul_assoc_W (u g) (u h) (u k)).symm.trans h1
  rw [h2, hghk] at h3
  -- cancel the common implementer of the triple composite
  have hgi : IsImplementable (g.comp (h.comp k)) :=
    isImplementable_comp hg (isImplementable_comp hh hk)
  have hcancel : ∀ x y : W, x ⋆ u (g.comp (h.comp k)) = y ⋆ u (g.comp (h.comp k)) → x = y := by
    intro x y hxy
    have := congrArg (fun t => t ⋆ ui (g.comp (h.comp k))) hxy
    simpa only [mul_assoc_W, (hspec _ hgi).inv_right, mul_one_W] using this
  exact (hcancel _ _ h3.symm)

/-- **DERIVED (§IV).**  The identity map is implementable. -/
theorem isImplementable_id : IsImplementable (LinearMap.id : W →ₗ[ℝ] W) :=
  ⟨w1, w1, mul_one_W w1, mul_one_W w1, fun x => by
    show (w1 ⋆ x) ⋆ w1 = x
    rw [one_mul_W, mul_one_W]⟩

/-- **DERIVED (§IV), normalization.**  If the identity automorphism is implemented by the
carrier unit, the discrepancy is trivial whenever one argument is the identity. -/
theorem central_discrepancy_units
    (hspec : ∀ g : W →ₗ[ℝ] W, IsImplementable g → Implements (u g) (ui g) g)
    (hu1 : u LinearMap.id = w1)
    {g : W →ₗ[ℝ] W} (hg : IsImplementable g) :
    cdisc u ui LinearMap.id g = w1 ∧ cdisc u ui g LinearMap.id = w1 := by
  constructor
  · rw [cdisc, LinearMap.id_comp, hu1, one_mul_W, (hspec g hg).inv_right]
  · rw [cdisc, LinearMap.comp_id, hu1, mul_one_W, (hspec g hg).inv_right]

/-! ## §IV — central redefinition of the lift choice -/

/-- **PRINCIPAL THEOREM (§IV): the redefinition law.**  Under a regular central
redefinition `u' g = lam g ⋆ u g` of the implementer choice, the central discrepancy is
multiplied by the corresponding central factor of the three transformations involved.  No
quotient and no equivalence relation is introduced: the change is an explicit identity. -/
theorem central_discrepancy_redefinition
    (lam lami : (W →ₗ[ℝ] W) → W)
    (hlam : ∀ g : W →ₗ[ℝ] W, lam g ∈ Z) (hlami : ∀ g : W →ₗ[ℝ] W, lami g ∈ Z)
    (g h : W →ₗ[ℝ] W) :
    cdisc (fun g => lam g ⋆ u g) (fun g => ui g ⋆ lami g) g h
      = ((lam g ⋆ lam h) ⋆ lami (g.comp h)) ⋆ cdisc u ui g h := by
  calc cdisc (fun g => lam g ⋆ u g) (fun g => ui g ⋆ lami g) g h
      = ((lam g ⋆ u g) ⋆ (lam h ⋆ u h)) ⋆ (ui (g.comp h) ⋆ lami (g.comp h)) := rfl
    _ = ((lam g ⋆ lam h) ⋆ (u g ⋆ u h)) ⋆ (lami (g.comp h) ⋆ ui (g.comp h)) := by
        rw [central_pair_shuffle (hlam h), Z_central (hlami (g.comp h))]
    _ = (((lam g ⋆ lam h) ⋆ lami (g.comp h))) ⋆ ((u g ⋆ u h) ⋆ ui (g.comp h)) :=
        central_pair_shuffle (hlami (g.comp h)) _ _
    _ = ((lam g ⋆ lam h) ⋆ lami (g.comp h)) ⋆ cdisc u ui g h := rfl

/-! ## §IV — the explicit regular split of the discrepancy -/

/-- **NEUTRAL DEFINITION.**  The internal element of a word for a per-axis lift family. -/
noncomputable def liftWordVal (U : Vec3 → ℝ → W) : AxisWord → W
  | [] => w1
  | p :: t => U p.1 p.2 ⋆ liftWordVal U t

/-- **NEUTRAL DEFINITION.**  The internal element of the reversed inverse word. -/
noncomputable def liftWordInv (U : Vec3 → ℝ → W) : AxisWord → W
  | [] => w1
  | p :: t => liftWordInv U t ⋆ U p.1 (-p.2)

/-- **NEUTRAL DEFINITION.**  The accumulated central residual of a word. -/
noncomputable def zWord (z : Vec3 → ℝ → W) : AxisWord → W
  | [] => w1
  | p :: t => z p.1 p.2 ⋆ zWord z t

/-- **NEUTRAL DEFINITION.**  The accumulated central residual of the reversed inverse
word. -/
noncomputable def zWordInv (z : Vec3 → ℝ → W) : AxisWord → W
  | [] => w1
  | p :: t => zWordInv z t ⋆ z p.1 (-p.2)

theorem zWord_mem_Z {z : Vec3 → ℝ → W} (hz : ∀ n θ, z n θ ∈ Z) (l : AxisWord) :
    zWord z l ∈ Z := by
  induction l with
  | nil => exact w1_mem_Z
  | cons p t ih => exact Z_mul_mem (hz p.1 p.2) ih

theorem zWordInv_mem_Z {z : Vec3 → ℝ → W} (hz : ∀ n θ, z n θ ∈ Z) (l : AxisWord) :
    zWordInv z l ∈ Z := by
  induction l with
  | nil => exact w1_mem_Z
  | cons p t ih => exact Z_mul_mem ih (hz p.1 (-p.2))

/-- **PRINCIPAL THEOREM (§IV), regular split, forward word.**  For a regular per-axis lift
family the internal element of a word is the accumulated central residual times the
inherited reference word. -/
theorem regular_word_factor {U : Vec3 → ℝ → W} {z : Vec3 → ℝ → W}
    (hz : ∀ n θ, z n θ ∈ Z) (hU : ∀ n θ, U n θ = z n θ ⋆ Un n θ) (l : AxisWord) :
    liftWordVal U l = zWord z l ⋆ wordVal l := by
  induction l with
  | nil => rw [liftWordVal, zWord, wordVal_nil, one_mul_W]
  | cons p t ih =>
      rw [liftWordVal, zWord, ih, hU]
      show (z p.1 p.2 ⋆ Un p.1 p.2) ⋆ (zWord z t ⋆ wordVal t)
        = (z p.1 p.2 ⋆ zWord z t) ⋆ (Un p.1 p.2 ⋆ wordVal t)
      calc (z p.1 p.2 ⋆ Un p.1 p.2) ⋆ (zWord z t ⋆ wordVal t)
          = z p.1 p.2 ⋆ ((Un p.1 p.2 ⋆ zWord z t) ⋆ wordVal t) := by
            simp only [mul_assoc_W]
        _ = z p.1 p.2 ⋆ ((zWord z t ⋆ Un p.1 p.2) ⋆ wordVal t) := by
            rw [← Z_central (zWord_mem_Z hz t)]
        _ = (z p.1 p.2 ⋆ zWord z t) ⋆ (Un p.1 p.2 ⋆ wordVal t) := by
            simp only [mul_assoc_W]

/-- **PRINCIPAL THEOREM (§IV), regular split, inverse word. -/
theorem regular_wordInv_factor {U : Vec3 → ℝ → W} {z : Vec3 → ℝ → W}
    (hz : ∀ n θ, z n θ ∈ Z) (hU : ∀ n θ, U n θ = z n θ ⋆ Un n θ) (l : AxisWord) :
    liftWordInv U l = zWordInv z l ⋆ wordInv l := by
  induction l with
  | nil => rw [liftWordInv, zWordInv, wordInv_nil, one_mul_W]
  | cons p t ih =>
      rw [liftWordInv, zWordInv, ih, hU]
      show (zWordInv z t ⋆ wordInv t) ⋆ (z p.1 (-p.2) ⋆ Un p.1 (-p.2))
        = (zWordInv z t ⋆ z p.1 (-p.2)) ⋆ (wordInv t ⋆ Un p.1 (-p.2))
      calc (zWordInv z t ⋆ wordInv t) ⋆ (z p.1 (-p.2) ⋆ Un p.1 (-p.2))
          = zWordInv z t ⋆ ((wordInv t ⋆ z p.1 (-p.2)) ⋆ Un p.1 (-p.2)) := by
            simp only [mul_assoc_W]
        _ = zWordInv z t ⋆ ((z p.1 (-p.2) ⋆ wordInv t) ⋆ Un p.1 (-p.2)) := by
            rw [← Z_central (hz p.1 (-p.2))]
        _ = (zWordInv z t ⋆ z p.1 (-p.2)) ⋆ (wordInv t ⋆ Un p.1 (-p.2)) := by
            simp only [mul_assoc_W]

/-- **PRINCIPAL THEOREM (§IV): which part of the discrepancy is the inherited sign and
which part is the residual.**  For two words of a regular per-axis lift inducing the *same*
inherited algebra automorphism, the internal discrepancy is the accumulated central
residual multiplied by the inherited reference-word defect, which is exactly `±1`
(Task 14).  The two contributions are completely separated. -/
theorem regular_word_defect_split {U : Vec3 → ℝ → W} {z : Vec3 → ℝ → W}
    (hz : ∀ n θ, z n θ ∈ Z) (hU : ∀ n θ, U n θ = z n θ ⋆ Un n θ)
    {l l' : AxisWord} (hl : IsUnitWord l) (hl' : IsUnitWord l')
    (haut : wordAut l = wordAut l') :
    liftWordVal U l ⋆ liftWordInv U l'
        = (zWord z l ⋆ zWordInv z l') ⋆ (wordVal l ⋆ wordInv l') ∧
      (wordVal l ⋆ wordInv l' = w1 ∨ wordVal l ⋆ wordInv l' = -w1) := by
  refine ⟨?_, reference_word_defect hl hl' haut⟩
  rw [regular_word_factor hz hU, regular_wordInv_factor hz hU]
  calc (zWord z l ⋆ wordVal l) ⋆ (zWordInv z l' ⋆ wordInv l')
      = zWord z l ⋆ ((wordVal l ⋆ zWordInv z l') ⋆ wordInv l') := by
        simp only [mul_assoc_W]
    _ = zWord z l ⋆ ((zWordInv z l' ⋆ wordVal l) ⋆ wordInv l') := by
        rw [← Z_central (zWordInv_mem_Z hz l')]
    _ = (zWord z l ⋆ zWordInv z l') ⋆ (wordVal l ⋆ wordInv l') := by
        simp only [mul_assoc_W]

/-! ## §IV — the mixed two-axis product in explicit regular form -/

/-- **DERIVED (§IV).**  The mixed product of two regular axis lifts is the product of the
two central residuals times the inherited mixed reference product. -/
theorem mixed_regular_product {z : Vec3 → ℝ → W} (hz : ∀ n θ, z n θ ∈ Z)
    (n m : Vec3) (θ φ : ℝ) :
    (z n θ ⋆ Un n θ) ⋆ (z m φ ⋆ Un m φ) = (z n θ ⋆ z m φ) ⋆ (Un n θ ⋆ Un m φ) := by
  calc (z n θ ⋆ Un n θ) ⋆ (z m φ ⋆ Un m φ)
      = z n θ ⋆ ((Un n θ ⋆ z m φ) ⋆ Un m φ) := by simp only [mul_assoc_W]
    _ = z n θ ⋆ ((z m φ ⋆ Un n θ) ⋆ Un m φ) := by rw [← Z_central (hz m φ)]
    _ = (z n θ ⋆ z m φ) ⋆ (Un n θ ⋆ Un m φ) := by simp only [mul_assoc_W]

/-- **PRINCIPAL THEOREM (§IV): the mixed-axis central composition defect, explicitly.**
Whenever the inherited mixed reference product closes on a single reference implementation
(Task 14, closure notion **B**), the composition defect of the regular lift is exactly the
central element `z n θ ⋆ z m φ ⋆ (z k ψ)⁻¹`: the reference part contributes nothing and the
whole defect comes from the residual. -/
theorem mixed_regular_central_defect {z : Vec3 → ℝ → W} (hz : ∀ n θ, z n θ ∈ Z)
    {n m k : Vec3} {θ φ ψ : ℝ} (hk : Un n θ ⋆ Un m φ = Un k ψ)
    {zi : W} (hzi : zi ∈ Z) (hinv : z k ψ ⋆ zi = w1) :
    (z n θ ⋆ Un n θ) ⋆ (z m φ ⋆ Un m φ)
      = ((z n θ ⋆ z m φ) ⋆ zi) ⋆ (z k ψ ⋆ Un k ψ) := by
  rw [mixed_regular_product hz, hk]
  calc (z n θ ⋆ z m φ) ⋆ Un k ψ
      = ((z n θ ⋆ z m φ) ⋆ (zi ⋆ z k ψ)) ⋆ Un k ψ := by
        rw [Z_central hzi (z k ψ), hinv, mul_one_W]
    _ = ((z n θ ⋆ z m φ) ⋆ zi) ⋆ (z k ψ ⋆ Un k ψ) := by simp only [mul_assoc_W]

end NullSectorTask15
