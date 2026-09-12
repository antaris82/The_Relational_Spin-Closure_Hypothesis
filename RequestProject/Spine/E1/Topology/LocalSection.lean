import Mathlib
import RequestProject.Spine.E1.Topology.SpinCoverTopology

/-!
# Spine / E1 / Topology : continuous local sections of the intrinsic spin cover

This module closes the last analytic obligation of the generic `E2` interface for the
**intrinsic** algebraic Spin/Lorentz double cover `SpinCore.spinCover : SpinGroup →* GLor`:
it constructs *continuous local sections* around every point of `GLor`, natively, from the
Clifford realisation itself.  Nothing is transported from the downstream `SL(2,ℂ)`
comparison, no covering-map or local-homeomorphism property is postulated, and no manifold
or Lie-group theorem is invoked.

## The mechanism

The construction is an explicit *algebraic inversion* of the twisted Clifford action,
followed by a normalisation that is two-valued exactly because the kernel is `{±1}`.

1. **Contraction (§1).**  `SpinCore.fierz y = y + Σᵢ eᵢ y eᵢ`.  Evaluated in the intrinsic
   eight-monomial frame it annihilates the six non-central monomials and multiplies `1` and
   `ω` by `4`; hence `fierz` lands in the centre `ℝ ⊕ ℝω` (`fierz_eq_central`), and
   `fierz 1 = 4`.
2. **The complex centre (§2).**  `SpinCore.cx : ℂ →ₐ[ℝ] Cl₃(ℝ)` is the algebra map determined
   by `i ↦ ω` (legitimate because `ω² = -1`).  It is injective, central-valued, fixed by
   Clifford conjugation, and continuous; `cxRetract` is a linear retraction of it.
3. **Reconstruction (§3).**  `SpinCore.recon F = A(F ·1) + Σᵢ A(F eᵢ)·eᵢ` is linear, hence
   continuous, in the endomorphism `F`, and satisfies the key identity
   `recon (spinLorLin g) = g * fierz (reverse g)` — the reconstruction of the action of `g`
   is `g` itself, up to a *central* factor.
4. **Discriminant (§4).**  For `F ∈ GLor` write `recon F = cx w · u` with `ρ u = F`.  The
   central number `w` is visible only through its square: `spinDisc F = w²` is a genuine
   function of `F`, and this is precisely where the `ℤ/2` ambiguity sits.
5. **Normalisation (§5–§6).**  Dividing by a square root of the discriminant gives
   `secCl F = ±u` (`secCl_spinCover`), so `spinSection F` is a *bona fide* spin element with
   `ρ (spinSection F) = F` wherever `spinDisc F ≠ 0`, and `spinSection 1 = 1`.
6. **Continuity (§7).**  On the open set `LorNbhd = {F | spinDisc F ∈ slitPlane}`, which
   contains `1` because `spinDisc 1 = 16`, the principal branch of the complex square root
   is continuous; hence `spinSection` is continuous there — as a map into the *unit group*,
   because the inverse of a spin element is its Clifford conjugate.
7. **Transport (§8–§9).**  Two lifts of the same element differ exactly by the kernel
   (`lift_ambiguity`).  Left translation by a chosen lift `ut` of `k` carries the identity
   section to a continuous section on the open neighbourhood `LorNbhdAt k`; changing the
   chosen lift multiplies the transported section by `-1`
   (`transportSection_negOneSpin`).  This yields `spinCover_hasLocalSection`.
8. **Two sheets (§10).**  Over `LorNbhd` the preimage splits as `sheetPlus ∪ sheetMinus`,
   two *disjoint open* sets exchanged by `-1`, with `ρ` restricting to a homeomorphism
   `sheetPlus ≃ₜ LorNbhd`.  Openness is not assumed: each sheet is the relative complement
   of the other, and each is relatively closed as the equaliser of two continuous maps into
   a Hausdorff group.

## What is a choice and what is not

The projection, `fierz`, `cx`, `recon` and `spinDisc` are canonical.  The *branch* of the
square root (equivalently, the choice of sheet) and the *lift* `ut` used in the transport
are choices, and they are choices **exactly up to the central kernel `{±1}`**: this is the
content of `lift_ambiguity` and `transportSection_negOneSpin`.  The section around the
identity is normalised by `spinSection 1 = 1`.

**Import firewall.**  `Mathlib` and the intrinsic experiment-1 spin core with its topology
layer only: no `SL(2,ℂ)` comparison, no complex matrix model, no `RequestProject.Spine.E2`,
no control module, no module of either historical experiment tree.
-/

noncomputable section

open CliffordAlgebra

namespace SpinCore

/-! ## 1.  The reconstruction (contraction) operator on `Cl₃(ℝ)` -/

local macro "cliff" : tactic => `(tactic|
  simp only [mono, omega, mul_assoc, s10, s20, s21, t10, t20, t21, cle_sq_mul, cle_sq,
    mul_neg, neg_neg, neg_mul, mul_one, one_mul])

/-- Conjugation by the third generator, in monomial coordinates. -/
theorem cle2_conj_monoComb (c : Fin 8 → ℝ) :
    cle 2 * monoComb c * cle 2
      = monoComb ![c 0, -c 1, -c 2, c 3, c 4, -c 5, -c 6, c 7] := by
  have h0 : cle 2 * mono 0 * cle 2 = mono 0 := by cliff
  have h1 : cle 2 * mono 1 * cle 2 = -mono 1 := by cliff
  have h2 : cle 2 * mono 2 * cle 2 = -mono 2 := by cliff
  have h3 : cle 2 * mono 3 * cle 2 = mono 3 := by cliff
  have h4 : cle 2 * mono 4 * cle 2 = mono 4 := by cliff
  have h5 : cle 2 * mono 5 * cle 2 = -mono 5 := by cliff
  have h6 : cle 2 * mono 6 * cle 2 = -mono 6 := by cliff
  have h7 : cle 2 * mono 7 * cle 2 = mono 7 := by cliff
  simp only [monoComb, Fin.sum_univ_eight, add_mul, mul_add, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, h0, h1, h2, h3, h4, h5, h6, h7, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simp only [Matrix.cons_val, smul_neg]
  module

/-- The **contraction operator** `y ↦ y + Σᵢ eᵢ y eᵢ` of the intrinsic Clifford algebra. -/
def fierz (y : Cl3) : Cl3 :=
  y + cle 0 * y * cle 0 + cle 1 * y * cle 1 + cle 2 * y * cle 2

/-- In the monomial frame the contraction operator kills all six non-central monomials and
multiplies the two central ones by `4`. -/
theorem fierz_monoComb (c : Fin 8 → ℝ) :
    fierz (monoComb c) = (4 * c 0) • (1 : Cl3) + (4 * c 7) • omega := by
  rw [fierz, cle0_conj_monoComb, cle1_conj_monoComb, cle2_conj_monoComb]
  simp only [monoComb, Fin.sum_univ_eight, mono, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  module

/-- **The contraction operator lands in the centre.** -/
theorem fierz_eq_central (y : Cl3) : ∃ a b : ℝ, fierz y = a • (1 : Cl3) + b • omega := by
  obtain ⟨c, rfl⟩ := exists_monoComb y
  exact ⟨4 * c 0, 4 * c 7, fierz_monoComb c⟩

theorem fierz_one : fierz (1 : Cl3) = (4 : ℝ) • (1 : Cl3) := by
  simp only [fierz, mul_one, cle_sq]
  module

/-! ## 2.  The complex centre of `Cl₃(ℝ)` -/

/-- The canonical `ℝ`-algebra embedding of `ℂ` onto the centre of `Cl₃(ℝ)`, determined by
`i ↦ ω`.  (`ω² = -1` is `SpinCore.omega_sq`.) -/
def cx : ℂ →ₐ[ℝ] Cl3 := Complex.lift ⟨omega, omega_sq⟩

@[simp] theorem cx_I : cx Complex.I = omega := by simp [cx]

theorem cx_ofReal (r : ℝ) : cx (r : ℂ) = algebraMap ℝ Cl3 r := by
  have h : ((r : ℂ)) = algebraMap ℝ ℂ r := rfl
  rw [h, AlgHom.commutes]

theorem cx_apply (z : ℂ) : cx z = z.re • (1 : Cl3) + z.im • omega := by
  have h : cx ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z.re • (1 : Cl3) + z.im • omega := by
    rw [map_add, map_mul, cx_I, cx_ofReal, cx_ofReal, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rwa [Complex.re_add_im] at h

/-- Every central element is in the image of `cx`. -/
theorem cx_mk (a b : ℝ) :
    cx (Complex.mk a b) = a • (1 : Cl3) + b • omega := by
  rw [cx_apply]

theorem cx_injective : Function.Injective cx := (cx : ℂ →+* Cl3).injective

theorem cx_central (z : ℂ) (y : Cl3) : cx z * y = y * cx z := by
  rw [cx_apply, add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul,
    mul_one, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, omega_central]

theorem cconj_cx (z : ℂ) : cconj (cx z) = cx z := by
  rw [cx_apply]; exact cconj_of_central _ _

/-- `cx` as an `ℝ`-linear map. -/
def cxLin : ℂ →ₗ[ℝ] Cl3 := cx.toLinearMap

theorem cxLin_ker : LinearMap.ker cxLin = ⊥ := LinearMap.ker_eq_bot.2 cx_injective

/-- A linear retraction of the central embedding; only its existence is used. -/
def cxRetract : Cl3 →ₗ[ℝ] ℂ :=
  (LinearMap.exists_leftInverse_of_injective cxLin cxLin_ker).choose

@[simp] theorem cxRetract_cx (z : ℂ) : cxRetract (cx z) = z := by
  have h := (LinearMap.exists_leftInverse_of_injective cxLin cxLin_ker).choose_spec
  simpa using LinearMap.congr_fun h z

theorem continuous_cxRetract : Continuous (cxRetract : Cl3 → ℂ) := by
  have h := continuous_linearMap_Cl3 cxRetract
  simpa using h

theorem continuous_cx : Continuous (cx : ℂ → Cl3) := by
  haveI : IsModuleTopology ℝ ℂ := isModuleTopologyOfFiniteDimensional
  have h := IsModuleTopology.continuous_of_linearMap (R := ℝ) cxLin
  simpa [cxLin] using h

/-! ## 3.  Reconstruction of a Clifford element from its Lorentz action -/

/-- **The reconstruction map.**  It is `ℝ`-linear in the endomorphism `F` and is built only
from the paravector embedding and the Clifford product. -/
def recon (F : EndLor) : Cl3 :=
  spinToCl (F sOne) + spinToCl (F ((0 : ℝ), evec 0)) * cle 0
    + spinToCl (F ((0 : ℝ), evec 1)) * cle 1 + spinToCl (F ((0 : ℝ), evec 2)) * cle 2

/-- **The reconstruction identity.**  Applied to the twisted Clifford action of `g`, the
reconstruction map returns `g` multiplied by the central element `fierz (reverse g)`. -/
theorem recon_spinLorLin (g : Cl3) :
    recon (spinLorLin g) = g * fierz (reverse (Q := q3) g) := by
  simp only [recon, spinLorLin_apply, spinToCl_spinLor, spinAct, spinToCl_sOne, spinToCl_cle,
    fierz]
  noncomm_ring

theorem continuous_spinToCl : Continuous (spinToCl : LorentzCarrier → Cl3) := by
  have h := IsModuleTopology.continuous_of_linearMap (R := ℝ) spinToClLin
  simpa using h

theorem continuous_endLor_apply (x : LorentzCarrier) :
    Continuous fun F : EndLor => F x := by
  have h := IsModuleTopology.continuous_of_linearMap (R := ℝ)
    (LinearMap.applyₗ (R := ℝ) (M := LorentzCarrier) (M₂ := LorentzCarrier) x)
  exact h

theorem continuous_recon : Continuous (recon : EndLor → Cl3) := by
  have h : ∀ x : LorentzCarrier, Continuous fun F : EndLor => spinToCl (F x) := fun x =>
    continuous_spinToCl.comp (continuous_endLor_apply x)
  exact (((h sOne).add ((h _).mul continuous_const)).add ((h _).mul continuous_const)).add
    ((h _).mul continuous_const)

/-! ## 4.  The discriminant of a Lorentz element -/

/-- The reconstruction map, read on the intrinsic Lorentz group. -/
def spinRecon (F : GLor) : Cl3 :=
  recon ((F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : EndLor)

theorem spinRecon_spinCover (u : SpinGroup) :
    spinRecon (spinCover u) = ((u : Cl3ˣ) : Cl3) * fierz (reverse (Q := q3) ((u : Cl3ˣ) : Cl3)) := by
  have h : (((spinCover u : GLor) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) : EndLor)
      = spinLorLin ((u : Cl3ˣ) : Cl3) := rfl
  rw [spinRecon, h, recon_spinLorLin]

/-- **The reconstruction of a spin element is that element times a central factor.** -/
theorem exists_cx_spinRecon (u : SpinGroup) :
    ∃ w : ℂ, spinRecon (spinCover u) = cx w * ((u : Cl3ˣ) : Cl3) := by
  obtain ⟨a, b, hab⟩ := fierz_eq_central (reverse (Q := q3) ((u : Cl3ˣ) : Cl3))
  refine ⟨Complex.mk a b, ?_⟩
  rw [spinRecon_spinCover, hab, ← cx_mk]
  exact (cx_central _ _).symm

/-- The **discriminant**: the central square of the reconstruction, read as a complex
number. -/
def spinDisc (F : GLor) : ℂ := cxRetract (spinRecon F * cconj (spinRecon F))

theorem spinDisc_of_cx_spinRecon {u : SpinGroup} {w : ℂ}
    (h : spinRecon (spinCover u) = cx w * ((u : Cl3ˣ) : Cl3)) :
    spinDisc (spinCover u) = w ^ 2 := by
  have hspin : ((u : Cl3ˣ) : Cl3) * cconj ((u : Cl3ˣ) : Cl3) = 1 := u.2.1
  have hprod : spinRecon (spinCover u) * cconj (spinRecon (spinCover u)) = cx (w ^ 2) := by
    rw [h, cconj_mul, cconj_cx, map_pow, sq]
    calc cx w * ((u : Cl3ˣ) : Cl3) * (cconj ((u : Cl3ˣ) : Cl3) * cx w)
        = cx w * (((u : Cl3ˣ) : Cl3) * cconj ((u : Cl3ˣ) : Cl3)) * cx w := by
          noncomm_ring
      _ = cx w * cx w := by rw [hspin, mul_one]
  rw [spinDisc, hprod, cxRetract_cx]

/-! ## 5.  A continuous branch of the square root and the local section -/

/-- The principal branch of the complex square root. -/
def csqrt (z : ℂ) : ℂ := z ^ (1 / 2 : ℂ)

theorem csqrt_mul_self {z : ℂ} (hz : z ≠ 0) : csqrt z * csqrt z = z := by
  rw [csqrt, ← Complex.cpow_add _ _ hz]
  norm_num

theorem csqrt_ne_zero {z : ℂ} (hz : z ≠ 0) : csqrt z ≠ 0 := by
  intro h
  rw [← csqrt_mul_self hz, h, mul_zero] at hz
  exact hz rfl

theorem continuousOn_csqrt : ContinuousOn csqrt Complex.slitPlane := fun _ hz =>
  (continuousAt_cpow_const hz).continuousWithinAt

/-- **The candidate local section**, as a Clifford element: the reconstruction, normalised
by a square root of its discriminant. -/
def secCl (F : GLor) : Cl3 := cx ((csqrt (spinDisc F))⁻¹) * spinRecon F

/-- **The two-valued reconstruction theorem.**  Wherever the discriminant is nonzero, the
normalised reconstruction of `ρ u` is `u` or `-u`. -/
theorem secCl_spinCover (u : SpinGroup) (h0 : spinDisc (spinCover u) ≠ 0) :
    secCl (spinCover u) = ((u : Cl3ˣ) : Cl3) ∨ secCl (spinCover u) = -((u : Cl3ˣ) : Cl3) := by
  obtain ⟨w, hw⟩ := exists_cx_spinRecon u
  have hdisc : spinDisc (spinCover u) = w ^ 2 := spinDisc_of_cx_spinRecon hw
  have hw0 : w ≠ 0 := by
    intro h
    exact h0 (by rw [hdisc, h]; ring)
  have hsq : csqrt (spinDisc (spinCover u)) * csqrt (spinDisc (spinCover u))
      = w ^ 2 := by rw [csqrt_mul_self h0, hdisc]
  set v := csqrt (spinDisc (spinCover u)) with hv
  have hv0 : v ≠ 0 := csqrt_ne_zero h0
  have hfac : (v - w) * (v + w) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 hfac with h | h
  · left
    have hvw : v⁻¹ * w = 1 := by
      rw [sub_eq_zero.1 h]
      field_simp
    rw [secCl, hw, ← hv, ← mul_assoc, ← map_mul, hvw, map_one, one_mul]
  · right
    have hvw : v⁻¹ * w = -1 := by
      rw [eq_neg_of_add_eq_zero_left h]
      field_simp
    rw [secCl, hw, ← hv, ← mul_assoc, ← map_mul, hvw, map_neg, map_one, neg_mul, one_mul]

/-! ## 6.  The local section around the identity -/

theorem spinCover_negOneSpin : spinCover negOneSpin = 1 :=
  (mem_ker_spinCover_iff negOneSpin).2 (Or.inr rfl)

theorem negOneSpin_mul_coe (u : SpinGroup) :
    (((negOneSpin * u : SpinGroup) : Cl3ˣ) : Cl3) = -((u : Cl3ˣ) : Cl3) := by
  rw [Subgroup.coe_mul, Units.val_mul, negOneSpin_coe, neg_one_mul]

/-- **Both normalisations are realised by a genuine spin element.**  Wherever the
discriminant is nonzero the normalised reconstruction of a Lorentz element *is* a spin
element lifting it. -/
theorem exists_spin_lift_secCl {F : GLor} (h0 : spinDisc F ≠ 0) :
    ∃ u : SpinGroup, spinCover u = F ∧ ((u : Cl3ˣ) : Cl3) = secCl F := by
  obtain ⟨u, rfl⟩ := spinCover_surjective F
  rcases secCl_spinCover u h0 with h | h
  · exact ⟨u, rfl, h.symm⟩
  · refine ⟨negOneSpin * u, ?_, ?_⟩
    · rw [map_mul, spinCover_negOneSpin, one_mul]
    · rw [negOneSpin_mul_coe, h]

theorem isSpinElem_secCl {F : GLor} (h0 : spinDisc F ≠ 0) : IsSpinElem (secCl F) := by
  obtain ⟨u, -, h⟩ := exists_spin_lift_secCl h0
  rw [← h]
  exact u.2

open Classical in
/-- **The local section of the intrinsic spin cover**, as a map into the spin group.  Where
the discriminant vanishes the value is irrelevant and is set to `1`. -/
def spinSection (F : GLor) : SpinGroup :=
  if h : IsSpinElem (secCl F) then mkSpin h else 1

theorem spinSection_eq_of_coe {F : GLor} {u : SpinGroup} (hu : ((u : Cl3ˣ) : Cl3) = secCl F) :
    spinSection F = u := by
  have h : IsSpinElem (secCl F) := hu ▸ u.2
  rw [spinSection, dif_pos h]
  exact Subtype.ext (Units.ext (by rw [mkSpin_coe]; exact hu.symm))

theorem spinSection_coe {F : GLor} (h0 : spinDisc F ≠ 0) :
    ((spinSection F : Cl3ˣ) : Cl3) = secCl F := by
  obtain ⟨u, -, h⟩ := exists_spin_lift_secCl h0
  rw [spinSection_eq_of_coe h]
  exact h

/-- **The section property.**  Wherever the discriminant is nonzero, `spinSection` is a
right inverse of the intrinsic cover. -/
theorem spinCover_spinSection {F : GLor} (h0 : spinDisc F ≠ 0) :
    spinCover (spinSection F) = F := by
  obtain ⟨u, hu, h⟩ := exists_spin_lift_secCl h0
  rw [spinSection_eq_of_coe h]
  exact hu

/-! ### The value at the identity -/

theorem spinRecon_one : spinRecon (1 : GLor) = cx 4 := by
  have h : (1 : GLor) = spinCover 1 := (map_one spinCover).symm
  have h1 : (((1 : SpinGroup) : Cl3ˣ) : Cl3) = 1 := rfl
  rw [h, spinRecon_spinCover, h1, reverse.map_one, fierz_one, one_mul,
    show ((4 : ℂ)) = ((4 : ℝ) : ℂ) by norm_num, cx_ofReal, Algebra.algebraMap_eq_smul_one]

theorem spinDisc_one : spinDisc (1 : GLor) = 16 := by
  rw [spinDisc, spinRecon_one, cconj_cx, ← map_mul, cxRetract_cx]
  norm_num

theorem csqrt_sixteen : csqrt 16 = 4 := by
  rw [csqrt, show ((16 : ℂ)) = ((16 : ℝ) : ℂ) by norm_num,
    show ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow (by norm_num)]
  norm_num [Real.rpow_natCast, ← Real.sqrt_eq_rpow]

theorem secCl_one : secCl (1 : GLor) = 1 := by
  rw [secCl, spinRecon_one, spinDisc_one, csqrt_sixteen, ← map_mul]
  norm_num

/-- **The section is normalised at the identity**: it takes the identity of the Lorentz
group to the identity of the spin group (not to `-1`). -/
theorem spinSection_one : spinSection (1 : GLor) = 1 :=
  spinSection_eq_of_coe (by rw [secCl_one]; rfl)

/-! ## 7.  Continuity of the section on an open neighbourhood of the identity -/

/-- The **identity neighbourhood** of the intrinsic Lorentz group on which the normalised
reconstruction is continuous: the discriminant avoids the branch cut of the square root. -/
def LorNbhd : Set GLor := {F | spinDisc F ∈ Complex.slitPlane}

theorem spinDisc_ne_zero_of_mem {F : GLor} (hF : F ∈ LorNbhd) : spinDisc F ≠ 0 :=
  Complex.slitPlane_ne_zero hF

theorem continuous_spinRecon : Continuous (spinRecon : GLor → Cl3) :=
  continuous_recon.comp (continuous_lorAut_toLinearMap.comp continuous_subtype_val)

theorem continuous_spinDisc : Continuous (spinDisc : GLor → ℂ) :=
  continuous_cxRetract.comp
    (continuous_spinRecon.mul (continuous_cconj.comp continuous_spinRecon))

theorem isOpen_LorNbhd : IsOpen LorNbhd :=
  Complex.isOpen_slitPlane.preimage continuous_spinDisc

theorem one_mem_LorNbhd : (1 : GLor) ∈ LorNbhd := by
  have h : spinDisc (1 : GLor) = 16 := spinDisc_one
  show spinDisc (1 : GLor) ∈ Complex.slitPlane
  rw [h]
  norm_num [Complex.mem_slitPlane_iff]

theorem continuousOn_secCl : ContinuousOn secCl LorNbhd := by
  have h1 : ContinuousOn (fun F : GLor => csqrt (spinDisc F)) LorNbhd :=
    continuousOn_csqrt.comp continuous_spinDisc.continuousOn fun _ hF => hF
  have h2 : ContinuousOn (fun F : GLor => (csqrt (spinDisc F))⁻¹) LorNbhd :=
    h1.inv₀ fun _ hF => csqrt_ne_zero (spinDisc_ne_zero_of_mem hF)
  exact (continuous_cx.comp_continuousOn h2).mul continuous_spinRecon.continuousOn

/-- **The local section is continuous** on the identity neighbourhood. -/
theorem continuousOn_spinSection : ContinuousOn spinSection LorNbhd := by
  rw [continuousOn_iff_continuous_restrict]
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · show Continuous fun x : LorNbhd => ((spinSection x.1 : Cl3ˣ) : Cl3)
    have he : (fun x : LorNbhd => ((spinSection x.1 : Cl3ˣ) : Cl3))
        = LorNbhd.restrict secCl := by
      funext x
      exact spinSection_coe (spinDisc_ne_zero_of_mem x.2)
    rw [he, ← continuousOn_iff_continuous_restrict]
    exact continuousOn_secCl
  · show Continuous fun x : LorNbhd => ((spinSection x.1 : Cl3ˣ)⁻¹).val
    have he : (fun x : LorNbhd => ((spinSection x.1 : Cl3ˣ)⁻¹).val)
        = (fun y : Cl3 => cconj y) ∘ LorNbhd.restrict secCl := by
      funext x
      have hs : ((spinSection x.1 : Cl3ˣ) : Cl3) = secCl x.1 :=
        spinSection_coe (spinDisc_ne_zero_of_mem x.2)
      have hspin : IsSpinElem ((spinSection x.1 : Cl3ˣ) : Cl3) := (spinSection x.1).2
      have hinv : ((spinSection x.1 : Cl3ˣ)⁻¹).val = cconj ((spinSection x.1 : Cl3ˣ) : Cl3) :=
        Units.inv_eq_of_mul_eq_one_right hspin.1
      rw [hinv, hs]
      rfl
    rw [he]
    refine continuous_cconj.comp ?_
    rw [← continuousOn_iff_continuous_restrict]
    exact continuousOn_secCl

/-! ## 8.  Kernel ambiguity of lifts -/

/-- **Two lifts of the same Lorentz element differ by the kernel.**  This is the exact sense
in which a local lift is determined only up to the central `ℤ/2`. -/
theorem lift_ambiguity {F : GLor} {u v : SpinGroup} (hu : spinCover u = F)
    (hv : spinCover v = F) : v = u ∨ v = negOneSpin * u := by
  have hker : v * u⁻¹ ∈ spinCover.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hu, hv, mul_inv_cancel]
  rcases (mem_ker_spinCover_iff _).1 hker with h | h
  · left
    have := congrArg (fun w : SpinGroup => w * u) h
    simpa [mul_assoc] using this
  · right
    have := congrArg (fun w : SpinGroup => w * u) h
    simpa [mul_assoc] using this

/-! ## 9.  Transport of the section by group multiplication -/

/-- The identity neighbourhood translated to an arbitrary point of the Lorentz group. -/
def LorNbhdAt (k : GLor) : Set GLor := (fun F => k⁻¹ * F) ⁻¹' LorNbhd

theorem isOpen_LorNbhdAt (k : GLor) : IsOpen (LorNbhdAt k) :=
  isOpen_LorNbhd.preimage (continuous_const.mul continuous_id)

theorem self_mem_LorNbhdAt (k : GLor) : k ∈ LorNbhdAt k := by
  show k⁻¹ * k ∈ LorNbhd
  rw [inv_mul_cancel]
  exact one_mem_LorNbhd

/-- **The transported local section**, attached to a chosen lift `ut` of `k = ρ ut`. -/
def transportSection (ut : SpinGroup) (F : GLor) : SpinGroup :=
  ut * spinSection ((spinCover ut)⁻¹ * F)

theorem spinCover_transportSection (ut : SpinGroup) {F : GLor}
    (hF : F ∈ LorNbhdAt (spinCover ut)) :
    spinCover (transportSection ut F) = F := by
  have h0 : spinDisc ((spinCover ut)⁻¹ * F) ≠ 0 := spinDisc_ne_zero_of_mem hF
  rw [transportSection, map_mul, spinCover_spinSection h0, ← mul_assoc, mul_inv_cancel, one_mul]

theorem continuousOn_transportSection (ut : SpinGroup) :
    ContinuousOn (transportSection ut) (LorNbhdAt (spinCover ut)) := by
  have hinner : Continuous fun F : GLor => (spinCover ut)⁻¹ * F :=
    continuous_const.mul continuous_id
  have h1 : ContinuousOn (fun F : GLor => spinSection ((spinCover ut)⁻¹ * F))
      (LorNbhdAt (spinCover ut)) :=
    continuousOn_spinSection.comp hinner.continuousOn fun _ hF => hF
  exact continuousOn_const.mul h1

/-- **Changing the chosen lift multiplies the transported section by the kernel element.** -/
theorem transportSection_negOneSpin (ut : SpinGroup) (F : GLor) :
    transportSection (negOneSpin * ut) F = negOneSpin * transportSection ut F := by
  rw [transportSection, transportSection, map_mul, spinCover_negOneSpin, one_mul, mul_assoc]

/-- **WP5 / the `hasLocalSection` obligation.**  Around every element of the intrinsic
Lorentz group there is an open neighbourhood carrying a continuous section of the intrinsic
spin cover. -/
theorem spinCover_hasLocalSection (k : GLor) :
    ∃ V : Set GLor, IsOpen V ∧ k ∈ V ∧ ∃ s : GLor → SpinGroup,
      ContinuousOn s V ∧ ∀ y ∈ V, spinCover (s y) = y := by
  obtain ⟨ut, hut⟩ := spinCover_surjective k
  refine ⟨LorNbhdAt k, isOpen_LorNbhdAt k, self_mem_LorNbhdAt k, transportSection ut, ?_, ?_⟩
  · rw [← hut]
    exact continuousOn_transportSection ut
  · intro y hy
    exact spinCover_transportSection ut (by rw [hut]; exact hy)

/-! ## 10.  The local two-sheet structure over the identity neighbourhood -/

/-- The sheet of the preimage of the identity neighbourhood picked out by the normalised
reconstruction. -/
def sheetPlus : Set SpinGroup :=
  {u | spinCover u ∈ LorNbhd ∧ spinSection (spinCover u) = u}

/-- The complementary sheet: the `-1` translate of `sheetPlus`. -/
def sheetMinus : Set SpinGroup :=
  {u | spinCover u ∈ LorNbhd ∧ spinSection (spinCover u) = negOneSpin * u}

theorem negOneSpin_mul_self : negOneSpin * negOneSpin = 1 := by
  have h := negOneSpin_sq
  rwa [pow_two] at h

theorem negOneSpin_mul_mul (u : SpinGroup) : negOneSpin * (negOneSpin * u) = u := by
  rw [← mul_assoc, negOneSpin_mul_self, one_mul]

theorem spinCover_negOneSpin_mul (u : SpinGroup) :
    spinCover (negOneSpin * u) = spinCover u := by
  rw [map_mul, spinCover_negOneSpin, one_mul]

theorem one_mem_sheetPlus : (1 : SpinGroup) ∈ sheetPlus := by
  refine ⟨?_, ?_⟩ <;> rw [map_one]
  · exact one_mem_LorNbhd
  · exact spinSection_one

/-- **The preimage of the identity neighbourhood is the union of the two sheets.** -/
theorem preimage_LorNbhd_eq : spinCover ⁻¹' LorNbhd = sheetPlus ∪ sheetMinus := by
  ext u
  constructor
  · intro hu
    have h0 : spinDisc (spinCover u) ≠ 0 := spinDisc_ne_zero_of_mem hu
    rcases lift_ambiguity (u := u) (v := spinSection (spinCover u)) rfl
      (spinCover_spinSection h0) with h | h
    · exact Or.inl ⟨hu, h⟩
    · exact Or.inr ⟨hu, h⟩
  · rintro (⟨hu, -⟩ | ⟨hu, -⟩) <;> exact hu

/-- **The two sheets are disjoint.** -/
theorem sheetPlus_disjoint_sheetMinus : Disjoint sheetPlus sheetMinus := by
  rw [Set.disjoint_left]
  rintro u ⟨-, h1⟩ ⟨-, h2⟩
  have h3 : negOneSpin * u = u := h2.symm.trans h1
  have hone : negOneSpin = 1 := by
    have h4 := congrArg (fun w : SpinGroup => w * u⁻¹) h3
    simpa [mul_assoc] using h4
  exact negOneSpin_ne_one hone

/-- **The lower sheet is the `-1` translate of the upper one.** -/
theorem sheetMinus_eq_image : sheetMinus = (fun u : SpinGroup => negOneSpin * u) '' sheetPlus := by
  ext u
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨negOneSpin * u, ⟨?_, ?_⟩, negOneSpin_mul_mul u⟩
    · rwa [spinCover_negOneSpin_mul]
    · rw [spinCover_negOneSpin_mul]
      exact h
  · rintro ⟨v, ⟨hv, hsv⟩, rfl⟩
    refine ⟨by rwa [spinCover_negOneSpin_mul], ?_⟩
    rw [spinCover_negOneSpin_mul, hsv, negOneSpin_mul_mul]

/-- **The two sheets are open.** -/
theorem isOpen_sheetPlus_and_sheetMinus : IsOpen sheetPlus ∧ IsOpen sheetMinus := by
  set A : Set SpinGroup := spinCover ⁻¹' LorNbhd with hAdef
  have hA : IsOpen A := isOpen_LorNbhd.preimage continuous_spinCover
  have hf : Continuous fun x : A => spinSection (spinCover x.1) :=
    continuousOn_spinSection.comp_continuous
      (continuous_spinCover.comp continuous_subtype_val) fun x => x.2
  have hid : Continuous fun x : A => (x.1 : SpinGroup) := continuous_subtype_val
  have hneg : Continuous fun x : A => negOneSpin * (x.1 : SpinGroup) :=
    continuous_const.mul continuous_subtype_val
  have hclosedP : IsClosed {x : A | spinSection (spinCover x.1) = x.1} := isClosed_eq hf hid
  have hclosedM : IsClosed {x : A | spinSection (spinCover x.1) = negOneSpin * x.1} :=
    isClosed_eq hf hneg
  have hPimg : sheetPlus = Subtype.val ''
      {x : A | spinSection (spinCover x.1) = negOneSpin * x.1}ᶜ := by
    ext u
    constructor
    · rintro ⟨hu, h⟩
      refine ⟨⟨u, hu⟩, ?_, rfl⟩
      intro hc
      exact Set.disjoint_left.1 sheetPlus_disjoint_sheetMinus ⟨hu, h⟩ ⟨hu, hc⟩
    · rintro ⟨x, hx, rfl⟩
      rcases (Set.ext_iff.1 preimage_LorNbhd_eq x.1).1 x.2 with h | h
      · exact h
      · exact absurd h.2 hx
  have hMimg : sheetMinus = Subtype.val ''
      {x : A | spinSection (spinCover x.1) = x.1}ᶜ := by
    ext u
    constructor
    · rintro ⟨hu, h⟩
      refine ⟨⟨u, hu⟩, ?_, rfl⟩
      intro hc
      exact Set.disjoint_left.1 sheetPlus_disjoint_sheetMinus ⟨hu, hc⟩ ⟨hu, h⟩
    · rintro ⟨x, hx, rfl⟩
      rcases (Set.ext_iff.1 preimage_LorNbhd_eq x.1).1 x.2 with h | h
      · exact absurd h.2 hx
      · exact h
  exact ⟨hPimg ▸ hA.isOpenMap_subtype_val _ hclosedM.isOpen_compl,
    hMimg ▸ hA.isOpenMap_subtype_val _ hclosedP.isOpen_compl⟩

theorem isOpen_sheetPlus : IsOpen sheetPlus := isOpen_sheetPlus_and_sheetMinus.1

theorem isOpen_sheetMinus : IsOpen sheetMinus := isOpen_sheetPlus_and_sheetMinus.2

/-- **The upper sheet maps bijectively onto the identity neighbourhood.** -/
theorem bijOn_spinCover_sheetPlus : Set.BijOn spinCover sheetPlus LorNbhd := by
  refine ⟨fun u hu => hu.1, ?_, ?_⟩
  · intro u hu v hv huv
    rw [← hu.2, ← hv.2, huv]
  · intro F hF
    refine ⟨spinSection F, ⟨?_, ?_⟩, ?_⟩
    · rwa [spinCover_spinSection (spinDisc_ne_zero_of_mem hF)]
    · rw [spinCover_spinSection (spinDisc_ne_zero_of_mem hF)]
    · exact spinCover_spinSection (spinDisc_ne_zero_of_mem hF)

theorem invOn_spinSection_sheetPlus : Set.InvOn spinSection spinCover sheetPlus LorNbhd :=
  ⟨fun _ hu => hu.2, fun _ hF => spinCover_spinSection (spinDisc_ne_zero_of_mem hF)⟩

/-- **The upper sheet is homeomorphic to the identity neighbourhood, via the cover.** -/
def sheetPlusHomeomorph : ↥sheetPlus ≃ₜ ↥LorNbhd where
  toFun u := ⟨spinCover u.1, u.2.1⟩
  invFun F := ⟨spinSection F.1,
    ⟨by rw [spinCover_spinSection (spinDisc_ne_zero_of_mem F.2)]; exact F.2,
     by rw [spinCover_spinSection (spinDisc_ne_zero_of_mem F.2)]⟩⟩
  left_inv u := Subtype.ext u.2.2
  right_inv F := Subtype.ext (spinCover_spinSection (spinDisc_ne_zero_of_mem F.2))
  continuous_toFun := by
    refine continuous_induced_rng.2 ?_
    exact continuous_spinCover.comp continuous_subtype_val
  continuous_invFun := by
    refine continuous_induced_rng.2 ?_
    show Continuous (LorNbhd.restrict spinSection)
    rw [← continuousOn_iff_continuous_restrict]
    exact continuousOn_spinSection

/-! ## 11.  The endpoints -/

/-- **WP4/WP6 endpoint — the local two-sheet structure.**  Over the open identity
neighbourhood `LorNbhd` the preimage of the intrinsic cover splits into two disjoint open
sheets exchanged by the kernel element `-1`; the upper one contains `1`, maps bijectively
onto `LorNbhd`, and does so homeomorphically (`SpinCore.sheetPlusHomeomorph`). -/
theorem intrinsic_spin_cover_local_two_sheets :
    IsOpen LorNbhd ∧ (1 : GLor) ∈ LorNbhd ∧
    IsOpen sheetPlus ∧ IsOpen sheetMinus ∧ (1 : SpinGroup) ∈ sheetPlus ∧
    spinCover ⁻¹' LorNbhd = sheetPlus ∪ sheetMinus ∧
    Disjoint sheetPlus sheetMinus ∧
    sheetMinus = (fun u : SpinGroup => negOneSpin * u) '' sheetPlus ∧
    Set.BijOn spinCover sheetPlus LorNbhd ∧
    Set.InvOn spinSection spinCover sheetPlus LorNbhd ∧
    ContinuousOn spinSection LorNbhd :=
  ⟨isOpen_LorNbhd, one_mem_LorNbhd, isOpen_sheetPlus, isOpen_sheetMinus, one_mem_sheetPlus,
    preimage_LorNbhd_eq, sheetPlus_disjoint_sheetMinus, sheetMinus_eq_image,
    bijOn_spinCover_sheetPlus, invOn_spinSection_sheetPlus, continuousOn_spinSection⟩

/-- **WP5 endpoint — native continuous local sections.**  The intrinsic spin cover admits a
continuous local section around every element of the intrinsic Lorentz group. -/
theorem intrinsic_spin_cover_hasLocalSection :
    ∀ k : GLor, ∃ V : Set GLor, IsOpen V ∧ k ∈ V ∧ ∃ s : GLor → SpinGroup,
      ContinuousOn s V ∧ ∀ y ∈ V, spinCover (s y) = y :=
  spinCover_hasLocalSection

end SpinCore

/-! ## Axiom audit of the local-section layer -/

#print axioms SpinCore.fierz_eq_central
#print axioms SpinCore.recon_spinLorLin
#print axioms SpinCore.secCl_spinCover
#print axioms SpinCore.spinCover_spinSection
#print axioms SpinCore.continuousOn_spinSection
#print axioms SpinCore.spinSection_one
#print axioms SpinCore.lift_ambiguity
#print axioms SpinCore.spinCover_hasLocalSection
#print axioms SpinCore.intrinsic_spin_cover_local_two_sheets
#print axioms SpinCore.intrinsic_spin_cover_hasLocalSection
