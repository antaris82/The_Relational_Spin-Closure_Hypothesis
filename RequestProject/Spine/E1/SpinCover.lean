import Mathlib
import RequestProject.Spine.E1.SpinGroup
import RequestProject.Spine.E1.DoubleCover

/-!
# Spine / E1 : the intrinsic Spin → Lorentz homomorphism

This module packages the twisted Clifford action of the intrinsic spin group on the Lorentz
carrier as a genuine **group homomorphism**

`SpinCore.spinCover : SpinGroup →* GLor`

onto the intrinsic Lorentz group of the carrier, and proves it **surjective**.

Both facts are consequences of the intrinsic Clifford material only:

* the action `SpinCore.spinLor` and its multiplicativity (`Paravector`);
* membership of the induced map in `G_L` (`SpinDeterminant`);
* realisability of every element of `G_L` by a spin element
  (`SpinCore.spinLor_surjective_onto_GLor`, `DoubleCover`).

**Import firewall.**  `Mathlib` plus the intrinsic experiment-1 Clifford/spin layer.  In
particular *not* `RequestProject.Spine.E1.SL2Comparison`, *not* the complex matrix model
`MatrixModel` / `PauliRepresentation`, *not* the Hermitian comparison endpoint, *not* the
Weyl-spinor module, and no module of either historical experiment tree.

**Provenance.**  `spinCover`, `spinCover_apply` and `spinCover_surjective` are the
declarations of the same names in `RequestProject.Spine.E1.SL2Comparison`, moved here with
their proofs unchanged except for the renaming `SpinGrp → SpinGroup` and the use of
`SpinCore.mkSpin`.  The imports of `MatrixModel` / `PauliRepresentation` they inherited from
that module are removed: neither was used by these proofs.
-/

noncomputable section

open CliffordAlgebra

namespace SpinCore

/-- **The intrinsic spin cover.**  The twisted Clifford action of the spin group on the
carrier, as a group homomorphism into the intrinsic Lorentz group `G_L`. -/
def spinCover : SpinGroup →* GLor where
  toFun u := ⟨spinLorEquiv u.2, spinLorEquiv_mem_GLor u.2⟩
  map_one' := by
    refine Subtype.ext (LinearEquiv.ext fun x => ?_)
    show spinLor ((1 : Cl3ˣ) : Cl3) x = _
    rw [Units.val_one, spinLor_one]
    simp
  map_mul' a b := by
    refine Subtype.ext (LinearEquiv.ext fun x => ?_)
    show spinLor (((a * b : SpinGroup) : Cl3ˣ) : Cl3) x = _
    rw [Subgroup.coe_mul, Units.val_mul,
      spinLor_mul ((a : Cl3ˣ) : Cl3) ((b : Cl3ˣ) : Cl3) x]
    simp [spinLorEquiv_apply]

@[simp] theorem spinCover_apply (u : SpinGroup) (x : LorentzCarrier) :
    ((spinCover u : GLor) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) x
      = spinLor ((u : Cl3ˣ) : Cl3) x := rfl

/-- **Surjectivity of the intrinsic spin cover.**  Every element of the intrinsic Lorentz
group of the carrier is induced by a spin element of `Cl₃(ℝ)`. -/
theorem spinCover_surjective : Function.Surjective spinCover := by
  intro F
  obtain ⟨g, hg, hF⟩ := spinLor_surjective_onto_GLor F.2
  exact ⟨mkSpin hg, Subtype.ext (by simpa [spinCover] using hF)⟩

/-- The bundled cover recovers the unbundled description of `G_L`: a linear self-equivalence
of the carrier is Lorentz exactly when it is the action of some element of the spin
group. -/
theorem mem_GLor_iff_spinCover (F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) :
    F ∈ GLor ↔ ∃ u : SpinGroup, ∀ x, spinLor ((u : Cl3ˣ) : Cl3) x = F x := by
  constructor
  · intro hF
    obtain ⟨u, hu⟩ := spinCover_surjective ⟨F, hF⟩
    exact ⟨u, fun x => congrArg (fun G : GLor =>
      (G : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) x) hu⟩
  · rintro ⟨u, hu⟩
    have hF : (spinLorEquiv u.2 : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) = F :=
      LinearEquiv.ext fun x => by rw [spinLorEquiv_apply]; exact hu x
    exact hF ▸ spinLorEquiv_mem_GLor u.2

end SpinCore
