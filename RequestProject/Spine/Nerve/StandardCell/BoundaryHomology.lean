import Mathlib.Analysis.Normed.Module.Connected
import RequestProject.Spine.AlgebraicTopology.MayerVietoris
import RequestProject.Spine.AlgebraicTopology.ReducedHomology
import RequestProject.Spine.Nerve.StandardCell.BoundaryCover

/-!
# Task 19, WP5–WP7 : singular homology of spheres and of the realized boundary

This module runs the Mayer–Vietoris induction of WP3/WP4 on the realized boundaries
`Bd r = |∂Δ[r]|`, which Task 17 identifies with the sphere `S^{r-1}`.  The result is the
complete degreewise computation of `H_*(|∂Δ[r]|;ℤ₂)`.

* `SpineTask19.IsLine` — being one-dimensional over `ℤ₂`;
* `SpineTask19.isZero_homology_of_isEmpty` — `H_*(∅) = 0`;
* `SpineTask19.mvOneEquiv` — the Mayer–Vietoris identification `H₁(X) ≃ H̃₀(U ∩ V)`;
* `SpineTask19.sphere_homology` — `H_q(S^n;ℤ₂)` in every degree, by induction on `n`;
* `SpineTask19.bd_isZero`, `SpineTask19.bd_isLine_top`, `SpineTask19.bd_isLine_zero` — the
  same statements for `|∂Δ[r]|`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Simplicial SSet SpineTask14 SpineTask18

universe u

namespace SpineTask19

/-! ## One-dimensional `ℤ₂`-vector spaces -/

/-- `M` is one-dimensional over `ℤ₂`. -/
def IsLine (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] : Prop :=
  Nonempty (M ≃ₗ[ZMod 2] ZMod 2)

theorem IsLine.congr {M N : Type*} [AddCommGroup M] [Module (ZMod 2) M] [AddCommGroup N]
    [Module (ZMod 2) N] (h : IsLine M) (e : M ≃ₗ[ZMod 2] N) : IsLine N :=
  h.map fun f => e.symm.trans f

theorem IsLine.of_iso {M N : ModuleCat.{u} (ZMod 2)} (h : IsLine M) (e : M ≅ N) : IsLine N :=
  h.congr e.toLinearEquiv

/-- The categorical repackaging used by the Task-14 blocker statement. -/
theorem IsLine.nonempty_iso {M : ModuleCat.{u} (ZMod 2)} (h : IsLine M) :
    Nonempty (M ≅ ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) :=
  h.map fun e => (e.trans ULift.moduleEquiv.symm).toModuleIso

/-! ## The empty space -/

theorem isZero_homology_of_isEmpty {X : TopCat.{u}} [IsEmpty ↥X] (q : ℕ) :
    IsZero ((singCx X).homology q) := by
  have hempty : IsEmpty (Sing X q) := ⟨fun σ => IsEmpty.false (sMap σ (stdSimplex.vertex 0))⟩
  refine ModuleCat.isZero_iff_subsingleton.2 (subsingleton_of_forall_eq 0 fun t => ?_)
  obtain ⟨z, hz, rfl⟩ := hcls_surjective t
  have hz0 : z = 0 := by
    refine Finsupp.ext fun a => ?_
    exact (hempty.false a).elim
  subst hz0
  exact hcls_zero hz

/-! ## Mayer–Vietoris in degree one -/

theorem ker_homologyMap_zero_eq_Hred0 {X Y : TopCat.{u}} (g : X ⟶ Y) [PathConnectedSpace ↥Y]
    (y₀ : ↥Y) :
    LinearMap.ker ((HomologicalComplex.homologyMap (singCxMap g) 0).hom) = Hred0 X := by
  ext t
  simp only [LinearMap.mem_ker, Hred0]
  constructor
  · intro ht
    have := augH_natural g t
    rw [ht, map_zero] at this
    exact this.symm
  · intro ht
    refine augH_injective y₀ ?_
    rw [augH_natural g t, ht, map_zero]

section MVOne

variable {X : TopCat.{u}}

/-- **WP3, degree one.**  For a cover of `X` by two contractible open sets, `H₁(X)` is the
reduced `H₀` of the intersection. -/
def mvOneEquiv (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    [ContractibleSpace ↥U] [ContractibleSpace ↥V] :
    (singCx X).homology 1 ≃ₗ[ZMod 2] Hred0 (subTop (U ∩ V)) := by
  classical
  have u₀ : ↥U := Classical.arbitrary ↥U
  have v₀ : ↥V := Classical.arbitrary ↥V
  have hm : Mono (pIota (incV V) 0) := mono_homologyMap_zero (subInc V) v₀
  have hmono : Function.Injective ((pairDelta (incUW U V) (incUW_injective U V) 0).hom) :=
    (ModuleCat.mono_iff_injective _).1 (mv_mono_delta_one U V)
  have hrange : LinearMap.range ((pairDelta (incUW U V) (incUW_injective U V) 0).hom)
      = Hred0 (subTop (U ∩ V)) := by
    rw [mv_range_delta_one U V]
    exact ker_homologyMap_zero_eq_Hred0 (incInterU U V) u₀
  exact ((mvIsoOne U V hU hV hUV hm).toLinearEquiv.trans
    (LinearEquiv.ofInjective _ hmono)).trans (LinearEquiv.ofEq _ _ hrange)

end MVOne

/-! ## The realized boundaries in low degree -/

instance totallyDisconnected_Bd_one : TotallyDisconnectedSpace ↥(Bd.{u} 1) :=
  totallyDisconnectedSpace_of_homeo SpineTask17.boundaryOneHomeo.{u}

instance isEmpty_Bd_zero : IsEmpty ↥(Bd.{u} 0) := SpineTask17.boundaryZero_isEmpty.{u}

/-- The two points of `|∂Δ[1]|`. -/
def bdOnePt (i : Fin 2) : ↥(Bd.{u} 1) := SpineTask17.boundaryOneHomeo.{u}.symm i

theorem bdOnePt_ne : bdOnePt.{u} 0 ≠ bdOnePt.{u} 1 := by
  intro h
  exact absurd (SpineTask17.boundaryOneHomeo.{u}.symm.injective h) (by decide)

theorem bdOnePt_all (x : ↥(Bd.{u} 1)) : x = bdOnePt.{u} 0 ∨ x = bdOnePt.{u} 1 := by
  have hx : x = bdOnePt.{u} (SpineTask17.boundaryOneHomeo.{u} x) :=
    (SpineTask17.boundaryOneHomeo.{u}.symm_apply_apply x).symm
  have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  rcases h2 (SpineTask17.boundaryOneHomeo.{u} x) with h | h
  · left; rw [hx, h]
  · right; rw [hx, h]

/-- `H̃₀(S⁰) ≅ ℤ₂`. -/
theorem isLine_Hred0_Bd_one : IsLine (Hred0 (Bd.{u} 1)) :=
  ⟨hred0TwoEquiv (bdOnePt.{u} 0) (bdOnePt.{u} 1) bdOnePt_ne bdOnePt_all⟩

/-- `|∂Δ[r]|` is path connected for `r ≥ 2`. -/
instance pathConnected_Bd (n : ℕ) : PathConnectedSpace ↥(Bd.{u} (n + 2)) := by
  have h : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 2))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < n + 2)
  haveI : PathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
    isPathConnected_iff_pathConnectedSpace.1
      (isPathConnected_sphere h 0 (by norm_num : (0 : ℝ) ≤ 1))
  exact pathConnectedSpace_of_homeo (bdSphere.{u} (n + 2))

theorem Hred0_Bd_eq_bot (n : ℕ) : Hred0 (Bd.{u} (n + 2)) = ⊥ := by
  obtain ⟨x₀⟩ : Nonempty ↥(Bd.{u} (n + 2)) := inferInstance
  exact Hred0_eq_bot x₀

/-! ## The Mayer–Vietoris steps for the realized boundaries -/

/-- The Mayer–Vietoris isomorphism `H_{m+2}(|∂Δ[n+2]|) ≅ H_{m+1}(|∂Δ[n+1]|)`. -/
def bdIsoSucc (n m : ℕ) :
    (singCx (Bd.{u} (n + 2))).homology (m + 2) ≅ (singCx (Bd.{u} (n + 1))).homology (m + 1) :=
  mvIsoSucc (bdU.{u} n) (bdV.{u} n) (isOpen_bdU.{u} n) (isOpen_bdV.{u} n) (bdU_union_bdV.{u} n) m
    ≪≫ singHomologyIsoOfHomotopyEquiv (bdInterHomotopyEquiv.{u} n) (m + 1)

/-- The Mayer–Vietoris identification `H₁(|∂Δ[n+2]|) ≃ H̃₀(|∂Δ[n+1]|)`. -/
def bdEquivOne (n : ℕ) :
    (singCx (Bd.{u} (n + 2))).homology 1 ≃ₗ[ZMod 2] Hred0 (Bd.{u} (n + 1)) :=
  (mvOneEquiv (bdU.{u} n) (bdV.{u} n) (isOpen_bdU.{u} n) (isOpen_bdV.{u} n)
    (bdU_union_bdV.{u} n)).trans (hred0Equiv (bdInterHomotopyEquiv.{u} n))

/-! ## The sphere induction -/

/-- **WP5.**  The homology of `S^n = |∂Δ[n+1]|` over `ℤ₂`: zero away from `0` and `n`, and
one-dimensional in degree `n` when `n > 0`. -/
theorem sphere_homology (n : ℕ) :
    (∀ q : ℕ, q ≠ 0 → q ≠ n → IsZero ((singCx (Bd.{u} (n + 1))).homology q)) ∧
      (n ≠ 0 → IsLine ((singCx (Bd.{u} (n + 1))).homology n)) := by
  induction n with
  | zero =>
    haveI : TotallyDisconnectedSpace ↥(Bd.{u} (0 + 1)) := totallyDisconnected_Bd_one.{u}
    refine ⟨fun q hq _ => ?_, fun h => absurd rfl h⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    exact isZero_homology_td m
  | succ n ih =>
    obtain ⟨ihz, iht⟩ := ih
    have hone : ∀ (h : n ≠ 0), IsZero ((singCx (Bd.{u} (n + 2))).homology 1) := by
      intro h
      refine ModuleCat.isZero_iff_subsingleton.2 ?_
      have hbot : Hred0 (Bd.{u} (n + 1)) = ⊥ := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
        exact Hred0_Bd_eq_bot m
      have : Subsingleton (Hred0 (Bd.{u} (n + 1))) := by
        rw [hbot]; infer_instance
      exact (bdEquivOne.{u} n).toEquiv.subsingleton
    refine ⟨fun q hq0 hqn => ?_, fun _ => ?_⟩
    · rcases q with _ | _ | m
      · exact absurd rfl hq0
      · exact hone (by omega)
      · refine IsZero.of_iso ?_ (bdIsoSucc.{u} n m)
        exact ihz (m + 1) (by omega) (by omega)
    · rcases n with _ | k
      · exact isLine_Hred0_Bd_one.congr (bdEquivOne.{u} 0).symm
      · exact (iht (by omega)).of_iso (bdIsoSucc.{u} (k + 1) k).symm

/-! ## WP7 : the statements for `|∂Δ[r]|` -/

/-- **WP7.**  `H_q(|∂Δ[r]|;ℤ₂) = 0` for `q ≠ 0` and `q ≠ r - 1`, when `r ≥ 1`. -/
theorem bd_isZero (r q : ℕ) (hr : r ≠ 0) (hq0 : q ≠ 0) (hqr : q ≠ r - 1) :
    IsZero ((singCx (Bd.{u} r)).homology q) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  exact (sphere_homology.{u} n).1 q hq0 (by simpa using hqr)

/-- **WP7.**  `H_{r-1}(|∂Δ[r]|;ℤ₂) ≅ ℤ₂` for `r ≥ 2`. -/
theorem bd_isLine_top (r : ℕ) (hr : 2 ≤ r) :
    IsLine ((singCx (Bd.{u} r)).homology (r - 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  simpa using (sphere_homology.{u} n).2 (by omega)

/-- **WP7.**  `H₀(|∂Δ[r]|;ℤ₂) ≅ ℤ₂` for `r ≥ 2`. -/
theorem bd_isLine_zero (r : ℕ) (hr : 2 ≤ r) : IsLine ((singCx (Bd.{u} r)).homology 0) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  obtain ⟨x₀⟩ : Nonempty ↥(Bd.{u} (n + 2)) := inferInstance
  exact ⟨h0Equiv x₀⟩

end SpineTask19
