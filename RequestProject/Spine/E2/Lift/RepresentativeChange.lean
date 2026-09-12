import RequestProject.Spine.E2.Lift.TripleOverlapDefect

/-!
# Task 28, Packages J, K and M: change of internal representatives

**HARD TARGET C, second half.**

Changing the internal representatives by continuous kernel-valued functions,

`u'_ij = ε_ij * u_ij`,

changes the triple-overlap defect by the *computed* factor

`δ'_ijk = (ε_jk * ε_ij * ε_ik⁻¹) * δ_ijk`   (item 76, endpoint `triple_defect_change_of_rep`),

the order being derived from the inherited multiplication convention and the already
certified centrality of the kernel (items 77, 78), not guessed.

Package K (items 84–88) records the quadruple-overlap consistency identity

`δ_ijk * δ_ikl = δ_jkl * δ_ijl`,

obtained directly from associativity in the internal group.

Package M (items 96–100) compares two refinements on their common refinement: the two
representative systems differ by continuous kernel-valued functions and their defects are
related by the change-of-representative law.  No direct limit over covers and no sheaf
machinery is used.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask28

universe u v w

namespace InternalProjection

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G]

/-! ## The algebraic rearrangement behind the change-of-representative law -/

omit [TopologicalSpace L] [IsTopologicalGroup L] in
/-- **DERIVED (item 77).**  The exact rearrangement used below, with the multiplication order
of the inherited convention: `b` and `c` are central, `a` is not required to be. -/
theorem central_rearrange {b c : L} (hb : ∀ l : L, Commute b l) (hc : ∀ l : L, Commute c l)
    (a p q r : L) :
    (a * p) * (b * q) * (c * r)⁻¹ = (a * b * c⁻¹) * (p * q * r⁻¹) := by
  have hc' : ∀ l : L, Commute c⁻¹ l := fun l => (hc l).inv_left
  calc (a * p) * (b * q) * (c * r)⁻¹
      = a * (p * b) * q * (r⁻¹ * c⁻¹) := by rw [mul_inv_rev]; group
    _ = a * (b * p) * q * (r⁻¹ * c⁻¹) := by rw [(hb p).eq]
    _ = (a * b) * ((p * q * r⁻¹) * c⁻¹) := by group
    _ = (a * b) * (c⁻¹ * (p * q * r⁻¹)) := by rw [(hc' (p * q * r⁻¹)).eq]
    _ = (a * b * c⁻¹) * (p * q * r⁻¹) := by group

variable {X : Type w} [TopologicalSpace X] (P : InternalProjection L G)

theorem ker_commute {z : L} (hz : z ∈ P.Ker) (l : L) : Commute z l := P.ker_comm hz l

/-! ## Package J — the change-of-representative law (items 76–83) -/

/-- **PACKAGE J (items 76–80), principal endpoint — HARD TARGET C.**
`triple_defect_change_of_rep`: modifying the three internal representatives by continuous
kernel-valued functions multiplies the triple-overlap defect by
`ε_jk * ε_ij * ε_ik⁻¹`, on the left, in exactly this order. -/
theorem triple_defect_change_of_rep {V : Set X} {uij ujk uik eij ejk eik : X → L}
    (heij : P.IsKerFunOn V eij) (heik : P.IsKerFunOn V eik) {x : X} (hx : x ∈ V) :
    tripleDefect (fun y => eij y * uij y) (fun y => ejk y * ujk y) (fun y => eik y * uik y) x
      = (ejk x * eij x * (eik x)⁻¹) * tripleDefect uij ujk uik x := by
  simpa [tripleDefect] using
    central_rearrange (b := eij x) (c := eik x) (P.ker_commute (heij.2 x hx))
      (P.ker_commute (heik.2 x hx)) (ejk x) (ujk x) (uij x) (uik x)

/-- **PACKAGE J (item 79).**  The modified defect is again a continuous kernel-valued
function, and the modifying factor `ε_jk * ε_ij * ε_ik⁻¹` is one too. -/
theorem changeFactor_isKerFunOn {V : Set X} {eij ejk eik : X → L}
    (heij : P.IsKerFunOn V eij) (hejk : P.IsKerFunOn V ejk) (heik : P.IsKerFunOn V eik) :
    P.IsKerFunOn V (fun x => ejk x * eij x * (eik x)⁻¹) :=
  (hejk.mul P heij).mul P heik.inv

/-- **PACKAGE J (item 81), principal.**  Changing the internal representatives can change the
defect while preserving every ordinary transition map: the modified representatives still
project onto the same ordinary maps. -/
theorem change_of_rep_preserves_ordinary {gij : X → G} {V : Set X} {uij eij : X → L}
    (hij : P.IsInternalRepOn gij V uij) (heij : P.IsKerFunOn V eij) :
    P.IsInternalRepOn gij V (fun x => eij x * uij x) :=
  P.isInternalRepOn_kerFun_mul hij heij

/-- **PACKAGE J (item 81).**  A concrete instance of the previous statement: if the kernel
function on the `ik` overlap is nontrivial at a point while the other two are trivial there,
the defect really changes at that point, although all ordinary transitions are untouched. -/
theorem defect_changes_of_nontrivial_kerFun {V : Set X} {uij ujk uik eij ejk eik : X → L}
    (heij : P.IsKerFunOn V eij) (heik : P.IsKerFunOn V eik) {x : X} (hx : x ∈ V)
    (h1 : eij x = 1) (h2 : ejk x = 1) (h3 : eik x ≠ 1) :
    tripleDefect (fun y => eij y * uij y) (fun y => ejk y * ujk y) (fun y => eik y * uik y) x
      ≠ tripleDefect uij ujk uik x := by
  rw [P.triple_defect_change_of_rep heij heik hx, h1, h2, one_mul, one_mul]
  intro hcon
  have h4 : (eik x)⁻¹ = 1 := by
    have hcan := congrArg (fun y => y * (tripleDefect uij ujk uik x)⁻¹) hcon
    simpa [mul_assoc] using hcan
  exact h3 (inv_eq_one.1 h4)

/-- **PACKAGE J (item 82).**  What is invariant without any quotient machinery: the defect is
unchanged exactly when the modifying factor is trivial, i.e. `ε_jk * ε_ij = ε_ik` pointwise.
No equivalence class is formed (item 83). -/
theorem defect_eq_iff_changeFactor_trivial {V : Set X} {uij ujk uik eij ejk eik : X → L}
    (heij : P.IsKerFunOn V eij) (heik : P.IsKerFunOn V eik) {x : X} (hx : x ∈ V) :
    tripleDefect (fun y => eij y * uij y) (fun y => ejk y * ujk y) (fun y => eik y * uik y) x
        = tripleDefect uij ujk uik x
      ↔ ejk x * eij x = eik x := by
  rw [P.triple_defect_change_of_rep heij heik hx]
  constructor
  · intro h
    have h1 : ejk x * eij x * (eik x)⁻¹ = 1 := by
      have hcan := congrArg (fun y => y * (tripleDefect uij ujk uik x)⁻¹) h
      simpa [mul_assoc] using hcan
    exact mul_inv_eq_one.1 h1
  · intro h
    rw [h, mul_inv_cancel, one_mul]

/-! ## Package K — quadruple-overlap consistency (items 84–88) -/

/-- **PACKAGE K (items 84–87), principal.**  On a common fourfold refined overlap the two
associative ways of multiplying three internal transition representatives give the
consistency identity `δ_ijk * δ_ikl = δ_jkl * δ_ijl`.  The proof is exactly associativity in
the internal group together with centrality of the kernel; no cohomological reading is
introduced (item 87). -/
theorem quadruple_defect_consistency {V : Set X} {uij ujk ukl uik ujl uil : X → L}
    {gij gjk gkl gik gjl : X → G}
    (hij : P.IsInternalRepOn gij V uij) (hjk : P.IsInternalRepOn gjk V ujk)
    (hkl : P.IsInternalRepOn gkl V ukl) (hik : P.IsInternalRepOn gik V uik)
    (hjl : P.IsInternalRepOn gjl V ujl)
    (hijk : ∀ x ∈ V, gik x = gjk x * gij x)
    (hjkl : ∀ x ∈ V, gjl x = gkl x * gjk x)
    {x : X} (hx : x ∈ V) :
    tripleDefect uij ujk uik x * tripleDefect uik ukl uil x
      = tripleDefect ujk ukl ujl x * tripleDefect uij ujl uil x := by
  have hdijk : tripleDefect uij ujk uik x ∈ P.Ker := P.tripleDefect_mem_ker hij hjk hik hijk hx
  have hdjkl : tripleDefect ujk ukl ujl x ∈ P.Ker := P.tripleDefect_mem_ker hjk hkl hjl hjkl hx
  set a := tripleDefect uij ujk uik x
  set b := tripleDefect ujk ukl ujl x
  -- the two bracketings of `u_kl * u_jk * u_ij`
  have hA : ujk x * uij x = a * uik x := tripleDefect_mul uij ujk uik x
  have hB : ukl x * uik x = tripleDefect uik ukl uil x * uil x :=
    tripleDefect_mul uik ukl uil x
  have hC : ukl x * ujk x = b * ujl x := tripleDefect_mul ujk ukl ujl x
  have hD : ujl x * uij x = tripleDefect uij ujl uil x * uil x :=
    tripleDefect_mul uij ujl uil x
  have key : a * (tripleDefect uik ukl uil x * uil x)
      = b * (tripleDefect uij ujl uil x * uil x) := by
    calc a * (tripleDefect uik ukl uil x * uil x)
        = a * (ukl x * uik x) := by rw [hB]
      _ = ukl x * (a * uik x) := by
            rw [← mul_assoc, (P.ker_commute hdijk (ukl x)).eq, mul_assoc]
      _ = ukl x * (ujk x * uij x) := by rw [hA]
      _ = ukl x * ujk x * uij x := (mul_assoc _ _ _).symm
      _ = b * ujl x * uij x := by rw [hC]
      _ = b * (ujl x * uij x) := mul_assoc _ _ _
      _ = b * (tripleDefect uij ujl uil x * uil x) := by rw [hD]
  rw [← mul_assoc, ← mul_assoc] at key
  exact mul_right_cancel key

/-! ## Package M — refinement comparison (items 96–100) -/

/-- **PACKAGE M (items 96, 97), principal.**  Two representative systems available on two
refined domains differ, on the common refinement, by a unique continuous kernel-valued
function. -/
theorem refinement_comparison_kerFun {g : X → G} {V₁ V₂ : Set X} {u₁ u₂ : X → L}
    (h₁ : P.IsInternalRepOn g V₁ u₁) (h₂ : P.IsInternalRepOn g V₂ u₂) :
    P.IsKerFunOn (V₁ ∩ V₂) (relFactor u₁ u₂) ∧
      ∀ x ∈ V₁ ∩ V₂, u₂ x = relFactor u₁ u₂ x * u₁ x :=
  ⟨P.relFactor_isKerFunOn (h₁.mono P Set.inter_subset_left) (h₂.mono P Set.inter_subset_right),
    fun x _ => (relFactor_mul_self u₁ u₂ x).symm⟩

/-- **PACKAGE M (item 98), principal.**  On the common refinement the triple defects of two
representative systems are related by the change-of-representative law of Package J. -/
theorem refinement_comparison_defect {gij gik : X → G} {V₁ V₂ : Set X}
    {uij ujk uik vij vjk vik : X → L}
    (h₁ij : P.IsInternalRepOn gij V₁ uij) (h₂ij : P.IsInternalRepOn gij V₂ vij)
    (h₁ik : P.IsInternalRepOn gik V₁ uik) (h₂ik : P.IsInternalRepOn gik V₂ vik)
    {x : X} (hx : x ∈ V₁ ∩ V₂) :
    tripleDefect vij vjk vik x
      = (relFactor ujk vjk x * relFactor uij vij x * (relFactor uik vik x)⁻¹)
        * tripleDefect uij ujk uik x := by
  have heij : P.IsKerFunOn (V₁ ∩ V₂) (relFactor uij vij) :=
    P.relFactor_isKerFunOn (h₁ij.mono P Set.inter_subset_left)
      (h₂ij.mono P Set.inter_subset_right)
  have heik : P.IsKerFunOn (V₁ ∩ V₂) (relFactor uik vik) :=
    P.relFactor_isKerFunOn (h₁ik.mono P Set.inter_subset_left)
      (h₂ik.mono P Set.inter_subset_right)
  have hchange := P.triple_defect_change_of_rep (uij := uij) (ujk := ujk) (uik := uik)
    (eij := relFactor uij vij) (ejk := relFactor ujk vjk) (eik := relFactor uik vik)
    heij heik hx
  have hv : ∀ (a b : X → L) (y : X), relFactor a b y * a y = b y := fun a b y =>
    relFactor_mul_self a b y
  simpa [hv] using hchange

end InternalProjection

end NullSectorTask28
