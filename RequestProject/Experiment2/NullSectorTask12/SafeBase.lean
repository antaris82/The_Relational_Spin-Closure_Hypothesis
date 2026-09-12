import RequestProject.Experiment2.NullSectorTask10.AlgebraExtension

/-!
# Task 12, Layer 0: the inherited (safe) base

## Import ledger (INHERITED)

The single import of this module is `RequestProject.Experiment2.NullSectorTask10.AlgebraExtension`,
hence the uncontaminated chain

`Task01 → Task04 → Task06 → Task07 → Task08.FullVec4Embedding →
 Task09.SafeBase → Task09.RealScalarNoGo → Task09.CentralPlane →
 Task09.UnknownQuadraticMap → Task09.Rigidity → Task09.Existence →
 Task10.SafeBase → Task10.AxisDecomposition → Task10.OldAxialRotation →
 Task10.AlgebraExtension`.

In particular **no identification / late-comparison module** of any earlier task is
reachable from any Task-12 reconstruction module, the Task-10 half-angle sectors
(`Task10.HalfAngleSectors`) are *not* imported here — they first enter in
`RequestProject.Experiment2.NullSectorTask12.HalfAngleRelation`, strictly after the intrinsic
classification, as demanded by the source-order firewall of §39 — and the
Task-10/Task-11 internal lifts first enter in
`RequestProject.Experiment2.NullSectorTask12.LiftStability`.

Inherited data actually used in Task 12:

* the associative carrier `W` with the bilinear product `⋆`, the two-sided unit `w1`,
  associativity, and the complete derived multiplication table of the eight derived
  basis elements `w1, wA, wB, wC, wP, wQ, wR, wS` (INHERITED, Task 08);
* the central two-plane `Z = spanℝ{w1, wS}` with `wS ⋆ wS = -w1` and its centrality
  (INHERITED, Task 09);
* the two central quadratic branches `Ncand 1 = N₊`, `Ncand (-1) = N₋` with their
  coefficient functions `nRe, nSc` (INHERITED, Task 09), always used symmetrically;
* the axial algebra-automorphism family `Phi : ℝ → (W →ₗ[ℝ] W)` (INHERITED, Task 10),
  used only from `AxisRelation` on.

## Firewalls

*Experiment-1 firewall*: no construction, theorem, name or file of Experiment 1 is used
anywhere in Task 12.

*Representation-target firewall*: no spinor, Weyl/Dirac/Pauli module, complex scalar
field, complex plane, column vector, matrix type, matrix rank, primitive-idempotent
terminology, `SU(2)` or `Spin(3)` occurs in the reconstruction core.  The condition
`e ⋆ e = e` is *derived* where it is used, never assumed in advance (§10).

*Physical-target firewall*: none of the forbidden words of §3 occurs as a construction,
an import or a target anywhere in Task 12.

## Content of this module

Purely instrumental bookkeeping, all of it derived from the inherited multiplication:

* the two multiplication operators `Lmul`, `Rmul` and the trace identity
  `trace (Lmul a ∘ Rmul b) = 8 * a 0 * b 0`;
* the rank of an idempotent operator;
* the derived conjugation `wconj` with `x ⋆ wconj x = Ncand 1 x`;
* the branch-symmetric vanishing predicate `IsNullElt` and the exact invertibility
  criterion.
-/

namespace NullSectorTask12

open NullSectorTask08 NullSectorTask09 NullSectorTask10

/-! ## Finite-dimensionality of the inherited carrier -/

theorem finrank_W : Module.finrank ℝ W = 8 := by
  simp

/-! ## The two multiplication operators -/

/-- Left multiplication by `a`, as a real-linear operator on the inherited carrier. -/
noncomputable def Lmul (a : W) : W →ₗ[ℝ] W := wit8Mul a

/-- Right multiplication by `b`, as a real-linear operator on the inherited carrier. -/
noncomputable def Rmul (b : W) : W →ₗ[ℝ] W := wit8Mul.flip b

@[simp] theorem Lmul_apply (a x : W) : Lmul a x = a ⋆ x := rfl

@[simp] theorem Rmul_apply (b x : W) : Rmul b x = x ⋆ b := rfl

/-! ## The trace identity -/

/-- The trace of a real-linear operator on the inherited carrier, in the derived
coordinates. -/
theorem trace_eq_coord_sum (f : W →ₗ[ℝ] W) :
    LinearMap.trace ℝ W f = ∑ i : Fin 8, f (Pi.single i (1 : ℝ)) i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 8))]
  simp [Matrix.trace]

theorem single_zero_eq : (Pi.single (0 : Fin 8) (1 : ℝ)) = w1 := by
  funext j; fin_cases j <;> simp [w1]
theorem single_one_eq : (Pi.single (1 : Fin 8) (1 : ℝ)) = wA := by
  funext j; fin_cases j <;> simp [wA]
theorem single_two_eq : (Pi.single (2 : Fin 8) (1 : ℝ)) = wB := by
  funext j; fin_cases j <;> simp [wB]
theorem single_three_eq : (Pi.single (3 : Fin 8) (1 : ℝ)) = wC := by
  funext j; fin_cases j <;> simp [wC]
theorem single_four_eq : (Pi.single (4 : Fin 8) (1 : ℝ)) = wP := by
  funext j; fin_cases j <;> simp [wP]
theorem single_five_eq : (Pi.single (5 : Fin 8) (1 : ℝ)) = wQ := by
  funext j; fin_cases j <;> simp [wQ]
theorem single_six_eq : (Pi.single (6 : Fin 8) (1 : ℝ)) = wR := by
  funext j; fin_cases j <;> simp [wR]
theorem single_seven_eq : (Pi.single (7 : Fin 8) (1 : ℝ)) = wS := by
  funext j; fin_cases j <;> simp [wS]

set_option maxHeartbeats 2000000 in
/-- **DERIVED.**  The trace of the composite "multiply by `a` on the left and by `b` on
the right" depends only on the unit coordinates of `a` and `b`. -/
theorem trace_Lmul_comp_Rmul (a b : W) :
    LinearMap.trace ℝ W ((Lmul a).comp (Rmul b)) = 8 * (a 0 * b 0) - 8 * (a 7 * b 7) := by
  rw [trace_eq_coord_sum, Fin.sum_univ_eight, single_zero_eq, single_one_eq,
    single_two_eq, single_three_eq, single_four_eq, single_five_eq, single_six_eq,
    single_seven_eq]
  simp only [LinearMap.comp_apply, Lmul_apply, Rmul_apply]
  simp [w1, wA, wB, wC, wP, wQ, wR, wS, wit8MulFun]
  ring

/-- **DERIVED.**  The trace of right multiplication. -/
theorem trace_Rmul (b : W) : LinearMap.trace ℝ W (Rmul b) = 8 * b 0 := by
  have h : (Lmul w1).comp (Rmul b) = Rmul b := by
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, Lmul_apply, Rmul_apply, one_mul_W]
  rw [← h, trace_Lmul_comp_Rmul]
  simp [w1]

/-! ## The rank of an idempotent operator -/

/-- **DERIVED.**  An idempotent real-linear operator has rank equal to its trace. -/
theorem finrank_range_of_idem {f : W →ₗ[ℝ] W} (hf : ∀ x, f (f x) = f x) :
    (Module.finrank ℝ (LinearMap.range f) : ℝ) = LinearMap.trace ℝ W f := by
  have hproj : LinearMap.IsProj (LinearMap.range f) f :=
    { map_mem := fun x => ⟨x, rfl⟩
      map_id := by rintro x ⟨y, rfl⟩; exact hf y }
  exact (hproj.trace).symm

/-! ## The derived conjugation -/

/-- The coordinate description of the derived conjugation. -/
def wconjFun (x : W) : W := ![x 0, -x 1, -x 2, -x 3, -x 4, -x 5, -x 6, x 7]

/-- **DERIVED.**  The conjugation of the inherited carrier, as a real-linear map.  It is
introduced only as an instrument; its defining property is the identity
`x ⋆ wconj x = Ncand 1 x` proved below. -/
def wconj : W →ₗ[ℝ] W where
  toFun := wconjFun
  map_add' := by intro x y; funext i; fin_cases i <;> simp [wconjFun] <;> ring
  map_smul' := by intro c x; funext i; fin_cases i <;> simp [wconjFun]

@[simp] theorem wconj_coord_0 (x : W) : wconj x 0 = x 0 := rfl
@[simp] theorem wconj_coord_1 (x : W) : wconj x 1 = -x 1 := rfl
@[simp] theorem wconj_coord_2 (x : W) : wconj x 2 = -x 2 := rfl
@[simp] theorem wconj_coord_3 (x : W) : wconj x 3 = -x 3 := rfl
@[simp] theorem wconj_coord_4 (x : W) : wconj x 4 = -x 4 := rfl
@[simp] theorem wconj_coord_5 (x : W) : wconj x 5 = -x 5 := rfl
@[simp] theorem wconj_coord_6 (x : W) : wconj x 6 = -x 6 := rfl
@[simp] theorem wconj_coord_7 (x : W) : wconj x 7 = x 7 := rfl

theorem wconj_injective : Function.Injective wconj := by
  intro x y h
  have h0 := congrArg (fun z : W => z 0) h
  have h1 := congrArg (fun z : W => z 1) h
  have h2 := congrArg (fun z : W => z 2) h
  have h3 := congrArg (fun z : W => z 3) h
  have h4 := congrArg (fun z : W => z 4) h
  have h5 := congrArg (fun z : W => z 5) h
  have h6 := congrArg (fun z : W => z 6) h
  have h7 := congrArg (fun z : W => z 7) h
  simp only [wconj_coord_0, wconj_coord_1, wconj_coord_2, wconj_coord_3, wconj_coord_4,
    wconj_coord_5, wconj_coord_6, wconj_coord_7, neg_inj] at h0 h1 h2 h3 h4 h5 h6 h7
  funext i
  fin_cases i <;> assumption

theorem wconj_eq_zero_iff (x : W) : wconj x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hh : wconj x = wconj 0 := by rw [h, map_zero]
    exact wconj_injective hh
  · intro h; rw [h, map_zero]

/-- **DERIVED.**  The product of an element with its conjugate is the inherited central
quadratic value. -/
theorem mul_wconj (x : W) : x ⋆ wconj x = Ncand 1 x := by
  funext i
  fin_cases i <;> simp [Ncand, nRe, nSc, w1, wS] <;> ring

/-- **DERIVED.**  The conjugate multiplies on either side with the same central value. -/
theorem wconj_mul (x : W) : wconj x ⋆ x = Ncand 1 x := by
  funext i
  fin_cases i <;> simp [Ncand, nRe, nSc, w1, wS] <;> ring

/-! ## The branch-symmetric vanishing predicate -/

/-- **DERIVED, BRANCH-SYMMETRIC.**  The vanishing of the inherited central quadratic
datum of `x`.  Both Task-09 branches are treated symmetrically: the predicate is stated
through the two coefficient functions, and the next theorem shows that it is exactly the
vanishing of `Ncand z x` for either sign `z = ±1`. -/
def IsNullElt (x : W) : Prop := nRe x = 0 ∧ nSc x = 0

theorem Ncand_eq_zero_iff {z : ℝ} (hz : z ≠ 0) (x : W) :
    Ncand z x = 0 ↔ IsNullElt x := by
  constructor
  · intro h
    have h0 := congrArg (fun y : W => y 0) h
    have h7 := congrArg (fun y : W => y 7) h
    simp [Ncand, w1, wS] at h0 h7
    refine ⟨h0, ?_⟩
    rcases h7 with h | h
    · exact absurd h hz
    · exact h
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i <;> simp [Ncand, h1, h2, w1, wS]

/-- **BRANCH SYMMETRY (§15).**  The two Task-09 branches vanish on exactly the same
elements; no branch is preferred anywhere in Task 12. -/
theorem null_branch_symmetric (x : W) : Ncand 1 x = 0 ↔ Ncand (-1) x = 0 := by
  rw [Ncand_eq_zero_iff one_ne_zero, Ncand_eq_zero_iff (z := (-1 : ℝ)) (by norm_num)]

theorem isNullElt_iff_Ncand (x : W) : IsNullElt x ↔ Ncand 1 x = 0 :=
  (Ncand_eq_zero_iff one_ne_zero x).symm

/-! ## The exact invertibility criterion -/

/-- **NEUTRAL.**  `x` has a two-sided multiplicative partner. -/
def HasInverse (x : W) : Prop := ∃ y : W, x ⋆ y = w1 ∧ y ⋆ x = w1

theorem hasInverse_w1 : HasInverse w1 := ⟨w1, one_mul_W _, one_mul_W _⟩

/-- The central partner of a nonzero central element. -/
noncomputable def zinv (a b : ℝ) : W :=
  (a / (a ^ 2 + b ^ 2)) • w1 + (-(b / (a ^ 2 + b ^ 2))) • wS

theorem zinv_spec {a b : ℝ} (h : ¬ (a = 0 ∧ b = 0)) :
    (a • w1 + b • wS) ⋆ zinv a b = w1 := by
  have hpos : a ^ 2 + b ^ 2 ≠ 0 := by
    intro hz
    exact h ⟨by nlinarith [sq_nonneg a, sq_nonneg b], by nlinarith [sq_nonneg a, sq_nonneg b]⟩
  rw [zinv, central_mul_rule]
  have e1 : a * (a / (a ^ 2 + b ^ 2)) - b * (-(b / (a ^ 2 + b ^ 2))) = 1 := by
    field_simp; ring
  have e2 : a * (-(b / (a ^ 2 + b ^ 2))) + b * (a / (a ^ 2 + b ^ 2)) = 0 := by
    field_simp; ring
  rw [e1, e2]
  simp

theorem zinv_spec' {a b : ℝ} (h : ¬ (a = 0 ∧ b = 0)) :
    zinv a b ⋆ (a • w1 + b • wS) = w1 := by
  rw [← Z_central (smul_add_smul_mem_Z a b) (zinv a b)]
  exact zinv_spec h

theorem Ncand_one_w1 : Ncand 1 w1 = w1 := by
  funext i; fin_cases i <;> simp [Ncand, nRe, nSc, w1, wS]

/-- **DERIVED.**  An element is invertible exactly when its inherited central quadratic
datum is nonzero. -/
theorem hasInverse_iff (x : W) : HasInverse x ↔ ¬ IsNullElt x := by
  constructor
  · rintro ⟨y, hxy, -⟩ hnull
    have hmul : Ncand 1 (x ⋆ y) = Ncand 1 x ⋆ Ncand 1 y :=
      Ncand_mul 1 (by norm_num) x y
    have hx0 : Ncand 1 x = 0 := (isNullElt_iff_Ncand x).1 hnull
    rw [hxy, hx0, zero_mul_W, Ncand_one_w1] at hmul
    have h0 : (w1 : W) 0 = (0 : W) 0 := by rw [hmul]
    simp [w1] at h0
  · intro h
    have hne : ¬ (nRe x = 0 ∧ nSc x = 0) := h
    have hNc : Ncand 1 x = nRe x • w1 + nSc x • wS := by
      simp [Ncand]
    refine ⟨wconj x ⋆ zinv (nRe x) (nSc x), ?_, ?_⟩
    · rw [← mul_assoc_W, mul_wconj, hNc]
      exact zinv_spec hne
    · have hcentral : wconj x ⋆ zinv (nRe x) (nSc x)
          = zinv (nRe x) (nSc x) ⋆ wconj x :=
        (Z_central (smul_add_smul_mem_Z _ _) (wconj x)).symm
      rw [hcentral, mul_assoc_W, wconj_mul, hNc]
      exact zinv_spec' hne

end NullSectorTask12
