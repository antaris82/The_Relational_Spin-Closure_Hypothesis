import RequestProject.Experiment2.NullSectorTask23.GlobalSection

/-!
# Task 23, Package H: comparison with the earlier direction domains

**RECONSTRUCTION LAYER.**

The earlier domains `Dom v` are subsets of **direction space**; the domains `Vset i` of this
task are subsets of the **visible carrier**.  They are therefore not comparable as they
stand (item 63): the comparison needs the axis/parameter presentation of a visible element,
i.e. one extra parameter coordinate, and it needs the direction-reversal ambiguity.

What is proved here:

* the exact axis/parameter membership criteria for the new domains;
* the exact map (item 65): membership of a visible element in `Vset 1` is equivalent to the
  conjunction of an *old* domain condition **up to reversal** and a parameter condition;
* item 66: where the sign condition holds, the old reference representative *is* the new
  local representative — the old data do induce the new local section there;
* item 67, negative: the domain `Vset 0` is induced by **no** old domain `Dom v`, so only a
  subclass of the new domains comes from the old ones (item 64 is thereby respected: no
  identification is made merely because both support local representatives).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask23

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21

open Quaternion Topology

/-! ## The visible element of an axis/parameter pair -/

/-- **NEUTRAL DEFINITION.**  The visible element attached to an axis and a parameter. -/
noncomputable def visOf {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) : GvisT :=
  ⟨⇑(visMap (⟨n, hn⟩, θ)), ⟨(⟨n, hn⟩, θ), rfl⟩⟩

theorem pr_Un {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    pr ⟨Un n θ, Un_mem_Lift hn θ⟩ = visOf hn θ := by
  refine Subtype.ext ?_
  show ⇑(proj (Un n θ)) = ⇑(visMap (⟨n, hn⟩, θ))
  rw [proj_Un hn]
  rfl

theorem mem_Vset_iff_rep {i : Fin 4} {u : LiftT} : pr u ∈ Vset i ↔ qco i (u : W) ≠ 0 :=
  ⟨fun h => mem_Vset_iff.1 h u rfl, fun h => mem_Vset_of h⟩

/-! ## The four coordinates of a reference implementer -/

theorem Un_eq_fromQuat {n : Vec3} (θ : ℝ) :
    Un n θ = fromQuat ⟨Real.cos (θ / 2), Real.sin (θ / 2) * n.1, Real.sin (θ / 2) * n.2.1,
      Real.sin (θ / 2) * n.2.2⟩ := by
  have hv : ((Real.sin (θ / 2) * n.1, Real.sin (θ / 2) * n.2.1, Real.sin (θ / 2) * n.2.2) :
      Vec3) = Real.sin (θ / 2) • n := by
    refine Prod.ext rfl (Prod.ext rfl rfl)
  rw [fromQuat]
  simp only []
  rw [hv, Jmap_linear.2, Un]

@[simp] theorem qco_two_fromQuat (q : ℍ) : qco 2 (fromQuat q) = q.imJ := by
  have h := (fromQuat_coord q).2.2.1
  simp only [qco_two, h]

@[simp] theorem qco_three_fromQuat (q : ℍ) : qco 3 (fromQuat q) = q.imK := by
  have h := (fromQuat_coord q).2.1
  simp only [qco_three, h, neg_neg]

theorem qco_Un_zero {n : Vec3} (θ : ℝ) : qco 0 (Un n θ) = Real.cos (θ / 2) := by
  rw [Un_eq_fromQuat, qco_zero_fromQuat]

theorem qco_Un_one {n : Vec3} (θ : ℝ) : qco 1 (Un n θ) = Real.sin (θ / 2) * n.1 := by
  rw [Un_eq_fromQuat, qco_one_fromQuat]

theorem qco_Un_two {n : Vec3} (θ : ℝ) : qco 2 (Un n θ) = Real.sin (θ / 2) * n.2.1 := by
  rw [Un_eq_fromQuat, qco_two_fromQuat]

theorem qco_Un_three {n : Vec3} (θ : ℝ) : qco 3 (Un n θ) = Real.sin (θ / 2) * n.2.2 := by
  rw [Un_eq_fromQuat, qco_three_fromQuat]

/-! ## Axis/parameter membership criteria -/

theorem visOf_mem_Vset_zero {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    visOf hn θ ∈ Vset 0 ↔ Real.cos (θ / 2) ≠ 0 := by
  rw [← pr_Un hn θ, mem_Vset_iff_rep]
  show qco 0 (Un n θ) ≠ 0 ↔ _
  rw [qco_Un_zero]

theorem visOf_mem_Vset_one {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    visOf hn θ ∈ Vset 1 ↔ Real.sin (θ / 2) * n.1 ≠ 0 := by
  rw [← pr_Un hn θ, mem_Vset_iff_rep]
  show qco 1 (Un n θ) ≠ 0 ↔ _
  rw [qco_Un_one]

/-! ## The exact comparison with the old domains -/

theorem mem_Dom_e1 {n : Vec3} : n ∈ Dom ((1, 0, 0) : Vec3) ↔ IsUnitAxis n ∧ 0 < n.1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    simpa [h3, dot3] using h2
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by simpa [h3, dot3] using h2⟩

/-- **PACKAGE H (item 65), principal.**  The exact map from the old direction-domain data to
the new visible-domain data: a visible element presented by an axis and a parameter lies in
`Vset 1` exactly when its axis lies in the old domain `Dom (1,0,0)` **up to reversal** and
the parameter is nondegenerate.  Both an extra parameter coordinate and the reversal
ambiguity are needed; neither is present in the old data alone. -/
theorem visOf_mem_Vset_one_iff_Dom {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ) :
    visOf hn θ ∈ Vset 1 ↔
      ((n ∈ Dom ((1, 0, 0) : Vec3) ∨ -n ∈ Dom ((1, 0, 0) : Vec3)) ∧ Real.sin (θ / 2) ≠ 0) := by
  rw [visOf_mem_Vset_one hn θ]
  constructor
  · intro h
    have hs : Real.sin (θ / 2) ≠ 0 := fun h0 => h (by rw [h0, zero_mul])
    have hn1 : n.1 ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
    refine ⟨?_, hs⟩
    rcases lt_or_gt_of_ne hn1 with hlt | hgt
    · right
      refine mem_Dom_e1.2 ⟨isUnitAxis_neg hn, ?_⟩
      show 0 < -n.1
      linarith
    · exact Or.inl (mem_Dom_e1.2 ⟨hn, hgt⟩)
  · rintro ⟨hd, hs⟩
    refine mul_ne_zero hs ?_
    rcases hd with hd | hd
    · exact ne_of_gt (mem_Dom_e1.1 hd).2
    · have h := (mem_Dom_e1.1 hd).2
      have h' : 0 < -n.1 := h
      exact ne_of_lt (by linarith)

/-- **PACKAGE H (item 66).**  Where the old domain condition and the parameter condition both
hold with positive sign, the old reference representative *is* the new local
representative: the old locally exact data do induce this new local section. -/
theorem sec_one_eq_Un {n : Vec3} (hn : IsUnitAxis n) (θ : ℝ)
    (hpos : 0 < Real.sin (θ / 2) * n.1) :
    sec 1 ⟨visOf hn θ, (visOf_mem_Vset_one hn θ).2 (ne_of_gt hpos)⟩
      = ⟨Un n θ, Un_mem_Lift hn θ⟩ := by
  refine (sec_unique (pr_Un hn θ) ?_).symm
  show 0 < qco 1 (Un n θ)
  rw [qco_Un_one]
  exact hpos

/-- **PACKAGE H (items 64, 67), principal negative result.**  No old direction domain induces
the visible domain `Vset 0`: for every `v` the criterion "the axis lies in `Dom v`" fails to
describe membership in `Vset 0`, because the identity element lies in `Vset 0` whatever axis
presents it, while no `Dom v` contains an antipodal pair.  Hence only a subclass of the new
domains comes from the old ones. -/
theorem Vset_zero_not_from_Dom (v : Vec3) :
    ¬ ∀ (n : Vec3) (hn : IsUnitAxis n) (θ : ℝ), (visOf hn θ ∈ Vset 0 ↔ n ∈ Dom v) := by
  intro h
  have he : IsUnitAxis ((1, 0, 0) : Vec3) := by simp [IsUnitAxis, h3, dot3]
  have hne : IsUnitAxis (-(1, 0, 0) : Vec3) := isUnitAxis_neg he
  have hcos : Real.cos ((0 : ℝ) / 2) ≠ 0 := by norm_num
  have h1 : ((1, 0, 0) : Vec3) ∈ Dom v := (h _ he 0).1 ((visOf_mem_Vset_zero he 0).2 hcos)
  have h2 : (-(1, 0, 0) : Vec3) ∈ Dom v := (h _ hne 0).1 ((visOf_mem_Vset_zero hne 0).2 hcos)
  exact Dom_no_antipodal h1 h2

/-- **PACKAGE H.**  Every new local representative is a signed old reference implementer:
the new local data never leave the inherited axis/parameter description. -/
theorem sec_eq_sign_Un (i : Fin 4) (g : ↥(Vset i)) :
    ∃ (n : Vec3) (hn : IsUnitAxis n) (θ : ℝ), sec i g = ⟨Un n θ, Un_mem_Lift hn θ⟩ := by
  obtain ⟨n, θ, hn, hval⟩ := (mem_Lift_iff_exists_Un ((sec i g : LiftT) : W)).1 (sec i g).2
  exact ⟨n, hn, θ, Subtype.ext hval⟩

end NullSectorTask23
