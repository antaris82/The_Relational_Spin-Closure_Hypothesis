import RequestProject.Experiment2.NullSectorTask17.SafeBase

/-!
# Task 17, Package A: intrinsic geometry of the inherited local domains

The inherited Task-16 local domain is

```
Dom v = { n | IsUnitAxis n ∧ 0 < h3 n v } ,
```

defined from the inherited spatial form alone.  This module settles its elementary
intrinsic geometry:

* membership identities and invariance under positive rescaling of `v` (§10);
* `Dom v` is nonempty **exactly** when `v ≠ 0` (§11);
* `Dom v` contains the normalized direction of `v` **exactly** when `v ≠ 0` (§12);
* `Dom v` contains no antipodal pair — reproved intrinsically (§13);
* `Dom v` is open in the inherited subspace of unit directions (§14);
* an **explicit** path inside `Dom v` between arbitrary members: the straight-line
  interpolation renormalized to unit length; it is proved to stay unit-normalized and
  strictly inside `Dom v` for the whole parameter interval (§15, §16);
* hence every nonempty `Dom v` is path-connected (§17) and therefore preconnected and
  connected (§18) — derived from the explicit path, not from any imported hemisphere or
  sphere theorem.
-/

namespace NullSectorTask17

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16

/-! ## The inherited domain, read inside the space of unit directions -/

/-- **NEUTRAL DEFINITION.**  A set of spatial directions, read as a subset of the inherited
space of unit directions. -/
def sphSet (S : Set Vec3) : Set Sph := {s : Sph | (s : Vec3) ∈ S}

@[simp] theorem mem_sphSet {S : Set Vec3} {s : Sph} : s ∈ sphSet S ↔ (s : Vec3) ∈ S :=
  Iff.rfl

/-! ## §10 — elementary membership identities -/

theorem mem_Dom_iff {v n : Vec3} : n ∈ Dom v ↔ IsUnitAxis n ∧ 0 < h3 n v := Iff.rfl

theorem mem_Dom_pos {v n : Vec3} (h : n ∈ Dom v) : 0 < h3 n v := h.2

/-- **DERIVED (§10).**  The domain is invariant under positive rescaling of the defining
direction. -/
theorem Dom_smul_pos {c : ℝ} (hc : 0 < c) (v : Vec3) : Dom (c • v) = Dom v := by
  ext n
  simp only [mem_Dom_iff, h3_comm n (c • v), h3_smul_left, h3_comm v n]
  constructor
  · rintro ⟨hu, hp⟩
    exact ⟨hu, by nlinarith [hp, hc]⟩
  · rintro ⟨hu, hp⟩
    exact ⟨hu, by positivity⟩

/-- **DERIVED (§10).**  The domain of the zero direction is empty. -/
theorem Dom_zero : Dom (0 : Vec3) = ∅ := by
  ext n
  simp only [mem_Dom_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro _
  simp [h3, dot3]

/-! ## §11, §12 — nonemptiness and the normalized direction -/

/-- **PRINCIPAL THEOREM (§12).**  The normalized direction attached to `v` lies in `Dom v`
exactly when `v` is nonzero. -/
theorem nrmz_mem_Dom_iff (v : Vec3) : nrmz v ∈ Dom v ↔ v ≠ 0 := by
  constructor
  · rintro ⟨hu, hp⟩ rfl
    simp [h3, dot3] at hp
  · intro hv
    exact ⟨nrmz_isUnitAxis hv, (nrmz_pos_iff hv v).2 (h3_self_pos hv)⟩

/-- **PRINCIPAL THEOREM (§11).**  `Dom v` is nonempty exactly when `v` is nonzero. -/
theorem Dom_nonempty_iff (v : Vec3) : (Dom v).Nonempty ↔ v ≠ 0 := by
  constructor
  · rintro ⟨n, hn⟩ rfl
    exact absurd hn.2 (by simp [h3, dot3])
  · intro hv
    exact ⟨nrmz v, (nrmz_mem_Dom_iff v).2 hv⟩

/-! ## §13 — no antipodal pair, reproved intrinsically -/

theorem h3_neg_left (n v : Vec3) : h3 (-n) v = -h3 n v := by
  simp only [h3, dot3, Prod.fst_neg, Prod.snd_neg]; ring

/-- **PRINCIPAL THEOREM (§13).**  `Dom v` contains no pair of opposite directions.  The
proof uses only the inherited form. -/
theorem Dom_antipodal_free {v n : Vec3} (h : n ∈ Dom v) : -n ∉ Dom v := by
  intro hneg
  have h1 := mem_Dom_pos h
  have h2 := mem_Dom_pos hneg
  rw [h3_neg_left] at h2
  linarith

/-! ## §14 — openness -/

theorem continuous_h3_sph (v : Vec3) : Continuous fun s : Sph => h3 (s : Vec3) v :=
  (continuous_h3_left v).comp continuous_subtype_val

/-- **PRINCIPAL THEOREM (§14).**  `Dom v` is open in the inherited subspace of unit
directions. -/
theorem isOpen_sphSet_Dom (v : Vec3) : IsOpen (sphSet (Dom v)) := by
  have he : sphSet (Dom v) = (fun s : Sph => h3 (s : Vec3) v) ⁻¹' Set.Ioi 0 := by
    ext s
    simp only [mem_sphSet, mem_Dom_iff, Set.mem_preimage, Set.mem_Ioi]
    exact ⟨fun h => h.2, fun h => ⟨s.2, h⟩⟩
  rw [he]
  exact (continuous_h3_sph v).isOpen_preimage _ isOpen_Ioi

/-! ## §15, §16 — the explicit path inside the domain -/

/-- **DERIVED (§16).**  For two members of a domain the straight-line interpolation is
never zero on the parameter interval: it has strictly positive inherited form against the
defining direction. -/
theorem segLin_h3_pos {v n₀ n₁ : Vec3} (h₀ : n₀ ∈ Dom v) (h₁ : n₁ ∈ Dom v) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < h3 (segLin n₀ n₁ t) v := by
  rw [h3_segLin_left]
  rcases ht with ⟨ht0, ht1⟩
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h]; simpa using h₀.2
  · rcases eq_or_lt_of_le ht1 with h' | h'
    · rw [h']; simpa using h₁.2
    · have := h₀.2
      have := h₁.2
      nlinarith [h₀.2, h₁.2]

theorem segLin_ne_zero {v n₀ n₁ : Vec3} (h₀ : n₀ ∈ Dom v) (h₁ : n₁ ∈ Dom v) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : segLin n₀ n₁ t ≠ 0 := by
  intro hz
  have := segLin_h3_pos h₀ h₁ ht
  rw [hz] at this
  simp [h3, dot3] at this

/-- **PRINCIPAL THEOREM (§15, §16).**  The renormalized straight-line interpolation between
two members of a domain is unit-normalized and lies strictly inside the domain for every
parameter of the interval. -/
theorem segPath_mem_Dom {v n₀ n₁ : Vec3} (h₀ : n₀ ∈ Dom v) (h₁ : n₁ ∈ Dom v) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : segPath n₀ n₁ t ∈ Dom v := by
  have hne := segLin_ne_zero h₀ h₁ ht
  exact ⟨nrmz_isUnitAxis hne, (nrmz_pos_iff hne v).2 (segLin_h3_pos h₀ h₁ ht)⟩

/-- **DERIVED.**  The explicit path joining two directions inside a set of unit
directions. -/
theorem joinedIn_segPath {S : Set Vec3} {n₀ n₁ : Vec3} (h₀ : IsUnitAxis n₀)
    (h₁ : IsUnitAxis n₁)
    (hne : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → segLin n₀ n₁ t ≠ 0)
    (hmem : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → segPath n₀ n₁ t ∈ S) :
    JoinedIn (sphSet S) ⟨n₀, h₀⟩ ⟨n₁, h₁⟩ := by
  have hcont : Continuous fun t : unitInterval => segPath n₀ n₁ (t : ℝ) := by
    have : ContinuousOn (fun t : ℝ => segPath n₀ n₁ t) (Set.Icc (0 : ℝ) 1) :=
      continuousOn_nrmz_comp (continuous_segLin n₀ n₁) hne
    exact this.restrict
  refine ⟨⟨⟨fun t : unitInterval => ⟨segPath n₀ n₁ (t : ℝ), segPath_isUnitAxis (hne t t.2)⟩,
      hcont.subtype_mk _⟩, ?_, ?_⟩, ?_⟩
  · exact Subtype.ext (by simpa using segPath_zero h₀)
  · exact Subtype.ext (by simpa using segPath_one h₁)
  · intro t
    exact hmem (t : ℝ) t.2

/-! ## §17, §18 — path-connectedness and connectedness -/

/-- **PRINCIPAL THEOREM (§17).**  Every nonempty inherited domain is path-connected inside
the space of unit directions, via the explicit renormalized straight-line path. -/
theorem isPathConnected_sphSet_Dom {v : Vec3} (hv : v ≠ 0) :
    IsPathConnected (sphSet (Dom v)) := by
  refine ⟨⟨nrmz v, ((nrmz_mem_Dom_iff v).2 hv).1⟩, (nrmz_mem_Dom_iff v).2 hv, ?_⟩
  intro s hs
  exact joinedIn_segPath _ s.2
    (fun t ht => segLin_ne_zero ((nrmz_mem_Dom_iff v).2 hv) hs ht)
    (fun t ht => segPath_mem_Dom ((nrmz_mem_Dom_iff v).2 hv) hs ht)

/-- **PRINCIPAL THEOREM (§18).**  Consequently every nonempty inherited domain is
preconnected, and connected.  This is derived from the explicit path above, not from any
imported theorem about hemispheres or spheres. -/
theorem isConnected_sphSet_Dom {v : Vec3} (hv : v ≠ 0) : IsConnected (sphSet (Dom v)) :=
  (isPathConnected_sphSet_Dom hv).isConnected

theorem isPreconnected_sphSet_Dom {v : Vec3} (hv : v ≠ 0) :
    IsPreconnected (sphSet (Dom v)) := (isConnected_sphSet_Dom hv).2

end NullSectorTask17
