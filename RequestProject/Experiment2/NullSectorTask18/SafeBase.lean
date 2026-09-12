import RequestProject.Experiment2.NullSectorTask17.RegularityAudit

/-!
# Task 18, Layer 0: the inherited (safe) base

## Import ledger (INHERITED)

* `RequestProject.Experiment2.NullSectorTask17.RegularityAudit` — the last *reconstruction* layer of
  Task 17.  Through it, and only through it, Task 18 inherits the whole Task-17
  reconstruction development (Packages A–G) and, transitively, the Task-16 reconstruction
  layer:

  * the associative carrier `W` with product `⋆`, unit `w1`, exact centre `Z`, the spatial
    carrier `Vec3` with the inherited form `h3`, the unit directions `IsUnitAxis`, the
    inherited subspace `Sph` of unit directions, the reference implementations `Un n θ`,
    the visible family `PhiGen n θ`;
  * the exact coincidence classification `coincidence_iff`, `coincidence_iff_coords`;
  * joint regularity `IsJointlyRegularFamily`, the recovered rates `rateAlpha`, `rateBeta`,
    their continuity, and the presentation `famOf`;
  * the local layer `Dom`, `IsTransformationValuedOn`, `locFam`, the global sign-relaxed
    class `IsSignTransformationValued` with its unique member `refFam`;
  * the Task-17 notions `IsAdmissibleDomain`, `AntipodalFree`, `sphSet`, `ovl`,
    `IsC1JointlyRegularFamily` and all their proved properties.

**Reconstruction firewall.**  `RequestProject.Experiment2.NullSectorTask17.Identification` — the only
comparison module of Task 17 — is *not* imported here, nor by any other Task-18
reconstruction module; neither is `RequestProject.Experiment2.NullSectorTask17.Task17` (which imports
it).  The single Task-18 comparison module,
`RequestProject.Experiment2.NullSectorTask18.Identification`, is imported by nothing but
`RequestProject.Experiment2.NullSectorTask18.Task18`.

No conventional geometric or topological target is imported or used anywhere in the
Task-18 reconstruction modules: no rotation or double-cover group, no spinor, no covering
space, no bundle, no Čech datum, no cocycle, no cohomology, no connection, no holonomy, no
fundamental group, no spin-structure theorem.  The words `open`, `connected`, `path`,
`component` are used in their bare point-set sense for the inherited subspace `Sph` of unit
directions.  No physical vocabulary occurs in any reconstruction statement.  No central
factor, sign, or local normalization is ever quotiented out: every such factor is carried
explicitly.

## Content of this module

Bookkeeping only:

* the predicate `IsHalfOdd`;
* elementary coordinate identities for the inherited form and for the normalization;
* the explicit lexicographic half-space `lexSet s` of unit directions (`s = ±1`), which
  will serve in Package B as an explicit inclusion-maximal connected admissible domain;
* the elementary fact that an open set of unit directions containing the initial point of a
  continuous curve of unit directions contains an initial segment of that curve.
-/

namespace NullSectorTask18

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17

/-! ## Half-odd values -/

/-- **NEUTRAL DEFINITION.**  A real number lies in `ℤ + 1/2`. -/
def IsHalfOdd (x : ℝ) : Prop := ∃ k : ℤ, x = (k : ℝ) + 1 / 2

theorem isHalfOdd_ne_int {x : ℝ} (hx : IsHalfOdd x) (k : ℤ) : x ≠ (k : ℝ) := by
  obtain ⟨j, hj⟩ := hx
  intro h
  exact not_int_and_halfodd j k hj h

/-- **DERIVED.**  Two half-odd numbers differing by less than one are equal. -/
theorem halfOdd_eq_of_close {x y : ℝ} (hx : IsHalfOdd x) (hy : IsHalfOdd y)
    (h : |x - y| < 1) : x = y := by
  obtain ⟨j, hj⟩ := hx
  obtain ⟨k, hk⟩ := hy
  have hjk : |((j : ℝ) - (k : ℝ))| < 1 := by
    have : x - y = (j : ℝ) - (k : ℝ) := by rw [hj, hk]; ring
    rwa [this] at h
  have hjk' : j = k := by
    by_contra hne
    have hne' : j - k ≠ 0 := sub_ne_zero.2 hne
    have h1 : (1 : ℤ) ≤ |j - k| := by
      rcases lt_trichotomy (j - k) 0 with h | h | h
      · rw [abs_of_neg h]; omega
      · exact absurd h hne'
      · rw [abs_of_pos h]; omega
    have h2 : (1 : ℝ) ≤ |((j : ℝ) - (k : ℝ))| := by
      have : ((|j - k| : ℤ) : ℝ) = |((j : ℝ) - (k : ℝ))| := by push_cast; rfl
      calc (1 : ℝ) ≤ ((|j - k| : ℤ) : ℝ) := by exact_mod_cast h1
        _ = |((j : ℝ) - (k : ℝ))| := this
    linarith
  rw [hj, hk, hjk']

/-! ## Coordinates -/

/-- **NEUTRAL DEFINITION.**  The first inherited coordinate direction. -/
def e1 : Vec3 := (1, 0, 0)

theorem e1_isUnitAxis : IsUnitAxis e1 := by simp [IsUnitAxis, h3, dot3, e1]

theorem e1_ne_zero : e1 ≠ (0 : Vec3) := by
  intro h
  have := congrArg (fun w : Vec3 => w.1) h
  norm_num [e1] at this

theorem h3_e1 (n : Vec3) : h3 n e1 = n.1 := by simp [h3, dot3, e1]

theorem mem_Dom_e1 {n : Vec3} : n ∈ Dom e1 ↔ IsUnitAxis n ∧ 0 < n.1 := by
  rw [mem_Dom_iff, h3_e1]

theorem nrmz_fst (w : Vec3) : (nrmz w).1 = (nrm w)⁻¹ * w.1 := rfl

theorem vec3_ne_zero_of_coords {w : Vec3} (h : w.1 ≠ 0 ∨ w.2.1 ≠ 0 ∨ w.2.2 ≠ 0) :
    w ≠ 0 := by
  intro hz
  rcases h with h | h | h
  · exact h (by rw [hz]; rfl)
  · exact h (by rw [hz]; rfl)
  · exact h (by rw [hz]; rfl)

theorem coords_ne_zero_of_isUnitAxis {n : Vec3} (hn : IsUnitAxis n) :
    n.1 ≠ 0 ∨ n.2.1 ≠ 0 ∨ n.2.2 ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3'⟩ := hcon
  have hu : h3 n n = 1 := hn
  rw [h3_self_coord, h1, h2, h3'] at hu
  norm_num at hu

/-! ## Explicit lexicographic half-spaces of unit directions

A *lexicographic half-space* is built from three real coordinate functions which are odd
and jointly nonvanishing on unit directions.  Two instances are used below; both contain
the inherited domain `Dom e1`, both contain exactly one member of every antipodal pair, and
they are distinct.
-/

/-- **NEUTRAL DEFINITION.**  Lexicographic positivity with respect to three real coordinate
functions. -/
def LexPosOf (f g k : Vec3 → ℝ) (n : Vec3) : Prop :=
  0 < f n ∨ (f n = 0 ∧ 0 < g n) ∨ (f n = 0 ∧ g n = 0 ∧ 0 < k n)

/-- **NEUTRAL DEFINITION.**  The set of unit directions that are lexicographically positive
for the three given coordinate functions. -/
def lexSetOf (f g k : Vec3 → ℝ) : Set Vec3 := {n : Vec3 | IsUnitAxis n ∧ LexPosOf f g k n}

theorem lexSetOf_unit {f g k : Vec3 → ℝ} : ∀ n ∈ lexSetOf f g k, IsUnitAxis n :=
  fun _ h => h.1

/-- **DERIVED.**  A lexicographic half-space contains no antipodal pair. -/
theorem lexSetOf_antipodalFree {f g k : Vec3 → ℝ} (hf : ∀ n, f (-n) = -f n)
    (hg : ∀ n, g (-n) = -g n) (hk : ∀ n, k (-n) = -k n) : AntipodalFree (lexSetOf f g k) := by
  intro n hn hneg
  have h1 : LexPosOf f g k n := hn.2
  have h2 : LexPosOf f g k (-n) := hneg.2
  rw [LexPosOf, hf n, hg n, hk n] at h2
  rcases h1 with a | ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ <;>
    rcases h2 with b | ⟨b1, b2⟩ | ⟨b1, b2, b3⟩ <;> linarith

/-- **DERIVED.**  A lexicographic half-space contains at least one member of every
antipodal pair of unit directions. -/
theorem lexSetOf_complete {f g k : Vec3 → ℝ} (hf : ∀ n, f (-n) = -f n)
    (hg : ∀ n, g (-n) = -g n) (hk : ∀ n, k (-n) = -k n)
    (hnz : ∀ n, IsUnitAxis n → f n ≠ 0 ∨ g n ≠ 0 ∨ k n ≠ 0) {n : Vec3} (hn : IsUnitAxis n) :
    n ∈ lexSetOf f g k ∨ -n ∈ lexSetOf f g k := by
  have hnn : IsUnitAxis (-n) := isUnitAxis_neg hn
  have hneg : LexPosOf f g k (-n) ↔
      0 < -f n ∨ (-f n = 0 ∧ 0 < -g n) ∨ (-f n = 0 ∧ -g n = 0 ∧ 0 < -k n) := by
    rw [LexPosOf, hf n, hg n, hk n]
  rcases lt_trichotomy (f n) 0 with h | h | h
  · exact Or.inr ⟨hnn, hneg.2 (Or.inl (by linarith))⟩
  · rcases lt_trichotomy (g n) 0 with h' | h' | h'
    · exact Or.inr ⟨hnn, hneg.2 (Or.inr (Or.inl ⟨by linarith, by linarith⟩))⟩
    · rcases lt_trichotomy (k n) 0 with h'' | h'' | h''
      · exact Or.inr ⟨hnn, hneg.2 (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩))⟩
      · rcases hnz n hn with hc | hc | hc
        · exact absurd h hc
        · exact absurd h' hc
        · exact absurd h'' hc
      · exact Or.inl ⟨hn, Or.inr (Or.inr ⟨h, h', h''⟩)⟩
    · exact Or.inl ⟨hn, Or.inr (Or.inl ⟨h, h'⟩)⟩
  · exact Or.inl ⟨hn, Or.inl h⟩

/-- **DERIVED.**  Exactly one member of every antipodal pair of unit directions lies in a
lexicographic half-space. -/
theorem lexSetOf_exactly_one {f g k : Vec3 → ℝ} (hf : ∀ n, f (-n) = -f n)
    (hg : ∀ n, g (-n) = -g n) (hk : ∀ n, k (-n) = -k n)
    (hnz : ∀ n, IsUnitAxis n → f n ≠ 0 ∨ g n ≠ 0 ∨ k n ≠ 0) {n : Vec3} (hn : IsUnitAxis n) :
    (n ∈ lexSetOf f g k ∧ -n ∉ lexSetOf f g k) ∨
      (n ∉ lexSetOf f g k ∧ -n ∈ lexSetOf f g k) := by
  rcases lexSetOf_complete hf hg hk hnz hn with h | h
  · exact Or.inl ⟨h, lexSetOf_antipodalFree hf hg hk n h⟩
  · exact Or.inr ⟨fun hcon => lexSetOf_antipodalFree hf hg hk n hcon h, h⟩

/-! ### The two instances -/

/-- **NEUTRAL DEFINITION.**  The lexicographic half-space of the coordinate order
`(x, y, z)`. -/
def lexA : Set Vec3 := lexSetOf (fun n => n.1) (fun n => n.2.1) (fun n => n.2.2)

/-- **NEUTRAL DEFINITION.**  The lexicographic half-space of the coordinate order
`(x, -y, z)`. -/
def lexB : Set Vec3 := lexSetOf (fun n => n.1) (fun n => -n.2.1) (fun n => n.2.2)

theorem coord_odd_fst : ∀ n : Vec3, (-n).1 = -n.1 := fun _ => rfl
theorem coord_odd_snd_fst : ∀ n : Vec3, (-n).2.1 = -n.2.1 := fun _ => rfl
theorem coord_odd_snd_snd : ∀ n : Vec3, (-n).2.2 = -n.2.2 := fun _ => rfl
theorem coord_odd_neg_snd_fst : ∀ n : Vec3, -(-n).2.1 = -(-n.2.1) := fun _ => rfl

theorem lexA_antipodalFree : AntipodalFree lexA :=
  lexSetOf_antipodalFree coord_odd_fst coord_odd_snd_fst coord_odd_snd_snd

theorem lexB_antipodalFree : AntipodalFree lexB :=
  lexSetOf_antipodalFree coord_odd_fst coord_odd_neg_snd_fst coord_odd_snd_snd

theorem lexA_complete {n : Vec3} (hn : IsUnitAxis n) : n ∈ lexA ∨ -n ∈ lexA :=
  lexSetOf_complete coord_odd_fst coord_odd_snd_fst coord_odd_snd_snd
    (fun _ h => coords_ne_zero_of_isUnitAxis h) hn

theorem lexB_complete {n : Vec3} (hn : IsUnitAxis n) : n ∈ lexB ∨ -n ∈ lexB := by
  refine lexSetOf_complete coord_odd_fst coord_odd_neg_snd_fst coord_odd_snd_snd ?_ hn
  intro m hm
  rcases coords_ne_zero_of_isUnitAxis hm with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by simpa using h))
  · exact Or.inr (Or.inr h)

theorem lexA_exactly_one {n : Vec3} (hn : IsUnitAxis n) :
    (n ∈ lexA ∧ -n ∉ lexA) ∨ (n ∉ lexA ∧ -n ∈ lexA) :=
  lexSetOf_exactly_one coord_odd_fst coord_odd_snd_fst coord_odd_snd_snd
    (fun _ h => coords_ne_zero_of_isUnitAxis h) hn

theorem lexA_unit : ∀ n ∈ lexA, IsUnitAxis n := fun _ h => h.1
theorem lexB_unit : ∀ n ∈ lexB, IsUnitAxis n := fun _ h => h.1

theorem lexA_fst_nonneg {n : Vec3} (h : n ∈ lexA) : 0 ≤ n.1 := by
  rcases h.2 with h' | ⟨h', -⟩ | ⟨h', -, -⟩
  · exact h'.le
  · exact h'.ge
  · exact h'.ge

theorem lexB_fst_nonneg {n : Vec3} (h : n ∈ lexB) : 0 ≤ n.1 := by
  rcases h.2 with h' | ⟨h', -⟩ | ⟨h', -, -⟩
  · exact h'.le
  · exact h'.ge
  · exact h'.ge

theorem Dom_e1_subset_lexA : Dom e1 ⊆ lexA :=
  fun _ hn => ⟨hn.1, Or.inl (mem_Dom_e1.1 hn).2⟩

theorem Dom_e1_subset_lexB : Dom e1 ⊆ lexB :=
  fun _ hn => ⟨hn.1, Or.inl (mem_Dom_e1.1 hn).2⟩

/-- **DERIVED.**  The two lexicographic half-spaces are different sets: they separate the
antipodal pair `±(0, 3/5, -4/5)` in opposite ways. -/
theorem lexA_ne_lexB : lexA ≠ lexB := by
  have hu : IsUnitAxis ((0, 3 / 5, -4 / 5) : Vec3) := by
    simp [IsUnitAxis, h3, dot3]; norm_num
  have hA : ((0, 3 / 5, -4 / 5) : Vec3) ∈ lexA := ⟨hu, Or.inr (Or.inl ⟨rfl, by norm_num⟩)⟩
  have hB : ((0, 3 / 5, -4 / 5) : Vec3) ∉ lexB := by
    rintro ⟨-, h | ⟨-, h⟩ | ⟨-, h, -⟩⟩ <;> norm_num at h
  intro hcon
  rw [hcon] at hA
  exact hB hA

/-! ## The explicit path towards the first coordinate direction -/

/-- **DERIVED.**  For a set of unit directions with nonnegative first coordinate containing
the inherited domain `Dom e1`, the renormalized straight-line path towards `e1` never
degenerates. -/
theorem lexlike_segLin_ne_zero {S : Set Vec3} (hunit : ∀ n ∈ S, IsUnitAxis n)
    (hnn : ∀ n ∈ S, 0 ≤ n.1) {n : Vec3} (hn : n ∈ S) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : segLin n e1 t ≠ 0 := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, segLin_zero]
    exact isUnitAxis_ne_zero (hunit n hn)
  · refine vec3_ne_zero_of_coords (Or.inl ?_)
    have hfst : (segLin n e1 t).1 = (1 - t) * n.1 + t := by simp [segLin, e1]
    have h0 : 0 ≤ n.1 := hnn n hn
    have hpos : 0 < (1 - t) * n.1 + t := by nlinarith [ht.2]
    rw [hfst]; exact ne_of_gt hpos

/-- **DERIVED.**  Such a set is stable under the renormalized straight-line path towards
`e1`: the path stays inside it for the whole parameter interval. -/
theorem lexlike_segPath_mem {S : Set Vec3} (hunit : ∀ n ∈ S, IsUnitAxis n)
    (hnn : ∀ n ∈ S, 0 ≤ n.1) (hDom : Dom e1 ⊆ S) {n : Vec3} (hn : n ∈ S) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : segPath n e1 t ∈ S := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, segPath, segLin_zero, nrmz_of_isUnitAxis (hunit n hn)]
    exact hn
  · have hne : segLin n e1 t ≠ 0 := lexlike_segLin_ne_zero hunit hnn hn ht
    have hfst : (segLin n e1 t).1 = (1 - t) * n.1 + t := by simp [segLin, e1]
    have h0 : 0 ≤ n.1 := hnn n hn
    have hpos : 0 < (1 - t) * n.1 + t := by nlinarith [ht.2]
    have hinv : 0 < (nrm (segLin n e1 t))⁻¹ := inv_pos.2 (nrm_pos hne)
    refine hDom ⟨nrmz_isUnitAxis hne, ?_⟩
    rw [h3_e1, segPath, nrmz_fst, hfst]
    positivity

/-- **DERIVED.**  Consequently such a set is path-connected inside the inherited subspace of
unit directions. -/
theorem lexlike_isPathConnected {S : Set Vec3} (hunit : ∀ n ∈ S, IsUnitAxis n)
    (hnn : ∀ n ∈ S, 0 ≤ n.1) (hDom : Dom e1 ⊆ S) : IsPathConnected (sphSet S) := by
  have he1 : e1 ∈ S := hDom (mem_Dom_e1.2 ⟨e1_isUnitAxis, by norm_num [e1]⟩)
  refine ⟨⟨e1, e1_isUnitAxis⟩, he1, ?_⟩
  intro s hs
  have hjoin : JoinedIn (sphSet S) ⟨(s : Vec3), s.2⟩ ⟨e1, e1_isUnitAxis⟩ :=
    joinedIn_segPath s.2 e1_isUnitAxis
      (fun t ht => lexlike_segLin_ne_zero hunit hnn hs ht)
      (fun t ht => lexlike_segPath_mem hunit hnn hDom hs ht)
  exact hjoin.symm.mono (le_refl _)

/-! ## Openness and curves -/

/-- **DERIVED.**  If a set of unit directions is open in the inherited subspace and
contains the initial point of a continuous curve of unit directions, it contains an initial
segment of that curve. -/
theorem open_curve_nearby {E : Set Vec3} (hE : IsOpen (sphSet E)) {γ : ℝ → Vec3}
    (hcont : Continuous γ) (hunit : ∀ t : ℝ, IsUnitAxis (γ t)) (h0 : γ 0 ∈ E) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ → γ t ∈ E := by
  have hΓ : Continuous fun t : ℝ => (⟨γ t, hunit t⟩ : Sph) := hcont.subtype_mk _
  have hopen : IsOpen ((fun t : ℝ => (⟨γ t, hunit t⟩ : Sph)) ⁻¹' sphSet E) :=
    hE.preimage hΓ
  have hmem : (0 : ℝ) ∈ (fun t : ℝ => (⟨γ t, hunit t⟩ : Sph)) ⁻¹' sphSet E := h0
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen 0 hmem
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hmem' : t ∈ Metric.ball (0 : ℝ) δ := by
    simpa [Real.dist_eq] using ht
  exact hball hmem'

end NullSectorTask18
