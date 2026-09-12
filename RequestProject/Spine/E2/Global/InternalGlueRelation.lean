import RequestProject.Spine.E2.Global.GlobalGlueBase

/-!
# Task 30, Packages B and C: the tagged local carrier and the gluing relation

**Hard target A, first half.**

`InternalPre S L = Σ i, U i × Lift` is the disjoint tagged local carrier (Package B): a
tagged representative is a chart index `i`, a base point `b ∈ U i` and an internal group
coordinate `a`.  No quotient is formed in Package B (item 26).

**Package C — the exact transition convention (items 27–29).**  The convention is *derived*,
not guessed.  The inherited ordinary frame side transforms chart coordinates by

`coord_j = g_ij • coord_i`

(Task XXVII, `frameTrivAt (triv j) = transition i j • frameTrivAt (triv i)`), and the
Task-XXIX multiplication convention for the internal transitions is

`u_jk * u_ij = u_ik`, `proj (u_ij) = g_ij`.

Both force the internal coordinate to transform by **left** multiplication,

`a_j = u_ij(b) * a_i`,

which is the first candidate of item 28.  With this orientation the three relation laws
follow from exactly the three inherited transition laws:

| relation law | inherited law used |
| --- | --- |
| reflexivity | `u_ii = 1` |
| symmetry | `u_ji = u_ij⁻¹` |
| transitivity | `u_jk * u_ij = u_ik` (index orientation `i → j → k`) |

Required endpoint: `internalGlueRel_equivalence` (item 34).

Because transitions act on the **left**, the global internal-group action constructed later
must act on the **right** (item 73); that consequence is drawn in `InternalGroupAction`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask30

open NullSectorTask28 NullSectorTask29

universe u v w t

section Glue

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {P : InternalProjection L G}

/-! ## Package B — the tagged local carrier -/

/-- **PACKAGE B (item 23), principal definition.**  The disjoint tagged local carrier
`Σ i, U i × Lift`.  It carries the ordinary disjoint-union topology of the local products;
no quotient is formed here. -/
abbrev InternalPre (S : TransitionSystem B ι G) (L : Type w) : Type max u w t :=
  Σ i : ι, ↥(S.U i) × L

variable {S : TransitionSystem B ι G}

/-- **PACKAGE B (item 24).**  The chart index of a tagged representative. -/
def preIdx (x : InternalPre S L) : ι := x.1

/-- **PACKAGE B (item 24).**  The base point of a tagged representative. -/
def prePt (x : InternalPre S L) : B := (x.2.1 : B)

/-- **PACKAGE B (item 24).**  The internal group coordinate of a tagged representative. -/
def preElt (x : InternalPre S L) : L := x.2.2

omit [Group L] [TopologicalSpace L] [IsTopologicalGroup L] in
theorem prePt_mem (x : InternalPre S L) : prePt x ∈ S.U (preIdx x) := x.2.1.2

omit [Group L] [TopologicalSpace L] [IsTopologicalGroup L] in
@[simp] theorem preIdx_mk (i : ι) (b : ↥(S.U i)) (a : L) :
    preIdx (⟨i, b, a⟩ : InternalPre S L) = i := rfl

omit [Group L] [TopologicalSpace L] [IsTopologicalGroup L] in
@[simp] theorem prePt_mk (i : ι) (b : ↥(S.U i)) (a : L) :
    prePt (⟨i, b, a⟩ : InternalPre S L) = (b : B) := rfl

omit [Group L] [TopologicalSpace L] [IsTopologicalGroup L] in
@[simp] theorem preElt_mk (i : ι) (b : ↥(S.U i)) (a : L) :
    preElt (⟨i, b, a⟩ : InternalPre S L) = a := rfl

omit [Group L] [TopologicalSpace L] [IsTopologicalGroup L] in
/-- **PACKAGE B (item 25), extensionality.**  A tagged representative is determined by its
chart index, base point and internal coordinate. -/
theorem pre_eta (x : InternalPre S L) :
    x = (⟨preIdx x, ⟨prePt x, prePt_mem x⟩, preElt x⟩ : InternalPre S L) := rfl

omit [Group L] [TopologicalSpace L] [IsTopologicalGroup L] in
/-- **PACKAGE B (item 25), extensionality in one chart.** -/
theorem pre_mk_inj {i : ι} {b b' : B} {hb : b ∈ S.U i} {hb' : b' ∈ S.U i} {a a' : L} :
    (⟨i, ⟨b, hb⟩, a⟩ : InternalPre S L) = ⟨i, ⟨b', hb'⟩, a'⟩ ↔ b = b' ∧ a = a' := by
  constructor
  · intro h
    exact ⟨congrArg prePt h, congrArg preElt h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## Package C — the gluing relation -/

variable (T : CompatibleContinuousInternalTransitions P S)

/-- **PACKAGE C (item 30), principal definition.**  Two tagged representatives are glued when
they lie above the same base point and their internal coordinates are related by the derived
convention `a_j = u_ij(b) * a_i`. -/
def InternalGlueRel (x y : InternalPre S L) : Prop :=
  ∃ hb : prePt y = prePt x,
    preElt y =
      uu T (preIdx x) (preIdx y) (prePt x) (prePt_mem x) (hb ▸ prePt_mem y) * preElt x

/-- **PACKAGE C.**  Glued representatives lie above the same base point. -/
theorem glueRel_pt_eq {x y : InternalPre S L} (h : InternalGlueRel T x y) :
    prePt y = prePt x :=
  h.elim fun hb _ => hb

/-- **PACKAGE C, the workhorse characterization.**  Above one base point the relation is
exactly left multiplication by the inherited internal transition. -/
theorem glueRel_iff_of_pt {i j : ι} {b : B} (hi : b ∈ S.U i) (hj : b ∈ S.U j) (a a' : L) :
    InternalGlueRel T (⟨i, ⟨b, hi⟩, a⟩ : InternalPre S L) ⟨j, ⟨b, hj⟩, a'⟩ ↔
      a' = uu T i j b hi hj * a :=
  ⟨fun h => h.elim fun _ hv => hv, fun h => ⟨rfl, h⟩⟩

/-- **PACKAGE C.**  The canonical glued partner of a tagged representative in another
chart. -/
theorem glueRel_mk {i j : ι} {b : B} (hi : b ∈ S.U i) (hj : b ∈ S.U j) (a : L) :
    InternalGlueRel T (⟨i, ⟨b, hi⟩, a⟩ : InternalPre S L)
      ⟨j, ⟨b, hj⟩, uu T i j b hi hj * a⟩ :=
  (glueRel_iff_of_pt T hi hj a _).2 rfl

/-- **PACKAGE C (item 31), principal.**  Reflexivity — proved from `u_ii = 1`. -/
theorem glueRel_refl (x : InternalPre S L) : InternalGlueRel T x x :=
  ⟨rfl, by
    show preElt x = uu T (preIdx x) (preIdx x) (prePt x) (prePt_mem x) (prePt_mem x) * preElt x
    rw [uu_self, one_mul]⟩

/-- **PACKAGE C (item 32), principal.**  Symmetry — proved from `u_ji = u_ij⁻¹`. -/
theorem glueRel_symm {x y : InternalPre S L} (h : InternalGlueRel T x y) :
    InternalGlueRel T y x := by
  obtain ⟨i, ⟨b, hi⟩, a⟩ := x
  obtain ⟨j, ⟨b', hj⟩, a'⟩ := y
  have hb : b' = b := glueRel_pt_eq T h
  subst hb
  rw [glueRel_iff_of_pt] at h
  rw [glueRel_iff_of_pt, h, uu_symm T i j b' hi hj, inv_mul_cancel_left]

/-- **PACKAGE C (item 33), principal.**  Transitivity — proved from the exact triple law
`u_jk * u_ij = u_ik`, with the inherited orientation of the indices. -/
theorem glueRel_trans {x y z : InternalPre S L} (hxy : InternalGlueRel T x y)
    (hyz : InternalGlueRel T y z) : InternalGlueRel T x z := by
  obtain ⟨i, ⟨b, hi⟩, a⟩ := x
  obtain ⟨j, ⟨b', hj⟩, a'⟩ := y
  obtain ⟨k, ⟨b'', hk⟩, a''⟩ := z
  have hb : b' = b := glueRel_pt_eq T hxy
  subst hb
  have hb' : b'' = b' := glueRel_pt_eq T hyz
  subst hb'
  rw [glueRel_iff_of_pt] at hxy hyz
  rw [glueRel_iff_of_pt, hyz, hxy, ← mul_assoc, uu_trans T i j k b'' hi hj hk]

/-- **PACKAGE C (item 34), REQUIRED ENDPOINT.**  The gluing relation is an equivalence
relation. -/
theorem internalGlueRel_equivalence : Equivalence (InternalGlueRel T) :=
  ⟨glueRel_refl T, glueRel_symm T, glueRel_trans T⟩

/-- **PACKAGE C.**  The associated setoid. -/
def InternalGlueSetoid : Setoid (InternalPre S L) :=
  ⟨InternalGlueRel T, internalGlueRel_equivalence T⟩

/-- **NEGATIVE CONTROL (item 148).**  Two tagged representatives in the *same* chart are
glued only if they are equal: the relation does not collapse a local product. -/
theorem glueRel_same_chart {i : ι} {b b' : B} {hb : b ∈ S.U i} {hb' : b' ∈ S.U i} {a a' : L}
    (h : InternalGlueRel T (⟨i, ⟨b, hb⟩, a⟩ : InternalPre S L) ⟨i, ⟨b', hb'⟩, a'⟩) :
    b = b' ∧ a = a' := by
  have hbb : b' = b := glueRel_pt_eq T h
  subst hbb
  rw [glueRel_iff_of_pt] at h
  rw [h, uu_self, one_mul]
  exact ⟨rfl, rfl⟩

end Glue

end NullSectorTask30
