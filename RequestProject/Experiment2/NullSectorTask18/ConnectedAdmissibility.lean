import RequestProject.Experiment2.NullSectorTask18.SafeBase

/-!
# Task 18, Package A: formal closure of the connected-domain result

Task 17 proved, separately, that antipodal-freeness is *sufficient* for admissibility of an
arbitrary set of unit directions, that a nonempty inherited domain is path-connected and
antipodal-free, and that an antipodal **pair** is admissible although it is not
preconnected.  This module closes the resulting paper-level statement as one named theorem:

> for a **preconnected** set of unit directions, `Admissible D ↔ AntipodalFree D`.

The two implications are proved independently (§11, §12):

* sufficiency is the Task-17 endpoint `antipodalFree_admissible`, which uses no
  connectedness at all;
* necessity is derived from two *different* Task-17 endpoints — constancy of the recovered
  rate on a preconnected admissible domain, and oddness of the recovered rate on antipodal
  pairs contained in the domain — which are incompatible with half-oddness.

Empty domains are treated explicitly (§13): both sides hold vacuously, so the theorem needs
**no** nonemptiness hypothesis; this is recorded as a separate lemma.  Connected and
path-connected corollaries are derived only afterwards (§14), from the preconnected
theorem.

The five point-set notions are named separately and are *not* treated as interchangeable
(§10); the elementary implications between them, and two explicit separations, are recorded
below.
-/

namespace NullSectorTask18

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17

/-! ## §10 — the five notions, kept apart -/

/-- **NEUTRAL DEFINITION (§10).**  A set of directions consisting of unit directions. -/
def UnitSet (D : Set Vec3) : Prop := ∀ n ∈ D, IsUnitAxis n

/-- **NEUTRAL DEFINITION (§10).**  Preconnectedness of a set of directions, read inside the
inherited subspace of unit directions. -/
def PreconnDomain (D : Set Vec3) : Prop := IsPreconnected (sphSet D)

/-- **NEUTRAL DEFINITION (§10).**  Connectedness (preconnected *and* nonempty). -/
def ConnDomain (D : Set Vec3) : Prop := IsConnected (sphSet D)

/-- **NEUTRAL DEFINITION (§10).**  Path-connectedness. -/
def PathConnDomain (D : Set Vec3) : Prop := IsPathConnected (sphSet D)

/-- **NEUTRAL DEFINITION (§10).**  Openness in the inherited subspace of unit
directions. -/
def OpenDomain (D : Set Vec3) : Prop := IsOpen (sphSet D)

theorem PathConnDomain.conn {D : Set Vec3} (h : PathConnDomain D) : ConnDomain D :=
  h.isConnected

theorem ConnDomain.preconn {D : Set Vec3} (h : ConnDomain D) : PreconnDomain D := h.2

theorem PathConnDomain.preconn {D : Set Vec3} (h : PathConnDomain D) : PreconnDomain D :=
  h.conn.preconn

/-- **DERIVED (§10), first separation.**  The empty domain is preconnected but not
connected: the two notions are different. -/
theorem empty_preconn_not_conn :
    PreconnDomain (∅ : Set Vec3) ∧ ¬ ConnDomain (∅ : Set Vec3) := by
  constructor
  · have : sphSet (∅ : Set Vec3) = (∅ : Set Sph) := by ext s; simp [sphSet]
    rw [PreconnDomain, this]
    exact isPreconnected_empty
  · intro h
    obtain ⟨s, hs⟩ := h.1
    exact hs

/-- **DERIVED (§10), second separation.**  An antipodal two-point domain is admissible but
not preconnected, so admissibility does not imply any connectedness. -/
theorem antipodal_pair_not_preconn {n : Vec3} (hn : IsUnitAxis n) :
    IsAdmissibleDomain ({n, -n} : Set Vec3) ∧ ¬ PreconnDomain ({n, -n} : Set Vec3) := by
  refine ⟨(antipodal_pair_admissible hn).1, ?_⟩
  intro hpre
  obtain ⟨-, U, hU, hexact, h1, h2⟩ := antipodal_pair_admissible hn
  have hunit : ∀ m ∈ ({n, -n} : Set Vec3), IsUnitAxis m := by
    rintro m (rfl | rfl)
    · exact hn
    · exact isUnitAxis_neg hn
  have := label_const_of_preconnected hU hunit hpre hexact n (by simp) (-n) (by simp)
  rw [h1, h2] at this
  norm_num at this

/-! ## §11, §12 — the preconnected admissibility theorem -/

/-- **DERIVED (§12), necessity.**  A preconnected admissible set of unit directions is
antipodal-free.  The proof combines two independent Task-17 endpoints: on a preconnected
admissible domain the recovered rate is constant, and on an antipodal pair contained in an
admissible domain it is odd.  A half-odd number is not its own negative. -/
theorem antipodalFree_of_admissible_preconn {D : Set Vec3} (hunit : UnitSet D)
    (hpre : PreconnDomain D) (hadm : IsAdmissibleDomain D) : AntipodalFree D := by
  intro n hn hneg
  obtain ⟨-, U, hU, hexact⟩ := hadm
  have hconst : rateBeta U n = rateBeta U (-n) :=
    label_const_of_preconnected hU hunit hpre hexact n hn (-n) hneg
  obtain ⟨-, -, -, hodd⟩ := admissible_necessary hU hunit hexact
  have hoddn : rateBeta U (-n) = -rateBeta U n := hodd n hn hneg
  obtain ⟨k, hk⟩ := (pointwise_rates hU hexact hn (hunit n hn)).2
  rw [hoddn] at hconst
  have hzero : rateBeta U n = 0 := by linarith
  rw [hzero] at hk
  have : (2 * k : ℤ) = -1 := by
    have : (2 * (k : ℝ)) = -1 := by linarith
    exact_mod_cast this
  omega

/-- **PRINCIPAL THEOREM (§11).**  For a **preconnected** set of unit directions,
admissibility and antipodal-freeness are equivalent.  No nonemptiness hypothesis is needed
(see `admissible_iff_antipodalFree_empty`). -/
theorem admissible_iff_antipodalFree_of_preconn {D : Set Vec3} (hunit : UnitSet D)
    (hpre : PreconnDomain D) : IsAdmissibleDomain D ↔ AntipodalFree D := by
  constructor
  · exact antipodalFree_of_admissible_preconn hunit hpre
  · intro hfree
    exact (antipodalFree_admissible hunit hfree).2

/-! ## §13 — the empty domain -/

theorem empty_unitSet : UnitSet (∅ : Set Vec3) := by intro n hn; exact absurd hn (by simp)

theorem empty_preconn : PreconnDomain (∅ : Set Vec3) := empty_preconn_not_conn.1

theorem empty_antipodalFree : AntipodalFree (∅ : Set Vec3) := by
  intro n hn
  exact absurd hn (by simp)

theorem empty_admissible : IsAdmissibleDomain (∅ : Set Vec3) :=
  (antipodalFree_admissible empty_unitSet empty_antipodalFree).2

/-- **DERIVED (§13).**  The empty domain satisfies both sides of the equivalence, so the
theorem is *not* vacuous there and nonemptiness is not required. -/
theorem admissible_iff_antipodalFree_empty :
    IsAdmissibleDomain (∅ : Set Vec3) ∧ AntipodalFree (∅ : Set Vec3) ∧
      (IsAdmissibleDomain (∅ : Set Vec3) ↔ AntipodalFree (∅ : Set Vec3)) :=
  ⟨empty_admissible, empty_antipodalFree,
    admissible_iff_antipodalFree_of_preconn empty_unitSet empty_preconn⟩

/-! ## §14 — the connected and path-connected corollaries -/

/-- **DERIVED (§14).**  The connected case, obtained from the preconnected theorem. -/
theorem admissible_iff_antipodalFree_of_conn {D : Set Vec3} (hunit : UnitSet D)
    (hconn : ConnDomain D) : IsAdmissibleDomain D ↔ AntipodalFree D :=
  admissible_iff_antipodalFree_of_preconn hunit hconn.preconn

/-- **DERIVED (§14).**  The path-connected case, obtained from the preconnected theorem. -/
theorem admissible_iff_antipodalFree_of_pathConn {D : Set Vec3} (hunit : UnitSet D)
    (hpath : PathConnDomain D) : IsAdmissibleDomain D ↔ AntipodalFree D :=
  admissible_iff_antipodalFree_of_preconn hunit hpath.preconn

/-- **DERIVED (§14).**  Specialization to the inherited domains: they are admissible and
antipodal-free, and the equivalence applies to them. -/
theorem Dom_admissible_iff_antipodalFree {v : Vec3} (hv : v ≠ 0) :
    IsAdmissibleDomain (Dom v) ∧ AntipodalFree (Dom v) ∧
      (IsAdmissibleDomain (Dom v) ↔ AntipodalFree (Dom v)) := by
  have hunit : UnitSet (Dom v) := fun n hn => hn.1
  have hfree : AntipodalFree (Dom v) := fun n hn => Dom_antipodal_free hn
  refine ⟨(antipodalFree_admissible hunit hfree).2, hfree,
    admissible_iff_antipodalFree_of_preconn hunit (isPreconnected_sphSet_Dom hv)⟩

end NullSectorTask18
