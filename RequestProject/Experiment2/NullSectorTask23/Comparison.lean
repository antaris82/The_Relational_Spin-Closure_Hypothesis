import RequestProject.Experiment2.NullSectorTask23.Hierarchy

/-!
# Task 23, Package M: comparison-only identification

**IDENTIFICATION / COMPARISON MODULE.  Nothing in this module is used by Packages A–L.**

Only here, and only after the intrinsic work is complete, is the reconstructed object
compared with established terminology (items 91–94).

The exact ingredients proved in Packages A–G are collected in `task23_ingredients`:

* a continuous surjection `pr : LiftT → GvisT`;
* fibres with exactly two elements and a discrete two-element sign carrier;
* an explicit finite open cover of the base;
* a continuous local representative on each cover element;
* a homeomorphism `pr ⁻¹' (Vset i) ≃ₜ Vset i × Sgn` over each cover element;
* transition data valued in `{+1,-1}`, continuous, hence locally constant;
* the identity, inverse and triple-overlap laws;
* recovery of the global carrier by gluing.

Because *all* of these hold, the object satisfies Mathlib's own definition of a covering
map, and this is proved here as `isCoveringMap_pr`: the conventional classification of the
reconstructed object is **a two-sheeted covering map of the visible carrier**.  Nothing
further is claimed: no frame bundle, no tangent bundle, no spin structure and no physical
interpretation occurs anywhere in this development (items 95–97, 100, 104).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask23

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14 NullSectorTask15 NullSectorTask16 NullSectorTask17 NullSectorTask18
open NullSectorTask19 NullSectorTask20 NullSectorTask21

open Quaternion Topology

/-! ## The exact ingredient list (item 92) -/

/-- **PACKAGE M (item 92).**  The complete list of exact ingredients established by
Packages A–G, in one statement. -/
theorem task23_ingredients :
    -- a continuous surjection
    (Continuous pr ∧ Function.Surjective pr) ∧
    -- a discrete two-element fibre
    (DiscreteTopology Sgn ∧ ∀ g : GvisT, ∃ u v : LiftT, u ≠ v ∧ pr u = g ∧ pr v = g ∧
        ∀ w : LiftT, pr w = g → w = u ∨ w = v) ∧
    -- an explicit open cover
    ((∀ i : Fin 4, IsOpen (Vset i)) ∧ (⋃ i : Fin 4, Vset i) = (Set.univ : Set GvisT)) ∧
    -- continuous local representatives
    (∀ i : Fin 4, Continuous (sec i) ∧ ∀ g : ↥(Vset i), pr (sec i g) = (g : GvisT)) ∧
    -- local product homeomorphisms
    (∀ i : Fin 4, ∃ e : ↥(pr ⁻¹' (Vset i)) ≃ₜ (↥(Vset i) × Sgn),
        ∀ u : ↥(pr ⁻¹' (Vset i)), ((e u).1 : GvisT) = pr (u : LiftT)) ∧
    -- transition data, continuous hence locally constant
    (∀ i j : Fin 4, Continuous (tau i j) ∧ IsLocallyConstant (tau i j)) ∧
    -- identity, inverse and triple-overlap laws
    ((∀ (i : Fin 4) (g : GvisT) (hi : g ∈ Vset i), tauAt i i g hi hi = 1) ∧
      (∀ (a b : Fin 4) (g : GvisT) (ha : g ∈ Vset a) (hb : g ∈ Vset b),
        tauAt b a g hb ha = (tauAt a b g ha hb)⁻¹) ∧
      (∀ (a b c : Fin 4) (g : GvisT) (ha : g ∈ Vset a) (hb : g ∈ Vset b) (hc : g ∈ Vset c),
        tauAt a c g ha hc = tauAt b c g hb hc * tauAt a b g ha hb)) ∧
    -- global recovery by gluing
    (∃ e : LiftLocal ≃ₜ LiftT, ∀ z : LiftLocal, pr (e z) = prLocal z) :=
  ⟨⟨continuous_pr, pr_surjective⟩,
   ⟨Sgn.discrete, core_fibre_two⟩,
   ⟨isOpen_Vset, Vset_covers⟩,
   fun i => ⟨continuous_sec i, pr_sec i⟩,
   fun i => ⟨preimageProdHomeo i, preimageProdHomeo_fst i⟩,
   fun i j => ⟨continuous_tau i j, isLocallyConstant_tau i j⟩,
   ⟨tauAt_self, tauAt_symm, tauAt_trans⟩,
   level3_sufficient⟩

/-! ## The conventional classification (item 93) -/

open scoped Classical in
/-- The local product map of the domain `Vset i`, written as a total function. -/
noncomputable def trivToFun (i : Fin 4) (u : LiftT) : GvisT × Sgn :=
  (pr u, if h : qco i (u : W) = 0 then 1 else sgnOf h)

open scoped Classical in
/-- Its inverse, written as a total function. -/
noncomputable def trivInvFun (i : Fin 4) (p : GvisT × Sgn) : LiftT :=
  if h : p.1 ∈ Vset i then sact p.2 (sec i ⟨p.1, h⟩) else ⟨w1, w1_mem_Lift⟩

theorem trivToFun_apply {i : Fin 4} {u : LiftT} (hu : qco i (u : W) ≠ 0) :
    trivToFun i u = (pr u, sgnOf hu) := by
  rw [trivToFun, dif_neg hu]

theorem trivInvFun_apply {i : Fin 4} {g : GvisT} (hg : g ∈ Vset i) (e : Sgn) :
    trivInvFun i (g, e) = sact e (sec i ⟨g, hg⟩) := by
  rw [trivInvFun, dif_pos hg]

theorem source_eq_Uset (i : Fin 4) : pr ⁻¹' (Vset i) = Uset i := preimage_Vset i

/-- **PACKAGE M.**  The local product decomposition of Package F, packaged as a
trivialization in the standard sense. -/
noncomputable def triv (i : Fin 4) : Trivialization Sgn pr where
  toFun := trivToFun i
  invFun := trivInvFun i
  source := pr ⁻¹' (Vset i)
  target := (Vset i) ×ˢ (Set.univ : Set Sgn)
  map_source' := by
    intro u hu
    have hq : qco i (u : W) ≠ 0 := by
      rw [source_eq_Uset] at hu; exact hu
    rw [trivToFun_apply hq]
    exact ⟨hu, Set.mem_univ _⟩
  map_target' := by
    rintro ⟨g, e⟩ ⟨hg, -⟩
    rw [trivInvFun_apply hg]
    show pr (sact e (sec i ⟨g, hg⟩)) ∈ Vset i
    rw [pr_sact, pr_sec]
    exact hg
  left_inv' := by
    intro u hu
    have hq : qco i (u : W) ≠ 0 := by
      rw [source_eq_Uset] at hu; exact hu
    rw [trivToFun_apply hq, trivInvFun_apply (mem_Vset_of hq)]
    show sact (sgnOf hq) (sec i ⟨pr u, mem_Vset_of hq⟩) = u
    rw [sec_eq_sact_of_rep (mem_Vset_of hq) rfl hq, ← sact_mul, Sgn.mul_self, sact_one]
  right_inv' := by
    rintro ⟨g, e⟩ ⟨hg, -⟩
    have hpos : 0 < qco i ((sec i ⟨g, hg⟩ : LiftT) : W) := sec_pos i ⟨g, hg⟩
    have hq : qco i ((sact e (sec i ⟨g, hg⟩) : LiftT) : W) ≠ 0 := by
      have h := sact_sec_mem_Uset i (⟨g, hg⟩, e)
      exact h
    rw [trivInvFun_apply hg, trivToFun_apply hq]
    refine Prod.ext ?_ ?_
    · show pr (sact e (sec i ⟨g, hg⟩)) = g
      rw [pr_sact, pr_sec]
    · show sgnOf hq = e
      have hval : qco i ((sact e (sec i ⟨g, hg⟩) : LiftT) : W)
          = (e : ℝ) * qco i ((sec i ⟨g, hg⟩ : LiftT) : W) := by
        rw [sact_val, qco_smul]
      refine Subtype.ext ?_
      rw [sgnOf_val, hval]
      have h : sgnOf (show (e : ℝ) * qco i ((sec i ⟨g, hg⟩ : LiftT) : W) ≠ 0 from by
          rw [← hval]; exact hq) = e := sgnOf_smul_of_pos hpos _
      exact congrArg Subtype.val h
  open_source := (isOpen_Vset i).preimage continuous_pr
  open_target := (isOpen_Vset i).prod isOpen_univ
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_restrict]
    have hres : (pr ⁻¹' (Vset i)).restrict (trivToFun i)
        = fun u : ↥(pr ⁻¹' (Vset i)) =>
            (((locProdInv i ⟨(u : LiftT), by rw [← source_eq_Uset]; exact u.2⟩).1 : GvisT),
              (locProdInv i ⟨(u : LiftT), by rw [← source_eq_Uset]; exact u.2⟩).2) := by
      funext u
      have hq : qco i ((u : LiftT) : W) ≠ 0 := mem_Vset_iff.1 u.2 (u : LiftT) rfl
      show trivToFun i (u : LiftT) = _
      rw [trivToFun_apply hq]
      rfl
    rw [hres]
    have hmap : Continuous fun u : ↥(pr ⁻¹' (Vset i)) =>
        (⟨(u : LiftT), by rw [← source_eq_Uset]; exact u.2⟩ : ↥(Uset i)) :=
      Continuous.subtype_mk continuous_subtype_val _
    exact Continuous.prodMk
      (continuous_subtype_val.comp (continuous_fst.comp ((continuous_locProdInv i).comp hmap)))
      (continuous_snd.comp ((continuous_locProdInv i).comp hmap))
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_restrict]
    have hres : ((Vset i) ×ˢ (Set.univ : Set Sgn)).restrict (trivInvFun i)
        = fun q : ↥((Vset i) ×ˢ (Set.univ : Set Sgn)) =>
            ((locProd i (⟨(q : GvisT × Sgn).1, q.2.1⟩, (q : GvisT × Sgn).2) : ↥(Uset i)) :
              LiftT) := by
      funext q
      show trivInvFun i ((q : GvisT × Sgn).1, (q : GvisT × Sgn).2) = _
      rw [trivInvFun_apply q.2.1]
      rfl
    rw [hres]
    have hmap : Continuous fun q : ↥((Vset i) ×ˢ (Set.univ : Set Sgn)) =>
        ((⟨(q : GvisT × Sgn).1, q.2.1⟩ : ↥(Vset i)), (q : GvisT × Sgn).2) :=
      Continuous.prodMk
        (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _)
        (continuous_snd.comp continuous_subtype_val)
    exact continuous_subtype_val.comp ((continuous_locProd i).comp hmap)
  baseSet := Vset i
  open_baseSet := isOpen_Vset i
  source_eq := rfl
  target_eq := rfl
  proj_toFun := by
    intro u hu
    have hq : qco i (u : W) ≠ 0 := by
      rw [source_eq_Uset] at hu; exact hu
    show (trivToFun i u).1 = pr u
    rw [trivToFun_apply hq]

/-- **PACKAGE M (item 93), principal comparison endpoint.**  All the required ingredients
having been proved intrinsically, the reconstructed object satisfies the standard
definition: the certified projection is a covering map of the visible carrier, with
two-element fibre.  This is the *only* conventional classification claimed by Task 23. -/
theorem isCoveringMap_pr : IsCoveringMap pr := by
  classical
  refine IsCoveringMap.mk pr (fun _ => Sgn) (fun g => triv (Classical.choose (exists_mem_Vset g)))
    fun g => ?_
  exact Classical.choose_spec (exists_mem_Vset g)

/-! ## Negative controls (items 98–104) -/

/-- **PACKAGE M (items 98, 99, 101, 102, 103), negative controls.**  Each entry is a proved
statement of the corresponding boundary. -/
theorem task23_negative_controls :
    -- 98: continuous local representatives exist, yet no global continuous one does
    ((∀ i : Fin 4, Continuous (sec i)) ∧
      ¬ ∃ σ : GvisT → LiftT, Continuous σ ∧ IsGlobalRep σ) ∧
    -- 99: a two-element fibre alone does not give a local product decomposition
    (¬ ∃ e : BadTotal ≃ₜ (ℝ × Sgn), ∀ z : BadTotal, (e z).1 = badProj z) ∧
    -- 101: the direction-reversal quotient is not the kernel-sign fibre
    (∃ a b c : RevQuot, a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧
    -- 102: integer label data are strictly finer than their sign
    (∃ b b' : ℝ, b ∈ HalfOddSet ∧ b' ∈ HalfOddSet ∧ (∃ k : ℤ, b' = b + 2 * (k : ℝ)) ∧
      (∃ θ : ℝ, labelBridge b θ ≠ labelBridge b' θ) ∧
      labelBridge b (2 * Real.pi) = labelBridge b' (2 * Real.pi)) ∧
    -- 103: the extended carrier is not reconstructed by two-valued data
    Set.Infinite {z : W | z ∈ LiftZ ∧ proj z = LinearMap.id} :=
  ⟨⟨continuous_sec, no_continuous_global_rep⟩,
   no_local_product_of_two_element_fibre,
   revQuot_not_two_element,
   sign_data_insufficient_for_extended,
   extended_fibre_infinite⟩

end NullSectorTask23
