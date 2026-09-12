import RequestProject.Spine.Nerve.Geometry.CarrierDim

/-!
# The weak topology of a geometric realization, and compact subsets

`SSet.toTop` is a left adjoint, hence preserves the tautological colimit presentation of a
simplicial set by standard simplices.  Colimits in `TopCat` carry the final topology, so `|K|`
carries the *weak topology* determined by its cells: a subset is closed exactly when its
preimage in every `|Δ[n]|` is closed (`NerveTopology.isClosed_iff`).

Combining this with the point model of `Nerve/Geometry/NormalForm.lean` gives the two facts
that the skeletal factorization of a singular simplex rests on:

* `NerveTopology.isClosed_cellPoint_eq` — the fibre of a cell over a point of `|K|` is closed
  (equivalently, `|K|` is a T1 space);
* `NerveTopology.exists_carrierDim_bound` — **a compact subset of `|K|` meets only cells of
  bounded dimension.**  This is the honest form of "a compact subset of a CW complex meets only
  finitely many cells"; it is proved here, not cited.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial Finset SpineTask16 NerveNormalForm

universe u

namespace NerveTopology

variable {K : SSet.{u}}

/-! ## The weak topology -/

/-- Barycentric coordinates on a realized standard simplex, as a homeomorphism. -/
noncomputable def coordHomeo (n : SimplexCategory) :
    (SSet.toTop.{u}.obj (SSet.stdSimplex.obj n) : Type u) ≃ₜ stdSimplex ℝ (Fin (n.len + 1)) :=
  (TopCat.homeoOfIso (SSet.toTopSimplex.{u}.app n)).trans Homeomorph.ulift

/-- **The realization carries the weak topology of its cells.** -/
theorem isClosed_iff (K : SSet.{u}) (S : Set (SSet.toTop.{u}.obj K)) :
    IsClosed S ↔ ∀ (X : SimplexCategory) (a : K.obj (op X)),
      IsClosed {w : stdSimplex ℝ (Fin (X.len + 1)) | cellPoint a w ∈ S} := by
  have hc : IsColimit (SSet.toTop.{u}.mapCocone (Presheaf.tautologicalCocone'.{u} K)) :=
    isColimitOfPreserves _ (Presheaf.isColimitTautologicalCocone'.{u} K)
  rw [TopCat.isClosed_iff_of_isColimit _ hc]
  constructor
  · intro h X a
    have h1 := h (CostructuredArrow.mk (SSet.yonedaEquiv.symm a))
    have h2 := ((coordHomeo.{u} X).symm.isClosed_preimage (s := _)).2 h1
    convert h2 using 1
  · intro h j
    have h1 := h j.left (SSet.yonedaEquiv j.hom)
    have h2 := ((coordHomeo.{u} j.left).isClosed_preimage (s := _)).2 h1
    convert h2 using 1
    ext t
    show _ ↔ cellPoint (SSet.yonedaEquiv j.hom) (coord j.left t) ∈ S
    rw [cellPoint, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl

/-- The underlying space of a geometric realization. -/
abbrev RealSpace (K : SSet.{u}) : Type u := (SSet.toTop.{u}.obj K : Type u)

/-- A cell of `|K|`, as a map of underlying spaces. -/
def cellMap {X : SimplexCategory} (a : K.obj (op X)) :
    stdSimplex ℝ (Fin (X.len + 1)) → RealSpace K := fun w => cellPoint a w

/-- The realization of a map of simplicial sets, as a map of underlying spaces. -/
def realMap {L K : SSet.{u}} (f : L ⟶ K) : RealSpace L → RealSpace K := Rz.{u}.map f

/-- A cell is a continuous map into the realization. -/
theorem continuous_cellPoint {X : SimplexCategory} (a : K.obj (op X)) :
    Continuous (cellMap a) :=
  (SSet.toTop.map (SSet.yonedaEquiv.symm a)).hom.continuous.comp
    (coordHomeo.{u} X).symm.continuous

/-! ## Fibres of a cell -/

/-- **The fibre of a cell over a point of `|K|` is closed.** -/
theorem isClosed_cellPoint_eq {X : SimplexCategory} (a : K.obj (op X))
    (x : (SSet.toTop.{u}.obj K : Type u)) :
    IsClosed {w : stdSimplex ℝ (Fin (X.len + 1)) | cellPoint a w = x} := by
  classical
  obtain ⟨m, σ, hσ, u, hu, hnf, hx⟩ := exists_cellPoint_nf K x
  set C : (Σ (k : Fin (X.len + 1)), ((⦋(k : ℕ)⦌ : SimplexCategory) ⟶ X) ×
      ((⦋(k : ℕ)⦌ : SimplexCategory) ⟶ ⦋m⦌)) → Set (stdSimplex ℝ (Fin (X.len + 1))) :=
    fun i => if K.map i.2.1.op a = K.map i.2.2.op σ then
        (stdSimplex.map i.2.1.toOrderHom) '' {v | stdSimplex.map i.2.2.toOrderHom v = u}
      else ∅ with hC
  have hcov : {w : stdSimplex ℝ (Fin (X.len + 1)) | cellPoint a w = x} = ⋃ i, C i := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hw
      obtain ⟨k, m', e, φ, v, σ', hσ', he, hφ, hv, hwe, hb, hp⟩ := isNF_nfOf a w
      have hnfw : nfOf a w = (SSet.N.mk σ hσ, extend u) := by rw [← nf_cellPoint, hw, hnf]
      rw [hp] at hnfw
      have hdim : m' = m := congrArg (fun p => (p : NFData K).1.dim) hnfw
      subst hdim
      have h1 : SSet.N.mk σ' hσ' = SSet.N.mk σ hσ := congrArg Prod.fst hnfw
      have h2 : extend (stdSimplex.map φ.toOrderHom v) = extend u := congrArg Prod.snd hnfw
      obtain rfl : σ' = σ := N_mk_inj h1
      have hφv : stdSimplex.map φ.toOrderHom v = u := extend_injective h2
      haveI : Mono e := SimplexCategory.mono_iff_injective.2 he
      have hk : k ≤ X.len := SimplexCategory.len_le_of_mono e
      refine ⟨⟨⟨k, by omega⟩, (e, φ)⟩, ?_⟩
      rw [hC]
      simp only [hb, if_pos]
      exact ⟨v, hφv, hwe⟩
    · rintro ⟨i, hi⟩
      simp only [hC] at hi
      by_cases hcond : K.map i.2.1.op a = K.map i.2.2.op σ
      · simp only [hcond, if_pos] at hi
        obtain ⟨v, hv, rfl⟩ := hi
        rw [← cellPoint_map, hcond, cellPoint_map, hv, hx]
      · rw [if_neg hcond] at hi
        exact absurd hi (Set.notMem_empty w)
  rw [hcov]
  refine isClosed_iUnion_of_finite (fun i => ?_)
  simp only [hC]
  by_cases hcond : K.map i.2.1.op a = K.map i.2.2.op σ
  · simp only [hcond, if_pos]
    have hfib : IsClosed {v : stdSimplex ℝ (Fin ((i.1 : ℕ) + 1)) |
        stdSimplex.map i.2.2.toOrderHom v = u} :=
      isClosed_eq (stdSimplex.continuous_map _) continuous_const
    exact (hfib.isCompact.image (stdSimplex.continuous_map _)).isClosed
  · rw [if_neg hcond]
    exact isClosed_empty

/-! ## Bounded carrier dimension on a cell -/

/-- The carrier dimension of a point of a cell is at most the dimension of the cell. -/
theorem carrierDim_cellPoint_le {X : SimplexCategory} (a : K.obj (op X))
    (w : stdSimplex ℝ (Fin (X.len + 1))) : carrierDim K (cellPoint a w) ≤ X.len := by
  obtain ⟨k, m, e, φ, v, σ, hσ, he, hφ, hv, hwe, hb, hp⟩ := isNF_nfOf a w
  haveI : Mono e := SimplexCategory.mono_iff_injective.2 he
  haveI := hφ
  have h1 : m ≤ k := SimplexCategory.len_le_of_epi φ
  have h2 : k ≤ X.len := SimplexCategory.len_le_of_mono e
  have hcd : carrierDim K (cellPoint a w) = m := by
    simp only [carrierDim, nf_cellPoint, hp]
    rfl
  omega

/-! ## Compact subsets meet only cells of bounded dimension -/

/-- **A compact subset of `|K|` has bounded carrier dimension.**  This is the point-set input
of the skeletal factorization; no CW structure is cited. -/
theorem exists_carrierDim_bound (K : SSet.{u}) (Q : Set (SSet.toTop.{u}.obj K))
    (hQ : IsCompact Q) : ∃ r : ℕ, ∀ x ∈ Q, carrierDim K x < r := by
  classical
  by_contra hcon
  push_neg at hcon
  choose g hgQ hgdim using hcon
  -- a sequence in `Q` whose carrier dimensions strictly increase
  set d : ℕ → ℕ := fun n => Nat.rec 0 (fun _ p => carrierDim K (g p) + 1) n with hd
  set f : ℕ → (SSet.toTop.{u}.obj K : Type u) := fun n => g (d n) with hf
  have hfQ : ∀ n, f n ∈ Q := fun n => hgQ (d n)
  have hstep : ∀ n, carrierDim K (f n) < carrierDim K (f (n + 1)) := by
    intro n
    have h2 : carrierDim K (f n) + 1 ≤ carrierDim K (f (n + 1)) := hgdim (d (n + 1))
    omega
  have hmono : StrictMono (fun n => carrierDim K (f n)) := strictMono_nat_of_lt_succ hstep
  have hge : ∀ n, n ≤ carrierDim K (f n) := fun n => hmono.le_apply
  have hinj : Function.Injective f := by
    intro p q h
    exact hmono.injective (by rw [h])
  -- every subset of the range of `f` is closed
  have hclosed : ∀ S : Set (SSet.toTop.{u}.obj K), S ⊆ Set.range f → IsClosed S := by
    intro S hS
    rw [isClosed_iff]
    intro X a
    set T : Set (SSet.toTop.{u}.obj K) := S ∩ {x | carrierDim K x ≤ X.len} with hT
    have hTfin : T.Finite := by
      have hsub : T ⊆ f '' (Set.Iic X.len) := by
        rintro y ⟨hyS, hyd⟩
        obtain ⟨n, rfl⟩ := hS hyS
        exact ⟨n, le_trans (hge n) hyd, rfl⟩
      exact Set.Finite.subset ((Set.finite_Iic _).image f) hsub
    have hEq : {w : stdSimplex ℝ (Fin (X.len + 1)) | cellPoint a w ∈ S}
        = ⋃ y ∈ T, {w : stdSimplex ℝ (Fin (X.len + 1)) | cellPoint a w = y} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      constructor
      · intro hw
        exact ⟨cellPoint a w, ⟨hw, carrierDim_cellPoint_le a w⟩, rfl⟩
      · rintro ⟨y, ⟨hyS, -⟩, rfl⟩
        exact hyS
    rw [hEq]
    exact hTfin.isClosed_biUnion (fun y _ => isClosed_cellPoint_eq a y)
  -- the range of `f` is then a compact discrete infinite set
  have hAclosed : IsClosed (Set.range f) := hclosed _ le_rfl
  have hAcompact : IsCompact (Set.range f) :=
    hQ.of_isClosed_subset hAclosed (by rintro _ ⟨n, rfl⟩; exact hfQ n)
  have hopen : ∀ n : ℕ, IsOpen (Set.range f \ {f n})ᶜ :=
    fun n => (hclosed _ Set.diff_subset).isOpen_compl
  obtain ⟨t, ht⟩ := hAcompact.elim_finite_subcover (fun n : ℕ => (Set.range f \ {f n})ᶜ) hopen
    (by
      rintro _ ⟨n, rfl⟩
      exact Set.mem_iUnion.2 ⟨n, by simp⟩)
  obtain ⟨N, hN⟩ := t.exists_notMem
  obtain ⟨n, hn, hmem⟩ := Set.mem_iUnion₂.1 (ht ⟨N, rfl⟩)
  have : f N = f n := by
    by_contra hne
    exact hmem ⟨⟨N, rfl⟩, by simpa using hne⟩
  exact hN (hinj this ▸ hn)

end NerveTopology
