import RequestProject.Spine.Cech.SpinCocycle

/-!
# Task 6, WP9 and WP11 : comparison with the Task-3 `ObstructionClass`, and refinement

## WP9 — what exactly is the relation between the two quotients?

The Task-3 carrier is

`CechSpinLift.ObstructionClass P 𝓤 = (ι → ι → ι → (X → L)) / Cohomologous`,

i.e. **all** `L`-valued functions of three indices — no cocycle condition, no kernel condition,
no constancy condition — modulo multiplication by `δε` for a *continuous kernel-valued*
1-cochain `ε` (again not required to be locally constant, and only compared on the overlaps).

The Task-6 carrier is the standard fixed-cover object `Ȟ²(𝓤;ℤ₂) = Ž²/B̌²`.

These are visibly not the same type, and neither is a definitional unfolding of the other.  What
is proved here:

* `CechSpinZ2.toObstruction` — a **canonical map** `Ȟ²(𝓤;ℤ₂) → ObstructionClass P 𝓤`, obtained by
  reading a `ℤ₂`-cocycle as the *constant* kernel-valued 2-cochain with those signs
  (`toOldCochain`).  It is well defined because a Čech coboundary becomes a Task-3
  `Cohomologous` change (`cohomologous_toOldCochain`).
* `CechSpinZ2.toObstruction_spinCechClass` — it sends the Task-6 Spin class to the Task-3 Spin
  class:  `toObstruction [z] = [c]`.  The two obstructions are therefore the *same* obstruction,
  presented in two carriers.
* `CechSpinZ2.toObstruction_injective` — on a cover with preconnected double overlaps the
  canonical map is **injective**.  This is the strongest honest statement: the Čech group embeds
  canonically into the Task-3 quotient, compatibly with the Spin classes.
* `CechSpinZ2.mem_ker_of_eq_toObstruction` and
  `CechSpinZ2.classOf_not_mem_range_toObstruction` — the map is **not** surjective in general:
  every class in its image has a representative that is kernel-valued on overlaps, whereas the
  Task-3 quotient also contains classes of cochains taking values outside `ker ρ`.  The old
  carrier is therefore strictly larger, and the honest classification of the pair is
  `EMBEDS_CANONICALLY` (with equality of the *Spin* classes and of their vanishing), not
  `DEFINITIONALLY_EQUAL`.
* `CechSpinZ2.spinCechClass_eq_zero_iff_obstruction_eq_trivial` — the two vanishing statements
  agree (on a cover with preconnected double overlaps).

## WP11 — refinement

`CechZ2.Hmap R.le 2` is the refinement pullback of WP11 on the Čech side; `Hmap_spinCechClass`
proves `r*[z_𝓤] = [z_𝓥]` for the pulled-back lift family, and
`spinCechClass_pull_indep_of_map` transports the Task-3 independence from the chosen refinement
index map through the embedding above.
-/

namespace CechSpinZ2

open CechSpinLift CechZ2 NullSectorTask28

universe u v w t

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι ι' : Type t}
  {𝓤 : CechCover X ι} {𝓥 : CechCover X ι'} {P : InternalProjection L G}
  {T : VisibleCocycle G 𝓤}

/-! ## Reading a Čech 2-cochain as a Task-3 2-cochain -/

open scoped Classical in
/-- A Čech `ℤ₂`-valued 2-cochain, read back as a Task-3 2-cochain: on each nonempty triple
overlap it is the *constant* kernel element with the prescribed sign. -/
noncomputable def toOldCochain (S : KernelSign P) (𝓤 : CechCover X ι) (z : Cochain 𝓤.U 2) :
    ι → ι → ι → (X → L) :=
  fun i j k _ => if h : (𝓤.overlap₃ i j k).Nonempty then S.ofZ (z (nerve₂ 𝓤 i j k h)) else 1

theorem toOldCochain_apply_of_mem (S : KernelSign P) (z : Cochain 𝓤.U 2) (i j k : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₃ i j k) (y : X) :
    toOldCochain S 𝓤 z i j k y = S.ofZ (z (nerve₂ 𝓤 i j k ⟨x, hx⟩)) := by
  simp only [toOldCochain]
  rw [dif_pos ⟨x, hx⟩]

theorem toOldCochain_mem_ker (S : KernelSign P) (z : Cochain 𝓤.U 2) (i j k : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₃ i j k) (y : X) : toOldCochain S 𝓤 z i j k y ∈ P.Ker := by
  rw [toOldCochain_apply_of_mem S z i j k hx y]
  exact S.ofZ_mem _

theorem sgn_toOldCochain (S : KernelSign P) (z : Cochain 𝓤.U 2) (i j k : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₃ i j k) :
    S.sgn (toOldCochain S 𝓤 z i j k x) = z (nerve₂ 𝓤 i j k ⟨x, hx⟩) := by
  rw [toOldCochain_apply_of_mem S z i j k hx x, S.sgn_ofZ]

/-- The value of the Čech coboundary of a 1-cochain on an explicit triple. -/
theorem d_apply_nerve₂ (a : Cochain 𝓤.U 1) (i j k : ι) (h : (𝓤.overlap₃ i j k).Nonempty)
    (hjk : (𝓤.overlap₂ j k).Nonempty) (hik : (𝓤.overlap₂ i k).Nonempty)
    (hij : (𝓤.overlap₂ i j).Nonempty) :
    d 𝓤.U 1 a (nerve₂ 𝓤 i j k h)
      = a (nerve₁ 𝓤 j k hjk) + a (nerve₁ 𝓤 i k hik) + a (nerve₁ 𝓤 i j hij) := by
  show (∑ t : Fin 3, a (face t (nerve₂ 𝓤 i j k h))) = _
  rw [Fin.sum_univ_three, face_nerve₂_zero 𝓤 i j k h hjk, face_nerve₂_one 𝓤 i j k h hik,
    face_nerve₂_two 𝓤 i j k h hij]

/-- **WP9, key step.**  A Čech coboundary becomes a Task-3 `Cohomologous` change: the map
`toOldCochain` descends to the quotients. -/
theorem cohomologous_toOldCochain (S : KernelSign P) (z z' : Cochain 𝓤.U 2)
    (a : Cochain 𝓤.U 1) (h : z' = z + d 𝓤.U 1 a) :
    Cohomologous P 𝓤 (toOldCochain S 𝓤 z) (toOldCochain S 𝓤 z') := by
  refine ⟨kerCochainOf S 𝓤 a, kerCochainOf_isKerCochain₁ S a, fun i j k x hx => ?_⟩
  have hij : x ∈ 𝓤.overlap₂ i j := 𝓤.overlap₃_subset_ij i j k hx
  have hjk : x ∈ 𝓤.overlap₂ j k := 𝓤.overlap₃_subset_jk i j k hx
  have hik : x ∈ 𝓤.overlap₂ i k := 𝓤.overlap₃_subset_ik i j k hx
  have mij : kerCochainOf S 𝓤 a i j x ∈ P.Ker :=
    (kerCochainOf_isKerCochain₁ S a i j).2 x hij
  have mjk : kerCochainOf S 𝓤 a j k x ∈ P.Ker :=
    (kerCochainOf_isKerCochain₁ S a j k).2 x hjk
  have mik : kerCochainOf S 𝓤 a i k x ∈ P.Ker :=
    (kerCochainOf_isKerCochain₁ S a i k).2 x hik
  have mz : toOldCochain S 𝓤 z i j k x ∈ P.Ker := toOldCochain_mem_ker S z i j k hx x
  have mz' : toOldCochain S 𝓤 z' i j k x ∈ P.Ker := toOldCochain_mem_ker S z' i j k hx x
  refine S.sgn_injOn mz' (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ mij mjk)
    (Subgroup.inv_mem _ mik)) mz) ?_
  rw [delta₁_apply,
    S.sgn_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ mij mjk) (Subgroup.inv_mem _ mik)) mz,
    S.sgn_mul (Subgroup.mul_mem _ mij mjk) (Subgroup.inv_mem _ mik), S.sgn_mul mij mjk,
    S.sgn_inv mik, sgn_kerCochainOf S a i j hij, sgn_kerCochainOf S a j k hjk,
    sgn_kerCochainOf S a i k hik, sgn_toOldCochain S z i j k hx,
    sgn_toOldCochain S z' i j k hx, h]
  rw [Cochain.add_apply, d_apply_nerve₂ a i j k ⟨x, hx⟩ ⟨x, hjk⟩ ⟨x, hik⟩ ⟨x, hij⟩]
  ring

/-! ## WP9 — the canonical map -/

/-- **WP9, principal.**  The canonical map from genuine fixed-cover Čech cohomology to the
Task-3 obstruction quotient. -/
noncomputable def toObstruction (S : KernelSign P) (𝓤 : CechCover X ι) :
    H2 𝓤.U → ObstructionClass P 𝓤 := fun q =>
  Quotient.liftOn' q (fun z : cocycles 𝓤.U 2 => classOf P 𝓤 (toOldCochain S 𝓤 (z : Cochain 𝓤.U 2)))
    (by
      intro z w hzw
      have hmem0 := (Submodule.quotientRel_def _).1 hzw
      have hmem : ((z : Cochain 𝓤.U 2) - (w : Cochain 𝓤.U 2)) ∈ coboundaries 𝓤.U 2 := by
        simpa using hmem0
      obtain ⟨a, ha⟩ := hmem
      have hz : (z : Cochain 𝓤.U 2) = (w : Cochain 𝓤.U 2) + d 𝓤.U 1 a := by
        rw [ha]; abel
      exact ((classOf_eq_iff _ _).2
        (cohomologous_toOldCochain S (w : Cochain 𝓤.U 2) (z : Cochain 𝓤.U 2) a hz)).symm)

@[simp] theorem toObstruction_mk (S : KernelSign P) (z : cocycles 𝓤.U 2) :
    toObstruction S 𝓤 (mk z) = classOf P 𝓤 (toOldCochain S 𝓤 (z : Cochain 𝓤.U 2)) := rfl

/-- The zero class goes to the trivial Task-3 class. -/
theorem toObstruction_zero (S : KernelSign P) :
    toObstruction S 𝓤 (0 : H2 𝓤.U) = trivialClass P 𝓤 := by
  show classOf P 𝓤 (toOldCochain S 𝓤 (0 : Cochain 𝓤.U 2)) = trivialClass P 𝓤
  refine (classOf_eq_iff _ _).2 ⟨one₁, isKerCochain₁_one, fun i j k x hx => ?_⟩
  rw [toOldCochain_apply_of_mem S (0 : Cochain 𝓤.U 2) i j k hx x]
  show (1 : L) = _
  rw [show (0 : Cochain 𝓤.U 2) (nerve₂ 𝓤 i j k ⟨x, hx⟩) = 0 from rfl, S.ofZ_zero]
  simp [delta₁, one₁]

/-- **WP9, principal endpoint.**  The canonical map carries the Task-6 Spin-lift Čech class to
the Task-3 Spin-lift obstruction class: the two are the same obstruction in two carriers. -/
theorem toObstruction_spinCechClass (S : KernelSign P) {D : SpinLiftFamily P T}
    (V : ConstOn₃ 𝓤 D.defect) :
    toObstruction S 𝓤 (spinCechClass S V) = D.obstruction := by
  show classOf P 𝓤 (toOldCochain S 𝓤 (zCochain S V)) = classOf P 𝓤 D.defect
  refine (classOf_eq_iff _ _).2 ⟨one₁, isKerCochain₁_one, fun i j k x hx => ?_⟩
  rw [toOldCochain_apply_of_mem S (zCochain S V) i j k hx x]
  have hval : zCochain S V (nerve₂ 𝓤 i j k ⟨x, hx⟩) = S.sgn (V.val i j k) := rfl
  rw [hval, S.ofZ_sgn (V.val_mem_ker i j k hx), ← V.spec i j k x hx]
  simp [delta₁, one₁]

/-! ## WP9 — injectivity on covers with preconnected double overlaps -/

/-- **WP9, principal endpoint.**  If every double overlap of the cover is preconnected then the
canonical map `Ȟ²(𝓤;ℤ₂) → ObstructionClass P 𝓤` is injective: genuine fixed-cover Čech
cohomology embeds canonically into the Task-3 quotient.

Preconnectedness is exactly what is needed and is used exactly once: a Task-3 `Cohomologous`
witness `ε` is only continuous and kernel-valued, hence merely *locally* constant; on
preconnected double overlaps it is constant and therefore is the image of a genuine Čech
1-cochain. -/
theorem toObstruction_injective (S : KernelSign P)
    (hpre : ∀ i j, IsPreconnected (𝓤.overlap₂ i j)) :
    Function.Injective (toObstruction S 𝓤) := by
  intro q q' hq
  obtain ⟨z, rfl⟩ := mk_surjective q
  obtain ⟨w, rfl⟩ := mk_surjective q'
  rw [toObstruction_mk, toObstruction_mk] at hq
  obtain ⟨ε, hε, hrel⟩ := (classOf_eq_iff _ _).1 hq
  have E : ConstOn₂ 𝓤 ε := ConstOn₂.ofPreconnected P hε hpre
  -- the Čech 1-cochain attached to the (now constant) comparison cochain
  refine (mk_eq_mk_iff z w).2 ⟨aCochain S E, ?_⟩
  funext σ
  obtain ⟨x, hx⟩ := nonempty₃ σ
  have hij : x ∈ 𝓤.overlap₂ (σ.idx 0) (σ.idx 1) := 𝓤.overlap₃_subset_ij _ _ _ hx
  have hjk : x ∈ 𝓤.overlap₂ (σ.idx 1) (σ.idx 2) := 𝓤.overlap₃_subset_jk _ _ _ hx
  have hik : x ∈ 𝓤.overlap₂ (σ.idx 0) (σ.idx 2) := 𝓤.overlap₃_subset_ik _ _ _ hx
  have mij : ε (σ.idx 0) (σ.idx 1) x ∈ P.Ker := (hε _ _).2 x hij
  have mjk : ε (σ.idx 1) (σ.idx 2) x ∈ P.Ker := (hε _ _).2 x hjk
  have mik : ε (σ.idx 0) (σ.idx 2) x ∈ P.Ker := (hε _ _).2 x hik
  have mz : toOldCochain S 𝓤 (z : Cochain 𝓤.U 2) (σ.idx 0) (σ.idx 1) (σ.idx 2) x ∈ P.Ker :=
    toOldCochain_mem_ker S _ _ _ _ hx x
  -- the Task-3 relation at `x`, transported through the sign dictionary
  have hsgn := congrArg S.sgn (hrel (σ.idx 0) (σ.idx 1) (σ.idx 2) x hx)
  rw [delta₁_apply,
    S.sgn_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ mij mjk) (Subgroup.inv_mem _ mik)) mz,
    S.sgn_mul (Subgroup.mul_mem _ mij mjk) (Subgroup.inv_mem _ mik), S.sgn_mul mij mjk,
    S.sgn_inv mik, sgn_toOldCochain S _ _ _ _ hx, sgn_toOldCochain S _ _ _ _ hx,
    E.spec _ _ x hij, E.spec _ _ x hjk, E.spec _ _ x hik] at hsgn
  -- rewrite both nerve simplices as `σ`
  have hself : nerve₂ 𝓤 (σ.idx 0) (σ.idx 1) (σ.idx 2) ⟨x, hx⟩ = σ := nerve₂_self σ ⟨x, hx⟩
  rw [hself] at hsgn
  have hd : d 𝓤.U 1 (aCochain S E) σ
      = S.sgn (E.val (σ.idx 1) (σ.idx 2)) + S.sgn (E.val (σ.idx 0) (σ.idx 2))
        + S.sgn (E.val (σ.idx 0) (σ.idx 1)) := by
    show (∑ t : Fin 3, aCochain S E (face t σ)) = _
    rw [Fin.sum_univ_three]
    rfl
  show d 𝓤.U 1 (aCochain S E) σ = ((z : Cochain 𝓤.U 2) - (w : Cochain 𝓤.U 2)) σ
  rw [hd, Cochain.sub_apply, hsgn]
  generalize S.sgn (E.val (σ.idx 0) (σ.idx 1)) = A
  generalize S.sgn (E.val (σ.idx 1) (σ.idx 2)) = B
  generalize S.sgn (E.val (σ.idx 0) (σ.idx 2)) = C
  generalize (z : Cochain 𝓤.U 2) σ = Z
  have key : ∀ A B C Z : ZMod 2, B + C + A = Z - (A + B + C + Z) := by decide
  exact key A B C Z

/-! ## WP9 — the image, and why the map is not surjective -/

/-- Every class in the image of the canonical map has a representative that is kernel-valued on
the overlaps. -/
theorem mem_ker_of_eq_toObstruction (S : KernelSign P) (q : H2 𝓤.U)
    (c : ι → ι → ι → (X → L)) (h : toObstruction S 𝓤 q = classOf P 𝓤 c) (i j k : ι) {x : X}
    (hx : x ∈ 𝓤.overlap₃ i j k) : c i j k x ∈ P.Ker := by
  obtain ⟨z, rfl⟩ := mk_surjective q
  rw [toObstruction_mk] at h
  obtain ⟨ε, hε, hrel⟩ := (classOf_eq_iff _ _).1 h
  have hij : x ∈ 𝓤.overlap₂ i j := 𝓤.overlap₃_subset_ij i j k hx
  have hjk : x ∈ 𝓤.overlap₂ j k := 𝓤.overlap₃_subset_jk i j k hx
  have hik : x ∈ 𝓤.overlap₂ i k := 𝓤.overlap₃_subset_ik i j k hx
  rw [hrel i j k x hx, delta₁_apply]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ((hε i j).2 x hij)
    ((hε j k).2 x hjk)) (Subgroup.inv_mem _ ((hε i k).2 x hik)))
    (toOldCochain_mem_ker S _ i j k hx x)

/-- **WP9, the exact mismatch.**  The Task-3 carrier is strictly larger: the class of a cochain
that takes a value *outside* the kernel on some nonempty triple overlap is not in the image of
the canonical map.  Hence `Ȟ²(𝓤;ℤ₂) ≅ ObstructionClass P 𝓤` is **false** in general, and
`EMBEDS_CANONICALLY` is the correct classification. -/
theorem classOf_not_mem_range_toObstruction (S : KernelSign P) {c : ι → ι → ι → (X → L)}
    {i j k : ι} {x : X} (hx : x ∈ 𝓤.overlap₃ i j k) (hout : c i j k x ∉ P.Ker) :
    ∀ q : H2 𝓤.U, toObstruction S 𝓤 q ≠ classOf P 𝓤 c := by
  intro q hq
  exact hout (mem_ker_of_eq_toObstruction S q c hq i j k hx)

/-! ## WP9 — the two vanishing statements agree -/

/-- **WP9, corollary.**  On a cover with preconnected double overlaps the Task-6 Čech class
vanishes exactly when the Task-3 obstruction class is trivial. -/
theorem spinCechClass_eq_zero_iff_obstruction_eq_trivial (S : KernelSign P)
    (hpre : ∀ i j, IsPreconnected (𝓤.overlap₂ i j)) {D : SpinLiftFamily P T}
    (V : ConstOn₃ 𝓤 D.defect) :
    spinCechClass S V = 0 ↔ D.obstruction = trivialClass P 𝓤 := by
  rw [spinCechClass_eq_zero_iff_exists_coherent S hpre V,
    ← D.obstruction_eq_trivialClass_iff_exists_coherent]

/-! ## WP11 — refinement naturality of the Spin Čech class -/

/-- The constancy datum of a defect pulls back along a refinement. -/
def ConstOn₃.pull (R : CoverRefinement 𝓥 𝓤) {D : SpinLiftFamily P T}
    (V : ConstOn₃ 𝓤 D.defect) : ConstOn₃ 𝓥 (D.pullLift R).defect where
  val a b c := V.val (R.r a) (R.r b) (R.r c)
  spec a b c x hx := V.spec _ _ _ x (R.overlap₃_le a b c hx)

/-- **WP11, principal endpoint — refinement naturality.**  `r*[z_𝓤] = [z_𝓥]`: the Čech class of
the refined lift family is the refinement pullback of the Čech class upstairs. -/
theorem Hmap_spinCechClass (S : KernelSign P) (R : CoverRefinement 𝓥 𝓤)
    {D : SpinLiftFamily P T} (V : ConstOn₃ 𝓤 D.defect) :
    Hmap R.le 2 (spinCechClass S V) = spinCechClass S (V.pull R) :=
  rfl

/-- **WP11.**  The refined class does not depend on which index map realises the refinement.
This is the Task-3 theorem `obstruction_pullLift_indep_of_map` transported through the
canonical embedding of WP9, so it needs the same preconnectedness hypothesis — on the refined
cover. -/
theorem spinCechClass_pull_indep_of_map (S : KernelSign P)
    (hpre : ∀ a b, IsPreconnected (𝓥.overlap₂ a b)) (R R' : CoverRefinement 𝓥 𝓤)
    {D : SpinLiftFamily P T} (V : ConstOn₃ 𝓤 D.defect) :
    spinCechClass S (V.pull R) = spinCechClass S (V.pull R') := by
  refine toObstruction_injective S hpre ?_
  rw [toObstruction_spinCechClass, toObstruction_spinCechClass]
  exact D.obstruction_pullLift_indep_of_map R R'

end CechSpinZ2
