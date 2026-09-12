import RequestProject.Spine.AlgebraicTopology.SimplicialSkeleton

/-!
# Task 14, WP3 : the simplicial skeletal cell-attachment theorem

The pinned Mathlib **does not** prove that `X.skeleton (n+1)` is obtained from `X.skeleton n`
by attaching `∂Δ[n] ⟶ Δ[n]` cells: it is listed verbatim as an open `TODO` at the top of
`Mathlib/AlgebraicTopology/SimplicialSet/Skeleton.lean`.  This module supplies the smallest
native theorem expressing exactly the required universal property.

## The decomposition (the mathematical heart)

`skelPiece_bijective` : for every `n`, the map

`(K^{(r-1)})_n  ⊕  (⨿_{σ ∈ NDeg_r X} { f : ⦋n⦌ ⟶ ⦋r⦌ // Epi f })  →  (K^{(r)})_n`

`inl x ↦ x`,   `inr (σ, f) ↦ σ · f`

is a **bijection**.  Under the Yoneda identifications `Δ[r]_n = (⦋n⦌ ⟶ ⦋r⦌)` and
`∂Δ[r]_n = {non-surjective maps}`, the right-hand summand is exactly `∐_σ (Δ[r]_n ∖ ∂Δ[r]_n)`,
so this *is* the degreewise pushout statement — pushouts of sets along a monomorphism being
disjoint unions with the complement.

The proof uses only pinned ingredients: `SSet.exists_nonDegenerate` and the Eilenberg–Zilber
uniqueness lemmas `SSet.unique_nonDegenerate_simplex` / `SSet.unique_nonDegenerate_map`, plus
`SSet.mem_skeleton_obj_iff_of_nonDegenerate`.

## The universal property

`AttachData X r Y` packages exactly the data of a map out of the pushout:

* a map `φ : K^{(r-1)} ⟶ Y`;
* for every nondegenerate `r`-simplex `σ` an `r`-simplex `y σ` of `Y` (i.e. a map
  `Δ[r] ⟶ Y`, by Yoneda);
* the agreement of the two on the boundary: for every **non-surjective** `h : ⦋n⦌ ⟶ ⦋r⦌`,
  `Y(h)(y σ) = φ(σ · h)` — the restriction of `y σ` along `∂Δ[r] ⟶ Δ[r]` is the composite
  `∂Δ[r] ⟶ K^{(r-1)} ⟶ Y` given by the canonical attaching map `σ · (−)`.

The attaching maps are **canonical**: they are `σ · (−)`, i.e. the Yoneda transposes of the
nondegenerate simplices themselves; nothing is chosen.

`attachExtend`, `attachExtend_comp_skInc`, `attachExtend_cell` and `attachExtend_unique` give
existence and uniqueness of the extension, i.e.

`K^{(r)} ≅ K^{(r-1)} ∪_{⨿ ∂Δ[r]} ⨿ Δ[r]`

in the form of the universal property, which is what WP3 asks for
("categorically or through an explicit universal property").
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet SpineTask13

universe u

namespace SpineTask14

variable {X : SSet.{u}} {r n : ℕ}

/-! ## Two facts about subcomplexes and nondegenerate simplices -/

/-- If `x` lies in a subcomplex and `x = y · f` with `f` an epimorphism, then `y` lies in the
subcomplex too (`f` is split epi). -/
theorem nonDeg_mem_of_mem {m : ℕ} (A : X.Subcomplex) (x : X _⦋n⦌) (hx : x ∈ A.obj (op ⦋n⦌))
    (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋m⦌) [Epi f] (y : X _⦋m⦌) (hy : x = X.map f.op y) :
    y ∈ A.obj (op ⦋m⦌) := by
  obtain ⟨⟨s⟩⟩ := isSplitEpi_of_epi f
  have h2 := A.map s.section_.op hx
  simp only [Set.mem_preimage] at h2
  rwa [hy, ← FunctorToTypes.map_comp_apply, ← op_comp, s.id, op_id,
    FunctorToTypes.map_id_apply] at h2

/-- A degeneracy of a nondegenerate `r`-simplex is **not** in the `r`-skeleton. -/
theorem notMem_skeleton_of_epi (σ : X.nonDegenerate r) (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋r⦌)
    [Epi f] : X.map f.op σ.1 ∉ (X.skeleton r).obj (op ⦋n⦌) := by
  intro h
  have hσ := nonDeg_mem_of_mem (X.skeleton r) _ h f σ.1 rfl
  exact absurd ((X.mem_skeleton_obj_iff_of_nonDegenerate σ r).1 hσ) (lt_irrefl r)

/-- Restricting a nondegenerate `r`-simplex along a **non-surjective** map lands in the
`r`-skeleton: this is the statement that the attaching map of the cell factors through
`K^{(r-1)}`. -/
theorem mem_skeleton_of_not_epi (σ : X.nonDegenerate r) (h : (⦋n⦌ : SimplexCategory) ⟶ ⦋r⦌)
    (hh : ¬ Epi h) : X.map h.op σ.1 ∈ (X.skeleton r).obj (op ⦋n⦌) := by
  cases r with
  | zero =>
      refine absurd ?_ hh
      rw [SimplexCategory.epi_iff_surjective]
      exact fun b => ⟨0, Subsingleton.elim (α := Fin 1) _ _⟩
  | succ s =>
      rw [SimplexCategory.epi_iff_surjective] at hh
      obtain ⟨i, θ, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective h hh
      have hmap : X.map (θ ≫ SimplexCategory.δ i).op σ.1
          = X.map θ.op (X.map (SimplexCategory.δ i).op σ.1) := by
        rw [op_comp, FunctorToTypes.map_comp_apply]
      rw [hmap]
      exact (X.skeleton (s + 1)).map θ.op
        (X.mem_skeleton (X.map (SimplexCategory.δ i).op σ.1) (Nat.lt_succ_self s))

/-! ## WP3, the degreewise decomposition -/

variable (X r n)

/-- The index set of the `r`-cells attached in dimension `n`: a nondegenerate `r`-simplex
together with a surjection `⦋n⦌ ↠ ⦋r⦌`, i.e. an `n`-simplex of `Δ[r]` **not** in `∂Δ[r]`. -/
abbrev CellIndex : Type u :=
  Σ _σ : X.nonDegenerate r, {f : (⦋n⦌ : SimplexCategory) ⟶ ⦋r⦌ // Epi f}

/-- The comparison map of the skeletal attachment square in dimension `n`. -/
def skelPiece :
    ((X.skeleton r).obj (op ⦋n⦌) ⊕ CellIndex X r n) → (X.skeleton (r + 1)).obj (op ⦋n⦌)
  | Sum.inl x => ⟨x.1, X.skeleton.monotone (Nat.le_succ r) _ x.2⟩
  | Sum.inr ⟨σ, f⟩ => ⟨X.map f.1.op σ.1,
      (X.skeleton (r + 1)).map f.1.op (X.mem_skeleton σ.1 (Nat.lt_succ_self r))⟩

/-- **WP3, the skeletal attachment theorem, degreewise form.**  In every dimension `n` the
`r`-skeleton is the disjoint union of the `(r-1)`-skeleton and one copy of the set of
surjections `⦋n⦌ ↠ ⦋r⦌` for each nondegenerate `r`-simplex.  This is exactly the pushout
square

`⨿_σ ∂Δ[r] → K^{(r-1)}`,  `⨿_σ Δ[r] → K^{(r)}`

evaluated in dimension `n`. -/
theorem skelPiece_bijective : Function.Bijective (skelPiece X r n) := by
  constructor
  · rintro (x | ⟨σ, ⟨f, hf⟩⟩) (y | ⟨τ, ⟨g, hg⟩⟩) h
    · exact congrArg Sum.inl (Subtype.ext
        (congrArg (fun z : ↑((X.skeleton (r + 1)).obj (op ⦋n⦌)) => (z : X _⦋n⦌)) h))
    · have hval : (x : X _⦋n⦌) = X.map g.op τ.1 :=
        congrArg (fun z : ↑((X.skeleton (r + 1)).obj (op ⦋n⦌)) => (z : X _⦋n⦌)) h
      exact absurd (hval ▸ x.2) (notMem_skeleton_of_epi τ g)
    · have hval : X.map f.op σ.1 = (y : X _⦋n⦌) :=
        congrArg (fun z : ↑((X.skeleton (r + 1)).obj (op ⦋n⦌)) => (z : X _⦋n⦌)) h
      exact absurd (hval ▸ y.2) (notMem_skeleton_of_epi σ f)
    · have hval : X.map f.op σ.1 = X.map g.op τ.1 :=
        congrArg (fun z : ↑((X.skeleton (r + 1)).obj (op ⦋n⦌)) => (z : X _⦋n⦌)) h
      have h1 : σ = τ := X.unique_nonDegenerate_simplex (X.map f.op σ.1) f σ rfl g τ hval
      subst h1
      have h2 : f = g := X.unique_nonDegenerate_map (X.map f.op σ.1) f σ rfl g σ hval
      subst h2
      rfl
  · intro x
    obtain ⟨m, f, hf, y, hy⟩ := X.exists_nonDegenerate x.1
    have hymem : y.1 ∈ (X.skeleton (r + 1)).obj (op ⦋m⦌) :=
      nonDeg_mem_of_mem _ x.1 x.2 f y.1 hy
    have hm : m < r + 1 := (X.mem_skeleton_obj_iff_of_nonDegenerate y (r + 1)).1 hymem
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hlt | heq
    · refine ⟨Sum.inl ⟨x.1, ?_⟩, Subtype.ext rfl⟩
      rw [hy]
      exact (X.skeleton r).map f.op ((X.mem_skeleton_obj_iff_of_nonDegenerate y r).2 hlt)
    · subst heq
      exact ⟨Sum.inr ⟨y, f, hf⟩, Subtype.ext hy.symm⟩

/-- The decomposition, as an equivalence. -/
def skelPieceEquiv :
    ((X.skeleton r).obj (op ⦋n⦌) ⊕ CellIndex X r n) ≃ (X.skeleton (r + 1)).obj (op ⦋n⦌) :=
  Equiv.ofBijective _ (skelPiece_bijective X r n)

/-! ## WP3, the universal property of the attachment -/

variable {X r}

/-- The canonical `r`-simplex of `K^{(r)}` determined by a nondegenerate `r`-simplex of `X`.
By Yoneda this is the canonical characteristic map `Δ[r] ⟶ K^{(r)}` of the cell; it is not a
choice. -/
def cellSimplex (σ : X.nonDegenerate r) : (X.skeleton (r + 1)).obj (op ⦋r⦌) :=
  ⟨σ.1, X.mem_skeleton σ.1 (Nat.lt_succ_self r)⟩

/-- **The data of a map out of the skeletal attachment.**  A map `φ` on the `(r-1)`-skeleton,
an `r`-simplex `cell σ` of `Y` for each nondegenerate `r`-simplex `σ` (equivalently, by Yoneda,
a map `Δ[r] ⟶ Y`), and the agreement of the two on `∂Δ[r]`, i.e. along every **non-surjective**
`h : ⦋n⦌ ⟶ ⦋r⦌`.  The attaching map used is the canonical one, `σ · (−)`. -/
structure AttachData (X : SSet.{u}) (r : ℕ) (Y : SSet.{u}) where
  /-- the map already defined on the `(r-1)`-skeleton -/
  base : Sk X r ⟶ Y
  /-- the `r`-simplex of `Y` attached to a nondegenerate `r`-simplex of `X` -/
  cell : X.nonDegenerate r → Y _⦋r⦌
  /-- the two agree on the boundary of the cell -/
  compat : ∀ {n : ℕ} (h : (⦋n⦌ : SimplexCategory) ⟶ ⦋r⦌) (hh : ¬ Epi h)
      (σ : X.nonDegenerate r),
    Y.map h.op (cell σ) = base.app (op ⦋n⦌) ⟨X.map h.op σ.1, mem_skeleton_of_not_epi σ h hh⟩

variable {Y : SSet.{u}}

/-- The underlying function of the extension, in dimension `n`. -/
def attachFun (D : AttachData X r Y) (n : ℕ) :
    (X.skeleton (r + 1)).obj (op ⦋n⦌) → Y _⦋n⦌ :=
  fun x => Sum.elim (fun a => D.base.app (op ⦋n⦌) a)
    (fun z => Y.map z.2.1.op (D.cell z.1)) ((skelPieceEquiv X r n).symm x)

theorem attachFun_inl (D : AttachData X r Y) (n : ℕ) (x : (X.skeleton (r + 1)).obj (op ⦋n⦌))
    (h : (x : X _⦋n⦌) ∈ (X.skeleton r).obj (op ⦋n⦌)) :
    attachFun D n x = D.base.app (op ⦋n⦌) ⟨x.1, h⟩ := by
  have hx : (skelPieceEquiv X r n).symm x = Sum.inl ⟨x.1, h⟩ :=
    (Equiv.symm_apply_eq _).2 (Subtype.ext rfl)
  rw [attachFun, hx]
  rfl

theorem attachFun_inr (D : AttachData X r Y) (n : ℕ) (x : (X.skeleton (r + 1)).obj (op ⦋n⦌))
    (σ : X.nonDegenerate r) (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋r⦌) (hf : Epi f)
    (hx : (x : X _⦋n⦌) = X.map f.op σ.1) :
    attachFun D n x = Y.map f.op (D.cell σ) := by
  have hx' : (skelPieceEquiv X r n).symm x = Sum.inr ⟨σ, f, hf⟩ :=
    (Equiv.symm_apply_eq _).2 (Subtype.ext hx)
  rw [attachFun, hx']
  rfl

/-- **WP3, existence.**  The extension of the attachment data to the `r`-skeleton. -/
def attachExtend (D : AttachData X r Y) : Sk X (r + 1) ⟶ Y where
  app m := attachFun D m.unop.len
  naturality := by
    rintro ⟨Δ⟩ ⟨Δ'⟩ g
    induction Δ using SimplexCategory.rec with | _ n =>
    induction Δ' using SimplexCategory.rec with | _ n' =>
    funext x
    show attachFun D n' ((Sk X (r + 1)).map g x) = Y.map g (attachFun D n x)
    by_cases hmem : (x : X _⦋n⦌) ∈ (X.skeleton r).obj (op ⦋n⦌)
    · have hmem' : X.map g x.1 ∈ (X.skeleton r).obj (op ⦋n'⦌) := (X.skeleton r).map g hmem
      rw [attachFun_inl D n' _ hmem', attachFun_inl D n x hmem]
      exact congrFun (D.base.naturality g) ⟨x.1, hmem⟩
    · obtain ⟨z, hz⟩ := (skelPiece_bijective X r n).2 x
      cases z with
      | inl a =>
          exact absurd ((congrArg (fun w : ↑((X.skeleton (r + 1)).obj (op ⦋n⦌)) =>
            (w : X _⦋n⦌)) hz) ▸ a.2) hmem
      | inr zz =>
          obtain ⟨σ, f, hf⟩ := zz
          have hx : (x : X _⦋n⦌) = X.map f.op σ.1 :=
            (congrArg (fun w : ↑((X.skeleton (r + 1)).obj (op ⦋n⦌)) => (w : X _⦋n⦌)) hz).symm
          have hgx : (((Sk X (r + 1)).map g x) : X _⦋n'⦌) = X.map (g.unop ≫ f).op σ.1 := by
            show X.map g x.1 = _
            rw [hx, op_comp, FunctorToTypes.map_comp_apply]
            rfl
          rw [attachFun_inr D n x σ f hf hx]
          by_cases hepi : Epi (g.unop ≫ f)
          · rw [attachFun_inr D n' _ σ (g.unop ≫ f) hepi hgx, op_comp,
              FunctorToTypes.map_comp_apply]
            rfl
          · rw [attachFun_inl D n' _ (hgx ▸ mem_skeleton_of_not_epi σ (g.unop ≫ f) hepi)]
            refine Eq.trans (congrArg (D.base.app (op ⦋n'⦌))
              (Subtype.ext hgx : (_ : ↑((X.skeleton r).obj (op ⦋n'⦌)))
                = ⟨X.map (g.unop ≫ f).op σ.1,
                    mem_skeleton_of_not_epi σ (g.unop ≫ f) hepi⟩)) ?_
            rw [← D.compat (g.unop ≫ f) hepi σ, op_comp, FunctorToTypes.map_comp_apply]
            rfl

/-- **WP3, the extension restricts to the given map on the `(r-1)`-skeleton.** -/
theorem attachExtend_comp_skInc (D : AttachData X r Y) :
    skInc X r ≫ attachExtend D = D.base := by
  ext m a
  obtain ⟨Δ⟩ := m
  induction Δ using SimplexCategory.rec with | _ n =>
  exact attachFun_inl D n _ a.2

/-- **WP3, the extension realises the prescribed cell on each nondegenerate `r`-simplex.** -/
theorem attachExtend_cell (D : AttachData X r Y) (σ : X.nonDegenerate r) :
    (attachExtend D).app (op ⦋r⦌) (cellSimplex σ) = D.cell σ := by
  refine Eq.trans (attachFun_inr D r _ σ (𝟙 _) inferInstance ?_) ?_
  · simp [cellSimplex]
  · rw [op_id, FunctorToTypes.map_id_apply]

/-- **WP3, uniqueness.**  A map out of the `r`-skeleton is determined by its restriction to the
`(r-1)`-skeleton together with its values on the nondegenerate `r`-simplices.  Together with
`attachExtend` this is exactly the universal property of the pushout

`K^{(r)} = K^{(r-1)} ∪_{⨿ ∂Δ[r]} ⨿ Δ[r]`. -/
theorem attachExtend_unique (D : AttachData X r Y) (ψ : Sk X (r + 1) ⟶ Y)
    (h₁ : skInc X r ≫ ψ = D.base)
    (h₂ : ∀ σ : X.nonDegenerate r, ψ.app (op ⦋r⦌) (cellSimplex σ) = D.cell σ) :
    ψ = attachExtend D := by
  ext m x
  obtain ⟨Δ⟩ := m
  induction Δ using SimplexCategory.rec with | _ n =>
  show ψ.app (op ⦋n⦌) x = attachFun D n x
  obtain ⟨z, hz⟩ := (skelPiece_bijective X r n).2 x
  cases z with
  | inl a =>
      have hmem : (x : X _⦋n⦌) ∈ (X.skeleton r).obj (op ⦋n⦌) :=
        (congrArg (fun w : ↑((X.skeleton (r + 1)).obj (op ⦋n⦌)) => (w : X _⦋n⦌)) hz) ▸ a.2
      rw [attachFun_inl D n x hmem, ← h₁]
      rfl
  | inr zz =>
      obtain ⟨σ, f, hf⟩ := zz
      have hx : (x : X _⦋n⦌) = X.map f.op σ.1 :=
        (congrArg (fun w : ↑((X.skeleton (r + 1)).obj (op ⦋n⦌)) => (w : X _⦋n⦌)) hz).symm
      have hxeq : x = (Sk X (r + 1)).map f.op (cellSimplex σ) := Subtype.ext hx
      rw [attachFun_inr D n x σ f hf hx, hxeq, ← h₂ σ]
      exact congrFun (ψ.naturality f.op) _

end SpineTask14
