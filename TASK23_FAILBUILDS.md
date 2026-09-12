# TASK 23 FAILBUILDS — every failed attempt, its diagnosis and its repair

Format: module / declaration, exact error (abridged to its first line where long), diagnosis,
repair, and whether the *statement* changed.  Statement changes are flagged explicitly; there
was exactly one (§10), and it is a correction of a false intermediate claim, not a weakening of
a target.

---

## 1. `Task23PuncturedCell.baryPt`

* Error: `failed to prove positivity/nonnegativity/nonzeroness`.
* Diagnosis: `positivity` was called on `0 ≤ bary r i` with `bary` still folded, so the goal was
  not syntactically an arithmetic expression.
* Repair: `simp only [bary]; positivity`.
* Statement unchanged.

## 2. `Task23PuncturedCell.sum_sub_bary`

* Error: `unsolved goals … ⊢ 1 - (↑r + 1) * (↑r + 1)⁻¹ = 0`, and a type mismatch on
  `Finset.sum_sub_distrib`.
* Diagnosis: the pointwise/`Pi` form of the sum was fighting the subtype coercion; and the final
  arithmetic identity needed `field_simp`.
* Repair: extracted `sum_bary : ∑ i, bary r i = 1` and stated `sum_sub_bary` in pointwise form
  `∑ i, (x i - bary r i) = 0`.
* Statement of the *lemma* changed (pointwise form); no target statement affected.

## 3. `Task23PuncturedCell.gaugeAt_le_one`

* Error: `linarith failed to find a contradiction … this : 0 ≤ ↑x i … a✝ : (↑r + 1)⁻¹ < …`.
* Diagnosis: `↑x i` (`Subtype.val` applied, then evaluated) and `x i` (the `CoeFun` on the
  subtype of `stdSimplex`) are definitionally equal but *syntactically distinct atoms*, so
  `linarith` saw two unrelated terms.  This coercion clash recurred throughout the module.
* Repair: force one spelling with an explicit `show`/`have` of the form
  `have hxi : (0 : ℝ) ≤ (x : Fin (r+1) → ℝ) i := x.2.1 i`.
* Statement unchanged.

## 4. `Task23PuncturedCell.gauge_radialFun_le_one`

* Error: `rewrite failed … 1 * ?a`.
* Diagnosis: `inv_mul_le_iff₀` produces `… ≤ denom * 1`, not `1 * …`.
* Repair: `mul_one` instead of `one_mul`.
* Statement unchanged.

## 5. `Task23PuncturedCell.continuous_radialFun_pair`

* Error: ``fun_prop was unable to prove `Continuous ?m```.
* Diagnosis: `fun_prop` cannot see through the pair `(↑p.1, ↑p.2)` into `I × ↥(puncturedLocus)`.
* Repair: explicit `(continuous_subtype_val.comp continuous_fst).prodMk (…)`.
* Statement unchanged.

## 6. `Task23PuncturedCell` — realized transport

* Error: `unexpected token 'σ'; expected '_' or identifier` (in the *first* draft of
  `Task23PushoutRetraction`), and `unsolved goals ⊢ baryPt r ∈ {baryPt r}`.
* Diagnosis: (i) `open unitInterval` installs the notation `σ` for the interval symmetry, which
  collides with `σ` used as a cell index; (ii) `Set.mem_singleton_iff` is not applied by `rw`
  when the membership is the goal.
* Repair: (i) do not `open unitInterval` in modules that use `σ`-style names — the interval is
  written `unitInterval` there; index variables were renamed to `s`; (ii) finish with `exact rfl`.
* Statement unchanged.

## 7. `Task23SkeletonTopology` — `Sk`, `skInc` unknown

* Error: ``Function expected at `skInc` … The identifier `skInc` is unknown``.
* Diagnosis: `Sk`/`skInc` live in `SpineTask13`, which was not opened.
* Repair: added `SpineTask13` to the `open` list.
* Statement unchanged.

## 8. `Task23SkeletonTopology` — `obtain rfl` clearing the wrong variable

* Error: ``Unknown identifier `s` `` after `obtain rfl : t = s`.
* Diagnosis: `subst` eliminated the *section* variable rather than the freshly introduced one,
  so later occurrences of the section variable no longer existed.
* Repair: either name the equation and `subst` it explicitly in the safe direction, or replace
  the later occurrences by `_`.
* Statement unchanged.

## 9. `Task23PushoutRetraction.continuous_totMap`

* Errors: ``Tactic `apply` failed … Continuous (Sum.elim ?f ?g)`` and, later,
  `typeclass instance problem is stuck: TopologicalSpace ?m`.
* Diagnosis: (i) `Continuous.sumElim` only matches a function *syntactically* of the form
  `Sum.elim f g`, not one defined by pattern matching; (ii) the helper lemmas
  `continuous_prod_sum` / `continuous_prod_sigma` had all types in a single universe `Type u`,
  but the interval factor lives in `Type 0`.
* Repair: define `totMap` with `Sum.elim`; make the helper lemmas `Type*`-polymorphic; supply
  `(C := fun _ => ↥(puncturedCell r))` explicitly at the application.
* Statement unchanged.

## 10. `Task23PushoutRetraction.homTot_wd` — **a false intermediate claim**

* Error: ``Tactic `rfl` failed: homTot X r (t, Sum.inr ⟨s, c⟩) is not definitionally equal to
  totMap X r (Sum.inr ⟨s, c⟩)``.
* Diagnosis: the first draft proved well-definedness through the auxiliary claim
  *“if `totMap v = totMap v'` then `homTot (t, v) = totMap v`”*, which is **false**: for an
  interior cell point identified only with itself, the homotopy genuinely moves the point.
* Repair: the auxiliary claim was deleted and replaced by the correct one,
  `homTot_of_bdry` (*the homotopy is constant on boundary points*), and the case analysis of
  `homTot_wd` was redone from the pushout description of the identifications: two total points
  with the same image are either literally equal, or both boundary points — and in the latter
  case both homotopies are constant.
* **Statement changed**: the auxiliary lemma was replaced (the theorem `homTot_wd` itself is
  unchanged).

## 11. `Task23RelativeHomotopy` — Mathlib names

* Errors: ``Unknown constant `HomologicalComplex.quasiIsoAt_iff_isIso_homologyMap` ``,
  ``Unknown constant `HomologicalComplex.isZero_of_isZero_X` ``,
  ``failed to synthesize Subsingleton ↑(ModuleCat.of …)``.
* Diagnosis: at the production pin the first lemma is in the *root* namespace
  (`quasiIsoAt_iff_isIso_homologyMap`); there is no `isZero_of_isZero_X`; and
  `ModuleCat.isZero_of_subsingleton` takes the `Subsingleton` as an instance argument.
* Repair: use the root-namespace name; replace the second by
  `ShortComplex.isZero_homology_of_isZero_X₂ (K.sc q)`; provide the `Subsingleton` instance
  explicitly with `@ModuleCat.isZero_of_subsingleton _ _ _ hsub`.
* Statement unchanged.

## 12. `Task23RelativeHomotopy.isIso_homologyMap_skToV`

* Error: `(deterministic) timeout at isDefEq, maximum number of heartbeats (200000)`.
* Diagnosis: the implicit `TopCat` objects of `SpineTask19.isIso_homologyMap_of_homotopyEquiv`
  had to be recovered by unifying `↥?X` with `↥(SSet.toTop.obj (Sk X r))`, i.e. by inverting a
  coercion — the elaborator searched instead of matching.
* Repair: pass `(X := SSet.toTop.obj (Sk X r))` and `(Y := TopCat.of ↥(puncturedNbhd X r))`
  explicitly.
* Statement unchanged.

## 13. `Task23RelativeHomotopy` — `(𝟙 S).app`

* Error: ``Invalid field notation … 𝟙 S has type CategoryStruct.toQuiver.1 S S``.
* Diagnosis: dot notation cannot see the `NatTrans` structure through the categorical identity.
* Repair: `NatTrans.app (𝟙 S) n`.
* Statement unchanged.

---

## Rejected routes

Recorded as required, with the reason each was abandoned *before* it could broaden the task:

* **A general final-topology theorem for `SSet.toTop`.**  Rejected: unnecessary.  The pinned
  `TopCat.isOpen_iff_of_isColimit` / `TopCat.isClosed_iff_of_isColimit` apply directly to the
  Task-15 realized pushout; the Task-22 audit's claim that they are missing is wrong.
* **Proving `Y = |Sk X (r+1)|` Hausdorff (or the family locally finite) in order to see that the
  barycentre set is closed.**  Rejected: it would have required local finiteness of an arbitrary
  realization, which is explicitly out of scope.  Replaced by the componentwise preimage
  computation of §7 of the audit, which needs only Hausdorffness of the *standard cell* — a
  Task-17 theorem — and no finiteness at all.
* **Gluing the cellwise homotopies pointwise.**  Rejected: the joint continuity of the glued
  homotopy is exactly the delicate point.  Replaced by the explicit quotient presentation and
  the pinned `Topology.IsQuotientMap.continuous_lift_prod_right`.
* **Preservation of arbitrary coproducts by singular chains / an infinite wedge theorem.**  Never
  attempted; the only additivity statement the remaining gap needs is the *finite* disjoint-union
  theorem recorded in `TASK23_AUDIT.md` §18(1), and it is not assumed anywhere.
* **General CW machinery (cellular chain complexes, closure-finiteness).**  Never attempted.
