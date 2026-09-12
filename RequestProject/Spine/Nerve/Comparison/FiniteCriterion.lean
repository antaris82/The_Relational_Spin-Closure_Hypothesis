import RequestProject.Spine.Nerve.Comparison.FamilyCompatibility

/-!
# Task 23, WP7 — the finite singular target decomposition (statement)

Task 22 introduced

```lean
def SpineTask22.SingularCellFamilyAdditivity (X : SSet.{u}) (r : ℕ) : Prop :=
  ∀ q, IsIso (tgtDecomp X r q)
```

*without* a finiteness hypothesis, while describing the intended downstream theorem as
finite-family only.  That documentation/type mismatch is recorded in `TASK23_AUDIT.md`; the
Task-22 definition is **not** modified here (it is a frozen interface).  Instead this module
adds the correctly named finite proposition

```lean
def SpineTask23.FiniteSingularCellFamilyAdditivity (X : SSet.{u}) (r : ℕ)
    [Fintype (X.nonDegenerate r)] : Prop := ∀ q, IsIso (tgtDecomp X r q)
```

which is the principal Task-23 target, stated with the exact existing `tgtDecomp`.

**Status: open.**  Task 23 established the whole geometric half of the argument — see
`Task23SkeletonTopology` (WP1), `Task23PuncturedCell` (WP2), `Task23PushoutRetraction` (WP3),
`Task23RelativeHomotopy` (WP4), `Task23Excision` (WP5) and `Task23StandardCellExcision` — so
that both

* `SpineTask23.cellPairIso  : H_q^{sing}(U, U ∩ V) ≅ H_q^{sing}(|Sk X (r+1)|, |Sk X r|)`, and
* `SpineTask23.stdCellIso   : H_q^{sing}(Δ°, Δ° \ {b_r}) ≅ H_q^{sing}(|Δ[r]|, |∂Δ[r]|)`

are available, where `U = |Sk X (r+1)| \ |Sk X r|` is the union of the open cells and
`V = |Sk X (r+1)| \ B` is the complement of the barycentres.  What is **not** available, and
what alone separates the two displayed isomorphisms from `FiniteSingularCellFamilyAdditivity`,
is recorded in `TASK23_AUDIT.md` §18:

1. the finite disjoint-union theorem
   `H_q^{sing}(∐_σ U_σ, ∐_σ W_σ) ≅ ⊕_σ H_q^{sing}(U_σ, W_σ)`, together with the identification
   of `(U, U ∩ V)` with the coproduct of the pairs `(Δ°_σ, Δ°_σ \ {b_σ})`;
2. the theorem that the resulting composite isomorphism *is* the existing `tgtDecomp`, i.e. that
   its `σ`-component is the map induced by the realized characteristic map `|cellChar X r σ|`.

No result of this project assumes either statement.
-/

noncomputable section

open CategoryTheory Simplicial SSet SpineTask22

universe u

namespace SpineTask23

/-- **The finite singular cell-family decomposition (open).**  The finite-family form of
`SpineTask22.SingularCellFamilyAdditivity`, stated with the *existing* comparison map
`SpineTask22.tgtDecomp` and with the finiteness hypothesis that Task 23 is scoped to.

It is stated here, and nowhere assumed. -/
def FiniteSingularCellFamilyAdditivity (X : SSet.{u}) (r : ℕ) [Fintype (X.nonDegenerate r)] :
    Prop :=
  ∀ q, IsIso (tgtDecomp X r q)

/-- The finite proposition is a special case of the Task-22 one: no strengthening is hidden in
the finiteness hypothesis. -/
theorem finiteSingularCellFamilyAdditivity_of_singularCellFamilyAdditivity
    (X : SSet.{u}) (r : ℕ) [Fintype (X.nonDegenerate r)]
    (h : SingularCellFamilyAdditivity X r) : FiniteSingularCellFamilyAdditivity X r := h

/-- **The finite-family `RelJIsIso` criterion.**  This is
`relJIsIso_of_singularCellFamilyAdditivity` rephrased for the finite proposition; it is a
conditional statement, its hypothesis being discharged in
`RequestProject.Spine.Nerve.Comparison.RelJ`. -/
theorem relJIsIso_of_finite (X : SSet.{u}) (r : ℕ) [Fintype (X.nonDegenerate r)]
    (h : FiniteSingularCellFamilyAdditivity X r) : SpineTask14.RelJIsIso X r :=
  relJIsIso_of_singularCellFamilyAdditivity X r h

end SpineTask23
