# TASK 35 — code hygiene report

Environment: Lean `v4.28.0`, Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

## 1. Prohibited constructs

Checked over the whole of `RequestProject/Spine` after the final green build
(`rg -n "sorry|admit|native_decide|unsafe|partial |implemented_by|^axiom "`):

| construct | occurrences in Task-35 modules | occurrences elsewhere in the Spine |
|---|---|---|
| `sorry`, `admit` | 0 | 0 |
| new `axiom` | 0 | 0 (the only matches of the word are prose in docstrings) |
| `native_decide`, `decide` | 0 | 0 in the Task-34/35 layer |
| `unsafe`, `implemented_by` | 0 | 0 |
| `partial` | 0 | 2 pre-existing, both in the *audit* meta-code `Spine/Audit/Firewall.lean` (import-graph traversal, not production mathematics); untouched by Task 35 |
| `Matrix.inv` | 0 | 0 |

No theorem was weakened to make a build pass; see `TASK35_FAILBUILDS.md`.

## 2. `simp` / `simpa` in the Task-35 production modules

Task-35 modules: `Spine/Solder/RegularSolder.lean`, `RegularExamples.lean`,
`BundleEquivalence.lean`, `SmoothMetric.lean`, `OrientationTime.lean`,
`WeakInsufficiency.lean`, `RegularGauge.lean`, `Spine/Comparison/SmoothSolderGate.lean`.

**Remaining `simp`/`simpa` tactic calls: none.**  The only occurrences of the token `simp` in
these files are `@[simp]` *attributes* on computation rules
(`localFrame_apply`, `BSclm_apply`, `act_A`, `proj_coreTotalMap`, `scaleEquiv_apply`), which are
declaration attributes, not proof automation.

The single tactic call that did exist, `RegularSolder.lean:391` — `by simp` discharging the side
condition `↑⊤ + 1 ≤ ↑⊤` of `ContDiffOn.fderivWithin` — was replaced during the Task-35 hygiene
pass by the structural term `le_of_eq ENat.coe_top_add_one` (failed build F11).

## 3. Other automation actually used in the Task-35 modules, and why

| tactic | sites | justification |
|---|---|---|
| `norm_num` | `SmoothMetric.lean:151,174`; `WeakInsufficiency.lean:223,242,256,272` | purely numeric closing steps on `ℝ` after the geometry has been reduced by `rw`/`show`: `1*1 - 0 = 1`, `1*0 - 0 = 0`, `2⁻¹*1*(2⁻¹*1) - 0 = 1/4`, and the two contradictions `(2 : ℝ) = 1`, `(1/4 : ℝ) = 1` obtained from uniqueness of limits.  None of them touches a geometric definition |
| `linarith` | `SmoothMetric.lean` (once, inside `metricCoeff_signature`); `Independence.lean` (once, after the Task-35 hygiene pass) | linear arithmetic over `ℝ` only |
| `ring` | `SmoothMetric.lean`, `Solder.lean` | commutative-ring normalisation of explicit real expressions |
| `filter_upwards` | `WeakInsufficiency.lean` | the standard idiom for an eventual equality on `𝓝[≠] 0`; no simp set involved |
| `open Classical in` | `RegularSolder.lean:294` (`weakFrame`), `WeakInsufficiency.lean:136` (`badFrameField`) | both define a function by a case split on an undecidable membership (`x ∈ B.chartRange i`, `x ≠ flatPoint`).  In both cases the *on-patch* value is immediately isolated as a rewriting lemma (`weakFrame_of_mem`, `badFrameField_of_ne`/`badFrameField_at`) so that no later proof ever unfolds the `dite`.  This is a definitional convenience, not a proof shortcut: no theorem's content depends on the choice made off the patch, and `#print axioms` shows only the standard `[propext, Classical.choice, Quot.sound]` |

## 4. Task-34 production-layer occurrences: what was removed, what remains

The task asked for removal of the Task-34 production-layer `simp`/`simpa` uses *where
practical*.  Removed (each replaced by an explicit structural proof, build re-verified):

| file | was | now |
|---|---|---|
| `Solder/Solder.lean` (`tangentMetric_nondegenerate`) | `simpa using fun h => hu (by simpa using …)` | `fun h => hu (by rw [← (E.tangentLinearEquiv x).apply_symm_apply u, h, map_zero])` |
| `Solder/Solder.lean` (`not_unique`) | `simpa using this` then `simp [SpinCore.sOne] at this` | `rw [← (E.frame i x₀).symm_apply_apply sOne, h4, map_zero]` then `exact one_ne_zero (congrArg Prod.fst h5)` |
| `Solder/Independence.lean` (`two_smul_sOne_ne_sOne`) | `simp [SpinCore.sOne] at this` | `congrArg Prod.fst h` + `rw [smul_eq_mul, mul_one]` + `one_ne_zero` |
| `Solder/Independence.lean` (independence endpoint) | `simpa using two_smul_sOne_ne_sOne` | `exact two_smul_sOne_ne_sOne` |

Remaining Task-34 occurrences, each recorded precisely with the reason it was kept:

| file:line | call | reason kept |
|---|---|---|
| `Solder/Solder.lean:84,86,87,89` | `simp only [BS_eq, sip, Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring` etc. | the four bilinearity fields of `BSbil`.  `simp only` with an explicit, closed rule list is used purely to push the coordinate projections through a `Prod`/`Pi` expression before `ring`; replacing it would mean writing out four long `rw` chains with no gain in trust (the rule list is fixed and contains no lemma about the geometry) |
| `Solder/Solder.lean:97` | `simp only [sip, Pi.neg_apply]; ring` | same pattern, negation of the spatial part |
| `Solder/LorentzBundle.lean:111` | `simpa using this` | unfolds the coercion of a product in `↥GLor` to the composition of the corresponding linear equivalences, inside `coordChange_comp`.  The pin offers no single `rw`-able lemma for the `MonoidHom`-image coercion chain at this position |
| `Solder/InternalLorentz.lean:142` | `simpa [projectedLorentzTransition] using this` | same coercion chain, in the cocycle law of the projected transition |
| `Solder/InternalLorentz.lean:153` | `simp only [projectedLorentzTransition, hv, Subgroup.coe_inv]` | explicit unfolding list only (definition + hypothesis + one coercion lemma); the mathematical step afterwards is the structural `symm_apply_apply` |
| `Solder/Independence.lean:77,84,87,99` | `cases i <;> cases j <;> simp [rescaleφ, smul_smul]` | finite case analysis over `Bool × Bool (× Bool)` for the concrete rescaling control; each branch is a scalar identity in `ℝ`.  This is control-example code, not part of any general statement |

## 5. Axiom audit

`#print axioms` is executed **in the source** at the end of every Task-35 module.  On the final
green build every Task-35 endpoint reports

```
[propext, Classical.choice, Quot.sound]
```

including in particular

```
SpinNative.SmoothTangentSolderData.smooth_solder_tangent_certificate
SpinNative.SmoothTangentSolderData.spin_endpoint_topological
SpinNative.smooth_solder_iff_regular_bundle_equivalence
SpinNative.SmoothTangentSolderData.smooth_tangent_lorentz_metric
SpinNative.weak_solder_not_regular
SpinNative.SmoothTangentSolderData.regular_solder_torsor
SpinNative.SmoothTangentSolderData.orientation_time_orientation_status
SpinNative.SmoothTangentSolderData.contDiffOn_solderLorentzRep
SpinNative.rescaleRegularSolder, SpinNative.rescale_const_id_not_solder
```
