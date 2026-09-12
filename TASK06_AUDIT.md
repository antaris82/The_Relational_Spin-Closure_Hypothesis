# TASK06_AUDIT.md — native fixed-cover Čech `ℤ₂`-cohomology and the Spin-lift class

Task 6 closes the first half of the gap left by Tasks 3–5: the Spin-lift obstruction, which so
far lived only in a **custom fixed-cover quotient**, is now represented by a genuine class

```
[z] ∈ Ȟ²(𝓤;ℤ₂)
```

in a **standard, Spin-independent** fixed-cover Čech cohomology theory built natively inside the
Spine, and the relation between the two carriers is settled by theorem.

Everything below is machine-checked unless explicitly marked as an open dependency or as a
hypothesis. The build is green (`lake build` → 8174 jobs), with no `sorry`, no `admit`, no
project-local `axiom`, no `unsafe`, no `partial`, no `implemented_by`, and every principal new
declaration reports only `[propext, Classical.choice, Quot.sound]`.

---

## 0. Deliverable summary and classification

| # | deliverable | where | classification |
|---|---|---|---|
| 1 | native fixed-cover Čech `ℤ₂`-cochain complex (degrees `0,1,2,3`, in fact all `n`) | `RequestProject/Spine/Cech/Cochain.lean` | STANDARD_CECH / DERIVED_NATIVE |
| 2 | coboundary, agreement with the alternating formula, theorem `δ_Č² = 0` | `…/Cech/Coboundary.lean` | STANDARD_CECH / DERIVED_NATIVE |
| 3 | `Žⁿ`, `B̌ⁿ`, `B̌ⁿ ⊆ Žⁿ`, genuine quotient `Ȟⁿ(𝓤;ℤ₂)` (`Ȟ¹`, `Ȟ²`) | `…/Cech/Cohomology.lean` | STANDARD_CECH / DERIVED_NATIVE |
| 4 | kernel-sign dictionary `ker ρ ≅ ℤ₂` (data + `MulEquiv`), Spin instance | `…/Cech/KernelSign.lean`, `…/Cech/SpinKernelSign.lean` | DERIVED_NATIVE (reuses Task-4 `spinSign`) |
| 5 | translation of the Task-3 defect into a Čech 2-cocycle (`zCochain`, `d_zCochain`) | `…/Cech/SpinCocycle.lean` | REPRESENTATION_BRIDGE / DERIVED_NATIVE |
| 6 | change of lift = Čech coboundary (`zCochain_change_of_lift`) | `…/Cech/SpinCocycle.lean` | REPRESENTATION_BRIDGE |
| 7 | lift-choice-independent class `[z] ∈ Ȟ²(𝓤;ℤ₂)` | `…/Cech/SpinCocycle.lean`, `…/Cech/SpinInstance.lean` | DERIVED_NATIVE |
| 8 | vanishing iff coherent Spin lifts, in standard Čech language | `…/Cech/SpinCocycle.lean`; frame form in `…/Cech/SpinInstance.lean` | DERIVED_NATIVE |
| 9 | refinement naturality `r*[z_𝓤] = [z_𝓥]`, independence of the index map | `…/Cech/Refinement.lean`, `…/Cech/Comparison.lean` | REFINEMENT_NATURAL |
| 10 | comparison with the Task-3 `ObstructionClass`: canonical map, injectivity, non-surjectivity | `…/Cech/Comparison.lean` | **EMBEDS_CANONICALLY** |
| 11 | exact specification of the next bridge `Ȟ²(𝓤;ℤ₂) → H²_sing(X;ℤ₂)` | `…/Cech/SingularBridgeSpec.lean` | DEFERRED (specification only) |
| 12 | Task-5 documentation correction (module count) | `TASK05_AUDIT.md` | maintenance |
| 13 | corrected `gq2` provenance entry | `TASK05_EXTERNAL_SOURCES.md`, Entry D | maintenance, NEGATIVE_CONTROL |
| 14 | this audit | `TASK06_AUDIT.md` | — |
| 15 | external-source ledger update | §9 below, `TASK05_EXTERNAL_SOURCES.md` | NOT_REQUIRED (no external source consulted in Task 6) |
| 16 | failbuild ledger | §7 | — |
| 17 | build evidence | §8 | — |
| 18 | axiom audit | §8 | — |

Nothing is claimed about `w₂(TM)`, about `Ȟ²(X;ℤ₂)` (the direct limit) or about
`H²_sing(X;ℤ₂)`; see §10 and the Critical Hypothesis Boundary in §11.

---

## 1. WP1 — audit of the existing Task-3 Čech representation

### 1.1 The declarations, classified

| Task-3 declaration | file | classification |
|---|---|---|
| `CechCover`, `overlap₂/₃/₄`, `mem_overlap*`, `isOpen_overlap*`, `overlap*_subset_*` | `Spine/E2/Cech/Cover.lean` | STANDARD_CECH_DATA |
| `VisibleCocycle`, `g_self`, `g_symm`, `cocycle'` | `…/Cover.lean` | STANDARD_CECH_DATA (nonabelian degree-one cocycle) |
| `CoverRefinement`, `overlap₂/₃/₄_le`, `pullback`, `id`, `comp` | `…/Cover.lean` | REFINEMENT_DATA |
| `SpinLiftFamily`, `IsLiftAdmissible`, `nonempty_spinLiftFamily_iff`, `isLiftAdmissible_of_*` | `…/LocalLifts.lean` | SPECIALIZED_SPIN_LIFT_DATA |
| `defect`, `defect_apply`, `lift_mul_lift`, `proj_defect`, `defect_mem_ker`, `defect_isKerFunOn`, `defect_isLocallyConstant`, `defect_const_of_preconnected` | `…/Defect.lean` | SPECIALIZED_SPIN_LIFT_DATA |
| `defect_cocycle₂`, `defect_delta_eq_one` | `…/Defect.lean` | STANDARD_CECH_DATA *in multiplicative form* (the degree-two cocycle law) |
| `IsKerCochain₁/₂`, `delta₁`, `one₁`, `one₂`, `mul₁`, `inv₁`, `delta₁_mul`, `delta₁_inv`, `isKerCochain₂_delta₁` | `…/Coboundary.lean` | NONSTANDARD_ENCODING (multiplicative, *function-valued* cochains; only degrees 1→2) |
| `liftRatio`, `twist`, `defect_twist`, `defect_eq_delta₁_mul`, `defect_change_of_lift` | `…/Coboundary.lean` | SPECIALIZED_SPIN_LIFT_DATA (representative change) |
| `Cohomologous`, `cohomologous_refl/symm/trans/equivalence` | `…/Obstruction.lean` | QUOTIENT_EQUIVALENCE_DATA |
| `ObstructionClass`, `classOf`, `classOf_eq_iff`, `trivialClass`, `obstruction`, `obstruction_lift_independent` | `…/Obstruction.lean` | QUOTIENT_EQUIVALENCE_DATA + NONSTANDARD_ENCODING |
| `IsCoherent`, `isCoherent_iff_defect_one`, `obstruction_eq_trivialClass_iff_*`, `coherent_lift_projects` | `…/Obstruction.lean` | SPECIALIZED_SPIN_LIFT_DATA |
| `pullCochain₁/₂`, `isKerCochain₁_pull`, `delta₁_pull`, `cohomologous_pull`, `restrictClass`, `restrictClass_id/comp`, `pullLift`, `defect_pullLift`, `obstruction_pullLift*`, `conjLift`, `defect_conjLift` | `…/Refinement.lean` | REFINEMENT_DATA |
| `cech_defect_eq_pm_one`, `cech_defect_kernel_card`, `spinLiftObstruction` | `…/SpinInstance.lean` | SPECIALIZED_SPIN_LIFT_DATA |

### 1.2 Dependency DAG (Task-3 layer, unchanged by Task 6)

```
E2/Lift/RepresentativeChange
        │
        ▼
E2/Cech/Cover ──────────────► E2/Cech/LocalLifts ──► E2/Cech/Defect
   (CechCover, overlaps,          (SpinLiftFamily)        (defect, kernel-valuedness,
    VisibleCocycle,                                        local constancy, 2-cocycle law)
    CoverRefinement)                                            │
                                                                ▼
                                                       E2/Cech/Coboundary
                                                (IsKerCochain₁, delta₁, liftRatio, twist,
                                                 change-of-lift law)
                                                                │
                                                                ▼
                                                       E2/Cech/Obstruction
                                                (Cohomologous, ObstructionClass, vanishing)
                                                                │
                                                                ▼
                                                       E2/Cech/Refinement ──► E2/Cech/SpinInstance
                                                                                    │
                                                                                    ▼
                                                                            E2/Cech/Core
```

The Task-6 layer sits on top of this and on Mathlib; the Task-3 modules are **unmodified**.

```
Mathlib ──► Cech/Cochain ──► Cech/Coboundary ──► Cech/Cohomology ──► Cech/Refinement
                                                        │                    │
E2/Cech/Cover ──────────────────────────────────────────┴──► Cech/CoverNerve │
E2/CentralDoubleCover ──────────────────────────────────────► Cech/KernelSign│
Geometry/Z2Class ───────────────────────────────────────────► Cech/SpinKernelSign
E2/Cech/Core + CoverNerve + KernelSign ─────────────────────► Cech/SpinCocycle
                                                              │
                                                              ▼
                                                        Cech/Comparison ──► Cech/SpinInstance
                                                                                 │
                                              Cohomology/Core ───────────────────┴──► Cech/SingularBridgeSpec
                                                                                 │
                                                                                 ▼
                                                                            Cech/Core
```

### 1.3 Verdict: does Task 3 already contain a Čech complex?

**Partly, and not in a form that can be repackaged by renaming.** Precisely:

* it contains the *shape* of the degree-1 → degree-2 piece of a Čech complex (`delta₁`), the
  degree-2 cocycle law (`defect_delta_eq_one`) and the coboundary relation (`Cohomologous`);
* but the coefficients are **not constant**: a Task-3 cochain in degree `n` is a family of
  **functions `X → L`**, i.e. sections of the sheaf of continuous kernel-valued functions, not
  elements of a fixed abelian group;
* it is **multiplicative**, with the kernel written as `{±1} ⊆ L` rather than as `ℤ₂`;
* the ambient cochain group of the quotient is **all `L`-valued** cochains — no kernel
  condition and no cocycle condition — so `ObstructionClass` is a quotient of the form
  `C²/im δ`, not `Ž²/B̌²`;
* there is **no** `δ⁰`, no `δ²` in the Čech direction, no degree-3 group, and hence no
  statement `δ² = 0` to inherit;
* only nonempty overlaps *matter*, but the encoding does not restrict to them.

Consequently Task 6 builds the standard complex from scratch (WP2–WP4, on Mathlib alone) and
links the two by a proved canonical map (WP9). **No functioning Task-3 infrastructure was
rewritten, removed or weakened**; every Task-3 declaration is still present and still green.

---

## 2. WP2–WP4 — the native Čech complex (Spin-independent)

* `CechZ2.inter U σ = ⋂ s, U (σ s)`, `CechZ2.Nerve U n = {σ : Fin (n+1) → ι // (inter U σ).Nonempty}`,
  `CechZ2.face` (delete a position, `Fin.succAbove`), with the theorem that a face of a nerve
  simplex is again one (nonemptiness is inherited, `inter_subset_comp`).
* `CechZ2.Cochain U n = Nerve U n → ZMod 2` — a genuine function type; `AddCommGroup` and
  `Module (ZMod 2)` are the derived `Pi` instances. Degrees `0,1,2,3` are instances of the
  generic definition; explicit nerve constructors `pair`, `triple`, `quad` are provided.
* `CechZ2.coboundary`/`CechZ2.d` — the plain sum over faces, **with**
  `CechZ2.coboundary_eq_alternating` proving that this *is* the conventional alternating sum
  `∑ (-1)^t c(… î_t …)` (the signs are `1` because `-1 = 1` in `ZMod 2`). The relation to the
  conventional formula is thus documented *by theorem*, not by comment.
* `CechZ2.coboundary_coboundary` / `d_comp_d` / `d_d` — **`δ_Č² = 0`**, proved from the
  `Fin.succAbove` simplicial identity `CechZ2.succAbove_comm`: the double sum over
  `Fin (n+3) × Fin (n+2)` is split into two halves in bijection carrying equal terms, and
  `x + x = 0` in `ZMod 2`. No Spin input; the module imports Mathlib only.
* `CechZ2.cocycles`, `coboundaries` (`B̌⁰ = 0`), `coboundaries_le_cocycles` (a theorem, from
  `δ² = 0`), `coboundariesIn`, and `CechZ2.Cohomology U n = Žⁿ ⧸ B̌ⁿ` as an actual
  `Submodule.Quotient`, with `mk`, `classOf`, `mk_eq_mk_iff`, `mk_eq_zero_iff`,
  `mk_eq_zero_iff_exists`, `mk_surjective`; `H1`, `H2` are the two required instances.
* `CechZ2.nerveMap`, `pull`, `pull_d` (cochain map), `pullCocycles`, `CechZ2.Hmap`,
  `Hmap_id`, `Hmap_comp` — the refinement pullback with functoriality.

The firewall now enforces mechanically that `Cech.Cochain`, `Cech.Coboundary`,
`Cech.Cohomology` and `Cech.Refinement` reach **no** module of `Spine.E1`, `Spine.E2`,
`Spine.Geometry`, `Spine.Cohomology` or `Spine.Controls` (anti-shortcut 2: the Čech theory is
not defined in terms of the Spin obstruction).

**The cover model.** No new cover model was introduced. The complex is stated for the
underlying family `U : ι → Set X`, so a Task-3 cover is used as `𝓤.U`, and
`CechSpinZ2.inter_pair/inter_triple/inter_quad` prove that the nerve overlaps **are** the
Task-3 `overlap₂/₃/₄` as sets.

---

## 3. WP5 — the kernel `{±1}` written additively

`CechSpinZ2.KernelSign P` is the dictionary as *data*: `sgn`, `ofZ`, `ofZ_mem`, `sgn_ofZ`,
`ofZ_sgn`, `sgn_mul`. Derived: `sgn_one` (`+1 ↦ 0`), `ofZ_zero`, `sgn_inv` (inversion is
invisible in characteristic two), `sgn_injOn`, `sgn_eq_zero_iff`, and the packaged group
isomorphism `KernelSign.kerMulEquiv : P.Ker ≃* Multiplicative (ZMod 2)`.

The Spin instance `CechSpinZ2.spinKernelSign` **reuses** the Task-4 map
`LorentzFrames.spinSign` / `zToSpin` together with `spinSign_one`, `spinSign_negOneSpin`,
`spinSign_mul`; no second sign convention is introduced, and the three conventions demanded by
WP5 are stated explicitly (`spinKernelSign_one`, `spinKernelSign_negOneSpin`,
`spinKernelSign_mul`). Multiplicative statements are never silently read as additive: every
passage goes through `sgn_mul`.

---

## 4. WP6–WP8, WP10 — the Spin defect in the new complex

### 4.1 The one extra hypothesis, stated honestly

A Task-3 defect `c_ijk : X → ker ρ` is a *function*; a constant-coefficient Čech cochain is one
value per overlap. The translation therefore needs constancy on overlaps. This is **not**
assumed silently: it is the datum `ConstOn₃ 𝓤 D.defect` (and `ConstOn₂` for 1-cochains), and it
is *constructed* from the Task-3 local-constancy theorem whenever the relevant overlaps are
preconnected (`ConstOn₃.ofPreconnectedDefect`, `ConstOn₂.ofPreconnected`).

Preconnected overlaps are **weaker than a good cover**: no contractibility, no acyclicity, no
higher-homotopy hypothesis is used anywhere, and the complex of §2 assumes nothing at all. The
hypothesis appears only in the theorems that need it, always as an explicit argument.

### 4.2 The results

* **WP6** `zCochain S V : Cochain 𝓤.U 2`, with `zCochain_apply` proving pointwise that its
  value is `sgn (c_ijk x)` for any `x` in the triple overlap, and `zCochain_indep_of_values`
  showing it does not depend on which constancy datum is used. The Task-3 defect is *consumed*,
  never redefined.
* **WP7** `d_zCochain : d 𝓤.U 2 (zCochain S V) = 0`. The proof takes a point `x` of the
  quadruple overlap, invokes the Task-3 multiplicative identity
  `c_jkl · c_ikl⁻¹ · c_ijl · c_ijk⁻¹ = 1` (`defect_delta_eq_one`) and applies `sgn`: `sgn_mul`
  turns the product into the sum, `sgn_inv` erases the two inverses, and the result is exactly
  the additive Čech coboundary `z(jkl) + z(ikl) + z(ijl) + z(ijk) = 0` on the four faces.
  This is a genuine translation, not a restatement: the additive identity is *derived* from the
  multiplicative one through the dictionary of §3.
* **WP8** `zCochain_change_of_lift : z' = z + δ_Č a`, where `a = aCochain S E` is the
  translation of the Task-3 comparison cochain `ε = g̃' g̃⁻¹`; hence
  `spinCechClass_lift_independent` and, under preconnected double overlaps,
  `spinCechClass_lift_independent_of_preconnected`.
* The class: `spinCechCocycle`, `spinCechClass`, `spinLiftCechClass` (intrinsic Spin),
  `frameCechClass` (Task-4 Lorentz frames).
* **WP10** `spinCechClass_eq_zero_iff_exists_coherent`:
  `[z] = 0 ∈ Ȟ²(𝓤;ℤ₂) ↔ ∃ coherent Spin lifts`, on covers with preconnected double overlaps.
  Forward: from `z = δ_Č a` the *constant* kernel-valued twist `kerCochainOf S 𝓤 a` makes the
  chosen lifts coherent (`isCoherent_twist_of_zCochain_eq_coboundary`). Backward: a coherent
  family has zero cochain, and the change-of-lift law exhibits `z` as a coboundary
  (`exists_coboundary_of_isCoherent`). The frame form is
  `frameCechClass_eq_zero_iff_spinStructure`: `[z]_frame = 0 ↔ a Spin structure exists`.
  The theorem consumes the **new** quotient; the Task-3 theorem is untouched and still green.

Anti-shortcut compliance: the class is not *defined* to be zero when coherent lifts exist — it
is defined as the class of a translated defect, and the equivalence is proved in both
directions.

---

## 5. WP9 — comparison with the Task-3 `ObstructionClass`

### 5.1 What each carrier contains

| | Task-3 `ObstructionClass P 𝓤` | Task-6 `Ȟ²(𝓤;ℤ₂)` |
|---|---|---|
| underlying objects | **all** families `c : ι → ι → ι → (X → L)` (no kernel condition, no cocycle condition, all triples including empty overlaps) | `ℤ₂`-valued functions on **nonempty** triple overlaps, **annihilated by `δ_Č`** |
| coefficients | functions into `L`, compared only on overlaps | the constant group `ℤ₂` |
| relation | `c' = (δε)·c` on overlaps, for `ε` continuous kernel-valued (only *locally* constant) | `z' - z ∈ im δ_Č`, for a genuine Čech 1-cochain |
| algebra | a bare `Quot` of a setoid | a `ZMod 2`-module quotient `Ž²/B̌²` |

### 5.2 What is proved

* `CechSpinZ2.toOldCochain` reads a `ℤ₂`-cocycle as the *constant* kernel-valued Task-3
  cochain with those signs; `cohomologous_toOldCochain` shows a Čech coboundary becomes a
  Task-3 `Cohomologous` change, so the construction descends:
  `CechSpinZ2.toObstruction : Ȟ²(𝓤;ℤ₂) → ObstructionClass P 𝓤` (a canonical map, with
  `toObstruction_zero`).
* `toObstruction_spinCechClass : toObstruction (spinCechClass S V) = D.obstruction` — **the two
  obstructions are the same obstruction in two carriers.**
* `toObstruction_injective` — on covers with **preconnected double overlaps** the canonical map
  is *injective*. Preconnectedness enters exactly once and unavoidably: a Task-3 witness `ε` is
  only continuous and kernel-valued, hence locally constant; on preconnected double overlaps it
  is constant, hence the image of a genuine Čech 1-cochain.
* `mem_ker_of_eq_toObstruction` and `classOf_not_mem_range_toObstruction` — the map is **not
  surjective in general**: every class in its image has a representative that is kernel-valued
  on overlaps, whereas the Task-3 carrier also contains classes of cochains taking values
  outside `ker ρ` on a nonempty triple overlap.
* `spinCechClass_eq_zero_iff_obstruction_eq_trivial` — the two vanishing statements agree
  (under the same preconnectedness hypothesis).

### 5.3 Classification, and the exact mismatch

**`EMBEDS_CANONICALLY`** — and *not* `DEFINITIONALLY_EQUAL`, *not* `CANONICALLY_EQUIVALENT`.

1. *What the old quotient contains:* arbitrary `L`-valued 2-cochains on all index triples,
   modulo multiplication by `δ` of a continuous kernel-valued 1-cochain, compared only on
   overlaps. It contains "junk" classes (non-kernel-valued cochains, values on empty overlaps
   which are invisible to the relation) and it imposes no cocycle condition.
2. *What standard Čech `H²` contains:* exactly the `ℤ₂`-cocycle classes on nonempty overlaps
   modulo genuine coboundaries — a `ZMod 2`-module.
3. *Canonical maps:* there is one in the direction `Ȟ²(𝓤;ℤ₂) → ObstructionClass P 𝓤`, and it
   is injective when the double overlaps are preconnected. There is **no** canonical map in the
   other direction: a general Task-3 cochain is neither kernel-valued nor constant on overlaps,
   so it has no `ℤ₂` value; and even for kernel-valued cochains a well-defined inverse would
   need local constancy plus connectedness of the overlaps.
4. *Does the vanishing theorem survive?* Yes, in both carriers, and the two statements are
   proved equivalent (§5.2, last item).
5. *Is a future migration of Task-3 data necessary?* Not for correctness — the embedding makes
   the Task-3 layer usable as is. It **is** advisable for the next tasks: the singular
   comparison (WP12) must consume `Ȟ²(𝓤;ℤ₂)`, since only that carrier is a `ℤ₂`-module with a
   cocycle/coboundary structure and refinement functoriality. Task-3 objects should from now on
   enter the certification branch **through** `toObstruction`/`spinCechClass`, not directly.

No representation mismatch is concealed: the non-surjectivity is itself a theorem.

---

## 6. WP11 — refinement, and WP12 — the next interface

**WP11.** `CechZ2.Hmap R.le 2 : Ȟ²(𝓤;ℤ₂) → Ȟ²(𝓥;ℤ₂)` is the pullback along a Task-3
`CoverRefinement` (whose fields `r`, `le` are exactly the data the generic construction needs);
`Hmap_id` and `Hmap_comp` are the functor laws. `ConstOn₃.pull` transports the constancy datum,
and `Hmap_spinCechClass : r*[z_𝓤] = [z_𝓥]` holds *definitionally* because the Task-3 defect of
the pulled-back lift family is the pullback of the defect on the nose. The previously proved
independence from the choice of refinement index map transfers cleanly:
`spinCechClass_pull_indep_of_map`, obtained from the Task-3 theorem
`obstruction_pullLift_indep_of_map` through the injective comparison of §5 (so it carries the
same preconnectedness hypothesis, on the refined cover).

**WP12.** `CechSingularSpec.Comparison X` names the exact missing map

```
Φ_𝓤 : Ȟ²(𝓤;ℤ₂) →ₗ[ℤ₂] H²_sing(X;ℤ₂),   natural in refinements,
```

as a hypothesis structure, together with the conditional consequences (`transport`,
`transport_eq_zero`, `transport_refinement`). **It is not constructed, it is not an axiom, and
nothing in the Spine consumes it.** The Task-5 provisional specification
(`Mod2Cohomology.ComparisonDatum`, which could only speak about the *old* quotient) is left in
place, untouched, as required.

Route audit (details in the module docstring):

* **Route A — good cover / nerve.** Needs small-simplices machinery for the Task-5 singular
  cochain complex: barycentric subdivision, the Lebesgue-number argument on a paracompact or
  metrisable base, and the small-chains theorem. Not in the pinned library for the mod-2
  singular cochains as constructed; each ingredient would have to be built natively. Under an
  acyclicity (good-cover) hypothesis the map becomes an isomorphism — that hypothesis is
  **not** assumed anywhere in Task 6.
* **Route B — direct limit.** `Ȟ*(X) = colim_𝓤 Ȟ*(𝓤)` is now possible in principle (the
  refinement functoriality exists), but taking the colimit is an explicit non-goal of Task 6,
  and it would still require a comparison theorem afterwards.
* **Route C — sheaf cohomology.** Mathlib has sheaf cohomology, but the identification of sheaf
  cohomology with *singular* cohomology on locally contractible spaces is absent, so this route
  is not materially shorter and would introduce a third carrier. Not pursued.

**Minimal next theorem (the answer to the last scientific question):** a `ℤ₂`-linear map
`Č²(𝓤;ℤ₂) → C²_sing(X;ℤ₂)` which sends Čech cocycles to singular cocycles and Čech coboundaries
to singular coboundaries — i.e. a cochain-level comparison in degree two. Everything else
(descent to classes, transport of `[z]`, refinement invariance) is already in place.

---

## 7. Failbuild ledger

Every failed elaboration during Task 6, with cause, repair and statement-change
classification. **No statement was weakened at any point** (`STATEMENT_UNCHANGED` throughout).

| # | command | diagnostic | cause | repair | statement change |
|---|---|---|---|---|---|
| 1 | `lake build` (`Cech/Cochain.lean`) | `Type mismatch` at the `Cochain` abbreviation, followed by `failed to synthesize` for the `Pi` module instances | the universe annotation `Type max w t` is wrong: `Nerve U n → ZMod 2` lives in `Type t` | annotate `Type t` | STATEMENT_UNCHANGED |
| 2 | `lake build` (`Cech/Refinement.lean`) | `Tactic 'rfl' failed` in `Hmap_id`, `Hmap_comp` | `ext z` leaves an element of a quotient, not a representative, so the goal is not definitional | `refine LinearMap.ext fun z => ?_; obtain ⟨z, rfl⟩ := mk_surjective z; rfl` | STATEMENT_UNCHANGED |
| 3 | `lake build` (`Cech/KernelSign.lean`) | `failed to synthesize instance` at `structure KernelSign (P : InternalProjection L G)` | `InternalProjection` requires `[IsTopologicalGroup L]`, missing from the `variable` line | add the instance binder | STATEMENT_UNCHANGED |
| 4 | `lake build` (`Cech/KernelSign.lean`) | `Unknown identifier self_eq_add_left.mp` | guessed a Mathlib lemma name that does not exist in the pinned version | replace by an explicit finite check `∀ x : ZMod 2, x = x + x → x = 0 := by decide` | STATEMENT_UNCHANGED |
| 5 | `lake build` (`Cech/SpinCocycle.lean`, first version) | `rewrite failed` at `dif_pos` in `ConstOn₂.ofPreconnected` / `ConstOn₃.ofPreconnectedDefect` | the goal displays the beta-reduced `dite`, so the pattern is not found | insert an explicit `show … = if h : … then … else …` before `rw [dif_pos …]` | STATEMENT_UNCHANGED |
| 6 | same | `motive is not type correct` in `spinCechClass_indep_of_values` | rewriting the cochain inside the dependent `cocycleOf` proof argument | prove it as `congrArg mk (Subtype.ext …)` instead | STATEMENT_UNCHANGED |
| 7 | same | several `rewrite failed` / type-mismatch errors around the face computations | `set i := σ.idx 0 …` blocks the definitional computation `(face t σ).idx s = σ.idx (t.succAbove s)` | drop `set`, keep `σ.idx k` explicit, and use `rfl`-level `have`s for the face values | STATEMENT_UNCHANGED |
| 8 | `lake build` (`Cech/SpinCocycle.lean`) | `failed to synthesize Decidable` in `kerCochainOf` | a `noncomputable def` still needs a `Decidable` instance for `dite` | `open scoped Classical in` before the definition, plus a dedicated `kerCochainOf_apply_of_mem` lemma so later proofs never re-open the `dite` | STATEMENT_UNCHANGED |
| 9 | same | `unexpected token 'open'; expected 'lemma'` | `open scoped Classical in` was placed *between* the docstring and the definition | move the `open … in` above the docstring | STATEMENT_UNCHANGED |
| 10 | `lake build` (`Cech/Comparison.lean`) | `Application type mismatch` at `(Submodule.quotientRel_def _).1 hzw` | the relation lives on the subtype `cocycles`, so the lemma yields membership of `z - w` in `coboundariesIn`, not the cochain-level statement | derive the cochain-level membership with `simpa` | STATEMENT_UNCHANGED |
| 11 | same | `rewrite failed` on `← E.spec …` | direction error: the hypothesis contains `ε … x`, so the rewrite must be forward, not backward | use `E.spec …` | STATEMENT_UNCHANGED |
| 12 | same | `rewrite failed` on `nerve₂_self` | the ambient goal carries the index `1 + 1`, not the literal `2`, so the pattern does not match syntactically | introduce the equation as a term `have hself := nerve₂_self σ ⟨x, hx⟩` (elaborated up to definitional equality) and rewrite with it | STATEMENT_UNCHANGED |
| 13 | same | contorted `decide` helper left an unsolved goal | over-general `key` lemma | `generalize` the four `ZMod 2` values and close with one `decide` identity | STATEMENT_UNCHANGED |
| 14 | `lake build` (`Cech/SpinInstance.lean`) | `Function expected at frameObstruction` (autoImplicit hint) | the Task-4 declaration lives in the `LorentzFrameData` namespace | qualify as `LorentzFrameData.frameObstruction` | STATEMENT_UNCHANGED |
| 15 | `lake build` (`Cech/SingularBridgeSpec.lean`) | `rewrite failed` on `← Hmap_spinCechClass` | the goal is stated through the `spinLiftCechClass` wrapper | `show` the unfolded form first | STATEMENT_UNCHANGED |

---

## 8. Build evidence and axiom audit

```
lake build RequestProject.Spine.E1.Core                    → OK
lake build RequestProject.Spine.E1.Topology.Core           → OK
lake build RequestProject.Spine.E2.Core                    → OK
lake build RequestProject.Spine.E2.Cech.Core               → OK
lake build RequestProject.Spine.Geometry.Core              → OK
lake build RequestProject.Spine.Cohomology.Core            → OK
lake build RequestProject.Spine.Cech.Cochain               → OK   (new Task-6 target)
lake build RequestProject.Spine.Cech.Coboundary            → OK   (new)
lake build RequestProject.Spine.Cech.Cohomology            → OK   (new)
lake build RequestProject.Spine.Cech.Refinement            → OK   (new)
lake build RequestProject.Spine.Cech.CoverNerve            → OK   (new)
lake build RequestProject.Spine.Cech.KernelSign            → OK   (new)
lake build RequestProject.Spine.Cech.SpinKernelSign        → OK   (new)
lake build RequestProject.Spine.Cech.SpinCocycle           → OK   (new)
lake build RequestProject.Spine.Cech.Comparison            → OK   (new)
lake build RequestProject.Spine.Cech.SpinInstance          → OK   (new)
lake build RequestProject.Spine.Cech.SingularBridgeSpec    → OK   (new)
lake build RequestProject.Spine.Cech.Core                  → OK   (new endpoint)
lake build RequestProject.Spine.Core                       → OK
lake build RequestProject.Spine.Audit.Firewall             → OK
lake build                                                 → Build completed successfully (8174 jobs).
```

Firewall output:

```
Spine external-project imports: 0 (prefixes checked: 7)
Spine modules audited: 144
Spine direct legacy imports:    Experiment1 = 0   Experiment2 = 0
Spine transitive legacy imports: Experiment1 = 0  Experiment2 = 0
SPINE FIREWALL AUDIT: all checks passed
```

Required isolation figures: **Experiment1 direct = 0, Experiment1 transitive = 0,
Experiment2 direct = 0, Experiment2 transitive = 0, external-project imports = 0.**

The firewall was extended for Task 6 with: endpoint reports for the twelve new modules; the
layering check that the Spin-independent half of the Čech layer reaches no `Spine.E1`,
`Spine.E2`, `Spine.Geometry`, `Spine.Cohomology` or `Spine.Controls` module; positive controls
that `Cech.SpinCocycle` *does* reach both `E2.Cech.Core` and `Cech.Cohomology`, that
`Cech.SpinInstance` reaches `Cech.SpinKernelSign` and that `Cech.SingularBridgeSpec` reaches
`Cohomology.Core`; and proof-closure audits for the eighteen principal new declarations.

Axiom audit (`RequestProject/Spine/Cech/Core.lean`, `#print axioms`): every principal
declaration reports `[propext, Classical.choice, Quot.sound]` (and `CechZ2.Cochain` reports no
axioms at all). Declarations audited: `Cochain`, `coboundary_eq_alternating`,
`coboundary_coboundary`, `d_comp_d`, `coboundaries_le_cocycles`, `Cohomology`,
`mk_eq_zero_iff`, `pull_d`, `Hmap`, `Hmap_id`, `Hmap_comp`, `KernelSign`, `kerMulEquiv`,
`spinKernelSign`, `zCochain`, `zCochain_apply`, `d_zCochain`, `spinCechClass`,
`zCochain_change_of_lift`, `spinCechClass_lift_independent`,
`spinCechClass_eq_zero_iff_exists_coherent`, `toObstruction`, `toObstruction_spinCechClass`,
`toObstruction_injective`, `classOf_not_mem_range_toObstruction`,
`spinCechClass_eq_zero_iff_obstruction_eq_trivial`, `Hmap_spinCechClass`,
`spinCechClass_pull_indep_of_map`, `spinLiftCechClass`,
`spinLiftCechClass_eq_zero_iff_exists_coherent`, `frameCechClass_eq_zero_iff_spinStructure`,
`CechSingularSpec.transport_refinement`.

Prohibited constructs: `rg` over `RequestProject/Spine/Cech/**` finds no `sorry`, no `admit`,
no `axiom`, no `unsafe`, no `partial`, no `implemented_by`.

---

## 9. External-source ledger for Task 6

**No external Lean project was consulted, inspected for technique, imported or copied while
doing the mathematical work of Task 6.** The Čech complex, the coboundary, `δ² = 0`, the
quotient, the refinement pullback and all bridge theorems were written from the standard
textbook definitions and from the Task-3/Task-5 material already in this repository. There is
therefore no new entry of type EXTERNALLY_INFORMED in this task.

The one external repository accessed during Task 6 was accessed **for the mandated provenance
correction only**, not for mathematics:

| field | value |
|---|---|
| repository | `https://github.com/roed314/gq2` |
| author | `roed314` (David Roe), with David Turturean (`CITATION.cff`) |
| commit inspected | `a2b1481f5e87acbb732b1e0fcf308a7ac2a9013a` (HEAD of `main`, 2026-09-01) |
| access date | 2026-09-08 |
| file consulted | `lean/gq2-claude/GQ2/StiefelWhitney.html` (generated documentation) |
| licence | no repository-level licence file at that commit (only vendored web-asset licences) |
| concept consulted | the *name* `StiefelWhitney` and the subject matter of that module |
| influence classification | **NEGATIVE_CONTROL**, NOT_USED — the module concerns Stiefel–Whitney/Hasse–Witt invariants `w₁, w₂` of binary quadratic forms in Galois cohomology, **not** tangent-bundle characteristic classes |

The Task-5 ledger has been corrected accordingly (`TASK05_EXTERNAL_SOURCES.md`, Entry D: wrong
path `roed-math/gq2-lean`, wrongly reported inaccessible). No external project is a dependency:
`lakefile.toml` requires Mathlib only, and the mechanical `auditNoExternal` check passes over
every Spine module.

---

## 10. Answers to the final scientific questions

**Q1. Is the native Spin-lift obstruction now represented by a genuine class
`[z] ∈ Ȟ²(𝓤;ℤ₂)` in a Spin-independent Čech cohomology theory?**

**Yes**, for a fixed cover, with one explicitly stated hypothesis. The carrier
`CechZ2.Cohomology 𝓤.U 2 = Ž²/B̌²` is built from Mathlib alone, is mechanically certified not to
depend on any Spin, lift or geometry module, and satisfies `δ_Č² = 0` and `B̌ⁿ ⊆ Žⁿ` as
theorems. The Spin defect is translated into it (`zCochain`), is a genuine cocycle
(`d_zCochain`), is well defined up to coboundary under change of lifts
(`zCochain_change_of_lift`), gives a lift-independent class (`spinCechClass_lift_independent`),
vanishes exactly when coherent Spin transition data exist
(`spinCechClass_eq_zero_iff_exists_coherent`, frame form
`frameCechClass_eq_zero_iff_spinStructure`) and is natural under refinement
(`Hmap_spinCechClass`). The hypothesis is that the defect (resp. the comparison cochain) is
constant on the relevant overlaps — automatic when those overlaps are preconnected. This is the
price of *constant* `ℤ₂` coefficients and it is carried in the statements, never hidden.

**Q2. Is the original Task-3 `ObstructionClass` definitionally equal, canonically equivalent, or
only related by a weaker bridge?**

Neither definitionally equal nor canonically equivalent: **`EMBEDS_CANONICALLY`**. There is a
canonical map `Ȟ²(𝓤;ℤ₂) → ObstructionClass P 𝓤` sending the new Spin class to the old one; it is
injective on covers with preconnected double overlaps, and it is provably **not** surjective in
general, because the old carrier also holds classes of cochains that are not kernel-valued on
overlaps. The old quotient is a `Quot` of *all* `L`-valued 2-cochains modulo locally-constant
kernel coboundaries; the new one is a `ℤ₂`-module `Ž²/B̌²`. Both vanishing criteria are proved
equivalent.

**Q3. What is the minimal next theorem required to transport this class into
`H²_sing(M;ℤ₂)`?**

A degree-two **cochain-level comparison for a fixed cover**: a `ℤ₂`-linear map
`Č²(𝓤;ℤ₂) → C²_sing(X;ℤ₂)` carrying Čech cocycles to singular cocycles and Čech coboundaries to
singular coboundaries (equivalently, the degree-two component of a cochain map). It descends
automatically to `Φ_𝓤 : Ȟ²(𝓤;ℤ₂) → H²_sing(X;ℤ₂)`, which is exactly the datum specified by
`CechSingularSpec.Comparison`; the transport of `[z]` and its refinement invariance are already
proved conditionally on it. Constructing that map requires subdivision machinery (Lebesgue
number / small simplices) for the Task-5 singular complex; making it an *isomorphism* requires
in addition an acyclicity (good-cover) hypothesis, which Task 6 deliberately does not assume.

---

## 11. Interpretation boundary (mandatory, unchanged)

`[z] ∈ Ȟ²(𝓤;ℤ₂)` is a **topological Spin-lift obstruction on a fixed open cover**. It is not
curvature, not torsion, not holonomy, not a synchronization mismatch, not matter/antimatter, not
a gravitational charge and not a dynamical state. Nothing in this task interprets it in terms of
the long-term hypothesis paper, and no dynamical closure is asserted anywhere.

Nor is any identification with `w₂(TM)` claimed. The certification DAG after Task 6 is

```
[z] ∈ Ȟ²(𝓤;ℤ₂)          (Task 6, done)
        ↓  Φ_𝓤            (specified, not constructed — Task 7+)
   H²_sing(X;ℤ₂)          (Task 5, done)
```

with the second branch (`TM ↦ w₂(TM)`) not yet started. Only when both branches live in the same
genuine carrier may equality even be *stated*.
