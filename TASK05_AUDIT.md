# TASK05_AUDIT.md — native mod-2 cohomology foundation and external-reference audit

Task 5 opens the **certification branch** whose eventual target is a genuine comparison of the
Task-3/Task-4 Lorentz-frame Spin-lift obstruction with the conventional Stiefel–Whitney class
`w₂(TM)`. Its job here is to close the *first* missing foundational dependency: a genuine
mod-2 singular cohomology theory `H*(X;ℤ₂)` inside the native Spine.

Everything below is machine-checked unless explicitly marked as an open dependency.
Provenance of the external references is in `TASK05_EXTERNAL_SOURCES.md` (mandatory reading
alongside this file).

---

## 0. Deliverable summary and classification

| # | deliverable | where | classification |
|---|---|---|---|
| 1 | singular mod-2 cochains `Cⁿ(X;ℤ₂)` | `RequestProject/Spine/Cohomology/Cochain.lean` | DERIVED_NATIVE / EXTERNALLY_INFORMED_INDEPENDENT_RECONSTRUCTION |
| 2 | coboundary `δ` and `δ² = 0` | `…/Coboundary.lean` | DERIVED_NATIVE / EXTERNALLY_INFORMED_INDEPENDENT_RECONSTRUCTION |
| 3 | `Zⁿ`, `Bⁿ`, `Bⁿ ⊆ Zⁿ`, quotient `Hⁿ(X;ℤ₂)` | `…/Cohomology.lean` | DERIVED_NATIVE |
| 4 | functorial pullback `f*` on cochains and on `Hⁿ`, functor laws | `…/Functorial.lean` | DERIVED_NATIVE (no external counterpart inspected) |
| 5 | Alexander–Whitney inclusions and coface identities | `…/AlexanderWhitney.lean` | DERIVED_NATIVE / EXTERNALLY_INFORMED_INDEPENDENT_RECONSTRUCTION |
| 6 | cup product on cochains, Leibniz rule | `…/Cup.lean` | DERIVED_NATIVE / EXTERNALLY_INFORMED_INDEPENDENT_RECONSTRUCTION |
| 7 | descended `H¹×H¹→H²`, `H²×H²→H⁴`, cup squares | `…/CupDescent.lean` | DERIVED_NATIVE |
| 8 | Čech-vs-singular type-gap analysis and bridge *specification* | `…/CechBridgeSpec.lean`, §WP8 | DEFERRED (bridge), DERIVED_NATIVE (conditional transport theorem) |
| 9 | Mathlib availability audit | §WP1 | MATHLIB_NATIVE / MISSING matrix |
| 10 | external-source ledger | `TASK05_EXTERNAL_SOURCES.md` | ATTRIBUTION_REQUIRED |
| 11 | native-vs-external architecture comparison | §WP7 | ATTRIBUTION_REQUIRED |
| 12 | future `w₂` route audit and dependency DAG | §WP9, §WP10 | DEFERRED / BLOCKED as marked |
| 13 | failbuild ledger, build evidence, axiom audit | §11, §12, §13 | — |

Explicit non-goals were respected: no Stiefel–Whitney theory, no `w₂(TM)`, no classifying
spaces, no Thom spaces, no Steenrod algebra, no Poincaré duality, no fundamental class, no
principal-bundle framework, no spin bundle total space, no soldering, no connection, curvature,
torsion, gravity, synchronization dynamics or CNNA coupling occurs in this task.

---

## WP1 — What the pinned Mathlib already supplies

Pinned environment: Lean `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0`
(`lake-manifest.json`). Every row was checked directly against the pinned sources
(`#check` / source search), not against documentation or memory.

| object | pinned Mathlib status | classification | consequence for Task 5 |
|---|---|---|---|
| `TopCat` | present | MATHLIB_NATIVE | reused as the ambient category |
| singular simplicial-set functor `TopCat.toSSet : TopCat ⥤ SSet` | present | MATHLIB_NATIVE | reused as the carrier of singular simplices — *not* reimplemented |
| `SSet`, `SimplexCategory`, cofaces `SimplexCategory.δ`, cosimplicial identity `δ_comp_δ` | present | MATHLIB_NATIVE | reused; `δ_comp_δ` is the sole input to `δ² = 0` |
| singular **chain** complex (`AlgebraicTopology.singularChainComplexFunctor`, `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`) | present | MATHLIB_PRIMITIVE_ONLY | *not* used: a chain complex of objects in an abstract additive category does not by itself supply mod-2 **cochains** with the concrete, pointwise carrier this task requires (WP2 forbids an opaque carrier), and dualising it into a usable cochain API is more work than the direct construction |
| chain/cochain complexes, `HomologicalComplex.homology` | present | MATHLIB_PRIMITIVE_ONLY | not used; the quotient `Zⁿ/Bⁿ` is built directly so that cocycles and coboundaries stay concrete and usable |
| `ZMod 2`, its field structure | present | MATHLIB_NATIVE | reused |
| `Submodule`, `Submodule.Quotient`, `Submodule.liftQ`, `Submodule.mapQ`, `LinearMap.ker/range` | present | MATHLIB_NATIVE | reused for `Zⁿ`, `Bⁿ`, `Hⁿ` and all descents |
| singular **cohomology** `Hⁿ(X;R)` of a topological space | **absent** | MISSING (EXTERNAL_ONLY: exists in the inspected external project A) | built natively in this task |
| cup product / Alexander–Whitney on singular cochains | **absent** | MISSING (EXTERNAL_ONLY) | built natively in this task |
| Čech cohomology of an open cover; nerve-based cohomology of spaces | **absent** (`CategoryTheory` has `cechNerve`, but no cohomology of a cover of a space) | MISSING | see WP8 |
| sheaf cohomology of a topological space | **absent** | MISSING | see WP8 |
| Stiefel–Whitney classes | **absent** (no declaration containing `StiefelWhitney`) | MISSING | see WP9 |
| Steenrod squares | **absent** | MISSING | out of scope |
| fundamental class of a manifold, Poincaré duality | **absent** (no `fundamentalClass`) | MISSING | see WP9 Route B |
| principal bundles | **absent** (no `PrincipalBundle`) | MISSING | out of scope by the Principal-Bundle Boundary rule |
| fibre bundles: `FiberBundle`, `FiberBundleCore`, vector bundles, trivializations | present | MATHLIB_NATIVE | not needed in Task 5; relevant to the separate soldering branch |
| paracompactness, partitions of unity, refinements | present (`ParacompactSpace`, `PartitionOfUnity`, shrinking lemmas) | MATHLIB_NATIVE | available, but **not** sufficient for a Čech-to-singular comparison — see WP8 |
| good covers / nerve theorem | **absent** | MISSING | see WP8 |

**Rule applied:** nothing already adequately supplied by Mathlib was recreated (the singular
simplicial set, the simplex category, the module and quotient machinery are all reused). And
the presence of a Mathlib *chain complex* was explicitly **not** treated as supplying the
desired cohomology theory.

---

## WP2 — Genuine singular `ℤ₂`-cochains  (`Cochain.lean`)

* `Mod2Cohomology.Simplex X n := (TopCat.toSSet.obj X).obj (op [n])` — Mathlib's singular
  `n`-simplices (continuous maps out of the topological `n`-simplex, in Mathlib's packaging).
* `Mod2Cohomology.reindex a σ` — the contravariant action of `a : [m] ⟶ [n]`, with
  `reindex_id` and `reindex_reindex` (functoriality).
* `Mod2Cohomology.face i σ` — the `i`-th face, i.e. `reindex` along `δ i`; `face_face`
  rewrites a double face as one reindexing along a composite of cofaces.
* `Mod2Cohomology.Cochain X n := Simplex X n → ZMod 2` — the mathematically direct definition
  `Cⁿ(X;ℤ₂) = Map(Sing_n X, ℤ₂)` requested by WP2.

The `AddCommGroup` and `Module (ZMod 2)` structures are the ones Mathlib derives for `Pi`
types; they are *derived*, never postulated. The carrier is a genuine function type: it is
**not** opaque, and no cohomology value is ever supplied as typeclass data.

## WP3 — Coboundary and `δ² = 0`  (`Coboundary.lean`)

`(δ f)(σ) = ∑_{i : Fin (n+2)} f (∂ᵢ σ)`, packaged as `Mod2Cohomology.d X n : Cⁿ →ₗ[ZMod 2] Cⁿ⁺¹`.

*Why the signs disappear, explicitly.* The integral coboundary is `∑ᵢ (-1)ⁱ f(∂ᵢσ)`. Over
`ZMod 2`, `-1 = 1`, so every sign is `1`. This is bookkeeping only: the cancellation in
`δ² = 0` does **not** come from signs. It comes from the cosimplicial identity

`SimplexCategory.δ_comp_δ : i ≤ j → δ i ≫ δ j.succ = δ j ≫ δ i.castSucc`  (the Mathlib lemma
used, as WP3 requires it to be documented),

which pairs the index set `Fin (n+3) × Fin (n+2)` of the double sum into two halves carrying
*equal* terms; the two halves then cancel because `x + x = 0` in `ZMod 2`. In the signed case
the same pairing is used and the paired terms have opposite signs.

Theorem-level results: `coboundary_coboundary` (pointwise) and `d_comp_d` (linear-map form).
The cochain-complex law is **proved, not postulated**.

## WP4 — Genuine cohomology  (`Cohomology.lean`)

* `cocycles X n = LinearMap.ker (d X n)` — `Zⁿ`;
* `coboundaries X n` — `Bⁿ`, defined by `B⁰ = ⊥` and `Bⁿ⁺¹ = LinearMap.range (d X n)`;
* `coboundaries_le_cocycles : Bⁿ ≤ Zⁿ` — a **theorem**, trivial in degree `0` and exactly
  `δ² = 0` in positive degree;
* `Cohomology X n := cocycles X n ⧸ coboundariesIn X n` — an actual `Submodule.Quotient`, with
  its derived `AddCommGroup` and `Module (ZMod 2)` instances, `mk`, `classOf`, `mk_eq_mk_iff`,
  `mk_eq_zero_iff`, `mk_surjective`, and `mk_injective_zero` in degree `0`.

The definition is degree-generic in `n : ℕ`, hence available in particular for
`n = 0,1,2,3,4`. `H²` is a genuine mathematical carrier: a quotient of the kernel of an
explicit linear map between explicit function spaces. It can host a future `w₂`.

## WP5 — Functoriality  (`Functorial.lean`)

For `f : X ⟶ Y` in `TopCat`:

* `simplexMap f n` — pushforward of singular simplices (the `n`-th component of
  `TopCat.toSSet.map f`), with `simplexMap_reindex` (naturality) and `simplexMap_face`;
* `pullback f n : Cⁿ(Y;ℤ₂) →ₗ Cⁿ(X;ℤ₂)`;
* `pullback_d : f*(δc) = δ(f*c)` — the chain-map property, a consequence of naturality of
  `TopCat.toSSet`; nothing is postulated;
* `cocyclesMap`, `pullback_mem_coboundaries`, and `Hmap f n : Hⁿ(Y;ℤ₂) →ₗ Hⁿ(X;ℤ₂)` via
  `Submodule.mapQ`;
* `Hmap_id : (𝟙 X)* = id` and `Hmap_comp : (f ≫ g)* = f* ∘ g*`.

## WP6 — Minimal cup product  (`AlexanderWhitney.lean`, `Cup.lean`, `CupDescent.lean`)

* four explicit monotone inclusions `frontIncl p q`, `backIncl p q`, `frontBig p q`,
  `backSmall p q`, and the six composition identities with the cofaces;
* `cup f g (τ) = f(front τ) · g(back τ)` with full bilinearity;
* **Leibniz rule** `coboundary_cup`:
  `δ(f ⌣ g)(τ) = (δf)(frontBig τ)·g(backSmall τ) + f(front τ)·(δg)(backBig τ)`,
  degree-generic, stated pointwise (necessarily: `(p+1)+q` and `(p+q)+1` are not
  definitionally equal in Lean, so the "obvious" degreewise formulation does not typecheck in
  general);
* `cup_cocycle` — cocycle ⌣ cocycle is a cocycle (any degrees);
* the four absorption lemmas `cup_delta_left_11`, `cup_delta_right_11`, `cup_delta_left_22`,
  `cup_delta_right_22`;
* the descended bilinear products
  `cupH11 : H¹ × H¹ → H²` and `cupH22 : H² × H² → H⁴`, and the cup squares
  `cupSquare1 : H¹ → H²`, `cupSquare2 : H² → H⁴`, plus the polarization identity
  `cupSquare2_expand`.

Deliberately **not** proved here (and not needed for this task's target): graded commutativity
of the cup product on cohomology, associativity, and any Steenrod operation beyond the top
square `x ↦ x ⌣ x`. Status: DEFERRED. In particular `cupSquare2` is the top square `Sq²` in
its degree — enough for the Wu-class route in dimension four to be *stated* later — but the
identification with a general Steenrod square is not claimed.

---

## WP7 — Native vs. external architecture (reference A, no code copied)

Compared against `NetRxn/SK_EFT_Hawking`, file `lean/SKEFTHawking/SingularCohomologyMod2.lean`,
commit `e7abc5d944bf7350d6de14de5ec8cb26c66e7f74`, inspected 2026-09-08 (see
`TASK05_EXTERNAL_SOURCES.md`, entry A).

| Topic | Native Spine construction | External construction | Same mathematical idea? | Same Lean representation? | External influence |
|---|---|---|---|---|---|
| singular simplex representation | `Simplex X n = (TopCat.toSSet.obj X).obj (op [n])`, plus a named `reindex` operation with functoriality lemmas | value of `TopCat.toSSet.obj X` at `op [n]`, used inline; no named reindexing | yes | essentially yes (native adds the named `reindex` API) | yes — the choice of `TopCat.toSSet` as carrier was confirmed there |
| cochain carrier | `Cochain X n = Simplex X n → ZMod 2` (`abbrev`) | `SingularCochain X n` (`abbrev`), same type | yes | yes | yes (convergent; standard definition) |
| face map | `face i σ = reindex (δ i) σ`; `face_face` via `reindex_reindex` | `face i σ` = `map (δ i).op σ`; `face_face` proved inline | yes | yes | yes |
| coboundary | `coboundary`, then `d` as a `ZMod 2`-linear map; explicit documentation of why signs vanish | `coboundary`, then `coboundaryₗ` | yes | yes | yes |
| proof of `δ² = 0` | index set `Fin(n+3)×Fin(n+2)` split with `Finset.sum_filter_add_sum_filter_not`, halves matched by `Finset.sum_bij'` using `δ_comp_δ`, closed by `x+x=0` | same index set, single `Finset.sum_involution` with an `if … then (b.castSucc, a.pred) else (b.succ, a.castPred)` involution, same `δ_comp_δ` | **yes — same mathematical mechanism** | no (bijection between two halves vs. involution on the whole set) | yes — the mathematical mechanism was seen there first |
| cocycles | `cocycles = LinearMap.ker (d X n)` | `LinearMap.ker (coboundaryₗ X n)` used directly | yes | yes | yes |
| coboundaries | `coboundaries` with `B⁰ = ⊥`, `Bⁿ⁺¹ = range δ`, and the theorem `Bⁿ ≤ Zⁿ` | `coboundaryRange` + `coboundaryRange_le_ker` | yes | close (native makes the degree-0 convention explicit in the definition) | yes |
| quotient | `Cohomology X n = cocycles ⧸ (coboundariesIn)` where `coboundariesIn` is the comap along `Zⁿ ↪ Cⁿ` | `Cohomology X n` as a quotient of `ker` by the mapped range | yes | close, different bookkeeping of "`B` inside `Z`" | yes |
| cup product | `cup` from four named inclusions; **one degree-generic pointwise Leibniz rule**, from which the degreewise absorption lemmas follow | `cup`, `cupₗ`, then `coboundary_cup` and separate `cup_coboundary_*` lemmas per degree pair; also a `cupOne22` cochain homotopy used for graded commutativity | yes for the product and Leibniz rule; the external project goes further (commutativity, `cupH24`, Wu route) | partly | yes — the front/back index bookkeeping and the need for shifted inclusions were confirmed there |
| functoriality | `pullback`, `pullback_d`, `Hmap`, `Hmap_id`, `Hmap_comp` | **not present** in the inspected file | n/a | n/a | none — native addition |

**Statement required by WP7.** The native implementation converges on essentially the same
mathematical construction as the prior external implementation, which was inspected before the
native layer was written. This is stated explicitly and the prior implementation is credited.
**No novelty is claimed for this reimplementation**: the construction is the classical one, and
an independent Lean realisation of it is not an original result. What is claimed is only that
the Spine now owns a self-contained, machine-checked copy inside its own dependency DAG, with
zero external dependencies, plus a functoriality layer that the inspected file does not
contain.

---

## WP8 — The Čech / singular type gap

### The two carriers

| | Task-3/Task-4 obstruction | Task-5 carrier |
|---|---|---|
| type | `CechSpinLift.ObstructionClass P 𝓤 = Quot (Cohomologous P 𝓤)` | `Mod2Cohomology.Cohomology (TopCat.of X) 2 = Z²/B²` |
| cochains | functions `ι → ι → ι → (X → L)` (kernel-valued, continuous, defined on triple overlaps of **one fixed cover** `𝓤`) | functions `Sing₂ X → ZMod 2` |
| relation quotiented | differ by `δ` of a kernel-valued 1-cochain on the same cover | differ by `δ` of a singular 1-cochain |
| algebraic structure | a `Quot` of a setoid; multiplicative kernel-valued, transported to `ZMod 2` pointwise in `LorentzFrames.zdefect` | a `ZMod 2`-module quotient |
| dependence on a cover | **yes** — the class is defined relative to `𝓤`; refinement naturality is proved (`obstruction_pullLift`), but no colimit over covers is taken | none |

These are different types built from different data. **The Spine contains no map between them
and no statement identifying them.** In particular the equation

> fixed-cover obstruction quotient  =  `H²_sing(X;ℤ₂)`

is **rejected without proof** and appears nowhere in the project. It is not even
type-correct as stated: the two sides are distinct types in distinct universes of construction.

### Minimal theorem needed for a comparison

`RequestProject/Spine/Cohomology/CechBridgeSpec.lean` states the requirement exactly, as an
ordinary structure `ComparisonDatum P 𝓤` with three fields:

1. `compare : ObstructionClass P 𝓤 → H²_sing(X;ℤ₂)`;
2. `compare_trivial` : the trivial class maps to `0`;
3. `compare_injective_at_trivial` : only the trivial class maps to `0`.

Field 3 is the essential one: without it, vanishing of the image would be strictly weaker than
vanishing of the obstruction and the comparison would be useless for certification. The
conditional theorem `comparison_vanishing_iff_exists_coherent` shows precisely what such a
datum would buy: transport of the Task-3 endpoint
(`obstruction_eq_trivialClass_iff_exists_coherent`) into singular cohomology. A comparison
datum is an explicit hypothesis; it is never constructed, never assumed globally, and nothing
downstream consumes it. No axiom is involved.

### Exact dependency specification for the future bridge

To *exhibit* a `ComparisonDatum` one needs, at minimum, the following chain — **none** of which
exists in the pinned library or in the Spine:

| edge | status | note |
|---|---|---|
| Čech cochain complex of an open cover with `ℤ₂` coefficients (as a genuine complex, not the ad-hoc fixed-cover quotient) | MISSING | the Task-3 quotient is only degree-2-modulo-degree-1 on one cover; a full complex is required to speak of `Ȟ²(𝓤;ℤ₂)` |
| identification of `ObstructionClass P 𝓤` with `Ȟ²(𝓤; ℤ₂)` for the constant sheaf `ℤ₂` | MISSING (should be cheap once the previous line exists, via the canonical `{±1} ≅ ℤ/2` already proved in `LorentzFrames.spinSign`) | the additive presentation `LorentzFrames.zdefect` already exists |
| refinement system / colimit `Ȟ²(X;ℤ₂) = colim_𝓤 Ȟ²(𝓤;ℤ₂)` | MISSING | Task-3 has refinement naturality of the class but no colimit |
| a good-cover hypothesis or a nerve theorem | MISSING | **not assumed** |
| paracompactness → the comparison | MISSING | paracompactness and partitions of unity *are* in Mathlib, but they do **not** by themselves supply the comparison theorem; assuming they do is explicitly rejected here |
| Čech-to-singular comparison `Ȟⁿ(X;ℤ₂) ≅ Hⁿ_sing(X;ℤ₂)` for paracompact (or good-cover) `X` | MISSING — this is the large theorem | Task 5 deliberately does **not** attempt it: it does not follow cheaply from anything available |

Verdict for WP8: **DEFERRED**, with the requirement made exact and machine-checked as a
specification.

---

## WP9 — Audit of the possible future definitions of conventional `w₂(TM)`

### Route A — standard characteristic-class construction

Define Stiefel–Whitney classes of a real vector bundle by the classical route (Thom
isomorphism + Steenrod squares, or a classifying-space/`BO(n)` argument, or the axiomatic
characterisation).

Missing infrastructure, all absent from the pinned Mathlib and from the Spine:
Thom spaces and the Thom isomorphism; Steenrod squares (and, for the axiomatic route, the
uniqueness theorem); classifying spaces `BO(n)` and their mod-2 cohomology; the cohomology of
a total space / sphere bundle; naturality of `w` under bundle maps; the Whitney sum formula.
Even with Task-5's `H*(·;ℤ₂)` in hand, this is a very large programme.
Status: **BLOCKED** on infrastructure of a size comparable to several further tasks.

### Route B — Wu formula in dimension four

Dependency chain: closed 4-manifold `M` → mod-2 fundamental class `[M]` → Poincaré duality at
the middle dimension → Wu class `v₂` → `w₂ = v₂ + v₁²`.

What Task 5 now supplies: `H²(M;ℤ₂)`, `H⁴(M;ℤ₂)`, the pairing ingredient
`cupH22 : H² × H² → H⁴` and the top square `cupSquare2`. This is exactly the input a
`v₂`-construction consumes.

What is still missing and would have to be **derived from the manifold**, not assumed:

1. the mod-2 fundamental class of a closed manifold, i.e. a functional `μ : H⁴(M;ℤ₂) → ℤ₂`
   (equivalently a class in `H₄`), and the theorem that it exists for every closed
   4-manifold (every manifold is `ℤ₂`-orientable);
2. non-degeneracy of the middle cup pairing `(a,b) ↦ μ(a ⌣ b)` — i.e. Poincaré duality at the
   middle dimension — plus finite-dimensionality of `H²(M;ℤ₂)`;
3. the Wu formula `w = Sq(v)` itself, which requires Steenrod squares in general degree and
   hence most of Route A's missing machinery, *unless* one takes `v₂` as a definition and then
   still has to prove that `v₂ + v₁²` is the conventional `w₂`.

The external reference A contains a file (`PoincareDualityWu.lean`) that builds `v₂` from a
**supplied** structure `PoincareDual4Mid` (fundamental-class functional + non-degeneracy +
finite-dimensionality). That file was inspected but **not** imported and **not** reproduced,
and no such datum is assumed here: item 1 and item 2 above remain genuine open dependencies of
this project, exactly as they are of that one. Taking `PoincareDual4Mid` as unexplained input
would relocate the hypothesis rather than discharge it.
Status: **DEFERRED**, with items 1–3 as the exact remaining edges.

### Route C — define the class from the Spin-lift obstruction

One could set `w₂ := [c]_frame`. **This is explicitly rejected.** It is circular with respect
to the certification goal: the whole point of the branch is to *prove* that the obstruction
equals the conventional `w₂(TM)`, and a definition cannot prove an identification. Naming a
declaration `w₂` would also violate the name-matching rule recorded in
`TASK05_EXTERNAL_SOURCES.md`, entry D. Task 5 defines no `w₂` at all.
Status: **REJECTED** as a definition; admissible only as a *theorem* once an independently
constructed `w₂` exists.

### Route D (negative control) — a typeclass-supplied `w₂`

Supplying `w₂` as typeclass data over an opaque carrier (the pattern of external reference A's
`SymTFT/StiefelWhitney.lean`) is explicitly forbidden by this task's anti-shortcut constraints
4 and 5, and is not used. It is recorded here so that the distinction between that narrower
predicate/substrate layer and the genuine singular-cohomology layer is on the record.
Status: **NEGATIVE_CONTROL / NOT_USED**.

---

## WP10 — The certification DAG and the next node

Legend: `✔` proved in the Spine; `✘` missing (nothing in Mathlib, nothing in the Spine).

```
   smooth 4-manifold M (Mathlib manifolds)                        ✔ (Task 4)
     └─ Lorentz-orthonormal, oriented, time-oriented local frames ✔ (Task 4)
          └─ GLor-valued frame transition cocycle                 ✔ (Task 4)
               └─ Spin lifts on a fixed cover                     ✔ (Task 3)
                    └─ triple-overlap kernel defect               ✔ (Task 3)
                         └─ [c]_frame ∈ ObstructionClass P 𝓤      ✔ (Task 3/4)
                              └─ additive ℤ₂ presentation         ✔ (Task 4, zdefect)

   X : TopCat
     └─ Sing X = TopCat.toSSet.obj X                              ✔ (Mathlib)
          └─ Cⁿ(X;ℤ₂)                                             ✔ (Task 5, WP2)
               └─ δ,  δ² = 0                                      ✔ (Task 5, WP3)
                    └─ Hⁿ(X;ℤ₂) = Zⁿ/Bⁿ                           ✔ (Task 5, WP4)
                         ├─ f* functorial                         ✔ (Task 5, WP5)
                         └─ ⌣ : H¹×H¹→H², H²×H²→H⁴, Sq-top        ✔ (Task 5, WP6)

   Branch 1 (Čech → singular):
     Čech complex of a cover with ℤ₂ coefficients                 ✘
       └─ ObstructionClass P 𝓤  ≅  Ȟ²(𝓤;ℤ₂)                       ✘ (cheap once above exists)
            └─ colimit over refinements: Ȟ²(X;ℤ₂)                 ✘
                 └─ good cover / nerve theorem, or paracompact
                    Čech-to-singular comparison                   ✘  ← large
                      └─ ComparisonDatum  (specified ✔)           ✘

   Branch 2 (manifold → w₂ via Wu, dim 4):
     mod-2 fundamental class [M] ∈ H₄(M;ℤ₂) / μ : H⁴ → ℤ₂         ✘
       └─ Poincaré duality: non-degeneracy of the middle pairing  ✘
            └─ Wu class v₂ (from μ, ⌣, Sq-top)                    ✘ (inputs ✔ after Task 5)
                 └─ Wu formula w₂ = v₂ + v₁²                      ✘ (needs Sq in general degree)

   Branch 3 (classical characteristic classes):
     Thom space / Thom isomorphism                                ✘
       └─ Steenrod squares                                        ✘
            └─ w(E) for real vector bundles, naturality, Whitney  ✘
                 └─ w₂(TM)                                        ✘

   Target:  [c]_frame = w₂(TM)                                    ✘
            (requires Branch 1 AND (Branch 2 or Branch 3))
```

Every missing edge above is explicit. Note that the target needs **both** a comparison of
carriers (Branch 1) and an independent construction of `w₂` (Branch 2 or 3): Task 5 closed
neither, but it closed the shared prerequisite of all of them.

### Recommended next certification node

The audit — not a preselection — points to the following shortest genuinely useful edge:

> **Next node: a native Čech cochain complex with `ℤ₂` coefficients on a fixed cover, and the
> identification of the Task-3/Task-4 obstruction class with its `Ȟ²`.**

Reasons: (i) it is the only remaining edge whose inputs already exist in the Spine — the
additive `ℤ₂` presentation `LorentzFrames.zdefect`, its 2-cocycle law and its coboundary law
are proved, so the identification is a bookkeeping theorem rather than new mathematics;
(ii) it converts the ad-hoc fixed-cover quotient into a standard object, which every later
route needs; (iii) it does *not* require a good cover, paracompactness or the large
comparison theorem, so it cannot be blocked. The two genuinely large edges (the Čech-to-
singular comparison, and either Wu/Poincaré duality or Thom/Steenrod) should be scheduled only
after that, and each should be its own task.

---

## Principal-bundle boundary and branch separation

No general `PrincipalBundle` library was built (explicit non-goal). The external
principal-bundle projects (references B and C) were inspected only because the *wider*
programme — Spin lift → associated Lorentz bundle → soldering — will need such infrastructure;
they are recorded in the infrastructure audit and in `TASK05_EXTERNAL_SOURCES.md`. That branch
is **not** merged with the certification branch: no module of
`RequestProject.Spine.Cohomology.**` mentions bundles, soldering, connections or dynamics.

---

## 11. Failbuild ledger (append-only)

Every failure encountered while building this layer, with diagnosis and repair. No entry
changed a mathematical statement; the classification column records this explicitly.

| # | command | error | diagnosis | repair | statement change |
|---|---|---|---|---|---|
| 1 | initial write of `RequestProject/Spine/Cohomology/Cochain.lean` | file-creation error: parent directory did not exist | the `Spine/Cohomology` directory had not been created yet | created the directory and rewrote the file; in the same rewrite the redundant `instance … := inferInstance` re-declarations of the inherited `Pi` structures were replaced pre-emptively by `example … := inferInstance` sanity checks (this was a precaution, not a reaction to a build failure) | none |
| 2 | `lake build …Functorial` | `No goals to be solved` at `congr 1` in `Hmap_id`/`Hmap_comp` | `rw [Hmap_mk]` already closed the goal by `rfl`; the follow-up tactics had nothing to act on | replaced the tactic block by a direct `congrArg mk (Subtype.ext …)` term | none |
| 3 | `lake build …AlexanderWhitney` (first version, `simp only [val_*]` approach) | `omega could not prove the goal`, unreduced atoms `↑((Hom.toOrderHom (backSmall p q)) k)` | the `val_*` rewrite lemmas failed to match because the bound variable's type displayed as `Fin ((SimplexCategory.mk q).len + 1)`, blocking syntactic matching | switched to `dsimp` of the definitions plus explicit per-branch closing (`rfl`, `exfalso … omega`, or `show _ = <explicit ℕ expression>; omega`) | none |
| 4 | `lake build …AlexanderWhitney` (after removing `Fin.val_mk` from a shared `simp only` on a linter hint) | `omega could not prove the goal` | the linter reported the argument unused *at one occurrence*; it was load-bearing at another | restored the argument; the remaining linter hint is cosmetic and does not affect correctness | none |
| 5 | `lake build …Cup` | `unsolved goals` in the two `Finset.sum_bij'` term-equality obligations, and `'show' tactic failed … not definitionally equal` | after rewriting with the coface identities, two Fin indices agreed only up to `Fin.ext` (`k.castSucc` vs `⟨k.val,_⟩`, `l.succ` vs `⟨(l+p+1)-p,_⟩`) | closed the first by `rfl` (defeq) and the second by `congrArg` along an explicit `Fin.ext` proof | none |
| 6 | `lake build …Cup` | `simp made no progress` in the final `calc` step | after `rw [hchar E]` the goal was `S₁+S₂ = S₁+S₂+0`, so `simp` had nothing to do | replaced by `rw [hchar E, add_zero]` | none |
| 7 | `lake build …CupDescent` | `No goals to be solved` at a trailing `rfl` (twice) | the preceding `simp only [zero_mul, zero_add]` had already closed those goals | deleted the redundant `rfl`s | none |

## 12. Build evidence

All commands run in the project root with the pinned toolchain, after the layer was complete.

```
lake build RequestProject.Spine.E1.Core            → Build completed successfully (8055 jobs).
lake build RequestProject.Spine.E1.Topology.Core   → Build completed successfully (8052 jobs).
lake build RequestProject.Spine.E2.Core            → Build completed successfully (8091 jobs).
lake build RequestProject.Spine.Core               → Build completed successfully (8149 jobs).
lake build RequestProject.Spine.Audit.Firewall     → Build completed successfully (8158 jobs).
lake build RequestProject.Spine.Cohomology.Core    → Build completed successfully (8062 jobs).   (new Task-5 target)
lake build                                         → Build completed successfully (8162 jobs).
```

Firewall output (`RequestProject.Spine.Audit.Firewall`):

```
Spine external-project imports: 0 (prefixes checked: 7)
Spine modules audited: 132
Spine direct legacy imports:    Experiment1 = 0   Experiment2 = 0
Spine transitive legacy imports: Experiment1 = 0  Experiment2 = 0
SPINE FIREWALL AUDIT: all checks passed
```

> **Documentation correction (recorded during Task-6 maintenance, 2026-09-08; no mathematical
> content of Task 5 is affected).**
>
> The number `132` above is the number of Spine modules *present in the audit environment*,
> i.e. reachable through the import header of `RequestProject.Spine.Audit.Firewall`.  It is
> **not** the number of Spine source files in the archive.  At the end of Task 5 the archive
> contained **134** modules under `RequestProject/Spine/**`.  The two modules on disk that the
> audit figure does not count are
>
> * `RequestProject/Spine/Audit/Firewall.lean` — the audit module itself, which is being
>   elaborated when the count is taken, and
> * `RequestProject/Spine/Foundation/MinkowskiMatrix.lean` — present in the archive but not
>   imported (directly or transitively) by any endpoint, hence absent from the audit
>   environment.
>
> Both figures are therefore correct for what they measure; only the wording was ambiguous.
> The corrected Task-5 statement is: **134 Spine modules in the archive, 132 in the audit
> environment.**  After Task 6 the same two figures are **146** and **144**.

The firewall was extended for this task with

* `auditNoExternal`, run over **every** Spine module, forbidding any transitive import whose
  module name lies under an inspected external project (`SKEFTHawking`, `SKEFT`, `MathPhysics`,
  `JanusFormal`, `Janus`, `GQ2`, `Gq2`) — this is the mechanical external-code isolation test;
* endpoint reports for all eight new Task-5 modules;
* a layering check that the seven pure-cohomology modules reach **no** module of
  `Spine.E1`, `Spine.E2`, `Spine.Geometry` or `Spine.Controls` (they are built on Mathlib
  alone), together with a positive control that the bridge specification *does* reach
  `Spine.E2.Cech.Obstruction` (so the audit is sensitive);
* proof-closure audits for the twelve principal new declarations.

Isolation: there is no git dependency on any external project (`lakefile.toml` requires only
Mathlib), no copied namespace, no generated code, no vendor directory, no external `.olean`,
and no external source file in the import closure. The Spine builds with all external
repositories absent.

## 13. Axiom audit

`#print axioms` is run inside `RequestProject/Spine/Cohomology/Core.lean` for every principal
Task-5 declaration. All report exactly `[propext, Classical.choice, Quot.sound]`:

```
Mod2Cohomology.Cochain, face_face, coboundary_coboundary, d_comp_d,
coboundaries_le_cocycles, Cohomology, mk_eq_zero_iff, pullback_d, Hmap, Hmap_id, Hmap_comp,
coboundary_cup, cup_cocycle, cupH11, cupH22, cupSquare1, cupSquare2,
comparison_vanishing_iff_exists_coherent
```

The Task-5 sources contain no `sorry`, no `admit`, no project-local `axiom`, no `unsafe`, no
`partial`, no `implemented_by`, and no equivalent proof bypass. (`ComparisonDatum` is a
*structure taken as an explicit hypothesis*, not an axiom, and nothing in the project supplies
or assumes an instance of it.)

---

## 14. Final scientific questions

**Q1. Has a genuine native singular cohomology carrier `H²(X;ℤ₂)` now been reconstructed
inside the Spine without importing or copying an external formalization?**

**Yes.** `Mod2Cohomology.Cohomology X 2` is the quotient `Z²/B²` of the kernel of an explicit
`ZMod 2`-linear coboundary between explicit function spaces
`Cⁿ(X;ℤ₂) = Sing_n X → ZMod 2` built on Mathlib's singular simplicial set. `δ² = 0` is a
theorem derived from `SimplexCategory.δ_comp_δ`; `B² ⊆ Z²` is a theorem; the carrier is a real
quotient module, not an opaque type and not typeclass input. It comes with functorial
pullbacks and with cup products `H¹×H¹→H²`, `H²×H²→H⁴`. Nothing external is imported or
copied, and the mechanical audit reports external-project imports = 0 over all 132 Spine
modules. The construction is the classical one and *converges* with the prior external
implementation credited in `TASK05_EXTERNAL_SOURCES.md`; no novelty is claimed for it.

**Q2. What is the shortest remaining theorem-level dependency chain required to identify the
existing Lorentz-frame Spin-lift obstruction with conventional `w₂(TM)`?**

Two independent chains must both be completed; neither is short.

*Carrier comparison (Branch 1).* Čech `ℤ₂`-cochain complex of a cover → identification of
`ObstructionClass P 𝓤` with `Ȟ²(𝓤;ℤ₂)` (cheap: the additive presentation already exists) →
colimit over refinements → a good-cover/nerve theorem or a paracompact Čech-to-singular
comparison theorem → an instance of the specified `ComparisonDatum`. The last edge is the
large one; paracompactness alone does **not** supply it, and this project refuses to assume
otherwise.

*Construction of `w₂` (Branch 2 or 3).* Either: mod-2 fundamental class of a closed
4-manifold → Poincaré duality at the middle dimension → Wu class `v₂` → Wu formula (needing
Steenrod squares) → `w₂`; or the classical route Thom space → Thom isomorphism → Steenrod
squares → Stiefel–Whitney classes with naturality and the Whitney sum formula.

Only then can `[c]_frame = w₂(TM)` be *stated*, let alone proved. Defining `w₂` to be the
obstruction is rejected as circular. The recommended immediate next node — the shortest edge
whose inputs already exist — is the native Čech `ℤ₂` complex plus the identification of the
Task-3/Task-4 class with `Ȟ²` of the cover.

**Q3. Which parts of this dependency chain had already been explored by other Lean projects,
and how must those prior works be credited even though the current implementation was
independently reconstructed?**

* **Singular mod-2 cohomology, cup product, and the `v₂`/Wu route in dimension four** had
  already been explored — and, for the cohomology layer, carried out — in
  `NetRxn/SK_EFT_Hawking` (`lean/SKEFTHawking/SingularCohomologyMod2.lean` and
  `PoincareDualityWu.lean`), at commit `e7abc5d944bf7350d6de14de5ec8cb26c66e7f74`. That work
  was inspected before this layer was written; the native construction converges with it on the
  cochain carrier, the face maps, the coboundary, the mechanism of the `δ² = 0` proof, the
  quotient, and the Alexander–Whitney product. It must be cited by author, repository, file
  and commit in any later paper, and the convergence must be stated — even though no code was
  copied and the Spine has no dependency on it. Its `SymTFT/StiefelWhitney.lean` is credited
  separately as a *negative control*: opaque carriers with typeclass-supplied `w`, which is
  exactly what this project must not do.
* **Reconstruction of principal/Pin bundles from Čech-style local data on top of Mathlib's
  `FiberBundleCore`** had been explored in `trigunino/janus-formal` (commit
  `a7262727…`); relevant to the separate soldering branch, credited as a design reference.
* **A hand-rolled `PrincipalBundle` and gauge-transformation design** exists in
  `TataSatyaPratheek/mathematical-physics-lean` (commit `f897b7f4…`, MIT); credited as a design
  reference and simultaneously as a negative control, since that project rests on 362
  project-local `axiom` declarations and is therefore incompatible with the Spine's trust
  policy.
* **A declaration named `StiefelWhitney` in a quadratic-forms/Galois-cohomology setting.**
  *(Provenance corrected during Task-6 maintenance, 2026-09-08.)*  The repository is
  `https://github.com/roed314/gq2`, inspected at commit
  `a2b1481f5e87acbb732b1e0fcf308a7ac2a9013a`; the Task-5 entry gave a wrong path
  (`roed-math/gq2-lean`) and wrongly reported it as inaccessible.  The generated documentation
  there covers `GQ2.StiefelWhitney`, i.e. Stiefel–Whitney/Hasse–Witt invariants `w₁`, `w₂` of
  binary quadratic forms in Galois cohomology — **not** tangent-bundle characteristic classes.
  It is recorded permanently as a name-collision **NEGATIVE_CONTROL** (nothing used, nothing
  copied, no dependency); see `TASK05_EXTERNAL_SOURCES.md`, Entry D.
* **Community discussion** on the historical absence of principal-bundle infrastructure in
  Mathlib is background context only and is not cited as a source of any mathematical fact.

Full ledger entries, with owner, repository, files, commit hashes, access dates, licence status
and classification, are in `TASK05_EXTERNAL_SOURCES.md`.
