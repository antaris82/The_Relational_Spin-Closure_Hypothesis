# TASK 13 — failbuild ledger (append-only)

Every failing build (or failing elaboration probe) of a Task-13 module, in order.
"Statement change" records whether the repair altered a *statement* rather than a proof.

---

## F0

* **command** — scratch elaboration probe (`import Mathlib`), definition
  `K ⋙ ModuleCat.free (ZMod 2)` for `K : SSet.{u}`
* **diagnostic** —
  `Application type mismatch: the argument ModuleCat.free (ZMod 2) has type
  Functor.{0,0,1,1} Type (ModuleCat (ZMod 2)) ... but is expected to have type
  Functor.{u,u,u+1,u+1} (Type u) (ModuleCat (ZMod 2))`
* **cause** — `ModuleCat.free` is universe-monomorphic: it produces `Type u ⥤ ModuleCat.{u} R`
  with the ring `R` in the *same* universe `u`, and `ZMod 2 : Type 0` forces `u = 0`.  The
  project's nerve lives in an arbitrary universe.
* **repair** — the free simplicial `ℤ₂`-module `SpineTask13.freeSSetModule` is built by hand
  (six lines: `ModuleCat.of (S.obj n →₀ ZMod 2)` with `Finsupp.lmapDomain` on morphisms), which
  is universe-polymorphic.
* **statement change** — NO (this determined how a definition is *built*, not what is claimed).

## F1

* **command** — `lake build RequestProject.Spine.Nerve.Task13Normalization`
* **diagnostic** — four issues in one run:
  1. `Unknown identifier NerveGeom.z2_sub_eq_add`;
  2. repeated `Application type mismatch: the argument x has type S _⦋q⦌ but is expected to
     have type SSetChain S q ... in the application Submodule.Quotient.mk x`;
  3. `Invalid field notation ... 𝟙 (AlternatingFaceMapComplex.obj (freeSSetModule S)) ... .f 0`;
  4. `typeclass instance problem is stuck: Membership (SSetChain T (n+1)) ?m`.
* **cause** — (1) the characteristic-two helper lives in `ChainHomotopyComparison`, which this
  module does not import; (2) `ext` descends through the `Finsupp` structure and introduces a
  *simplex* rather than a *chain* when the goal is a map out of a quotient; (3) dot notation
  cannot project through `𝟙`; (4) an underscore in a `show ... ∈ _` left the submodule
  undetermined.
* **repair** — (1) a local `z2_add_self_gen` was proved instead; (2) `ext` replaced by
  `Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)`; (3) `HomologicalComplex.id_f` and
  `ModuleCat.hom_id` used as rewrites instead of a `have ... := rfl`; (4) the target submodule
  written out explicitly.
* **statement change** — NO (proofs only).

## F2

* **command** — `lake build RequestProject.Spine.Nerve.Task13Normalization`
* **diagnostic** — three `Application type mismatch` / `Type mismatch` errors of the form
  `Eq.symm (congrFun (φ.naturality f) y) has type (φ.app m ≫ T.map f) y = (S.map f ≫ φ.app n) y
  but is expected to have type φ.app n (S.map f y) = T.map f (φ.app m y)`.
* **cause** — composition in `Type` reverses the reading order, so the naturality square already
  had the orientation needed, and the `≫`-form was not unfolded by `exact`.
* **repair** — normalise with `simp only [types_comp_apply]` first and drop the `.symm`; the
  same repair applies to the third site (`PInfty_f_naturality`), closed with `simpa`.
* **statement change** — NO (proofs only).

## F3

* **command** — `lake build RequestProject.Spine.Nerve.Task13Skeletal`
* **diagnostic** — in sequence:
  1. `Invalid projection ... Finsupp.mem_supported has function type ...`;
  2. `Invalid argument name v for function Finsupp.mapDomain_support`;
  3. `failed to synthesize instance of type class DecidableEq (S _⦋n + 1⦌)`.
* **cause** — (1) `Finsupp.mem_supported` takes the ring explicitly, so `.2` cannot be used as
  dot notation on the unapplied lemma; (2) the named argument is `s`, not `v`, in the pin;
  (3) `Finsupp.mapDomain_support` needs decidable equality on the target type.
* **repair** — `(Finsupp.mem_supported (ZMod 2) _).2`, `(s := y)`, and `classical` at the head
  of the proof.
* **statement change** — NO (proofs only).

## F4

* **command** — `lake build RequestProject.Spine.Nerve.Task13Skeletal`
* **diagnostic** — `Unknown constant Submodule.quotEquivBot`.
* **cause** — guessed name; the pin calls it `Submodule.quotEquivOfEqBot`.
* **repair** — `(Submodule.quotEquivOfEqBot _ hbot).trans (normChainEquiv _ r)`.
* **statement change** — NO (proof term only).

## F5

* **command** — `lake build RequestProject.Spine.Nerve.Task13CanonicalMap`
* **diagnostic** —
  `failed to synthesize instance of type class
  HAdd (SSetChain (coverNerveSSet U) (q+1) →ₗ[ZMod 2] SimpChain U (q+1))
       (SimpChain U (q+1) →ₗ[ZMod 2] SSetChain (coverNerveSSet U) (q+1)) ?m`
* **cause** — the restatement of the homotopy identity for the nerve mixed the two *equal but
  differently displayed* abbreviations `NerveGeom.SimpChain U q` and
  `NerveGeom.SSetChain (coverNerveSSet U) q`, so the elaborator could not see the two summands
  as endomorphisms of one type.
* **repair** — the two restatements (`nerve_normHtpy_zero`, `nerve_normHtpy_succ`) are phrased
  with `sSetBoundary (coverNerveSSet U)`; `nerveBoundary_eq` proves by `rfl` that this is the
  Task-9 `simpBoundary U`, so nothing is lost.
* **statement change** — NO in content (the two sides are definitionally the same map, and that
  identification is itself a theorem in the file); the *presentation* of the restatement changed.
