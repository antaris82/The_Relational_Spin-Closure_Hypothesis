# Naming normalization audit

**Scope.** Strictly a module-path / packaging normalization of the combined
Lean project. No mathematical content was added, removed or modified.

---

## 1. Old mapping (incorrect, previous archive)

| Module root | Contained development | Correct canonical label |
| --- | --- | --- |
| `RequestProject.Exp1` | Split Complex Lorentzian Dynamics | Experiment **2** |
| `RequestProject.Exp2` | Intrinsic Branching from a Derived Lorentz Structure | Experiment **1** |

The labels `Exp1` / `Exp2` were therefore **reversed** with respect to the
established project terminology.

## 2. Corrected mapping

| Module root | Mathematical project | Canonical label |
| --- | --- | --- |
| `RequestProject.Experiment1` | **Intrinsic Branching from a Derived Lorentz Structure** (`Split-Complex-Lorentzian_Kinematics`, branch `Intrinsic-Branching-from-a-Derived-Lorentz-Structure`) | Experiment 1 / E1 |
| `RequestProject.Experiment2` | **Split Complex Lorentzian Dynamics** (`Split-Complex_Lorentz_Dynamics`, branch `main`) | Experiment 2 / E2 |

No `Exp1` / `Exp2` aliases were introduced, and none are retained: after
normalization the strings `Exp1` and `Exp2` occur in **0** Lean files.

## 3. Exact prefix transformations applied

Directory relocation (performed with `git mv`, so rename provenance is recorded
in git history):

```text
RequestProject/Exp2/  →  RequestProject/Experiment1/
RequestProject/Exp1/  →  RequestProject/Experiment2/
```

Textual rewriting, applied to every `*.lean` file under `RequestProject/`
(imports and doc-comment references) in a single simultaneous pass:

```text
RequestProject.Exp2   →   RequestProject.Experiment1
RequestProject.Exp1   →   RequestProject.Experiment2
```

Command used:

```sh
find RequestProject -name '*.lean' -print0 | xargs -0 sed -i \
  -e 's/RequestProject\.Exp1/RequestProject.Experiment2/g' \
  -e 's/RequestProject\.Exp2/RequestProject.Experiment1/g'
```

(`sed` applies the two `-e` scripts to each line left to right, but the
right-hand sides contain no `Exp1`/`Exp2` token, so the substitution is
effectively simultaneous — verified by the post-check below.)

Pre-check: **every** occurrence of the tokens `Exp1`/`Exp2` in the project was
already fully qualified as `RequestProject.Exp1` / `RequestProject.Exp2`
(470 and 352 occurrences respectively; 0 unqualified occurrences), so the
transformation is exactly a module-prefix rewrite.

Post-check occurrence counts:

| Token | Before | After |
| --- | --- | --- |
| `RequestProject.Exp1` | 470 | 0 |
| `RequestProject.Exp2` | 352 | 0 |
| `RequestProject.Experiment1` | 0 | 352 |
| `RequestProject.Experiment2` | 0 | 470 |

## 4. File counts

| Tree | Lean files |
| --- | --- |
| `RequestProject/Experiment1/` (E1) | 152 |
| `RequestProject/Experiment2/` (E2) | 334 |
| Vendored total | 486 |
| Non-vendored project files | `RequestProject/Main.lean`, `RequestProject/CombinedDemo.lean` |

File counts are unchanged from the previous archive (previously 152 under `Exp2`
and 334 under `Exp1`); no file was added, deleted or split.

## 5. Non-prefix source-difference audit

Method: a snapshot of the pre-normalization trees was taken; the *inverse-free*
prefix substitution of §3 was applied mechanically to the snapshot; the result
was compared recursively (`diff -r`) with the post-normalization trees.

```sh
cp -r RequestProject/Exp2 snap/norm1 ; cp -r RequestProject/Exp1 snap/norm2
sed -i 's/RequestProject\.Exp2/RequestProject.Experiment1/g'  (all of snap/norm1)
sed -i 's/RequestProject\.Exp1/RequestProject.Experiment2/g'  (all of snap/norm2)
diff -r snap/norm1 RequestProject/Experiment1
diff -r snap/norm2 RequestProject/Experiment2
```

Result (number of diff output lines):

```text
E1 non-path source differences = 0
E2 non-path source differences = 0
```

Both vendored trees are therefore byte-identical to their previous state modulo
the explicit module-prefix transformation. In particular no theorem statement,
definition, proof, `set_option`, attribute or external import was touched, and
no namespace qualification beyond import-path rewriting was required.

## 6. Namespace-collision audit

Performed after the module-root rename.

**Module names.** The two trees live under disjoint module roots
(`RequestProject.Experiment1.*`, `RequestProject.Experiment2.*`), so module-name
collisions are impossible even where the leaf names coincide.

**Declaration namespaces.** Top-level `namespace` heads used by each tree:
49 distinct in E1, 72 distinct in E2. Their intersection is a single name:

```text
Counterexample
```

(E1: `Experiment1/Task7Counterexamples.lean`, `Experiment1/SectorAlgebra.lean`;
E2: `Experiment2/NullSectorTask29/Counterexample.lean`.)

**Fully qualified declaration names.** A mechanical scan of all declaration
heads (`theorem`/`lemma`/`def`/`abbrev`/`structure`/`inductive`/`class`/
`instance`/`opaque`), resolved against the enclosing `namespace` stack, gives
3270 declaration names in E1 and 6192 in E2. The raw intersection contained
three entries — `about`, `is`, `of` — all of which were manually inspected and
found to be **false positives**: they are prose words at the start of a
continuation line inside a doc comment (e.g. `theorem about what a
future-oriented …`), not declarations. There are therefore **no** genuinely
colliding fully qualified declaration names.

Even in the shared `Counterexample` namespace the leaf declaration names are
disjoint, so the two trees can be `open`ed together without ambiguity; and in
any case simultaneous *import* — which is what this task requires — is
unaffected by declaration-name overlap.

**Classification:**

| Category | Verdict |
| --- | --- |
| Module-path collisions | `NONE` |
| Fully qualified declaration collisions | `NONE` |
| Shared top-level namespace heads (`Counterexample`) | `RESOLVED_BY_MODULE_QUALIFICATION` (disjoint leaves; no action taken) |
| Declarations requiring a namespace refactor | `NONE` — no `REQUIRES_DECLARATION_NAMESPACE_REFACTOR` case arose |

No declaration namespace was altered.

## 7. Combined smoke test

`RequestProject/CombinedDemo.lean` now imports one representative module from
each correctly named experiment:

```lean
import RequestProject.Experiment1.SpinFinal
import RequestProject.Experiment2.NullSectorTask01.Task01
```

(the same representative endpoints as the previous combined smoke test, with the
labels corrected), and re-states one already-proved result from each:

* `CombinedDemo.experiment1_spin_double_cover` ← `SpinLorentz.spin_lorentz_double_cover` (E1);
* `CombinedDemo.experiment2_task01_restriction` ← `NullSectorTask01.task01_restriction` (E2).

No cross-experiment mathematical statement was added.

Axiom audit of the two endpoints (`#print axioms`, emitted during the build):

```text
'CombinedDemo.experiment1_spin_double_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'CombinedDemo.experiment2_task01_restriction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Conclusion: both correctly named experiments coexist and can be imported
simultaneously in the same Lean environment.**

## 8. Build results

All commands run from the project root.

### 8.1 Incremental build after path normalization / focused build of the smoke test

```sh
lake build RequestProject.CombinedDemo
```

Result: `Build completed successfully (8043 jobs).` — 0 errors.
(The same command was used both as the incremental post-normalization check and
as the focused build of `CombinedDemo.lean`; the smoke-test module and its
transitive dependencies were rebuilt under the new module paths.)

### 8.2 Full-project build

```sh
lake build
```

Result: `Build completed successfully (8514 jobs).` — 0 errors.

Exact job counts: **8043** (focused, `RequestProject.CombinedDemo` and its
dependencies) and **8514** (whole project, all 486 vendored modules plus
`Main.lean` and `CombinedDemo.lean`).

### 8.3 Warnings

0 errors. The build emits only pre-existing upstream style warnings from the
vendored sources; in the full-project run 236 warning lines were logged, by
linter:

| Linter | Count |
| --- | --- |
| `linter.unusedSimpArgs` | 140 |
| `linter.unreachableTactic` | 23 |
| `linter.unusedTactic` | 23 |
| `linter.unnecessarySeqFocus` | 10 |
| `linter.unusedSectionVars` | 9 |
| `linter.unusedVariables` | 8 |
| `linter.unnecessarySimpa` | 5 |

None of these are new: they originate in the vendored proofs, which this task
did not modify. Additionally the developments themselves emit `#print axioms`
`info` messages, all reporting only `propext`, `Classical.choice`, `Quot.sound`.

### 8.4 Failed builds and repairs

Exactly one build failure occurred during this task.

* **Command:** `lake build RequestProject.CombinedDemo`
* **Exact error:**
  `error: RequestProject/CombinedDemo.lean:43:75: unexpected token '#print'; expected 'lemma'`
* **Diagnosis:** when adding the optional axiom audit to the smoke-test file, the
  explanatory note was written as a documentation comment `/-- … -/`, which Lean
  requires to be attached to a declaration; the following line is a `#print`
  command, not a declaration.
* **Repair:** the documentation comment was changed to an ordinary line comment
  `-- Axiom audit for the two smoke-test endpoints (standard axioms only).`
* **Mathematical content changed:** **no** — the change is a comment syntax fix
  in the smoke-test file only; no vendored source was involved.

No other build failed. In particular the path normalization itself produced a
green incremental build on the first attempt.

## 9. Formal-policy check

Scanned across all Lean sources of the project:

* `sorry` — none;
* `admit` — none;
* `axiom` declarations — none;
* `@[implemented_by]` — none;
* `native_decide`, `bv_decide` — none;
* new `unsafe` — none;
* new `partial` — none (the pre-existing `partial def` occurrences are upstream
  metaprogramming helpers inside the experiments' own dependency-audit files and
  were left byte-identical).

## 10. Acceptance criteria

| # | Criterion | Status |
| --- | --- | --- |
| 1 | `Experiment1` = Intrinsic Branching from a Derived Lorentz Structure everywhere | ✅ |
| 2 | `Experiment2` = Split Complex Lorentzian Dynamics everywhere | ✅ |
| 3 | Old reversed `Exp1`/`Exp2` naming no longer causes ambiguity (0 occurrences in Lean sources; documented in the docs) | ✅ |
| 4 | Both experiments still import simultaneously | ✅ (`CombinedDemo.lean` builds) |
| 5 | Both source trees unchanged modulo the audited module-prefix transformation | ✅ (0 / 0 diffs) |
| 6 | No new mathematical cross-experiment theorem | ✅ |
| 7 | Combined project builds green | ✅ (8514 jobs, 0 errors) |
| 8 | Provenance documentation records the inversion and its correction | ✅ (`COMBINED_PROJECT_PROVENANCE.md`) |
