# TASK 39 — code hygiene

Scope: the four modules added by Task 39, plus the one audit-only edit of an existing module.

```text
RequestProject/Spine/Deformation/SmoothProjectedGauge.lean   §4  smooth projected Lorentz gauge
RequestProject/Spine/Deformation/SolderTransport.lean        §5  transport of regular solder solutions
RequestProject/Spine/Closure/IntermediateMilestone.lean      §7  intermediate-milestone certificate
RequestProject/Spine/Closure/AxiomAudit.lean                 §36 `#print axioms` audit module
RequestProject/Spine/Deformation/Firewall.lean               audit-only extension (no check relaxed)
```

No frozen mathematical module was edited by Task 39.  The only edit outside the new files is
the extension of the branch firewall's audited-module list and the addition of one further
leaf check (see `TASK39_FAILBUILDS.md` and `TASK39_PROVENANCE.md`).

## Prohibited constructs — none present

Checked with whole-word `rg` over the four new files.

| construct | occurrences in new modules |
| --- | --- |
| `sorry` | 0 |
| `admit` | 0 |
| new `axiom` | 0 |
| `native_decide` | 0 |
| `unsafe` | 0 |
| `partial` | 0 |
| `implemented_by` | 0 |
| `Matrix.inv` | 0 |

The only textual occurrences of `sorry`, `axiom`, `native_decide` and `Classical` anywhere in
the new files are inside the documentation header of `Spine/Closure/AxiomAudit.lean`, which
*describes* the audit result (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no
project axiom, no `native_decide` axiom).  They are prose, not code.

## Discouraged tactics — none present

| tactic | occurrences in new proof modules |
| --- | --- |
| `simp` / `simpa` / `simp only` | 0 |
| `Classical` (`open Classical`, `Classical.choice` in source) | 0 |
| `decide` | 0 |
| `native_decide` | 0 |
| `omega` | 0 |
| `linarith` | 0 |
| `norm_num` | 0 |
| `aesop` | 0 |
| leftover `exact?` / `apply?` | 0 |

Tactics actually used, by module:

| module | tactics |
| --- | --- |
| `SmoothProjectedGauge.lean` | `rw`, `exact`, `show`, `refine`, `congr`, `cases`, `ring`, `rfl` |
| `SolderTransport.lean` | `rw`, `show`, `refine`, `obtain`, `intro`, `funext`, `exact`, `congr`, `ring`, `rfl` |
| `IntermediateMilestone.lean` | `obtain`, `exact`, `refine` only — the certificate merely aggregates already certified endpoints |

`Spine/Closure/AxiomAudit.lean` contains no tactic proofs at all: it is a sequence of
`#print axioms` commands on 62 endpoint theorems.

## Localized `Classical` exceptions of the repository — listed exactly, none added

Task 39 adds **no** new `Classical` use.  For completeness, the twelve pre-existing localized
`open Classical in` sites inside the certified spine are, at the state frozen here:

```text
RequestProject/Spine/E1/Topology/LocalSection.lean:311
RequestProject/Spine/Nerve/Geometry/PointModel.lean:43
RequestProject/Spine/E2/Topology/AtlasTopology.lean:68
RequestProject/Spine/E2/Topology/FrameTopology.lean:190
RequestProject/Spine/E2/Topology/FrameTopology.lean:213
RequestProject/Spine/E2/Global/InternalQuotient.lean:106
RequestProject/Spine/E2/Global/InternalQuotient.lean:127
RequestProject/Spine/Solder/WeakInsufficiency.lean:136
RequestProject/Spine/Solder/RegularSolder.lean:294
RequestProject/Spine/Task36/LoopSpinFreedom.lean:189
RequestProject/Spine/Deformation/LoopSharedTransport.lean:87
RequestProject/Spine/Deformation/FixedBaseSmokeTest.lean:106
```

Each is a case split on a non-decidable membership predicate used to *define* a function by
`if … then … else`; none of them enters a mathematical hypothesis.  They are the exceptions
recorded by the earlier task hygiene documents and are reproduced here so that the frozen
release lists them explicitly rather than hiding them.

Two `partial def` occur in the meta-level audit tooling only:

```text
RequestProject/Spine/Audit/Firewall.lean:98   closureAux
RequestProject/Spine/Audit/Firewall.lean:231  collectDeps
```

These are import-graph traversals in `MetaM`; they carry no mathematical content and are
pre-existing.  Task 39 did not add any.

## Style

* Every new declaration carries a docstring tagged with its Task-39 part (`§4`, `§5`, `§7`).
* The only `set_option`s in the new proof modules are the two already used throughout the
  branch, `synthInstance.maxHeartbeats 400000` and `maxHeartbeats 1000000`.  No linter is
  disabled anywhere.
* No no-op tactic (`skip`, stray `try`) remains.
* The mechanical token audit of `Spine/Deformation/Firewall.lean` scans the enlarged branch
  and passes; the new closure branch is additionally checked to be an import leaf.
