# TASK 40 — fail / change ledger (append-only)

Every validator failure, registry mismatch, manifest mismatch and generator failure
encountered while producing the Task-40 release hardening, recorded at the moment it happened.
Nothing is erased after the final PASS.  Historical ledgers `TASK10…TASK39_FAILBUILDS.md` are
untouched; they remain the authoritative record of their own tasks and are mirrored (never
rewritten) into `docs/machine/FAILBUILD_LEDGER.jsonl`.

Task 40 is a documentation task: **no Lean build ever failed**, and the only Lean edit was
audit-only (four plus one `#print axioms` lines appended to
`RequestProject/Spine/Closure/AxiomAudit.lean`).  For each entry: exact command, exact file,
exact error, diagnosis, repair, and the four impact questions.

---

## F1

* **Command** `python3 audit/verify_documentation_snapshot.py`
* **Location** `NEXT_PHASE_TRANSPORT_GATE.md:7` and three further lines (§1 bullet list, §3, §7)
* **Error** `forbidden statement 'no Lie algebra'`, `forbidden statement 'spinCover ∘ ω'`,
  `forbidden statement 'transition-cocycle deformations are pure gauge'`,
  `forbidden statement 'transition-cocycle deformation is a change of trivialisation'`
* **Diagnosis** the newly added overclaim sentinels (Part VIII §15) fired on the *replacement*
  handoff document, which quotes the withdrawn sentences in order to forbid them.  A blanket
  file exemption would have disabled the check on exactly the document that most needs it.
* **Repair** the sentinel check was refined to a line-level test: a match is accepted only when
  an explicit do-not-claim marker (`forbidden`, `must not`, `must never`, `withdrawn`,
  `quoted invalid`, `type error`, `not proved`, …) occurs within three lines of it.  One
  sentence of `NEXT_PHASE_TRANSPORT_GATE.md` §2 was additionally rewritten so that the negative
  context is explicit on the line itself.
* Theorem statement changed? **NO** — assumptions changed? **NO** — source architecture
  changed? **NO** — documentation schema changed? **YES** (the validator gained the sentinel
  context rule).

## F2

* **Command** `python3 audit/verify_documentation_snapshot.py`
* **Location** `docs/machine/SOURCE_MANIFEST.json`, `docs/machine/RELEASE_MANIFEST.json`
  (26 entries)
* **Error** `hash mismatch for …` for every document, registry, DAG and Lean file touched by
  Task 40
* **Diagnosis** expected: the manifests are generated artefacts and Task 40 edited the files
  they fingerprint.  The new hash check (Part VIII §16 / Part IX §18) is what made the
  mismatches visible instead of silent.
* **Repair** regenerate in the fixed order `build_axiom_audit` → `build_theorem_registry` →
  `build_module_registry` → `build_failbuild_ledger` → `build_dags` → `build_manifests`, then
  re-run the validator.  Mismatches after regeneration: **0**.
* Theorem statement changed? **NO** — assumptions changed? **NO** — source architecture
  changed? **NO** — documentation schema changed? **NO**

## F3

* **Command** `python3 audit/build_axiom_audit.py /tmp/build.log`
* **Location** `docs/machine/AXIOM_AUDIT.json`
* **Error** `wrote 62 endpoints` while the audit module contains 67 `#print axioms` lines; the
  theorem registry then marked five entries `NOT_AUDITED`
  (`smoothEmergentManifoldCertificate`, `tangentTransition_eq_derivative_baseTransition`,
  `tangent_spin_base_data_do_not_force_transition_identification`,
  `smooth_tangent_lorentz_metric`, `native_transport_knob_smoketest_certificate`).
* **Diagnosis** the first version of the new generator scanned the build log line by line, but
  Lean wraps a long axiom list across several lines, so those five records were invisible to a
  per-line regex.
* **Repair** scan the whole log text at once with `re.S`, sorting the matches by position.  The
  regenerated audit contains all 67 endpoints, `result: PASS`, every observed axiom set equal to
  `[propext, Classical.choice, Quot.sound]`.
* Theorem statement changed? **NO** — assumptions changed? **NO** — source architecture
  changed? **NO** — documentation schema changed? **NO**

## F4

* **Command** `python3 audit/verify_documentation_snapshot.py` (first run of the new
  classification checks)
* **Location** `docs/machine/PROJECT_STATE.json`, `docs/machine/OBJECT_REGISTRY.jsonl`
* **Error** the pre-Task-40 file placed ℝ³/`sip`, `q3`, `BaseGluingData`, the native Spin
  transition datum and the regular solder in a single `primitive_input` bucket, and classified
  `SmoothTangentSolderData` as `DERIVED` with no existence field
* **Diagnosis** review defects ISSUE-40-04 and the solder half of ISSUE-40-04/§10: a reader
  could infer both that the global data are primitive and that a regular solder always exists.
* **Repair** the strict six-key taxonomy (`primitive_local_input`, `derived_local_structures`,
  `additional_global_data`, `global_regularization_or_gate_data`, `derived_global_structures`,
  `control_specific_data`), the new object fields `definition_status` / `existence_status` /
  `existence_note`, the new `canonical_status` values `ADDITIONAL_GLOBAL_DATUM`, `GATE_DATA`,
  `CONTROL_MODEL`, and validator checks enforcing all of it.
* Theorem statement changed? **NO** — assumptions changed? **NO** — source architecture
  changed? **NO** — documentation schema changed? **YES** (documented in
  `docs/machine/REGISTRY_SCHEMA.md`)

## F5

* **Command** `python3 audit/verify_documentation_snapshot.py` (new declaration-kind check)
* **Location** `docs/machine/THEOREM_REGISTRY.jsonl`, entries `THM-S017`, `THM-S018`
* **Error** two registry entries declared as theorems name the Lean *definitions*
  `Task37.Deformation.loopSolderTransport` and `Task37.Deformation.loopSolderEquiv`
* **Diagnosis** review defect ISSUE-40-05: a definition was being presented as proof support
  for a scientific claim.
* **Repair** the registry gained the `declaration_kind` field (read from the source text), the
  `proof_status` of a non-proof entry is now `CONSTRUCTED` rather than `PROVED`, the theorem
  `loopSolderTransport_involutive` was registered as `THM-S021`, and the validator now requires
  every PROVED-like claim to have at least one `theorem`/`lemma` support.  `CLAIM-S010` is
  supported by `THM-S019`, `THM-S020` and `THM-S021`.
* Theorem statement changed? **NO** — assumptions changed? **NO** — source architecture
  changed? **NO** — documentation schema changed? **YES**

## F6 (metadata error found and corrected)

* **Command** `wc -l` on the four Task-39 modules, compared with `TASK39_AUDIT.md`
* **Location** `TASK39_AUDIT.md:19`
* **Error** the baseline table said `8356 jobs (three new modules)`
* **Diagnosis** review defect ISSUE-40-06: Task 39 introduced **four** new Lean modules
  (`Deformation/SmoothProjectedGauge.lean`, `Deformation/SolderTransport.lean`,
  `Closure/IntermediateMilestone.lean`, `Closure/AxiomAudit.lean`); the audit module was
  omitted from the count.
* **Repair** the line now records four modules and the per-module line counts computed from the
  current tree (144 + 265 + 271 + 114 = 794), with an inline note that it is a Task-40
  correction.  The historical text is preserved by the note rather than silently overwritten.
* Theorem statement changed? **NO** — assumptions changed? **NO** — source architecture
  changed? **NO** — documentation schema changed? **NO**

---

## Recorded source change (audit only)

* **File** `RequestProject/Spine/Closure/AxiomAudit.lean`
* **Change** five additional `#print axioms` lines: `SpinCore.gB_bracket_mem`,
  `SpinCore.gBLie_bracket`, `SpinCore.bivectorEquivSkew_wedge`, `SpinCore.finrank_gB`,
  `Task37.Deformation.loopSolderTransport_involutive`.
* **Why necessary** Task 40 registers these five already-existing declarations, and the release
  policy is that every registry endpoint is axiom-audited from a build artefact.
* **Theorem neutrality** the module proves nothing; it contains only `#print axioms` commands.
  No import was added (all five declarations are already in the transitive import closure), no
  statement was touched, and the full build still reports **8356 jobs**.
* Theorem statement changed? **NO** — assumptions changed? **NO** — source architecture
  changed? **NO** — documentation schema changed? **NO**
