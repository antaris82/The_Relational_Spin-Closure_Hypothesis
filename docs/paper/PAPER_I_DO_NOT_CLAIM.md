# PAPER I — sentences that must NOT be written

This file is part of the scientific result, not an embarrassment.  Each entry gives a sentence
that the project's mathematics does **not** support, the reason, and the strongest statement
that *is* supported.

Claim IDs refer to `docs/machine/CLAIM_REGISTRY.jsonl`.

---

### 1. "Gravity has been derived."
**Why not.** No field equation, no action principle, no dynamics of any kind exists in the
repository [CLAIM-B008].
**Instead.** A smooth Lorentzian tangent geometry is *constructed* in the regular-solder sector
[CLAIM-G009].  Geometry is not dynamics.

### 2. "The Einstein equations have been derived."
**Why not.** Same reason; there is no curvature object to write them with [CLAIM-B003],
[CLAIM-B008].
**Instead.** Nothing. Do not mention Einstein equations except to say they are absent.

### 3. "Curvature emerges from Spin transport."
**Why not.** There is no transport one-form, no field strength and no Riemann tensor in the
project; the deformation-branch firewall forbids even *naming* a declaration after such an
object [CLAIM-B003].
**Instead.** The first tested transition-level knob is gauge-absorbable on the tested control
[CLAIM-S011], which is why a transport layer is the next research direction [CLAIM-B009].

### 4. "All four-manifolds admit the native solder."
**Why not.** The Möbius-type control admits **no** regular solder for **any** native Spin datum
[CLAIM-G017], [CLAIM-N003], and there is no general existence theorem [CLAIM-B007].
**Instead.** A regular solder is a gate; all solder-dependent theorems are conditional.

### 5. "w₁(TM) = w₂(TM) = 0 has been proved."
**Why not.** The project proves orientation compatibility of the emergent atlas and triviality
of a **project-native fixed-cover kernel-valued** obstruction class.  No Stiefel–Whitney class,
no `H²(M; ℤ/2)` and no comparison theorem exists in this repository [CLAIM-B002], `OP-006`.
**Instead.** "A regular solder forces project-native orientation compatibility and triviality of
the project-native Spin-lifting obstruction" [CLAIM-G011], [CLAIM-G013].

### 6. "Every transition-cocycle deformation is pure gauge."
Equivalently forbidden: "a transition-cocycle deformation is a change of trivialisation, not a
change of geometry".
**Why not.** The result is about **one** family on **one** control base with a two-component
periodic overlap that leaves interpolation room.  Nothing is proved for other bases, other
covers, co-varying bases or other families [CLAIM-S004], [CLAIM-S011], `OP-007`, `OP-008`.
A general Čech-deformation classification is NOT PROVED.
**Instead.** Use the scoped wording of §7 of `PAPER_I_FACT_SHEET.md`:

> The specific Task-37 native one-parameter Spin Čech-transition deformation on the frozen
> periodic fixed-cover control base lies in one full-Spin Čech gauge orbit for all finite λ;
> on that control the regular solder solution spaces for λ₁ and λ₂ are related by the certified
> transport, and the induced tangent Lorentz metric is preserved under that correspondence.

### 7. "The Task-38 parameter λ is a curvature."
**Why not.** λ parameterizes a one-parameter subgroup of the intrinsic Spin group
[CLAIM-L010]; the project has no curvature to compare it with [CLAIM-B003].
**Instead.** "λ is the parameter of the native one-parameter Spin subgroup generating the tested
transition deformation."

### 8. "Positive/negative λ means positive/negative curvature."
**Why not.** Same reason, plus the fact that admissibility is symmetric in the sign for purely
group-theoretic reasons [CLAIM-S003].
**Instead.** "−λ is the opposite direction along the same one-parameter subgroup."

### 9. "A Spin connection or a holonomy functional is already present."
**Why not.** Neither exists [CLAIM-B003]; `transportState` is a group element, not a transport
operator, and `paraMap` is the computed value of an already certified projection.
**Instead.** List them as the next layer, `OP-002` … `OP-004`.

### 10. "The fixed-cover loop model is homeomorphic to S¹ × ℝ³."
**Why not.** No such homeomorphism, and no statement about the fundamental group, is proved or
used anywhere [CLAIM-B004], `OP-009`.  Earlier drafts used this wording; it was corrected.
**Instead.** "The frozen periodic control base has a fixed cover with a two-component periodic
overlap, one component of which is a wrap-around" [CLAIM-G022].

### 11. "The Spin cocycle gauge of the smoke test is smooth."
**Why not.** The intrinsic `SpinGroup` carries no smooth structure [CLAIM-B001]; only the
**projected** Lorentz gauge has been proved `C^∞` [CLAIM-S009].
**Instead.** "The Spin-side gauge is continuous; its native projection is `C^∞` on every chart
domain."

### 12. "The regular solder gives a smooth bundle equivalence with TM."
**Why not.** The certified equivalence has continuous total-space maps and `C^∞` *local
representatives* [CLAIM-G008].  A stronger total-space smooth vector-bundle-equivalence package
is not available for an **infrastructure / packaging** reason: the pinned Mathlib has no
vector-bundle morphism or equivalence type, and `VectorBundleCore.IsContMDiff` is stated over
the base manifold while the solder supplies `ContDiffOn` in chart coordinates
(`RequestProject/Spine/Task36/SmoothBundlePackaging.lean`).
**Instead.** State the regularity exactly, as in `PAPER_I_FACT_SHEET.md` §4.

### 12b. "A smooth Lorentz bundle equivalence is blocked because the native Spin cocycle is only continuous."
**Why not.** This is the obsolete Task-35 causal explanation; it was corrected in Task 36 and
must not be reintroduced.  A regular smooth solder already gives smooth local/projected Lorentz
transition representatives (`SmoothTangentSolderData.contDiffOn_solderLorentzRep`,
`Task36.internal_bundle_coordChange_smooth_in_charts`), so smoothness of the native Spin cocycle
is **not** required merely to obtain smooth projected Lorentz bundle data.  The remaining
limitation is the infrastructure/packaging one of entry 12.
**Instead.** "Smooth projected Lorentz data is certified; the strong total-space packaging is
blocked by infrastructure."  And keep the two apart: smooth projected Lorentz data is **not** a
fully packaged smooth intrinsic Spin Lie-group bundle theory, and neither is evidence for the
other [CLAIM-B001].

### 13. "The emergent manifold is time orientable."
**Why not.** What is proved is a coherent chartwise future-cone reduction in the project's own
sense; no comparison with the standard notion exists [CLAIM-B006], `OP-010`.
**Instead.** "A regular solder yields a project-native future-cone reduction."

### 14. "The construction computes H¹(M; ℤ/2) of the emergent manifold."
**Why not.** The multiplicity results are fixed-cover statements; no refinement limit is taken
[CLAIM-B005].
**Instead.** "On the fixed cover of the N-loop control there are 2^N gauge-inequivalent native
Spin data, instantiated at N = 2" [CLAIM-G019].

### 15. "The construction canonizes the Spin structure."
**Why not.** The discrete lift freedom survives, by explicit control [CLAIM-G018],
[CLAIM-N005].
**Instead.** Say that the bottom-up route does *not* remove the freedom — that is the result.

### 16. "The project has no Lie algebra."
**Why not.** It does: `SpinCore.gB` / `SpinCore.gBLie`, a six-dimensional real Lie algebra of
endomorphisms skew for the intrinsic form `BS`, linearly equivalent to `⋀[ℝ]^2 LorentzCarrier`
[CLAIM-L011], THM-L012 … THM-L015.  Earlier drafts of the transport handoff said otherwise; that
was wrong and is withdrawn.
**Instead.** "The intrinsic Lorentz sector carries a six-dimensional Lorentz-skew Lie-algebra
realization; what is missing is its relation to the infinitesimal structure of the intrinsic
`SpinGroup`."

### 17. "`gB` is the Lie algebra of the intrinsic `SpinGroup`."
**Why not.** No smooth or Lie-group structure on `SpinGroup` exists [CLAIM-B001], there is no
`Lie(SpinGroup)` object in the repository, and no equivalence with `gB` is proved
[CLAIM-B010], `OP-001`, `OP-012`.  Textbook facts about `Lie(Spin(1,3))` are not formalized
here and must not be cited as if they were.
**Instead.** "Identifying the infinitesimal structure of the intrinsic `SpinGroup` with
`gB`/`gBLie` is the first open edge of the next phase."

### 18. "The Lorentz connection is `spinCover ∘ ω`."
**Why not.** `spinCover : SpinGroup →* GLor` is a **group-level** homomorphism; a connection
one-form is Lie-algebra valued, so the composite is not even type-correct.  The required
differential `dρ_e` does not exist in the repository [CLAIM-B011], `OP-012`.
**Instead.** "Once the intrinsic infinitesimal Spin/Lorentz structures are related, the
Lorentz-side connection must be induced through the differential of the native Spin cover, or
through an explicitly proved equivalent infinitesimal representation."  This is a future
architectural requirement, not a current theorem.

### 19. "A regular solder always exists / solder existence is derived."
**Why not.** `SmoothTangentSolderData` is an additional global gate datum: its *type* is
constructed, but its *inhabitance* is not derived and can fail [CLAIM-B007], [CLAIM-G017],
`OP-011`.  The machine-readable registry classifies it as `GATE_DATA` for exactly this reason.
**Instead.** "Every solder-dependent statement of this project is conditional on a regular
solder being given."

### 19b. "`transportState` is the unique / canonical native Spin deformation."
**Why not.** The Task-37/38 family is a deliberately **selected** one-parameter subgroup,
generated by the chosen Clifford direction `cle 0`
(`transportElem l = cosh(l/2) + sinh(l/2) · cle 0`,
`RequestProject/Spine/Deformation/SharedTransport.lean`).  No theorem says that `cle 0` is
canonically selected by the primitive Euclidean input, that the family is unique, or that it
exhausts the native Spin deformation directions [CLAIM-L010] (`canonical_status:
SELECTED_CONTROL`, `exhaustive: false`).
**Instead.** "The Task-37/38 deformation is a deliberately selected one-parameter subgroup
generated by the chosen Clifford direction `cle 0`.  It is a control slice through the intrinsic
Spin structure, not a theorem that this direction is canonical, exhaustive, or the full
deformation space."

### 19c. "The Task-38 result classifies the full Spin deformation space / applies to every native Spin deformation."
**Why not.** The pure-gauge outcome is proved for the selected `cle 0` family on the frozen
periodic fixed-cover control and for nothing else [CLAIM-S011], [CLAIM-L010]; a general
Čech-deformation classification is not proved.
**Instead.** "On that control, the selected `cle 0` transition-cocycle family lies in one
full-Spin Čech gauge orbit and leaves the induced tangent metric unchanged."

### 20. "The smoke test proves that the transition layer is physically irrelevant."
**Why not.** It proves gauge absorbability on one control, and it says nothing about other
layers, other bases or physics [CLAIM-S011], `OP-007`.
**Instead.** "On the tested control the transition-cocycle knob has no closure-selection power
and leaves the induced tangent metric unchanged."
