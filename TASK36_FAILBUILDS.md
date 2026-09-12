# TASK 36 — failed-build provenance

Every failed build of the Task-36 adversarial battery, in chronological order.  Nothing in
this file is ever deleted after a green build.

Frozen Task-35 baseline: commit `a3e3e7a` ("Initial commit" of this working tree), full build
`lake build RequestProject` = **8327 jobs, green**, architecture audit passing, principal
Task-35 endpoints audited to `[propext, Classical.choice, Quot.sound]`.

---

## FB-36-01

* command: `lake build RequestProject.Spine.Task36.LoopModel`
* file/line: `RequestProject/Spine/Task36/LoopModel.lean:230`, `:235` (`mapsTo_φb`)
* error: `Tactic 'rewrite' failed: Did not find an occurrence of the pattern` when rewriting
  `wrap_fst` / `unwrap_fst` inside an anonymous-constructor proof of slab membership.
* diagnosis: membership in `slab a b` is membership in a preimage of `Set.Ioo`; the
  conjunction was not exposed, so the rewrite target `(wrap t x).1` was not present
  syntactically.
* repair: go through the membership characterisation `Task36.mem_slab` before rewriting.
* statement changed: no.  assumptions changed: no.  architecture changed: no.

## FB-36-02

* command: `lake build RequestProject.Spine.Task36.LoopModel`
* file/line: `RequestProject/Spine/Task36/LoopModel.lean:266–267` (`φb_cocycle`)
* error: `Application type mismatch: ... hy : y ∈ Wb true false but is expected to have type
  y ∈ Wb true true`.
* diagnosis: the two `cases`-generated goals `(true, false, false)` and `(true, false, true)`
  were addressed in the wrong order; the bullets were swapped.
* repair: swap the two bullets.
* statement changed: no.  assumptions changed: no.  architecture changed: no.

## FB-36-03

* command: `lake build RequestProject.Spine.Task36.LoopModel`
* file/line: `RequestProject/Spine/Task36/LoopModel.lean:418`, `:435`
  (`tangentTransitionMap_wrap`, `tangentTransitionMap_overlap`)
* error: `Type mismatch: Eq.symm (φb_ft_of_lt t hz.right) has type wrap t z = φb t false true z
  but is expected to have type φb t false true z = wrap t z`.
* diagnosis: `HasFDerivAt.congr_of_eventuallyEq` takes the eventual equality in the direction
  `f₁ =ᶠ f`, i.e. the *new* function on the left; the `.symm` was superfluous.
* repair: drop `.symm`.
* statement changed: no.  assumptions changed: no.  architecture changed: no.

## FB-36-04

* command: `lake build RequestProject.Spine.Task36.OrientationReversing`
* file/line: `RequestProject/Spine/Task36/OrientationReversing.lean:58`, `:60`, `:86`, `:93`
* error: `unsolved goals` in the slab-membership witnesses of the two test points, and
  `unexpected token '·'` in a `cases ... with` block.
* diagnosis: `norm_num` cannot see through the definitions `pWrap`, `pOver` to their first
  coordinate; and the `cases p with | mk n b => cases b` layout was not valid tactic syntax.
* repair: add the projection lemmas `pWrap_fst`, `pOver_fst` and rewrite with them; replace
  the `cases ... with` block by `obtain ⟨-, b⟩ := p; cases b`.
* statement changed: no.  assumptions changed: no.  architecture changed: no.

## FB-36-05

* command: `lake build RequestProject.Spine.Task36.OrientationReversing`
* file/line: `RequestProject/Spine/Task36/OrientationReversing.lean:131`, then `:139`
* error: `Tactic 'rewrite' failed: Did not find an occurrence of the pattern
  (loopGluingOf Unit ?t).φ ((), false) ((), true) pOver`.
* diagnosis: `moebiusGluing` is definitionally `loopGluingOf Unit LoopTwist.flip` but not
  syntactically; `rw` matches syntactically.
* repair: state each specialised fact as a `have` whose type mentions `moebiusGluing`
  (elaboration closes the definitional gap), then rewrite with that `have`.
* statement changed: no.  assumptions changed: no.  architecture changed: no.

## FB-36-06

* command: `lake build RequestProject.Spine.Task36.SpinFoamControl`
* file/line: `RequestProject/Spine/Task36/SpinFoamControl.lean:101`
* error: `Unknown identifier 'oneChartGluing_isManifold'`, `Unknown identifier
  'oneChartSolder'` (and the resulting `sorryAx` in the axiom audit of the same declaration,
  which is the elaborator's error recovery, not a `sorry` in the source).
* diagnosis: the new module imported only `RequestProject.Spine.Task36.SpinNotLorentz`, whose
  closure reaches `Task36.OrientationReversing` but not `Task36.TrivialControl`, where the
  one-chart positive control lives.
* repair: add `import RequestProject.Spine.Task36.TrivialControl`.
* statement changed: no.  assumptions changed: no.  architecture changed: no (both modules are
  on the bottom-up side of the Task-36 firewall).

## FB-36-07

* command: `lake build RequestProject.Spine.Task36.Firewall`
* file/line: `RequestProject/Spine/Task36/TrivialControl.lean:63`
* error: `unexpected token 'omit'; expected 'lemma'`.
* diagnosis: the linter repair `omit [IsTopologicalGroup L] in` had been inserted *between*
  the doc comment and the `theorem`; a doc comment must be immediately followed by the
  declaration.
* repair: move the `omit ... in` line above the doc comment.
* statement changed: no.  assumptions changed: no (`IsTopologicalGroup L` was an unused
  automatically included section variable).  architecture changed: no.
