"""Minimal, deliberately dumb extraction of a Lean declaration's statement text.

Used by `audit/build_theorem_registry.py` so that the `statement_text` field of
`docs/machine/THEOREM_REGISTRY.jsonl` is *copied from the source file* rather than
rewritten from memory.

The extractor is intentionally not a Lean parser.  It finds the line that starts the
declaration (``theorem <name>``, ``def <name>``, ``structure <name>`` possibly preceded by
``noncomputable``/``private``/``protected``) and returns the text up to, but not including,
the proof/definition separator ``:=`` or the trailing `` by`` at the end of a line, whichever
comes first at bracket depth zero.  If it cannot do that safely it returns the raw lines and
lets the caller decide; the validator only checks that the declaration name occurs in the
declared file.

Task-41 repair (ISSUE-41-03).  A ``:=`` at bracket depth zero is *not* always the body
delimiter: the result type of a declaration may itself contain a term-level binder such as

    theorem foo ... :
        haveI : IsManifold localModelI 1 (Space B) := <instance term>
        <the actual conclusion> := by

Every such binder (``have``, ``haveI``, ``let``, ``letI``, ``suffices``) consumes exactly one
following ``:=`` that belongs to the *type*, not to the body.  The scanner therefore counts
the depth-zero binder keywords it has passed and skips that many depth-zero ``:=`` tokens
before accepting one as the body delimiter.  This is structural scanning only: no Lean parser,
no new dependency, and no semantic reading of proof bodies.
"""

from __future__ import annotations

import re
from pathlib import Path

_OPENERS = "([{⟨"
_CLOSERS = ")]}⟩"

# Term-level binders that may legally occur inside a declaration's *type* and that each
# introduce one ``:=`` which must not be mistaken for the body delimiter.
_TYPE_BINDER_RE = re.compile(r"(?:have|haveI|let|letI|suffices)\b")
_IDENT_CHARS = set(
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'!?.")

_DECL_RE = r"^(?:noncomputable\s+)?(?:private\s+|protected\s+)?(?:theorem|lemma|def|structure|abbrev|instance)\s+{name}\b"

_KIND_RE = r"^(?:noncomputable\s+)?(?:private\s+|protected\s+)?(theorem|lemma|def|structure|abbrev|instance)\s+{name}\b"

DECLARATION_KINDS = {"theorem", "lemma", "definition", "structure", "abbreviation", "instance"}

_KIND_NAMES = {"theorem": "theorem", "lemma": "lemma", "def": "definition",
               "structure": "structure", "abbrev": "abbreviation", "instance": "instance"}


def declaration_kind(path: Path, short_name: str) -> str:
    """Return the declaration kind of `short_name` in `path`.

    A conservative source-text check, not a Lean parser: it reads the keyword that opens the
    declaration line.  Raises `KeyError` if no such declaration line exists.
    """
    pattern = re.compile(_KIND_RE.format(name=re.escape(short_name)))
    for line in path.read_text(encoding="utf-8").splitlines():
        m = pattern.match(line)
        if m:
            return _KIND_NAMES[m.group(1)]
    raise KeyError(f"declaration {short_name} not found in {path}")


def find_declaration_line(path: Path, short_name: str) -> int | None:
    """Return the 0-based index of the line declaring `short_name`, or None."""
    pattern = re.compile(_DECL_RE.format(name=re.escape(short_name)))
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines()):
        if pattern.match(line):
            return i
    return None


def extract_statement(path: Path, short_name: str) -> str:
    """Return the source text of the statement of `short_name` in `path`."""
    lines = path.read_text(encoding="utf-8").splitlines()
    start = find_declaration_line(path, short_name)
    if start is None:
        raise KeyError(f"declaration {short_name} not found in {path}")
    depth = 0
    pending_binders = 0  # depth-0 have/let/suffices whose ``:=`` still has to be skipped
    out: list[str] = []
    for line in lines[start:]:
        cut = None
        j = 0
        n = len(line)
        while j < n:
            ch = line[j]
            if ch in _OPENERS:
                depth += 1
            elif ch in _CLOSERS:
                depth -= 1
            elif depth == 0 and line.startswith("--", j):
                break  # a line comment: nothing after it belongs to the statement
            elif depth == 0 and line.startswith(":=", j):
                if pending_binders:
                    pending_binders -= 1
                    j += 2
                    continue
                cut = j
                break
            elif depth == 0 and (j == 0 or line[j - 1] not in _IDENT_CHARS):
                m = _TYPE_BINDER_RE.match(line, j)
                if m and (m.end() >= n or line[m.end()] not in _IDENT_CHARS):
                    pending_binders += 1
                    j = m.end()
                    continue
            j += 1
        if cut is not None:
            piece = line[:cut].rstrip()
            if piece:
                out.append(piece)
            break
        stripped = line.rstrip()
        if depth == 0 and pending_binders == 0 and stripped.endswith(" by"):
            out.append(stripped[: -len(" by")].rstrip())
            break
        out.append(stripped)
        if len(out) > 120:
            break
    return "\n".join(out).strip()


# --------------------------------------------------------------------------------------
# Task-41 (ISSUE-41-03): conservative sanity checks on an extracted statement.
# --------------------------------------------------------------------------------------

# Declarations whose extraction is known to have been truncated before Task 41, together with
# the terminal text their statement must contain.  This is the mandatory regression case.
REGRESSION_TERMINALS = {
    "tangentTransition_eq_derivative_baseTransition": "= B.tangentTransitionMap i j y",
}


def statement_problems(path: Path, short_name: str, statement: str) -> list[str]:
    """Return a list of problems with `statement` as the statement of `short_name` in `path`.

    Conservative, purely structural checks — no Lean parsing, no mathematical reconstruction:

    * the statement is nonempty;
    * it opens with the declaration keyword and the declared name;
    * every one of its lines occurs in the declared source file (it belongs to that file);
    * a theorem/lemma statement extends beyond its declaration header, i.e. it contains the
      `:` that opens the result type;
    * a known regression declaration contains its expected terminal conclusion.
    """
    problems: list[str] = []
    if not statement.strip():
        problems.append("empty statement_text")
        return problems
    first = statement.splitlines()[0]
    if not re.match(_DECL_RE.format(name=re.escape(short_name)), first):
        problems.append(f"statement_text does not open with the declaration of {short_name}")
    source = path.read_text(encoding="utf-8")
    for line in statement.splitlines():
        if line.strip() and line not in source:
            problems.append(f"extracted line is not present in {path.name}: {line.strip()[:60]}")
            break
    kind = declaration_kind(path, short_name)
    if kind in {"theorem", "lemma"}:
        header_end = re.match(_DECL_RE.format(name=re.escape(short_name)), first)
        rest = statement[header_end.end():] if header_end else statement
        if ":" not in rest:
            problems.append("theorem statement does not extend beyond the declaration header")
    terminal = REGRESSION_TERMINALS.get(short_name)
    if terminal is not None and terminal not in statement:
        problems.append(f"regression declaration {short_name} is truncated: it must contain "
                        f"{terminal!r}")
    return problems


def extraction_status(path: Path, short_name: str, statement: str) -> str:
    """`OK` if the extracted statement passes the conservative checks, else `UNRELIABLE`."""
    return "OK" if not statement_problems(path, short_name, statement) else "UNRELIABLE"
