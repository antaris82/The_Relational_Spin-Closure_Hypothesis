#!/usr/bin/env python3
"""Syntactic declaration/dependency analysis for the production Spine.

For every module under the given prefixes this collects

  * the fully-qualified names it declares (tracking `namespace`/`end` nesting);
  * the identifiers it mentions;

and derives, for each module, the set of *other* modules that declare a name it
mentions.  From that it computes a minimal (transitively irredundant) candidate
import set.  The analysis is syntactic and therefore approximate: it may
over-approximate (a short name shared by several modules) and it can miss
instance/notation dependencies.  It is used to *propose* narrow imports; the
Lean build is the authority.

Usage:
    python3 scripts/decl_deps.py decls            # module -> declarations
    python3 scripts/decl_deps.py needs MOD...     # proposed minimal imports
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PREFIXES = ["RequestProject/Spine"]

IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)")
NS = re.compile(r"^namespace\s+([A-Za-z0-9_.'ₓ]+)")
ENDNS = re.compile(r"^end\s+([A-Za-z0-9_.'ₓ]+)")
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?ₓ₀-₉]*)"
)
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_.'!?ₓ₀-₉]*")


def all_modules() -> list[str]:
    out = []
    for pref in PREFIXES:
        for p in sorted((ROOT / pref).rglob("*.lean")):
            out.append(str(p.relative_to(ROOT))[: -len(".lean")].replace("/", "."))
    return out


def path_of(mod: str) -> Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def parse(mod: str):
    """Return (declared fully-qualified names, mentioned identifiers, imports)."""
    text = path_of(mod).read_text()
    lines = text.splitlines()
    stack: list[str] = []
    decls: set[str] = set()
    imports: list[str] = []
    for line in lines:
        m = IMPORT.match(line)
        if m and m.group(1).startswith("RequestProject."):
            imports.append(m.group(1))
            continue
        m = NS.match(line)
        if m:
            stack.append(m.group(1))
            continue
        m = ENDNS.match(line)
        if m:
            if stack and stack[-1] == m.group(1):
                stack.pop()
            continue
        m = DECL.match(line)
        if m:
            nm = m.group(1)
            full = ".".join(stack + [nm]) if stack else nm
            decls.add(full)
            decls.add(nm)
    # strip comment lines crudely for the mention scan
    body = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    body = re.sub(r"--.*", " ", body)
    body = re.sub(r"\.\{[^}]*\}", " ", body)  # universe annotations `f.{u}`
    mentions = {t.rstrip(".") for t in IDENT.findall(body)}
    extra = set()
    for t in mentions:
        parts = t.split(".")
        for i in range(len(parts)):
            extra.add(".".join(parts[i:]))
    return decls, mentions | extra, imports


def build():
    mods = all_modules()
    info = {m: parse(m) for m in mods}
    owner: dict[str, set[str]] = {}
    for m, (decls, _, _) in info.items():
        for d in decls:
            owner.setdefault(d, set()).add(m)
    return mods, info, owner


def direct_imports(info, m):
    return info[m][2]


def closure(info, m, seen=None):
    seen = set() if seen is None else seen
    for d in direct_imports(info, m):
        if d in info and d not in seen:
            seen.add(d)
            closure(info, d, seen)
    return seen


def main():
    mods, info, owner = build()
    cmd = sys.argv[1] if len(sys.argv) > 1 else "decls"
    if cmd == "decls":
        for m in mods:
            decls = sorted(d for d in info[m][0] if "." in d)
            print(f"== {m}")
            for d in decls:
                print(f"   {d}")
        return
    if cmd == "needs":
        targets = sys.argv[2:] or mods
        for m in targets:
            _, mentions, imps = info[m]
            avail = closure(info, m)
            need = set()
            for t in mentions:
                for o in owner.get(t, ()):
                    if o != m and o in avail:
                        need.add(o)
            # transitively irredundant
            minimal = set(need)
            for n in list(need):
                for k in closure(info, n):
                    minimal.discard(k)
            print(f"== {m}")
            print(f"   current : {sorted(imps)}")
            print(f"   proposed: {sorted(minimal)}")
            drop = [i for i in imps if i not in minimal]
            if drop:
                print(f"   droppable: {sorted(drop)}")
        return
    if cmd == "missing":
        targets = sys.argv[2:] or mods
        for m in targets:
            _, mentions, _ = info[m]
            avail = closure(info, m)
            miss: dict[str, set[str]] = {}
            for t in mentions:
                own = owner.get(t, ())
                if len(t) < 8 or len(own) != 1:
                    continue  # short or ambiguous names are noise
                for o in own:
                    if o != m and o not in avail and "Spine" in o:
                        miss.setdefault(o, set()).add(t)
            if miss:
                print(f"== {m}")
                for o in sorted(miss):
                    ex = sorted(miss[o])[:4]
                    print(f"   {o}  ({len(miss[o])} names, e.g. {ex})")
        return
    if cmd == "why":
        # why does module A mention things from module B?
        a, b = sys.argv[2], sys.argv[3]
        _, mentions, _ = info[a]
        hits = sorted(d for d in info[b][0] if d in mentions and "." in d)
        print("\n".join(hits))
        return
    raise SystemExit("unknown command")


if __name__ == "__main__":
    main()
