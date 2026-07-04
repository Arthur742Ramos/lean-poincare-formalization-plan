#!/usr/bin/env python3
"""Deterministic lexical helper for the Point 4 completion audit.

This tool exists because a naive ``grep`` for ``sorry`` is unreliable: the word
also appears inside prose such as "proved sorry-free", which caused the status
pulses to flip-flop between "0 sorries" and "6 sorries" for the *same* six
docstring lines.  Everything here strips Lean comments and string literals
*first*, so the token counts reflect real code, not documentation.

Subcommands
-----------
cheats <root>
    Scan every ``*.lean`` file under ``<root>`` (after removing comments and
    string literals) for the proof-bearing cheats the Point 4 plan forbids:
    ``sorry``, ``admit``, ``sorryAx``, ``native_decide``, ``decide!`` and the
    ``axiom`` / ``opaque`` declaration keywords.  Prints one ``file:line: tok``
    per hit and a trailing ``TOTAL <n>`` line.  Exit code is the hit count
    (capped at 200) so callers can branch on zero/non-zero.

locate <base_name> <root>
    Find the declaration of ``<base_name>`` and print, tab-separated:
        FQN <tab> MODULE <tab> FILE <tab> LINE
    where FQN prepends the enclosing ``namespace`` stack and MODULE is the
    dotted import path.  Also writes the declaration's *signature text* (decl
    head up to the body ``:=`` / ``where``) to stdout after a line ``---SIG---``
    so the caller can scan it for forbidden restricting binders.  Exits 0 if
    found, 3 if not found.
"""
from __future__ import annotations

import os
import re
import sys


# --- comment / string aware stripping -------------------------------------

def strip_comments(text: str) -> list[str]:
    """Return the source as a list of lines with all comment and string-literal
    content replaced by spaces (preserving line count and column positions).

    Handles nested ``/- -/`` block comments (Lean doc comments ``/-- -/`` start
    with ``/-`` so they are covered), ``--`` line comments, and ``"..."`` string
    literals with ``\\`` escapes.  Char literals are intentionally *not* treated
    as delimiters (the prime ``'`` is overloaded as an identifier character in
    Lean, so swallowing on ``'`` would be far more dangerous than ignoring it).
    """
    out: list[list[str]] = [[]]
    i, n = 0, len(text)
    state = "code"          # code | line | block | string
    depth = 0               # block-comment nesting depth
    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if c == "\n":
            out.append([])
            if state == "line":
                state = "code"
            i += 1
            continue
        if state == "code":
            if c == "-" and nxt == "-":
                state = "line"
                out[-1].append("  ")
                i += 2
                continue
            if c == "/" and nxt == "-":
                state = "block"
                depth = 1
                out[-1].append("  ")
                i += 2
                continue
            if c == '"':
                state = "string"
                out[-1].append(" ")
                i += 1
                continue
            out[-1].append(c)
            i += 1
            continue
        if state == "line":
            out[-1].append(" ")
            i += 1
            continue
        if state == "block":
            if c == "/" and nxt == "-":
                depth += 1
                out[-1].append("  ")
                i += 2
                continue
            if c == "-" and nxt == "/":
                depth -= 1
                out[-1].append("  ")
                i += 2
                if depth == 0:
                    state = "code"
                continue
            out[-1].append(" " if c != "\t" else "\t")
            i += 1
            continue
        if state == "string":
            if c == "\\":
                out[-1].append("  ")
                i += 2
                continue
            if c == '"':
                state = "code"
            out[-1].append(" ")
            i += 1
            continue
    return ["".join(row) for row in out]


IDENT = re.compile(r"[A-Za-z0-9_'!?]")


def _iter_lean_files(root: str):
    for dirpath, dirnames, filenames in os.walk(root):
        # skip build / vcs dirs
        dirnames[:] = [d for d in dirnames if d not in (".lake", ".git", "build")]
        for fn in filenames:
            if fn.endswith(".lean"):
                yield os.path.join(dirpath, fn)


# Tokens that indicate an unfinished / unsound proof or an added assumption.
# Plain ``decide`` is sound (kernel-checked) and therefore allowed; only the
# ``decide!`` and ``native_decide`` variants are flagged.
WORD_CHEATS = ["sorry", "admit", "sorryAx", "native_decide"]
DECL_KW_CHEATS = ["axiom", "opaque"]  # only when they open a declaration


def _standalone(line: str, tok: str, start: int) -> bool:
    before = line[start - 1] if start > 0 else " "
    after_idx = start + len(tok)
    after = line[after_idx] if after_idx < len(line) else " "
    return not IDENT.match(before) and not IDENT.match(after)


def cmd_cheats(root: str) -> int:
    hits = 0
    for path in sorted(_iter_lean_files(root)):
        try:
            with open(path, encoding="utf-8") as fh:
                raw = fh.read()
        except (OSError, UnicodeDecodeError):
            continue
        lines = strip_comments(raw)
        for lineno, line in enumerate(lines, 1):
            for tok in WORD_CHEATS:
                idx = line.find(tok)
                while idx != -1:
                    if _standalone(line, tok, idx):
                        print(f"{path}:{lineno}: {tok}")
                        hits += 1
                    idx = line.find(tok, idx + 1)
            stripped = line.lstrip()
            # allow leading attributes like `@[simp] axiom` — re-lstrip after ']'
            head = stripped
            if head.startswith("@["):
                close = head.find("]")
                if close != -1:
                    head = head[close + 1:].lstrip()
            for kw in DECL_KW_CHEATS:
                if head.startswith(kw) and (len(head) == len(kw) or not IDENT.match(head[len(kw)])):
                    print(f"{path}:{lineno}: {kw}")
                    hits += 1
            # `decide!` (bang variant)
            idx = line.find("decide!")
            while idx != -1:
                before = line[idx - 1] if idx > 0 else " "
                if not IDENT.match(before):
                    print(f"{path}:{lineno}: decide!")
                    hits += 1
                idx = line.find("decide!", idx + 1)
    print(f"TOTAL {hits}")
    return min(hits, 200)


DECL_KW = r"(?:noncomputable\s+)?(?:private\s+|protected\s+|public\s+)?(?:theorem|lemma|def|abbrev|instance)"


def _namespace_stack(lines: list[str], target_line: int) -> list[str]:
    """Compute the enclosing ``namespace`` stack at ``target_line`` (1-based)."""
    stack: list[tuple[str, str]] = []  # (kind, name); kind in {ns, sec}
    for lineno, line in enumerate(lines, 1):
        if lineno >= target_line:
            break
        s = line.strip()
        m = re.match(r"^namespace\s+([\w.]+)", s)
        if m:
            for part in m.group(1).split("."):
                stack.append(("ns", part))
            continue
        m = re.match(r"^section\b\s*([\w.]*)", s)
        if m:
            stack.append(("sec", m.group(1) or ""))
            continue
        m = re.match(r"^end\b\s*([\w.]*)", s)
        if m:
            name = m.group(1)
            if not name:
                if stack:
                    stack.pop()
            else:
                # pop entries matching the (possibly dotted) end name
                parts = name.split(".")
                for _ in parts:
                    if stack:
                        stack.pop()
            continue
    return [nm for kind, nm in stack if kind == "ns"]


LIB_ROOT = "PoincareCurvature"


def _module_of(path: str, root: str) -> str:
    # Anchor the module name at the library root component so the result is a
    # valid import path (``PoincareCurvature.Foo.Bar``) regardless of the scan
    # root that was passed in.
    parts = os.path.normpath(os.path.abspath(path)).split(os.sep)
    if LIB_ROOT in parts:
        parts = parts[parts.index(LIB_ROOT):]
    else:
        parts = [os.path.relpath(path, root)]
    mod = ".".join(parts)
    return mod[:-5] if mod.endswith(".lean") else mod


def cmd_locate(base: str, root: str) -> int:
    decl_re = re.compile(rf"^\s*{DECL_KW}\s+{re.escape(base)}\b")
    for path in sorted(_iter_lean_files(root)):
        try:
            with open(path, encoding="utf-8") as fh:
                raw = fh.read()
        except (OSError, UnicodeDecodeError):
            continue
        code = strip_comments(raw)
        for lineno, line in enumerate(code, 1):
            if decl_re.match(line):
                ns = _namespace_stack(code, lineno)
                fqn = ".".join(ns + [base]) if ns else base
                module = _module_of(path, root)
                print(f"{fqn}\t{module}\t{path}\t{lineno}")
                # emit signature text: decl head up to the *top-level* body
                # marker (`:=` or `where` at bracket depth 0). Named arguments
                # like `(M := M)` and return-type `(E := F)` sit at depth > 0 and
                # must NOT be mistaken for the body start.
                sig: list[str] = []
                depth = 0
                done = False
                for j in range(lineno - 1, min(lineno - 1 + 800, len(code))):
                    cur = code[j]
                    sig.append(cur)
                    k = 0
                    while k < len(cur):
                        ch = cur[k]
                        if ch in "([{":
                            depth += 1
                        elif ch in ")]}":
                            depth = max(0, depth - 1)
                        elif depth == 0 and cur[k:k + 2] == ":=":
                            done = True
                            break
                        elif (depth == 0 and cur[k:k + 5] == "where"
                              and (k == 0 or not IDENT.match(cur[k - 1]))
                              and (k + 5 >= len(cur) or not IDENT.match(cur[k + 5]))):
                            done = True
                            break
                        k += 1
                    if done:
                        break
                print("---SIG---")
                print("\n".join(sig))
                return 0
    return 3


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__)
        return 2
    cmd = argv[1]
    if cmd == "cheats":
        root = argv[2] if len(argv) > 2 else "."
        return cmd_cheats(root)
    if cmd == "locate":
        if len(argv) < 4:
            print("usage: point4_scan.py locate <base_name> <root>", file=sys.stderr)
            return 2
        return cmd_locate(argv[2], argv[3])
    print(f"unknown subcommand: {cmd}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
