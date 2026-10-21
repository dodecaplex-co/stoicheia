#!/usr/bin/env python3
"""Check that every theorem brief 0009's restriction section names has a statement pin.

    python3 -I scripts/check_superposition_pins.py
    python3 -I scripts/check_superposition_pins.py --brief FILE --audit FILE --library FILE

The section is the one headed "## The restriction theorem" in
docs/briefs/0009-superposition.md, up to the next heading of its level or above. Each
name in backticks there, one Lean identifier, dotted or not, must have a statement pin in
Audit/Superposition.lean, under its full name: the name in `Elements.Superposition`, where
the restriction's theorems are, or else in `Elements.BookI`, as the brief writes I.4's and
I.8's. A statement pin is an `info:` docstring whose first line names the declaration,
then a bare `#guard_msgs in`, then `#check @<full name>`, or for a definition `#print
<full name>`. An axiom pin, `#print axioms`, is not a statement pin: a weaker statement
under the same name can keep its axioms. `lake build Audit` checks that each pin's
docstring is what Lean prints; this script checks that the pins exist, and that the audit
file holds nothing else, so that no option or declaration in it can change what a pin
prints or which declaration it names.

So the audit file may hold only its leading `import` lines, one module each; comments,
`--`, `/- … -/` and the module doc `/-! … -/`; and pins, each a docstring `/-- … -/`, then
a bare `#guard_msgs in`, then `#check @<name>`, `#print <name>` or `#print axioms <name>`,
and nothing more. Anything else is refused, with its line: a `set_option` of any kind
(`pp.deepTerms`, `pp.oneline` and `pp.maxSteps` shorten what Lean prints, and a docstring
that matches a shortened statement pins almost nothing); `namespace`, `section`, `open`
and `end` (in a namespace, a new declaration can take a pinned name); any declaration;
`#eval`; `#exit`; and a `#guard_msgs` with options, such as `(substring := true)`,
`(drop info)` or `(whitespace := lax)`, which let a message pass that is not the
docstring. A name pinned only under such options is also reported with that pin's line.
The file is read as Lean reads it: a pin inside a comment, nested as Lean nests them, is
not run, and is not counted. And Audit.lean, the root that `lake build Audit` builds,
must import `Audit.Superposition` among its leading imports: without it, that build does
not run the pins at all.

Not checked, since they are not names of theorems:

* `Rule.infer`, the locked rule's field, whose statement Certificate/axioms.lock pins;
  `Metric`, a type; and `cite`, a constructor of `Derives`;
* file names, with a `/` or a file suffix such as `.lean`;
* Lean's own axioms, `propext`, `Classical.choice` and `Quot.sound`;
* a single letter, which is a variable; and anything in backticks that is not one
  identifier, such as `Rule I` or `∀ c ∈ cites, c.Holds I`.

Fenced code in the section is skipped. Exits 0 when every name is pinned, the audit file
holds nothing else and Audit.lean imports it; 1 otherwise, printing `FILE:LINE: `name`
has no statement pin in AUDIT` for each name not pinned, `AUDIT:LINE: `…` is not a
leading import, a comment or a pin` for each line refused, and a line naming Audit.lean
if it does not import the audit file; 2 when the brief, its section, the audit file or
Audit.lean cannot be read, or when the section names no theorem at all, which means it
was misread. Standard library only.
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BRIEF = Path("docs/briefs/0009-superposition.md")
AUDIT = Path("Audit/Superposition.lean")
# The root of the `Audit` library, which `lake build Audit` builds with what it imports;
# it must import the audit file's module.
LIBRARY = Path("Audit.lean")
MODULE = ".".join(AUDIT.with_suffix("").parts)
HEADING = "## The restriction theorem"
# The namespaces the brief writes names in, in the order they are tried: each gives a full
# name, and a name is pinned only when one of these full names is.
NAMESPACES = ("Elements.Superposition", "Elements.BookI")

# Not names of theorems (see the module docstring).
ALLOWED = {"Rule.infer", "Metric", "cite"}
LEAN_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FILE_SUFFIX = re.compile(r"\.(lean|md|lock|toml|py|json|txt|sh|yml|yaml)$")

# One Lean identifier: letters, digits, `_`, `'`, `!`, `?` and subscripts, in dotted
# parts that do not start with a digit.
_PART = r"[^\W\d][\w'!?₀-₉]*"
IDENTIFIER = re.compile(rf"{_PART}(?:\.{_PART})*")
NAME_END = r"(?![\w.'!?₀-₉])"
CODE_SPAN = re.compile(r"`([^`\n]+)`")
FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})")
HEADING_LINE = re.compile(r"^ {0,3}(#{1,6})[ \t]")

# What follows a pin's docstring: `#guard_msgs`, any options, `in`, then `#check @name` or
# `#print name`, but never `#print axioms name`.
GUARDED = re.compile(
    r"\s*#guard_msgs(?P<options>(?:\s*\([^)]*\))*)\s+in\s+"
    r"(?:#check\s+@(?P<check>\S+)|#print\s+(?!axioms\b)(?P<print>\S+))")
# The first line of the docstring, which must name the declaration: `@name :` or `name :`
# for `#check`, `def name`, `structure name` and the like for `#print`.
KEYWORD = r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*" \
          r"(?:def|theorem|structure|class|inductive|abbrev|opaque|instance)\s+"
EXIT = re.compile(r"(?<![\w#])#exit(?![\w'!?])")
# What the audit file may hold besides comments and docstrings: its leading imports, one
# module each, and after each docstring one pin, a bare `#guard_msgs in` over `#check @name`,
# `#print name` or `#print axioms name`.
IMPORT = re.compile(rf"\s*import[ \t]+(?P<module>{IDENTIFIER.pattern}){NAME_END}")
PIN = re.compile(r"\s*#guard_msgs\s+in\s+"
                 rf"(?:#check\s+@|#print\s+axioms\s+|#print\s+(?!axioms{NAME_END}))"
                 rf"{IDENTIFIER.pattern}{NAME_END}")
# What Lean reads whole in code: a raw string `r"…"` or `r#"…"#`, closed by `"` and as many
# `#`, and a character literal such as `'"'` or `'\n'`, neither inside a name.
NAME_CHAR = re.compile(r"[\w'!?₀-₉.]")
RAW_STRING = re.compile(r'r(#*)"')
CHAR_LITERAL = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'")


class Unreadable(Exception):
    """The brief, its section, the audit file or Audit.lean cannot be read."""


def section(text: str, heading: str = HEADING) -> list[tuple[int, str]]:
    """The section's lines, numbered from 1 in the whole file, fenced code left out."""
    lines = text.splitlines()
    try:
        start = next(i for i, line in enumerate(lines) if line.rstrip() == heading)
    except StopIteration:
        raise Unreadable(f"no heading {heading!r}") from None
    level = len(HEADING_LINE.match(heading).group(1))
    out, fence = [], None
    for i in range(start + 1, len(lines)):
        line = lines[i]
        opening = FENCE.match(line)
        if fence is not None:
            if opening and opening.group(1)[0] == fence[0] and len(opening.group(1)) >= len(fence):
                fence = None
            continue
        if opening:
            fence = opening.group(1)
            continue
        found = HEADING_LINE.match(line)
        if found and len(found.group(1)) <= level:
            break
        out.append((i + 1, line))
    return out


def is_name(span: str) -> bool:
    """A name of a theorem the section may cite, as against the exceptions above."""
    if not IDENTIFIER.fullmatch(span) or len(span) == 1:
        return False
    if "/" in span or FILE_SUFFIX.search(span):
        return False
    return span not in ALLOWED and span not in LEAN_AXIOMS


def names(lines: list[tuple[int, str]]) -> list[tuple[int, str]]:
    """Each name in backticks, with its line, in order."""
    return [(number, span) for number, line in lines
            for span in CODE_SPAN.findall(line) if is_name(span.strip())]


def lex(text: str) -> list[tuple[str, int, str]]:
    """A Lean file as Lean reads it, to its end: its doc comments `/-- … -/`, as ("doc",
    offset, body), and the code between them, as ("code", offset, code), each offset where
    the piece starts in `text`. A `--` comment and a block comment `/- … -/` or `/-! … -/`,
    nested as Lean nests them, become white space, keeping their line breaks; a string
    literal, raw or not, and a character literal stay whole, so a `--` or a `"` inside one
    starts nothing. A doc comment's `-/` is looked for after its `/--`, as Lean looks for
    it, so `/--/` opens one and does not close it."""
    pieces: list[tuple[str, int, str]] = []
    code: list[str] = []
    start = i = 0
    n = len(text)

    def flush() -> None:
        if code:
            pieces.append(("code", start, "".join(code)))
            code.clear()

    while i < n:
        # A `'` or an `r` that ends or continues a name, as in `B'` or `hr`, opens nothing.
        in_name = i > 0 and NAME_CHAR.match(text[i - 1]) is not None
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = n if end < 0 else end
            code.append(" ")
        elif text.startswith("/-", i):
            doc = text.startswith("/--", i)
            depth, j = 1, i + (3 if doc else 2)
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            if depth:
                raise Unreadable(f"a comment opened at line {text.count(chr(10), 0, i) + 1} "
                                 "is never closed")
            if doc:
                flush()
                pieces.append(("doc", i, text[i + 3:j - 2]))
                start = j
            else:
                code.append("\n" * text.count("\n", i, j) or " ")
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            code.append(text[i:j + 1])
            i = j + 1
        elif not in_name and (raw := RAW_STRING.match(text, i)):
            close = '"' + raw.group(1)
            end = text.find(close, raw.end())
            j = n if end < 0 else end + len(close)
            code.append(text[i:j])
            i = j
        elif not in_name and (char := CHAR_LITERAL.match(text, i)):
            code.append(char.group())
            i = char.end()
        else:
            if not code:
                start = i
            code.append(text[i])
            i += 1
    flush()
    return pieces


def lean_pieces(text: str) -> list[tuple[str, int, str]]:
    """The pieces of `lex` that Lean runs: nothing after a `#exit` is read."""
    out = []
    for kind, offset, body in lex(text):
        if kind == "code" and (stop := EXIT.search(body)):
            out.append((kind, offset, body[:stop.start()]))
            break
        out.append((kind, offset, body))
    return out


def leading_imports(code: str) -> tuple[list[str], int]:
    """The modules the `import` lines at the start of a file's first code import, and
    where those lines end in it."""
    modules, end = [], 0
    while imported := IMPORT.match(code, end):
        modules.append(imported.group("module"))
        end = imported.end()
    return modules, end


def imports(text: str) -> list[str]:
    """The modules a Lean file imports: its leading `import` lines, as Lean reads them."""
    pieces = lex(text)
    return leading_imports(pieces[0][2])[0] if pieces and pieces[0][0] == "code" else []


def strays(text: str) -> list[tuple[int, str]]:
    """Each line of the audit file that holds anything but its leading imports, comments,
    docstrings and pins, each pin directly after its docstring, with the line's text. The
    file is read to its end, so a `#exit` is one of them."""
    lines = text.split("\n")
    pieces = lex(text)
    found: set[int] = set()
    for index, (kind, offset, code) in enumerate(pieces):
        if kind != "code":
            continue
        end = leading_imports(code)[1] if index == 0 else 0
        if index and pieces[index - 1][0] == "doc" and (pin := PIN.match(code, end)):
            end = pin.end()
        first = text.count("\n", 0, offset) + code.count("\n", 0, end) + 1
        found.update(first + k for k, line in enumerate(code[end:].split("\n")) if line.strip())
    return [(number, lines[number - 1].strip()) for number in sorted(found)]


def statement_pins(text: str) -> tuple[set[str], dict[str, tuple[int, str]]]:
    """The full names the audit file pins by their statements, under a bare `#guard_msgs
    in`; and those pinned only under `#guard_msgs` with options, each with the line of its
    pin and the options."""
    found: set[str] = set()
    weak: dict[str, tuple[int, str]] = {}
    pieces = lean_pieces(text)
    for (kind, offset, body), after in zip(pieces, pieces[1:] + [("code", len(text), "")]):
        info = body.lstrip()
        if kind != "doc" or not info.startswith("info:") or after[0] != "code":
            continue
        first = info[len("info:"):].lstrip(" \t").split("\n", 1)[0]
        guarded = GUARDED.match(after[2])
        if not guarded:
            continue
        name = guarded.group("check") or guarded.group("print")
        shape = rf"@?{re.escape(name)}\s*:" if guarded.group("check") \
            else rf"{KEYWORD}{re.escape(name)}{NAME_END}"
        if not re.match(shape, first):
            continue
        options = guarded.group("options").strip()
        if options:
            line = (text.count("\n", 0, after[1])
                    + after[2].count("\n", 0, guarded.start("options")) + 1)
            weak.setdefault(name, (line, options))
        else:
            found.add(name)
    return found, {name: where for name, where in weak.items() if name not in found}


def pins(text: str) -> set[str]:
    """The full names the audit file pins by their statements, under a bare guard."""
    return statement_pins(text)[0]


def full_names(name: str) -> list[str]:
    """`name`, as the brief writes it, in full in each namespace it may be in."""
    return [f"{space}.{name}" for space in NAMESPACES]


def read(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        raise Unreadable(f"cannot read {path}") from None


def shorten(line: str, width: int = 80) -> str:
    return line if len(line) <= width else line[:width - 1] + "…"


def check(brief: Path, audit: Path, library: Path = ROOT / LIBRARY) \
        -> tuple[list[str], list[str], int]:
    """What the audit file holds besides its imports, comments and pins, line by line, and
    Audit.lean's missing import of it, each as a message; the names without a statement
    pin, each as a message; and how many names the section has."""
    shown_brief, shown_audit = display(brief), display(audit)
    found = names(section(read(brief)))
    if not found:
        raise Unreadable(f"{shown_brief}: {HEADING!r} names no theorem; is it the section "
                         "of the restriction theorem?")
    text = read(audit)
    full, weak = statement_pins(text)
    refused = [f"{shown_audit}:{number}: `{shorten(line)}` is not a leading import, a comment "
               "or a pin" for number, line in strays(text)]
    if MODULE not in imports(read(library)):
        refused.append(f"{display(library)}: does not import {MODULE} among its leading "
                       "imports, so `lake build Audit` does not run the pins")
    missing = []
    for number, name in found:
        candidates = full_names(name)
        if any(c in full for c in candidates):
            continue
        message = f"{shown_brief}:{number}: `{name}` has no statement pin in {shown_audit}"
        weakly = [(c, weak[c]) for c in candidates if c in weak]
        if weakly:
            pinned_as, (line, options) = weakly[0]
            message += (f": its pin at {shown_audit}:{line} is under `#guard_msgs {options}"
                        " in`, which lets a message pass that is not the docstring; only a "
                        "bare `#guard_msgs in` pins a statement")
        else:
            message += (f" (an `info:` docstring, a bare `#guard_msgs in`, then `#check "
                        f"@{candidates[0]}`, or `#print` for a definition)")
        missing.append(message)
    return refused, missing, len({name for _, name in found})


def display(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(ROOT))
    except ValueError:
        return str(path)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--brief", type=Path, default=ROOT / BRIEF, metavar="FILE")
    parser.add_argument("--audit", type=Path, default=ROOT / AUDIT, metavar="FILE")
    parser.add_argument("--library", type=Path, default=ROOT / LIBRARY, metavar="FILE")
    args = parser.parse_args(argv)
    try:
        refused, missing, count = check(args.brief, args.audit, args.library)
    except Unreadable as e:
        print(f"check_superposition_pins: {e}", file=sys.stderr)
        return 2
    for message in refused + missing:
        print(message)
    if refused:
        print(f"✗ {len(refused)} refused: {display(args.audit)} may hold only its leading "
              "imports, comments and pins (a docstring, a bare `#guard_msgs in`, then "
              "`#check @name`, `#print name` or `#print axioms name`), so that nothing in it "
              "changes what a pin prints or which declaration it names; and "
              f"{display(args.library)} must import {MODULE}")
    if missing:
        print(f"✗ {len(missing)} of {count} names in {HEADING!r} have no statement pin")
    if refused or missing:
        return 1
    print(f"✓ every name in {HEADING!r}, {count} in all, has a statement pin in "
          f"{display(args.audit)}, which holds only imports, comments and pins; "
          f"{display(args.library)} imports it")
    return 0


if __name__ == "__main__":
    sys.exit(main())
