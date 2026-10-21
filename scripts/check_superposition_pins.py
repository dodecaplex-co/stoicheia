#!/usr/bin/env python3
"""Check that every theorem brief 0009's restriction section names has a statement pin.

    python3 -I scripts/check_superposition_pins.py
    python3 -I scripts/check_superposition_pins.py --brief FILE --audit FILE

The section is the one headed "## The restriction theorem" in
docs/briefs/0009-superposition.md, up to the next heading of its level or above. Each
name in backticks there, one Lean identifier, dotted or not, must have a statement pin in
Audit/Superposition.lean, under its full name: the name in `Elements.Superposition`, where
the restriction's theorems are, or else in `Elements.BookI`, as the brief writes I.4's and
I.8's. A statement pin is an `info:` docstring whose first line names the declaration,
then a bare `#guard_msgs in`, then `#check @<full name>`, or for a definition `#print
<full name>`. An axiom pin, `#print axioms`, is not a statement pin: a weaker statement
under the same name can keep its axioms. `lake build Audit` checks that each pin's
docstring is what Lean prints; this script checks that the pins exist.

The audit file is read as Lean reads it. A pin inside a `--` comment or a block comment
`/- … -/` (a module doc `/-! … -/` among them, nested as Lean nests them), inside a string
or character literal, or after `#exit`, is not run, and is not counted. Nor is a pin
whose `#guard_msgs` has options, such as `(substring := true)`, `(drop info)` or
`(whitespace := lax)`: they let a message pass that is not the docstring, so only a bare
`#guard_msgs in` compares the whole statement; a name pinned only that way is reported
with the pin's line.

Not checked, since they are not names of theorems:

* `Rule.infer`, the locked rule's field, whose statement Certificate/axioms.lock pins;
  `Metric`, a type; and `cite`, a constructor of `Derives`;
* file names, with a `/` or a file suffix such as `.lean`;
* Lean's own axioms, `propext`, `Classical.choice` and `Quot.sound`;
* a single letter, which is a variable; and anything in backticks that is not one
  identifier, such as `Rule I` or `∀ c ∈ cites, c.Holds I`.

Fenced code in the section is skipped. Exits 0 when every name is pinned; 1 when a name
is not, printing `FILE:LINE: `name` has no statement pin in AUDIT` for each; 2 when the
brief, its section or the audit file cannot be read, or when the section names no
theorem at all, which means it was misread. Standard library only.
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BRIEF = Path("docs/briefs/0009-superposition.md")
AUDIT = Path("Audit/Superposition.lean")
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
# What Lean reads whole in code: a raw string `r"…"` or `r#"…"#`, closed by `"` and as many
# `#`, and a character literal such as `'"'` or `'\n'`, neither inside a name.
NAME_CHAR = re.compile(r"[\w'!?₀-₉.]")
RAW_STRING = re.compile(r'r(#*)"')
CHAR_LITERAL = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'")


class Unreadable(Exception):
    """The brief, its section or the audit file cannot be read."""


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


def lean_pieces(text: str) -> list[tuple[str, int, str]]:
    """The audit file as Lean reads it: its doc comments `/-- … -/`, as ("doc", offset,
    body), and the code between them, as ("code", offset, code), each offset where the
    piece starts in `text`. A `--` comment and a block comment `/- … -/` or `/-! … -/`,
    nested as Lean nests them, become white space, keeping their line breaks; a string
    literal, raw or not, and a character literal stay whole, so a `--` or a `"` inside one
    starts nothing; and nothing after a `#exit` is read."""
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
            depth, j = 1, i + 2
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
    out = []
    for kind, offset, body in pieces:
        if kind == "code" and (stop := EXIT.search(body)):
            out.append((kind, offset, body[:stop.start()]))
            break
        out.append((kind, offset, body))
    return out


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


def check(brief: Path, audit: Path) -> tuple[list[str], int]:
    """The names without a statement pin, each as a message; and how many names the
    section has."""
    shown_brief, shown_audit = display(brief), display(audit)
    found = names(section(read(brief)))
    if not found:
        raise Unreadable(f"{shown_brief}: {HEADING!r} names no theorem; is it the section "
                         "of the restriction theorem?")
    full, weak = statement_pins(read(audit))
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
    return missing, len({name for _, name in found})


def display(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(ROOT))
    except ValueError:
        return str(path)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--brief", type=Path, default=ROOT / BRIEF, metavar="FILE")
    parser.add_argument("--audit", type=Path, default=ROOT / AUDIT, metavar="FILE")
    args = parser.parse_args(argv)
    try:
        missing, count = check(args.brief, args.audit)
    except Unreadable as e:
        print(f"check_superposition_pins: {e}", file=sys.stderr)
        return 2
    for message in missing:
        print(message)
    if missing:
        print(f"✗ {len(missing)} of {count} names in {HEADING!r} have no statement pin")
        return 1
    print(f"✓ every name in {HEADING!r}, {count} in all, has a statement pin in "
          f"{display(args.audit)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
