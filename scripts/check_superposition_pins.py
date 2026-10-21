#!/usr/bin/env python3
"""Check that every theorem and definition brief 0009's restriction section names is pinned.

    python3 -I scripts/check_superposition_pins.py
    python3 -I scripts/check_superposition_pins.py --brief FILE --audit FILE --library FILE

The section is the one headed "## The restriction theorem" in
docs/briefs/0009-superposition.md, up to the next heading of its level or above. Each
name in backticks there, one Lean identifier, dotted or not, must have a statement pin in
Audit/Superposition.lean, under its full name: the name in `Elements.Superposition`, where
the restriction's theorems are, or else in `Elements.BookI`, as the brief writes I.4's and
I.8's. A statement pin is an `info:` docstring whose first line names the declaration,
then a bare `#guard_msgs in`, then `#check @<full name>` for a theorem, or `#print <full
name>` for a definition, since `#check` shows only a definition's type and not its body.
An axiom pin, `#print axioms`, is not a statement pin: a weaker statement under the same
name can keep its axioms. The two definitions the section names, `Rule.Figure` and
`Interpretation.Embedding`, are held to `#print` by name: a `#check` pin of either is
refused, whatever it prints, and each must have a `#print` pin, even if the section stops
naming it. Three definitions the section does not name must have a `#print` pin as well,
since theorems it names read them: `Placed`, read by `Rule.of_placement`; `Val.place`, by
`Metric.holds_place`; and `Metric.names`, by `exportable_iff`, `not_exportable_second` and
`not_exportable_third`. `lake build Audit` checks that each pin's docstring is what Lean
prints; this script checks that the pins exist, and that the audit file holds nothing
else, so that no option or declaration in it can change what a pin prints or which
declaration it names.

A `#check` pin of any other name is refused, with its line, when Lean's print of the
type, in its docstring, shows that the type is not a proposition, so that what it pins is
a definition: when the type ends in a sort (`Prop`, `Type`, `Sort u` and the like), or
when it opens a binder with an arrow, as in `{P : Type} →`, since Lean writes a
proposition's binder after `∀` instead (`∀ {P : Type},`). These two signs are the
backstop for a definition the section names later. The docstring is read, and not the
brief or the Lean source, because it is Lean's own account of the declaration the pin
names, which `lake build Audit` holds exact; the brief marks no name as a definition, and
reading the source would mean resolving Lean's namespaces without Lean. A type with
neither sign cannot be told from a theorem's statement by its print, so a definition of
such a type that the section names later, pinned by `#check`, would pass: a type such as
`Nat → Nat`, or one whose sort is spelt through a name, such as `id Type`, `outParam
Type` or an `abbrev` of a sort, which Lean prints as it is written (`… → id Type`). That
is why the five definitions above do not rest on the signs. And a statement pin whose docstring holds `⋯` or `[...]`,
the marks Lean leaves where it cuts a print short, is refused with the line of the mark,
wherever the option was set, in the audit file or outside it: `pp.deepTerms` and
`pp.maxSteps`, at its default on a long enough statement, leave `⋯`, and `pp.oneline`
leaves `[...]`. A docstring that matches a shortened print pins only part of the
statement. The default `pp.proofs` also prints a proof inside a term as `⋯`, and such a pin
is refused too; no pin has one. An option that hides part of a print with no mark, such
as `pp.piBinderTypes false`, which drops the types of binders, is not seen: since the
audit file may set no option, it could be set only outside the file, in the lakefile, a
protected file, and that protection holds it off, not this script.

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

Not checked:

* `Rule.infer`, the locked rule's field, whose statement Certificate/axioms.lock pins;
  `Metric`, a type, and `cite`, a constructor of `Derives`, which the lock pins too,
  `Metric` with its constructors;
* file names, with a `/` or a file suffix such as `.lean`;
* Lean's own axioms, `propext`, `Classical.choice` and `Quot.sound`;
* a single letter, which is a variable; and anything in backticks that is not one
  identifier, such as `Rule I` or `∀ c ∈ cites, c.Holds I`.

Fenced code in the section is skipped. Exits 0 when every name is pinned, the five
definitions are printed, the audit file holds nothing else and Audit.lean imports it; 1
otherwise, printing `FILE:LINE: `name` has no statement pin in AUDIT` for each name not
pinned, `AUDIT: `name`, read by …, has no `#print` pin` for each of the three not
printed, `AUDIT: `name`, held to `#print` by name …, has no `#print` pin` for each of the
two the section no longer names and that is not printed (one it names is reported as a
name not pinned), `AUDIT:LINE: `…` is not a leading import, a comment or a pin` for each
line refused, `AUDIT:LINE: `…` pins a definition by `#check`` for a `#check` of a
definition, `AUDIT:LINE: `…` holds `⋯`` for a shortened print, and a line naming
Audit.lean if it does not import the audit file; 2 when the brief, its section, the audit
file or Audit.lean cannot be read, or when the section names no theorem at all, which
means it was misread. Standard library only.
"""

import argparse
import re
import sys
from pathlib import Path
from typing import NamedTuple

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

# The definitions the section names, held to `#print` by name: a `#check` pin of either is
# refused whatever it prints, and each must have a `#print` pin, as each in `PRINTED` must.
# The signs below are not enough for them: a sort spelt through a name, as in a structure
# declared `: id Type`, shows neither sign, so a field added to it would pass under a
# `#check`. The signs stay for a definition the section names later.
DEFINITIONS = ("Elements.Superposition.Rule.Figure",
               "Elements.Superposition.Interpretation.Embedding")

# Definitions the section does not name, each with the theorems the section names that
# read it. Each must be printed whole by `#print` all the same: a change to its body would
# change what those theorems say, while their statement pins, which show only its name,
# still passed.
PRINTED = {
    "Elements.Superposition.Placed": ("Rule.of_placement",),
    "Elements.Superposition.Val.place": ("Metric.holds_place",),
    "Elements.Superposition.Metric.names":
        ("exportable_iff", "not_exportable_second", "not_exportable_third"),
}

# Pinned by the lock, not here (see the module docstring).
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
    r"(?P<command>#check\s+@(?P<check>\S+)|#print\s+(?!axioms\b)(?P<print>\S+))")
# The first line of the docstring, which must name the declaration: `@name :` or `name :`
# for `#check`, `def name`, `structure name` and the like for `#print`.
KEYWORD = r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*" \
          r"(?:def|theorem|structure|class|inductive|abbrev|opaque|instance)\s+"
# What tells, in Lean's print of a type, that the type is not a proposition. A sort, as
# Lean prints one: `Prop`, `Type`, `Sort u`, `Type (max u v)` and the like; a type that
# ends in one is never a proposition.
SORT = re.compile(r"Prop|(?:Type|Sort)(?:\s+(?:[\w.?]+|\((?:[^()]|\([^()]*\))*\)))?")
# And a binder group opened with an arrow, `(x : A) →`, `{x : A} →`, `⦃x : A⦄ →` or
# `[A] →`: Lean writes `∀` before the group instead when the type is a proposition.
BINDER_NAMES = re.compile(r"\s*[^\s:()\[\]{}⦃⦄⟨⟩,]+(?:\s+[^\s:()\[\]{}⦃⦄⟨⟩,]+)*\s+:\s")
BRACKETS = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩"}
# A term whose body runs as far as it can: what follows one is never cut at an arrow.
LEADING = re.compile(r"(?<![\w'!?₀-₉.])(?:∀|∃!?|fun|λ|let|have|show|match|if)(?![\w'!?₀-₉])")
# The marks Lean leaves where it cuts a print short: `⋯` (`pp.deepTerms`, `pp.maxSteps`,
# and a proof inside a term under the default `pp.proofs`) and `[...]` (`pp.oneline`).
SHORTENED = ("⋯", "[...]")
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


class Pin(NamedTuple):
    """A statement pin Lean runs: an `info:` docstring whose first line names the
    declaration, then `#guard_msgs`, with or without options, then `#check @name` or
    `#print name`."""
    name: str
    command: str            # "check" or "print"
    line: int               # the line of the `#check` or `#print`
    options: str            # the guard's options, empty for a bare guard
    options_line: int       # the line of the guard's options
    shortened: tuple[int, str] | None   # the line and mark of a shortened print
    sign: str | None        # for `#check`, what in its type shows a definition

    def by_name(self) -> bool:
        """Whether the pin is a `#check` of a definition held to `#print` by name."""
        return self.command == "check" and self.name in DEFINITIONS

    def fault(self) -> tuple[int, str] | None:
        """Why the pin does not pin its statement, with the line to point to, said after
        "its pin at FILE:LINE"; None when it does."""
        if self.options:
            return self.options_line, (
                f"is under `#guard_msgs {self.options} in`, which lets a message pass that "
                "is not the docstring; only a bare `#guard_msgs in` pins a statement")
        if self.shortened:
            line, mark = self.shortened
            return line, (f"holds `{mark}`, where Lean cut its print short, so the docstring "
                          "matches only part of the statement; no statement pin may be "
                          "shortened")
        if self.by_name():
            return self.line, ("is a `#check` of a definition held to `#print` by name, "
                               "whatever its print shows, since `#check` shows only a "
                               "definition's type; only `#print` pins a definition")
        if self.sign:
            return self.line, (f"is a `#check`, but Lean prints the type {self.sign}, so "
                               "what it pins is a definition, of which `#check` shows only "
                               "the type; only `#print` pins a definition")
        return None


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


def arrow_parts(type_: str) -> list[str]:
    """Lean's print of a type, cut at its outermost arrows: `A → (B → C) → D` gives `A`,
    `(B → C)` and `D`. A term that runs as far as it can, such as `∀ x, …`, `fun x => …`
    or `have x := …; …`, runs to the end, as Lean reads it, and a string is read whole."""
    parts, depth, start, i, n = [], 0, 0, 0, len(type_)
    while i < n:
        c = type_[i]
        if c == '"':
            i += 1
            while i < n and type_[i] != '"':
                i += 2 if type_[i] == "\\" else 1
        elif c in BRACKETS:
            depth += 1
        elif c in BRACKETS.values():
            depth -= 1
        elif depth == 0 and c == "→":
            parts.append(type_[start:i].strip())
            start = i + 1
        elif depth == 0 and LEADING.match(type_, i):
            break
        i += 1
    return parts + [type_[start:].strip()]


def is_binder(part: str) -> bool:
    """Whether `part` is one binder group, `(x y : A)`, `{x : A}`, `⦃x : A⦄` or `[A]`,
    and not, say, `(A → B)` or `{ x := a }`."""
    if not part or part[0] not in "({⦃[":
        return False
    depth = 0
    for k, c in enumerate(part):
        depth += (c in BRACKETS) - (c in BRACKETS.values())
        if depth == 0:
            break
    if depth or k != len(part) - 1:
        return False
    return part[0] == "[" or BINDER_NAMES.match(part[1:-1]) is not None


def definition_sign(type_: str) -> str | None:
    """What in Lean's print of a type shows that the type is not a proposition, so that a
    declaration of that type is a definition and not a theorem, said after "Lean prints
    the type"; None when the print shows neither sign."""
    parts = arrow_parts(" ".join(type_.split()))
    if SORT.fullmatch(parts[-1]):
        return f"ending in the sort `{parts[-1]}`"
    binder = next((part for part in parts[:-1] if is_binder(part)), None)
    if binder:
        return f"with `{binder} →`, where a proposition has `∀ {binder},`"
    return None


def read_pins(text: str) -> list[Pin]:
    """Every statement pin in the audit file that Lean runs, in order."""
    found: list[Pin] = []
    pieces = lean_pieces(text)
    for (kind, offset, body), after in zip(pieces, pieces[1:] + [("code", len(text), "")]):
        info = body.lstrip()
        if kind != "doc" or not info.startswith("info:") or after[0] != "code":
            continue
        printed = info[len("info:"):].lstrip(" \t")
        guarded = GUARDED.match(after[2])
        if not guarded:
            continue
        name = guarded.group("check") or guarded.group("print")
        shape = rf"@?{re.escape(name)}\s*:" if guarded.group("check") \
            else rf"{KEYWORD}{re.escape(name)}{NAME_END}"
        named = re.match(shape, printed.split("\n", 1)[0])
        if not named:
            continue

        def line(position: int) -> int:
            return text.count("\n", 0, position) + 1

        marks = [(body.index(mark), mark) for mark in SHORTENED if mark in body]
        shortened = None
        if marks:
            index, mark = min(marks)
            shortened = (line(offset + len("/--") + index), mark)
        found.append(Pin(
            name=name,
            command="check" if guarded.group("check") else "print",
            line=line(after[1] + guarded.start("command")),
            options=guarded.group("options").strip(),
            options_line=line(after[1] + guarded.start("options")),
            shortened=shortened,
            sign=definition_sign(printed[named.end():]) if guarded.group("check") else None))
    return found


def statement_pins(text: str) -> tuple[set[str], dict[str, tuple[int, str]]]:
    """The full names the audit file pins by their statements: under a bare `#guard_msgs
    in`, with a docstring Lean did not cut short, and by `#print` if a definition. And
    those pinned only otherwise, each with the line to point to and why its pin does not
    count."""
    found: set[str] = set()
    weak: dict[str, tuple[int, str]] = {}
    for pin in read_pins(text):
        fault = pin.fault()
        if fault:
            weak.setdefault(pin.name, fault)
        else:
            found.add(pin.name)
    return found, {name: where for name, where in weak.items() if name not in found}


def pins(text: str) -> set[str]:
    """The full names the audit file pins by their statements."""
    return statement_pins(text)[0]


def printed_pins(text: str) -> set[str]:
    """The full names the audit file pins by a `#print` that counts, its definitions
    printed whole."""
    return {pin.name for pin in read_pins(text) if pin.command == "print" and not pin.fault()}


def refused_pins(text: str) -> list[tuple[int, str]]:
    """Each line of a pin the audit file may not hold, though it is shaped as one, with
    why: the mark of a shortened print, and a `#check` of a definition, held to `#print`
    by name or showing a sign. (A guard with options is one of the `strays`.)"""
    found = []
    for pin in read_pins(text):
        if pin.shortened:
            line, mark = pin.shortened
            found.append((line, f"holds `{mark}`, where Lean cut its print short, so the pin "
                                f"of `{pin.name}` matches only part of the statement"))
        if pin.by_name():
            found.append((pin.line, f"pins a definition by `#check`, which shows only its "
                                    f"type (`{pin.name}` is held to `#print` by name, whatever "
                                    f"its print shows); only `#print {pin.name}` pins a "
                                    "definition"))
        elif pin.sign:
            found.append((pin.line, f"pins a definition by `#check`, which shows only its "
                                    f"type (Lean prints the type {pin.sign}); only "
                                    f"`#print {pin.name}` pins a definition"))
    return found


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


def readers(name: str) -> str:
    """The theorems that read one of the definitions in `PRINTED`, as a phrase."""
    shown = [f"`{reader}`" for reader in PRINTED[name]]
    return shown[0] if len(shown) == 1 else ", ".join(shown[:-1]) + " and " + shown[-1]


def check(brief: Path, audit: Path, library: Path = ROOT / LIBRARY) \
        -> tuple[list[str], list[str], list[str], list[str], int]:
    """What the audit file holds besides its imports, comments and pins, line by line, the
    pins it may not hold, and Audit.lean's missing import of it, each as a message; the
    names without a statement pin, each as a message; the definitions in `PRINTED` without
    a `#print` pin, each as a message; those in `DEFINITIONS` the section no longer names
    and without a `#print` pin, each as a message (one it names is among the names without
    a statement pin, since only a `#print` pins it); and how many names the section has."""
    shown_brief, shown_audit = display(brief), display(audit)
    found = names(section(read(brief)))
    if not found:
        raise Unreadable(f"{shown_brief}: {HEADING!r} names no theorem; is it the section "
                         "of the restriction theorem?")
    text = read(audit)
    lines = text.split("\n")
    full, weak = statement_pins(text)
    refusals = [(number, f"`{shorten(line)}` is not a leading import, a comment or a pin")
                for number, line in strays(text)]
    refusals += [(number, f"`{shorten(lines[number - 1].strip())}` {why}")
                 for number, why in refused_pins(text)]
    refused = [f"{shown_audit}:{number}: {message}" for number, message in sorted(refusals)]
    if MODULE not in imports(read(library)):
        refused.append(f"{display(library)}: does not import {MODULE} among its leading "
                       "imports, so `lake build Audit` does not run the pins")
    missing = []
    for number, name in found:
        candidates = full_names(name)
        if any(c in full for c in candidates):
            continue
        message = f"{shown_brief}:{number}: `{name}` has no statement pin in {shown_audit}"
        weakly = [weak[c] for c in candidates if c in weak]
        definition = next((c for c in candidates if c in DEFINITIONS), None)
        if weakly:
            line, why = weakly[0]
            message += f": its pin at {shown_audit}:{line} {why}"
        elif definition:
            message += (f" (an `info:` docstring, a bare `#guard_msgs in`, then `#print "
                        f"{definition}`)")
        else:
            message += (f" (an `info:` docstring, a bare `#guard_msgs in`, then `#check "
                        f"@{candidates[0]}`, or `#print` for a definition)")
        missing.append(message)
    printed, every_pin = printed_pins(text), read_pins(text)

    def no_print(name: str, what: str) -> str:
        message = f"{shown_audit}: `{name}`, {what}, has no `#print` pin"
        other = next((pin for pin in every_pin if pin.name == name), None)
        if other and other.fault():
            line, why = other.fault()
            message += f": its pin at {shown_audit}:{line} {why}"
        elif other:
            message += (f": its pin at {shown_audit}:{other.line} is a `#check`, which shows "
                        "only a definition's type; only `#print` pins a definition")
        else:
            message += f" (an `info:` docstring, a bare `#guard_msgs in`, then `#print {name}`)"
        return message

    named = {full for _, name in found for full in full_names(name)}
    unprinted = [no_print(name, f"read by {readers(name)}") for name in PRINTED
                 if name not in printed]
    dropped = [no_print(name, "held to `#print` by name, though the section no longer names it")
               for name in DEFINITIONS if name not in printed and name not in named]
    return refused, missing, unprinted, dropped, len({name for _, name in found})


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
        refused, missing, unprinted, dropped, count = check(args.brief, args.audit,
                                                            args.library)
    except Unreadable as e:
        print(f"check_superposition_pins: {e}", file=sys.stderr)
        return 2
    for message in refused + missing + unprinted + dropped:
        print(message)
    if refused:
        print(f"✗ {len(refused)} refused: {display(args.audit)} may hold only its leading "
              "imports, comments and pins (a docstring, a bare `#guard_msgs in`, then "
              "`#check @name`, `#print name` or `#print axioms name`), so that nothing in it "
              "changes what a pin prints or which declaration it names; a definition is "
              "pinned by `#print`, never `#check`; no statement pin may be cut short (`⋯`, "
              f"`[...]`); and {display(args.library)} must import {MODULE}")
    if missing:
        print(f"✗ {len(missing)} of {count} names in {HEADING!r} have no statement pin")
    if unprinted:
        print(f"✗ {len(unprinted)} of the {len(PRINTED)} definitions that pinned theorems "
              "read have no `#print` pin")
    if dropped:
        print(f"✗ {len(dropped)} of the {len(DEFINITIONS)} definitions held to `#print` by name "
              f"have no `#print` pin and are no longer named in {HEADING!r}")
    if refused or missing or unprinted or dropped:
        return 1
    shown = [name.removeprefix(f"{NAMESPACES[0]}.") for name in PRINTED]
    print(f"✓ every name in {HEADING!r}, {count} in all, has a statement pin in "
          f"{display(args.audit)}, by `#print` for a definition, and {', '.join(shown[:-1])} "
          f"and {shown[-1]} are printed whole; the file holds only imports, comments and "
          f"pins, none cut short, and {display(args.library)} imports it")
    return 0


if __name__ == "__main__":
    sys.exit(main())
