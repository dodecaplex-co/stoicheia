"""Check the house style's hard rules, and report its defaults.

The rules are those of docs/STYLE.md, section 8, which is their one home: S1 to S26
fail the script, and D4 to D11 and D14 to D16 are listed for a reader to judge and fail
nothing. Run from anywhere; the paths are the repository's.

    python3 scripts/check_style.py              # every rule, S12 included
    python3 scripts/check_style.py --no-lean    # S12 skipped, for an unbuilt tree
    python3 scripts/check_style.py --quiet      # the reports as counts only
    python3 scripts/check_style.py --require-idea-letters   # S21 on every figure, as the switch is
    python3 -I tests/test_check_style.py        # the rules' cases, which CI runs first

S12 asks Lean whether each backticked name in the texts it reads exists, so it needs a
built tree (`lake build`) and `lake` on the PATH; without them the script fails and says
so, unless `--no-lean` is given. The overlap catalogue's audit lemmas are Lean's only
once `lake build Audit` has run: until then they are listed as not checked. CI runs the
script after both.

S23 reads every tracked text file, including comments and Markdown fences: it refuses
seven-character opening, base and closing merge markers, and seven-equals separators
between opening and closing markers or where they cannot be Markdown setext underlines.
Text has no NUL and decodes as UTF-8; without Git it walks the tree, omitting the build
and cache directories named in MARKER_SKIP_DIRS (including every .lake, model's too).
Traversal errors stop the check. Symlinks are skipped: Git stores a link's target path,
not the contents it points to. The walk is for S23 alone.

What the scopes cover (STYLE, section 8):

* Prose: mishnah/<book>/NN.md, mishnah/intro/<book>.md, reading/<book>/NN.md.
* Mishnah: mishnah/<book>/NN.md alone.
* Review notes: the texts of review/<book>/NN.toml that its page shows (REVIEW_SHOWN),
  and each tag's `meaning` and `badge` in review/terms.toml.
* Catalogues: docs/reports/gaps-book-*.md and docs/reports/overlaps.md.
* Other reports: every other docs/reports/*.md, save the outside reviews
  (outside-review-*.md), which keep their reviewers' words as written; the crew's own
  logs, docs/reports/crew/, are not read.
* README: README.md, without its section "How it was made".
* Lean notes: in Elements/**/*.lean, the text of `/- … -/` blocks and docstrings, save
  the docstring of each `theorem PropN`, which is Heath's enunciation. The `--` lines
  are Heath's proof and out of scope.
* Rendered docstrings: of the Lean notes, the docstrings that render.py copies onto the
  pages, each tacit rule's and each other axiom's that is not a postulate or a definition
  (`render.load_axiom_docs`, `render.axiom_groups`).
* Generated: CERTIFICATE.md, GRAPH.md, book/<book>/index.md, book/<book>/front.md and
  book/names.md. A failure here is mended in scripts/render.py or in the source it reads.
* Idea figures, figures/<book>/NN-idea.svg; Euclid's figures, figures/<book>/NN.svg;
  the figures of the modern way, figures/<book>/NN-modern.svg (S24, S25), each drawn to
  stand under its page's paragraph "**The modern way.**", with Euclid's figure's letters
  and the paragraph's own names.

S12 reads the Prose, the Review notes, the Catalogues, the Rendered docstrings and the
front pages (book/<book>/front.md). It does not read the Other reports: a dated report is
right as of its commit, and a Lean name changed later must not fail a report nobody
touched. A text of one book gets that book's namespace; a text with no book of its own
gets every book's; and the foundations' Rendered docstrings get only `Elements` and
`Elements.Tacit`. S12 reads the name before the colon of a backticked `name : type` too,
for a hypothesis is said in words, not by its local name (STYLE, section 1). A backticked
word that is Lean's or the certificate's but no declaration (a tactic, a field of
facts.json) is listed in NOT_DECLARED with its reason.

The reach of #66, held file by file (REACH_PENDING). The Review notes, the overlap
catalogue, the Other reports, the Rendered docstrings, the front pages and the table of
names came under the rules on 19 October, with S7 in the gap catalogues and the Generated
files, S12 beyond the mishnah, and S22. A file that had findings of that reach on the
day was listed with the rules it had findings of and whoever mends them, and while it is
listed its findings of those rules are reported (D16) and fail nothing; every other
finding of the reach fails at once, in a listed file as in any other, and so does every
finding a file was held to before. A rule of an entry whose file has no finding of it left
is reported as done, for the change that takes the rule out of the entry, or the entry out
once each of its rules is done; S12, which alone asks Lean, is not, under `--no-lean` or
when Lean could not be asked. Once no entry is left, the list goes.

"Outside quotations" means with every "…" span (within one paragraph), every link
target `](…)`, every code span and every fenced code block blanked first. HTML comments
are never shown to a reader, and are blanked everywhere. Blanking keeps every line in
its place, so each finding names its line. A blanked span reads as spaces, so the words
of a phrase may stand apart across one: S3 finds "I think" in 'as I "so" think'.

The words of a phrase in S2 to S7, S9, S11 and D7 to D10 are found however a line or a
comment wraps them: they may stand apart by spaces or tabs (and commas, between S9's
letters), or by one line break with the next line's indent and comment leader ("--" in
Lean, ">" in a Markdown quotation). A blank line ends such a phrase, save S2's "first
mate" and the "Definition N" of S7 and D10, whose words may stand apart by any white
space. Those patterns are tested on such phrases, case by case (below).

S10 refuses TeX in the mishnah, save `$…$` in a paragraph that opens
`**The modern way.**`, which ends where Markdown ends a paragraph (`MODERN_WAY_ENDS`);
and there it refuses the shapes of span known to break on GitHub (STYLE, section
4, "Mathematics"). Sample spans tried on GitHub on 18 October found most of them, and
showed its Markdown taking away backslashes inside a span, so Markdown reads there; by
CommonMark's rules for emphasis, checked with a CommonMark parser and not tried on GitHub,
a `*`, or a `_` after anything but a letter or a digit, pairs with another across two
spans, so a span holds no `*`, `~` or backtick, and a `_` only straight after a letter or
a digit. A shape not yet found may still break: the reviewer's checklist, item 5 (STYLE,
section 8), which sees each span rendered on GitHub, stays the guard. The tests hold
cases on both sides of that boundary.

S2's crew words match whole words in any case, plurals and possessives included ("the
bosuns", "the crew's"). The figure rules also ask for a <title>: "I.N at a glance" on an
idea figure, "Euclid I.N: …" on Euclid's (STYLE, section 7). A known departure a rule
cannot see is right is listed below with its reason, and printed on every run; one that
no longer applies fails. An idea figure marks a point Heath leaves without a letter in the
figure itself, with `data-unlettered` and its reason (S21), and those are printed too.
S20 judges a letter's ink by the fill under it, an angle's wedge included. S26 measures
a letter as Georgia draws its capital, upright or italic, by the convex hull of its
outline's points (GLYPHS_UPRIGHT, GLYPHS_ITALIC), against every stroke and dot of its
figure and the canvas's edge.

How the rules read a phrase, S10's boundary for TeX, how S20 reads a letter on and beside
an angle's wedge, and how S26 measures a letter against the strokes beside it are tested
case by case in tests/test_check_style.py, which needs no Lean. CI runs it just before
this script, in the order of docs/WORKFLOW.md, section 8; a defect fixed in that reading
comes with a case there. Standard library only.
"""

from __future__ import annotations

import argparse
import fnmatch
import math
import os
import re
import shutil
import string
import subprocess
import sys
import tempfile
import tomllib
import unicodedata
import xml.etree.ElementTree as ET
from collections import defaultdict
from io import BytesIO
from pathlib import Path
from typing import NamedTuple

import check_fidelity
import heath
import render

ROOT = heath.ROOT

# ---------------------------------------------------------------------------------------
# Exceptions. Each is a known departure that the rule cannot see is right, with its
# reason. Add one only with a reason a reviewer can check; never to quiet a real fault.

# S16: letters drawn in Euclid's figure that are not in Heath's text, or the reverse.
# {(book, n): {"extra": {letters drawn but not in the text}, "missing": {...}, "why": …}}
LETTER_EXCEPTIONS = {
    ("II", 7): {
        "extra": {"H", "N"},
        "why": "Heath's figure (scan leaf n408) letters H and N, where the parallels "
               "through G meet AD and DE; his text says only \"let the figure be drawn\"",
    },
    ("II", 14): {
        "extra": {"C"},
        "why": "Heath's figure (scan leaf n429) letters C, a corner of the parallelogram "
               "his text calls BD, and the text never names it",
    },
}

# S21, the switch (STYLE, sections 7 and 8). While the figures at a glance were gaining
# Heath's letters, this was False: S21 held an idea figure only once it carried a letter,
# and D14 listed, book by book, the figures with none yet. Every figure now carries its
# letters, so it is True, and S21 fails every idea figure with a point unlettered; D14 is
# empty. Never set it back to quiet a figure: letter the figure.
IDEA_LETTERS_REQUIRED = True

# Upright letters, the switch (STYLE, sections 4, 7 and 8). Heath's letters take one style
# in the text and in the figures, upright, by the owner's decision of 18 October. The
# figures were drawn with italic letters, and while they were being set upright this was
# False: S15 and S20 took a figure's letters italic or upright, one style in each figure,
# and D15 listed the figures still italic. Every figure is now upright, so it is True, and
# S15 and S20 fail an italic letter; D15 is empty. Never set it back to quiet a figure:
# set the figure upright.
UPRIGHT_LETTERS_REQUIRED = True

# S12: backticked words that are Lean's, or the certificate's, but that no `#check` can
# find, since they are not declarations. {word: why}. Each is printed on every run, and
# one that no text S12 reads uses any more fails.
NOT_DECLARED = {
    "by_contra": "a tactic, which Lean runs rather than declares (reading/I/39.md)",
    "grind": "a tactic, which Lean runs rather than declares (the overlap catalogue)",
    "direct_axioms": "a field of facts.json (Certificate/FIELDS.md), not a Lean name",
    "own_axioms": "a field of facts.json (Certificate/FIELDS.md), not a Lean name",
    "inherited": "a field of facts.json (Certificate/FIELDS.md), not a Lean name",
}

# The reach of #66 (STYLE, section 8, "The reach of 19 October"), held file by file. Each
# file below had findings of the rules' new reach on 19 October, of the rules named beside
# it ({file: (rules, who mends them)}); while it is listed, its findings of those rules
# are reported (D16) and fail nothing. Every other finding of the reach fails, in a listed
# file as in any other, and every file is held to what it was held to before. A rule of
# an entry whose file has no finding of it left is reported as done (reach_done), for the
# change that takes the rule out of the entry, or the entry out once each of its rules is
# done; it never fails, since the change that mends a file judged by this check cannot
# change the check too (docs/WORKFLOW.md, section 10). Never add a file, or a rule to a
# file, to quiet a new finding: mend the text.
REACH_PENDING: dict[str, tuple[str, str]] = {
    # The notes of a proof (S22): a change to the file needs its record read again.
    "Elements/BookIII/Prop19.lean": ("S22", "the next change to the file, with its record"),
    # The foundations' notes (S22): the coordinator's files.
    "Elements/Foundations/Definitions.lean": ("S22", "the coordinator, who owns the foundations"),
    "Elements/Foundations/DefinitionsII.lean": ("S22", "the coordinator, who owns the foundations"),
    "Elements/Foundations/DefinitionsIII.lean": ("S22", "the coordinator, after the mixed angles (#57)"),
    "Elements/Foundations/Magnitudes.lean": ("S22", "the coordinator, who owns the foundations"),
    "Elements/Foundations/Postulates.lean": ("S22", "the coordinator, who owns the foundations"),
    "Elements/Foundations/Words.lean": ("S22", "the coordinator, who owns the foundations"),
}

# ---------------------------------------------------------------------------------------
# Findings.

failures: list[tuple[str, str, int, str]] = []   # (rule, file, line, message)
reports: dict[str, list[tuple[str, int, str]]] = defaultdict(list)
reach_found: set[tuple[str, str]] = set()   # (file, rule) of REACH_PENDING with a finding
lean_short: list[str] = []   # why S12 did not put every name to Lean, when it did not

RULES = {
    "S1": "an em dash",
    "S2": "crew talk outside quotations",
    "S3": "the first person singular outside quotations",
    "S4": "a hedge for a checker outside quotations",
    "S5": "Heath's references called Euclid's, or Postulate 5 'never needed'",
    "S6": "'tacit assumption' or 'tacit law' outside quotations",
    "S7": "a definition without its book",
    "S8": "a curly quotation mark",
    "S9": "an italic letter",
    "S10": "TeX in the mishnah, outside a well-formed $…$ of the modern way",
    "S11": "a retired refrain",
    "S12": "a backticked Lean name that Lean does not know",
    "S13": "an idea figure's caption missing or over 50 words",
    "S14": "an idea figure's canvas, colours or title",
    "S15": "a Euclid's figure's canvas, letters, colours, strokes, caption or title",
    "S16": "figure letters not all and only Heath's",
    "S17": "a further-reading file's shape or links",
    "S18": "a book with pages and no introduction",
    "S19": "a book introduction that does not link the book's brief",
    "S20": "an idea figure's letter not Heath's, or not upright, at 14 and in the ink of what it stands on",
    "S21": "a point of an idea figure without its letter",
    "S22": "letters in backticks, where they are plain",
    "S23": "a merge-conflict marker",
    "S24": "a modern figure's canvas, colours, strokes, title, or paragraph to stand under",
    "S25": "a modern figure's text not Euclid's figure's letters, upright, or the modern way's names, italic",
    "S26": "one letter, one point: a letter drawn twice in a figure, or near a stroke, a dot or the edge",
}

REPORTS = {
    "D4": "a mishnah with more than four distinct Lean names",
    "D5": "an idea caption over 40 words, or of more than two sentences",
    "D6": "'first', 'only', 'better', 'best', 'unlike': a comparison or a claim to priority?",
    "D7": "'Lean cannot' (say what our representation does)",
    "D8": "'gives no citation' and its kin (say 'Heath gives no reference')",
    "D9": "'need' joined to Postulate 5 (say 'uses')",
    "D10": "S6 or S7 outside their failing scope",
    "D11": "Euclid's figure strokes or dots off the usual widths",
    "D14": "figures at a glance not yet lettered (S21 holds them once the switch is on)",
    "D15": "figures whose letters are all italic, while the switch for upright letters is off (with it on, S15 and S20 fail them)",
    "D16": "the reach of 19 October, of a rule its file is still listed for in REACH_PENDING (fails once it is out)",
}


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def fail(rule: str, path: Path, line: int, message: str, *, new: bool = False) -> None:
    """A failure; or, for a finding of the new reach (`new`) of a rule its file is still
    listed for in REACH_PENDING, a D16 report, with the rule it would fail."""
    pending = REACH_PENDING.get(rel(path))
    if new and pending and rule in pending[0].split():
        reach_found.add((rel(path), rule))
        report("D16", path, line, f"{rule}: {message}")
    else:
        failures.append((rule, rel(path), line, message))


def report(rule: str, path: Path, line: int, message: str) -> None:
    reports[rule].append((rel(path), line, message))


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def excerpt(text: str, start: int, end: int, width: int = 50) -> str:
    """The match with a little context, on one line."""
    a = max(0, start - width)
    b = min(len(text), end + width)
    s = " ".join(text[a:b].split())
    return ("…" if a else "") + s + ("…" if b < len(text) else "")


MARKER_SKIP_DIRS = {
    ".git", ".lake", "__pycache__", ".pytest_cache", ".mypy_cache", ".ruff_cache",
    ".tox", ".venv", "venv", "node_modules", "build", "dist", "_build",
}
CONFLICT_EDGE = re.compile(r"^(<{7}|\|{7}|>{7})(?: |$)")
CONFLICT_MIDDLE = re.compile(r"={7}[ \t]*")
CONFLICT_KINDS = {"<": "opening", "|": "base", ">": "closing"}
LINK_REFERENCE_OPEN = re.compile(r"^ {0,3}\[")
GFM_WHITESPACE_CHARS = " \t\n\v\f\r"
GFM_WHITESPACE = r"[ \t\n\v\f\r]"
# A block quote or list item: a seven-equals line after one cannot underline a
# paragraph (a setext underline is never a lazy continuation), so S23 refuses it.
CONTAINER_START = re.compile(r"^ {0,3}(?:>|[-+*](?:[ \t]|$)|[0-9]{1,9}[.)](?:[ \t]|$))")
# Of those, the ones that may interrupt a paragraph: a block quote, a bullet item with
# some text, or an ordered one numbered 1 with some text. Any other goes on with it.
PARAGRAPH_CONTAINER_START = re.compile(
    rf"^ {{0,3}}(?:>|(?:[-+*]|0{{0,8}}1[.)])[ \t]{GFM_WHITESPACE}*[^ \t\n\v\f\r])")
HTML_RAW_NAMES = r"script|pre|style|textarea"
HTML_RAW_START = re.compile(
    rf"^ {{0,3}}<({HTML_RAW_NAMES})(?:{GFM_WHITESPACE}|>|$)", re.I)
HTML_RAW_END = rf"</(?:{HTML_RAW_NAMES})>"
HTML_CDATA_START = re.compile(r"^ {0,3}<!\[CDATA\[")
HTML_DECLARATION_START = re.compile(r"^ {0,3}<![A-Z]")
HTML_INSTRUCTION_START = re.compile(r"^ {0,3}<\?")
HTML_BLOCK_TAG_START = re.compile(
    r"^ {0,3}</?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|"
    r"colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|"
    r"frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|"
    r"nav|noframes|ol|optgroup|option|p|param|search|section|source|summary|table|tbody|td|"
    rf"tfoot|th|thead|title|tr|track|ul)(?:{GFM_WHITESPACE}|/?>|$)", re.I)
HTML_TAG_NAME = r"[A-Za-z][A-Za-z0-9-]*"
HTML_ATTRIBUTE_NAME = r"[A-Za-z_:][A-Za-z0-9_.:-]*"
HTML_ATTRIBUTE_VALUE = r'''(?:[^ \t\n\v\f\r"'=<>`]+|'[^']*'|"[^"]*")'''
HTML_ATTRIBUTE = (rf"(?:{GFM_WHITESPACE}+{HTML_ATTRIBUTE_NAME}"
                  rf"(?:{GFM_WHITESPACE}*={GFM_WHITESPACE}*{HTML_ATTRIBUTE_VALUE})?)")
HTML_COMPLETE_TAG = re.compile(
    rf"^ {{0,3}}(?:<(?!(?i:{HTML_RAW_NAMES})(?![A-Za-z0-9-])){HTML_TAG_NAME}"
    rf"{HTML_ATTRIBUTE}*{GFM_WHITESPACE}*/?>|"
    rf"</{HTML_TAG_NAME}{GFM_WHITESPACE}*>){GFM_WHITESPACE}*$")


def possible_reference_label(line: str, active: bool | None) -> tuple[bool | None, bool]:
    """Carry a possible link-reference label across lines and recognize its colon."""
    if active is None:
        match = LINK_REFERENCE_OPEN.match(line)
        if not match:
            return None, False
        active = False
        at = match.end()
    else:
        at = 0
    while at < len(line):
        if line[at] == "\\" and at + 1 < len(line):
            active = True
            at += 2
        elif line[at] == "[":
            return None, False
        elif line[at] == "]":
            return None, bool(active and line[at + 1:at + 2] == ":")
        else:
            active = active or line[at] not in GFM_WHITESPACE_CHARS
            at += 1
    return active, False


def spaces_or_tabs_only(text: str) -> bool:
    """Whether text is empty or consists only of Markdown blank-line characters."""
    return not text.strip(" \t")


def table_block_boundary(line: str) -> bool:
    """Whether a line ends a GFM table instead of becoming its next row."""
    return (spaces_or_tabs_only(line) or ATX_LINE.match(line) is not None
            or THEMATIC_LINE.fullmatch(line) is not None
            or CONTAINER_START.match(line) is not None
            or line.expandtabs(4).startswith("    "))


def repository_files(root: Path):
    """S23's paths: Git's tracked paths, or a pruned walk in a copy without Git.

    Do not consult ignore rules or prune tracked paths. In a checkout, Git missing or
    failing stops the check, rather than silently leaving tracked files unread or
    reading untracked ones. A traversal error raises with its path. The walk never
    follows symlinks, and the scanner skips any that Git lists.
    """
    if (root / ".git").exists():
        result = subprocess.run(["git", "ls-files", "-z"], cwd=root,
                                capture_output=True, check=True)
        for name in result.stdout.split(b"\0"):
            if name:
                yield root / os.fsdecode(name)
        return
    def walk_error(error: OSError) -> None:
        raise OSError(f"could not scan {error.filename}: {error}") from error

    for folder, dirs, files in os.walk(root, onerror=walk_error):
        dirs[:] = sorted(d for d in dirs if d not in MARKER_SKIP_DIRS
                         and not (Path(folder) / d).is_symlink())
        for name in sorted(files):
            path = Path(folder) / name
            if path.name != ".git" and not path.is_symlink() and path.is_file():
                yield path


def conflict_markers(text: str, *, markdown: bool) -> list[tuple[int, str]]:
    """Return (line, kind), without blanking comments, strings or fenced code.

    Edges begin with exactly seven identical characters followed by a space or
    the line's end. A middle has exactly seven equals, with optional trailing
    horizontal space. No other length is examined as a middle, so S23 errs toward
    refusal in doubtful contexts: an author whose heading is refused can use eight
    equals. Outside a conflict, a lone Markdown middle is allowed only when every
    line of the preceding block is ordinary paragraph text. The block ends at a
    blank line, marker, ATX or completed setext heading, thematic break, fence, HTML
    block or GFM table. Any possible link reference definition prefix (up to three
    spaces, a bracketed label allowing escaped brackets and line breaks, then a colon)
    disqualifies the whole block, even with no destination yet or extra words after it.
    Thus "[label]: destination extra words" is refused with seven equals despite
    being paragraph text. An indented line (four columns, tabs expanded) cannot
    start a paragraph, but may continue one. Paragraphs may span several lines. A
    fence inside a comment, or a comment inside a fence, opens no block. This is
    not a full CommonMark parser.
    """
    lines = text.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    edges = [CONFLICT_EDGE.match(line) for line in lines]
    last_close = max((i for i, edge in enumerate(edges)
                      if edge and edge[1][0] == ">"), default=-1)
    found = []
    conflict_depth = 0
    fence = html_end = ""
    comment = paragraph = False
    table = False
    reference_definition = False
    reference_label: bool | None = None
    for i, (line, edge) in enumerate(zip(lines, edges)):
        block = False
        if markdown:
            match = FENCE_LINE.fullmatch(line)
            if fence:
                block = True
                if (match and match[1][0] == fence[0] and len(match[1]) >= len(fence)
                        and spaces_or_tabs_only(match[2])):
                    fence = ""
            elif comment:
                block = True
                comment = "-->" not in line
            elif html_end:
                block = True
                if html_end == "\n":
                    block = not spaces_or_tabs_only(line)
                    if not block:
                        html_end = ""
                elif re.search(html_end, line, re.I):
                    html_end = ""
            elif re.match(r"^ {0,3}<!--", line):
                block = True
                comment = "-->" not in line
            else:
                if HTML_RAW_START.match(line):
                    block = True
                    html_end = HTML_RAW_END
                elif HTML_CDATA_START.match(line):
                    block = True
                    html_end = r"\]\]>"
                elif HTML_DECLARATION_START.match(line):
                    block = True
                    html_end = ">"
                elif HTML_INSTRUCTION_START.match(line):
                    block = True
                    html_end = r"\?>"
                elif HTML_BLOCK_TAG_START.match(line) or (
                        not paragraph and HTML_COMPLETE_TAG.fullmatch(line)):
                    block = True
                    html_end = "\n"
                elif match and (match[1][0] != "`" or "`" not in match[2]):
                    fence = match[1]
                    block = True
                if block and html_end != "\n" and re.search(html_end, line, re.I):
                    html_end = ""
            if block:
                table = False
            elif table:
                if table_block_boundary(line):
                    table = False
                else:
                    block = True
            if (not block and paragraph and i
                    and gfm_table_columns(lines[i - 1], line) is not None):
                table = True
                block = True
        kind = None
        if edge:
            char = edge[1][0]
            kind = CONFLICT_KINDS[char]
            if char == "<":
                conflict_depth += 1
            elif char == ">":
                conflict_depth = max(0, conflict_depth - 1)
        elif CONFLICT_MIDDLE.fullmatch(line):
            if (conflict_depth and i < last_close or not markdown or block or not paragraph
                    or reference_definition):
                kind = "middle"
        if kind:
            found.append((i + 1, kind))
        if (kind or block or spaces_or_tabs_only(line) or ATX_LINE.match(line)
                or THEMATIC_LINE.fullmatch(line)
                or paragraph and SETEXT_LINE.fullmatch(line)):
            paragraph = False
            reference_definition = False
            reference_label = None
        else:
            reference_label, completed_reference = possible_reference_label(
                line, reference_label)
            if completed_reference or (PARAGRAPH_CONTAINER_START if paragraph
                                       else CONTAINER_START).match(line):
                reference_definition = True
                paragraph = False
            elif not paragraph and line.expandtabs(4).startswith("    "):
                paragraph = False
            else:
                paragraph = True
    return found


def check_conflict_markers() -> None:
    """S23 covers raw text independently of prose scopes, skipping symlinks.

    A tracked symlink's text is its target path, not the bytes of its target.
    """
    for path in repository_files(ROOT):
        if path.is_symlink() or not path.is_file():
            continue
        data = path.read_bytes()
        if b"\0" in data:
            continue
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError:
            continue
        for line, kind in conflict_markers(text, markdown=path.suffix.lower() == ".md"):
            fail("S23", path, line, f"{kind} merge-conflict marker")


# ---------------------------------------------------------------------------------------
# Blanking: each helper returns a string of the same length, with the spans it removes
# turned to spaces and their newlines kept.

def _blank(m: re.Match) -> str:
    return re.sub(r"[^\n]", " ", m.group(0))


HTML_COMMENT = re.compile(r"<!--.*?-->", re.S)
PARAGRAPH_BREAK = re.compile(r"(\n[ \t]*\n)")
QUOTATION = re.compile(r'"[^"]*"')
# Square brackets that are not a link's text: Heath's references, [Def. 15].
SQUARE = re.compile(r"\[[^\[\]\n]*\](?![(\[])")


def blank_blocks(text: str) -> str:
    """HTML comments and fenced blocks blanked, code spans kept: the text whose paragraphs
    S10 reads, so that a line holding only a code span goes on with its paragraph."""
    return blank_html_comments(blank_fences(text))


def blank_code(text: str, *, indented_code: bool = True,
               reference_labels: set[str] | None = None, inline_html: bool = False) -> str:
    """Fenced blocks, code spans and HTML comments blanked: what a reader reads as prose,
    quotations included."""
    syntax = markdown_syntax(text, indented_code=indented_code,
                             reference_labels=reference_labels, inline_html=inline_html)
    ranges = (syntax.comments + syntax.destinations
              + [(span.start, span.end) for span in syntax.spans]
              + markdown_blocks(text, indented_code=indented_code).fences)
    return blank_ranges(text, ranges)


def blank_quotes(text: str) -> str:
    """Each "…" span blanked, within one paragraph: an unmatched quotation mark never
    swallows the paragraphs after it."""
    parts = PARAGRAPH_BREAK.split(text)
    return "".join(p if PARAGRAPH_BREAK.fullmatch(p) else QUOTATION.sub(_blank, p)
                   for p in parts)


def straighten(text: str) -> str:
    """Curly apostrophes and quotation marks made straight, so that "Euclid’s own" is
    caught as "Euclid's own". S8 reports the curly marks themselves."""
    return text.translate(str.maketrans({"’": "'", "‘": "'", "“": '"', "”": '"'}))


def paragraphs(text: str):
    """(offset, paragraph) for each paragraph of a Markdown text, trimmed."""
    off = 0
    for part in PARAGRAPH_BREAK.split(text):
        if part.strip() and not PARAGRAPH_BREAK.fullmatch(part):
            yield off + len(part) - len(part.lstrip()), part.strip()
        off += len(part)


SENTENCE_END = re.compile(r'(?<=[.?!])["\')*]*\s+(?=["*(\[`]?[A-Z])')


# A paragraph break, or a new line opening a heading, a list item or a table row.
BLOCK_BREAK = re.compile(r"\n[ \t]*\n|\n(?=[ \t]*(?:#|[-*] |\d+\. |\|))")
MARKDOWN_BLOCK_BREAK = re.compile(
    r"\n[ \t]*\n|\n(?= {0,3}(?:#{1,6}(?:[ \t]|$)"
    r"|[-+*][ \t]+\S|0{0,8}1[.)][ \t]+\S|>|```|~~~|<[A-Za-z/!?]"
    r"|([-*_])(?:[ \t]*\1){2,}[ \t]*$|(?:=+|-+)[ \t]*$"
    r"|[^\n]*\n {0,3}(?=[^\n]*\|)\|?(?:[ \t]*:?-+:?[ \t]*\|)*[ \t]*:?-+:?[ \t]*\|?[ \t]*$))",
    re.M)


def sentences(text: str):
    """(offset, sentence), split at a paragraph, heading, list item or table row, and after
    ".", "?" or "!" before a capital. "I.29", "vol. 1" and "C.N. 1" stay whole; "Def. I.15"
    is split, which no rule here minds."""
    start = 0
    for m in list(BLOCK_BREAK.finditer(text)) + [None]:
        end = m.start() if m else len(text)
        block = text[start:end]
        at = 0
        for s in SENTENCE_END.finditer(block):
            yield start + at, block[at:s.start()]
            at = s.end()
        yield start + at, block[at:]
        start = m.end() if m else len(text)


# ---------------------------------------------------------------------------------------
# The files of each scope.

def books_with_pages() -> list[str]:
    found = set(heath.BOOKS)
    for d in ("mishnah", "book", "figures"):
        base = ROOT / d
        if base.is_dir():
            found |= {p.name for p in base.iterdir() if p.is_dir() and p.name in heath.ROMAN}
    return sorted(found, key=heath.arabic)


def numbered(directory: Path, suffix: str) -> list[Path]:
    """NN<suffix> files of a book directory, in order."""
    if not directory.is_dir():
        return []
    return sorted(p for p in directory.iterdir() if re.fullmatch(r"\d\d" + re.escape(suffix), p.name))


def mishnah_files() -> list[Path]:
    return [p for b in books_with_pages() for p in numbered(ROOT / "mishnah" / b, ".md")]


def intro_files() -> list[Path]:
    return sorted((ROOT / "mishnah" / "intro").glob("*.md"), key=lambda p: heath.arabic(p.stem)
                  if p.stem in heath.ROMAN else 99)


def reading_files() -> list[Path]:
    return [p for b in books_with_pages() for p in numbered(ROOT / "reading" / b, ".md")]


REPORTS_DIR = ROOT / "docs" / "reports"


def is_catalogue(path: Path) -> bool:
    """The gap catalogues and the overlap catalogue: reports that describe the edition as
    it stands, and are kept up to date with it."""
    return path.parent == REPORTS_DIR and (fnmatch.fnmatchcase(path.name, "gaps-book-*.md")
                                           or path.name == "overlaps.md")


def is_report(path: Path) -> bool:
    """Any other report of docs/reports/, save an outside review, which keeps its
    reviewer's words as written. The crew's own logs, docs/reports/crew/, are not read."""
    return (path.parent == REPORTS_DIR and path.suffix == ".md" and not is_catalogue(path)
            and not path.name.startswith("outside-review-"))


def catalogue_files() -> list[Path]:
    return sorted(p for p in REPORTS_DIR.glob("*.md") if is_catalogue(p))


def report_files() -> list[Path]:
    return sorted(p for p in REPORTS_DIR.glob("*.md") if is_report(p))


def front_files() -> list[Path]:
    """book/<book>/front.md: a book's definitions, with their Lean, written by render.py
    from heath/<book>/front.md and its own table, FRONT_LEAN."""
    return [p for b in books_with_pages() if (p := ROOT / "book" / b / "front.md").exists()]


def generated_files() -> list[Path]:
    """The pages render.py writes that the rules read: CERTIFICATE.md, GRAPH.md, each
    book's index and front page, and the table of names. The proposition pages are made
    of the sources the other scopes read."""
    files = [ROOT / "CERTIFICATE.md", ROOT / "GRAPH.md"]
    files += [ROOT / "book" / b / "index.md" for b in books_with_pages()]
    files += front_files() + [ROOT / "book" / "names.md"]
    return [p for p in files if p.exists()]


# The generated files that came under the rules with the reach of #66: every finding in
# them is of that reach.
def is_new_generated(path: Path) -> bool:
    return path in front_files() or path == ROOT / "book" / "names.md"


def review_files() -> list[Path]:
    return [p for b in books_with_pages() for p in numbered(ROOT / "review" / b, ".toml")]


# The texts of a review record that its page shows (render.py): the field table's
# statement, extra hypotheses, argument, representation and overlap; the figure note, its
# case and its note; the clause map's claims; and the passages' notes. Heath's own words
# (`omitted`, `text_only`, a passage's `at`) are check_fidelity.py's, and the name a
# `helper` gives is Lean's.
REVIEW_SHOWN = {"statement": ("note", "short", "hypotheses"), "route": ("note",),
                "representation": ("note",), "overlap": ("note",),
                "coverage": ("checked", "explains"), "passage": ("note",),
                "figure": ("case", "note")}
# In review/terms.toml, what a page shows of each tag: its meaning (the Representation
# row, where a record has no note of its own) and its badge.
TERMS_SHOWN = ("meaning", "badge")
# A TOML file read token by token, so that a "#" inside a string is no comment and a
# quotation inside a comment is no string: multi-line strings first (an escape, a line
# break after a backslash, and up to two quotation marks before the closing three among
# their text), then one-line strings, then comments. Each string is checked by decoding it.
TOML_TOKEN = re.compile(r'"""(?:[^"\\]|\\[\s\S]|"(?!""))*"{3,5}'
                        r"|'''(?:[^']|'(?!''))*'{3,5}"
                        r'|"(?:[^"\\\n]|\\.)*"|\'[^\'\n]*\'|#[^\n]*')
TOML_HEADER = re.compile(r"^[ \t]*(\[\[?)[ \t]*([A-Za-z0-9_.-]+)[ \t]*\]\]?[ \t]*$",
                         re.M)
TOML_ASSIGNMENT = re.compile(r"^[ \t]*([A-Za-z0-9_-]+)[ \t]*=", re.M)


class TomlStringLocation(NamedTuple):
    line0: int
    last: int
    lines: list[int]


def decode_toml_string(token: str, first_line: int) -> tuple[str, list[int]]:
    """Decode one TOML string and retain the source line of every decoded character."""
    multiline = token.startswith(('"""', "'''"))
    basic = token.startswith('"')
    width = 3 if multiline else 1
    content = token[width:-width]
    source = width
    if multiline and content.startswith("\r\n"):
        content, source = content[2:], source + 2
    elif multiline and content.startswith("\n"):
        content, source = content[1:], source + 1

    decoded = []
    lines = []

    def emit(value: str, at: int) -> None:
        decoded.extend(value)
        lines.extend([first_line + token.count("\n", 0, at)] * len(value))

    simple = {'b': '\b', 't': '\t', 'n': '\n', 'f': '\f', 'r': '\r', '"': '"', '\\': '\\'}
    at = 0
    while at < len(content):
        absolute = source + at
        if basic and content[at] == "\\":
            continuation = re.match(r"\\[ \t]*\r?\n[ \t\r\n]*", content[at:])
            if multiline and continuation:
                at += continuation.end()
                continue
            escaped = content[at + 1]
            if escaped in simple:
                emit(simple[escaped], absolute)
                at += 2
                continue
            digits = 4 if escaped == "u" else 8
            emit(chr(int(content[at + 2:at + 2 + digits], 16)), absolute)
            at += 2 + digits
            continue
        if content.startswith("\r\n", at):
            emit("\n", absolute)
            at += 2
            continue
        emit(content[at], absolute)
        at += 1
    return "".join(decoded), lines


def toml_string_locations(raw: str) -> dict[tuple[str, int, str, int], TomlStringLocation]:
    """Decoded source locations, keyed by table, table-array occurrence, key and index."""
    tokens = []
    masked = list(raw)
    for m in TOML_TOKEN.finditer(raw):
        if m.group(0).startswith("#"):
            for i in range(m.start(), m.end()):
                if masked[i] != "\n":
                    masked[i] = " "
            continue
        try:
            text = tomllib.loads("s = " + m.group(0))["s"]
        except tomllib.TOMLDecodeError:
            continue
        decoded, lines = decode_toml_string(m.group(0), line_of(raw, m.start()))
        tokens.append((m, text, lines if decoded == text else []))
        for i in range(m.start(), m.end()):
            if masked[i] != "\n":
                masked[i] = " "
    syntax = "".join(masked)
    events = sorted([(m.start(), "header", m) for m in TOML_HEADER.finditer(syntax)]
                    + [(m.start(), "assignment", m)
                       for m in TOML_ASSIGNMENT.finditer(syntax)])
    table, occurrence = "", 0
    occurrences: dict[str, int] = defaultdict(int)
    found = {}
    for n, (_, kind, m) in enumerate(events):
        if kind == "header":
            table = m.group(2)
            if m.group(1) == "[[":
                occurrence = occurrences[table]
                occurrences[table] += 1
            else:
                occurrence = 0
            continue
        end = events[n + 1][0] if n + 1 < len(events) else len(raw)
        values = [(token, text, lines) for token, text, lines in tokens
                  if m.end() <= token.start() < end]
        for index, (token, text, lines) in enumerate(values):
            starts_below = re.match(r'("""|' + "'''" + r')(\\[ \t]*)?\r?\n',
                                    token.group(0)) is not None
            first = line_of(raw, token.start())
            last = line_of(raw, token.end() - 1)
            if len(lines) != len(text):
                lines = [min(first + text.count("\n", 0, at), last)
                         for at in range(len(text))]
            found[(table, occurrence, m.group(1), index)] = TomlStringLocation(
                first - (0 if starts_below else 1), last, lines)
    return found


class ReviewText(NamedTuple):
    line0: int
    key: str
    text: str
    last: int | None
    line_at: object


def review_texts(raw: str, terms: bool = False) -> list[ReviewText]:
    """Reader-visible review strings with decoded offsets mapped to their source lines."""
    try:
        data = tomllib.loads(raw)
    except tomllib.TOMLDecodeError:
        return []
    wanted = []
    if terms:
        tags = data.get("tag")
        for tag, table in (tags.items() if isinstance(tags, dict) else []):
            wanted += [(f"tag.{k}", table[k], (f"tag.{tag}", 0, k, 0))
                       for k in TERMS_SHOWN
                       if isinstance(table, dict) and isinstance(table.get(k), str)]
    else:
        for section, keys in REVIEW_SHOWN.items():
            tables = data.get(section)
            tables = [tables] if isinstance(tables, dict) else tables
            for occurrence, table in enumerate(tables if isinstance(tables, list) else []):
                for k in keys:
                    v = table.get(k) if isinstance(table, dict) else None
                    values = [v] if isinstance(v, str) else v if isinstance(v, list) else []
                    for index, t in enumerate(values):
                        if isinstance(t, str):
                            wanted.append((f"{section}.{k}", t,
                                           (section, occurrence, k, index)))
    where = toml_string_locations(raw)
    found = []
    for key, t, selector in wanted:
        location = where.get(selector)
        if location:
            line_at = lambda at, location=location: (location.lines[min(max(at, 0),
                len(location.lines) - 1)] if location.lines else location.last)
            found.append(ReviewText(location.line0, key, t, location.last, line_at))
        else:
            found.append(ReviewText(0, key, t, None, text_lines(t)))
    return sorted(found, key=lambda x: x.line0)


def ref_of(path: Path) -> str | None:
    """"I.5" for mishnah/I/05.md, reading/I/05.md, figures/I/05-idea.svg or
    figures/I/05-modern.svg."""
    m = re.fullmatch(r"(\d\d)(?:-idea|-modern)?\.(?:md|svg)", path.name)
    if m and path.parent.name in heath.ROMAN:
        return f"{path.parent.name}.{int(m.group(1))}"
    return None


def readme_text() -> str:
    """README.md, with its section "How it was made" blanked (it says how the work was
    done, and may name the roles)."""
    text = (ROOT / "README.md").read_text(encoding="utf-8")
    m = re.search(r"^## How it was made[^\n]*\n.*?(?=^## |\Z)", text, re.S | re.M)
    if m:
        text = text[:m.start()] + _blank(m) + text[m.end():]
    return text


def lean_notes(path: Path) -> str:
    """The Lean file with everything but its notes blanked: the text inside each `/- … -/`
    block and docstring (nested blocks included), save the docstring of `theorem PropN`,
    which is Heath's enunciation. The `--` lines outside blocks are Heath's proof."""
    m = re.fullmatch(r"Prop(\d+)\.lean", path.name)
    n = int(m.group(1)) if m and path.parent.name.startswith("Book") else None
    return notes_text(path.read_text(encoding="utf-8"), n)


def lean_note_spans(src: str, n: int | None = None) -> list[tuple[int, int]]:
    """The source ranges of a Lean file's reader-visible block-comment interiors: of each
    block its `-/` closes, from past its `/-`, `/--` or `/-!` to that `-/`, the comments
    read as Lean reads them (`check_fidelity.lean_comments`)."""
    skip = None
    if n is not None:
        span = heath.theorem_span(src, n)
        if span is not None:
            skip = span.start
    spans = []   # (first, last) character of each note's text
    for i, _ in check_fidelity.lean_comments(src):
        if (src.startswith("/-", i) and i != skip
                and (end := check_fidelity.comment_end(src, i)) is not None):
            opener = 3 if src.startswith(("/--", "/-!"), i) else 2
            spans.append((i + opener, end - 2))
    return spans


def notes_text(src: str, n: int | None = None) -> str:
    """`lean_notes` of a Lean source; `n` names the `theorem PropN` whose docstring is
    blanked."""
    out = re.sub(r"[^\n]", " ", src)
    for a, b in lean_note_spans(src, n):
        out = out[:a] + src[a:b] + out[b:]
    return out


def lean_files() -> list[Path]:
    return sorted((ROOT / "Elements").rglob("*.lean"))


def check_lean_notes(path: Path, src: str, rendered: list) -> list:
    """The rules for a Lean file's notes: every rule of the Lean notes over all of them, as
    before #66, the rendered docstrings among them; then S6 and S7 over each rendered
    docstring as the pages show it, its white space made one space. Returns the rendered
    docstrings as texts for S12."""
    texts = []
    replaced: dict[str, set[int]] = defaultdict(set)
    for r in rendered:
        offset = shown_offsets(src, r.first, r.last)
        at = lambda x, offset=offset: line_of(src, offset(x))   # noqa: E731
        found: list[tuple[str, int]] = []
        check_text(path, r.doc, {"rendered"}, line_at=at, collect=found)
        for rule, x in found:
            replaced[rule].add(offset(x))
        texts.append(NamedText(path, r.doc, FOUNDATIONS_OPENS, line_at=at))
    m = re.fullmatch(r"Prop(\d+)\.lean", path.name)
    n = int(m.group(1)) if m and path.parent.name.startswith("Book") else None
    check_text(path, notes_text(src, n), {"lean"}, replaced=replaced, check_s22=False)
    for first, last in lean_note_spans(src, n):
        check_letters_in_code(path, src[first:last],
                              line_at=lambda at, first=first: line_of(src, first + at),
                              indented_code=False)
    return texts


def shown_offsets(src: str, first: int, last: int):
    """For a docstring whose text is `src[first:last]`, shown with its white space made
    one space: the offset in `src` of an offset in the text as shown."""
    words = [(m.start(), m.end()) for m in re.finditer(r"\S+", src[first:last])]
    starts, at = [], 0
    for a, b in words:
        starts.append(at)
        at += b - a + 1

    def offset(x: int) -> int:
        if not words:
            return first
        k = max(i for i, n in enumerate(starts) if n <= x) if x >= 0 else 0
        a, b = words[k]
        return first + a + min(x - starts[k], b - a)
    return offset


class Rendered(NamedTuple):
    """A docstring render.py copies onto the pages: its axiom, the first and last
    character of its text in the file, and the text as the pages show it, its white space
    made one space."""
    name: str
    first: int
    last: int
    doc: str


def rendered_docstrings() -> dict[str, list[Rendered]]:
    """The docstrings render.py copies onto the pages, by file: those of the tacit rules,
    and of any other axiom that is not a postulate or a definition (`render.axiom_groups`),
    as `render.load_axiom_docs` reads them, each found again in its file by
    `docstring_span`."""
    facts = render.load_facts()
    shown = set()
    for book, count in heath.BOOKS.items():
        for n in range(1, count + 1):
            proposition = facts.get(f"{book}.{n}")
            if not proposition or proposition["status"] == "sketched":
                continue
            entries = [proposition] + [
                entry for entry in render.attached_entries(proposition, facts)
                if entry["status"] != "sketched"
            ]
            for entry in entries:
                _, _, tacit, other = render.axiom_groups(entry)
                shown.update(tacit + other)

    found: dict[str, list[Rendered]] = defaultdict(list)
    sources: dict[str, str] = {}
    for name, (doc, path, line) in sorted(render.load_axiom_docs().items()):
        if name not in shown or not path:
            continue
        src = sources.setdefault(path, (ROOT / path).read_text(encoding="utf-8"))
        span = docstring_span(src, line, doc)
        if span is None:
            fail("S7", ROOT / path, line, f"the docstring render.py shows for `{name}` was not "
                 "found above its axiom, so the rules could not read it")
            continue
        found[path].append(Rendered(name, *span, doc))
    return found


def docstring_span(src: str, line: int, doc: str) -> tuple[int, int] | None:
    """The first and last character of the text of the docstring of the axiom whose name
    stands on line `line` of a Lean source, read as render.py reads it
    (`render.axiom_docstrings`, so none inside a remark: #349), if it reads as `doc` once
    its white space is made one space, as render.py reads it; else None."""
    for text, _, name, span in render.axiom_docstrings(src):
        if src.count("\n", 0, name) + 1 == line and " ".join(text.split()) == doc:
            return span
    return None


# ---------------------------------------------------------------------------------------
# The text rules. Each pattern is matched on the text the rule names (raw, without code,
# or outside quotations); every match is one finding.

# Between two words of a phrase: spaces, or one line break with the next line's indent
# and its comment leader ("--" in Lean, ">" in a Markdown quotation), so that a phrase is
# found however a line or a comment wraps it. A blank line ends the phrase. ANY_GAP is
# GAP or any white space, a blank line included: the gap of S2's "first mate" and of
# "Definition N", which have always been found across one.
GAP = r"(?:[ \t]+|[ \t]*\n[ \t]*(?:(?:--|>)[ \t]*)?)"
ANY_GAP = rf"(?:\s+|{GAP})"
LEADER = re.compile(r"\n[ \t]*(?:--|>)")


def flat(s: str) -> str:
    """A match on one line, as a finding shows it: "Lean\\n  -- cannot" is "Lean cannot"."""
    return " ".join(LEADER.sub(" ", s).split())


def phrase(*ps: str, gap: str = GAP) -> str:
    """The alternatives `ps`, each a pattern whose spaces stand for `gap`: "Lean cannot"
    matches "Lean cannot", "Lean\\ncannot" and "Lean\\n  -- cannot"."""
    return "(?:" + "|".join(p.replace(" ", gap) for p in ps) + ")"


def words(*ws: str) -> str:
    """Whole words of a list, plurals and possessives allowed: crew, crews, crew's. The
    words of "first mate" may stand apart by any white space, or wrap as GAP allows."""
    return r"\b" + phrase(*ws, gap=ANY_GAP) + r"(?:s|es)?\b"


EM_DASH = re.compile("—")
CREW = re.compile(words("crew", "captain", "first mate", "bosun", "sailor", "voyage", "fleet",
                        "enforcer", "polisher"), re.I)
# "Book I was …" is a book, not a person: an "I" right after the word "Book" or "Books"
# and one space, on one line, is passed over. After any other gap ("Book  I", "Book\nI")
# it is found, as it always was.
FIRST_PERSON = re.compile(r"(?<!\bBook )(?<!\bBooks )"
                          + phrase(r"\bI (?:am|was|have|think|found|would)\b")
                          + r"|\b[Mm](?:y|e)\b")
HEDGE = re.compile(phrase(r"\bnote that\b", r"\bstrictly speaking\b", r"\bit is worth noting\b"),
                   re.I)
# "never need" or "never needs" with Postulate 5, a postulate, parallels or "it" later in
# the same clause: "never need it", "I.1 to I.28 never need the fifth postulate".
EUCLID_CITES = re.compile(phrase(
    r"\bEuclid cites\b", r"\bEuclid's own bracketed\b",
    r"\bnever needs?\b(?=[^.;:!?]{0,40}?\b(?:it|postulates?|parallels?)\b)"), re.I)
TACIT = re.compile(phrase(r"\btacit (?:assumptions?|laws?)\b"), re.I)
DEFINITION = re.compile(phrase(r"\b(?:Definitions?|Defs?\.) \d+\b", gap=ANY_GAP))
CURLY = re.compile("[“”‘’]")
# Between two letters of S9's run: GAP, with commas among its spaces and tabs ("*AB, CD*",
# "*AB,\nCD*"). A blank line ends the run.
LETTER_GAP = r"(?:[ \t,]+|[ \t,]*\n[ \t]*(?:(?:--|>)[ \t]*)?[ \t,]*)"
ITALIC_LETTER = re.compile(r"(?:^|[^*])(\*[A-Z]+[′₀-₉]*(?:" + LETTER_GAP + r"[A-Z]+[′₀-₉]*)*\*)"
                           r"(?:$|[^*])", re.M)
TEX = re.compile(r"\\|\^\{|\$")
LEAN_CANNOT = re.compile(phrase(r"\bLean (?:cannot|can't|can not)\b"), re.I)
NO_CITATION = re.compile(phrase(r"\bno citations?\b"), re.I)
COMPARISON = re.compile(r"\b(?:first|only|better|best|unlike)\b", re.I)
NEED = re.compile(r"\bneed(?:s|ed)?\b", re.I)
POSTULATE_5 = re.compile(phrase(r"\bPostulate 5\b", r"\bPost\. 5\b", r"\bparallel postulate\b",
                                r"\bfifth postulate\b"), re.I)

# S22: a code span holding letters alone: a capital or a run of capitals (each with its
# prime or subscript), or several runs apart by commas or spaces: `P`, `PQ`, `ABCD`,
# `AB, CD`. Letters are plain (STYLE, section 1), Heath's and those of a step written over
# any letters alike, and the Lean's variables among them; no Lean name or expression of
# ours is capitals alone.
LETTER_RUN = r"(?:[A-Z][′'₀-₉]*)+"
LETTERS_ONLY = re.compile(rf"\s*{LETTER_RUN}(?:\s*,\s*{LETTER_RUN}|\s+{LETTER_RUN})*\s*")
LETTERS_IN_CODE = re.compile(r"`+([^`]+)`+")
BACKTICKS = re.compile(r"`+")
ATX_LINE = re.compile(r"^ {0,3}#{1,6}(?:[ \t]|$)")
LIST_LINE = re.compile(
    r"^(?P<indent> {0,3})(?:(?P<bullet>[-+*])|(?P<number>\d{1,9})[.)])"
    r"(?P<space>[ \t]+)(?P<body>.*)$")
FENCE_LINE = re.compile(r"^ {0,3}(`{3,}|~{3,})(.*)$")
THEMATIC_LINE = re.compile(r"^ {0,3}([-*_])(?:[ \t]*\1){2,}[ \t]*$")
SETEXT_LINE = re.compile(r"^ {0,3}(?:=+|-+)[ \t]*$")
TABLE_DELIMITER_CELL = re.compile(r":?-+:?")


HTML_BLOCK_TAGS = ("address|article|aside|base|basefont|blockquote|body|caption|center|col|"
                     "colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|"
                     "form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|"
                     "menu|menuitem|nav|noframes|ol|optgroup|option|p|param|search|section|"
                     "summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul")
# The first six HTML block kinds interrupt a paragraph; a complete tag on its own
# line, the seventh kind, opens a block only when no paragraph is open.
HTML_BLOCKS = (
    (re.compile(r"<(?:pre|script|style|textarea)(?:[ \t>]|$)", re.I),
     re.compile(r"</(?:pre|script|style|textarea)>", re.I)),
    (re.compile(r"<!--"), re.compile(r"-->")),
    (re.compile(r"<\?"), re.compile(r"\?>")),
    (re.compile(r"<![A-Za-z]"), re.compile(r">")),
    (re.compile(r"<!\[CDATA\["), re.compile(r"\]\]>")),
    (re.compile(rf"</?(?:{HTML_BLOCK_TAGS})(?:[ \t>]|/>|$)", re.I), None),
)
HTML_TAG_LINE = re.compile(r"(?:<[A-Za-z][A-Za-z0-9-]*(?:[ \t]+[A-Za-z_:][\w.:-]*"
                             r"(?:[ \t]*=[ \t]*(?:[^\s\"'=<>`]+|'[^']*'|\"[^\"]*\"))?)*"
                             r"[ \t]*/?>|</[A-Za-z][A-Za-z0-9-]*[ \t]*>)[ \t]*$")
INLINE_HTML = re.compile(
    r"(?:<[A-Za-z][A-Za-z0-9-]*(?:\s+[A-Za-z_:][\w.:-]*"
    r"(?:\s*=\s*(?:\"[^\"]*\"|'[^']*'|[^\s\"'=<>`]+))?)*\s*/?>"
    r"|</[A-Za-z][A-Za-z0-9-]*\s*>"
    r"|<\?.*?\?>"
    r"|<![A-Z].*?>"
    r"|<!\[CDATA\[.*?\]\]>)", re.S)

class InlineBlock(NamedTuple):
    text: str
    offsets: list[int]
    references: bool = True
    paragraph: bool = False


class CodeSpan(NamedTuple):
    start: int
    end: int
    content: str
    offsets: list[int]


class MarkdownBlocks(NamedTuple):
    inline: list[InlineBlock]
    fences: list[tuple[int, int]]
    comments: list[tuple[int, int]]


def table_cell_ranges(line: str) -> tuple[list[tuple[int, int]], bool]:
    """The source ranges of a GFM row's cells, and whether the row has a separator."""
    pipes = []
    slashes = 0
    for at, char in enumerate(line):
        if char == "\\":
            slashes += 1
            continue
        if char == "|" and slashes % 2 == 0:
            pipes.append(at)
        slashes = 0
    if not pipes:
        return [(0, len(line))], False
    edges = [-1] + pipes + [len(line)]
    cells = [(edges[k] + 1, edges[k + 1]) for k in range(len(edges) - 1)]
    if spaces_or_tabs_only(line[:pipes[0]]):
        cells.pop(0)
    if cells and spaces_or_tabs_only(line[pipes[-1] + 1:]):
        cells.pop()
    return cells, True


def gfm_table_columns(header: str, delimiter: str) -> int | None:
    """Return a GFM table's column count when these lines start one."""
    header_cells, header_has_pipe = table_cell_ranges(header)
    delimiter_cells, delimiter_has_pipe = table_cell_ranges(delimiter)
    if ((header_has_pipe or delimiter_has_pipe)
            and len(header_cells) == len(delimiter_cells)
            and delimiter_cells
            and all(TABLE_DELIMITER_CELL.fullmatch(delimiter[a:b].strip(" \t"))
                    for a, b in delimiter_cells)):
        return len(header_cells)
    return None


# S24 and S25 retain their original whitespace reading, separate from S23 above.
def modern_table_cell_ranges(line: str) -> tuple[list[tuple[int, int]], bool]:
    """The source ranges of a GFM row's cells, and whether the row has a separator."""
    pipes = []
    slashes = 0
    for at, char in enumerate(line):
        if char == "\\":
            slashes += 1
            continue
        if char == "|" and slashes % 2 == 0:
            pipes.append(at)
        slashes = 0
    if not pipes:
        return [(0, len(line))], False
    edges = [-1] + pipes + [len(line)]
    cells = [(edges[k] + 1, edges[k + 1]) for k in range(len(edges) - 1)]
    if not line[:pipes[0]].strip():
        cells.pop(0)
    if cells and not line[pipes[-1] + 1:].strip():
        cells.pop()
    return cells, True


def modern_table_columns(header: str, delimiter: str) -> int:
    """The number of columns when two lines open a GFM table, or zero otherwise."""
    header_cells, header_has_pipe = modern_table_cell_ranges(header)
    delimiter_cells, delimiter_has_pipe = modern_table_cell_ranges(delimiter)
    if ((header_has_pipe or delimiter_has_pipe)
            and len(header_cells) == len(delimiter_cells)
            and delimiter_cells
            and all(TABLE_DELIMITER_CELL.fullmatch(delimiter[a:b].strip())
                    for a, b in delimiter_cells)):
        return len(header_cells)
    return 0


def table_inline_blocks(block: InlineBlock) -> list[InlineBlock]:
    """Split a recognized GFM table into independent, offset-preserving cells."""
    lines = []
    at = 0
    for line in block.text.split("\n"):
        lines.append((at, at + len(line), line))
        at += len(line) + 1
    table = None
    for k in range(len(lines) - 1):
        _, _, header = lines[k]
        _, _, delimiter = lines[k + 1]
        columns = modern_table_columns(header, delimiter)
        if columns:
            table = (k, columns)
            break
    if table is None:
        return [block]

    found = []
    table, columns = table
    header_start = lines[table][0]
    prefix_end = max(0, header_start - 1)
    if prefix_end:
        found.append(InlineBlock(block.text[:prefix_end], block.offsets[:prefix_end],
                                 block.references, block.paragraph))
    for row_number, row in enumerate([lines[table]] + lines[table + 2:]):
        start, _, text = row
        cells, _ = modern_table_cell_ranges(text)
        if row_number:
            cells = (cells + [(len(text), len(text))] * columns)[:columns]
        for a, b in cells:
            while a < b and text[a] in " \t":
                a += 1
            while b > a and text[b - 1] in " \t":
                b -= 1
            if a < b:
                found.append(InlineBlock(text[a:b], block.offsets[start + a:start + b], False))
    return found


def markdown_blocks(text: str, *, indented_code: bool = True,
                    raw_html: bool = False) -> MarkdownBlocks:
    """The inline leaf blocks, fences and comment blocks of a Markdown text, with source
    offsets retained after block quote and list markers are removed.

    Mark top-level paragraphs for modern_span. With `raw_html`, leave raw HTML blocks
    out of that selection, with their contents inert, including any apparent fences;
    the wording rules retain their existing reading of text inside HTML by default."""
    blocks: list[InlineBlock] = []
    fences = []
    comments = []
    chars: list[str] = []
    offsets: list[int] = []
    container = None
    list_item = None
    list_number = 0
    fence = None
    fence_start = 0
    comment = None
    comment_start = 0
    html = None

    def flush(paragraph: bool = True) -> None:
        nonlocal chars, offsets, container
        if chars:
            blocks.append(InlineBlock("".join(chars), offsets,
                                      paragraph=paragraph and container == (0, None)))
        chars, offsets, container = [], [], None

    def emit(body: str, source: list[int], own, newline: int) -> None:
        nonlocal container
        if container != own:
            flush()
            container = own
        if chars:
            chars.append("\n")
            offsets.append(newline)
        chars.extend(body)
        offsets.extend(source)

    at = 0
    lines = text.splitlines(keepends=True)
    if text and (not lines or sum(map(len, lines)) < len(text)):
        lines.append(text[sum(map(len, lines)):])
    for raw in lines:
        line_start = at
        line_end = at + len(raw)
        body = raw.rstrip("\r\n")
        source = list(range(at, at + len(body)))
        at = line_end

        pos, quote = 0, 0
        while True:
            mark = pos
            while mark < len(body) and mark - pos < 3 and body[mark] == " ":
                mark += 1
            if mark >= len(body) or body[mark] != ">":
                break
            mark += 1
            if mark < len(body) and body[mark] in " \t":
                mark += 1
            pos, quote = mark, quote + 1
        base_body, base_source = body[pos:], source[pos:]
        consumed = False
        while True:
            body, source = base_body, base_source
            literal = fence is not None or comment is not None or html is not None
            listed = LIST_LINE.match(body)
            interrupts = (container is not None
                          and not (list_item and list_item[0] == quote))
            if (listed and interrupts
                    and (not listed.group("body").strip()
                         or (listed.group("number") is not None
                             and int(listed.group("number")) != 1))):
                listed = None
            if listed and not literal:
                list_number += 1
                indent = listed.start("body")
                list_item = (quote, list_number, indent)
                body, source = listed.group("body"), source[indent:]
                own = (quote, list_number)
            elif list_item and list_item[0] == quote and body.strip():
                indent = list_item[2]
                leading = len(body) - len(body.lstrip(" "))
                owner = (quote, list_item[1])
                if leading >= indent:
                    body, source = body[indent:], source[indent:]
                    own = owner
                elif not literal and container == owner:
                    own = owner
                else:
                    list_item = None
                    own = (quote, None)
            elif list_item and list_item[0] == quote and literal:
                own = (quote, list_item[1])
            else:
                if list_item and list_item[0] != quote:
                    list_item = None
                own = (quote, None)

            starts_block = (not body.strip() or listed is not None or ATX_LINE.match(body)
                            or FENCE_LINE.match(body) or THEMATIC_LINE.fullmatch(body)
                            or SETEXT_LINE.fullmatch(body)
                            or re.match(r"^ {0,3}<!--", body))
            if (not literal and container is not None and quote < container[0]
                    and not starts_block):
                own = container

            if fence is not None:
                char, width, owner = fence
                if own != owner:
                    fences.append((fence_start, line_start))
                    fence = None
                    continue
                if re.fullmatch(rf" {{0,3}}{re.escape(char)}{{{width},}}[ \t]*", body):
                    fences.append((fence_start, line_end))
                    fence = None
                consumed = True
                break

            if comment is not None:
                if own != comment:
                    comments.append((comment_start, line_start))
                    comment = None
                    continue
                close = body.find("-->")
                if close >= 0:
                    comments.append((comment_start, source[close + 2] + 1))
                    comment = None
                    base_body, base_source = body[close + 3:], source[close + 3:]
                    if base_body:
                        continue
                consumed = True
                break
            if html is not None:
                end, owner = html
                if own != owner:
                    html = None
                    continue
                if (end is None and not body.strip()) or (end is not None and end.search(body)):
                    html = None
                consumed = True
                break
            break
        if consumed:
            continue

        leading = body[:len(body) - len(body.lstrip(" \t"))]
        indented = len(leading.expandtabs(4)) >= 4
        if indented_code and body.strip() and indented and not (chars and container == own):
            flush()
            fences.append((line_start, line_end))
            continue

        if raw_html:
            content = body.lstrip(" \t")
            indent = body[:len(body) - len(content)]
            if len(indent.expandtabs(4)) <= 3:
                end = next((e for s, e in HTML_BLOCKS if s.match(content)), False)
                if (end is False and not (chars and container == own)
                        and HTML_TAG_LINE.fullmatch(content)):
                    end = None
                if end is not False:
                    flush()
                    if end is None or not end.search(content):
                        html = (end, own)
                    continue

        opened_comment = re.match(r"^ {0,3}<!--", body)
        if opened_comment and "-->" not in body[opened_comment.end():]:
            flush()
            comment = own
            comment_start = line_start
            continue

        if list_item and own == (quote, None) and body.strip():
            list_item = None

        opened = FENCE_LINE.match(body)
        if opened and not (opened.group(1).startswith("`") and "`" in opened.group(2)):
            flush()
            fence = (opened.group(1)[0], len(opened.group(1)), own)
            fence_start = line_start
            continue
        if not body.strip():
            flush()
            continue
        if SETEXT_LINE.fullmatch(body):
            flush(paragraph=False)
            continue
        if THEMATIC_LINE.fullmatch(body):
            flush()
            continue
        if ATX_LINE.match(body):
            flush()
            blocks.append(InlineBlock(body, source))
            continue
        emit(body, source, own, line_start - 1)
    flush()
    if fence is not None:
        fences.append((fence_start, len(text)))
    if comment is not None:
        comments.append((comment_start, len(text)))
    inline = [cell for block in blocks for cell in table_inline_blocks(block)]
    return MarkdownBlocks(inline, fences, comments)


def blank_ranges(text: str, spans) -> str:
    """`text` with each half-open source span blanked and every newline retained."""
    out = text
    for start, end in spans:
        out = out[:start] + re.sub(r"[^\n]", " ", out[start:end]) + out[end:]
    return out


def blank_fences(text: str) -> str:
    return blank_ranges(text, markdown_blocks(text).fences)


class MarkdownSyntax(NamedTuple):
    spans: list[CodeSpan]
    comments: list[tuple[int, int]]
    destinations: list[tuple[int, int]]


class LinkDestination(NamedTuple):
    start: int
    end: int
    label: int
    deactivates_links: bool


def offset_runs(offsets: list[int]) -> list[tuple[int, int]]:
    """The half-open source ranges of a list of offsets, split where container markers
    fall between them."""
    runs: list[tuple[int, int]] = []
    for offset in offsets:
        if runs and runs[-1][1] == offset:
            runs[-1] = (runs[-1][0], offset + 1)
        else:
            runs.append((offset, offset + 1))
    return runs


def backslashes_before(text: str, at: int) -> int:
    return at - len(text[:at].rstrip("\\"))


def escapes_punctuation(text: str, at: int) -> bool:
    return (text[at:at + 1] == "\\" and at + 1 < len(text)
            and text[at + 1] in string.punctuation)


AUTOLINK = re.compile(
    r"<(?:[A-Za-z][A-Za-z0-9+.-]{1,31}:[^<>\x00-\x20]*"
    r"|[A-Za-z0-9.!#$%&'*+/=?^_`{|}~-]+@"
    r"[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?"
    r"(?:\.[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?)*)>"
)
REFERENCE_LABEL = re.compile(r"^ {0,3}\[((?:\\.|[^\[\]\\]){1,999})\]:")


def reference_title(text: str) -> bool:
    """Whether `text` is one complete CommonMark link-reference title."""
    if len(text) < 2 or (text[0], text[-1]) not in (("\"", "\""), ("'", "'"), ("(", ")")):
        return False
    closer = text[-1]
    at = 1
    while at < len(text) - 1:
        if escapes_punctuation(text, at):
            at += 2
        elif text[at] == closer:
            return False
        else:
            at += 1
    return at == len(text) - 1


def reference_definition_title(line: str) -> bool | None:
    """Whether a valid reference definition has a same-line title, or None if invalid."""
    match = REFERENCE_LABEL.match(line)
    if not match or not match.group(1).strip():
        return None
    at = match.end()
    while at < len(line) and line[at] in " \t":
        at += 1
    if at == len(line):
        return None
    if line[at] == "<":
        at += 1
        while at < len(line) and line[at] != ">":
            if line[at] == "<" or ord(line[at]) < 0x20:
                return None
            at += 2 if escapes_punctuation(line, at) else 1
        if at == len(line):
            return None
        at += 1
    else:
        depth = 0
        start = at
        while at < len(line) and line[at] not in " \t":
            if escapes_punctuation(line, at):
                at += 2
                continue
            if line[at] == "(":
                depth += 1
            elif line[at] == ")":
                depth -= 1
                if depth < 0:
                    return None
            elif line[at] == "<" or ord(line[at]) < 0x20:
                return None
            at += 1
        if at == start or depth:
            return None
    if at == len(line):
        return False
    if line[at] not in " \t":
        return None
    tail = line[at:].strip()
    if not tail:
        return False
    return True if reference_title(tail) else None


def reference_definition(line: str) -> bool:
    """Whether one line is a complete CommonMark link-reference definition."""
    return reference_definition_title(line) is not None


def reference_destination_ranges(text: str) -> list[LinkDestination]:
    """The consecutive link-reference definitions at the start of an inline block."""
    found = []
    lines = []
    offset = 0
    for line in text.split("\n"):
        lines.append((offset, line))
        offset += len(line) + 1
    k = 0
    while k < len(lines):
        start, line = lines[k]
        titled = reference_definition_title(line)
        if titled is None:
            break
        end = start + len(line)
        if not titled and k + 1 < len(lines):
            title_start, title_line = lines[k + 1]
            continuation = re.fullmatch(r" {0,3}(\S.*)", title_line)
            if continuation and reference_title(continuation.group(1)):
                end = title_start + len(title_line)
                k += 1
        found.append(LinkDestination(start, end, start, False))
        k += 1
    return found


def inline_destination_end(text: str, start: int) -> int | None:
    """The end of a valid CommonMark inline link target opened at `start`."""
    def space(at: int) -> int:
        while at < len(text) and text[at] in " \t":
            at += 1
        if at < len(text) and text[at] == "\n":
            at += 1
            while at < len(text) and text[at] in " \t":
                at += 1
        return at

    def title(at: int) -> int | None:
        pairs = {'"': '"', "'": "'", '(': ')'}
        if at >= len(text) or text[at] not in pairs:
            return None
        opener = text[at]
        closer = pairs[opener]
        at += 1
        while at < len(text):
            if escapes_punctuation(text, at):
                at += 2
            elif text[at] == closer:
                return at + 1
            elif opener == "(" and text[at] == "(":
                return None
            elif text[at] == "\n" and text[at:at + 2] == "\n\n":
                return None
            else:
                at += 1
        return None

    at = space(start + 1)
    if at >= len(text):
        return None
    if text[at] == ")":
        return at + 1
    if text[at] == "<":
        at += 1
        while at < len(text):
            if escapes_punctuation(text, at):
                at += 2
                continue
            if text[at] == ">":
                break
            if text[at] == "\n" or text[at] == "<" or ord(text[at]) < 0x20:
                return None
            at += 1
        if at == len(text):
            return None
        at += 1
    else:
        depth = 0
        began = at
        while at < len(text):
            char = text[at]
            if escapes_punctuation(text, at):
                at += 2
                continue
            if char == "(":
                depth += 1
            elif char == ")":
                if depth == 0:
                    break
                depth -= 1
            elif char.isspace() or ord(char) < 0x20:
                break
            at += 1
        if at == began or depth:
            return None
    if at < len(text) and text[at] == ")":
        return at + 1
    separated = space(at)
    if separated == at or separated >= len(text):
        return None
    if text[separated] == ")":
        return separated + 1
    titled = title(separated)
    if titled is None:
        return None
    closed = space(titled)
    return closed + 1 if closed < len(text) and text[closed] == ")" else None


def matching_link_label(text: str, close: int) -> int | None:
    """The unescaped `[` matched by the `]` at `close`, if there is one."""
    depth = 0
    for at in range(close - 1, -1, -1):
        if text[at] == "\n" and at and text[at - 1] == "\n":
            return False
        if backslashes_before(text, at) % 2:
            continue
        if text[at] == "]":
            depth += 1
        elif text[at] == "[":
            if depth == 0:
                return at
            depth -= 1
    return None


def reference_key(label: str) -> str:
    """A reference label with case and whitespace normalised for matching."""
    return " ".join(label.split()).casefold()


def document_reference_labels(text: str) -> set[str]:
    """Reference definitions throughout the document, excluding code and raw HTML."""
    labels = set()
    for block in markdown_blocks(text, raw_html=True).inline:
        if block.references:
            for definition in reference_destination_ranges(block.text):
                match = REFERENCE_LABEL.match(block.text[definition.start:definition.end])
                if match:
                    labels.add(reference_key(match.group(1)))
    return labels


def link_destination_ranges(text: str, *, references: bool = True,
                            reference_labels: set[str] | None = None,
                            inline_html: bool = False) -> list[LinkDestination]:
    """Link destinations and their label starts in one inline block."""
    found = reference_destination_ranges(text) if references else []
    found += [LinkDestination(m.start(), m.end(), m.start(), False)
              for m in AUTOLINK.finditer(text)
              if backslashes_before(text, m.start()) % 2 == 0]
    if inline_html:
        found += [LinkDestination(m.start(), m.end(), m.start(), False)
                  for m in INLINE_HTML.finditer(text)
                  if backslashes_before(text, m.start()) % 2 == 0]
    for match in re.finditer(r"\]", text):
        close = match.start()
        label = matching_link_label(text, close)
        if backslashes_before(text, close) % 2 or label is None:
            continue
        end = (inline_destination_end(text, close + 1)
               if text[close + 1:close + 2] == "(" else None)
        if end is None and reference_labels:
            identifier = re.match(r"\[((?:\\.|[^\[\]\\]){0,999})\]", text[close + 1:])
            key = identifier.group(1) if identifier else ""
            if not key:
                key = text[label + 1:close]
            if reference_key(key) in reference_labels:
                end = close + 1 + (identifier.end() if identifier else 0)
        if end is not None:
            image = (label > 0 and text[label - 1] == "!"
                     and backslashes_before(text, label - 1) % 2 == 0)
            found.append(LinkDestination(close, end, label, not image))
    return sorted(found)


def markdown_syntax(text: str, *, indented_code: bool = True,
                    reference_labels: set[str] | None = None,
                    inline_html: bool = False) -> MarkdownSyntax:
    """The CommonMark code spans and HTML comments of a Markdown text, with source offsets.
    Comments are the container-bounded comment blocks and the closed inline comments. In
    each inline leaf block, a code span and an inline comment are read in source order:
    whichever opens first is read, so a comment hides the backticks inside it, and a code
    span the comment markers inside it."""
    parsed = markdown_blocks(text, indented_code=indented_code)
    spans: list[CodeSpan] = []
    comments = list(parsed.comments)
    destinations = []
    for block in parsed.inline:
        ticks = [(m.start(), m.end()) for m in BACKTICKS.finditer(block.text)]
        openers = [m.start() for m in re.finditer("<!--", block.text)
                   if backslashes_before(block.text, m.start()) % 2 == 0]
        links = link_destination_ranges(block.text, references=block.references,
                                        reference_labels=reference_labels,
                                        inline_html=inline_html)
        active = {link.label: True for link in links}
        consumed: list[tuple[int, int]] = []
        i, pos = 0, 0
        while True:
            while i < len(ticks) and ticks[i][0] < pos:
                i += 1
            opener = next((at for at in openers if at >= pos), len(block.text))
            link = next((candidate for candidate in links
                         if candidate.start >= pos and active[candidate.label]
                         and not any(start <= candidate.label < end
                                     for start, end in consumed)),
                        LinkDestination(len(block.text), len(block.text),
                                        len(block.text), False))
            if i < len(ticks) and ticks[i][0] < min(opener, link[0]):
                raw_start, opened = ticks[i]
                start = raw_start + backslashes_before(block.text, raw_start) % 2
                width = opened - start
                close = next((j for j in range(i + 1, len(ticks))
                              if ticks[j][1] - ticks[j][0] == width), None) if width else None
                if close is None:
                    i += 1
                    continue
                closed, end = ticks[close]
                content = re.sub(r"\r\n?|\n", " ", block.text[opened:closed])
                if (len(content) >= 2 and content.startswith(" ") and content.endswith(" ")
                        and content.strip(" ")):
                    content = content[1:-1]
                source = block.offsets[start:end]
                spans.append(CodeSpan(source[0], source[-1] + 1, content, source))
                consumed.append((start, end))
                pos = end
                continue
            if link.start < opener:
                destinations.extend(offset_runs(block.offsets[link.start:link.end]))
                if link.deactivates_links:
                    for outer in links:
                        if (outer.deactivates_links and outer.label < link.label
                                and link.end <= outer.start):
                            active[outer.label] = False
                pos = link.end
                continue
            if opener == len(block.text):
                break
            close = block.text.find("-->", opener + 4)
            if close < 0:
                openers = []
                continue
            comments.extend(offset_runs(block.offsets[opener:close + 3]))
            consumed.append((opener, close + 3))
            pos = close + 3
    return MarkdownSyntax(spans, comments, destinations)


def code_span_details(text: str, *, indented_code: bool = True) -> list[CodeSpan]:
    """The CommonMark code spans in inline leaf blocks, with their source offsets."""
    return markdown_syntax(text, indented_code=indented_code).spans


def markdown_code_spans(text: str):
    """(start, end, content) of each code span of a Markdown text, read as CommonMark
    reads it: a backtick string is closed by the next string of the same length in its
    inline block; soft line endings become spaces, and one enclosing space is removed
    when the content is not all spaces. A run that finds no closer is text."""
    return [(span.start, span.end, span.content) for span in code_span_details(text)]


def html_comment_spans(text: str) -> list[tuple[int, int]]:
    """Closed HTML comments and container-bounded, line-opening comment blocks,
    excluding markers inside fenced blocks and code spans (markdown_syntax)."""
    return markdown_syntax(text).comments


def blank_html_comments(text: str) -> str:
    return blank_ranges(text, html_comment_spans(text))


def letter_spans(text: str, *, indented_code: bool = True) -> str:
    """S22's reading: `text` with every code span blanked but those that hold letters
    alone (LETTERS_ONLY), and everything outside a code span blanked too, so that
    LETTERS_IN_CODE finds each such span and nothing across two spans."""
    out = re.sub(r"[^\n]", " ", text)
    chars = list(out)
    for span in code_span_details(text, indented_code=indented_code):
        if LETTERS_ONLY.fullmatch(span.content):
            for offset in span.offsets:
                chars[offset] = text[offset]
    return "".join(chars)


def check_letters_in_code(path: Path, raw: str, *, line_at=None,
                          indented_code: bool = True, collect=None) -> None:
    """Apply S22 to one Markdown inline-block domain."""
    raw = raw.replace("\r\n", "\n")
    straight = straighten(raw)
    find_all("S22", LETTERS_IN_CODE, path,
             letter_spans(straight, indented_code=indented_code), raw,
             line_at=line_at or text_lines(raw), new=True, collect=collect)


# S11: retired refrains of STYLE section 3, and the mishnah allowed each ("nowhere" is
# the empty set).
REFRAINS = [
    (re.compile(phrase(r"\bcertificate (?:cites|records)\b")), set()),
    (re.compile(phrase(r"\bOf the postulates\b")), set()),
    (re.compile(phrase(r"\bbesides Euclid's\b")), set()),
    (re.compile(phrase(r"\bjust Euclid's three\b")), set()),
    (re.compile(phrase(r"\bcomes in through\b")), {"I.29"}),
    (re.compile(phrase(r"\bLean (?:wants it said|asks why|makes us say so)\b")),
     {"I.1", "I.5", "I.22"}),
    (re.compile(phrase(r"\b[Uu]ses Postulate 1\b")), {"I.1", "I.3"}),
    (re.compile(phrase(r"\bbrings it in\b")), {"I.1", "I.3"}),
    (re.compile(phrase(r"\bwith no letter\b")), set()),
    (re.compile(phrase(r"\bproves it once\b")), set()),
    (re.compile(phrase(r"\bWe give his argument once\b")), set()),
    (re.compile(phrase(r"\band the Lean cites it\.")), set()),
]
RETIRED_LEADS = re.compile(
    r"^\*\*" + phrase(r"What Lean made us say\.", r"What else Lean made us say\.",
                      r"What it rests on\.", r"Where the parallels meet\.", r"Naming the pieces\.",
                      r"Where [A-Z]+ falls\.") + r"\*\*", re.M)
UNDER_I31 = re.compile(phrase(r"\bunder I\.31\b"))
PROCLUS = re.compile(r"\bProclus\b")


def proclus_under_i31(text: str) -> list[tuple[int, int]]:
    """S11's "under I.31" in a sentence naming Proclus: the span of each in `text`."""
    spans = []
    for off, sent in sentences(text):
        m = UNDER_I31.search(sent)
        if m and PROCLUS.search(sent):
            spans.append((off + m.start(), off + m.end()))
    return spans


def find_all(rule: str, pattern: re.Pattern, path: Path, text: str, shown: str | None = None,
             *, failing: bool = True, what: str = "", line_at=None, new: bool = False,
             passed=frozenset(), collect=None) -> None:
    """Each match of `pattern` in `text` (already blanked as the rule asks) is a finding.
    `shown` is the text the excerpt is taken from, so the reader sees the words;
    `line_at` gives the file's line of an offset in `text`, for a text taken from a file
    (a review note, a rendered docstring); `new` marks a finding of the reach of #66
    (REACH_PENDING); a match that starts at an offset of `passed` is passed by; and
    `collect`, a list, gains (rule, offset) for each finding."""
    shown = text if shown is None else shown
    line_at = line_at or (lambda a: line_of(text, a))
    for m in pattern.finditer(text):
        a, b = (m.span(1) if m.groups() and m.group(1) else m.span())
        if a in passed:
            continue
        if collect is not None:
            collect.append((rule, a))
        found = flat(m.group(1) if m.groups() and m.group(1) else m.group(0))
        msg = f'{what}"{found}": {excerpt(shown, a, b)}'
        if failing:
            fail(rule, path, line_at(a), msg, new=new)
        else:
            report(rule, path, line_at(a), msg)


def text_lines(text: str, line0: int = 0, last: int | None = None):
    """The file's line of an offset in `text`, a text that starts after the file's line
    `line0` and ends on its line `last` (a one-line string's escapes may make more lines
    of it than the file has)."""
    def at(a: int) -> int:
        line = line0 + line_of(text, a)
        return min(line, last) if last else line
    return at


def check_text(path: Path, raw: str, scopes: set[str], *, new: bool = False,
               replaced=None, line_at=None, collect=None, check_s22: bool = True) -> None:
    """The text rules for one file, or for one text of it (a review note, a rendered
    docstring), by the scopes it belongs to. `new` marks a text that came under the rules
    with the reach of #66, whose every finding is of that reach; in the other texts, the
    reach is S7 where it was D10, S6 in the rendered docstrings, and S22. `replaced`
    gives, for S6 and S7, the offsets in `raw` where they found something in a Lean
    file's rendered docstrings, read as the pages show them, so D10 passes by the match
    there that the failure replaces. `line_at` gives the file's line of an offset in
    `raw`, for a text taken from a file; `collect`, a list, gains (rule, offset) for each
    finding."""
    raw = raw.replace("\r\n", "\n")
    straight = straighten(raw)
    prose, cat, readme = "prose" in scopes, "catalogue" in scopes, "readme" in scopes
    notes, gen = "lean" in scopes, "generated" in scopes
    review, reports_, rendered = "review" in scopes, "report" in scopes, "rendered" in scopes
    code_free = blank_code(straight, indented_code=not notes)
    outside = blank_quotes(code_free)

    line_at = line_at or text_lines(raw)

    replaced = replaced or {}

    def find(rule, pattern, text, *, failing=True, reach=False, passed=frozenset()):
        find_all(rule, pattern, path, text, raw, failing=failing, line_at=line_at,
                 new=new or reach, passed=passed, collect=collect)

    if prose or review or cat or readme or notes or reports_:
        find("S1", EM_DASH, blank_code(raw, indented_code=not notes))
    if prose or review or cat or readme or notes:
        find("S2", CREW, outside)
        find("S3", FIRST_PERSON, outside)
    if prose or review or cat or notes:
        find("S4", HEDGE, outside)
    if prose or review or cat or readme or notes or gen:
        find("S5", EUCLID_CITES, outside)
    if prose or review or rendered or gen:
        find("S6", TACIT, outside, reach=rendered)
    elif cat or readme or notes:
        find("D10", TACIT, outside, failing=False, passed=replaced.get("S6", frozenset()))
    defs = SQUARE.sub(_blank, outside)
    if prose or review or cat or reports_ or rendered or gen:
        find("S7", DEFINITION, defs, reach=cat or rendered or gen)
    elif readme or notes:
        find("D10", DEFINITION, defs, failing=False, passed=replaced.get("S7", frozenset()))
    if prose or review or cat or reports_:
        find("S8", CURLY, blank_code(raw, indented_code=not notes))
    if prose or review or cat or notes:
        find("S9", ITALIC_LETTER, code_free)
    if check_s22 and (prose or review or cat or notes or reports_ or gen):
        check_letters_in_code(path, raw, line_at=line_at, indented_code=not notes,
                              collect=collect)
    if prose or readme:
        find("D6", COMPARISON, outside, failing=False)
    if prose or review or cat or notes:
        find("D7", LEAN_CANNOT, outside, failing=False)
    if prose or review or cat:
        find("D8", NO_CITATION, outside, failing=False)
    if prose or review or cat or readme or notes:
        for off, sent in sentences(outside):
            if NEED.search(sent) and POSTULATE_5.search(sent):
                m = NEED.search(sent)
                report("D9", path, line_at(off + m.start()),
                       excerpt(raw, off + m.start(), off + m.end(), 70))


# ---------------------------------------------------------------------------------------
# The mishnah: TeX, refrains, Lean names.

# S10's one exception (STYLE, section 4, "Mathematics"): in a paragraph that opens
# MODERN_WAY, and ends at MODERN_WAY_ENDS, mathematics may stand between single dollars,
# and the check refuses the shapes of span known to break on GitHub. Its renderer, read with
# sample spans on 18 October, opens a span only at a line's start, after white space or
# after "(", and closes it only before white space, a line's end or a mark of
# MATH_CLOSES_BEFORE; it renders no span that crosses a line or begins or ends with a
# space; its Markdown takes away a backslash before a punctuation mark (\{ becomes {, \,
# becomes ,); and it escapes <, > and & inside a span twice. The lost backslashes show
# that its Markdown reads inside a span, so the refusals of *, _, ~ and a backtick follow
# CommonMark's rules, checked with a CommonMark parser and not tried on GitHub: a *, or a
# _ after anything but a letter or a digit, can open emphasis and pair with another across
# two spans; GFM reads ~ as strikethrough; and a backtick opens code. A shape not found
# here may still break, and the reviewer's checklist, item 5 (STYLE, section 8: each span
# seen rendered on GitHub), stays the guard.
MODERN_WAY = "**The modern way.**"
# Where the modern way's paragraph ends, as CommonMark ends a paragraph, with GFM's
# tables: at a blank line, or before a line, indented at most three spaces, that opens a
# block allowed to interrupt a paragraph. Those are an ATX heading; a bullet list item, or
# an ordered one numbered 1, with some text; a block quotation; a code fence; an HTML
# block, read here as any line opening a tag, "<!" or "<?", a little wider than
# CommonMark's (it lets "<span>" go on); a thematic break or a setext underline; and a
# table, whose next line is a delimiter row. Any other line, "|z| is one", "2. So" or
# "#check", goes on with it.
MODERN_WAY_ENDS = MARKDOWN_BLOCK_BREAK
MATH_OPENS_AFTER = " \t\n("
MATH_CLOSES_BEFORE = " \t\n.,;:!?)]'\"’”–-/"
MATH_ESCAPE = re.compile(r"\\[!-/:-@\[-`{-~]")      # a backslash before ASCII punctuation
MATH_HTML = re.compile(r"[<>&]")


def math_fault(text: str, a: int, b: int) -> str | None:
    """The shape known to break on GitHub that the span from the `$` at `a` to the `$` at
    `b` of `text` has, or None."""
    body = text[a + 1:b]
    if not body:
        return "$$: display mathematics is not allowed; write $…$ within the sentence"
    if "\n" in body:
        return "a $…$ across a line break, which GitHub does not render; keep it on one line"
    if body[0].isspace() or body[-1].isspace():
        return "a space just inside a $: GitHub renders $x$, not $ x $"
    before = text[a - 1] if a else "\n"
    if before not in MATH_OPENS_AFTER:
        return (f"the opening $ follows {before!r}: GitHub opens $…$ only at a line's start, "
                "after a space or after (")
    after = text[b + 1] if b + 1 < len(text) else "\n"
    if after not in MATH_CLOSES_BEFORE:
        return (f"the closing $ comes before {after!r}: GitHub closes $…$ only before a space, "
                "a line's end or one of . , ; : ! ? ) ] ' \" - – /")
    m = MATH_ESCAPE.search(body)
    if m:
        return (f"{m.group(0)} inside $…$: GitHub's Markdown takes away a backslash before a "
                "punctuation mark; write \\lbrace, \\rbrace, \\thinspace, \\Vert")
    if "*" in body:
        return "* inside $…$, which GitHub's Markdown can read as emphasis; write \\ast"
    for i, c in enumerate(body):
        if c == "_" and not (i and body[i - 1].isalnum()):
            where = f"after {body[i - 1]!r} inside" if i else "first in"
            return (f"a _ {where} $…$, which GitHub's Markdown can read as emphasis; "
                    "put a subscript straight after a letter or digit, x_{1}^{2} rather "
                    "than x^{2}_{1}, \\mathrm{A_1} rather than \\mathrm{A}_1")
    if "~" in body:
        return ("~ inside $…$, which GitHub's Markdown can read as strikethrough; write a "
                "space or \\sim")
    if "`" in body:
        return "a backtick inside $…$, which GitHub's Markdown reads as code"
    depth = 0
    for c in body:
        depth += {"{": 1, "}": -1}.get(c, 0)
        if depth < 0:
            break
    if depth:
        return "the braces { } inside $…$ do not balance"
    m = MATH_HTML.search(body)
    if m:
        return (f"{m.group(0)} inside $…$, which GitHub escapes twice; write \\lt, \\gt, "
                "\\le, \\ge")
    return None


def tex_findings(text: str) -> list[tuple[int, int, str]]:
    """S10 on a mishnah, fenced blocks and HTML comments already blanked: (start, end,
    message) for each finding. TeX (a backslash, `^{` or `$`) is refused everywhere, save
    in a `$…$` span of a paragraph that opens MODERN_WAY, a paragraph ended as
    MODERN_WAY_ENDS says; there every `$` pairs with the next, and no span may have a shape
    known to break on GitHub (math_fault)."""
    found, outside = [], text
    start = 0
    for brk in list(MODERN_WAY_ENDS.finditer(text)) + [None]:
        end = brk.start() if brk else len(text)
        block, at = text[start:end], start
        start = brk.end() if brk else len(text)
        if not block.lstrip().startswith(MODERN_WAY):
            continue
        dollars = [at + m.start() for m in re.finditer(r"\$", block)]
        for k in range(0, len(dollars), 2):
            a = dollars[k]
            if k + 1 == len(dollars):
                found.append((a, a + 1, "an unpaired $: each $ that opens mathematics in the "
                              "modern way closes it in the same paragraph"))
                b = a
            else:
                b = dollars[k + 1]
                fault = math_fault(text, a, b)
                if fault:
                    found.append((a, b + 1, fault))
            outside = outside[:a] + re.sub(r"[^\n]", " ", outside[a:b + 1]) + outside[b + 1:]
    for m in TEX.finditer(outside):
        found.append((m.start(), m.end(), f'"{m.group(0)}", TeX outside a $…$ of the modern way'))
    return sorted(found)


IDENT_PART = r"[A-Za-z_][A-Za-z0-9_₀-₉]*(?:'[A-Za-z0-9_₀-₉']*)*"
IDENT = re.compile(rf"{IDENT_PART}(?:\.{IDENT_PART})*\.?")
FILE_NAME = re.compile(r".*\.(?:lean|json|md|svg|py|toml|txt|lock)$")


# A backticked hypothesis or variable with its type, `hBCE : Between B C E`: the name
# before the colon (not `:=`, `::` or a link's `://`) is read as a name too.
BINDER = re.compile(r"([A-Za-z_][A-Za-z0-9_.'!?₀-₉]*)[ \t]*:(?![=:/])")


class LeanName(NamedTuple):
    name: str
    at: int
    binder: bool
    span: CodeSpan


def lean_name_occurrences(text: str, binders: bool = True) -> list[LeanName]:
    """The first visible occurrence of each Lean name."""
    names = []
    for span in code_span_details(text):
        inner = span.content.strip()
        binder = BINDER.match(inner) if binders else None
        name = inner if IDENT.fullmatch(inner) else binder.group(1) if binder else None
        if name and not FILE_NAME.fullmatch(name) and name not in {use.name for use in names}:
            names.append(LeanName(name, span.start, binder is not None, span))
    return names


def lean_names(text: str, binders: bool = True) -> list[str]:
    """The backticked Lean names of a text, file names aside, in order of first use: a
    span that is one name, and, unless `binders` is False, the name a span `name : type`
    opens with."""
    return [use.name for use in lean_name_occurrences(text, binders)]


def check_mishnah(path: Path, raw: str) -> None:
    ref = ref_of(path)
    text = blank_blocks(raw)
    for a, b, msg in tex_findings(text):
        fail("S10", path, line_of(text, a), f"{msg}: {excerpt(raw, a, b)}")
    for pattern, allowed in REFRAINS:
        if ref in allowed:
            continue
        for m in pattern.finditer(text):
            where = ("only " + ", ".join(sorted(allowed, key=heath.prop_key))) if allowed else "nowhere"
            fail("S11", path, line_of(text, m.start()),
                 f'"{flat(m.group(0))}" (allowed {where}): {excerpt(raw, m.start(), m.end())}')
    for a, b in proclus_under_i31(text):
        fail("S11", path, line_of(text, a),
             f'"under I.31" beside Proclus (allowed nowhere): {excerpt(raw, a, b)}')
    for m in RETIRED_LEADS.finditer(text):
        fail("S11", path, line_of(text, m.start()), f"retired lead {flat(m.group(0))}")
    names = lean_names(raw, binders=False)
    if len(names) > 4:
        report("D4", path, 1, f"{len(names)} Lean names: {', '.join(names)}")


class NamedText(NamedTuple):
    """A text S12 reads: the file a finding names, the text (the file's own, or one text
    of it, as a review note), the namespaces opened for it, and whether S12 read it before
    the reach of #66 (the mishnah, whose plain names it read and whose `name : type` it
    did not)."""
    path: Path
    text: str
    opens: str
    held: bool = False
    line_at: object = None   # the file's line of an offset in the text, if taken from a file
    hypothesis: bool = False


def book_opens(book: str) -> str:
    """What S12 opens for a text of one book: `Elements`, its book and the tacit rules."""
    return f"Elements Elements.Book{book} Elements.Tacit"


def every_book_opens() -> str:
    """What S12 opens for a text with no book of its own (the overlap catalogue and the
    review terms): every book, so that a name two books share is ambiguous, and is written
    with its book (`BookI.Prop5.base`)."""
    return " ".join(["Elements"] + [f"Elements.Book{b}" for b in heath.BOOKS] + ["Elements.Tacit"])


# What S12 opens for the docstrings of the foundations, which come before every book.
FOUNDATIONS_OPENS = "Elements Elements.Tacit"
# The audit lemmas the overlap catalogue names are Lean's once `lake build Audit` has run
# (CI runs it before this script); until then they are listed as not checked.
AUDIT_OLEAN = ROOT / ".lake" / "build" / "lib" / "lean" / "Audit.olean"
SCRIPT = ROOT / "scripts" / "check_style.py"


class NameUse(NamedTuple):
    text: NamedText
    at: int
    binder: bool


Groups = dict[str, dict[str, list[NameUse]]]   # {namespaces opened: {name: uses}}


def s12_plan(texts: list[NamedText], audit_built: bool):
    """What S12 asks of Lean: (the groups put to Lean as before #66, with `import
    Elements` alone; the groups put to it with the Audit library as well; the audit lemmas
    left unchecked; the words of NOT_DECLARED in use). A text S12 read before (`held`, the
    mishnah) is read as it was: every name of it is asked of Lean, with `import Elements`
    alone, so NOT_DECLARED and the audit lemmas excuse nothing there. In the other texts,
    a word of NOT_DECLARED is not asked, and an audit lemma is asked once the Audit library
    is built, and listed as unchecked till then."""
    old: Groups = defaultdict(lambda: defaultdict(list))
    new: Groups = defaultdict(lambda: defaultdict(list))
    unchecked: set[str] = set()
    used: set[str] = set()
    for t in texts:
        for occurrence in lean_name_occurrences(t.text):
            if t.hypothesis and occurrence.binder:
                line = t.line_at(occurrence.at) if t.line_at else line_of(t.text, occurrence.at)
                content = occurrence.span.content.strip()
                fail("S12", t.path, line, f"`{content}`: write the hypothesis in words, "
                     "not as a Lean binder (STYLE, section 1, \"Hypotheses in words\")",
                     new=True)
                continue
            name = occurrence.name
            use = NameUse(t, occurrence.at, occurrence.binder)
            if name in NOT_DECLARED:
                used.add(name)
            if t.held:
                old[t.opens][name].append(use)
            elif name in NOT_DECLARED:
                continue
            elif name.startswith("Audit.") and not audit_built:
                unchecked.add(name)
            else:
                new[t.opens][name].append(use)
    return old, new, sorted(unchecked), used


def lean_probe(groups: Groups, imports: list[str]) -> int:
    """Put every name of `groups` to Lean with `#check`, each group in a section of its
    own with its namespaces open, in one run, and fail S12 for each name Lean does not
    know, in each text that gives it. Returns how many names were put to Lean."""
    # A run can have more than Lean's default 100 errors. Read every name, including
    # names after a pending file's findings; otherwise a truncated run can pass as done.
    lines = [f"import {m}" for m in imports]
    where: dict[int, tuple[str, list[NameUse]]] = {}
    for opens in sorted(groups):
        if not groups[opens]:
            continue
        lines += ["", "section", f"open {opens}"]
        for name in sorted(groups[opens]):
            lines.append(f"#check @{name}")
            where[len(lines)] = (name, groups[opens][name])
        lines.append("end")
    if not where:
        return 0
    with tempfile.TemporaryDirectory() as tmp:
        probe = Path(tmp) / "StyleNames.lean"
        probe.write_text("\n".join(lines) + "\n", encoding="utf-8")
        try:
            run = subprocess.run(["lake", "env", "lean", "-DmaxErrors=0", str(probe)], cwd=ROOT,
                                 capture_output=True, text=True, timeout=900)
        except (OSError, subprocess.TimeoutExpired) as e:
            lean_short.append("could not run Lean")
            fail("S12", SCRIPT, 0, f"could not run Lean ({e}); build the tree with "
                 "`lake build`, or pass --no-lean")
            return 0
    out = run.stdout + run.stderr
    errors = list(re.finditer(rf"{re.escape(probe.name)}:(\d+):\d+: error(?:\([^)]*\))?: (.*)", out))
    if run.returncode != 0 and not errors:
        lean_short.append("Lean failed before checking a name")
        fail("S12", SCRIPT, 0, "Lean failed before checking a name (is the tree "
             "built? run `lake build`, or pass --no-lean):\n      " + out.strip()[:400])
        return 0
    for m in errors:
        line = int(m.group(1))
        if line not in where:
            lean_short.append("Lean failed outside the names")
            fail("S12", SCRIPT, 0, f"Lean: {m.group(2)} (is the tree built? run "
                 "`lake build`, or pass --no-lean)")
            continue
        name, uses = where[line]
        for use in uses:
            t, at, binder = use.text, use.at, use.binder
            hint = ("; a hypothesis is said in words, never by its local name (STYLE, "
                    "section 1, \"Hypotheses in words\")" if binder else "")
            line = t.line_at(at) if t.line_at else line_of(t.text, at)
            fail("S12", t.path, line, f"`{name}`: {m.group(2).strip()}{hint}",
                 new=binder or not t.held)
    return len(where)


def check_lean_names(texts: list[NamedText]) -> tuple[int, list[str]]:
    """S12: every backticked name in the texts is one Lean knows, with each text's
    namespaces open (s12_plan says how each is asked). The mishnah keeps `Elements`,
    `Elements.Book<book>` and `Elements.Tacit` open, with every book checked in its own
    section of one Lean run. Returns how many names were put to Lean, and the audit
    lemmas left unchecked because the Audit library is not built."""
    old, new, unchecked, used = s12_plan(texts, AUDIT_OLEAN.exists())
    for name in sorted(set(NOT_DECLARED) - used):
        fail("S12", SCRIPT, 0, f"`{name}` is in NOT_DECLARED, but no text S12 reads uses it "
             "any more: take it out")
    audit = any(n.startswith("Audit.") for g in new.values() for n in g)
    count = lean_probe(old, ["Elements"])
    count += lean_probe(new, ["Elements"] + (["Audit"] if audit else []))
    return count, unchecked


# ---------------------------------------------------------------------------------------
# Further reading and the introductions.

WEB_LINK = re.compile(r"\]\((https?://[^)\s]+)\)|href=\"(https?://[^\"]+)\"")


def reading_links() -> set[str]:
    text = (ROOT / "docs" / "reading.md").read_text(encoding="utf-8")
    return {a or b for a, b in WEB_LINK.findall(text)}


def check_reading(path: Path, raw: str, allowed: set[str]) -> None:
    lines = [(k, l) for k, l in enumerate(raw.splitlines(), 1) if l.strip()]
    if not 1 <= len(lines) <= 3:
        fail("S17", path, 1, f"{len(lines)} lines; a reading file has one to three")
    for k, l in lines:
        if not l.startswith("- "):
            fail("S17", path, k, f"not a list item: {l[:60]}")
    for m in WEB_LINK.finditer(raw):
        url = m.group(1) or m.group(2)
        if url not in allowed:
            fail("S17", path, line_of(raw, m.start()), f"{url} is not given by docs/reading.md")


def check_intros() -> None:
    present = {p.stem for p in intro_files()}
    for book in books_with_pages():
        has_pages = any((ROOT / d / book).is_dir() for d in ("mishnah", "book"))
        if has_pages and book not in present:
            fail("S18", ROOT / "mishnah" / "intro", 0, f"Book {book} has pages and no "
                 f"mishnah/intro/{book}.md")
    for path in intro_files():
        raw = path.read_text(encoding="utf-8")
        if not re.search(rf"\]\([^)]*briefs/(?:\d{{4}}-)?book-{re.escape(path.stem)}\.md(?:#[^)]*)?\)", raw):
            fail("S19", path, 1, f"no link to Book {path.stem}'s brief in docs/briefs/")


# ---------------------------------------------------------------------------------------
# Figures.

SVG = "{http://www.w3.org/2000/svg}"
IDEA_COLOURS = {"#fbf7ee", "#d0312d", "#f2b705", "#1f5aa6", "#222222"}
WHITE = {"#fff", "#ffffff", "white"}
EUCLID_COLOURS = {"#fbf7ee", "#3b2f2f", "#8c7b62", "#a0522d", "#e9dcc0"}
COLOUR_ATTRS = ("fill", "stroke", "stop-color", "color", "flood-color", "lighting-color")
DRAWN = {"line", "path", "polyline", "polygon", "circle", "ellipse", "rect"}
FILLED = DRAWN - {"line"}
INHERITED = ("fill", "fill-rule", "stroke", "stroke-width", "stroke-linecap",
             "stroke-linejoin", "stroke-miterlimit", "stroke-dasharray",
             "font-family", "font-size", "font-style", "font-weight", "text-anchor")
LETTER = re.compile(r"[A-Z][′'₀-₉]*")
ASCII_NUMERIC_ANNOTATION = re.compile(r"[0-9]+")

# Inventory of all 198 checked figures at 209d71fd, plus explicit initial keyword
# values. No style, definitions, references, relative paths, quadratic curves or scales
# occur there. Keep this language closed before any traversal can measure a figure.
SVG_ELEMENTS = {"svg", "title", "desc", "g", "line", "polyline", "polygon", "rect",
                "circle", "ellipse", "path", "text"}
SVG_NUMBERS = {"x", "y", "x1", "y1", "x2", "y2", "cx", "cy", "r", "rx", "ry",
               "width", "height", "font-size", "stroke-width", "fill-opacity", "stroke-opacity"}
SVG_KEYWORDS = {
    "fill": {"none", "black", "#1f5aa6", "#222222", "#3b2f2f", "#d0312d", "#e9dcc0",
             "#f2b705", "#fbf7ee", "#fff"},
    "stroke": {"none", "#1f5aa6", "#222222", "#3b2f2f", "#8c7b62", "#a0522d", "#d0312d",
               "#f2b705", "#fbf7ee", "#fff"},
    "font-family": {"Georgia", "Georgia, serif", "Georgia, 'Times New Roman', serif"},
    "font-style": {"normal", "italic"},
    "font-weight": {"normal", "bold"},
    "text-anchor": {"start", "middle", "end"},
    "stroke-linecap": {"butt", "round"},
    "stroke-linejoin": {"miter", "round"},
}
SVG_SPACE = " \t\r\n"
# Main's largest numeric input at 209d71fd is 440. This admits ample room around
# its canvases while keeping coordinates, lengths, radii and path arithmetic bounded.
SVG_NUMBER_LIMIT = 10_000
# Main's deepest checked figure at c6ff6817 is 3 levels below its root.
SVG_MAX_DEPTH = 16

# The letters of a figure at a glance (S20, S21; STYLE, section 7). Lengths are in the
# canvas's units, 400 × 300.
IDEA_INK = "#222222"            # a letter on the parchment or on yellow
IDEA_INK_ON_DARK = "#fbf7ee"    # a letter on red, blue or black, in the parchment's colour
DARK = {"#d0312d", "#1f5aa6", "#222222"}
IDEA_LETTER_SIZE = 14
BYRNE = {"#d0312d", "#f2b705", "#1f5aa6", "#222222"}
NEAR = 30.0      # the farthest a letter's centre may stand from its point
MARK = 25.0      # a straight line shorter than this is a mark (an equals sign), not a point
SAME = 8.0       # points nearer than this are one point (a corner where two lines end)
DOT = 6.0        # a filled circle of this radius at most is a dot
UNLETTERED = "data-unlettered"
NUM = re.compile(r"[-+]?(?:\d+\.?\d*|\.\d+)(?:[eE][-+]?\d+)?")
IDENTITY = (1.0, 0.0, 0.0, 1.0, 0.0, 0.0)

# A path's `d`, read for the fill a letter stands on (S20): its commands, the numbers each
# takes, and how finely its arcs and curves are followed in straight pieces.
PATH_COMMAND = re.compile(r"[\s,]*([MmZzLlHhVvCcSsQqTtAa])")
PATH_NUMBER = re.compile(r"[\s,]*(" + NUM.pattern + ")")
PATH_FLAG = re.compile(r"[\s,]*([01])")
PATH_ARITY = {"m": 2, "l": 2, "h": 1, "v": 1, "c": 6, "s": 4, "q": 4, "t": 2, "a": 7}
ARC_STEP = math.radians(3)   # an arc, in a straight piece to each 3 degrees of its sweep
CURVE_ERROR = 0.001          # the maximum Bézier chord error, before transforms
CURVE_MAX_DEPTH = 16         # at most 2**16 chords per curve; refuse if still not flat

# One letter, one point (S26; STYLE, sections 7 and 8). A letter names one thing: a figure
# draws it once, or once in each of Heath's figures where they stand side by side, and it
# stands clear of every stroke, every dot and the canvas's edge, so that no line runs
# through it and it is not read as another point's. A letter is measured as Georgia, the
# figures' font, draws its capital, upright or italic as the figure sets it (an italic
# letter fails S15 and S20, and is still measured as it is drawn): by the convex
# hull of the points of the capital's outline, on its curves and off them, which holds the
# ink. GLYPHS_UPRIGHT and GLYPHS_ITALIC give each capital's advance and that hull's
# corners, x and y in turn with y up, in the font's units, EM to the em: a coarse shape,
# read from the fonts with fontTools once, so that the script needs neither. The hull
# misses no stroke that comes near the ink; it also spans a letter's hollows (an L's
# corner, a K's notch), so a stroke that ends in one is found while the ink is clear. A
# prime or a subscript after the capital is not measured, but its advance (SUFFIXES, the
# same upright and italic) places the capital when the label is anchored at its middle or
# its end.
CLEAR = 2.0     # the least room between a letter's hull and a stroke, a dot or the edge
EM = 2048
SUFFIXES = {"′": 658, "'": 441, **{chr(0x2080 + i): 1024 for i in range(10)}}
# The figures where two or three of Heath's figures stand side by side, one to a case
# (STYLE, section 7): the x of each straight cut between two of them, in the canvas's
# units. A letter belongs to the case its hull's middle stands in, is drawn once in each,
# and stands wholly on one side of every cut.
SIDE_BY_SIDE = {
    ("III", 25): (150.0, 275.0),
    ("III", 33): (147.0, 290.0),
    ("III", 35): (222.0,),
    ("III", 36): (190.0,),
}
GLYPHS_UPRIGHT = {
    "A": (1374, (-41, 0, 1421, 0, 1421, 71, 739, 1439, 659, 1439, -41, 71)),
    "B": (1339, (95, 0, 857, 0, 1026, 48, 1162, 141, 1248, 287, 1248, 483, 1170, 1196,
            1094, 1316, 972, 1389, 833, 1419, 102, 1419, 95, 71)),
    "C": (1315, (78, 526, 184, 255, 273, 161, 363, 67, 596, -33, 919, -33, 1203, 148, 1289,
            359, 1227, 1419, 859, 1450, 613, 1450, 365, 1342, 182, 1143, 78, 866)),
    "D": (1534, (94, 0, 828, 0, 1102, 84, 1212, 169, 1321, 254, 1457, 520, 1457, 896, 1315,
            1184, 1098, 1340, 850, 1419, 102, 1419, 94, 71)),
    "E": (1338, (86, 0, 1264, 0, 1291, 418, 1184, 1419, 86, 1419)),
    "F": (1227, (86, 0, 701, 0, 983, 444, 1199, 1064, 1199, 1419, 86, 1419)),
    "G": (1485, (78, 530, 190, 258, 379, 69, 631, -33, 894, -33, 1158, 31, 1291, 91, 1471,
            567, 1471, 640, 1278, 1419, 911, 1450, 641, 1450, 378, 1339, 185, 1137, 78,
            860)),
    "H": (1669, (98, 0, 1567, 0, 1567, 1419, 98, 1419)),
    "I": (798, (79, 0, 718, 0, 718, 1419, 79, 1419)),
    "J": (1060, (11, 149, 214, -34, 482, -34, 645, 42, 755, 168, 808, 316, 1006, 1348,
            1006, 1419, 380, 1419, 11, 372)),
    "K": (1422, (102, 0, 1475, 0, 1475, 71, 1393, 1419, 102, 1419)),
    "L": (1236, (98, 0, 1207, 0, 1237, 422, 697, 1419, 98, 1419)),
    "M": (1899, (48, 0, 1806, 0, 1806, 71, 1804, 1419, 57, 1419, 48, 71)),
    "N": (1571, (24, 1348, 48, 0, 1237, -14, 1324, -14, 1554, 1348, 1554, 1419, 24, 1419)),
    "O": (1524, (80, 550, 183, 273, 363, 77, 614, -34, 901, -34, 1147, 70, 1336, 263, 1444,
            539, 1444, 876, 1338, 1153, 1153, 1347, 903, 1453, 626, 1453, 377, 1349, 188,
            1152, 80, 881)),
    "P": (1249, (91, 1348, 98, 0, 707, 0, 1184, 958, 1184, 1228, 937, 1419, 91, 1419)),
    "Q": (1524, (80, 550, 178, 283, 353, 86, 923, -346, 1051, -385, 1238, -385, 1373, -356,
            1418, -343, 1444, 574, 1444, 876, 1338, 1153, 1153, 1347, 903, 1453, 626, 1453,
            377, 1349, 188, 1152, 80, 881)),
    "R": (1437, (98, 0, 1480, 0, 1480, 71, 1201, 1172, 1127, 1301, 1065, 1341, 1001, 1382,
            843, 1419, 98, 1419)),
    "S": (1149, (94, 485, 108, -1, 490, -29, 791, -29, 1069, 215, 1069, 482, 1001, 1419,
            661, 1451, 477, 1451, 319, 1392, 261, 1340, 200, 1285, 134, 1145)),
    "T": (1267, (15, 1034, 298, 0, 968, 0, 1251, 1034, 1251, 1419, 15, 1419)),
    "U": (1549, (74, 1348, 260, 294, 328, 147, 395, 90, 463, 33, 663, -34, 871, -34, 1046,
            13, 1125, 67, 1205, 123, 1303, 297, 1533, 1348, 1533, 1419, 74, 1419)),
    "V": (1365, (-38, 1348, 628, -18, 711, -18, 1407, 1348, 1407, 1419, -38, 1419)),
    "W": (1998, (-4, 1348, 536, -18, 1447, -18, 2028, 1348, 2028, 1419, -4, 1419)),
    "X": (1455, (13, 0, 1457, 0, 1457, 71, 1410, 1419, 27, 1419, 13, 71)),
    "Y": (1260, (-44, 1348, 292, 0, 956, 0, 1314, 1348, 1314, 1419, -44, 1419)),
    "Z": (1232, (27, 0, 1167, 0, 1214, 443, 1190, 1419, 127, 1419, 84, 1018, 27, 35)),
}
GLYPHS_ITALIC = {
    "A": (1374, (-160, 0, 1302, 0, 1317, 66, 952, 1439, 872, 1439, -145, 66)),
    "B": (1339, (-29, 0, 768, 0, 965, 55, 1051, 113, 1131, 167, 1236, 340, 1298, 1077,
            1298, 1234, 1236, 1333, 1126, 1394, 1003, 1419, 306, 1419, 290, 1353)),
    "C": (1315, (100, 400, 183, 190, 328, 43, 522, -33, 830, -33, 1140, 143, 1266, 358,
            1427, 1419, 1041, 1452, 751, 1452, 448, 1302, 340, 1178, 228, 1049, 100, 721)),
    "D": (1534, (-29, 0, 769, 0, 1096, 116, 1229, 229, 1357, 338, 1515, 669, 1515, 1024,
            1398, 1241, 1209, 1368, 997, 1419, 306, 1419, -14, 66)),
    "E": (1338, (-37, 0, 1141, 0, 1264, 418, 1388, 1419, 290, 1419, -22, 66)),
    "F": (1227, (-35, 0, 583, 0, 963, 444, 1322, 1064, 1404, 1419, 291, 1419, 275, 1353)),
    "G": (1485, (100, 403, 187, 191, 341, 43, 547, -33, 745, -33, 874, -13, 1021, 24, 1124,
            64, 1190, 91, 1481, 572, 1496, 640, 1482, 1419, 1093, 1452, 781, 1452, 467,
            1311, 235, 1064, 100, 733)),
    "H": (1669, (-25, 0, 1444, 0, 1756, 1353, 1771, 1419, 302, 1419, -10, 66)),
    "I": (798, (-44, 0, 595, 0, 907, 1353, 922, 1419, 283, 1419, -29, 66)),
    "J": (1060, (-50, 106, 118, -34, 373, -34, 545, 44, 679, 166, 762, 315, 1194, 1353,
            1209, 1419, 579, 1419, -50, 329)),
    "K": (1422, (-21, 0, 1336, 0, 1353, 66, 1597, 1419, 306, 1419, -6, 66)),
    "L": (1236, (-25, 0, 1084, 0, 1211, 422, 901, 1419, 302, 1419, -10, 66)),
    "M": (1899, (-76, 0, 1682, 0, 1698, 66, 1993, 1353, 2008, 1419, 260, 1419)),
    "N": (1571, (-75, 0, 1109, -14, 1199, -14, 1743, 1353, 1759, 1419, 229, 1419, 213,
            1353)),
    "O": (1496, (100, 288, 404, -34, 811, -34, 1108, 107, 1224, 229, 1337, 348, 1477, 683,
            1477, 1138, 1169, 1453, 766, 1453, 465, 1311, 240, 1067, 100, 734)),
    "P": (1249, (-25, 0, 584, 0, 1205, 822, 1312, 1012, 1312, 1266, 1097, 1419, 295, 1419,
            280, 1353)),
    "Q": (1496, (100, 290, 393, -24, 780, -386, 1000, -386, 1171, -357, 1232, -338, 1477,
            683, 1477, 1138, 1169, 1453, 766, 1453, 465, 1311, 240, 1067, 100, 734)),
    "R": (1437, (-26, 0, 1354, 0, 1370, 66, 1330, 1219, 1269, 1323, 1168, 1385, 1026, 1419,
            302, 1419)),
    "S": (1149, (-9, -1, 370, -29, 614, -29, 815, 41, 973, 169, 1065, 353, 1199, 1419, 825,
            1451, 641, 1451, 448, 1383, 380, 1326, 310, 1267, 225, 1105, 89, 485)),
    "T": (1267, (130, 1034, 174, 0, 844, 0, 1366, 1034, 1455, 1419, 219, 1419)),
    "U": (1549, (212, 144, 449, -34, 749, -34, 931, 8, 1016, 57, 1104, 108, 1245, 289,
            1721, 1353, 1737, 1419, 278, 1419, 262, 1353, 212, 313)),
    "V": (1365, (151, 1353, 501, -18, 584, -18, 1599, 1353, 1614, 1419, 166, 1419)),
    "W": (1998, (182, 1353, 408, -18, 1322, -18, 2217, 1353, 2232, 1419, 197, 1419)),
    "X": (1455, (-110, 0, 1321, 0, 1336, 66, 1614, 1419, 243, 1419, -95, 66)),
    "Y": (1260, (143, 1353, 169, 0, 833, 0, 1501, 1353, 1517, 1419, 159, 1419)),
    "Z": (1232, (-90, 0, 1048, 0, 1198, 443, 1387, 1419, 326, 1419, 190, 1018, -81, 35)),
}

# data-unlettered marks in the idea figures, printed on every run:
# {(file, reason): [elements, points]}
idea_exemptions: dict[tuple[str, str], list[int]] = defaultdict(lambda: [0, 0])

# The figures whose letters are all italic, which D15 lists while UPRIGHT_LETTERS_REQUIRED
# is False; it is True, so S15 and S20 fail them and D15 is empty:
# {book: {"of Euclid's figures": [NN, …], "figures at a glance": [NN, …]}}
italic_figures: dict[str, dict[str, list[str]]] = defaultdict(lambda: defaultdict(list))


def letter_style(eff) -> str:
    """A letter's font-style: "normal" (upright, SVG's default) or what it is set to."""
    return (eff.get("font-style") or "normal").strip().lower()


def check_letter_style(path: Path, rule: str, found: list[tuple[str, str]]) -> None:
    """S15's and S20's style of a figure's letters, each (letter, its font-style): upright
    (STYLE, sections 4 and 7). Were UPRIGHT_LETTERS_REQUIRED False, they could all be italic
    instead, one style in each figure, and the figure would be listed for D15."""
    styles: dict[str, list[str]] = defaultdict(list)
    for s, style in found:
        styles[style].append(s)
    for style, letters in sorted(styles.items()):
        if style not in ("normal", "italic"):
            fail(rule, path, 0, f"letter(s) {', '.join(letters)} in font-style {style}: "
                 "Heath's letters are upright (STYLE, section 4)")
    if "italic" not in styles:
        return
    if UPRIGHT_LETTERS_REQUIRED:
        fail(rule, path, 0, f"letter(s) {', '.join(styles['italic'])} italic: Heath's letters "
             "are upright (STYLE, section 4)")
    elif "normal" in styles:
        fail(rule, path, 0, f"letter(s) {', '.join(styles['italic'])} italic beside "
             f"{', '.join(styles['normal'])} upright: one style in each figure, upright as "
             "the figure is converted (STYLE, section 8)")
    else:
        kind = "figures at a glance" if path.stem.endswith("-idea") else "of Euclid's figures"
        italic_figures[path.parent.name][kind].append(path.name[:2])


def tag(el) -> str:
    return el.tag[len(SVG):] if el.tag.startswith(SVG) else el.tag


def style_of(el) -> dict[str, str]:
    """An element's presentation attributes, its `style` declarations overriding them."""
    attrs = {k: v.strip() for k, v in el.attrib.items()}
    for decl in attrs.pop("style", "").split(";"):
        if ":" in decl:
            k, v = decl.split(":", 1)
            attrs[k.strip()] = v.strip()
    return attrs


def walk(el, inherited=None):
    """(element, its own attributes, its effective inherited ones) for the whole tree."""
    own = style_of(el)
    eff = dict(inherited or {})
    eff.update({k: own[k] for k in INHERITED if k in own})
    yield el, own, eff
    for child in el:
        yield from walk(child, eff)


def placed(el, m=IDENTITY, inherited=None, exempt=None):
    """walk(), with each element's place: (element, own attributes, effective inherited
    ones, its transform composed with its ancestors', and the data-unlettered in force as
    (the element that carries it, its reason), or None)."""
    inherited = dict(inherited or {})
    own = dict(el.attrib)
    eff = dict(inherited)
    eff.update({k: own[k] for k in INHERITED if k in own})
    m = compose(m, letter_transform_of(own.get("transform")))
    if UNLETTERED in el.attrib:
        exempt = (el, " ".join(el.attrib[UNLETTERED].split()))
    yield el, own, eff, m, exempt
    for child in el:
        yield from placed(child, m, eff, exempt)


def text_of(el) -> str:
    raw = "".join(el.itertext())
    if tag(el) == "text":
        # SVG's default white-space handling removes newlines, changes tabs to
        # spaces, then collapses spaces. Unicode spaces retain their advance.
        raw = raw.replace("\r", "").replace("\n", "").replace("\t", " ")
        return re.sub(" +", " ", raw).strip(" ")
    return raw.strip()


def number(value: str | None) -> float | None:
    return length(value)


def coord(value: str | None) -> float:
    """A coordinate attribute's first number (x="10" or x="10 24"), or 0, SVG's default."""
    m = NUM.search(value or "")
    return float(m.group(0)) if m else 0.0


def compose(a, b):
    """The affine map a after b, each as the six numbers of SVG's matrix(a b c d e f)."""
    return (a[0] * b[0] + a[2] * b[1], a[1] * b[0] + a[3] * b[1],
            a[0] * b[2] + a[2] * b[3], a[1] * b[2] + a[3] * b[3],
            a[0] * b[4] + a[2] * b[5] + a[4], a[1] * b[4] + a[3] * b[5] + a[5])


def transform_of(value: str | None):
    """A `transform` attribute as one affine map: translate, scale, rotate, skewX, skewY
    and matrix, applied as SVG applies them, the last first."""
    m = IDENTITY
    for name, args in re.findall(r"([A-Za-z]+)\s*\(([^)]*)\)", value or ""):
        v = [float(x) for x in NUM.findall(args)]
        if not v:
            continue
        if name == "translate":
            t = (1.0, 0.0, 0.0, 1.0, v[0], v[1] if len(v) > 1 else 0.0)
        elif name == "scale":
            t = (v[0], 0.0, 0.0, v[1] if len(v) > 1 else v[0], 0.0, 0.0)
        elif name == "rotate":
            c, s = math.cos(math.radians(v[0])), math.sin(math.radians(v[0]))
            t = (c, s, -s, c, 0.0, 0.0)
            if len(v) >= 3:
                t = compose(compose((1.0, 0.0, 0.0, 1.0, v[1], v[2]), t),
                            (1.0, 0.0, 0.0, 1.0, -v[1], -v[2]))
        elif name == "skewX":
            t = (1.0, 0.0, math.tan(math.radians(v[0])), 1.0, 0.0, 0.0)
        elif name == "skewY":
            t = (1.0, math.tan(math.radians(v[0])), 0.0, 1.0, 0.0, 0.0)
        elif name == "matrix" and len(v) == 6:
            t = tuple(v)
        else:
            continue
        m = compose(m, t)
    return m


def letter_transform_of(value: str | None):
    """The complete transform forms in main's figures; None for any other spelling."""
    if value is None:
        return IDENTITY
    name, opening, tail = value.partition("(")
    if not opening or not tail.endswith(")"):
        return None
    args = decimal_list(tail[:-1])
    if args is None:
        return None
    v = [float(x) for x in args]
    if name == "translate" and len(v) == 2:
        return (1.0, 0.0, 0.0, 1.0, v[0], v[1])
    if name == "rotate" and len(v) == 3:
        c, s = math.cos(math.radians(v[0])), math.sin(math.radians(v[0]))
        return compose(compose((1.0, 0.0, 0.0, 1.0, v[1], v[2]),
                               (c, s, -s, c, 0.0, 0.0)),
                       (1.0, 0.0, 0.0, 1.0, -v[1], -v[2]))
    return None


def at(m, x: float, y: float) -> tuple[float, float]:
    return (m[0] * x + m[2] * y + m[4], m[1] * x + m[3] * y + m[5])


def back(m, x: float, y: float) -> tuple[float, float] | None:
    """The point that the affine map m takes to (x, y), or None if m flattens the plane."""
    det = m[0] * m[3] - m[1] * m[2]
    if abs(det) < 1e-12:
        return None
    x, y = x - m[4], y - m[5]
    return ((m[3] * x - m[2] * y) / det, (m[0] * y - m[1] * x) / det)


class SvgMeasurementError(Exception):
    """A figure whose geometry cannot be measured within S26's numerical limits."""


def finite_geometry(*values: float) -> None:
    if not all(math.isfinite(v) for v in values):
        raise SvgMeasurementError("non-finite intermediate result")


def bezier_points(ps, depth: int = 0) -> list[tuple[float, float]]:
    """Subdivide until the control polygon lies within CURVE_ERROR of the chord.
    The curve lies in that polygon's convex hull, so the chord's CURVE_ERROR tube
    contains the curve, including a reversal or a closed curve with coincident ends."""
    finite_geometry(*(v for p in ps for v in p))
    gaps = [point_gap(p, ps[0], ps[-1]) for p in ps[1:-1]]
    finite_geometry(*gaps)
    if max(gaps) <= CURVE_ERROR:
        return [ps[-1]]
    if depth >= CURVE_MAX_DEPTH:
        raise SvgMeasurementError("cubic subdivision limit reached")
    left, right = [ps[0]], [ps[-1]]
    while len(ps) > 1:
        ps = [((a[0] + b[0]) / 2, (a[1] + b[1]) / 2) for a, b in zip(ps, ps[1:])]
        left.append(ps[0])
        right.append(ps[-1])
    return bezier_points(left, depth + 1) + bezier_points(right[::-1], depth + 1)


class StrokeSegment(NamedTuple):
    """An original segment and its endpoint directions, before flattening."""
    start: tuple[float, float]
    end: tuple[float, float]
    start_tangent: tuple[float, float]
    end_tangent: tuple[float, float]


def stroke_segment(points) -> StrokeSegment:
    """A straight or Bézier segment, using the next distinct control point at each end."""
    a, b = points[0], points[-1]
    p = next((p for p in points[1:] if p != a), a)
    q = next((q for q in reversed(points[:-1]) if q != b), b)
    return StrokeSegment(a, b, (p[0] - a[0], p[1] - a[1]),
                         (b[0] - q[0], b[1] - q[1]))


def arc_points(x1: float, y1: float, rx: float, ry: float, phi: float, large: float,
               sweep: float, x2: float, y2: float,
               errors: list[float] | None = None,
               segments: list[StrokeSegment] | None = None) -> list[tuple[float, float]]:
    """An elliptical arc of a path, from (x1, y1) to (x2, y2), as the points along it after
    the first, its centre found from its ends as SVG's implementation notes find it.
    Given `segments`, retain the endpoint tangents from that centre parametrisation."""
    if (x1, y1) == (x2, y2):
        return []
    rx, ry = abs(rx), abs(ry)
    if rx == 0 or ry == 0:
        if segments is not None:
            segments.append(stroke_segment([(x1, y1), (x2, y2)]))
        return [(x2, y2)]
    c, s = math.cos(math.radians(phi)), math.sin(math.radians(phi))
    dx, dy = (x1 - x2) / 2, (y1 - y2) / 2
    px, py = c * dx + s * dy, -s * dx + c * dy
    u, v = px / rx, py / ry
    grow = u * u + v * v
    finite_geometry(u, v, grow)
    if grow > 1:
        rx, ry = rx * math.sqrt(grow), ry * math.sqrt(grow)
    rxy, rxpy, rypx = rx * ry, rx * py, ry * px
    num = rxy * rxy - rxpy * rxpy - rypx * rypx
    den = rxpy * rxpy + rypx * rypx
    finite_geometry(rx, ry, num, den)
    if den == 0:
        raise SvgMeasurementError("arc centre calculation underflowed")
    ratio = num / den
    finite_geometry(ratio)
    k = math.sqrt(max(0.0, ratio))
    if large == sweep:
        k = -k
    qx, qy = k * rx * py / ry, -k * ry * px / rx
    cx, cy = c * qx - s * qy + (x1 + x2) / 2, s * qx + c * qy + (y1 + y2) / 2
    ax, ay, bx, by = (px - qx) / rx, (py - qy) / ry, (-px - qx) / rx, (-py - qy) / ry
    finite_geometry(qx, qy, cx, cy, ax, ay, bx, by)
    if segments is not None:
        direction = 1 if sweep else -1
        tangents = [(direction * (-c * rx * y - s * ry * x),
                     direction * (-s * rx * y + c * ry * x))
                    for x, y in ((ax, ay), (bx, by))]
        finite_geometry(*(v for tangent in tangents for v in tangent))
        segments.append(StrokeSegment((x1, y1), (x2, y2), *tangents))
    start = math.atan2(ay, ax)
    turn = (math.atan2(by, bx) - start) % math.tau
    if not sweep and turn > 0:
        turn -= math.tau
    n = max(1, math.ceil(abs(turn) / ARC_STEP))
    if errors is not None:
        # Use the radii after SVG enlarges them to reach the endpoints.
        errors.append(max(rx, ry) * (1 - math.cos(abs(turn) / (2 * n))))
    pts = []
    for i in range(1, n):
        a = start + turn * i / n
        ex, ey = rx * math.cos(a), ry * math.sin(a)
        p = (cx + c * ex - s * ey, cy + s * ex + c * ey)
        finite_geometry(*p)
        pts.append(p)
    return pts + [(x2, y2)]


def path_rings(d: str, closed: list[bool] | None = None,
               errors: list[float] | None = None,
               segments: list[list[StrokeSegment]] | None = None) -> list[list[tuple[float, float]]]:
    """A path's subpaths as the rings of points its fill closes: straight segments as they
    are, arcs and curves in short straight pieces. A path is read as far as it is well
    formed, as SVG draws it. Given a list `closed`, it gains a flag for each ring: whether
    a Z closes it, as its stroke is drawn (S26), retaining a single point closed by Z
    for its caps. A moveto alone draws nothing. Given `errors`, append a conservative
    maximum chord error for each retained ring, before transforms. Given `segments`,
    retain each ring's original segments and tangents for stroke joins."""
    rings: list[list[tuple[float, float]]] = []
    ring: list[tuple[float, float]] = []
    ring_errors: list[float] = []
    run_segments: list[StrokeSegment] = []

    def keep(shut: bool) -> None:
        if len(ring) > 1 or (closed is not None and shut and ring):
            rings.append(ring)
            if closed is not None:
                closed.append(shut)
            if errors is not None:
                errors.append(max(ring_errors, default=0.0))
            if segments is not None:
                segments.append(run_segments + [stroke_segment([ring[-1], ring[0]])]
                                if shut else run_segments)

    x = y = sx = sy = 0.0
    cmd, ctrl, pos = "", None, 0
    while True:
        found = PATH_COMMAND.match(d, pos)
        if found:
            cmd, pos = found.group(1), found.end()
        elif cmd in ("", "Z", "z"):
            break
        kind = cmd.lower()
        if kind == "z":
            keep(True)
            ring, x, y, ctrl = [(sx, sy)], sx, sy, None
            ring_errors = []
            run_segments = []
            continue
        args = []
        for i in range(PATH_ARITY[kind]):
            got = (PATH_FLAG if kind == "a" and i in (3, 4) else PATH_NUMBER).match(d, pos)
            if not got:
                break
            args.append(float(got.group(1)))
            pos = got.end()
        if len(args) < PATH_ARITY[kind]:
            break
        ox, oy = (x, y) if cmd.islower() else (0.0, 0.0)
        pairs = [(ox + args[i], oy + args[i + 1]) for i in range(0, len(args) - 1, 2)]
        if kind == "m":
            keep(False)
            (x, y), ctrl = pairs[0], None
            sx, sy, ring = x, y, [(x, y)]
            ring_errors = []
            run_segments = []
            cmd = "l" if cmd == "m" else "L"
            continue
        if kind == "h":
            pts, ctrl = [(ox + args[0], y)], None
        elif kind == "v":
            pts, ctrl = [(x, oy + args[0])], None
        elif kind == "l":
            pts, ctrl = pairs, None
        elif kind == "a":
            pts = arc_points(x, y, *args[:5], ox + args[5], oy + args[6], ring_errors,
                             run_segments if segments is not None else None)
            ctrl = None
        else:
            if kind in "st":
                same = ctrl is not None and ctrl[0] == ("c" if kind == "s" else "q")
                pairs.insert(0, (2 * x - ctrl[1][0], 2 * y - ctrl[1][1]) if same else (x, y))
            curve = [(x, y)] + pairs
            pts = bezier_points(curve)
            if segments is not None:
                run_segments.append(stroke_segment(curve))
            if errors is not None:
                ring_errors.append(CURVE_ERROR)
            ctrl = ("c" if kind in "cs" else "q", curve[-2])
        if kind in "hlv" and segments is not None:
            run_segments.append(stroke_segment([(x, y), pts[-1]]))
        ring += pts
        x, y = ring[-1]
    keep(False)
    return rings


def enclosed(rings, x: float, y: float, evenodd: bool) -> bool:
    """Whether (x, y) lies within the rings by SVG's fill rule, nonzero or evenodd."""
    winding = 0
    for ring in rings:
        for (x1, y1), (x2, y2) in zip(ring, ring[1:] + ring[:1]):
            if (y1 > y) != (y2 > y) and x < x1 + (y - y1) * (x2 - x1) / (y2 - y1):
                winding += 1 if y2 > y1 else -1
    return winding % 2 == 1 if evenodd else winding != 0


def inside(el, own, x: float, y: float, evenodd: bool = False) -> bool:
    """Whether (x, y), in the element's own coordinates, lies within the fill of a polygon,
    polyline, path, rect, circle or ellipse."""
    t = tag(el)
    if t in ("polygon", "polyline"):
        v = [float(n) for n in NUM.findall(own.get("points", ""))]
        return enclosed([list(zip(v[0::2], v[1::2]))], x, y, evenodd)
    if t == "path":
        return enclosed(path_rings(own.get("d", "")), x, y, evenodd)
    if t == "rect":
        x0, y0 = coord(own.get("x")), coord(own.get("y"))
        return x0 <= x <= x0 + coord(own.get("width")) and y0 <= y <= y0 + coord(own.get("height"))
    if t == "circle":
        return math.dist((x, y), (coord(own.get("cx")), coord(own.get("cy")))) <= coord(own.get("r"))
    if t == "ellipse":
        rx, ry = coord(own.get("rx")), coord(own.get("ry"))
        if rx <= 0 or ry <= 0:
            return False
        u, v = (x - coord(own.get("cx"))) / rx, (y - coord(own.get("cy"))) / ry
        finite_geometry(u, v)
        return math.hypot(u, v) <= 1
    return False


def fill_under(root, x: float, y: float) -> str:
    """The colour a letter's middle stands on: the fill of the last polygon, polyline,
    path (an angle's wedge), rect, circle or ellipse drawn over it, not transparent
    (transforms applied), or else the parchment."""
    under = "#fbf7ee"
    for el, own, eff, m, _ in placed(root):
        fill = (eff.get("fill") or "black").strip().lower()
        if tag(el) not in FILLED or fill == "none":
            continue
        opacity = number(own.get("fill-opacity"))
        if opacity is not None and opacity < 0.5:
            continue
        p = back(m, x, y)
        evenodd = (eff.get("fill-rule") or "nonzero").strip() == "evenodd"
        if p is not None and inside(el, own, *p, evenodd):
            under = fill
    return under


class SvgDeclarationError(ET.ParseError):
    """A DTD or entity declaration refused before any declared entity is read."""


class FigureTreeBuilder(ET.TreeBuilder):
    def __init__(self):
        super().__init__()
        self.processing_instructions = []

    def pi(self, target, data):
        self.processing_instructions.append((target, data))

    def doctype(self, name, pubid, system):
        raise SvgDeclarationError("DTD or entity declaration is outside S26's SVG allow-list")


def parse_svg(path: Path, source: bytes | None = None):
    """Refuse declaration markers in the bytes before constructing any XML parser.

    Strip NULs for the scan so UTF-16 and UTF-32 spellings cannot bypass it. This
    deliberately also refuses such text inside a comment. Parse the original bytes
    from the same read; the doctype callback remains a second guard.
    """
    raw = path.read_bytes() if source is None else source
    declarations = raw.replace(b"\x00", b"")
    if b"<!DOCTYPE" in declarations or b"<!ENTITY" in declarations:
        raise SvgDeclarationError("DTD or entity declaration is outside S26's SVG allow-list")
    target = FigureTreeBuilder()
    return ET.parse(BytesIO(raw), parser=ET.XMLParser(target=target)), target.processing_instructions


def svg_root(path: Path, source: bytes | None = None, *, missing_ok: bool = False):
    try:
        if source is not None:
            tree, _ = parse_svg(path, source)
            return tree.getroot()
        tree, processing_instructions = parse_svg(path)
    except OSError:
        if missing_ok:
            return None
        raise
    except SvgDeclarationError as e:
        fail("S26", path, 0, str(e))
        return None
    except (ET.ParseError, LookupError, UnicodeDecodeError, ValueError) as e:
        rule = ("S14" if path.stem.endswith("-idea") else
                "S24" if path.stem.endswith("-modern") else "S15")
        fail(rule, path, 0, f"not well-formed SVG: {e}")
        return None
    if processing_instructions:
        target, data = processing_instructions[0]
        instruction = target + (f" {data}" if data else "")
        fail("S26", path, 0,
             f"processing instruction {instruction!r} is outside S26's SVG allow-list")
        return None
    return tree.getroot()


def caption_text_rules(path: Path, el, kind: str) -> None:
    """S1 and S2 in a figure's title and caption."""
    text = text_of(el)
    if "—" in text:
        fail("S1", path, 0, f"em dash in the {kind}: {text[:60]}")
    for m in CREW.finditer(blank_quotes(text)):
        fail("S2", path, 0, f'"{m.group(0)}" in the {kind}')


def colours(path: Path, root, allowed: set[str], rule: str) -> None:
    bad = defaultdict(int)
    for el, own, _ in walk(root):
        for k in COLOUR_ATTRS:
            v = own.get(k)
            if v is None or v.lower() == "none":
                continue
            if v.lower() not in allowed:
                bad[f"{k}={v}"] += 1
    for what, n in sorted(bad.items()):
        fail(rule, path, 0, f"colour {what} ({n}×) is not in the palette")


def check_idea(path: Path, ref: str, required: bool) -> int:
    """S13, S14, S20, S21 and S26 for one idea figure. Returns how many of its points wait
    for a letter while it is in the transition (no letter yet, the switch off), else 0."""
    root = svg_root(path)
    if root is None or not supported_svg(path, root):
        return 0
    try:
        return measure_idea(path, ref, required, root)
    except SvgMeasurementError as e:
        fail("S26", path, 0, f"cannot measure SVG: {e}")
        return 0


def measure_idea(path: Path, ref: str, required: bool, root) -> int:
    vb = " ".join(root.get("viewBox", "").replace(",", " ").split())
    if vb != "0 0 400 300":
        fail("S14", path, 0, f"viewBox {vb or 'missing'}, not 0 0 400 300")
    title = root.find(f"{SVG}title")
    if title is None or not text_of(title):
        fail("S14", path, 0, "no <title>")
    else:
        caption_text_rules(path, title, "title")
        if not re.fullmatch(rf"{re.escape(ref)} at a glance(?:: .+)?", " ".join(text_of(title).split())):
            fail("S14", path, 0, f"title \"{text_of(title)}\" is not \"{ref} at a glance\", "
                 "with a name after a colon if it has one")
    desc = root.find(f"{SVG}desc")
    if desc is None or not text_of(desc):
        fail("S13", path, 0, "no caption (<desc>)")
    else:
        caption_text_rules(path, desc, "caption")
        text = " ".join(text_of(desc).split())
        n = len(text.split())
        if n > 50:
            fail("S13", path, 0, f"caption of {n} words; 50 at most")
        ends = len(re.findall(r"[.?!][\"')]*(?=\s|$)", text))
        if n > 40 or ends > 2:
            report("D5", path, 0, f"caption of {n} words, {ends} sentence(s)")
    colours(path, root, IDEA_COLOURS | WHITE, "S14")
    one_letter_one_point(path, root)
    return check_idea_letters(path, root, required)


def drawn_letters(path: Path) -> set[str] | None:
    """The letters Euclid's figure draws, which S16 holds to Heath's text; None when there
    is no figure to read (S15 or S26 says why)."""
    try:
        tree, _ = parse_svg(path)
    except (OSError, ET.ParseError, LookupError, UnicodeDecodeError, ValueError):
        return None
    root = tree.getroot()
    return {text_of(el) for el in root.iter() if tag(el) == "text" and LETTER.fullmatch(text_of(el))}


def letter_centre(own, eff, m, s: str) -> tuple[float, float]:
    """About where a letter's glyph stands: x and y give the start of its baseline (its
    middle or its end, by text-anchor), and a capital in Georgia is about 0.6 em wide and
    0.7 em high."""
    size = number(eff.get("font-size")) or 16.0
    w = 0.6 * size * len(s)
    shift = {"middle": 0.0, "end": -w / 2}.get((eff.get("text-anchor") or "start").strip(), w / 2)
    return at(m, coord(own.get("x")) + shift, coord(own.get("y")) - 0.35 * size)


def idea_points(root) -> list[tuple[str, tuple[float, float], tuple | None]]:
    """(kind, where, exemption) for each point an idea figure shows (S21): a dot (a filled
    circle of radius 6 at most), each end of a straight line drawn in a Byrne colour or
    black and 25 long at least, and each corner of a polygon filled or stroked in one.
    White grid lines, parchment dividers, paths (the angles and arcs) and polylines (the
    right-angle marks) show no points. `exemption` is the data-unlettered in force."""
    out = []
    for el, own, eff, m, exempt in placed(root):
        t = tag(el)
        fill = (eff.get("fill") or "black").strip().lower()
        stroke = (eff.get("stroke") or "none").strip().lower()
        if t == "circle":
            if 0 < coord(own.get("r")) <= DOT and fill != "none":
                out.append(("a dot", at(m, coord(own.get("cx")), coord(own.get("cy"))), exempt))
        elif t == "line" and stroke in BYRNE:
            a = at(m, coord(own.get("x1")), coord(own.get("y1")))
            b = at(m, coord(own.get("x2")), coord(own.get("y2")))
            if math.dist(a, b) >= MARK:
                out += [("an end of a straight line", a, exempt), ("an end of a straight line", b, exempt)]
        elif t == "polygon" and (fill in BYRNE or stroke in BYRNE):
            v = [float(x) for x in NUM.findall(own.get("points", ""))]
            out += [("a corner of a polygon", at(m, x, y), exempt) for x, y in zip(v[0::2], v[1::2])]
    return out


def ink_fault(root, eff, centre: tuple[float, float], s: str) -> str | None:
    """S20's ink for letter s, its glyph's middle at `centre`: what is wrong with it, or
    None. It is #222222 on the parchment or yellow, and #fbf7ee on red, blue or black."""
    dark = fill_under(root, *centre) in DARK
    ink = IDEA_INK_ON_DARK if dark else IDEA_INK
    if (eff.get("fill") or "black").strip().lower() == ink:
        return None
    return (f"letter {s} in {eff.get('fill') or 'black'}, not {ink}: a letter "
            f"on {'red, blue or black' if dark else 'the parchment or yellow'} is in {ink}")


def check_idea_letters(path: Path, root, required: bool) -> int:
    """S20: each letter is one of Heath's, as Euclid's figure draws it, upright (or, while
    UPRIGHT_LETTERS_REQUIRED is False, italic, one style in the figure), at 14, in the
    figure's black, or in the parchment's colour where it stands on red, blue or black.
    S21: each point the figure shows has a letter within 30 of it, or is marked
    data-unlettered with its reason. Returns the points waiting for a letter while the
    figure is in the transition, else 0."""
    euclid = path.with_name(path.name.replace("-idea", ""))
    heaths = drawn_letters(euclid)
    letters, styles = [], []
    for el, own, eff, m, _ in placed(root):
        if tag(el) != "text":
            continue
        s = text_of(el)
        if not re.search(r"[A-Za-z]", s):
            continue
        if not LETTER.fullmatch(s):
            fail("S20", path, 0, f"<text>{s}</text>: an idea figure's text is Heath's letters, "
                 "one to a <text>, or numbers on a fill")
            continue
        if heaths is None:
            fail("S20", path, 0, f"letter {s}, and no {euclid.name} to take Heath's letters from")
        elif s not in heaths:
            fail("S20", path, 0, f"letter {s} is not one of Heath's letters as {euclid.name} "
                 f"draws them ({', '.join(sorted(heaths))})")
        centre = letter_centre(own, eff, m, s)
        fault = ink_fault(root, eff, centre, s)
        if fault:
            fail("S20", path, 0, fault)
        if number(eff.get("font-size")) != IDEA_LETTER_SIZE:
            fail("S20", path, 0, f"letter {s} at font-size {eff.get('font-size')}, not {IDEA_LETTER_SIZE}")
        styles.append((s, letter_style(eff)))
        letters.append(centre)
    check_letter_style(path, "S20", styles)

    points = idea_points(root)
    for el in root.iter():
        if UNLETTERED not in el.attrib:
            continue
        why = " ".join(el.attrib[UNLETTERED].split())
        excused = sum(1 for _, _, ex in points if ex is not None and ex[0] is el)
        if len(why.split()) < 2:
            fail("S21", path, 0, f'<{tag(el)} {UNLETTERED}="{why}">: give the reason Heath '
                 "leaves these points without letters, in words")
        if not excused:
            fail("S21", path, 0, f'<{tag(el)} {UNLETTERED}="{why}"> marks no point a letter '
                 "would go to (a dot, an end of a straight line, a corner); remove it")
        tally = idea_exemptions[(rel(path), why)]
        tally[0] += 1
        tally[1] += excused

    groups: list[list] = []
    for p in points:
        for g in groups:
            if math.dist(g[0][1], p[1]) < SAME:
                g.append(p)
                break
        else:
            groups.append([p])
    waiting = []
    for g in groups:
        shown = [p for p in g if p[2] is None]
        if shown and not any(math.dist(p[1], c) <= NEAR for p in shown for c in letters):
            waiting.append(shown)
    if not letters and not required:
        return len(waiting)
    for shown in waiting:
        kinds = " and ".join(sorted({k for k, _, _ in shown}))
        x, y = shown[0][1]
        fail("S21", path, 0, f"the point at ({x:.0f}, {y:.0f}), {kinds}, has no letter "
             f"within {NEAR:g}: give it Heath's letter, or mark what draws it {UNLETTERED} "
             "with the reason his figure gives it none")
    return 0


def glyph_hull(own, eff, m, s: str) -> list[tuple[float, float]]:
    """The corners of the hull of letter s's capital (S26), upright or italic as its
    font-style sets it, where the text element puts it: x and y give the start of its
    baseline (its middle or its end, by text-anchor, the whole label's advance counted,
    a prime or a subscript after the capital included), at its font-size, with dx and dy
    applied before transforms."""
    glyphs = GLYPHS_ITALIC if letter_style(eff) == "italic" else GLYPHS_UPRIGHT
    advance, corners = glyphs[s[0]]
    whole = advance + sum(SUFFIXES.get(c, 0) for c in s[1:])
    k = (number(eff.get("font-size")) or 16.0) / EM
    x = coord(own.get("x")) + coord(own.get("dx")) + {
        "middle": -whole * k / 2, "end": -whole * k}.get(
        (eff.get("text-anchor") or "start").strip(), 0.0)
    y = coord(own.get("y")) + coord(own.get("dy"))
    return [at(m, x + corners[i] * k, y - corners[i + 1] * k)
            for i in range(0, len(corners), 2)]


def stretch(m) -> float:
    """The most an affine map m lengthens any length: its larger singular value. A
    stroke's width and a dot's radius are taken at this, so that a map that stretches one
    way more than another never makes them seem thinner than they are (S26)."""
    a, b, c, d = m[:4]
    t, det = a * a + b * b + c * c + d * d, a * d - b * c
    return math.sqrt((t + math.sqrt(max(0.0, t * t - 4 * det * det))) / 2)



def decimal_end(value: str, pos: int) -> int | None:
    """Read an optional sign, digits, and an optional point followed by digits, linearly."""
    if pos < len(value) and value[pos] in "+-":
        pos += 1
    start = pos
    while pos < len(value) and "0" <= value[pos] <= "9":
        pos += 1
    if pos == start:
        return None
    if pos < len(value) and value[pos] == ".":
        pos += 1
        start = pos
        while pos < len(value) and "0" <= value[pos] <= "9":
            pos += 1
        if pos == start:
            return None
    return pos


def length(value: str | None) -> float | None:
    """One bounded plain decimal, with no unit, exponent or internal white space."""
    v = (value or "").strip(SVG_SPACE)
    if not v or decimal_end(v, 0) != len(v):
        return None
    n = float(v)
    if n == 0 and any(c in "123456789" for c in v):
        return None  # A positive radius rounded to zero would silently lose its arc.
    return n if math.isfinite(n) and abs(n) <= SVG_NUMBER_LIMIT else None


def decimal_list(value: str) -> list[str] | None:
    """Plain decimals separated by a comma with optional white space, or white space.
    Retain the spelling so path flags can require exactly 0 or 1."""
    v = value.strip(SVG_SPACE)
    parts, pos = [], 0
    while pos < len(v):
        end = decimal_end(v, pos)
        if end is None or length(v[pos:end]) is None:
            return None
        parts.append(v[pos:end])
        pos = end
        while pos < len(v) and v[pos] in SVG_SPACE:
            pos += 1
        if pos == len(v):
            return parts
        if v[pos] == ",":
            pos += 1
            while pos < len(v) and v[pos] in SVG_SPACE:
                pos += 1
            if pos == len(v):
                return None
        elif pos == end:
            return None
    return None


def supported_path(value: str) -> bool:
    """Whole paths in main's command language, including counts, separators and flags."""
    parts = re.split(r"([A-Za-z])", value.strip(SVG_SPACE))
    if len(parts) < 3 or parts[0] or parts[1] != "M":
        return False
    for cmd, args in zip(parts[1::2], parts[2::2]):
        if cmd not in "MLHVACZ":
            return False
        if cmd == "Z":
            if args.strip(SVG_SPACE):
                return False
            continue
        v = decimal_list(args)
        arity = PATH_ARITY[cmd.lower()]
        if v is None or len(v) % arity:
            return False
        if cmd == "A" and any(float(v[i]) < 0 or float(v[i + 1]) < 0
                              or v[i + 3] not in ("0", "1") or v[i + 4] not in ("0", "1")
                              for i in range(0, len(v), arity)):
            return False
    return True


def arc_fault(value: str) -> str | None:
    """What SVG draws, in place of an arc, for the first arc of a supported path that it
    does not draw as one; or None. SVG's implementation notes for arcs (F.6.2) omit an arc
    whose ends are one point, and then draw one with a radius of 0 as a straight line, so
    that an arc with both draws nothing. Any other arc draws, whatever its large-arc and sweep flags: radii too short to reach its
    ends are enlarged until they reach (F.6.6), and two distinct ends then lie on two
    ellipses of those radii, or on one when the radii only just reach; the flags take one
    arc of them from the one end to the other (F.6.5), and on one ellipse both arcs are
    halves, so that the large-arc flag changes nothing."""
    parts = re.split(r"([A-Za-z])", value.strip(SVG_SPACE))
    x = y = sx = sy = 0.0
    for cmd, args in zip(parts[1::2], parts[2::2]):
        if cmd == "Z":
            x, y = sx, sy
            continue
        v = [float(n) for n in decimal_list(args)]
        arity = PATH_ARITY[cmd.lower()]
        for i in range(0, len(v), arity):
            group = v[i:i + arity]
            if cmd == "A" and (group[5], group[6]) == (x, y):
                return f"nothing for an arc whose ends are one point, ({x:g}, {y:g})"
            if cmd == "A" and (group[0] == 0 or group[1] == 0):
                return f"a straight line for an arc with a radius of 0, from ({x:g}, {y:g})"
            if cmd == "H":
                x = group[0]
            elif cmd == "V":
                y = group[0]
            else:
                x, y = group[-2:]
            if cmd == "M" and i == 0:
                sx, sy = x, y
    return None


def supported_svg(path: Path, root) -> bool:
    """Refuse deep trees and unsupported SVG before recursive walks or measurements.
    Read raw XML attributes only; CSS is neither accepted nor interpreted."""
    if root.tag != SVG + "svg":
        fail("S26", path, 0, f"<{tag(root)}> root is not an SVG-namespaced <svg> in "
             "S26's SVG allow-list")
        return False

    valid = True
    pending = [(root, 0)]
    while pending:
        el, depth = pending.pop()
        if depth > SVG_MAX_DEPTH:
            fail("S26", path, 0, f"SVG nesting exceeds {SVG_MAX_DEPTH} levels below the root")
            return False
        children = list(el)
        pending.extend((child, depth + 1) for child in children)
        t = tag(el)
        if not el.tag.startswith(SVG):
            fail("S26", path, 0, f"<{t}> is outside S26's SVG namespace")
            valid = False
        if children and t not in ("svg", "g"):
            fail("S26", path, 0,
                 f"<{t}> may not contain element children in S26's SVG allow-list")
            valid = False
    if not valid:
        return False

    for el in root.iter():
        t = tag(el)
        if t not in SVG_ELEMENTS or (t == "svg" and el is not root):
            fail("S26", path, 0, f"<{t}> is outside S26's SVG allow-list")
            valid = False
            continue
        if t == "ellipse" and not {"rx", "ry"} <= el.attrib.keys():
            fail("S26", path, 0, "<ellipse> needs explicit rx and ry in S26's SVG allow-list")
            valid = False
        for attr, value in el.attrib.items():
            if attr in SVG_NUMBERS:
                n = length(value)
                ok = n is not None
                if ok and attr in ("r", "rx", "ry", "width", "height", "font-size", "stroke-width"):
                    ok = n >= 0
                if ok and attr in ("fill-opacity", "stroke-opacity"):
                    ok = 0 < n <= 1
            elif attr in SVG_KEYWORDS:
                ok = value in SVG_KEYWORDS[attr]
            elif attr in ("points", "viewBox", "stroke-dasharray"):
                v = decimal_list(value)
                ok = v is not None
                if attr == "viewBox":
                    ok = ok and len(v) == 4 and float(v[2]) > 0 and float(v[3]) > 0
                elif attr == "points":
                    ok = ok and len(v) % 2 == 0
                else:
                    ok = value == "none" or (ok and all(float(n) >= 0 for n in v)
                                                  and any(float(n) > 0 for n in v))
            elif attr == "transform":
                ok = letter_transform_of(value) is not None
            elif attr == "d":
                ok = supported_path(value)
                drawn = arc_fault(value) if ok else None
                if drawn:
                    fail("S26", path, 0, f"<{t}> d {value!r}: SVG draws {drawn}, so it is "
                         "outside S26's SVG allow-list")
                    valid = False
                    continue
            else:
                ok = attr == UNLETTERED
            if not ok:
                fail("S26", path, 0, f"<{t}> {attr} {value!r} is outside S26's SVG allow-list")
                valid = False
        if t == "text":
            s = text_of(el)
            if not LETTER.fullmatch(s) and not ASCII_NUMERIC_ANNOTATION.fullmatch(s):
                fail("S26", path, 0,
                     f"<text> payload {s!r} is outside S26's SVG allow-list")
                valid = False
    if not valid:
        return False
    # Attribute spellings are now safe to traverse. Only point labels need the
    # regular outlines: main also uses bold numerical annotations.
    for el, _, eff in walk(root):
        if tag(el) != "text":
            continue
        s = text_of(el)
        if not LETTER.fullmatch(s):
            continue
        if eff.get("font-family") not in SVG_KEYWORDS["font-family"]:
            fail("S26", path, 0, f"letter {s} has effective font-family "
                 f"{eff.get('font-family')!r}: outside S26's SVG allow-list")
            valid = False
        if eff.get("fill", "black") == "none":
            fail("S26", path, 0,
                 f"letter {s} has effective fill 'none': outside S26's SVG allow-list")
            valid = False
        if eff.get("stroke", "none") != "none":
            fail("S26", path, 0, f"letter {s} has an effective stroke: outside S26's SVG allow-list")
            valid = False
        if eff.get("font-weight", "normal") != "normal":
            fail("S26", path, 0, f"letter {s} has effective font-weight "
                 f"{eff['font-weight']!r}: outside S26's SVG allow-list")
            valid = False
    return valid


def rect_outline(own, errors: list[float] | None = None) -> list[tuple[float, float]] | None:
    """A rect's outline, its corners rounded by rx and ry as SVG rounds them (one given
    stands for both, and each is at most half the side), in short straight pieces; None
    when it has no width or no height, and SVG draws nothing. Given `errors`, append the
    corners' conservative chord error, before transforms."""
    x0, y0 = coord(own.get("x")), coord(own.get("y"))
    w, h = coord(own.get("width")), coord(own.get("height"))
    if w <= 0 or h <= 0:
        return None
    rx, ry = length(own.get("rx")), length(own.get("ry"))
    rx = ry if rx is None else rx
    ry = rx if ry is None else ry
    rx, ry = min(rx or 0.0, w / 2), min(ry or 0.0, h / 2)
    if rx <= 0 or ry <= 0:
        return [(x0, y0), (x0 + w, y0), (x0 + w, y0 + h), (x0, y0 + h), (x0, y0)]
    out = []
    quarter = max(1, round(math.pi / 2 / ARC_STEP))
    if errors is not None:
        errors.append(max(rx, ry) * (1 - math.cos(math.pi / (4 * quarter))))
    for cx, cy, start in ((x0 + w - rx, y0 + ry, -90), (x0 + w - rx, y0 + h - ry, 0),
                          (x0 + rx, y0 + h - ry, 90), (x0 + rx, y0 + ry, 180)):
        for i in range(quarter + 1):
            a = math.radians(start + 90 * i / quarter)
            out.append((cx + rx * math.cos(a), cy + ry * math.sin(a)))
    return out + out[:1]


def miter_joins(segments, half: float, limit: float, closed: bool):
    """The filled corners beyond a round join, before transforms, up to the mitre limit.
    Only original segment boundaries join; directionless segments are skipped, and a
    closed subpath joins its last segment back to its first."""
    directed = [s for s in segments
                if s.start_tangent != (0, 0) and s.end_tangent != (0, 0)]
    if closed and directed:
        directed = directed + directed[:1]
    for a, c in zip(directed, directed[1:]):
        b = a.end
        ab, bc = math.hypot(*a.end_tangent), math.hypot(*c.start_tangent)
        ux, uy = (v / ab for v in a.end_tangent)
        vx, vy = (v / bc for v in c.start_tangent)
        turn, den = ux * vy - uy * vx, 1 + ux * vx + uy * vy
        if turn == 0 or den <= 0:
            continue
        if math.sqrt(2 / den) > limit:
            continue
        side = 1 if turn > 0 else -1
        nx, ny, mx, my = side * uy, -side * ux, side * vy, -side * vx
        yield [b, (b[0] + half * nx, b[1] + half * ny),
               (b[0] + half * (nx + mx) / den, b[1] + half * (ny + my) / den),
               (b[0] + half * mx, b[1] + half * my), b]


def strokes(path: Path, root):
    """(what it is, its points, half its width plus chord error) for each stroke, as a run
    of straight pieces: a line, a polyline, a polygon or a rect's outline (its corners
    rounded as rx and ry round them), each subpath of a path (closed where a Z closes it),
    a circle or an ellipse in short straight pieces; transforms applied, the width taken
    at the most the transform stretches it, a dashed stroke read whole, and a stroke SVG
    does not draw (a circle of no radius, a rect of no width, a run of no length with
    butt caps) left out (S26). Mitre joins add closed filled outlines
    with None in place of half the width: their outlines already include it."""
    for el, own, eff, m, _ in placed(root):
        t = tag(el)
        if t not in DRAWN or (eff.get("stroke") or "none").strip().lower() == "none":
            continue
        w = length(eff.get("stroke-width", "1"))
        if w is None or not math.isfinite(w):
            fail("S26", path, 0, f"<{t}> stroke-width {eff.get('stroke-width')!r} is not "
                 "a finite plain decimal")
            continue
        if w <= 0:
            continue
        closed = []
        run_errors = []
        segment_runs = []
        if t == "line":
            runs = [[(coord(own.get("x1")), coord(own.get("y1"))),
                     (coord(own.get("x2")), coord(own.get("y2")))]]
            run_errors = [0.0]
        elif t in ("polyline", "polygon"):
            v = [float(n) for n in NUM.findall(own.get("points", ""))]
            run = list(zip(v[0::2], v[1::2]))
            runs = [run + run[:1] if t == "polygon" else run]
            run_errors = [0.0]
        elif t == "path":
            rings = path_rings(own.get("d", ""), closed, run_errors, segment_runs)
            runs = [ring + ring[:1] if shut else ring for ring, shut in zip(rings, closed)]
        elif t == "rect":
            errors = []
            outline = rect_outline(own, errors)
            runs = [outline] if outline else []
            run_errors = [max(errors, default=0.0)] if outline else []
        else:
            cx, cy = coord(own.get("cx")), coord(own.get("cy"))
            rx = coord(own.get("r")) if t == "circle" else coord(own.get("rx"))
            ry = coord(own.get("r")) if t == "circle" else coord(own.get("ry"))
            steps = round(math.tau / ARC_STEP)
            runs = [] if rx <= 0 or ry <= 0 else [
                [(cx + rx * math.cos(i * math.tau / steps),
                  cy + ry * math.sin(i * math.tau / steps))
                 for i in range(steps + 1)]]
            # An ellipse stretches the unit circle by at most its greater radius.
            run_errors = ([max(rx, ry) * (1 - math.cos(math.pi / steps))]
                          if runs else [])
        dashed = (eff.get("stroke-dasharray") or "none").strip().lower() != "none"
        kind = "a dashed line" if dashed and t == "line" else \
            ("an " if t == "ellipse" else "a ") + t
        cap = (eff.get("stroke-linecap") or "butt").strip()
        miter = (eff.get("stroke-linejoin") or "miter").strip() == "miter"
        limit = length(eff.get("stroke-miterlimit"))
        limit = 4.0 if limit is None else limit
        if t != "path":
            closed = [t in ("polygon", "rect", "circle", "ellipse")] * len(runs)
            # Rounded rectangles join their sides tangentially to their corners.
            segment_runs = [[stroke_segment([a, b]) for a, b in zip(run, run[1:])]
                            if t in ("polyline", "polygon", "rect")
                            and not any(run_errors) else []
                            for run in runs]
        for run, shut, segments, error in zip(runs, closed, segment_runs, run_errors):
            if len(run) > 1 and not (cap == "butt" and all(p == run[0] for p in run)):
                half = (w / 2 + error) * stretch(m)
                yield kind, [at(m, x, y) for x, y in run], half
                if miter:
                    for join in miter_joins(segments, w / 2, limit, shut):
                        yield kind, [at(m, x, y) for x, y in join], None


def dots(root):
    """(where, radius) for each dot a figure draws: a filled circle of radius DOT at most,
    transforms applied, its radius taken at the most the transform stretches it (S26, as
    S21 reads a dot)."""
    for el, own, eff, m, _ in placed(root):
        r = coord(own.get("r"))
        filled = (eff.get("fill") or "black").strip().lower() != "none"
        if tag(el) == "circle" and 0 < r <= DOT and filled:
            yield at(m, coord(own.get("cx")), coord(own.get("cy"))), r * stretch(m)


def point_gap(p, a, b) -> float:
    """How far the point p stands from the straight piece ab."""
    dx, dy = b[0] - a[0], b[1] - a[1]
    n = dx * dx + dy * dy
    t = 0.0 if n == 0 else max(0.0, min(1.0, ((p[0] - a[0]) * dx + (p[1] - a[1]) * dy) / n))
    return math.hypot(p[0] - a[0] - t * dx, p[1] - a[1] - t * dy)


def crosses(a, b, c, d) -> bool:
    """Whether the straight pieces ab and cd cross."""
    def side(p, q, r):
        return (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0])
    return side(a, b, c) * side(a, b, d) < 0 and side(c, d, a) * side(c, d, b) < 0


def hull_gap(hull, a, b) -> float:
    """How far the straight piece ab stands from the convex polygon `hull`: 0 if it meets
    it."""
    if enclosed([hull], *a, False) or enclosed([hull], *b, False):
        return 0.0
    gap = math.inf
    for c, d in zip(hull, hull[1:] + hull[:1]):
        if crosses(a, b, c, d):
            return 0.0
        gap = min(gap, point_gap(c, a, b), point_gap(a, c, d), point_gap(b, c, d))
    return gap


def nearest(hull, pieces, spots) -> tuple[float, str] | None:
    """How near a stroke (less half its width), its filled joins, or a dot (less
    its radius) comes to a letter's hull, and what it is; None if none comes within CLEAR."""
    xs, ys = [p[0] for p in hull], [p[1] for p in hull]
    best = None
    for kind, run, half in pieces:
        if half is None and enclosed([run], *hull[0], False):
            if best is None or best[0] > 0:
                best = (0.0, kind)
        reach = CLEAR + (half or 0.0)
        lo_x, hi_x = min(xs) - reach, max(xs) + reach
        lo_y, hi_y = min(ys) - reach, max(ys) + reach
        for a, b in zip(run, run[1:]):
            if max(a[0], b[0]) < lo_x or min(a[0], b[0]) > hi_x \
                    or max(a[1], b[1]) < lo_y or min(a[1], b[1]) > hi_y:
                continue
            gap = hull_gap(hull, a, b) - (half or 0.0)
            if gap < CLEAR and (best is None or gap < best[0]):
                best = (gap, kind)
    for p, r in spots:
        gap = (0.0 if enclosed([hull], *p, False) else
               min(point_gap(p, c, d) for c, d in zip(hull, hull[1:] + hull[:1]))) - r
        if gap < CLEAR and (best is None or gap < best[0]):
            best = (gap, "a dot")
    return best


def one_letter_one_point(path: Path, root, cuts: tuple[float, ...] = ()) -> None:
    """S26: a figure draws each letter once, or, where Heath's figures stand side by side
    with `cuts` between them, once in each, every letter wholly on one side of every cut;
    and each letter stands CLEAR of every stroke, every dot and the canvas's edge,
    measured by the hull of its capital as Georgia draws it, upright or italic."""
    if not supported_svg(path, root):
        return
    vb = [float(v) for v in NUM.findall(root.get("viewBox", ""))]
    pieces, spots = list(strokes(path, root)), list(dots(root))
    count: dict[tuple[int, str], int] = defaultdict(int)
    for el, own, eff, m, _ in placed(root):
        if tag(el) != "text":
            continue
        unsupported = False
        if len(el):
            fail("S26", path, 0, "<text> has an element child: draw each label in a "
                 "separate <text>")
            unsupported = True
        s = text_of(el)
        if not LETTER.fullmatch(s):
            if re.search(r"[A-Z]", s):
                fail("S26", path, 0, f"<text> {s!r} has unmeasured capitals: draw each "
                     "label in a separate <text>")
            continue
        if unsupported:
            continue
        hull = glyph_hull(own, eff, m, s)
        xs, ys = [p[0] for p in hull], [p[1] for p in hull]
        where = f"letter {s} at ({coord(own.get('x')):g}, {coord(own.get('y')):g})"
        count[(sum(1 for c in cuts if (min(xs) + max(xs)) / 2 > c), s)] += 1
        for c in cuts:
            if min(xs) < c < max(xs):
                fail("S26", path, 0, f"{where} stands across the cut at x {c:g} between two "
                     "of the figures side by side (SIDE_BY_SIDE)")
        near = nearest(hull, pieces, spots)
        if near:
            gap, kind = near
            fail("S26", path, 0, f"{where} meets {kind}" if gap <= 0 else
                 f"{where} stands {gap:.1f} from {kind}, under {CLEAR:g}: move it clear")
        if len(vb) == 4:
            edge = min(min(xs) - vb[0], vb[0] + vb[2] - max(xs),
                       min(ys) - vb[1], vb[1] + vb[3] - max(ys))
            if edge < CLEAR:
                fail("S26", path, 0, f"{where} stands {max(edge, 0):.1f} from the canvas's "
                     f"edge, under {CLEAR:g}")
    for (case, s), k in sorted(count.items()):
        if k > 1:
            fail("S26", path, 0, f"letter {s} drawn {k} times"
                 + (f" in the figure {case + 1} of {len(cuts) + 1} side by side" if cuts else "")
                 + ": one letter names one point")


def heath_letters(book: str, n: int) -> set[str]:
    """The capital letters of Heath's text, as STYLE section 8 gives the command: comments,
    headings, Heath's references, "Q. E. D.", "Q. E. F.", "I say" and "PORISM." taken out,
    then every word wholly in capitals, letter by letter."""
    text = HTML_COMMENT.sub("", heath.heath_path(book, n).read_text(encoding="utf-8"))
    found = set()
    for line in text.splitlines():
        if line.startswith("#"):
            continue
        line = re.sub(r"\[[^\]\n]*\]", "", line)
        line = re.sub(r"Q\. E\. [DF]\.", "", line)
        line = line.replace("I say", "").replace("PORISM.", "")
        for w in re.findall(r"\b[A-Z]+\b", line):
            found.update(w)
    return found


def check_euclid(path: Path, ref: str) -> None:
    root = svg_root(path)
    if root is None or not supported_svg(path, root):
        return
    try:
        measure_euclid(path, ref, root)
    except SvgMeasurementError as e:
        fail("S26", path, 0, f"cannot measure SVG: {e}")


def measure_euclid(path: Path, ref: str, root) -> None:
    book, n = ref.split(".")
    n = int(n)
    vb = root.get("viewBox", "").replace(",", " ").split()
    width = float(vb[2]) if len(vb) == 4 else None
    if width is None or not 400 <= width <= 440:
        fail("S15", path, 0, f"viewBox width {width}, not 400 to 440")
    title = root.find(f"{SVG}title")
    if title is None or not text_of(title):
        fail("S15", path, 0, "no <title>")
    else:
        caption_text_rules(path, title, "title")
        if not re.fullmatch(rf"Euclid {re.escape(ref)}: .+", " ".join(text_of(title).split())):
            fail("S15", path, 0, f"title \"{text_of(title)}\" is not \"Euclid {ref}: …\"")
    if root.find(f".//{SVG}desc") is not None:
        fail("S15", path, 0, "a caption (<desc>): Euclid's figure has none")
    colours(path, root, EUCLID_COLOURS, "S15")

    drawn, styles = set(), []
    thin, heavy = defaultdict(int), defaultdict(int)
    usual = defaultdict(int)
    for el, own, eff in walk(root):
        t = tag(el)
        if t == "text":
            s = text_of(el)
            if LETTER.fullmatch(s):
                drawn.add(s[0])
                styles.append((s, letter_style(eff)))
                size = number(eff.get("font-size"))
                if size != 17:
                    fail("S15", path, 0, f"letter {s} at font-size {eff.get('font-size')}, not 17")
            continue
        if t not in DRAWN:
            continue
        stroke = (eff.get("stroke") or "none").lower()
        if stroke != "none":
            w = length(eff.get("stroke-width", "1"))
            if w is None or not math.isfinite(w):
                continue  # S26 names unsupported widths, without assuming a default.
            if w < 1.2:
                thin[w] += 1
            elif w > 3.2:
                heavy[w] += 1
            expected = {"#3b2f2f": (1.6, 1.6), "#8c7b62": (1.3, 1.3), "#a0522d": (2.4, 2.6)}.get(stroke)
            if expected and not expected[0] <= w <= expected[1]:
                usual[f"{stroke} stroke {w:g} (usual {expected[0]:g}"
                      + (f" to {expected[1]:g})" if expected[1] != expected[0] else ")")] += 1
        elif t == "circle" and (eff.get("fill") or "").lower() in ("#3b2f2f", "#a0522d"):
            r = number(own.get("r"))
            if r is not None and r != 2.6:
                usual[f"dot of radius {r:g} (usual 2.6)"] += 1
    for w, k in sorted(thin.items()):
        fail("S15", path, 0, f"stroke-width {w:g} ({k}×) is under 1.2")
    for w, k in sorted(heavy.items()):
        fail("S15", path, 0, f"stroke-width {w:g} ({k}×) is over 3.2")
    if usual:
        report("D11", path, 0, "; ".join(f"{what} ×{k}" for what, k in sorted(usual.items())))
    check_letter_style(path, "S15", styles)

    # S16: all and only Heath's letters.
    text = heath_letters(book, n)
    exc = LETTER_EXCEPTIONS.get((book, n), {})
    extra = drawn - text - exc.get("extra", set())
    missing = text - drawn - exc.get("missing", set())
    if extra:
        fail("S16", path, 0, f"draws {', '.join(sorted(extra))}, not in heath/{book}/{n:02d}.md")
    if missing:
        fail("S16", path, 0, f"does not draw {', '.join(sorted(missing))}, which "
             f"heath/{book}/{n:02d}.md names")
    for side, letters in (("extra", exc.get("extra", set())), ("missing", exc.get("missing", set()))):
        stale = letters - drawn if side == "extra" else letters & drawn
        if stale:
            fail("S16", path, 0, f"the exception for {', '.join(sorted(stale))} in "
                 "LETTER_EXCEPTIONS no longer applies; remove it")
    one_letter_one_point(path, root, SIDE_BY_SIDE.get((book, n), ()))


# ---------------------------------------------------------------------------------------
# The figure of the modern way (S24, S25; STYLE, section 7): figures/<book>/NN-modern.svg,
# intended for the page's paragraph "**The modern way.**". It is drawn as Euclid's figure
# is, on its canvas and in its palette, with its letters, upright, at the same points,
# and with the paragraph's own names for what the modern way measures (a, b, θ, u),
# italic, so that a reader moves between the two figures by the same names.

MODERN_SUFFIX = "-modern.svg"
MODERN_TEXT_SIZE = 17
# Main's deepest modern figure at c6ff6817 has three levels below its root.
MODERN_MAX_DEPTH = 16
# What the text of a modern figure may hold besides one of Heath's letters: the
# paragraph's lower-case Latin and Greek names, digits, and the signs of an expression.
MODERN_TEXT = re.compile(r"[a-zα-ωϑϕ0-9 +\-−·×()/√²³⁰¹⁴-⁹⁻½=,.|′'₀-₉<>≤≥±]+")
# TeX's Greek letters, as the paragraph writes them, and the letter each names.
TEX_GREEK = {"alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ", "epsilon": "ε",
             "varepsilon": "ε", "zeta": "ζ", "eta": "η", "theta": "θ", "vartheta": "θ",
             "iota": "ι", "kappa": "κ", "lambda": "λ", "mu": "μ", "nu": "ν", "xi": "ξ",
             "pi": "π", "varpi": "π", "rho": "ρ", "varrho": "ρ", "sigma": "σ",
             "varsigma": "σ", "tau": "τ", "upsilon": "υ", "phi": "φ", "varphi": "φ",
             "chi": "χ", "psi": "ψ", "omega": "ω"}
# The variant letters, each read as the letter it is a form of, in the paragraph and in
# the figure alike: ϑ as θ, ϕ as φ, ς as σ, ϖ as π, ϱ as ρ.
GREEK_VARIANTS = str.maketrans({"ϑ": "θ", "ϕ": "φ", "ς": "σ", "ϖ": "π", "ϱ": "ρ"})
TEX_SPAN = re.compile(r"\$([^$\n]+)\$")
# A command whose argument TeX sets upright, as words or Heath's letters: the argument,
# braces balanced, is no name of the modern way.
TEX_UPRIGHT = re.compile(r"\\(?:mathrm|text|textrm|textup|operatorname)\s*\{")
TEX_COMMAND = re.compile(r"\\([A-Za-z]+)")
# A lower-case letter standing alone in the paragraph's words, not the s of "A's" or
# "Euclid’s" after an apostrophe. Python's patterns name no class of Unicode's, so a
# letter of another script, a mark or a format character beside it is found by
# joins_word, and keeps it in its word too (éxponent spelled with a combining accent,
# eхponent with a Cyrillic х).
LONE_LOWER = re.compile(r"(?<![A-Za-z'’])[a-z](?![A-Za-z])")
# The abbreviations whose letters are no names: e.g. and i.e., each full stop escaped or
# not (e\.g\., which Markdown shows as e.g.) and spaces after the first or not (e. g.,
# e.  g., which a reader sees as e. g.); and the p of Heath's page before its number, as
# STYLE, section 5, cites it (vol. 1, p. 383), with the number when it is a Roman one,
# whose letters are no names either (p. ix, pp. v–vii).
ABBREVIATION = re.compile(r"(?<![A-Za-z])(?:(?:[eE]\\?\.\s*g|[iI]\\?\.\s*e)\\?\."
                          r"|pp?\\?\.(?:(?=\s*\d)|\s*[ivxlcdm]+(?:[–-][ivxlcdm]+)?"
                          r"(?![A-Za-z])))")
# The characters that show nothing and are not format characters (Unicode's Cf, which
# their category finds): the rest of Unicode's Default_Ignorable_Code_Point, the Hangul
# fillers, which it counts as letters, the combining grapheme joiner and the variation
# selectors, which it counts as marks, and the code points it leaves unassigned among
# them.
INVISIBLE = re.compile(r"[͏ᅟᅠ឴឵᠋-᠏⁥ㅤ"
                       r"︀-️ﾠ￰-￸\U000e0000-\U000e0fff]")
# What stands beside the article "a", spaces between, when it is a name, as in "AC = a"
# or "(a + b)²": a sign of an expression, a digit, raised or lowered, or a bracket.
BESIDE_A_NAME = set("=+-−×·/<>≤≥()[]0123456789⁰¹²³⁴⁵⁶⁷⁸⁹₀₁₂₃₄₅₆₇₈₉")


def modern_text_of(el) -> str:
    return "".join(el.itertext()).strip()


def modern_drawn_letters(path: Path) -> set[str] | None:
    """The letters Euclid's figure draws for S25, preserving internal whitespace."""
    try:
        tree, _ = parse_svg(path)
    except (OSError, ET.ParseError):
        return None
    return {modern_text_of(el) for el in tree.getroot().iter()
            if tag(el) == "text" and LETTER.fullmatch(modern_text_of(el))}


def without_upright(body: str) -> str:
    """A TeX span with each upright argument (\\mathrm{…}, \\text{…}) taken out, its
    braces balanced, so that nested braces end where TeX ends them."""
    out, pos = [], 0
    for m in TEX_UPRIGHT.finditer(body):
        if m.start() < pos:
            continue
        out.append(body[pos:m.start()])
        depth, i = 1, m.end()
        while i < len(body) and depth:
            depth += {"{": 1, "}": -1}.get(body[i], 0)
            i += 1
        out.append(" ")
        pos = i
    return "".join(out) + body[pos:]


def modern_span(text: str) -> tuple[int, int] | None:
    """Where the paragraph that opens "**The modern way.**" stands in a mishnah, as
    (start, end) source offsets. Read blocks in the original text, before masking any
    comments or code. Four columns of indentation start code, but cannot interrupt an
    open paragraph. Fences and HTML blocks keep their contents out of the search;
    inline comments leave the paragraph's line boundaries intact. Leading reference
    definitions are excluded without moving the offsets into the original text.
    These offsets also let a renderer put the figure after the whole paragraph."""
    for block in markdown_blocks(text, raw_html=True).inline:
        if not block.paragraph:
            continue
        definitions = reference_destination_ranges(block.text)
        start = definitions[-1].end if definitions else 0
        content = block.text[start:].lstrip(" \t\n")
        if content.startswith(MODERN_WAY):
            first = len(block.text) - len(content)
            return block.offsets[first], block.offsets[-1] + 1
    return None


def modern_paragraph(text: str) -> str | None:
    """The paragraph of a mishnah that opens "**The modern way.**" (modern_span), as a
    reader sees it: its HTML tags and comments and code blanked afterwards.
    Inline links keep their labels, with brackets and targets removed so that visible
    word boundaries stay intact and a link's bracket cannot turn the article a into a name.
    Reference links resolve against the whole document before their identifiers are
    blanked. None when there is no such paragraph."""
    span = modern_span(text)
    if span is None:
        return None
    source = text[span[0]:span[1]]
    syntax = markdown_syntax(source, indented_code=False,
                             reference_labels=document_reference_labels(text), inline_html=True)
    visible = blank_ranges(source, syntax.comments + syntax.destinations
                           + [(s.start, s.end) for s in syntax.spans])
    removed = set()
    for link in link_destination_ranges(source, references=False):
        if link.label < link.start and (link.start, link.end) in syntax.destinations:
            removed.add(link.label)
            removed.update(range(link.start, link.end))
    return "".join(c for i, c in enumerate(visible) if i not in removed)


def modern_markup_findings(text: str) -> list[str]:
    """Refuse unsupported markup before it can supply names to a modern figure."""
    blocks = markdown_blocks(text, raw_html=True).inline
    span = modern_span(text)
    candidate = next((block for block in blocks if block.paragraph
                      and any(line.lstrip(" \t").startswith(MODERN_WAY)
                              for line in block.text.splitlines())), None)
    # A leading multiline reference definition can hide the paragraph from modern_span.
    # Refuse its syntax here without trying to resolve its destination.
    if span is None and candidate is None:
        return []
    found = []
    if span is None:
        if candidate.references and any(REFERENCE_LABEL.match(line)
                                        for line in candidate.text.splitlines()):
            found.append("unsupported reference definition beside the modern paragraph")
        return found
    source = text[span[0]:span[1]]
    labels = document_reference_labels(text) | {
        reference_key(match.group(1))
        for block in blocks if block.references
        for line in block.text.splitlines()
        if (match := REFERENCE_LABEL.match(line))
    }
    selected = next((block for block in blocks if span[0] in block.offsets), None)
    contained_definition = bool(selected and selected.references
                                and reference_destination_ranges(selected.text))
    syntax = markdown_syntax(source, indented_code=False, reference_labels=labels,
                             inline_html=True)
    resolved_reference = any(
        source[start:start + 1] == "]" and source[start + 1:start + 2] != "("
        for start, _ in syntax.destinations)
    if contained_definition or resolved_reference:
        found.append("unsupported reference definition beside the modern paragraph")
    visible = blank_ranges(source, [(s.start, s.end) for s in syntax.spans])
    # Main uses no character references. Refuse their spellings, even after an escaped
    # ampersand, instead of letting the spelling supply names the reader does not see.
    if re.search(r"&(?:#[xX][0-9a-fA-F]+|#[0-9]+|[A-Za-z][A-Za-z0-9]*);", visible):
        found.append("unsupported character reference in the modern paragraph")
    # A format character (Unicode's Cf: a zero-width space, a soft hyphen, a joiner) shows
    # nothing, nor does a Hangul filler or a variation selector (INVISIBLE), so a letter
    # beside one would stand alone in a word the reader sees whole: e.g. or exponent.
    invisible = sorted({c for c in visible
                        if unicodedata.category(c) == "Cf" or INVISIBLE.match(c)})
    if invisible:
        found.append("unsupported invisible character "
                     + ", ".join(f"U+{ord(c):04X}" for c in invisible)
                     + " in the modern paragraph")
    # Refuse emphasis touching a word, also through an apostrophe or full stop, escaped or
    # not, with the emphasis on one side of it or both (*e*.g., *e*.*g*.).
    # Removing link syntax first also catches e[*x*](/reference)ponent.
    if re.search(r"\w(?:\*+|\\?['’.][*_]+|[*_]+\\?['’.][*_]*)\w", modern_paragraph(text)):
        found.append("unsupported intraword emphasis in the modern paragraph")
    if syntax.comments or any(backslashes_before(visible, m.start()) % 2 == 0
                              for m in INLINE_HTML.finditer(visible)):
        found.append("unsupported inline HTML tag or comment in the modern paragraph")
    # Inline links are supported; any remaining bracketed label could be a reference.
    links = link_destination_ranges(visible, references=False)
    visible = blank_ranges(visible, [(link.label, link.end) for link in links])
    if re.search(r"(?<!\\)\[[^\]\n]*\]", visible):
        found.append("unsupported reference-style link in the modern paragraph")
    return found


def joins_word(c: str) -> bool:
    """Whether a character beside a letter keeps it in one word: a letter of any script,
    Greek too (the r of 2πr is a name in TeX, $2\\pi r$), a mark, which sits on the letter
    before it, or a format character."""
    return bool(c) and (c.isalpha() or unicodedata.category(c) in {"Mn", "Mc", "Me", "Cf"})


def modern_names(paragraph: str) -> set[str]:
    """The names a modern-way paragraph uses: each lower-case Latin or Greek letter of a
    $…$ span, its commands taken out (\\vec, \\frac, \\sin) and its Greek ones read as
    their letters (\\theta, θ), what \\mathrm{…} sets upright left aside (Heath's points);
    and, outside the spans, each Greek letter, and each lower-case letter that stands
    alone, with no letter of any script, mark or format character beside it (joins_word),
    save the letters of English: one after an apostrophe (A's), those of e.g. and i.e.
    and of Heath's page (ABBREVIATION), and the article "a" when no sign of an expression,
    digit or bracket stands beside it (BESIDE_A_NAME)."""
    names: set[str] = set()

    def span(m: re.Match) -> str:
        body = without_upright(m.group(1))
        body = TEX_COMMAND.sub(lambda c: " " + TEX_GREEK.get(c.group(1), "") + " ", body)
        names.update(c for c in body.translate(GREEK_VARIANTS) if c.isalpha() and c.islower())
        return " "

    rest = TEX_SPAN.sub(span, paragraph).translate(GREEK_VARIANTS)
    rest = ABBREVIATION.sub(_blank, rest)
    for m in LONE_LOWER.finditer(rest):
        if joins_word(rest[m.start() - 1:m.start()]) or joins_word(rest[m.end():m.end() + 1]):
            continue
        before, after = rest[:m.start()].rstrip()[-1:], rest[m.end():].lstrip()[:1]
        if m.group(0) != "a" or {before, after} & BESIDE_A_NAME:
            names.add(m.group(0))
    names.update(c for c in rest if "α" <= c <= "ω")
    return names


# Derived from all 30 figures at 209d71fd: no CSS, units or exponent notation.
MODERN_ELEMENTS = {"svg", "title", "defs", "marker", "g", "rect", "line", "circle",
                   "ellipse", "path", "polygon", "polyline", "text"}
MODERN_NUMBERS = {"x", "y", "x1", "x2", "y1", "y2", "cx", "cy", "r", "rx", "ry",
                  "width", "height", "fill-opacity", "markerWidth", "markerHeight",
                  "refX", "refY", "font-size", "stroke-width"}
# Exact values from those figures, never CSS-wide keywords. The palette and text checks
# still apply after this syntax gate; omitted attributes retain their SVG defaults.
MODERN_VALUES = {
    "fill": EUCLID_COLOURS | {"none"},
    "stroke": {"#3b2f2f", "#8c7b62", "#a0522d"},
    "font-family": {"Georgia", "Georgia, serif", "Georgia, 'Times New Roman', serif"},
    "font-style": {"italic"},
    "text-anchor": {"middle", "start"},
    "stroke-linejoin": {"round"},
    "markerUnits": {"userSpaceOnUse"},
    "orient": {"auto-start-reverse"},
    "marker-end": {"url(#axis)", "url(#head)"},
    "id": {"axis", "head"},
}
MODERN_ATTRIBUTES = MODERN_NUMBERS | MODERN_VALUES.keys() | {
    "viewBox", "points", "stroke-dasharray", "transform", "d"}
# Marker viewports have their own exact spellings, from the same 30 figures.
# None uses text or strokes inside a marker, so those are refused below rather than
# measured without the marker's scale. An omitted markerUnits keeps SVG's default.
MODERN_MARKER_VALUES = {
    "id": {"axis", "head"},
    "markerUnits": {"userSpaceOnUse"},
    "markerWidth": {"5", "7", "12"},
    "markerHeight": {"5", "6", "10"},
    "viewBox": {"0 0 10 10", "0 0 7 6", "0 0 12 10"},
    "refX": {"9", "6", "11"},
    "refY": {"5", "3"},
    "orient": {"auto-start-reverse"},
}


def modern_number(value: str | None) -> float | None:
    """A finite plain decimal, scanned once without regex backtracking or units."""
    if not value:
        return None
    i = int(value[0] in "+-")
    start = i
    while i < len(value) and "0" <= value[i] <= "9":
        i += 1
    if i == start:
        return None
    if i < len(value) and value[i] == ".":
        i += 1
        start = i
        while i < len(value) and "0" <= value[i] <= "9":
            i += 1
        if i == start:
            return None
    if i != len(value):
        return None
    result = float(value)
    return result if math.isfinite(result) else None


def modern_numbers(value: str) -> list[float] | None:
    """Space-separated plain decimals, as main spells lists and transform arguments."""
    values = [modern_number(part) for part in value.split(" ")]
    return None if None in values else values


def modern_transform(value: str) -> bool:
    """Main uses one rotation about an explicit centre, with nothing trailing."""
    if not value.startswith("rotate(") or not value.endswith(")"):
        return False
    args = modern_numbers(value[7:-1])
    return (args is not None and len(args) == 3
            and all(math.isfinite(n) for n in transform_of(value)))


def modern_path(value: str) -> bool:
    """Main's paths use explicit M, L, A and final z, with space-separated decimals. An
    arc has positive radii and ends at another point than it begins, or SVG draws it as
    a straight line or not at all (arc_fault)."""
    parts, i, point = value.split(" "), 0, None
    if parts[0] != "M":
        return False
    while i < len(parts):
        command = parts[i]
        if command == "z":
            return i == len(parts) - 1
        count = {"M": 2, "L": 2, "A": 7}.get(command)
        if count is None:
            return False
        args = parts[i + 1:i + 1 + count]
        numbers = [modern_number(arg) for arg in args]
        if len(args) != count or None in numbers:
            return False
        if command == "A" and (any(n <= 0 for n in numbers[:2])
                               or any(arg not in {"0", "1"} for arg in args[3:5])
                               or numbers[5:] == point):
            return False
        point = numbers[-2:]
        i += count + 1
    return True


def serialized_attribute_values(source: str):
    """The quoted attribute values of XML start tags, before XML normalisation."""
    at = 0
    while at < len(source):
        start = source.find("<", at)
        if start < 0:
            return
        if source.startswith("<!--", start):
            end = source.find("-->", start + 4)
            at = len(source) if end < 0 else end + 3
            continue
        if source.startswith("<![CDATA[", start):
            end = source.find("]]>", start + 9)
            at = len(source) if end < 0 else end + 3
            continue
        if source.startswith("<?", start):
            end = source.find("?>", start + 2)
            at = len(source) if end < 0 else end + 2
            continue
        if source.startswith(("</", "<!"), start):
            end = source.find(">", start + 2)
            at = len(source) if end < 0 else end + 1
            continue
        quote = None
        end = start + 1
        while end < len(source):
            char = source[end]
            if quote:
                if char == quote:
                    quote = None
            elif char in "\"'":
                quote = char
            elif char == ">":
                break
            end += 1
        tag_source = source[start:end + 1]
        for match in re.finditer(
                r"\s+[A-Za-z_:][\w.:-]*\s*=\s*(?P<quote>['\"])(?P<value>.*?)(?P=quote)",
                tag_source, re.S):
            yield match.group("value")
        at = end + 1


def modern_svg_findings(root, source: str | None = None) -> list[tuple[str, str]]:
    """Close the input before walk() reads any presentation attributes or text."""
    if source is not None and any("&" in value for value in serialized_attribute_values(source)):
        return [("S24", "unsupported character reference in a serialized attribute value")]
    # Bound the tree iteratively before any recursive helper sees it.
    pending = [(root, 0)]
    while pending:
        el, depth = pending.pop()
        if depth > MODERN_MAX_DEPTH:
            return [("S24", f"modern figure nesting exceeds {MODERN_MAX_DEPTH} levels "
                      "below <svg>")]
        pending.extend((child, depth + 1) for child in el)
    found = []
    for el in root.iter():
        t = tag(el)
        if (el.tag != SVG + t or t not in MODERN_ELEMENTS
                or (el is root) != (t == "svg")):
            rule = "S25" if t == "tspan" else "S24"
            found.append((rule, f"unsupported <{t}> in a modern figure"))
        if t == "text":
            for child in el:
                found.append(("S24", f"unsupported <{tag(child)}> child of <text>: "
                              "use plain text"))
        for key, value in el.attrib.items():
            valid = False
            if t == "marker":
                valid = value in MODERN_MARKER_VALUES.get(key, set())
            elif key in MODERN_NUMBERS:
                valid = modern_number(value) is not None
            elif key in MODERN_VALUES:
                valid = value in MODERN_VALUES[key]
            elif key == "transform":
                valid = modern_transform(value)
            elif key == "d":
                valid = modern_path(value)
            elif key == "points":
                pairs = [pair.split(",") for pair in value.split(" ")]
                valid = all(len(pair) == 2 and all(modern_number(n) is not None for n in pair)
                            for pair in pairs)
            elif key in {"viewBox", "stroke-dasharray"}:
                values = modern_numbers(value)
                valid = (values is not None and (len(values) == 4 if key == "viewBox"
                                                 else all(n >= 0 for n in values)))
            if not valid:
                rule = "S25" if key in {"font-size", "font-style"} else "S24"
                what = "malformed or unsupported" if key in MODERN_ATTRIBUTES else "unsupported"
                found.append((rule, f"{what} {key} {value!r} on <{t}>"))
    if found:
        return found
    # Read inheritance only after the syntax gate has excluded CSS. Include ancestors
    # outside the marker: a stroke on <defs> or the root still reaches its shapes.
    in_markers = {child for marker in root.iter(SVG + "marker") for child in marker.iter()}
    for el, _, eff in walk(root):
        if el not in in_markers:
            continue
        t = tag(el)
        if t == "text":
            found.append(("S24", "unsupported <text> inside <marker>"))
        elif t in DRAWN and eff.get("stroke", "none") != "none":
            found.append(("S24", f"unsupported stroke on <{t}> inside <marker>"))
    return found


def modern_findings(root, ref: str, heaths: set[str] | None,
                    names: set[str] | None) -> list[tuple[str, str]]:
    """(rule, message) for each fault of a modern figure (S24, S25), given the letters its
    Euclid's figure draws (None: no Euclid's figure) and the names its page's modern way
    uses (None: no such paragraph)."""
    found = modern_svg_findings(root)
    if found:
        return found
    for dimension in ("width", "height"):
        value = root.get(dimension)
        if value is not None and modern_number(value) <= 0:
            found.append(("S24", f"root {dimension} {value!r}, not positive"))
    vb = root.get("viewBox", "").split(" ")
    values = [modern_number(value) for value in vb]
    width = values[2] if len(values) == 4 else None
    if len(values) != 4 or None in values:
        found.append(("S24", f"malformed viewBox {root.get('viewBox')!r}: "
                      "expected four finite SVG numbers"))
    else:
        if not 400 <= width <= 440:
            found.append(("S24", f"viewBox width {width}, not 400 to 440, as Euclid's figure"))
        if values[3] <= 0:
            found.append(("S24", f"viewBox height {values[3]}, not positive"))
    titles = list(root.iter(f"{SVG}title"))
    direct_titles = root.findall(f"{SVG}title")
    title = direct_titles[0] if len(titles) == len(direct_titles) == 1 else None
    if len(titles) != 1 or len(direct_titles) != 1:
        found.append(("S24", f"{len(titles)} <title> elements, not exactly one directly "
                      "under <svg>"))
    elif " ".join(modern_text_of(title).split()) != f"{ref}: the modern way":
        got = f"title \"{modern_text_of(title)}\""
        found.append(("S24", f"{got}, not \"{ref}: the modern way\""))
    if root.find(f".//{SVG}desc") is not None:
        found.append(("S24", "a caption (<desc>): the modern-way paragraph serves as its caption"))
    if heaths is None:
        found.append(("S24", "no Euclid's figure to take the letters from"))
    if names is None:
        found.append(("S24", "the page's mishnah has no paragraph opening "
                      f"{MODERN_WAY} for the figure to stand under"))
    bad = defaultdict(int)
    for el, own, eff in walk(root):
        t = tag(el)
        for k in COLOUR_ATTRS:
            v = own.get(k)
            if v is not None and v.lower() != "none" and v.lower() not in EUCLID_COLOURS:
                bad[f"{k}={v}"] += 1
        if (t in FILLED or t == "text") and eff.get("fill") is None:
            found.append(("S24", f"a <{t}> with no fill, which SVG paints black: give it "
                          "a colour of the palette, or fill=\"none\""))
        if (t in DRAWN or t == "text") and (eff.get("stroke") or "none").lower() != "none":
            raw_width = eff.get("stroke-width")
            w = 1.0 if raw_width is None else modern_number(raw_width)
            if w is None:
                found.append(("S24", f"malformed stroke-width {raw_width!r} on a <{t}>"))
            elif not 1.2 <= w <= 3.2:
                found.append(("S24", f"stroke-width {w:g} on a <{t}>, not 1.2 to 3.2"))
        if t != "text":
            continue
        raw = "".join(el.itertext())
        odd = "".join(sorted({c for c in raw if c not in " \t\r\n"
                             and not ("A" <= c <= "Z")
                             and not MODERN_TEXT.fullmatch(c.translate(GREEK_VARIANTS))}))
        if odd:
            found.append(("S25", f"<text>{raw}</text> holds {odd!r}: a modern figure's text is "
                          "Heath's letters, or the modern way's names, numbers and signs"))
            continue
        s = re.sub(r"[ \t\r\n]+", " ", raw).strip(" ").translate(GREEK_VARIANTS)
        if not s:
            continue
        if eff.get("font-family") not in MODERN_VALUES["font-family"]:
            found.append(("S25", f"<text>{s}</text> has no allowed effective font-family: "
                          "declare Georgia on the text or an ancestor"))
        if modern_number(eff.get("font-size")) != MODERN_TEXT_SIZE:
            found.append(("S25", f"<text>{s}</text> at font-size {eff.get('font-size')}, "
                          f"not {MODERN_TEXT_SIZE}"))
        style = letter_style(eff)
        if LETTER.fullmatch(s):
            if heaths is not None and s not in heaths:
                found.append(("S25", f"letter {s} is not one Euclid's figure draws "
                              f"({', '.join(sorted(heaths))})"))
            if style != "normal":
                found.append(("S25", f"letter {s} in font-style {style}: Heath's letters are "
                              "upright (STYLE, section 4)"))
            continue
        if re.search(r"[A-Z]", s):
            found.append(("S25", f"<text>{s}</text>: a capital stands alone, as one of Heath's "
                          "letters; a length or a vector takes the modern way's own name"))
            continue
        if not MODERN_TEXT.fullmatch(s):
            odd = "".join(sorted({c for c in s if not MODERN_TEXT.fullmatch(c)}))
            found.append(("S25", f"<text>{s}</text> holds {odd!r}: a modern figure's text is "
                          "Heath's letters, or the modern way's names, numbers and signs"))
            continue
        letters = sorted({c for c in s if c.isalpha()})
        if not letters:
            continue
        if style != "italic":
            found.append(("S25", f"<text>{s}</text> in font-style {style}: the modern way's "
                          "names are italic, as its mathematics sets them"))
        unknown = [c for c in letters if names is not None and c not in names]
        if unknown:
            found.append(("S25", f"<text>{s}</text>: {', '.join(unknown)} is no name of the "
                          "page's modern way"))
    for what, k in sorted(bad.items()):
        found.append(("S24", f"colour {what} ({k}×) is not in Euclid's figure's palette"))
    return found


def check_modern(path: Path, ref: str) -> None:
    """S24 and S25 for one figure of the modern way."""
    data = path.read_bytes()
    try:
        source = data.decode("utf-8")
    except UnicodeDecodeError as e:
        fail("S24", path, 0, f"unsupported SVG encoding: {e}")
        return
    if "\0" in source:
        fail("S24", path, 0, "unsupported SVG encoding: expected UTF-8")
        return
    if re.search(r"<!\s*(?:DOCTYPE|ENTITY)\b", source, re.I):
        fail("S24", path, 0, "unsupported DTD or entity declaration in a modern figure")
        return
    root = svg_root(path, data)
    if root is None:
        return
    refused = modern_svg_findings(root, source)
    for rule, message in refused:
        fail(rule, path, 0, message)
    if refused:
        return
    # ElementTree drops processing instructions, including those before the root.
    for pattern, what in ((r"<\?xml-stylesheet\b", "stylesheet reference"),
                          (r"@import\b", "@import")):
        if re.search(pattern, source, re.I):
            fail("S24", path, 0, f"unsupported {what} in a modern figure")
            return
    book, n = ref.split(".")
    heaths = modern_drawn_letters(path.with_name(f"{int(n):02d}.svg"))
    mishnah = ROOT / "mishnah" / book / f"{int(n):02d}.md"
    raw = mishnah.read_text(encoding="utf-8") if mishnah.exists() else ""
    markup = modern_markup_findings(raw)
    for message in markup:
        fail("S25", path, 0, f"mishnah/{book}/{int(n):02d}.md: {message}")
    # Refused markup supplies no names, and is not a claim that the paragraph is absent.
    para = modern_paragraph(raw) if not markup else None
    names = set() if markup else modern_names(para) if para is not None else None
    title = root.find(f"{SVG}title")
    if title is not None:
        caption_text_rules(path, title, "title")
    for rule, message in modern_findings(root, ref, heaths, names):
        fail(rule, path, 0, message)


def check_figures(required: bool) -> None:
    for book in books_with_pages():
        d = ROOT / "figures" / book
        waiting = []
        for path in numbered(d, "-idea.svg"):
            left = check_idea(path, ref_of(path), required)
            if left:
                waiting.append(f"{path.name[:2]} ({left})")
        for path in numbered(d, ".svg"):
            check_euclid(path, ref_of(path))
        for path in numbered(d, MODERN_SUFFIX):
            check_modern(path, ref_of(path))
        if waiting:
            report("D14", d, 0, f"{len(waiting)} without letters, with the points each "
                   f"has to letter: {', '.join(waiting)}")
        for kind, names in sorted(italic_figures[book].items()):
            report("D15", d, 0, f"{len(names)} {kind} with italic letters: " + ", ".join(names))


# ---------------------------------------------------------------------------------------

def reach_done(no_lean: bool = False) -> list[tuple[str, list[str], bool]]:
    """The entries of REACH_PENDING with a rule whose file has no finding of it left,
    each as (the file, those rules, whether they are all its rules), for D16 to report as
    done. S12 alone asks Lean: under `no_lean`, or when Lean could not be asked of every
    name (`lean_short`), it found nothing it could have found, so it is never done."""
    unasked = no_lean or bool(lean_short)
    done = []
    for f, (pending, _) in sorted(REACH_PENDING.items()):
        rules = pending.split()
        left = [r for r in rules if (f, r) not in reach_found and not (unasked and r == "S12")]
        if left:
            done.append((f, left, len(left) == len(rules)))
    return done


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--no-lean", action="store_true",
                        help="skip S12, which needs a built tree")
    parser.add_argument("--quiet", action="store_true",
                        help="give the reports as counts, without each finding")
    parser.add_argument("--require-idea-letters", action="store_true",
                        help="hold every idea figure to S21, as IDEA_LETTERS_REQUIRED = True "
                             "does; it is on, so this changes nothing unless it is turned off")
    args = parser.parse_args()
    required = IDEA_LETTERS_REQUIRED or args.require_idea_letters

    check_conflict_markers()
    named: list[NamedText] = []   # the texts S12 reads
    for path in mishnah_files():
        raw = path.read_text(encoding="utf-8")
        check_text(path, raw, {"prose"})
        check_mishnah(path, raw)
        named.append(NamedText(path, raw, book_opens(path.parent.name), held=True))
    for path in intro_files():
        raw = path.read_text(encoding="utf-8")
        check_text(path, raw, {"prose"})
        named.append(NamedText(path, raw, book_opens(path.stem) if path.stem in heath.ROMAN
                               else every_book_opens()))
    allowed = reading_links()
    for path in reading_files():
        raw = path.read_text(encoding="utf-8")
        check_text(path, raw, {"prose"})
        check_reading(path, raw, allowed)
        named.append(NamedText(path, raw, book_opens(path.parent.name)))
    terms = ROOT / "review" / "terms.toml"
    for path in review_files() + ([terms] if terms.exists() else []):
        is_terms = path == terms
        for note in review_texts(path.read_text(encoding="utf-8"), terms=is_terms):
            check_text(path, note.text, {"review"}, line_at=note.line_at, new=True)
            named.append(NamedText(path, note.text, every_book_opens() if is_terms
                                   else book_opens(path.parent.name), line_at=note.line_at,
                                   hypothesis=note.key == "statement.hypotheses"))
    for path in catalogue_files():
        raw = path.read_text(encoding="utf-8")
        book = re.fullmatch(r"gaps-book-(\w+)\.md", path.name)
        check_text(path, raw, {"catalogue"}, new=book is None)
        named.append(NamedText(path, raw, book_opens(book.group(1))
                               if book and book.group(1) in heath.ROMAN else every_book_opens()))
    for path in report_files():   # dated: S12 does not read them
        check_text(path, path.read_text(encoding="utf-8"), {"report"}, new=True)
    check_text(ROOT / "README.md", readme_text(), {"readme"})
    shown_docs = rendered_docstrings()
    for path in lean_files():
        named += check_lean_notes(path, path.read_text(encoding="utf-8"),
                                  shown_docs.get(rel(path), []))
    for path in generated_files():
        check_text(path, path.read_text(encoding="utf-8"), {"generated"},
                   new=is_new_generated(path))
    for path in front_files():
        named.append(NamedText(path, path.read_text(encoding="utf-8"),
                               book_opens(path.parent.name)))
    check_intros()
    check_figures(required)
    if "D14" in reports:
        print("note: S21 holds only the idea figures that carry a letter, until "
              "IDEA_LETTERS_REQUIRED is set (STYLE, section 8); D14 lists the rest")
    if "D15" in reports:
        print("note: S15 and S20 take italic letters, one style in each figure, until "
              "UPRIGHT_LETTERS_REQUIRED is set (STYLE, section 8); D15 lists the figures")
    if args.no_lean:
        print("note: S12 skipped (--no-lean); the Lean names of the texts it reads were not "
              "checked")
    elif shutil.which("lake") is None:
        lean_short.append("`lake` is not on the PATH")
        fail("S12", SCRIPT, 0, "`lake` is not on the PATH; build the tree, or pass --no-lean")
    else:
        names, unchecked = check_lean_names(named)
        print(f"S12: {names} backticked names put to Lean, from {len({t.path for t in named})} "
              "files: the prose, the review notes, the catalogues, the rendered "
              "docstrings and the front pages")
        if unchecked:
            print(f"note: S12 left {len(unchecked)} audit lemma(s) unchecked, for the Audit "
                  "library is not built (`lake build Audit`, as CI runs it): "
                  + ", ".join(f"`{n}`" for n in unchecked))
    done = {f: (rules, whole) for f, rules, whole in reach_done(args.no_lean)}
    for f, (pending, who) in sorted(REACH_PENDING.items()):
        rules, whole = done.get(f, ([], False))
        if not (ROOT / f).exists():
            report("D16", ROOT / f, 0, f"done: listed in REACH_PENDING ({who}), but there is "
                   "no such file now; take it out")
        elif whole:
            report("D16", ROOT / f, 0, f"done: no finding of {pending} is left ({who}); take "
                   "it out of REACH_PENDING")
        elif rules:
            report("D16", ROOT / f, 0, f"done: no finding of {' '.join(rules)} is left ({who}); "
                   f"take {'it' if len(rules) == 1 else 'them'} out of its entry in "
                   f"REACH_PENDING, \"{pending}\"")

    if not args.quiet:
        print("Exceptions the script allows, each with its reason:")
        for (book, n), exc in sorted(LETTER_EXCEPTIONS.items(), key=lambda x: heath.prop_key(f"{x[0][0]}.{x[0][1]}")):
            letters = sorted(exc.get("extra", set()) | exc.get("missing", set()))
            print(f"  S16 figures/{book}/{n:02d}.svg ({', '.join(letters)}): {exc['why']}")
        for word, why in sorted(NOT_DECLARED.items()):
            print(f"  S12 `{word}`: {why}")
        for (f, why), (elements, points) in sorted(idea_exemptions.items()):
            print(f"  S21 {f} ({elements} marked {UNLETTERED}, {points} point(s)): {why}")
    if reports:
        total = sum(len(v) for v in reports.values())
        print(f"Reported for a reader to judge ({total}; these fail nothing):")
        for rule in sorted(reports, key=lambda r: int(r[1:])):
            hits = reports[rule]
            print(f"  {rule} {REPORTS[rule]}: {len(hits)}")
            if not args.quiet:
                for f, line, msg in hits:
                    print(f"      {f}{':' + str(line) if line else ''}: {msg}")
    if failures:
        print(f"\n{len(failures)} style failure(s) (docs/STYLE.md, section 8):")
        for rule, f, line, msg in sorted(failures, key=lambda x: (int(x[0][1:]), x[1], x[2])):
            print(f"  ✗ {rule} {f}{':' + str(line) if line else ''}: {msg}")
        by_rule = defaultdict(int)
        for rule, *_ in failures:
            by_rule[rule] += 1
        print("  by rule: " + ", ".join(f"{r} {RULES[r]} ({k})"
                                       for r, k in sorted(by_rule.items(), key=lambda x: int(x[0][1:]))))
        return 1
    rules = "S1–S26" if not args.no_lean else "S1–S11 and S13–S26"
    print(f"\n✓ style: the hard rules hold ({rules})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
