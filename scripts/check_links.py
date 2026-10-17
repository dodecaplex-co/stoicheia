"""Check the links in the repository's Markdown files.

Every relative link must reach a file or folder of the repository, and every `#anchor`
must name a place in what it points to:

* in a Markdown file, a heading, by the slug GitHub gives it ("## Euclid's proof" is
  `#euclids-proof`, and a second heading of the same name `#euclids-proof-1`), or an
  `<a name="…">` or `id="…"` in its HTML;
* in any other file, lines it has: `#L12` or `#L12-L20`, as GitHub numbers them.

Links are read from inline links and images, `[text](target)`, reference definitions,
`[label]: target`, and the `href` and `src` of HTML tags. Fenced code, inline code and
HTML comments are skipped, and so are web addresses (anything with a scheme, as
`https:`) and mail.

The pieces render.py pastes into a page are checked where they are read:
`mishnah/<book>/NN.md` and `reading/<book>/NN.md` from `book/<book>/NN.md`, and
`mishnah/intro/<book>.md` from `book/<book>/index.md`. A link there resolves from the
page's folder, and a bare `#anchor` names a place on the page.

    python3 scripts/check_links.py            every .md file git knows of (or, outside
                                              git, every one under the repository)
    python3 scripts/check_links.py FILE ...   just these

Exits 1 if any link is broken, printing each as `file:line: target: what is wrong`.
Standard library only.
"""

from __future__ import annotations

import html
import os
import re
import subprocess
import sys
import unicodedata
from functools import lru_cache
from pathlib import Path
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parent.parent

# Folders never searched when git cannot list the files.
SKIP_DIRS = {".git", ".lake", ".claude", "__pycache__", "node_modules"}

# A piece of a page, and the page it is read on: (pattern, page), the page written with
# the pattern's groups.
FRAGMENTS = [
    (re.compile(r"mishnah/intro/([IVX]+)\.md"), "book/{0}/index.md"),
    (re.compile(r"mishnah/([IVX]+)/(\d+)\.md"), "book/{0}/{1}.md"),
    (re.compile(r"reading/([IVX]+)/(\d+)\.md"), "book/{0}/{1}.md"),
]

SCHEME = re.compile(r"^[A-Za-z][A-Za-z0-9+.-]*:")
LINE_ANCHOR = re.compile(r"L(\d+)(?:C\d+)?(?:-L(\d+)(?:C\d+)?)?")
FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})")
ATX = re.compile(r"^ {0,3}(#{1,6})(?:[ \t]+(.*?))?(?:[ \t]+#+)?[ \t]*$")
SETEXT = re.compile(r"^ {0,3}(=+|-+)[ \t]*$")
COMMENT = re.compile(r"<!--.*?-->", re.S)
# Link text: brackets may nest one deep, as in "[`[I. 4]`](…)"; "\[" is no bracket.
LINK_TEXT = re.compile(r"(?<!\\)\[(?:[^\[\]\\]|\\.|\[(?:[^\[\]\\]|\\.)*\])*\]\(")
REF_DEF = re.compile(r"^ {0,3}\[((?:[^\[\]\\]|\\.)+)\]:[ \t]*(<[^>]*>|\S+)")
HTML_URL = re.compile(r"<[A-Za-z][^>]*?\b(?:href|src)\s*=\s*(\"[^\"]*\"|'[^']*')", re.S)
HTML_ANCHOR = re.compile(r"<[A-Za-z][^>]*?\b(?:name|id)\s*=\s*(\"[^\"]*\"|'[^']*')", re.S)


def markdown_files() -> list[Path]:
    """Every .md file of the repository: tracked or new, but not ignored, as git lists
    them; without git, every one under ROOT outside SKIP_DIRS."""
    try:
        out = subprocess.run(["git", "ls-files", "-co", "--exclude-standard", "-z", "--", "*.md"],
                             cwd=ROOT, capture_output=True, check=True).stdout.decode()
        return sorted({ROOT / f for f in out.split("\0") if f and (ROOT / f).is_file()})
    except (OSError, subprocess.CalledProcessError):
        found = []
        for d, dirs, files in os.walk(ROOT):
            dirs[:] = [x for x in dirs if x not in SKIP_DIRS]
            found += [Path(d) / f for f in files if f.endswith(".md")]
        return sorted(found)


def rel(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return str(path)


def read_on(path: Path) -> Path:
    """The page a file is read on: for a piece render.py pastes into a page, that page;
    for any other file, the file itself."""
    name = rel(path)
    for pattern, page in FRAGMENTS:
        m = pattern.fullmatch(name)
        if m:
            return ROOT / page.format(*m.groups())
    return path


def blank_code(text: str) -> list[str]:
    """The file's lines with fenced code blocks and HTML comments blanked, so that the
    numbering stays and nothing in them is read as a link or a heading."""
    text = COMMENT.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), text)
    lines = text.split("\n")
    fence = None
    for i, line in enumerate(lines):
        m = FENCE.match(line)
        if fence:
            if m and m.group(1)[0] == fence[0] and len(m.group(1)) >= len(fence) \
                    and not line.strip()[len(m.group(1)):].strip():
                fence = None
            lines[i] = ""
        elif m:
            fence = m.group(1)
            lines[i] = ""
    return lines


def blank_spans(line: str) -> str:
    """A line with its inline code spans blanked: `` `[x](y)` `` is code, not a link."""
    out, i = [], 0
    while i < len(line):
        if line[i] == "`":
            run = len(line[i:]) - len(line[i:].lstrip("`"))
            close = line.find("`" * run, i + run)
            # The closing run must be exactly as long as the opening one.
            while close >= 0 and line[close + run:close + run + 1] == "`":
                close = line.find("`" * run, close + run + 1)
            if close >= 0:
                out.append(" " * (close + run - i))
                i = close + run
                continue
            out.append(line[i:i + run])
            i += run
            continue
        out.append(line[i])
        i += 1
    return "".join(out)


def destination(line: str, start: int) -> str | None:
    """The target of an inline link whose "(" ends just before `start`: "<…>" or a run
    without spaces whose parentheses balance, before an optional title and the ")"."""
    rest = line[start:].lstrip()
    if rest.startswith("<"):
        end = rest.find(">")
        return rest[1:end] if end > 0 else None
    depth, out = 0, []
    for ch in rest:
        if ch == "(":
            depth += 1
        elif ch == ")":
            if depth == 0:
                break
            depth -= 1
        elif ch.isspace():
            break
        out.append(ch)
    return "".join(out)


def links(path: Path):
    """(line number, target) for every link in a Markdown file."""
    for number, line in enumerate(blank_code(path.read_text()), 1):
        m = REF_DEF.match(line)
        if m:
            yield number, m.group(2).strip("<>")
            continue
        spans = blank_spans(line)
        for m in LINK_TEXT.finditer(spans):
            target = destination(line, m.end())
            if target is not None:
                yield number, target
        for m in HTML_URL.finditer(spans):
            yield number, html.unescape(m.group(1)[1:-1])


def heading_text(raw: str) -> str:
    """A heading's text as GitHub renders it: links and images give their text, code
    its contents, and tags, emphasis and escapes vanish."""
    s = re.sub(r"!?\[((?:[^\[\]]|\[[^\[\]]*\])*)\]\([^)]*\)", r"\1", raw)
    s = re.sub(r"!?\[((?:[^\[\]]|\[[^\[\]]*\])*)\]\[[^\]]*\]", r"\1", s)
    s = re.sub(r"(`+)(.*?)\1", r"\2", s)
    s = re.sub(r"<[^>]+>", "", s)
    s = re.sub(r"\\([!-/:-@\[-`{-~])", r"\1", s)
    s = s.replace("*", "")
    s = re.sub(r"(?<!\w)_+|_+(?!\w)", "", s)
    return html.unescape(s).strip()


def slug(text: str) -> str:
    """GitHub's slug of a heading's text: lower case; letters, marks, digits, "_", "-"
    and spaces kept, everything else dropped; each space a "-"."""
    kept = [ch for ch in text.lower() if ch in " -" or unicodedata.category(ch)[0] in "LM"
            or unicodedata.category(ch) in ("Nd", "Pc")]
    return "".join(kept).replace(" ", "-")


@lru_cache(maxsize=None)
def anchors(path: Path) -> frozenset:
    """Every #anchor a Markdown file has: its headings' slugs, numbered as GitHub numbers
    a repeated one, and the name and id of its HTML tags."""
    lines = blank_code(path.read_text())
    found, seen = set(), {}

    def add(raw):
        base = slug(heading_text(raw))
        count = seen.get(base, 0)
        found.add(base if count == 0 else f"{base}-{count}")
        seen[base] = count + 1

    previous = ""
    for line in lines:
        m = ATX.match(line)
        if m:
            add(m.group(2) or "")
        elif SETEXT.match(line) and previous.strip() and not re.match(
                r"^ {0,3}([#|>*+-]|\d+[.)]|<)", previous) and not SETEXT.match(previous):
            add(previous.strip())
        for m in HTML_ANCHOR.finditer(blank_spans(line)):
            found.add(html.unescape(m.group(1)[1:-1]))
        previous = line
    return frozenset(found)


@lru_cache(maxsize=None)
def line_count(path: Path) -> int:
    data = path.read_bytes()
    return data.count(b"\n") + (0 if data.endswith(b"\n") or not data else 1)


def check_anchor(target: Path, anchor: str) -> str | None:
    """What is wrong with `#anchor` in the file or folder `target`, or None."""
    if target.is_dir():
        readme = target / "README.md"
        if not readme.is_file():
            return f"#{anchor}: {rel(target)}/ is a folder with no README.md to hold it"
        target = readme
    if target.suffix == ".md":
        names = anchors(target)
        if anchor in names:
            return None
        near = [n for n in names if n.lower() == anchor.lower()]
        hint = f" (did you mean #{near[0]}?)" if near else ""
        return f"no heading or anchor #{anchor} in {rel(target)}{hint}"
    m = LINE_ANCHOR.fullmatch(anchor)
    if not m:
        return f"#{anchor}: in {rel(target)}, which is not Markdown, an anchor is a line, #L12"
    lines = line_count(target)
    first, last = int(m.group(1)), int(m.group(2) or m.group(1))
    if first > last:
        return f"#{anchor}: the lines run backwards"
    if not 1 <= first <= last <= lines:
        return f"#{anchor}: {rel(target)} has {lines} lines"
    return None


@lru_cache(maxsize=None)
def listing(folder: Path) -> frozenset:
    return frozenset(os.listdir(folder))


def spelled_as(where: Path) -> str | None:
    """Where a path that exists differs in case from the names on disk, as it may on a
    Mac but not on GitHub: the first name spelled otherwise, or None."""
    here = ROOT
    for part in where.relative_to(ROOT).parts:
        if part not in listing(here):
            return part
        here = here / part
    return None


def relative(target: str) -> bool:
    """Is this link ours to check? Not a web address, mail or other scheme, and not empty."""
    target = target.strip()
    return bool(target) and not SCHEME.match(target) and not target.startswith("//")


def check_link(source: Path, target: str) -> str | None:
    """What is wrong with one relative link of the file `source`, or None if it is sound."""
    path, _, anchor = target.strip().partition("#")
    path = unquote(path.split("?", 1)[0])
    anchor = unquote(anchor)
    page = read_on(source)
    if not path:
        where = page
    elif path.startswith("/"):
        where = ROOT / path.lstrip("/")
    else:
        where = page.parent / path
    where = Path(os.path.normpath(where))
    if where != ROOT and ROOT not in where.parents:
        return "leads outside the repository"
    if not where.exists():
        return f"no such file: {rel(where)}" + (
            f" (from {rel(page)}, where {rel(source)} is read)" if page != source else "")
    wrong = spelled_as(where)
    if wrong:
        return f"{rel(where)}: {wrong!r} is spelled otherwise on disk, and GitHub minds the case"
    if anchor:
        return check_anchor(where, anchor)
    return None


def main(argv: list[str]) -> int:
    files = [Path(a).resolve() for a in argv] if argv else markdown_files()
    checked = broken = 0
    for path in files:
        for number, target in links(path):
            if not relative(target):
                continue
            checked += 1
            problem = check_link(path, target)
            if problem:
                broken += 1
                print(f"{rel(path)}:{number}: {target}: {problem}")
    if broken:
        print(f"✗ {broken} of {checked} links in {len(files)} Markdown files are broken")
        return 1
    print(f"✓ links: all {checked} relative links and anchors in {len(files)} Markdown files resolve")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
