"""Exact counts for inline prose, shared by render.py and check_fidelity.py.

Syntax: <!-- count:vocabulary -->91<!-- /count -->. Append :word or :Word to
spell a number in lower case or with its first letter capitalised. Only the value
belongs to the generator. Literal examples must escape '<', even in code spans.

Git must resolve the supplied root as its work tree. Only tracked Markdown and
review records are scanned. A tracked Markdown file absent from the work tree (lstat
finds nothing there) is noted and passed over under the check inputs, and refused
anywhere else (absent_tracked); any other error reading it is refused. Symlinks, paths
through a symlink and paths resolving outside the root are refused; a symlink is
never absent. Whole renderer outputs are scanned but may not contain markers. The
decisions log and reports are history, except the living gap and overlap catalogues;
markers there are refused. Markers are also refused when they overlap README scope
regions or PROGRAM's status region, which the renderer replaces. Counts use files
alone, never a Lean run or build outputs. Run this module to print every available
count and its current value.
"""

import ast
from dataclasses import dataclass
from functools import partial
import os
from pathlib import Path
import re
import subprocess
import tomllib

import heath


def repository_path(root, path):
    """Check a path before reading or writing, refusing symlinks and escapes."""
    root = Path(os.path.abspath(root))
    resolved_root = root.resolve()
    supplied = Path(path)
    path = Path(os.path.abspath(supplied if supplied.is_absolute() else root / supplied))
    if path.is_relative_to(root):
        relative = path.relative_to(root)
        boundary = root
    elif root != resolved_root and path.is_relative_to(resolved_root):
        relative = path.relative_to(resolved_root)
        boundary = resolved_root
    else:
        raise ValueError(f"{path}: path is outside repository root {root}")
    component = boundary
    for part in relative.parts:
        component /= part
        if component.is_symlink():
            name = component.relative_to(boundary)
            raise ValueError(f"{name}: symlink is forbidden")
    if not path.resolve().is_relative_to(resolved_root):
        raise ValueError(f"{path}: resolved path is outside repository root {root}")
    return path


def tracked_files(root, pattern):
    """Read Git's index only when its resolved work tree is the supplied root."""
    try:
        top = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=root,
                             capture_output=True, check=True)
    except (subprocess.CalledProcessError, OSError) as error:
        raise ValueError(f"{root}: cannot resolve Git work tree; "
                         "a checkout or explicit GIT_DIR and GIT_WORK_TREE is required") from error
    resolved = Path(top.stdout.decode().removesuffix("\n")).resolve()
    if resolved != root.resolve():
        raise ValueError(f"{root}: Git work tree {resolved} does not match "
                         f"repository root {root.resolve()}")
    try:
        result = subprocess.run(["git", "ls-files", "-z", "--", pattern], cwd=root,
                                capture_output=True, check=True)
    except (subprocess.CalledProcessError, OSError) as error:
        raise ValueError(f"{root}: cannot list tracked files with Git") from error
    return [Path(name.decode()) for name in result.stdout.split(b"\0") if name]


def shown(name):
    """A path as a note or a fault names it: written as repr writes a string, so that a
    backslash or any character that is not printable, a control character among them, is
    escaped, and no name can forge a line of the terminal."""
    return repr(name)


def absent_tracked(root, paths):
    """The tracked `paths` absent from the work tree, and a fault for each one outside
    the check inputs.

    The pre-flight's pass with origin/main's checks (scripts/safe_push.py: steps 3 and 4
    run check_fidelity.py and render.py in it, and step 4 the negative suite) takes the
    files a commit adds under the check inputs out of the work tree, while Git's index
    still lists them: each of those is noted on stdout, for the caller to pass over. The
    pre-flight takes nothing else out, so any other is a fault, for the caller to fail on.
    A path is absent only when lstat raises FileNotFoundError; any other OSError, as for
    a path in a directory of mode 000, is raised to the caller, which fails on it. A
    path that is or passes through a symlink is not absent, and its readers treat it as
    before: updates refuses it (repository_path); the negative suite's marker copy skips
    a symlink and follows a symlinked directory, and its source copy follows both. Each
    name is printed escaped (shown). Returns the absent paths, as given, and the faults.
    """
    absent = []
    for rel in paths:
        try:
            path = repository_path(root, rel)
        except ValueError:
            continue
        try:
            path.lstat()
        except FileNotFoundError:
            absent.append(rel)
    if not absent:
        return [], []
    # The check inputs are listed once, in the harness. It is imported only when a tracked
    # file is absent, so an ordinary run of a check never loads it.
    from safe_push import CHECK_INPUTS, under

    faults = []
    for rel in absent:
        name = Path(rel).as_posix()
        if under(name, CHECK_INPUTS):
            print("note: tracked but absent from the work tree (under the check inputs, as a "
                  "file the commit adds is in the pre-flight's pass with origin/main's "
                  f"checks): {shown(name)}")
        else:
            faults.append("tracked but absent from the work tree, outside the check "
                          f"inputs: {shown(name)}")
    return absent, faults


def lock_table(root, table):
    """Read one of the lock's two tables, requiring the lock's declared shape."""
    path = repository_path(root, "Certificate/axioms.lock")
    data = tomllib.loads(path.read_text())
    if set(data) != {"axioms", "vocabulary"} or not all(
            isinstance(t, dict) and all(isinstance(v, str) for v in t.values())
            for t in data.values()):
        raise ValueError("Certificate/axioms.lock: expected axioms and vocabulary tables of strings")
    return data[table]


def axiom_groups(entry):
    """The renderer's classification by name: postulates, definitions, tacit, other."""
    axioms = entry["axioms"]
    posts = [a for a in axioms if a.startswith("Postulate")]
    defs = [a for a in axioms if a.startswith("Definition")]
    tacit = [a for a in axioms if a.startswith("Tacit.")]
    other = [a for a in axioms if a not in posts + defs + tacit]
    return posts, defs, tacit, other


def axioms(root):
    """Count entries in Certificate/axioms.lock's [axioms] table."""
    return len(lock_table(root, "axioms"))


def tacit_rules(root):
    """Count locked axioms classified as tacit rules by the renderer."""
    return len(axiom_groups({"axioms": lock_table(root, "axioms")})[2])


def postulates(root):
    """Count locked axioms classified as postulates by the renderer."""
    return len(axiom_groups({"axioms": lock_table(root, "axioms")})[0])


def axioms_but_postulate_5(root):
    """Count locked axioms other than Postulate5, as in "the other 86" beside the
    parallel postulate."""
    return len(set(lock_table(root, "axioms")) - {"Postulate5"})


def vocabulary(root):
    """Count entries in Certificate/axioms.lock's [vocabulary] table."""
    return len(lock_table(root, "vocabulary"))


def companion_entries(root):
    """Read the literal companions list; refuse syntax this reader cannot count exactly."""
    # Reuse the source scanner, including nested comments and strings. Import locally
    # because check_fidelity imports this module too; neither import runs a check.
    from check_fidelity import read_lean

    path = repository_path(root, "Elements/Companions.lean")
    source = path.read_text()
    code, unsure = read_lean(source)
    start = re.search(r"\bdef\s+Elements\.companions\s*:\s*"
                      r"List\s*\(\s*Lean\.Name\s*×\s*String\s*\)\s*:=\s*\[", code)
    if unsure or start is None:
        raise ValueError("Elements/Companions.lean: cannot read the literal companions list")
    end = code.find("]", start.end())
    if end < 0:
        raise ValueError("Elements/Companions.lean: unclosed companions list")
    if code[end + 1:].strip():
        raise ValueError("Elements/Companions.lean: unsupported code after companions list")
    body = source[start.end():end]
    blank = code[start.end():end]
    entry = re.compile(r'\(\s*``Elements\.Book([IVX]+)\.Prop([1-9][0-9]*)'
                       r'\.([A-Za-z_][A-Za-z_0-9.]*)\s*,\s*"([^"\n]*)"\s*\)')
    entries = []
    cursor = 0
    while blank[cursor:].strip():
        gap = re.match(r"\s*", blank[cursor:]).end()
        cursor += gap
        # Locate tokens in the blanked code, then read the reference from the source.
        match = entry.match(blank, cursor)
        if match is None:
            raise ValueError("Elements/Companions.lean: unsupported companion entry")
        stop = match.end()
        raw = body[cursor:stop]
        # Comments between tokens are deliberately refused, rather than miscounted.
        item = entry.fullmatch(raw)
        if item is None:
            raise ValueError("Elements/Companions.lean: unsupported companion entry")
        book, n, name, ref = item.groups()
        if ref != f"{book}.{n} {name}":
            raise ValueError(f"Elements/Companions.lean: companion reference disagrees: {ref!r}")
        entries.append((book, int(n), name))
        cursor = stop + re.match(r"\s*", blank[stop:]).end()
        if cursor < len(blank):
            if blank[cursor] != ",":
                raise ValueError("Elements/Companions.lean: expected a comma between companions")
            cursor += 1
    if len(entries) != len(set(entries)):
        raise ValueError("Elements/Companions.lean: duplicate companion")
    return entries


def companions(root):
    """Count listed companion theorems in Elements/Companions.lean, excluding comments."""
    return len(companion_entries(root))


def companion_propositions(root):
    """Count distinct (book, proposition) pairs widened by the listed companions."""
    return len({(book, n) for book, n, _ in companion_entries(root)})


def review_stages(root, book):
    """Read tracked review/<book>/NN.toml records, requiring valid numbers and stages."""
    stages = []
    directory = repository_path(root, Path("review") / book)
    if not directory.is_dir():
        raise ValueError(f"review/{book}: missing record directory")
    for rel in tracked_files(root, f"review/{book}/[0-9][0-9].toml"):
        if rel.parent != Path("review") / book:
            continue
        if not 1 <= int(rel.stem) <= heath.BOOKS[book]:
            raise ValueError(f"{rel}: proposition number is outside Book {book}")
        path = repository_path(root, rel)
        data = tomllib.loads(path.read_text())
        review = data.get("review")
        stage = review.get("stage") if isinstance(review, dict) else None
        if stage not in heath.STAGES:
            raise ValueError(f"{path.relative_to(root)}: invalid [review].stage {stage!r}")
        stages.append(stage)
    return stages


def reviews(root, book):
    """Count review/<book>/NN.toml records, irrespective of stage or stamp freshness."""
    return len(review_stages(root, book))


def full_reviews(root, book):
    """Count records whose [review].stage is full, irrespective of stamp freshness."""
    return review_stages(root, book).count("full")


ACCEPTANCE = "docs/reports/acceptance-books-I-III.md"


def acceptance_summary(root):
    """Read the generated report's summary at its own revision, never rerun acceptance."""
    text = repository_path(root, ACCEPTANCE).read_text()
    sections = re.findall(r"^## Summary\n(.*?)(?=^## |\Z)", text, re.M | re.S)
    if len(sections) != 1:
        raise ValueError(f"{ACCEPTANCE}: expected one generated Summary")
    summary = sections[0].strip().split("\n\n", 1)[0]
    match = re.fullmatch(r"\*\*([0-9]+) failing items?\*\*(?:, and [0-9]+ not run)?"
                      r"\. ([0-9]+) of the ([0-9]+) propositions pass every item of their own\.$",
                      summary)
    if match:
        failing, passing, total = map(int, match.groups())
        if passing <= total:
            return failing, passing
    if summary == "**No failures.** Every item of the checklist passes.":
        # The all-pass form omits the total in the summary; the generated preamble
        # still states the number of propositions checked.
        totals = re.findall(r"for each of the ([0-9]+) propositions", text)
        if len(totals) == 1:
            return 0, int(totals[0])
    raise ValueError(f"{ACCEPTANCE}: cannot read the generated acceptance counts")


def acceptance_failing(root):
    """Count failing items stated in the acceptance report's generated summary."""
    return acceptance_summary(root)[0]


def acceptance_passing(root):
    """Count propositions passing every own item in the report's generated summary."""
    return acceptance_summary(root)[1]


SCREEN = "Audit/screen.py"
SUPERPOSITION = "Audit/Superposition.lean"
PRINT_AXIOMS = re.compile(r"#print[ \t\r\n]+axioms\s+(?=[^\W\d])")
ESCAPED_NAME = re.compile(r"«[^»]*(?:»|\Z)")
SYNTAX_QUOTATION = re.compile(r"`[ \t\r\n]*\(")
REFLECTIVE_NAMES = {"__builtins__", "delattr", "eval", "exec", "getattr", "globals",
                    "locals", "setattr", "vars"}


def source_text(root, path):
    """Read a source file a count parses, refusing it by name if it cannot be read."""
    try:
        return repository_path(root, path).read_bytes().decode("utf-8")
    except UnicodeError as error:
        raise ValueError(f"{path}: cannot decode the file") from error
    except OSError as error:
        raise ValueError(f"{path}: cannot read the file ({error.strerror})") from error


def bound_names(node):
    """Names bound by one AST node without following Python execution."""
    if isinstance(node, ast.Name) and not isinstance(node.ctx, ast.Load):
        return {node.id}
    if isinstance(node, ast.arg):
        return {node.arg}
    if isinstance(node, ast.alias):
        return {node.asname or node.name.split(".")[0]}
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {node.name}
    if isinstance(node, (ast.Global, ast.Nonlocal)):
        return set(node.names)
    if isinstance(node, ast.ExceptHandler):
        return {node.name} if node.name else set()
    if isinstance(node, (ast.MatchAs, ast.MatchStar)):
        return {node.name} if node.name else set()
    if isinstance(node, ast.MatchMapping):
        return {node.rest} if node.rest else set()
    return set()


def screen_circle_rules(root):
    """Count the names in Audit/screen.py's CIRCLE, parsed with ast, never imported or run."""
    try:
        tree = ast.parse(source_text(root, SCREEN), SCREEN)
    except SyntaxError as error:
        raise ValueError(f"{SCREEN}: cannot parse the screen") from error
    assigned = [node for node in tree.body if isinstance(node, ast.Assign) and any(
        isinstance(target, ast.Name) and target.id == "CIRCLE" for target in node.targets)]
    if len(assigned) != 1 or len(assigned[0].targets) != 1:
        raise ValueError(f"{SCREEN}: expected one module-level assignment to CIRCLE alone")
    target, value = assigned[0].targets[0], assigned[0].value
    if not (isinstance(value, ast.Call) and not value.args and not value.keywords
            and isinstance(value.func, ast.Attribute) and value.func.attr == "split"
            and isinstance(value.func.value, ast.Constant)
            and isinstance(value.func.value.value, str)):
        raise ValueError(f"{SCREEN}: CIRCLE is not a string literal split with no arguments")
    itertools_imports = [name for node in tree.body if isinstance(node, ast.Import)
                         for name in node.names
                         if name.name == "itertools" and name.asname is None]
    if len(itertools_imports) != 1:
        raise ValueError(f"{SCREEN}: expected one module-level import of itertools")
    itertools_import = itertools_imports[0]
    parents = {child: node for node in ast.walk(tree) for child in ast.iter_child_nodes(node)}
    for node in ast.walk(tree):
        if (isinstance(node, ast.ImportFrom)
                and any(name.name == "*" for name in node.names)):
            raise ValueError(f"{SCREEN}:{node.lineno}: wildcard import can bind CIRCLE")
        if ((isinstance(node, ast.Name) and node.id in REFLECTIVE_NAMES)
                or (isinstance(node, ast.Attribute)
                    and node.attr in REFLECTIVE_NAMES
                    | {"CIRCLE", "__dict__", "__globals__", "f_globals", "f_locals"})
                or (isinstance(node, ast.alias)
                    and node.name.split(".")[-1] in REFLECTIVE_NAMES)):
            raise ValueError(f"{SCREEN}:{node.lineno}: reflective namespace access is forbidden")
        bindings = bound_names(node)
        if "itertools" in bindings and node is not itertools_import:
            raise ValueError(f"{SCREEN}:{node.lineno}: itertools is rebound outside its import")
        if isinstance(node, ast.Name) and node.id == "itertools":
            member = parents[node]
            call = parents.get(member)
            read_only = (isinstance(node.ctx, ast.Load)
                         and isinstance(member, ast.Attribute)
                         and member.value is node
                         and member.attr == "combinations"
                         and isinstance(member.ctx, ast.Load)
                         and isinstance(call, ast.Call)
                         and call.func is member)
            if not read_only:
                raise ValueError(f"{SCREEN}:{node.lineno}: itertools escapes its read-only use")
        if "CIRCLE" in bindings and node is not target:
            raise ValueError(f"{SCREEN}:{node.lineno}: CIRCLE is bound or changed "
                             "outside its one assignment")
        if isinstance(node, ast.Name) and node.id == "CIRCLE" and node is not target:
            parent = parents[node]
            read_only = (
                isinstance(node.ctx, ast.Load)
                and ((isinstance(parent, (ast.For, ast.AsyncFor, ast.comprehension))
                      and parent.iter is node)
                     or (isinstance(parent, ast.Call)
                         and node in parent.args
                         and isinstance(parent.func, ast.Attribute)
                         and isinstance(parent.func.value, ast.Name)
                         and parent.func.value.id == "itertools"
                         and parent.func.attr == "combinations")))
            if not read_only:
                raise ValueError(f"{SCREEN}:{node.lineno}: CIRCLE is bound or changed "
                                 "outside its one assignment")
    names = value.func.value.value.split()
    if len(names) != len(set(names)):
        raise ValueError(f"{SCREEN}: CIRCLE names a rule twice")
    return len(names)


def superposition_dependency_checks(root):
    """Count #print axioms commands in Audit/Superposition.lean, outside comments and strings."""
    # Reuse the source scanner, as companion_entries does, and for the same reason import
    # it locally. read_lean reads a comment or a string that never closes on to the end of
    # the file without counting it unsure, so a line of code is set after the end: it is
    # blanked only when something the file opens is left open.
    from check_fidelity import LONE_CR, read_lean

    source = source_text(root, SUPERPOSITION)
    if LONE_CR.search(source):
        raise ValueError(f"{SUPERPOSITION}: contains an isolated carriage return")
    code, unsure = read_lean(source + "\nend")
    if unsure or not code.endswith("\nend"):
        raise ValueError(f"{SUPERPOSITION}: cannot read every comment and string for certain")
    plain = ESCAPED_NAME.sub(
        lambda match: "x" + re.sub(r"[^\n]", " ", match[0][1:])
        if match[0].endswith("»") else re.sub(r"[^\n]", " ", match[0]), code[:-4])
    if SYNTAX_QUOTATION.search(plain):
        raise ValueError(f"{SUPERPOSITION}: syntax quotations cannot be counted")
    return len(PRINT_AXIOMS.findall(plain))


COUNTS = {
    "axioms": axioms,
    "tacit-rules": tacit_rules,
    "postulates": postulates,
    "axioms-but-postulate-5": axioms_but_postulate_5,
    "vocabulary": vocabulary,
    "companions": companions,
    "companion-propositions": companion_propositions,
    **{f"reviews:{book}": partial(reviews, book=book) for book in heath.BOOKS},
    **{f"reviews:{book}:full": partial(full_reviews, book=book) for book in heath.BOOKS},
    "acceptance:failing": acceptance_failing,
    "acceptance:passing": acceptance_passing,
    "screen-circle-rules": screen_circle_rules,
    "superposition-dependency-checks": superposition_dependency_checks,
}


def number_word(n):
    """Spell a non-negative integer in British English, including zero and hundreds."""
    small = ("zero one two three four five six seven eight nine ten eleven twelve "
             "thirteen fourteen fifteen sixteen seventeen eighteen nineteen").split()
    tens = "zero ten twenty thirty forty fifty sixty seventy eighty ninety".split()
    if n < 0:
        raise ValueError("a count cannot be negative")
    if n < 20:
        return small[n]
    if n < 100:
        return tens[n // 10] + ("-" + small[n % 10] if n % 10 else "")
    for scale, word in ((10**12, "trillion"), (10**9, "billion"),
                        (10**6, "million"), (1000, "thousand"), (100, "hundred")):
        if n >= scale:
            quotient, rest = divmod(n, scale)
            return (number_word(quotient) + " " + word
                    + ((" and " if rest < 100 else " ") + number_word(rest) if rest else ""))


START = re.compile(r"<!--\s*/?\s*count\b", re.I)
OPEN = re.compile(r"<!-- count:([A-Za-z0-9]+(?:[-:][A-Za-z0-9]+)*) -->")
CLOSE = "<!-- /count -->"


@dataclass(frozen=True)
class Marker:
    name: str
    start: int
    value_start: int
    value_end: int
    end: int


def markers(text, path):
    """Read every reserved count comment, refusing malformed, nested or unpaired ones."""
    opened = None
    found = []
    for token in START.finditer(text):
        line = text.count("\n", 0, token.start()) + 1
        where = f"{path}:{line}"
        end = text.find("-->", token.end())
        comment = text[token.start():end + 3] if end >= 0 else ""
        match = OPEN.fullmatch(comment)
        if match:
            if opened is not None:
                raise ValueError(f"{where}: nested count marker")
            opened = (match[1], token.start(), end + 3)
        elif comment == CLOSE:
            if opened is None:
                raise ValueError(f"{where}: count closing marker has no opening marker")
            name, start, value_start = opened
            if "\n" in text[value_start:token.start()]:
                raise ValueError(f"{path}:{text.count(chr(10), 0, start) + 1}: "
                                 "count marker must be inline")
            found.append(Marker(name, start, value_start, token.start(), end + 3))
            opened = None
        else:
            raise ValueError(f"{where}: malformed count marker")
    if opened is not None:
        name, start, _ = opened
        raise ValueError(f"{path}:{text.count(chr(10), 0, start) + 1}: "
                         f"unclosed count marker {name!r}")
    return found


def whole_output(path):
    """Whether render.py owns the whole Markdown file."""
    return path.parts[0] == "book" or path.as_posix() in {"CERTIFICATE.md", "GRAPH.md"}


def historical(path):
    """Protect decisions and all reports except living gap and overlap catalogues."""
    return (path.as_posix() == "docs/briefs/0002-decisions.md"
            or (path.parts[:2] == ("docs", "reports")
                and not (path.parent == Path("docs/reports")
                         and (path.name == "overlaps.md"
                              or re.fullmatch(r"gaps-book-[IVX]+\.md", path.name)))))


README_SCOPE_MARKERS = re.compile(
    r"(<!-- scope:([IVX]+) -->)(.*?)(<!-- /scope:\2 -->)", re.S)
PROGRAM_STATUS_MARKERS = re.compile(r"(<!-- status -->\n)(.*?)(<!-- /status -->)", re.S)


def partial_output_region(path, text, span):
    """Name a renderer-owned region containing a count marker, if there is one."""
    if path == Path("README.md"):
        pattern, name = README_SCOPE_MARKERS, "README.md scope region"
    elif path == Path("docs/PROGRAM.md"):
        pattern, name = PROGRAM_STATUS_MARKERS, "docs/PROGRAM.md status region"
    else:
        return None
    if any(span.start < region.end() and region.start() < span.end
           for region in pattern.finditer(text)):
        return name
    return None


def tracked_markdown(root):
    """List tracked Markdown with Git's index, including names with spaces or newlines."""
    return tracked_files(root, "*.md")


def value(root, name, cache):
    """Resolve a registered count and its optional word form, with per-run caching."""
    base, _, form = name.rpartition(":")
    if form not in {"word", "Word"}:
        base, form = name, ""
    if base not in COUNTS:
        raise ValueError(f"unknown count name {name!r}")
    if base not in cache:
        cache[base] = COUNTS[base](root)
    rendered = number_word(cache[base]) if form else str(cache[base])
    return rendered.capitalize() if form == "Word" else rendered


def updates(root, *, check=False):
    """Plan all replacements before writing; report stale text only when checking."""
    changes, errors, cache = {}, [], {}
    try:
        paths = tracked_markdown(root)
        absent, faults = absent_tracked(root, paths)
    except (ValueError, OSError) as error:
        return {}, [str(error)]
    errors += faults
    for path in paths:
        if path in absent:
            continue
        try:
            text = repository_path(root, path).read_text()
            token = START.search(text)
            if whole_output(path) and token:
                line = text.count("\n", 0, token.start()) + 1
                raise ValueError(f"{path}:{line}: count markers are forbidden "
                                 "in whole renderer outputs")
            spans = markers(text, path)
        except (ValueError, OSError) as error:
            errors.append(str(error))
            continue
        filled = text
        for span in reversed(spans):
            where = f"{path}:{text.count(chr(10), 0, span.start) + 1}"
            if historical(path):
                errors.append(f"{where}: count marker {span.name!r} is forbidden in dated history")
                continue
            region = partial_output_region(path, text, span)
            if region:
                errors.append(f"{where}: count marker {span.name!r} is forbidden in {region}")
                continue
            try:
                computed = value(root, span.name, cache)
            except (ValueError, OSError) as error:
                errors.append(f"{where}: {error}")
                continue
            stated = text[span.value_start:span.value_end]
            if check and stated != computed:
                errors.append(f"{where}: count {span.name!r}: stated {stated!r}, "
                              f"computed {computed!r}; run python3 scripts/render.py")
            filled = filled[:span.value_start] + computed + filled[span.value_end:]
        if filled != text:
            changes[root / path] = filled
    return changes, errors


def without_markers(text):
    """Copy already validated prose into a book page with values but no count comments."""
    return OPEN.sub("", text).replace(CLOSE, "")


if __name__ == "__main__":
    for name, count in COUNTS.items():
        print(f"{name}: {count(heath.ROOT)}")
