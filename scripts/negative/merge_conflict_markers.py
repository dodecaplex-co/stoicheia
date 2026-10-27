"""Without a build, in a temporary copy without Git of the two tracked files it plants,
CONTRIBUTING.md and NOTICE, of the two the style check reads in any tree, README.md and
docs/reading.md, and of the tracked scripts at the top of scripts/: opening, base and
closing merge markers, a middle between outer markers, and a lone middle in a non-Markdown
file, comment, fence or after a completed heading, indented code or link reference
definition (on one line or two) each fail S23 of `check_style.py --no-lean` with their
file, line and kind. Setext headings, including several lines and one after a comment
containing a fence, leave the unplanted copy's result unchanged, and that result is a pass,
so a check that cannot run on the copy is not taken for a refusal. Symlinks are not copied.
This runs before the plants that build. The style check on the whole tree, S23 among its
rules, runs in the check registry.
"""

import re
import subprocess
import sys
import tempfile
from pathlib import Path

import negative_tests as nt

BUILDS = False

# The copy: the two files planted, the two texts the style check reads whatever the tree
# holds, and the scripts it runs, check_style.py and the modules it imports.
PLANTED = ("CONTRIBUTING.md", "NOTICE")
READ_ALWAYS = ("README.md", "docs/reading.md")
SCRIPT = re.compile(r"scripts/[^/]+\.py")


def plant() -> None:
    """Plant raw marker lines in copies of tracked text, with no Git or Lean needed
    by the check. The unplanted copy must pass, and each harmless heading must leave
    its result unchanged.
    """
    listing, names = nt.tracked_names()
    if listing.returncode != 0:
        decoded = subprocess.CompletedProcess(
            listing.args, listing.returncode,
            listing.stdout.decode(errors="replace"), listing.stderr.decode(errors="replace"))
        nt.expect_success("tracked files for marker plants", decoded)
        return
    with tempfile.TemporaryDirectory(prefix="stoicheia-markers-") as tmp:
        root = Path(tmp)
        nt.copy_marker_files(root, [name for name in names if name in PLANTED + READ_ALWAYS
                                    or SCRIPT.fullmatch(name)])

        def check() -> subprocess.CompletedProcess:
            return subprocess.run([sys.executable, "scripts/check_style.py", "--no-lean"],
                                  cwd=root, capture_output=True, text=True)

        baseline = check()
        if not nt.expect_success("the style check on the unplanted copy", baseline):
            return
        markdown = "CONTRIBUTING.md"
        non_markdown = "NOTICE"
        cases = [
            ("opening", markdown, ["<" * 7 + " ours"], [(0, "opening")]),
            ("base", markdown, ["|" * 7 + " base"], [(0, "base")]),
            ("middle between markers", markdown,
             ["<" * 7 + " ours", "A paragraph.", "=" * 7, ">" * 7 + " theirs"],
             [(0, "opening"), (2, "middle"), (3, "closing")]),
            ("lone middle", non_markdown, ["=" * 7], [(0, "middle")]),
            ("closing", markdown, [">" * 7 + " theirs"], [(0, "closing")]),
            ("middle in a comment", markdown,
             ["<!--", "Comment text", "=" * 7, "-->"], [(2, "middle")]),
            ("middle after a completed heading", markdown,
             ["Heading", "=" * 3, "=" * 7], [(2, "middle")]),
            ("middle after a hyphen heading", markdown,
             ["Heading", "-" * 3, "=" * 7], [(2, "middle")]),
            ("middle after indented code", markdown,
             ["", "    code", "=" * 7], [(2, "middle")]),
            ("middle after a reference definition", markdown,
             ["", "[label]: destination", "=" * 7], [(2, "middle")]),
            ("middle after a two-line reference definition", markdown,
             ["", "[label]:", " /url", "=" * 7], [(3, "middle")]),
            ("middle in a fence", markdown,
             ["```", "Code text", "=" * 7, "```"], [(2, "middle")]),
            ("middle after a fence inside a comment", markdown,
             ["<!--", "```", "Comment text", "=" * 7, "-->"], [(3, "middle")]),
        ]
        for name, rel, lines, expected in cases:
            path = root / rel
            saved = path.read_bytes()
            prefix = saved + b"\n"
            first = prefix.count(b"\n") + 1
            try:
                path.write_bytes(prefix + ("\n".join(lines) + "\n").encode())
                wanted = [f"S23 {rel}:{first + offset}: {kind} merge-conflict marker"
                          for offset, kind in expected]
                nt.expect_failure(f"{name} merge marker", check(), *wanted)
            finally:
                path.write_bytes(saved)
        path = root / markdown
        saved = path.read_bytes()
        for heading in ("A planted setext heading", "A planted heading\ncontinued",
                        "<!--\n```\n-->\nA planted heading",
                        "A planted heading\n    continued"):
            try:
                path.write_bytes(saved + ("\n" + heading + "\n" + "=" * 7 + "\n").encode())
                result = check()
                if (result.returncode, result.stdout, result.stderr) != (
                        baseline.returncode, baseline.stdout, baseline.stderr):
                    nt.failures.append(f"a setext heading changed the style check's result: {heading!r}")
                    print(result.stdout + result.stderr)
                else:
                    print(f"✓ a seven-equals setext heading ({heading!r}): no new refusal")
            finally:
                path.write_bytes(saved)
