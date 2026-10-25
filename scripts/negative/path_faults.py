"""Without a build, in a temporary copy of Git's index named by GIT_INDEX_FILE: a case
twin of README.md, a case twin of a protected file (Certificate/fields.md, beside
Certificate/FIELDS.md), a space in a page's name, an upper-case extension, a symbolic
link, an executable bit on a script outside the six, an svg under book/ and a
misnamed review record each make `check_paths.py` fail, naming the path and its
rule, on a copy that passes before it is planted. The real index and the work tree
are never written and no file is read; the real index's entries are compared before
and after. It runs with the file-only plants.
"""

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import check_paths
import negative_tests as nt

BUILDS = False

# The file-name standard's plants: a fault of each kind, planted in a copy of Git's
# index: what it is, its mode and path, and the rule of check_paths.py that must name it.
PATH_FAULTS = (
    ("a case twin of README.md", "100644", "readme.md", "P2"),
    ("a case twin of a protected file", "100644", "Certificate/fields.md", "P2"),
    ("a space in a page's name", "100644", "book/I/Planted page.md", "P1"),
    ("an upper-case extension", "100644", "docs/planted.MD", "P3"),
    ("a symbolic link", "120000", "docs/planted-link.md", "P6"),
    ("an executable bit outside the six", "100755", "scripts/heath.py", "P6"),
    ("an svg under book/", "100644", "book/I/01.svg", "P4"),
    ("a misnamed review record", "100644", "review/I/1.toml", "P5"),
)


def plant() -> None:
    """Plant each fault of PATH_FAULTS in a fresh copy of Git's index, named to Git by
    GIT_INDEX_FILE, and run check_paths.py on that copy: each must fail, naming the path
    and its rule, and the copy must pass before anything is planted, so that each fault
    is caught for itself. Only the copy is written, so the real index, the work tree and
    `git status` stay as they were; Git's listing of the real index is compared before
    and after. No file is read: the planted entries reuse a tracked object's id."""
    listing = ("git", "ls-files", "-s", "-z")
    before = nt.run(*listing)
    index = nt.run("git", "rev-parse", "--git-path", "index")
    if not (nt.expect_success("the index's entries before the path plants", before)
            and nt.expect_success("the index's place", index)):
        return
    real = nt.ROOT / index.stdout.strip()
    blob = before.stdout.split("\t", 1)[0].split(" ")[1]
    with tempfile.TemporaryDirectory(prefix="stoicheia-paths-") as tmp:
        copy = Path(tmp) / "index"
        env = {**os.environ, "GIT_INDEX_FILE": str(copy)}
        shutil.copyfile(real, copy)
        if nt.expect_success("check_paths.py on an unplanted copy of the index",
                             subprocess.run([sys.executable, "scripts/check_paths.py"],
                                            cwd=nt.ROOT, env=env, capture_output=True,
                                            text=True)):
            print("✓ an unplanted copy of the index passes check_paths.py")
        for name, mode, path, rule in PATH_FAULTS:
            shutil.copyfile(real, copy)
            planted = subprocess.run(
                ["git", "-c", "core.ignorecase=false", "-c", "core.precomposeunicode=false",
                 "update-index", "--add", "--cacheinfo", f"{mode},{blob},{path}"],
                cwd=nt.ROOT, env=env, capture_output=True, text=True)
            if not nt.expect_success(f"planting {name} in a copy of the index", planted):
                continue
            nt.expect_failure(f"{name} in the index",
                              subprocess.run([sys.executable, "scripts/check_paths.py"],
                                             cwd=nt.ROOT, env=env, capture_output=True,
                                             text=True),
                              f"✗ {rule} {check_paths.shown(path)}: ")
    after = nt.run(*listing)
    if nt.expect_success("the index's entries after the path plants", after):
        if after.stdout != before.stdout:
            nt.failures.append("the path plants changed the real index")
        else:
            print("✓ the path plants left the real index as it was")
