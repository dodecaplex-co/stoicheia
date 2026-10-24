"""A symbolic link named `.lake`, to a directory, to a file or to nothing, is refused in
model/, model/Model/ and model/Check/, each case in a small tree of its own, so the
edition's model/.lake is never moved, copied or read: check_fidelity's source scan, run on
that tree, must name the link by its own path, as one it does not follow, and read nothing
through it. A real model/.lake directory holding an axiom and a link is not read.
"""

import tempfile
from pathlib import Path

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """A symbolic link named `.lake`, to a directory, to a file or to nothing, is refused
    by its own path in model/, model/Model/ and model/Check/, never followed; a real
    model/.lake directory holding an axiom and a link is not entered. Each case is a
    small tree of its own, so the edition's model/.lake is never moved, copied or read."""
    axiom = "axiom planted_axiom : True\n"
    for folder in ("model", "model/Model", "model/Check"):
        for kind in ("directory", "file", "dangling"):
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp).resolve()
                (root / "model/Model").mkdir(parents=True)
                (root / "model/Check").mkdir()
                target = root / "Target"
                if kind == "directory":
                    target.mkdir()
                    (target / "Planted.lean").write_text(axiom)
                elif kind == "file":
                    target.write_text(axiom)
                rel = f"{folder}/.lake"
                (root / rel).symlink_to(target, target_is_directory=kind == "directory")
                nt.expect_failure(f"a {kind} link at {rel}", nt.rules_in(root),
                                  f"{rel}: a symbolic link, which the source scan does not follow;",
                                  unwanted=(f"{rel}/", f"{rel}:1:"))
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        (root / "model/.lake").mkdir(parents=True)
        (root / "model/.lake/Planted.lean").write_text(axiom)
        (root / "model/.lake/Link.lean").symlink_to(root / "model/.lake/Planted.lean")
        result = nt.rules_in(root)
        if result.returncode != 0:
            nt.failures.append("a real model/.lake was read: " + result.stdout.strip())
            print(result.stdout[-3000:])
        else:
            print("✓ a real model/.lake holding an axiom and a link: not read")
