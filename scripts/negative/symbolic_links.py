"""Symbolic links to a directory in model/Model/ and to a file in model/Check/
(`model/Model/PlantedLink`, to model/Check, and `model/Check/PlantedLink.lean`, to
`Elements.lean`) are refused by `check_fidelity.py` by their own paths, as symbolic links
the source scan does not follow, without following them: nothing beneath the directory's
link may be named.
"""

from pathlib import Path

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """Refuse a directory link and a file link by their own paths."""
    links = (("model/Model/PlantedLink", nt.ROOT / "model/Check"),
             ("model/Check/PlantedLink.lean", nt.ROOT / "Elements.lean"))
    planted: list[Path] = []
    try:
        for rel, target in links:
            path = nt.ROOT / rel
            assert not path.exists() and not path.is_symlink(), f"{rel} exists; update this test"
            assert target.exists(), f"{target.relative_to(nt.ROOT)} is missing; update this test"
            path.symlink_to(target, target_is_directory=target.is_dir())
            planted.append(path)
        result = nt.fidelity()
        for rel, _ in links:
            nt.expect_failure(f"a symbolic link at {rel}", result,
                              f"{rel}: a symbolic link, which the source scan does not follow;",
                              unwanted=("model/Model/PlantedLink/",))
    finally:
        for path in planted:
            path.unlink(missing_ok=True)
