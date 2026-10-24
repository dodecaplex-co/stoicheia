"""An axiom in a `.lake` folder of model/Model/ and of model/Check/ is caught:
`check_fidelity.py` must name each, as an axiom declared outside `Elements/Foundations/`.
One in model/.lake, the package's own, is not read, and must not be named.
"""

from pathlib import Path

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """An axiom in a `.lake` folder of model/Model/ and of model/Check/ is caught, and one
    in the package's own model/.lake is not read."""
    plants = ("model/Model/.lake/Planted.lean", "model/Check/.lake/Planted.lean",
              "model/.lake/Planted.lean")
    planted: list[Path] = []          # files, then the folders made for them
    try:
        for rel in plants:
            path = nt.ROOT / rel
            assert not path.exists() and not path.is_symlink(), f"{rel} exists; update this test"
            if not path.parent.exists():
                path.parent.mkdir()
                planted.append(path.parent)
            path.write_text("axiom planted_axiom : True\n")
            planted.insert(0, path)
        result = nt.fidelity()
        for rel in plants[:2]:
            nt.expect_failure(f"an axiom in {rel}", result,
                              f"{rel}:1: declares an axiom outside Elements/Foundations/",
                              unwanted=("model/.lake/",))
    finally:
        for path in planted:
            if path.is_dir():
                path.rmdir()
            else:
                path.unlink(missing_ok=True)
