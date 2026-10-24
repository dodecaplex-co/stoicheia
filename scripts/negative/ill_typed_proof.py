"""An ill-typed proof in I.1's compiled module, for leanchecker's kernel replay:
`True.intro` as a proof of `False`, added past the kernel by
`set_option debug.skipKernelTC true` and a `run_cmd` that calls `addDecl`, the way
docs/reports/read-through-01.md names. The source scan refuses both, so I.1 is compiled
with them by `lake env lean -o`, over its own `.olean`, from a copy outside the tree.
leanchecker, invoked as in `check_kernel.py`, must reject the proof, naming the
declaration and the kernel's type mismatch, not a file it cannot read. The build is
restored as corrupt_olean restores it, and on success the whole environment is replayed.
The plant's Lean, ILL_TYPED and ILL_TYPED_LEAN, is in scripts/negative_tests.py, where
tests/test_negative_tests.py reads it.
"""

import tempfile
from pathlib import Path

import negative_tests as nt

BUILDS = True


def plant() -> None:
    """Exercise leanchecker's kernel replay with an ill-typed proof in I.1's compiled module,
    rejected by name, not as a file it cannot read; the build is restored as corrupt_olean
    restores it."""
    bin_ = nt.check_kernel.toolchain_bin()
    command = ("lake", "env", str(bin_ / "leanchecker"), "--fresh", "Elements")
    rel = "Elements/BookI/Prop01.lean"
    path = nt.ROOT / ".lake/build/lib/lean/Elements/BookI/Prop01.olean"
    saved = path.read_bytes()
    outputs = nt.BuildOutputs()
    try:
        with tempfile.TemporaryDirectory(prefix="stoicheia-kernel-") as tmp:
            root = Path(tmp).resolve()
            source = root / rel
            source.parent.mkdir(parents=True)
            source.write_text("import Lean.Elab.Command\n" + (nt.ROOT / rel).read_text()
                              + nt.ILL_TYPED_LEAN)
            if not nt.expect_success("I.1 compiled with an ill-typed proof",
                                     nt.run("lake", "env", "lean", "-R", str(root), "-o",
                                            str(path), str(source))):
                return
        nt.expect_failure("an ill-typed proof in I.1's compiled module, replayed by "
                          "leanchecker",
                          nt.run(*command), f"while replaying declaration '{nt.ILL_TYPED}'",
                          f"(kernel) declaration type mismatch, '{nt.ILL_TYPED}'",
                          unwanted=("failed to read file", "invalid header", "does not exist"))
    finally:
        path.write_bytes(saved)
        if nt.rebuild_restored("the Elements build restored after the ill-typed proof",
                               outputs, force=path):
            nt.expect_success("leanchecker's replay after the ill-typed proof", nt.run(*command))
