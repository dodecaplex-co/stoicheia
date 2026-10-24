"""A corrupt header in I.1's compiled `.olean`, for leanchecker's loading of compiled files:
leanchecker, invoked as in `check_kernel.py`, must fail naming the file and its invalid
header. The original bytes are restored, a rebuild is required, and on success the whole
environment is replayed.
"""

import negative_tests as nt

BUILDS = True


def plant() -> None:
    """Exercise leanchecker's loader, without pretending to plant an invalid proof."""
    bin_ = nt.check_kernel.toolchain_bin()
    command = ("lake", "env", str(bin_ / "leanchecker"), "--fresh", "Elements")
    path = nt.ROOT / ".lake/build/lib/lean/Elements/BookI/Prop01.olean"
    saved = path.read_bytes()
    assert saved.startswith(b"olean"), "I.1's compiled header has changed; update this test"
    outputs = nt.BuildOutputs()
    try:
        path.write_bytes(b"broken" + saved[6:])
        nt.expect_failure("a corrupt compiled header read by leanchecker", nt.run(*command),
                          "failed to read file", "Elements/BookI/Prop01.olean", "invalid header")
    finally:
        path.write_bytes(saved)
        if nt.rebuild_restored("the restored Elements build", outputs, force=path):
            nt.expect_success("leanchecker's replay after restoration", nt.run(*command))
