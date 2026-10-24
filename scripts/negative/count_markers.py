"""Without a build, in a disposable source copy: a stale inline vocabulary count and an
unknown count name are refused by check_fidelity.py, and a correct count passes. Missing or
mismatched Git work trees and a Markdown symlink are refused with diagnostics, the symlink
by check_fidelity.py and render.py alike, neither writing through it. `--counts-only` runs
this plant alone, after the file-only regressions.
"""

import subprocess
import sys
import tempfile
from pathlib import Path

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """Plant count faults and unsafe discovery paths in a copy, without Lean."""
    with nt.count_source_copy() as (copy, env):
        path = copy / "docs/PROGRAM.md"
        original = path.read_text()
        line = original.count("\n") + 2
        computed = nt.generated_counts.vocabulary(copy)
        for name, stated in (("vocabulary", str(computed + 1)),
                             ("unknown-count", "0"), ("vocabulary", str(computed))):
            path.write_text(original + f"\nVocabulary: <!-- count:{name} -->"
                            f"{stated}<!-- /count -->.\n")
            result = subprocess.run([sys.executable, "scripts/check_fidelity.py"],
                                    cwd=copy, env=env, capture_output=True, text=True)
            where = f"docs/PROGRAM.md:{line}:"
            if name == "unknown-count":
                nt.expect_failure("an unknown count name", result, where,
                                  "unknown count name 'unknown-count'")
            elif stated != str(computed):
                nt.expect_failure("a stale inline count", result, where, "count 'vocabulary'",
                                  f"stated '{stated}'", f"computed '{computed}'",
                                  "run python3 scripts/render.py")
            elif nt.expect_success("a correct inline count", result):
                print("✓ a correct inline count: passed (without Lean)")
        path.write_text(original)
        for name, git_env, diagnostic in (
                ("missing Git metadata",
                 {k: v for k, v in env.items() if not k.startswith("GIT_")},
                 "cannot resolve Git work tree"),
                ("a mismatched Git work tree", {**env, "GIT_WORK_TREE": str(nt.ROOT)},
                 "does not match repository root")):
            result = subprocess.run([sys.executable, "scripts/check_fidelity.py"],
                                    cwd=copy, env=git_env, capture_output=True, text=True)
            nt.expect_failure(name, result, diagnostic, unwanted=("Traceback",))
        with tempfile.TemporaryDirectory(prefix="stoicheia-count-target-", dir="/tmp") as tmp:
            target = Path(tmp) / "notes.md"
            text = "<!-- count:vocabulary -->0<!-- /count -->\n"
            target.write_text(text)
            path.unlink()
            path.symlink_to(target)
            try:
                for script in ("check_fidelity.py", "render.py"):
                    result = subprocess.run([sys.executable, f"scripts/{script}"],
                                            cwd=copy, env=env, capture_output=True, text=True)
                    nt.expect_failure(f"a Markdown symlink in {script}", result,
                                      "docs/PROGRAM.md: symlink is forbidden", unwanted=("Traceback",))
                    if target.read_text() != text:
                        nt.failures.append(f"{script} wrote through a Markdown symlink")
            finally:
                path.unlink()
                path.write_text(original)
