#!/usr/bin/env python3
"""Exercise the model source audit across cached incremental builds."""

from pathlib import Path
import os
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "model"
NON_ASCII_NOTE = MODEL / "Model" / "notes-é.txt"
CANONICAL_SOURCE = ROOT / "Elements" / "Foundations" / "Phrases.lean"
ALIASED_SOURCE = ROOT / "Elements" / "Foundations" / "Phraſes.lean"


def exact_entry_exists(path: Path) -> bool:
    return any(entry.name == path.name for entry in path.parent.iterdir())


def build(*targets: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "build", *targets], cwd=MODEL, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )


def require_success(label: str, result: subprocess.CompletedProcess[str]) -> None:
    if result.returncode:
        raise AssertionError(f"{label} failed ({result.returncode}):\n{result.stdout}")


def require_failure(
    label: str, result: subprocess.CompletedProcess[str], message: str | None = None,
) -> None:
    if not result.returncode:
        raise AssertionError(f"{label} unexpectedly passed")
    if message is not None and message not in result.stdout:
        raise AssertionError(f"{label} missed {message!r}:\n{result.stdout}")


def reject_with_both_builds(label: str, message: str | None = None) -> None:
    require_failure(f"ordinary build after {label}", build(), message)
    require_failure(
        f"direct Check.RoundTrip build after {label}", build("Check.RoundTrip"), message,
    )


def main() -> int:
    for fixture in (NON_ASCII_NOTE, ALIASED_SOURCE):
        if exact_entry_exists(fixture):
            raise AssertionError(f"fixture path already exists: {fixture.relative_to(ROOT)}")
    source = CANONICAL_SOURCE.read_bytes()
    try:
        require_success("cached ordinary build", build())
        require_success("cached direct Check.RoundTrip build", build("Check.RoundTrip"))

        NON_ASCII_NOTE.write_bytes(b"notes\n")
        reject_with_both_builds(
            "adding a non-ASCII non-source entry",
            "model/Model/notes-é.txt: non-canonical source path",
        )
        NON_ASCII_NOTE.unlink()
        require_success("restored ordinary build", build())

        os.replace(CANONICAL_SOURCE, ALIASED_SOURCE)
        message = None
        if CANONICAL_SOURCE.exists():
            message = "Elements/Foundations/Phraſes.lean: non-canonical source path"
        reject_with_both_builds(
            "renaming a selected source without changing its bytes",
            message,
        )
    finally:
        if exact_entry_exists(NON_ASCII_NOTE):
            NON_ASCII_NOTE.unlink()
        if exact_entry_exists(ALIASED_SOURCE):
            os.replace(ALIASED_SOURCE, CANONICAL_SOURCE)
    if CANONICAL_SOURCE.read_bytes() != source:
        raise AssertionError("renamed source was not restored byte for byte")
    require_success("final restored ordinary build", build())
    require_success("final restored direct Check.RoundTrip build", build("Check.RoundTrip"))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, OSError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
