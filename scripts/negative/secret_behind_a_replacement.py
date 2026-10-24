"""Without a build, in a temporary repository of its own, never this clone (#256): a
commit adding a token, its blob read through a clean stand-in, once by `git replace`
and once by a folder of refs that GIT_REPLACE_REF_BASE names, so that git shows the
stand-in while a push would send the token. `safe_push.py --scan-push`, as the
pre-push hook runs it, refuses each, naming the secret scan, and the repository's
clean commit passes while each stand-in is live. A git command that fails while the
repository is set up is reported, and the plant stops there. The token is built as
the plant runs, so this file passes the scan itself. Only count_markers runs under
--counts-only; this plant runs with the rest, before the plants that build.
"""

import base64
import hashlib
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """A token committed in a temporary repository of its own, never this clone, its blob
    read through a clean stand-in (#256): git shows the stand-in, while a push sends the
    token, so the scan must read past it. The token is built here, as
    scripts/test_safe_push.py builds its TOKEN, so that this file passes the scan."""
    token = base64.b64encode(hashlib.sha256(b"a planted token").digest()).decode()
    # None of the caller's git environment: the temporary repository is the only one read.
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    scan = [sys.executable, str(nt.ROOT / "scripts" / "safe_push.py"), "--scan-push"]

    class SetUpFailed(Exception):
        """A git command setting up the repository failed, and has been reported."""

    with tempfile.TemporaryDirectory(prefix="stoicheia-replace-") as tmp:
        repo = Path(tmp)

        def git(*args: str, stdin: str | None = None) -> str:
            result = subprocess.run(["git", *args], cwd=repo, env=env, input=stdin,
                                    capture_output=True, text=True)
            if not nt.expect_success(f"a token behind a replacement: git {' '.join(args)}",
                                     result):
                raise SetUpFailed
            return result.stdout.strip()

        try:
            git("init", "-q")
            for key, value in (("user.name", "negative tests"),
                               ("user.email", "negative-tests@example.invalid"),
                               ("commit.gpgsign", "false")):
                git("config", key, value)
            notes = repo / "notes.md"
            notes.write_text("Some notes.\n")
            git("add", "notes.md")
            git("commit", "-q", "--no-verify", "-m", "A clean commit")
            clean = git("rev-parse", "HEAD")
            notes.write_text(f'Some notes.\napi_token = "{token}"\n')
            git("commit", "-q", "--no-verify", "-am", "A token")
            planted, blob = git("rev-parse", "HEAD"), git("rev-parse", "HEAD:notes.md")
            stand_in = git("hash-object", "-w", "--stdin", stdin="Some notes.\nNo more.\n")
            for how, ref, extra in (("git replace", f"refs/replace/{blob}", {}),
                                    ("GIT_REPLACE_REF_BASE", f"refs/stand-ins/{blob}",
                                     {"GIT_REPLACE_REF_BASE": "refs/stand-ins/"})):
                if extra:
                    git("update-ref", ref, stand_in)
                else:
                    git("replace", blob, stand_in)
                name = f"a token behind a replacement ({how})"
                planted_env = {**env, **extra}
                shown = subprocess.run(["git", "show", f"{planted}:notes.md"], cwd=repo,
                                       env=planted_env, capture_output=True, text=True)
                if shown.returncode != 0 or token in shown.stdout:
                    # Then the plant hides nothing, and a refusal would prove nothing.
                    nt.failures.append(f"{name}: git does not read the stand-in")
                    print(f"✗ {name}: git does not read the stand-in")
                else:
                    nt.expect_failure(name, subprocess.run(
                        [*scan, planted, clean, "refs/heads/planted"], cwd=repo,
                        env=planted_env, capture_output=True, text=True),
                        "pre-push: refusing the push to refs/heads/planted: the secret scan "
                        "found", unwanted=(token,))
                # The clean commit, scanned while the stand-in is still live, passes.
                beside = f"the clean commit beside a replacement ({how})"
                result = subprocess.run([*scan, clean, "0" * 40, "refs/heads/clean"],
                                        cwd=repo, env=planted_env, capture_output=True,
                                        text=True)
                if nt.expect_success(beside, result):
                    print(f"✓ {beside}: passed (without Lean)")
                git("update-ref", "-d", ref)
        except SetUpFailed:
            return
