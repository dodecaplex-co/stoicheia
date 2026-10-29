"""I.1's generated page left stale beside a changed mishnah: after `render.py`, the
`git status --porcelain` command of WORKFLOW, section 8, over the whole worktree, must name
the changed page, ` M book/I/01.md`, beside its source, ` M mishnah/I/01.md`, and nothing
else beyond the status a first render leaves, and the rendered page must hold the changed
source and not the obsolete sentence planted in it. Editing just the page would be repaired
back to HEAD and leave that status clean, so the source changes too. The pages are rendered
once before the plant, and the plant is judged against that status and those bytes: in the
pre-flight's pass with origin/main's checks, a renderer change finds its own regenerated
pages stale, and that is freshness, not this plant's verdict (#677). Every generated output
is saved and restored, and the worktree must return to its entry status. The plant judges
the refusal itself, and records it with `nt.refused`.
"""

import sys

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """A stale page after a source change, tested by the actual freshness command: the
    whole-worktree `git status --porcelain` of section 8, CI's check job and the
    pre-flight.

    Rendering a hand edit alone restores HEAD, so it cannot test the post-render
    Git status. Change the source too, then require both its rendered text and the
    status lines of the page and its source beside the status the first render left, and
    nothing else. Save every output, including pre-existing local edits.
    """
    source = nt.ROOT / "mishnah/I/01.md"
    page = nt.ROOT / "book/I/01.md"
    saved_source = source.read_bytes()
    saved = {p: p.read_bytes() for p in nt.generated_files()}
    command = ("git", "status", "--porcelain")
    before = nt.run(*command)
    if not nt.expect_success("freshness entry status", before):
        return
    planted_status = nt.run("git", "status", "--porcelain", "--", "book/I/01.md",
                            "mishnah/I/01.md")
    if not nt.expect_success("I.1 page and mishnah entry status", planted_status):
        return
    if planted_status.stdout:
        nt.failures.append("freshness: book/I/01.md and mishnah/I/01.md must be clean "
                           "before the plant")
        return
    current = b"A source sentence planted for the freshness check."
    obsolete = b"An obsolete sentence planted in the generated page."
    assert current not in saved_source and obsolete not in saved[page]
    try:
        if not nt.expect_success("rendering the pages as the sources stand",
                                 nt.run(sys.executable, "scripts/render.py")):
            return
        settled = nt.run(*command)
        if not nt.expect_success("freshness status as rendered", settled):
            return
        source.write_bytes(source.read_bytes() + b"\n" + current + b"\n")
        page.write_bytes(page.read_bytes() + b"\n" + obsolete + b"\n")
        if not nt.expect_success("rendering the stale page",
                                 nt.run(sys.executable, "scripts/render.py")):
            return
        status = nt.run(*command)
        if not nt.expect_success("freshness status", status):
            return
        rendered = page.read_bytes()
        expected = {*settled.stdout.splitlines(), " M book/I/01.md", " M mishnah/I/01.md"}
        if (current not in rendered or obsolete in rendered
                or sorted(status.stdout.splitlines()) != sorted(expected)):
            nt.failures.append("freshness: expected the rendered source, and ' M book/I/01.md' "
                               "and ' M mishnah/I/01.md' beside the status as rendered")
            print(status.stdout)
        else:
            nt.refused("a stale generated page: caught by git status:  M book/I/01.md")
    finally:
        source.write_bytes(saved_source)
        for path in nt.generated_files() - saved.keys():
            path.unlink()
        for path, data in saved.items():
            path.write_bytes(data)
        after = nt.run(*command)
        if nt.expect_success("restored freshness status", after):
            if after.stdout != before.stdout:
                nt.failures.append("freshness: the worktree did not return to its entry status")
            else:
                print("✓ freshness: the worktree restored to its entry status")
