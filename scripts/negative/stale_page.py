"""I.1's generated page left stale beside a changed mishnah: after `render.py`, the
`git status --porcelain` command of WORKFLOW, section 8, must name the changed page,
` M book/I/01.md`, and the rendered page must hold the changed source and not the obsolete
sentence planted in it. Editing just the page would be repaired back to HEAD and leave that
status clean, so the source changes too. Every generated output is saved and restored, and
the generated paths must return to their entry status. The plant judges the refusal itself,
and records it with `nt.refused`.
"""

import sys

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """A stale page after a source change, tested by the actual freshness command.

    Rendering a hand edit alone restores HEAD, so it cannot test the post-render
    Git status. Change the source too, then require both its rendered text and the
    page's own status line. Save every output, including pre-existing local edits.
    """
    source = nt.ROOT / "mishnah/I/01.md"
    page = nt.ROOT / "book/I/01.md"
    saved_source = source.read_bytes()
    saved = {p: p.read_bytes() for p in nt.generated_files()}
    command = ("git", "status", "--porcelain", "--", *nt.GENERATED)
    before = nt.run(*command)
    if not nt.expect_success("freshness entry status", before):
        return
    page_status = nt.run("git", "status", "--porcelain", "--", "book/I/01.md")
    if not nt.expect_success("I.1 page entry status", page_status):
        return
    if page_status.stdout:
        nt.failures.append("freshness: book/I/01.md must be clean before the plant")
        return
    current = b"A source sentence planted for the freshness check."
    obsolete = b"An obsolete sentence planted in the generated page."
    assert current not in saved_source and obsolete not in saved[page]
    try:
        source.write_bytes(saved_source + b"\n" + current + b"\n")
        page.write_bytes(saved[page] + b"\n" + obsolete + b"\n")
        if not nt.expect_success("rendering the stale page",
                                 nt.run(sys.executable, "scripts/render.py")):
            return
        status = nt.run(*command)
        if not nt.expect_success("freshness status", status):
            return
        rendered = page.read_bytes()
        if (current not in rendered or obsolete in rendered
                or status.stdout.splitlines() != sorted(
                    [*before.stdout.splitlines(), " M book/I/01.md"], key=lambda s: s[3:])):
            nt.failures.append("freshness: expected the rendered source and ' M book/I/01.md'")
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
                nt.failures.append("freshness: generated paths did not return to their entry status")
            else:
                print("✓ freshness: generated paths restored to their entry status")
