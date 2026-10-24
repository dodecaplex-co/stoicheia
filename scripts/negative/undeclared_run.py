"""III.16's review record, `review/III/16.toml`, without the passage that declares its angle
clauses, of whatever kind (left in Euclid's words, or argued another way by a companion),
leaves a run of `--` lines with no Lean beneath it undeclared. Every `[[passage]]` that
begins within such a run is dropped, and `check_fidelity.py` must fail, naming the run of
the angle clauses by its first words, "I say further that the angle of the". If no passage
of the record begins there, the plant fails, asking for it to be updated.
"""

import negative_tests as nt

BUILDS = False


def toml_blocks(text: str) -> list[str]:
    """A TOML file cut before each table header, so that whole tables can be dropped."""
    blocks, current = [], []
    for line in text.splitlines(keepends=True):
        if line.lstrip().startswith("[") and current:
            blocks.append("".join(current))
            current = []
        current.append(line)
    blocks.append("".join(current))
    return blocks


def plant() -> None:
    """Drop the [[passage]] tables that begin within III.16's runs of `--` lines with no
    Lean beneath them, and the run of the angle clauses must be caught: the message names
    it by its first words, since the runs before it are caught too. The passage that
    declares that run may be of any kind (left in Euclid's words, or argued another way
    by a companion); what is tested is that a run no passage declares is caught."""
    import tomllib
    record = nt.heath.review_path("III", 16)
    src = nt.heath.lean_path("III", 16).read_text()
    runs = nt.check_fidelity.uncarried_runs(src, 16)
    starts = nt.check_fidelity.sentence_starts(nt.check_fidelity.proof_lines(src, 16))
    saved = record.read_text()
    kept, dropped = [], []
    for block in toml_blocks(saved):
        table = tomllib.loads(block).get("passage", [{}])[0] if block.lstrip().startswith("[[passage]]") else {}
        at = nt.check_fidelity._plain(table.get("at", "")) if table else None
        if at and any(ln in run.lines and words.startswith(at) for run in runs for ln, words in starts):
            dropped.append(at)
        else:
            kept.append(block)
    angles = nt.check_fidelity._plain("I say further that the angle of the")
    if not any(at.startswith(angles) for at in dropped):
        nt.failures.append("III.16's angle clauses: review/III/16.toml declares no passage in "
                           "the run of `--` lines with no Lean beneath it that begins 'I say "
                           "further that the angle of the'; update this test")
        return
    record.write_text("".join(kept))
    try:
        nt.expect_failure("III.16's record without the passage on its angle clauses", nt.fidelity(),
                          "III.16: the `--` lines from 'I say further that the angle of the'")
    finally:
        record.write_text(saved)
