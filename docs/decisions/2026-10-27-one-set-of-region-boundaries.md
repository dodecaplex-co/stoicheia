- **The generated regions have one definition, in `scripts/heath.py`, which render.py,
  safe_push, the merge queue's judge and the negative suite all read (tooling,
  [#578](https://github.com/jackChallis/stoicheia/issues/578)).** render.py writes three
  hand-written files only between markers: README.md's scope summaries, PROGRAM.md's
  status table and WORKFLOW.md's section 8 block. Their boundaries were written out in
  four places, and the copies disagreed in detail. Two faults followed. A README.md whose
  scope markers were lost or broken rendered silently, and only acceptance B1 noticed it.
  And safe_push and the queue's judge dropped the markers along with the regions when
  they compared the hand-written rest, so a train deleting a whole region, markers and
  all, looked like a change to generated text alone. This is train 3 of the plan for
  compiling the shared pages, recorded on 27 October 2026
  ([#572](https://github.com/jackChallis/stoicheia/issues/572) and #578 are the
  coordinator's record of it): widening work, for which the hold on new guards in the
  landing tool is waived.

  What changes. heath.py's new section, "Generated regions", holds `GENERATED_WHOLE`, the
  files generated whole (facts.json, which `lake env lean Certificate/Facts.lean` writes,
  and book/, CERTIFICATE.md and GRAPH.md, which render.py writes), and `REGIONS`, the
  files render.py writes only between markers, with the pattern of each file's regions.
  PROGRAM.md's and WORKFLOW.md's markers must each stand on a line of their own, since
  WORKFLOW's prose quotes them inline. The section also holds the inline counts' marker
  tokens, moved from generated_counts.py. Four functions read the regions:
  - `regions(path, text)` refuses, with `RegionError`, any comment that looks like a
    marker but is not exactly one (in PROGRAM.md and WORKFLOW.md, one at a line's start),
    a marker's text inside a body, a closer with no opener, an opener with no closer,
    nesting, the same region twice, a README.md region for a book not in `BOOKS`, and a
    missing region (README.md needs one for each book of `BOOKS`).
  - `outside(path, text, counts=False)` gives the hand-written part, with each region's
    body emptied and its markers kept, and, with `counts`, each count's value emptied too.
    A region whose body holds a marker's text is left whole, as written by hand.
  - `bodies(path, text)` gives the generated part, the bodies `outside` empties.
  - `fill(path, text, write)` writes each body, refusing first what `regions` refuses,
    and then any write that would change a byte outside a body.

  heath.py is the home because safe_push's harness already carries origin/main's copy of
  it beside origin/main's safe_push.py. So the pre-flight reads origin/main's boundaries,
  never the commit's, and the harness needs no new module.

  The files, each a protected path changed here:
  - scripts/heath.py: the definition, and its self-check's plants (`REGION_PLANTS`),
    which `python3 scripts/heath.py`, a check of CI's `check` job, runs on today's three
    files. A deletion inside a region keeps the hand-written part as it was, and render.py
    writes the body back (`fill`, given today's bodies, gives back today's file). A
    deletion of a marker or of a whole region, or a marker's text put in a body, is
    refused, and a deletion of prose outside is seen.
  - scripts/render.py: README.md, PROGRAM.md and WORKFLOW.md are filled through
    `heath.fill`, all three before any file is written. A fault in their markers now stops
    the render with nothing written, where README.md's was silent.
  - scripts/generated_counts.py: its marker names and count tokens are now heath's, and a
    count marker inside WORKFLOW.md's checks block is refused, as one inside the other two
    regions already was.
  - scripts/registry.py: its `MARKERS` goes. It still imports nothing of the repository's,
    since safe_push runs origin/main's copy of it alone.
  - scripts/safe_push.py: `GENERATED` and `GENERATED_REGIONS` come from heath, with the
    same members. `generated_parts` compares `heath.bodies` and `heath.outside`, so a
    marker deleted or bent, or a region deleted with its markers, counts as a change to
    the hand-written rest.
  - scripts/check_queue.py: `hand_written_intact` reads the hand-written part through
    `heath.outside`, markers kept, for all three files, and `checkout` refuses a working
    copy whose hand-written part of any of them differs from the group head's, where it
    let the three differ whole.
  - scripts/negative_tests.py: its list of generated files comes from heath, and so now
    includes docs/WORKFLOW.md.
  - scripts/test_safe_push.py and tests/test_check_queue.py: the registry's tests read
    heath's region, and two new tests show that a region deleted with its markers is a
    change to the hand-written part, where the old reading saw none; a third shows that
    the queue's judge refuses a working copy's edit of README.md's prose, but not of a
    scope body, which the render freshness check catches.

  render.py now checks docs/program.toml and all three files' markers before it writes
  any file, and check_queue.py requires heath.py from its own directory, as it does
  safe_push.py and check_train.py. The patterns that find a marker's text read a run of
  spaces once, in linear time, and still run on Pythons older than 3.11. Every existing
  output renders byte for byte as before. The merge queue's lane, outside the repository,
  is to read `heath.REGIONS` and `heath.outside(path, text, counts=True)` from the main
  clone in place of its own copies.
