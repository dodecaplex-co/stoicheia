<!-- entry: id=entry-header-and-notes cards=577 line="Decision entries carry a header line, and render.py compiles the briefs' and PROGRAM.md's notes from it." -->
- **Decision entries carry a header line, and `render.py` compiles the notes of the briefs
  and of PROGRAM.md from it (checks,
  [#577](https://github.com/jackChallis/stoicheia/issues/577)).** The coordinator's orders
  of 27 October 2026 assign card #577 under the plan the owner approved on 27 October 2026.
  The orders give the plan's aim as each thing said once, in a file of its own, with its
  restatements compiled. Trains have kept adding a dated status paragraph to a brief, each
  at the same spot (brief 0008 holds six), and the same news again in PROGRAM.md, so two
  trains in flight collide there.
  Each train already writes an entry of its own in this folder, and entries never collide.
  So an entry now says, in a header line, what it is news for, and `render.py` writes the
  notes of the briefs and of PROGRAM.md from those headers.

  The header is the entry's line 1, a comment GitHub does not show; its form and rules are
  in [WORKFLOW](../WORKFLOW.md), section 10, "Decision entries", and this entry is the
  first to begin with one. It gives an id, the entry's cards, the briefs and the sections of
  PROGRAM.md it is news for, the earlier entries it corrects or reverts, and its news, in
  one line. `render.py` refuses, naming the file and the line, anything but the exact
  form, and each refusal has its reason:

  - keys out of their order, twice, unknown or with extra spaces, and a comment that does
    not close on line 1 or has text after it: so a header reads one way only, and every
    tool that reads one later reads it alike;
  - a header over 2,000 characters, before it is parsed: so no header costs a reader
    much;
  - an id that is not lower-case letters and digits joined by hyphens, or that another
    header bears: so an id names one entry;
  - a card that is not an issue number, with no leading zero: so each card links to an
    issue;
  - a brief that `docs/briefs/` does not hold, or the decisions page, which is dated
    history and holds no notes; and a section of PROGRAM.md that is not in a fixed list,
    which `render.py` and the regions' reader share and which names no heading of
    PROGRAM's, so renaming a heading never breaks an entry, which is never edited. The
    list is `landed` alone: entries are only ever added, so a region of them only grows,
    and a section whose items leave it, as PROGRAM's open items do, would need a way for
    an entry to close an earlier entry's item, which the header does not have;
  - a correction or a revert of anything but an earlier entry, in name order, which may
    have a header or none: so an entry never corrects itself, a later entry, the README or
    a file that is not there;
  - an item named twice in a list, or an empty one;
  - a line empty or over 300 characters, with a space at either end, or holding a double
    quote, which would end it, a comment's opener or closer, which would hide part of the
    page it is copied into, a Markdown link, since the line is copied into pages in other
    folders, where a relative link would break, or a `<`, `[` or `]`, since raw HTML could
    hide text or link to a file, and a bracket could bind to a link that page defines;
  - a header anywhere but at the start of line 1, or a second one: so none is passed over.

  A brief may hold one notes region, between `<!-- notes -->` and `<!-- /notes -->`, and
  PROGRAM.md one for each section of the list, between `<!-- notes:landed -->` and
  `<!-- /notes:landed -->` and their like, each marker on a line of its own. Between them
  `render.py` writes a line for each entry whose header names the brief or the section,
  sorted by the entries' file names, so by date and then by name: the date, the cards in
  numeric order, the news, a sentence for what the entry corrects or reverts and for every
  entry whose header corrects or reverts it, whatever that entry names, each linked, and a
  link to the entry. A region holds those lines and nothing else, so that a misplaced
  marker never swallows text written by hand: any other line between the markers stops
  the render, naming the file and the line. Where no markers stand it writes nothing, so
  every page renders today as it did. A bad marker, or a count marker inside a region,
  stops the render before it writes.

  Old entries are not given headers: `render.py` checks a header where one stands and
  requires none, and WORKFLOW asks every new entry for one. The markers come with card
  #579's migrations; this change places none. Until card #578 teaches the pre-flight the
  notes regions, a line `render.py` writes into a brief is read by the pre-flight as a new
  hand-written line there, which counts as an approval where it names a statement; so no
  notes marker is placed before #578 lands.

  This entry approves the change to [`scripts/render.py`](../../scripts/render.py) that
  reads and checks each entry's header and fills the notes regions after every check has
  passed, refusing a region that holds a line it does not write.

  This entry approves the change to
  [`scripts/generated_counts.py`](../../scripts/generated_counts.py) that adds the notes
  regions' reader, kept beside the other regions' patterns, and refuses a count marker
  inside a notes region.

  This entry approves the change to
  [`tests/test_decision_entries.py`](../../tests/test_decision_entries.py) that tests the
  header, each of its refusals, the notes lines, their markers and the lines a region may
  hold, and a whole render, which changes no file until markers are planted.

  This entry approves the change to
  [`tests/test_generated_counts.py`](../../tests/test_generated_counts.py) that refuses a
  count marker in a brief's notes region and in each region of PROGRAM.md, and a section
  of PROGRAM.md not in the list.

  This entry approves the changes to [`docs/WORKFLOW.md`](../WORKFLOW.md) that describe
  the header and the notes regions in section 10, add them to what section 8 checks, and
  add the regions to the integrator's files, a table of the shared hand-written files and
  their subject owners, and what the landing lane's intake refuses, to section 4.

  No Lean file, statement, definition, lock, record, brief or `--` line changes.
