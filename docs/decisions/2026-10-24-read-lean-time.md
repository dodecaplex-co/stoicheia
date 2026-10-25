- **The reader of Lean finds where each string ends once, however its holes nest
  ([#390](https://github.com/jackChallis/stoicheia/issues/390)).** `heath.read_lean`,
  with `lean_comments` and `without_comments`, which share `_read_code`, reads a string
  literal that follows no `s!` or its kin two ways, plain and with its `{…}` holes, to see
  whether the two end in one place (#206). Until now it read the string with holes afresh
  wherever it met it, and that reading read every string in its holes again in the same
  way, its own two readings and all. A review of the second part of
  [#349](https://github.com/jackChallis/stoicheia/issues/349), the train that brought the
  landing tool's `statement_end` to this reader, found that its time therefore grew
  exponentially with the depth of nested holes, and as the square of the length of a long
  run of them. Timed on one machine with Python 3.14.2, the reader on main at c609656e
  took 0.014 seconds over 20 levels of `"{`, 0.098 over 24 and 0.653 over 28, about 1.6
  times as long for each level more, and was not done with 200 levels in 20 seconds;
  `"{"` written 4000 times, 12,000 characters, took it 6.62 seconds, and `s!"{"` written
  2400 times 3.05; and its recursion, three frames to a level, met Python's default limit
  of 1000 frames at a depth of 333, so that it raised RecursionError at once on 2000
  levels of `"{`. A run of holes that each open a block comment was slow another way, as
  the review of this change's first form found: each hole walked its comment to the end of
  the text, so that `"{/-"` written 2400 times took that reader 1.17 seconds, and written
  9600 times, 48,000 characters, 18.8. The checks read Lean's comments and literals with
  this reader, and so does the landing tool's guard that no statement changed, so a few
  kilobytes of Lean could stall either, or stop it.

  The change is to `scripts/heath.py` alone, and changes nothing the reader reads but for
  one refusal, of strings nested past a budget (below). A new class, `_Ends`, finds for the
  text read where each string ends and which way it is read, and where each hole closes,
  each once: the end of a reading with holes once for each place where its text goes on,
  just after the opening quote or a hole's `}`, and the close of a hole once for each
  place, and state of the scan, that the code of a hole passes through. The scan's tokens
  from a place rest only on that place, on whether the token before it is one of `s!`,
  `m!`, `f!` and `throwError`, and on the scan's two flags for projections, `can_project`
  and `field_dot`, never on how deep in braces the scan is; so two scans that meet go on
  as one, each place waits at its depth for the `}` that closes that depth, and a scan that
  reaches a place whose close is known goes straight to it. A hole may also begin within a
  comment, a raw string or a «…» name that an earlier hole reads whole, as each hole of
  `"{/-"` begins within the block that the hole before it opens; so the scan of holes
  takes where such a token ends from `_Ends` too. A block's end comes from a walk that
  passes no place twice, each place waiting at its depth for the `-/` that closes it as a
  hole's places wait for its `}`; a line comment's end, a name's `»` and a raw string's
  closing `"` and `#`s come from a list of their offsets, made in one pass over the text
  for each closer. The reading that writes the marks, which passes each place once, finds
  them with `comment_end` and `_find`, and `comment_end`, which the Jev generator and
  risk.py hold word for word, is unchanged. A name stands as the token before what follows
  by its `«` alone, not its whole text, since all that is asked of that token is whether
  it is `s!` or its kin. Where a string's text ends, read plain or with holes, comes from
  one list, found once, of the `"` and `{` that no `\` escapes. The reading that writes
  the marks then reads each string only the way `_Ends` found it is read, and its holes
  only when it is read with them. Both run as generators on a stack of the reader's own,
  not on Python's, so that no depth of holes reaches the recursion limit. `_read_code`,
  `_read_string` and `_read_interpolated` keep their names and arguments, since
  `check_fidelity.py` imports all three and calls `_read_code`.

  With `strings`, `read_lean` gives each string's text too, and a string's text holds its
  holes and every string within them, so that those texts grow as the square of the depth
  of nesting: 20,000 closed levels of `s!"{`, 120,000 characters, came to 1.2 billion
  characters, and the review of the first form measured a peak of 1.40 GB of memory,
  where the old reader raised RecursionError at once. So `read_lean` now refuses, with
  ValueError and before it builds them, a text whose strings, each counted from its
  opening quote past its closing one, a raw string by its text, come to more than 1024
  characters for each of its own and 2²⁴ more (`STRINGS_PER_CHARACTER` and
  `STRINGS_SPARE`). They come to at most the
  text's length times the depth to which its strings nest, so the budget admits strings
  nested 1024 deep in any text, three times the depth at which the old reader stopped,
  and refuses no text it could read. The repository's Lean comes to at most 0.176
  characters for each of its own (`Elements/Companions.lean`, 560 of 3182, at c609656e),
  and 2000 closed levels in 12,000 characters, one of the plants below, to 12,002,000.
  The budget counts characters, not bytes: where a string holds a character outside the
  Basic Multilingual Plane, Python keeps 4 bytes for each of its characters, so the
  strings' texts may still take some 4 KB of memory for each character of the source (a
  4 MB text of that kind peaked at 4.0 GB in the review of this form), where the old
  reader stopped at once; the refusal still fails closed past the budget.
  Both callers outside the tests that pass `strings` fail closed on the refusal: `check_fidelity.py`'s
  `check_rules` lets it end the check with a traceback and exit status 1, as it did in a
  scratch run that read 10,000 such levels in place of `Elements/Companions.lean`; and
  the landing tool's `statement_end`, which its guards call before anything is pushed or
  merged, lets it end the pre-flight or the merge with an error.

  It is exact. Where a string's reading with holes ends rests only on its offset, where a
  hole closes only on where its code begins, and where a comment, a raw string or a name
  ends only on where it begins, so the old reader computed the same values over and over;
  and it threw away the marks of every reading it did not choose, so the marks of the
  readings chosen are the marks it gave. Main's `heath.py` at c609656e and this train's,
  as the scratch evidence ran it (blob 7ea023e4), give the same `read_lean(src, strings)`,
  its text, its unsure offsets and its strings, and the same `lean_comments(src)`: on
  each of the 265 Lean files the repository tracks at c609656e, 3,005,301 characters, and
  on each cut short at every multiple of 997 characters; on every text of 0 to 8 symbols
  drawn from `"`, `{`, `}`, `\`, `'`, `-`, `/`, `s!`, `a`, a line feed and a space,
  235,794,769 texts in all; on every text of 0 to 7 symbols drawn from `"`, `{`, `}`, `\`,
  `.`, `1`, `s!`, `r#`, `«`, `¹` and a space, 21,435,888 more, for the numbers,
  projections, raw strings and names among the holes; on every text of 0 to 6 symbols
  drawn from 23, `"`, `{`, `}`, `\`, `'`, `--`, `/-`, `-/`, `s!`, `m!`, `throwError`,
  `r#"`, `"#`, `«`, `»`, `.`, `1`, `x`, `¹`, `℃`, a line feed, a space and a carriage
  return, 154,764,793 more; on every text of 0 to 7 symbols drawn from `"`, `{`, `}`, `/`,
  `-`, `/-`, `-/` and `x`, 2,396,745, for blocks within holes, and of 0 to 6 drawn from
  `"`, `{`, `}`, `--`, a line feed, `«`, `»`, `r#"`, `"#`, `r"` and `x`, 1,948,717, for
  line comments, names and raw strings within them; on 600,000 random texts of up to 40
  of the 23 symbols, and 200,000 of up to 60 from those and 27 more, as `0x`, `·`, `'"'`
  and `f!`; and on 600,000 texts of up to 400 characters built of strings and holes
  nested up to six deep, with comments, character literals, raw strings and names, then
  cut and spliced at random. On half of the random texts of the 23 symbols, and half of
  the built ones, `_read_code` from each offset and in each hole, `_read_string` both
  ways and `_read_interpolated` at each `"` gave the same values and marks as well; and
  under Python 3.12.9 the same held of 100,000 more built texts, and 100,000 more random
  ones with those readings. No text differed. The comparison found each of three faults
  planted in the new walks, a block closed a character short, a wrong close taken from a
  block's memory, and a closer found past one at the very place sought, on 324 to 1,498
  of 30,000 built texts. Where the old reader raised RecursionError, the new one reads, up
  to the budget for `strings`; the self test holds two such plants, and the one it must
  refuse.

  The new reader read 200 levels of `"{` in 0.0008 seconds and 2000 in 0.0077, `"{"`
  written 4000 times in 0.018, `s!"{"` written 2400 times in 0.013, 2000 closed levels of
  `s!"{` in 0.016, and `"{/-"` written 2400 times in 0.0097 and 9600 times in 0.039; and
  it refused 10,000 closed levels of `s!"{` in 0.060. Of 44 shapes, each written out to
  12,000 and to 48,000 characters, runs of string holes nested and flat, with comments,
  raw strings, names, character literals, numbers, escapes and stray braces and quotes,
  the slowest took 0.025 and 0.103 seconds, and none took more than 4.3 times as long at
  four times the length. At about a megabyte, runs of holes that each open a block, a
  line comment, a name or a raw string took 0.70 to 0.84 seconds. One shape stays above
  linear: raw strings within holes, each closed by a different number of `#`s, for each
  of which the scan of holes lists the offsets of its closer in one pass over the text.
  A text of n characters holds at most about √(2n) such numbers; a megabyte of them took
  0.80 seconds, where the old reader, which looked for each closer from its hole on, took
  0.59, and 4 MB took 6.1. The new reader read every Lean file at c609656e, with
  `read_lean` and `lean_comments` each, in 0.99 to 1.00 seconds, where the old reader
  took 1.12 to 1.13.

  Heath's self test, `python3 scripts/heath.py` (its entry in `checks/` is unchanged),
  now reads six plants, `READER_PLANTS`, each in a child process given 20 seconds, which
  must finish in under half a second and read as the old reader reads it, or reads it made
  smaller where it cannot: the offsets of the strings it cannot read for certain, those of
  its strings in order, and its first string's text. A seventh, `READER_REFUSED`, 10,000
  closed levels of `s!"{`, it must refuse, as quickly. With the old reader planted back
  into a scratch copy of the new file, the self test fails on all seven: the first was not
  done in 20 seconds, the next two took 6.49 and 2.90 seconds, the fourth, the fifth and
  the seventh raised RecursionError, and the sixth took 1.17 seconds. With this change's
  first form planted back, it fails on the sixth, at 1.17 seconds, and on the seventh,
  which that form reads; with the budget alone taken out, on the seventh. Two readers
  that are fast but wrong, one that never reads a string with holes and one that ends
  each plain string a character early, fail it on two plants and on five. The test is
  heath's own rather than a new file under `tests/`, because the contracts of `heath.py`
  are checked there already, and a new entry in `checks/` would also change the list of
  checks that WORKFLOW's section 8 generates.

  This entry approves the change to `scripts/heath.py`: its reader of Lean finds each
  string's end and each hole's close once, on a stack of its own, finds once where each
  comment, raw string or name ends that holes begin within, refuses strings nested past
  their budget, and its self test reads six plants of deep and long runs of string holes
  against the clock and must refuse a seventh.
