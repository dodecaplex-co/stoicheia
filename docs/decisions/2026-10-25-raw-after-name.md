- **The reader of Lean reads a name on through a `.` after its «…» part, as Lean does
  (tooling, [#430](https://github.com/jackChallis/stoicheia/issues/430)).** The review of
  the second train of [#349](https://github.com/jackChallis/stoicheia/issues/349), which
  brought the landing tool's `statement_end` to `heath.read_lean`, found that the reader
  took the `r"` after a dotted «…» part for the start of a raw string, as in
  `(h : «a».r"\") := " = s := rfl) : True := trivial`, and the same after `x.«b».` or
  `℃.`. Card #430, from that review, records the limit.
  The reader ended the name at the `»`, read the `.` alone, and began a raw string at the
  `r`: it read the raw string `\`, and `statement_end` ended that statement at
  `(h : «a».r"\") `. Lean 4.35's `identFnAux` reads a name's parts, plain or «…», joined
  by a `.` before a character that may begin one, so Lean reads the name `«a».r` and then
  the plain string `"\") := "`. It refuses the text, with "unexpected token; expected
  ')'" at the quote after the name, since an argument needs a space before it, so no file
  that builds holds it; but the reader read it otherwise all the same, and read an `s!`
  there as Lean's: `«a».s!"{"a"}"`, which Lean reads as the name `«a».s!`, the string
  `{`, the name `a` and the string `}`, the reader took for an interpolated string with a
  hole.

  Lean's readings. Each text was given to Lean 4.35, with `lake env lean`, in a scratch
  file outside the tree: in a declaration, as above, where Lean refused each of the six
  plants below at the quote after the name; and through commands declared for the probe,
  as `elab "probe " i:ident s:str : command`, which take a name and then a string with no
  space between them and log what Lean read. Lean read the names `«a».r`, `x.«b».r`,
  `℃.r`, `«a».«b».r`, `a℃.r`, `«a».s!`, `x.«b».s!` and `℃.s!`, each before a plain
  string, `"\") := "` as `") := ` and `"{"` as `{`; and `«a».r#"\") := "#` as the name
  `«a».r` and a `#`, which it refused. After `℃.`, what Lean reads rests on the tokens the
  file declares and on the parser that reads it. With a token `+℃` declared, a command
  that takes `"+℃" "." str` read `+℃.r"\"` as `+℃`, `.` and the raw string `\`, and a
  term read `+℃.s!"{1}"` as a projection with the field `s!`; with no such token, Lean
  read `+`, the name `℃.r` or `℃.s!`, and a plain string.

  The change is to `scripts/heath.py` alone. A «…» name is now read on through the parts
  after it, as Lean reads a name (`_name`): each part a run of the characters the reader
  takes for a name, or another «…» part to its `»`, joined by a `.` before a character
  that begins a name or a `«` (`NAME_GOES_ON`), so that an `r` or an `s!` after `«a».` or
  `x.«b».` is part of the name and the string after it is plain, as Lean reads them. A
  name that begins with plain parts is read by `IDENT`, as before, and the `.` and the «…»
  name after those parts as tokens of their own, which mark the text, and leave the scan,
  as one token would. After `℃.` the reader cannot know which way Lean reads, so there it
  fails closed, as it does after `℃` itself
  ([#234](https://github.com/jackChallis/stoicheia/issues/234)): `closed_up` now reads the
  run of name characters before an offset on through each `.` before a character that may
  begin a name (`DOTTED_RUN`), so that a raw string after `℃.` is marked as one the reader
  cannot read for certain, which `check_fidelity.py`'s `check_rules` refuses and before
  which `statement_end` runs to the end of the text, and an `s!` there begins no
  interpolated string. `IDENT` and `NAME_RUN`, which `check_fidelity.py` imports, are
  unchanged; `closed_up`, which it imports too, changes as above, and it calls it only
  through `read_lean`; and so is `comment_end`, which `risk.py` and the Jev generator hold
  word for word.

  The reader stays linear. A name with «…» parts is a token within which holes may begin,
  since a part may hold a `{` and a `"`. Read afresh in each such hole, a quote and then
  2000 parts `«{"»` joined by dots, 10,000 characters, took 0.75 seconds, where the reader
  on main took 0.017, and about four times as long at twice the length. So `_Ends`, which
  since [#390](https://github.com/jackChallis/stoicheia/issues/390) finds once where each
  string ends and each hole closes, now finds once where each name ends too
  (`_Ends.name`): each part a walk passes is remembered with where the name ends, as the
  places of a block comment are, so that no part is walked twice. With it, that text took
  0.010 seconds, against 0.013 for the reader on main in the same run; at 50,000
  characters, 0.054 and 0.069; and at 200,000, 0.22 and 0.29.

  The plants. Heath's self test, `python3 scripts/heath.py`, now reads six plants of
  names, `READER_NAMES`: the review's text, with its raw string after `«a».`, after
  `x.«b».` and after `℃.`, and the same three with `s!"{"a"}"` in place of the raw string.
  Each holds the offsets of what the reader cannot read for certain and the strings it
  reads: as Lean reads them after a «…» part; after `℃.` with the raw string marked; and
  in all three `s!` plants with the first string marked, since its braces could be holes.
  It gains a seventh plant against the clock, `READER_PLANTS`' last: the text of 2500
  parts above, which the reader on main reads as this one does. With main's reader put
  back into a scratch copy of the tree, under this self test, the self test fails on all
  six plants of names and passes the seven against the clock; with `_Ends.name`'s memory
  taken out, it fails on the seventh, at 1.19 to 1.38 seconds in three runs; with
  `closed_up` reading runs that stop at a `.`, on the two after `℃.`; and with
  `NAME_GOES_ON` matching nothing, on the four after a «…» part.

  The same readings. Main's `heath.py` at f3cfef05 and this train's read alike: on each
  of the 265 Lean files the repository tracks there, 3,009,505 characters, `read_lean`
  with `strings` gives one text, one list of unsure offsets and one list of strings with
  either reader, and `lean_comments` one list of comments; and safe_push's
  `statement_end`, with each reader in turn, gives the same statement for each of the 259
  `theorem PropN…` declarations in the 99 proposition files, none of which runs to the
  end of its text. Main at e974643c holds the same reader and the same Lean files.

  The times, on one machine with Python 3.14.2, this reader's and then main's, the best of
  five runs. #390's probes: 200 levels of `"{`, 0.0007 and 0.0007 seconds; 2000 levels,
  0.0074 and 0.0072; `"{"` written 4000 times, 0.0183 and 0.0181; `s!"{"` written 2400
  times, 0.0123 and 0.0123; 2000 closed levels of `s!"{`, 0.0150 and 0.0148; `"{/-"`
  written 2400 times, 0.0095 and 0.0095, and 9600 times, 0.0391 and 0.0394; and the
  refusal of 10,000 closed levels of `s!"{`, 0.0571 and 0.0569. Every Lean file the
  repository tracks, read with `read_lean` and `lean_comments` each: 1.031 and 1.029
  seconds. Of 22 shapes, each written out to about 12,000, 48,000 and 192,000 characters
  and timed best of three, eleven names of «…» parts holding quotes and braces, after a
  quote, an `s!"{` or nothing, two runs of `℃.`, #390's five runs and nests of string
  holes, and four runs of holes that open a name, the slowest at 192,000 characters,
  `"{` nested, took 0.41 seconds, as main's reader does, and none took more than about
  four times as long at four times the length but two, a long dotted run of `℃a` and a
  name after `x.`, which took 6.3 and 5.2 times as long at 192,000 characters, and 3.9
  and 4.0 times at 768,000 in a second run, as main's reader did. Of every text of up to
  four of the symbols `«`, `»`, `.`, `"`, `{`, `}`, `r` and `x`, written out to 6000
  characters after nothing, `"`, `"{` or `s!"{`, 18,720 texts timed best of two, the
  slowest took 0.018 seconds.

  Left open, for a card of its own: after a `.` that follows a term, Lean reads an `r` as
  a field, so that it read `(x).r"\") := "`, `p.1.r"\") := "` and `"a".r"\") := "`,
  through a command that takes a term and then a string, as a term ending in `.r` and the
  plain string `") := `, and `.r"\") := "` as the name `.r` and that string; in a
  declaration it refused each at the quote after the `r`. But with a token `).` declared,
  Lean read `(x).r"\"` as `(`, `x`, `).` and the raw string `\`, so there, as after `℃.`,
  its reading rests on the file's tokens. The reader still reads a raw string after such a
  `.`, and an `s!` there as Lean's. Those are no dotted names, and this change leaves them
  as they were; marking such a raw string, and such an `s!`'s string, as ones the reader
  cannot read for certain is the card's to weigh.

  This entry approves, in `scripts/heath.py`, the reader's reading of a name whole through
  its «…» parts (`_name`, `_part` and `NAME_GOES_ON`), `_Ends.name`, which finds once
  where each name ends that holes begin within, `closed_up`'s reading on through a `.`
  (`DOTTED_RUN`), the self test's six plants of names and its seventh plant against the
  clock, and the comments and docstrings that say so.