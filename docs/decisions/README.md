# Decision entries

*Each decision written after the decisions page's entry of 20 October 2026, "Decision
entries, one file each", is a file of its own here. That entry and those before it are on
[the decisions page](../briefs/0002-decisions.md), as are the entries that pull requests
opened before it landed add there.*

An entry records one decision: what was decided, and why. Its file is named
`<YYYY-MM-DD>-<slug>.md`, the day of the decision and then a short name of lower-case
letters and digits joined by hyphens, as `2026-10-21-entry-files.md`. The name carries the
date, so an entry needs no date heading; and GitHub lists this folder in name order, which
is date order, with the newest entries at the bottom, as on the decisions page.

Entries are dated history, and are never edited. A correction is a new entry, in words of
its own, naming the entry it corrects; a revert is a new entry too, and the entry of the
change it undoes stays. The pre-flight refuses a change, a deletion or a move of an entry
that main already holds.

An entry names each file, statement and lock it approves in a sentence of its own, never
on a line or in a list repeated from an older entry or the decisions page: the pre-flight
counts a line of an entry only when the decisions record holds neither that line nor a
run of 12 or more of its words, read in capitals or small letters alike, with Cyrillic and
Greek letters that look like Latin ones read as those, and blanks as spaces. So a copy of
an older entry, re-wrapped, recased or written in those look-alike letters, approves
nothing, though it is not refused for being one; a copy reworded, or with words put in,
is beyond that comparison, and is for the reviews to find. A refusal names each line that
did not count, and why. Lines added to the decisions page are not compared so: they count
as any new line does, as they always have.

This README is no entry, and stays the same from one entry to the next. How to write an
entry, and what one may not hold, is in
[WORKFLOW, "Landing work: pull requests"](../WORKFLOW.md#landing-work-pull-requests), under
"Decision entries".
