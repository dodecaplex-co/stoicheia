# Decision entries

The coordinator writes each new decision in `YYYY-MM-DD-slug.md`: a valid date followed
by a short name of lower-case letters and digits, with words separated by hyphens.
Each file holds the entry's text without a date heading.

[`render.py`](../../scripts/render.py) assembles the entries in filename order at the
end of the [decisions page](../briefs/0002-decisions.md), between its
`decisions:entries` markers. It supplies date headings and omits a heading that would
repeat the preceding one. Existing decisions stay on the page. The
[ownership rules](../WORKFLOW.md#4-files-and-ownership) apply to the generated entries.
