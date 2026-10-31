<!--
Stoicheia's pull request template (docs/WORKFLOW.md, "Landing work: pull requests").
`git safe-push --branch <name>` (origin/main's scripts/safe_push.py) fills the places
marked `safe_push` and writes its pre-flight summary between the preflight markers; the
coordinator writes the rest. `git safe-push --merge <n>` refuses while a box marked
**Required** is unticked, or one marked **Required if protected** when a protected path
changes, or one marked **Required if code** unless the change is of Markdown files alone,
of R0 or R1 by current main's `scripts/risk.py`, while a required box of this template is
missing from the body, and while "What and why", a row of the Reviews table (the security
review's when a protected path changes, and `/no-mistakes`'s when the change counts as
code or is protected), "Unfinished work" or "Needs the owner's OK" is unwritten, or an
issue named under "Unfinished work" is not open with blocks-release. A pull request
labelled release is refused while any blocks-release issue is open. Boxes and other
sections count where GitHub shows them; "Unfinished work" is checked as raw text, as
docs/WORKFLOW.md says under "The merge".
-->

## What and why

<!-- One coherent change, in your words, above the commits safe_push lists. Link the brief
and the decision it carries out: a section of docs/briefs/, and its decision entry in
docs/decisions/ (docs/WORKFLOW.md, "Decision entries"), or an earlier entry of
docs/briefs/0002-decisions.md. A check is never changed in the same pull request as the
code it checks. -->

<!-- safe_push: commits -->

## Statements changed

<!-- Each statement changed, and the brief revision or decisions entry that approves it;
or "None". -->

<!-- safe_push: statements -->

## Unfinished work

<!-- Each piece of unfinished work this pull request lands: a prototype, a provisional
answer, a restricted or partial scope awaiting a proof, a deferred page, a test not yet
in CI, anything a disclosure calls "to come". Name each with its open issue labelled
blocks-release, as #N; or write "None". Plain ASCII text, read as written: a list, each
item "- " or "* " at the left edge, wrapped with two to five spaces, naming one or more
issues as #N; no links, code, HTML, other comments or headings, and no other line of the
body may begin with these two words of the heading. This comment may stay, on lines of
its own. -->

## Review records

<!-- Each record touched, and whether it was re-stamped: by whom, at which commit; or that it gained only its `text` stamp from `scripts/review_stamp.py --migrate-text`. -->

<!-- safe_push: records -->

## Protected paths

<!-- The paths docs/WORKFLOW.md lists under "Protected paths": each changed file is named
in a decisions entry, and the pull request carries the label security-review. -->

<!-- safe_push: protected -->

## Checks run on the exact commit

<!-- The pre-flight's summary, as safe_push.py wrote it; it is replaced, never edited. -->

<!-- safe_push: preflight -->

## Reviews

<!-- /code-review always; /security-review when a protected path changes; /no-mistakes
before merge, without its push and pull request steps (git safe-push does those), unless
the change is of Markdown files alone, of R0 or R1 by scripts/risk.py: such a change has
a second reader instead, recorded in the /code-review row, and the /no-mistakes row says
"Not needed". Give the commit each ran on, and how each blocking or material finding was
resolved (docs/WORKFLOW.md, section 9). -->

| Review | Commit | Blocking or material findings, and how each was resolved |
|---|---|---|
| /code-review | | |
| /security-review | | |
| /no-mistakes | | |

## Generated files

<!-- Regenerated from the integrated sources and committed by the integrator
(docs/WORKFLOW.md, section 4). -->

<!-- safe_push: generated -->

## Needs the owner's OK

<!-- Anything public the pull request leads to: a tag, a release or its notes, the GitHub
description, anything sent outside the repository. Quote the owner's OK, or write
"Nothing". -->

## Checklist

- [ ] **Required:** One coherent change, and no check changed together with the code it checks.
- [ ] **Required:** The checks above are safe_push.py's pre-flight of this pull request's head commit.
- [ ] **Required:** Each statement changed is named in its approving brief revision or decisions entry, or none changed.
- [ ] **Required:** Each piece of unfinished work is named under "Unfinished work" with its open issue labelled blocks-release, or there is none.
- [ ] **Required:** Each review record touched was re-stamped by its reviewer, or gained only its `text` stamp from `scripts/review_stamp.py --migrate-text`, or none was touched.
- [ ] **Required:** /code-review was run, and each blocking or material finding is resolved above.
- [ ] **Required if protected:** /security-review was run, and each blocking or material finding is resolved above.
- [ ] **Required if code:** /no-mistakes was run before merge, and each blocking or material finding is resolved above.
- [ ] **Required:** Generated files were regenerated by the integrator, or none changed.
- [ ] **Required:** Nothing public goes out without the owner's OK.
