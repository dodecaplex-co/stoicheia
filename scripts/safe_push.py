#!/usr/bin/env python3
"""The pre-flight of a pull request, and its merge: the way work reaches main.

    git safe-push --branch <name> [--label L]... [--title T] [--body-file F] [--ready]
                  [--land] [--commit <sha>] [--dry-run] [--main-checks-cache]
    git safe-push --merge <pr-number> [--dry-run]
    git safe-push --dry-run [--commit <sha>] [--main-checks-cache]  # the checks alone

`git safe-push` is the launcher scripts/install_hooks.sh installs outside the tracked
tree (scripts/hooks/safe-push): it runs origin/main's copy of this file, whatever the
checkout holds. `python3 scripts/safe_push.py ...` runs the checkout's copy, which hands
over to origin/main's when it differs; that holds only while the copy run is one that
hands over, so the launcher is the way in.

Nothing is pushed to main: main changes only by a pull request's merge commit
(docs/WORKFLOW.md, "Landing work: pull requests"). Run with none of --branch, --merge
and --dry-run, the script refuses, and says to use --branch.

The pre-flight (--branch) checks one commit (HEAD unless --commit names another) from end
to end, reading nothing from the working tree, and only then pushes it to
refs/heads/<name> and opens the pull request, or updates the open one. The steps run in
order, and the first that fails stops it with a message saying why:

1. Preconditions. The commit exists; `git fetch origin`; origin/main is an ancestor of
   the commit, so that the merge commit will hold exactly the tree checked; the branch,
   if origin has it, is an ancestor too, for nothing is ever forced; the branch is not
   main; the branch name and the title hold nothing the scan refuses. The harness is
   origin/main's: when this copy of safe_push.py or heath.py, or the check_train.py
   beside it, differs from origin/main's, origin/main's replaces this process
   (os.execve), so that a branch cannot weaken the guards that judge it, and an
   interruption reaches the copy that pushed.
2. A secret scan of every line the push adds, of every file it adds or changes, of its
   commit messages, and of each commit's author and committer, and then of each commit's
   own change, since the push publishes the history: a secret added and taken out again,
   or a key file added and then renamed, is found in the commit that brings it. It looks
   for private keys, API-key-like tokens, Authorization headers with values, `.env` and
   key files, the owner's private paths (an agent's scratchpad among them) and
   machine-made identities: in each line, across consecutive lines, inside base64 that
   decodes to text, and in symlinks, which may not point out of the repository. Whether
   a file is text or binary is read from its bytes (a NUL anywhere makes it binary, and
   a binary file is read whole: its printable runs and its UTF-16 runs, wherever they
   stand), and the diff is read as text, so a .gitattributes line cannot take a file out
   of the scan. A false positive goes in origin/main's `scripts/safe_push_allow.toml`:
   one file, one rule, a part of the line, and the flagged value itself, pinned (held in
   that part, or named by its SHA-256), to an entry, with its reason. A commit's message
   or identity cannot be allowed, and an entry added by the push itself does not count.
   An allowed finding is noted in the pull request by its place, its rule, its value's
   SHA-256 and the reason, never by its line. Every git command safe_push.py runs itself
   (run()) reads with git's replacement objects off, whatever the caller's environment
   holds, since a push sends the originals (#256); its `git status` check is one of them.
   The programs it runs as checks are not: they keep the environment tool_env() copies,
   which holds GIT_NO_REPLACE_OBJECTS under the launcher or after a hand-over, and
   otherwise only if the caller set it, and of git's other variables only the four that
   name its global and system configuration files or shut them, or the system attributes
   file, out (CONFIG_FILE_VARIABLES), which tie git to no repository: so a check finds
   its repository by its working directory, never by a hook's GIT_DIR (#355), and reads
   the configuration files that safe_push.py's own git reads, save one named by a
   relative path, which tool_env() drops (#430). Nor does any command safe_push.py runs
   itself, git's or another's, get a variable that ties git to one repository
   (REPOSITORY_VARIABLES: GIT_DIR, GIT_INDEX_FILE, GIT_WORK_TREE and their kin, as `git
   rev-parse --local-env-vars` lists them) from the caller, but GIT_NO_REPLACE_OBJECTS
   as above: each finds its repository by its working directory too, the hand-over's
   included (#357), but main()'s one git rev-parse before any step, which is given the
   caller's GIT_DIR and GIT_WORK_TREE on its command line, as --git-dir= and
   --work-tree=, to see the repository they name (#186). The harness sets one itself,
   on purpose: base_tree's temporary GIT_INDEX_FILE, named to run() in `keep`.
3. Invariant guards against origin/main. First, before the commit is checked out, the
   paths guards. They read the tree of each commit the push brings (origin/main..the
   commit), each tree once, and a finding names, for each tree that holds it, the first
   commit with that tree, at most three and then "and N more":
   - every path is plain printable ASCII, with no space; no two paths, nor two folders of
     them, are one name once casefolded and NFC-normalised, as a case-insensitive disk
     (macOS's default) compares them; and none is a protected path or a check input
     spelt otherwise (LAKEFILE.lean, Scripts/x.py): such a twin, as certificate/FIELDS.md
     beside Certificate/FIELDS.md, or Scripts/json.py beside scripts/, is checked out
     over the file or into the folder the protected paths and the check inputs name,
     unseen by both;
   - every path keeps origin/main's own standard (docs/WORKFLOW.md, "File names"):
     origin/main's scripts/check_paths.py, read from its blob and run in this process,
     judges each tree, before any of the commit's code has run, and refuses when it does
     not load or fails on a tree. When origin/main has no check_paths.py, as before the
     pull request that brings it, a note says so.
   They read the trees, which such a disk cannot hold, and when they refuse, no worktree
   is made. Then, in a fresh temporary worktree of the commit, the guards below. A
   new decision is a dated entry of its own, docs/decisions/<YYYY-MM-DD>-<slug>.md, which
   the push adds (docs/WORKFLOW.md, section 10, "Decision entries"); 0002-decisions.md,
   the decisions page, holds the entries written before that rule, and a pull request
   opened before it may still add one there, whose new lines count as any new line does.
   The page and the entries are the decisions record:
   - every statement (facts.json's `statement`, and the Lean source of `theorem PropN`,
     its porism and its companions, up to its own `:=`, whitespace aside) is unchanged,
     unless the push adds a new line to `docs/briefs/`, or to an entry, naming it;
   - `Certificate/axioms.lock` is unchanged, unless the decisions record gains a new line
     mentioning the lock;
   - a protected path (PROTECTED, below, as docs/WORKFLOW.md lists them) changes only
     with a new line in the decisions record naming each file changed by its whole path,
     at either end, a relative link resolving from the folder of the file that holds it
     (names_path), a mention starting the text or following whitespace or one of
     ( < [ ` " ' * (mention), and the pull request then carries the label
     `security-review`;
   - every changed file under `heath/` carries, in the change, a comment naming a scan
     leaf of its own pages, as origin/main's copy of the file lists them;
   - no review record is stale, and the generated pages are current (check_fidelity.py
     and render.py, on the commit as committed);
   - the commit's registry of checks reads, by the commit's own scripts/registry.py, as
     the pre-flight of every later train will read it once the commit is origin/main's
     (guard_registry): render.py and CI load the reader from scripts/ and read the
     worktree, so a reader that works only so would pass them both;
   - no whole directory under Elements/, heath/, review/, figures/ or mishnah/ is
     deleted unless the decisions record gains a new line naming it, as a protected path
     is named;
   - docs/decisions/ holds regular files alone, its README.md, which once added stays,
     and dated entries, each dated from FIRST_ENTRY to the day after the earlier of the
     commit's committer date and the runner's own date; an entry is only added: none
     there at origin/main is changed, deleted or renamed; and no path the commit changes
     is spelled otherwise than docs/decisions/ where a Mac's file system reads it as that
     folder (entry_changes).
   A new line here is a mention the push adds: an old line that already named the
   thing, edited in place, does not count. A line of a dated entry the push adds counts
   only when the decisions record held none like it, nor a run of SHARED_RUN of its
   words, each read as `skeleton` reads it (entry_lines); a guard that refuses names
   each line of an entry that did not count and in which its own reading finds a mention
   of what it asks for, and why (uncounted). That comparison is for entries alone: a
   line added to the page is compared with nothing, and any new line there counts, but
   its mentions are read by the same rules as an entry's (mention, names_path). A
   branch named train/* requires --body-file, and step "3. train" then runs
   origin/main's check_train.py on the commit and that body, before the full checks;
   while origin/main has none, every train is refused, and no commit's own copy runs in
   its place.
4. First the change's risk class (risk_class), from R0 to R5, as origin/main's
   scripts/risk.py gives it for `git diff origin/main...<commit>`: its copy at
   origin/main, read out of git and run from a temporary directory, never the commit's, so
   that a change cannot lower its own class by editing the classifier. A pull request
   labelled release (given with --label, or on the open pull request) is R5, a label only
   ever raising the class; so is a base with no scripts/risk.py, and any failure to
   compute the class. The class and why are a step line, and the record's "class". For
   R0 to R2 the rest of this step is skipped: CI runs the rest of section 8's sequence on
   the pull request before the merge, and --merge waits for CI green, while the negative
   tests run on main after the merge and on the cadence
   (docs/decisions/2026-10-22-checks-by-risk.md); one "skip" line says so. Such a change
   touches no check input and no protected path but
   judged content (beyond_low), so keep_apart cannot arise; should origin/main's risk.py
   ever class one that does R0 to R2, the full checks run. For R3 to R5, the full check
   sequence of docs/WORKFLOW.md, section 8, in that worktree, and
   `negative_tests.py` in a second one, each step timed. The sequence is CI's `check`
   job's as origin/main's registry of checks lists it (checks/, one file per check, read
   out of git by origin/main's scripts/registry.py, run from a temporary directory: never
   the commit's registry or reader, so that a change cannot alter the checks its own
   pre-flight runs), then the `model` job's (check_sequence;
   docs/decisions/2026-10-22-check-registry.md).
   While origin/main holds no registry, the lists built in here stand in for it; when it
   holds one that cannot be read, the pre-flight refuses. The checks run with
   origin/main's copies of the check scripts and their expected values (CHECK_INPUTS,
   below); when the commit changes any of those, they run again with the commit's own
   copies, which must pass. A check that fails with origin/main's copies is noted for the
   security review, and refuses the commit when it also changes what the checks judge
   (keep_apart, below): a check change lands in a pull request of its own, before the
   code it checks. Step 3 has already judged every commit's tree by origin/main's standard
   for paths, before any of the commit's code ran; as a second line, a failure here of
   origin/main's path check (check_paths.py and its cases) refuses the commit whatever
   else it changes: every path is what it judges, so a looser check cannot land with the
   path it would let in. Each pass begins with the worktree at the commit, or is refused,
   since the commit's code may have run in an earlier one: its HEAD the commit, its index
   the commit's tree, no file flagged skip-worktree or assume-unchanged (either keeps git
   from looking at the file on disk), and `git status --porcelain --untracked-files=all`
   empty, each asked of git with stat settings at their defaults, no fsmonitor, untracked
   cache or hook, and, as the worktrees are made, file modes compared and no conversion or
   attributes but the system's (attr.tree the empty tree), whatever the shared .git/config
   says, and refused while the shared .git/info/attributes exists; then every ignored file
   is removed but the build's caches, .lake/ and model/.lake/, a channel the commit's
   build already has (#197). This asks git and compares no bytes, so routes past it remain
   (a hand-edited index, a process left running, a .git below the root among them; #218),
   each needing code of this commit or one checked before to have run first, through a
   change to a protected script or its Lean at elaboration (#197). origin/main's copies
   are taken out again by a reset to the commit. Two kinds of failure are not a check's
   verdict, and are noted only:
   pages gone stale under origin/main's render.py (or facts.json rewritten by its
   certificate), which the pages' diff shows in full; and a failure on a commit whose
   only check inputs changed are values pinned to the edition (PINNED, below; the
   certificate's expectations only while none of origin/main's is dropped or loosened;
   the model's law names, and a law's code in the two harnesses that check every law
   (MODEL_LAW_CODE), only while each law changed moves with its axiom; the Markdown of
   the check inputs that are not code (COUNTED_PROSE) only while nothing but the values
   between its count markers changes, and the model's page, whose prose may change too,
   only while its count markers stand), which move with the content they pin. A crash of
   origin/main's render.py, its check of docs/program.toml among them, is a verdict.
   Step 3's two checks run the same way. With --main-checks-cache, for R3 to R5 (the
   classes that run this step in full), but not on a train/* branch, whose train check
   runs in this process after the commit's code (open_cache), origin/main's pass here
   (both its loops) is
   reused from ~/.cache/stoicheia/main-checks/ when an earlier run checked the same trees
   with the same harness, toolchain and environment (main_checks_fields). After the
   class is read and origin/main's count-marker reader is loaded, every command the run
   starts runs under sandbox-exec, which stops it writing that directory (open_cache);
   without the sandbox, there is no cache. It does not stop a run without the flag, nor
   code run as the user outside a flagged run, nor what a flagged run's code leaves for
   a later command or a later run to load before its sandbox starts (run).
5. The pull request settled first: our open one for the branch (a fork's of the same
   name is never touched), or a new one; its body, --body-file or generated from
   .github/pull_request_template.md (the commits, the statements, the review records
   touched, the generated files, the protected paths, and the pre-flight's summary, each
   between its markers, each on a line of its own; on an update without --body-file,
   each marked part is written afresh and the coordinator's words are left as they are,
   a marker they quote among them), scanned. Then
   `git push origin <sha>:refs/heads/<name>`, never forced; then `gh pr create --base
   main --head <name>`, a draft unless --ready, or `gh pr edit` of the open one; then its
   CI, followed to its conclusion (`gh pr checks --watch`). Its label for its kind
   (tooling, text, lean or docs), given or already on the open one, is settled in step 1,
   before the checks; a dry run, which does not ask GitHub, notes a missing one.
6. A summary, printed and appended to `~/.cache/stoicheia/pushes.log`, outside the
   repository (`STOICHEIA_PUSH_LOG` names another file); each step's output is kept
   beside it in `logs/`, and the pre-flight's record in `preflight/`, for --merge.

--merge <n> merges a pull request only when its head passes the secret scan and the
guards against the current origin/main, run again then (a record of the pre-flight is a
local file, so it stands in for the full checks alone, and only when origin/main's
harness made it; a record that left them to CI for its class, only while the class,
recomputed then by origin/main's risk.py, is still R0 to R2; else step 4 runs again by
the class too), CI on that head is green (`gh pr checks`:
check, model, negative, formal-model and acceptance, the ruleset's required checks, each
pass, a skipped run not counting, and nothing fails or waits), no required box of its
checklist is unticked (the template's own required boxes included, so deleting one does
not help; origin/main's template, or the head's while origin/main has none), the
coordinator has written its "What and why", its reviews (each with its commit and its
findings) and its "Needs the owner's OK", read as GitHub shows them by CommonMark's
rules (not in a comment, an HTML block or code, and a box only as a list item), and its
"Unfinished work", checked as raw text under a heading GitHub shows (None, or a plain
list of #N references to issues open with blocks-release). The title
and branch name, which go into main's merge commit, hold nothing the scan refuses, it
carries a label for its kind and `security-review` when a protected path changes, and it
is not a draft; a pull request labelled release waits until no blocks-release issue or
pull request is open, read from GitHub at the gate, with any unreadable response refusing
the merge, merges only on a record of the full pre-flight of its head (never one that left
step 4 to CI), and only with a green run of .github/workflows/safe-push-tests.yml at its
exact head, whose copy of that workflow is origin/main's, with each of the three jobs the
gate names there and passed (the verdict on the safe_push tests' shards, the negative
tests, the formal model's check), and every other job passed, the eight shards among them,
but the one that reports a red run on main (suite_gate, #301). Malformed labels refuse;
the merge and pre-flight watcher ignore a stale release-gate job from Release gate only on
an ordinary pull request with readable labels.
The pre-flight's notes are shown beside the checklist. Then
`gh pr merge <n> --merge --delete-branch --match-head-commit <head>` with the merge
commit's subject and body given (GitHub's own words: the owner GitHub names for the head,
never origin's URL's, which names the old owner after a transfer, and refused when GitHub
names none an account could have; the branch name, scanned; and the title, scanned; a
branch renamed since the merge first read it is refused, as a head moved is): a merge
commit, never a squash or a rebase, since review records stamp the branch's commits.
Whatever gh's exit, GitHub is then asked whether the pull request merged before anything
is said, for gh can fail after merging, and exit 0 without merging when a merge queue or
auto-merge takes the pull request to merge later (issue #42). Once gh is asked to merge,
the run says nothing merged only when GitHub says OPEN or CLOSED after gh failed, and
success only when GitHub says merged and origin/main holds the merge commit GitHub names
by its full object name; gh exiting 0 with the pull request not merged, a merge commit
GitHub does not name or origin/main does not hold, an interruption before GitHub answers,
or GitHub not to be asked, or answering with no state of its own, is "merge state
unknown", with no revert advised. Afterwards that merge commit is checked to join the
base and the head checked, with the head's tree.

--land, with --branch and --ready (the body final at the push, since nothing comes
between), goes on, once CI is green and nothing failed, to the merge of that pull request
in the same process, as --merge does it (#557,
docs/decisions/2026-10-26-one-run-landing.md). It refuses, merging nothing: a head GitHub
has for the pull request that is not the commit pushed (the run merges only what it
pushed); an origin whose URL, as git gives it, is not the one git gave the pre-flight
before any of the commit's code ran; origin/main moved during CI, before anything is
judged against the new main; and a copy of the harness on disk that no longer matches
origin/main's (the merge hands over to no other copy). It holds the merge for the
security review, merging nothing, when the pre-flight noted origin/main's checks failing
on the commit (a failure keep_apart reads, or its "pinned values"): that review reads the
note, and a separate --merge follows it. Otherwise the pre-flight's record, kept in
memory from the push and never read from a file, stands in for step 4 even for a head
that changes the checks or a protected path, which a separate --merge never lets a record
do, only while no main-checks cache hit served origin/main's pass and checks_record
accepts it (of step 4 in full, every step passed; or, for a change still of R0 to R2, of
a pre-flight that left it to CI); else step 4 runs by the class, as for a separate
--merge. The disk is never read on that path: the record saved there is not loaded,
whatever it holds. A separate --merge keeps the rule above unchanged.

When main's rules require a merge queue, --merge keeps these gates, checks the head
against the newest commit of origin/main's first-parent chain that it contains, as the
queue's judge does, and enqueues it with expectedHeadOid pinned.
It follows the queue to a verified merge or an ejection; an unreadable or timed out
verdict is exit 3. In both modes, open main-red issues or a failed completed post-merge
run at main's tip refuse every merge but the fix's: a pull request whose body has the
line "Fixes main-red: #<n>", naming every open main-red issue and no other, and whose
own CI passes, as every merge's must. Unreadable rules or main-health answers refuse too.

`--dry-run` does everything but the push, the pull request and the merge. The temporary
worktrees are removed at the end, on a failure too. The pre-push hook,
`scripts/hooks/pre-push` (installed by `scripts/install_hooks.sh`), runs origin/main's
secret scan (`--scan-push`) on a push to any branch, refuses every push to main, and
refuses a tag unless STOICHEIA_TAG_PUSH names it, which the owner's OK alone sets, and
scans the tag then.

Exit status: 0 when done (a pull request opened or updated with CI green, a merge, a dry
run passed, or nothing to do); 1 when refused before any push or merge; 2 for a usage
error; 3 when pushed but CI failed or was not followed, merged but main is not the tree
checked or could not be read, or when the merge state is unknown (it may have happened,
or may happen yet); with --land, 3 also when pushed with CI green and the merge refused,
interrupted or stopped by an error, or held for the security review.
Standard library, git and gh; Python 3.11 or later.
"""

from __future__ import annotations

import argparse
import ast
import base64
import binascii
import contextlib
import copy
import datetime
import hashlib
import html
import importlib.util
import inspect
import io
import json
import math
import os
import platform
# platform.mac_ver() imports plistlib, and with it xml.parsers.expat, when it is first
# called; Python's own handling of an uncaught exception imports traceback, and with it
# a dozen more: both imported here, with tomllib, so that nothing is imported once the
# sandbox is set (run), not even when the run crashes there.
import plistlib  # noqa: F401
import posixpath
import re
import secrets
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
import tomllib
import traceback  # noqa: F401
import types
import unicodedata
from collections import Counter
from pathlib import Path
from typing import Callable, NamedTuple

sys.path.insert(0, str(Path(__file__).resolve().parent))
import heath  # noqa: E402  (the contracts: parse_ref, prop_key, theorem_span)

# origin/main's harness runs in place of a branch's copy when this marker is in it.
HARNESS_PROTOCOL = 2

PY = sys.executable
DECISIONS = "docs/briefs/0002-decisions.md"
# Dated decision entries, each a page of its own (docs/WORKFLOW.md, section 10), and the
# folder's README, which is no entry.
ENTRIES = "docs/decisions/"
ENTRIES_README = "docs/decisions/README.md"
DECISION_ENTRY = re.compile(r"docs/decisions/([0-9]{4}-[0-9]{2}-[0-9]{2})-[a-z0-9]+"
                            r"(?:-[a-z0-9]+)*\.md")
# The first day an entry may bear: the day of the decisions page's entry "Decision entries,
# one file each", which began them (render.py's FIRST_ENTRY). The last is the day after the
# earlier of the pushed commit's committer date and the runner's own date (entry_changes).
FIRST_ENTRY = datetime.date(2026, 10, 20)
# A run of this many consecutive words that an entry shares with the decisions record is
# copied from it, however the lines are wrapped.
SHARED_RUN = 12
# Unicode's default-ignorable characters that are no format characters (Cf), as
# render.py's IGNORABLE.
IGNORABLE = ((0x034F, 0x034F), (0x115F, 0x1160), (0x17B4, 0x17B5), (0x180B, 0x180F),
             (0x2065, 0x2065), (0x3164, 0x3164), (0xFE00, 0xFE0F), (0xFFA0, 0xFFA0),
             (0xFFF0, 0xFFF8), (0xE0000, 0xE0FFF))
# The letters of the Cyrillic and Greek alphabets that look like Latin ones, each read as
# the Latin letter it looks like, capital as capital and small as small, since a capital
# and its small letter may look like different Latin ones (Greek capital eta like H,
# small eta like n): the decisions record compares an entry by this reading (skeleton).
# Letters of other scripts are not read so.
LOOK_ALIKES = str.maketrans({unicodedata.lookup(name): latin for latin, names in (
    ("A", "CYRILLIC CAPITAL LETTER A, GREEK CAPITAL LETTER ALPHA"),
    ("B", "CYRILLIC CAPITAL LETTER VE, GREEK CAPITAL LETTER BETA"),
    ("C", "CYRILLIC CAPITAL LETTER ES, GREEK CAPITAL LUNATE SIGMA SYMBOL"),
    ("D", "CYRILLIC CAPITAL LETTER KOMI DE"),
    ("E", "CYRILLIC CAPITAL LETTER IE, GREEK CAPITAL LETTER EPSILON"),
    ("H", "CYRILLIC CAPITAL LETTER EN, CYRILLIC CAPITAL LETTER SHHA, GREEK CAPITAL LETTER ETA"),
    ("I", "CYRILLIC CAPITAL LETTER BYELORUSSIAN-UKRAINIAN I, CYRILLIC LETTER PALOCHKA, "
          "GREEK CAPITAL LETTER IOTA"),
    ("J", "CYRILLIC CAPITAL LETTER JE, GREEK CAPITAL LETTER YOT"),
    ("K", "CYRILLIC CAPITAL LETTER KA, GREEK CAPITAL LETTER KAPPA"),
    ("M", "CYRILLIC CAPITAL LETTER EM, GREEK CAPITAL LETTER MU"),
    ("N", "GREEK CAPITAL LETTER NU"),
    ("O", "CYRILLIC CAPITAL LETTER O, GREEK CAPITAL LETTER OMICRON"),
    ("P", "CYRILLIC CAPITAL LETTER ER, GREEK CAPITAL LETTER RHO"),
    ("Q", "CYRILLIC CAPITAL LETTER QA"),
    ("S", "CYRILLIC CAPITAL LETTER DZE"),
    ("T", "CYRILLIC CAPITAL LETTER TE, GREEK CAPITAL LETTER TAU"),
    ("W", "CYRILLIC CAPITAL LETTER WE"),
    ("X", "CYRILLIC CAPITAL LETTER HA, GREEK CAPITAL LETTER CHI"),
    ("Y", "CYRILLIC CAPITAL LETTER U, CYRILLIC CAPITAL LETTER STRAIGHT U, "
          "GREEK CAPITAL LETTER UPSILON"),
    ("Z", "GREEK CAPITAL LETTER ZETA"),
    ("\N{LATIN CAPITAL LETTER E WITH DIAERESIS}", "CYRILLIC CAPITAL LETTER IO"),
    ("\N{LATIN CAPITAL LETTER I WITH DIAERESIS}", "CYRILLIC CAPITAL LETTER YI"),
    ("a", "CYRILLIC SMALL LETTER A, GREEK SMALL LETTER ALPHA"),
    ("c", "CYRILLIC SMALL LETTER ES, GREEK LUNATE SIGMA SYMBOL"),
    ("d", "CYRILLIC SMALL LETTER KOMI DE"),
    ("e", "CYRILLIC SMALL LETTER IE"),
    ("h", "CYRILLIC SMALL LETTER SHHA"),
    ("i", "CYRILLIC SMALL LETTER BYELORUSSIAN-UKRAINIAN I, GREEK SMALL LETTER IOTA"),
    ("j", "CYRILLIC SMALL LETTER JE, GREEK LETTER YOT"),
    ("l", "CYRILLIC SMALL LETTER PALOCHKA"),
    ("n", "GREEK SMALL LETTER ETA"),
    ("o", "CYRILLIC SMALL LETTER O, GREEK SMALL LETTER OMICRON"),
    ("p", "CYRILLIC SMALL LETTER ER, GREEK SMALL LETTER RHO"),
    ("q", "CYRILLIC SMALL LETTER QA"),
    ("s", "CYRILLIC SMALL LETTER DZE"),
    ("u", "GREEK SMALL LETTER UPSILON"),
    ("v", "GREEK SMALL LETTER NU"),
    ("w", "CYRILLIC SMALL LETTER WE"),
    ("x", "CYRILLIC SMALL LETTER HA, GREEK SMALL LETTER CHI"),
    ("y", "CYRILLIC SMALL LETTER U, CYRILLIC SMALL LETTER STRAIGHT U, "
          "GREEK SMALL LETTER GAMMA"),
    ("\N{LATIN SMALL LETTER E WITH DIAERESIS}", "CYRILLIC SMALL LETTER IO"),
    ("\N{LATIN SMALL LETTER I WITH DIAERESIS}", "CYRILLIC SMALL LETTER YI"),
) for name in names.split(", ")})
# Characters that render blank though Unicode counts them neither white space nor
# default-ignorable, as render.py's BLANK_GLYPHS: a fixed list, since Unicode has no
# property for a blank glyph. The Braille pattern blank, the musical symbol null notehead
# and the Khitan small script filler; an entry may not hold one (invisible).
BLANK_GLYPHS = frozenset("\u2800\U0001d159\U00016fe4")
# Characters that look blank and that str.split does not take for white space: those of
# BLANK_GLYPHS and the Hangul fillers (IGNORABLE), none of which an entry may hold, though
# the decisions page may. skeleton reads them, and every space separator (Unicode's Zs),
# as a space.
BLANKS = BLANK_GLYPHS | frozenset("\u115f\u1160\u3164\uffa0")
BRIEFS = "docs/briefs/"
LOCK = "Certificate/axioms.lock"
ALLOWLIST = "scripts/safe_push_allow.toml"
TEMPLATE = ".github/pull_request_template.md"
GUARDED_DIRS = ("Elements", "heath", "review", "figures", "mishnah")
# A change to any of these needs a decisions entry naming the file, and the label below.
# docs/WORKFLOW.md's "Protected paths" names each of them (test_safe_push checks it).
# lakefile.lean is here although the repository has none: Lake reads it in preference to
# lakefile.toml, and runs it. .gitignore is here because an added rule hides untracked
# files from `git status`, and so from the check that the generated pages are current.
# checks/ is the registry of CI's `check` job, one file per check (#229): a check added,
# removed, or with its command, job or order changed, is named in a decisions entry.
# docs/ACCEPTANCE.md's table of the limitations allowed is what tests/test_acceptance_limits.py
# ties to check_acceptance.py's ALLOWED_LIMITS, so it is a check input, protected as one
# (#249). PROTECTED_JUDGED, below, joins them. scripts/auto_revert.py keeps its own copy of the
# two, in this order, since it must not import the revision it reverts; a change here is
# made there too (tests/test_auto_revert.py compares them).
PROTECTED = ("scripts/", ".github/", "Certificate/", "tests/", "review/SCHEMA.md",
             "review/terms.toml", ".gitattributes", ".gitignore", "lakefile.toml",
             "lakefile.lean", "lean-toolchain", "lake-manifest.json", "checks/",
             "docs/ACCEPTANCE.md")
# Protected, and still judged (#96): the audit lemmas of docs/reports/overlaps.md, whose
# pinned axiom lists (`#guard_msgs`) back the catalogue's claims, and Audit.lean, the root
# that decides which of them `lake build Audit` checks; the model's Model/Audit.lean and
# Model.lean, which pin its proofs to Lean's own axioms with Elements absent, and include
# that audit in the build; and the formal model's build files,
# its package, toolchain and pinned Mathlib, with model/lakefile.lean, which Lake would read
# in preference to model/lakefile.toml, and model/lock.sha256, the hash of the lock the model
# was last checked against. A change to any of them needs a decisions entry and the label, as for
# every protected path. They are content the checks judge, not checks, so they stay judged
# (judged_files): a check change still lands apart from them, as before they were protected.
PROTECTED_JUDGED = ("Audit/", "Audit.lean", "model/Model/Audit.lean", "model/Model.lean",
                    "model/lakefile.toml", "model/lakefile.lean",
                    "model/lean-toolchain", "model/lake-manifest.json", "model/lock.sha256")
PROTECTED += PROTECTED_JUDGED
# The checks and what they expect: origin/main's copies judge the commit (step 4). The
# registry, checks/, is one of them: a commit that changes it is a check change, kept apart
# from what the checks judge, and the sequence step 4 runs is origin/main's registry in any
# case (check_sequence). So is docs/ACCEPTANCE.md, whose table of allowed limitations and
# check_acceptance.py's ALLOWED_LIMITS change together (#249).
CHECK_INPUTS = ("scripts/", "tests/", "Certificate/", "review/SCHEMA.md", "review/terms.toml",
                "checks/", "docs/ACCEPTANCE.md")
# Of those, the values pinned to the edition, not code. The lock and the model's hash of it
# are compared exactly, both ways: check_fidelity.py the lock with facts.json, and the
# model's run its hash with the lock. The model's page and results are its account of the
# laws; `results_check.py` holds them to one commit and the present harness, and
# `check_fidelity.py` the page's count markers to what they count. A change to the page is
# a pinned value only while the same markers stand in it (counts_moved). The certificate's
# expectations are checked one way only, each for what it says, so a change to them is a
# pinned value only while it keeps every expectation origin/main has (kept_expectations).
# The model's law names are compared with the lock both ways, but a line of them changed
# while its axiom stands would loosen the model's check of that axiom, so a change to them
# is a pinned value only while each line changed moves with its axiom's entry in the lock
# (laws_move_with_axioms). The values between count markers in the Markdown of
# COUNTED_PROSE, below, are compared exactly with the files they count (check_fidelity.py),
# so a change to that Markdown, the model's page aside, is a pinned value only while
# nothing but those values changes (counts_moved). A change to the content they pin moves
# them with it, in the same pull request; they stay protected (a decisions line,
# security-review, the lock's guard), and the commit's own checks must pass.
EXPECTATIONS = "tests/certificate_expectations.json"
MODEL_HASH = "tests/model/lock.sha256"
MODEL_LAWS = "tests/model/laws.toml"
MODEL_PAGE = "tests/model/MODEL.md"
MODEL_RESULTS = "tests/model/results/"
PINNED = (EXPECTATIONS, LOCK, MODEL_HASH, MODEL_LAWS, MODEL_PAGE, MODEL_RESULTS)
# The two harnesses that implement every law of the model. They are check code; but a
# law's code in them moves with its axiom, as its line of laws.toml does, while it keeps to
# itself, the laws that stay keep their order, and the rest of the file stays as it was
# (laws_move_with_axioms).
MODEL_LAW_CODE = ("tests/model/search.py", "tests/model/hyperbolic.py")
# The check inputs that are not code: Certificate/FIELDS.md and review/SCHEMA.md say what
# the certificate and the records hold, and Markdown under tests/ is prose too
# (tests/model/MODEL.md, the only one today, is pinned whole but for its count markers,
# which must stand). render.py fills the count markers in their Markdown, as COUNT_READER
# defines them, and check_fidelity.py holds each value to the files it counts: a new word
# in the lock moves FIELDS.md's count of the words with it, in no other order. scripts/ is
# check code: a count there is never pinned.
COUNTED_PROSE = ("Certificate/", "review/SCHEMA.md", "tests/")
COUNT_READER = "scripts/generated_counts.py"
COUNT_READERS: dict[tuple[str, str], object] = {}
SECURITY_LABEL = "security-review"
RELEASE_LABEL = "release"
BLOCKS_RELEASE = "blocks-release"
LABELS = {
    **{f"stage-{n}": f"Brief 0005, stage {n}" for n in range(2, 7)},
    "tooling": "Scripts, CI and the harness",
    "text": "Heath's text, commentary and the reader's pages",
    "lean": "Proofs and statements",
    "docs": "Guides, briefs and reports",
    SECURITY_LABEL: "Changes a protected path: needs /security-review before merge",
    RELEASE_LABEL: "A release pull request: --merge refuses it while a blocks-release issue is open",
    BLOCKS_RELEASE: "Unfinished or prototype work on main: no release until this is closed",
}
KIND_LABELS = ("tooling", "text", "lean", "docs")      # every pull request carries one
assert set(KIND_LABELS) <= set(LABELS)
# The required status checks of the ruleset on main, in its order (judge_checks).
REQUIRED_CHECKS = ("check", "model", "negative", "formal-model", "acceptance")
# The risk classifier (docs/decisions/2026-10-22-risk-lanes.md), whose copy at origin/main,
# never the commit's, gives the class of the change (risk_class); and the classes whose
# pre-flight leaves step 4 to CI (docs/decisions/2026-10-22-checks-by-risk.md).
RISK = "scripts/risk.py"
LOW_CLASSES = ("R0", "R1", "R2")
RISK_TIMEOUT = 300        # seconds origin/main's risk.py may take to class a change
# A release pull request merges only with a green run of this workflow at its exact head
# (#301), the head's copy of it being origin/main's, since a run at the head runs the
# head's copy: each of its jobs in SUITE_JOBS there and passed, and every other job too,
# save the one that reports a red run on main, which a green run skips. SUITE_JOBS are
# the workflow's jobs but that one and the matrix of its eight shards, safe-push-shards,
# whose jobs GitHub names `safe-push-shards (K)`: the verdict on the shards,
# safe-push-tests, which needs them, the negative tests and the formal model's check. The
# gate holds each shard's job to have passed as it holds any job it does not name (Units
# holds both to the workflow).
SUITE_WORKFLOW = "safe-push-tests.yml"
SUITE_PATH = f".github/workflows/{SUITE_WORKFLOW}"
SUITE_JOBS = ("safe-push-tests", "negative-tests", "formal-model-kernel")
SUITE_REPORT_JOB = "report"
GENERATED = ("facts.json", "book/", "CERTIFICATE.md", "GRAPH.md", "README.md", "docs/PROGRAM.md",
             "docs/WORKFLOW.md")
# Of these, three are generated only between their markers (render.py's SCOPE_MARKERS and
# STATUS_MARKERS, and registry.py's MARKERS, between which render.py writes section 8's
# first command block from the registry of checks); the rest of each is written by hand.
GENERATED_REGIONS = {
    "README.md": re.compile(r"<!-- scope:([IVX]+) -->.*?<!-- /scope:\1 -->", re.S),
    "docs/PROGRAM.md": re.compile(r"<!-- status -->\n.*?<!-- /status -->", re.S),
    "docs/WORKFLOW.md": re.compile(r"<!-- checks -->\n.*?<!-- /checks -->", re.S),
}
CI_APPEAR_TIMEOUT = 300   # seconds to wait for the checks to appear after the push
CI_POLL = 10              # seconds between looks for them (both shortened by the tests)
CI_WATCH_INTERVAL = "30"  # seconds between `gh pr checks --watch` refreshes
HEAD_TIMEOUT = 60         # seconds to wait for GitHub to see the branch's new head
TAIL = 40                 # lines of a failed step's output to print

# The registry of CI's `check` job, one file per check, and its one reader, both read at
# origin/main for step 4 (check_sequence; docs/decisions/2026-10-22-check-registry.md).
REGISTRY = "checks"
REGISTRY_READER = "scripts/registry.py"
REGISTRY_TIMEOUT = 120    # seconds a registry.py, origin/main's or the commit's, may take
# The name of the registry's one `empty` entry, the check that `git status --porcelain`
# prints nothing; no command may bear it (check_sequence, FRESHNESS).
EMPTY_CHECK = "git status --porcelain is empty"
# The `check` job's sequence, built in: it stands in for the registry only while
# origin/main holds none, so that the train that adds the registry is judged by the
# sequence every train was judged by before it. Units pins it to a list of its own, as it
# pins MODEL_JOB and NEGATIVE, so that the registry grows without it. A follow-up card
# removes these lines once the registry is on main.
CHECKS = [
    ("lake build", ["lake", "build"]),
    ("lake build Audit", ["lake", "build", "Audit"]),
    ("lake build Staging", ["lake", "build", "Staging"]),
    ("lake env lean Certificate/Facts.lean", ["lake", "env", "lean", "Certificate/Facts.lean"]),
    ("python3 -I tests/test_certificate.py", [PY, "-I", "tests/test_certificate.py"]),
    ("python3 scripts/sweep_citations.py --self-test",
     [PY, "scripts/sweep_citations.py", "--self-test"]),
    ("python3 scripts/sweep_citations.py", [PY, "scripts/sweep_citations.py"]),
    ("python3 scripts/check_kernel.py --self-test",
     [PY, "scripts/check_kernel.py", "--self-test"]),
    ("python3 scripts/heath.py", [PY, "scripts/heath.py"]),
    ("python3 scripts/check_fidelity.py", [PY, "scripts/check_fidelity.py"]),
    ("python3 -I tests/test_check_style.py", [PY, "-I", "tests/test_check_style.py"]),
    ("python3 -I tests/test_release_gate.py", [PY, "-I", "tests/test_release_gate.py"]),
    ("python3 -I tests/test_jev_models.py", [PY, "-I", "tests/test_jev_models.py"]),
    ("python3 scripts/audit/jev.py self-test", [PY, "scripts/audit/jev.py", "self-test"]),
    ("python3 -I tests/test_screen.py", [PY, "-I", "tests/test_screen.py"]),
    ("python3 -I tests/test_acceptance_limits.py",
     [PY, "-I", "tests/test_acceptance_limits.py"]),
    ("python3 -I tests/test_check_superposition_pins.py",
     [PY, "-I", "tests/test_check_superposition_pins.py"]),
    ("python3 -I scripts/check_superposition_pins.py",
     [PY, "-I", "scripts/check_superposition_pins.py"]),
    ("python3 scripts/check_style.py", [PY, "scripts/check_style.py"]),
    ("python3 scripts/render.py", [PY, "scripts/render.py"]),
    (EMPTY_CHECK, None),
    ("python3 scripts/check_queue.py --tree .", [PY, "scripts/check_queue.py", "--tree", "."]),
    ("python3 scripts/check_links.py", [PY, "scripts/check_links.py"]),
]
# CI's `model` job, run after the `check` job's sequence, in the same worktree. The
# registry holds the `check` job's checks alone, so this stays here, as NEGATIVE does. It
# leaves out the model job's `results_check.py`, which only CI runs until it joins this
# list (WORKFLOW, section 8).
MODEL_JOB = [
    ("python3 -I tests/model/run.py --fast", [PY, "-I", "tests/model/run.py", "--fast"]),
]
# CI's `negative` job, in a second disposable worktree: negative_tests.py plants breaks
# in the tree it runs in.
NEGATIVE = [
    ("negative: lake build", ["lake", "build"]),
    ("negative: lake env lean Certificate/Facts.lean",
     ["lake", "env", "lean", "Certificate/Facts.lean"]),
    ("negative: python3 scripts/negative_tests.py", [PY, "scripts/negative_tests.py"]),
]

ARGV: list[str] = []      # this run's arguments, for origin/main's harness to run with
HARNESS = "this copy of `scripts/safe_push.py`"   # which harness ran, for the record
HARNESS_BLOB: str | None = None     # its blob, when it is origin/main's

# The cache of origin/main's pass of step 4 (--main-checks-cache; open_cache, MainChecks).
# CACHE is its directory while this run uses it, and SANDBOX the sandbox-exec profile that
# every command then runs under (run), which may not write it. Both stay None without the
# flag, or when the directory or the sandbox cannot be had.
MAIN_CHECKS_FORMAT = 1
SANDBOX_EXEC = "/usr/bin/sandbox-exec"
DENIED = "Operation not permitted"      # what a write the sandbox refuses says (EPERM)
ENTRY_BYTES = 16 * 2 ** 20      # the largest entry read: 16 MiB (one measured 156,119 bytes)
CACHE: Path | None = None
SANDBOX: str | None = None
CACHE_HIT = False       # origin/main's pass was taken from the cache in this run (main_checks)


class Refusal(Exception):
    """A step failed: nothing is pushed or merged (or, after it, nothing more is done)."""


class NothingToPush(Exception):
    """origin/main is already the commit."""


# --------------------------------------------------------------------------------------
# Running commands


# The variables that tie git to one repository, as `git rev-parse --local-env-vars` lists
# them. A hook sets some of them (GIT_DIR, GIT_INDEX_FILE, GIT_WORK_TREE) for the
# repository it runs in; left set, they would send safe_push's own commands to that
# repository and its index: `git worktree add` would check the commit out into a linked
# worktree's index under a hook's GIT_INDEX_FILE (#357). So no command safe_push runs gets
# one of the caller's but GIT_NO_REPLACE_OBJECTS (KEPT_GIT_VARIABLES), and git finds its
# repository by the working directory each command names, but in main()'s one read of the
# repository the caller's GIT_DIR and GIT_WORK_TREE name, given to it as git's options
# (#186); the one the harness sets itself,
# base_tree's temporary GIT_INDEX_FILE, is named to run() in `keep`. The list is git
# 2.50's, with GIT_INTERNAL_SUPER_PREFIX, which older git printed too.
REPOSITORY_VARIABLES = frozenset({
    "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_COMMON_DIR", "GIT_CONFIG", "GIT_CONFIG_COUNT",
    "GIT_CONFIG_PARAMETERS", "GIT_DIR", "GIT_GRAFT_FILE", "GIT_IMPLICIT_WORK_TREE",
    "GIT_INDEX_FILE", "GIT_INTERNAL_SUPER_PREFIX", "GIT_NO_REPLACE_OBJECTS",
    "GIT_OBJECT_DIRECTORY", "GIT_PREFIX", "GIT_REPLACE_REF_BASE", "GIT_SHALLOW_FILE",
    "GIT_WORK_TREE"})


def own_env(env=None, keep=()) -> dict:
    """A copy of `env` (os.environ when None) with none of REPOSITORY_VARIABLES but those
    KEPT_GIT_VARIABLES names, so that a check started with tool_env() keeps
    GIT_NO_REPLACE_OBJECTS (#355, #357), and those `keep` names, which the harness sets
    itself, on purpose (base_tree's temporary GIT_INDEX_FILE)."""
    return {name: value for name, value in (os.environ if env is None else env).items()
            if name not in REPOSITORY_VARIABLES or name in KEPT_GIT_VARIABLES
            or name in frozenset(keep)}


def without_replacements(env=None, keep=()) -> dict:
    """A copy of `env` (os.environ when None) with none of REPOSITORY_VARIABLES but
    GIT_NO_REPLACE_OBJECTS, set to 1, so no GIT_REPLACE_REF_BASE. Git from 2.19 to 2.41
    still lets core.useReplaceRefs=true in config override it, which run() pins off
    (NO_REPLACE_REFS)."""
    env = own_env(env, keep)
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    return env


# Git from 2.19 to 2.41 lets core.useReplaceRefs=true in config turn replacements back on
# despite GIT_NO_REPLACE_OBJECTS; configuration given on git's command line is read last.
NO_REPLACE_REFS = ("-c", "core.useReplaceRefs=false")


def run(cmd, cwd, *, env=None, input=None, binary=False,
        capture=True, keep=(), timeout=None) -> subprocess.CompletedProcess:
    """Every command the harness starts starts here, but origin/main's risk.py, which
    risk_class runs with a time limit, and the Git read that loads origin/main's
    count-marker reader, both before the main-checks cache is opened. While the cache is
    in use (open_cache), each runs under sandbox-exec with SANDBOX, a profile that may
    not write the cache: git, the guards' check_fidelity.py and render.py, the readers of
    the registry of steps 3 and 4 (the commit's own being the commit's code), every step
    of the full checks, gh. So the commands a flagged run starts cannot write the cache
    directly. The sandbox does not stop a run without the flag (a ship's own dry run
    among them), which starts its commands with no sandbox; nor anything code run as the
    same user does outside a flagged run; nor anything a flagged run's code leaves for a
    later command to run before its sandbox starts: the launcher in
    .git/stoicheia/, alias.safe-push in .git/config, a program earlier on the PATH, the
    harness copy in ~/.cache/stoicheia/harness/, a module in the harness's own directory,
    which Python searches first, or in Python's standard library (the user's own under
    Homebrew), Python's start-up files. That is the exposure the --merge step-4 record
    already has, a local file any code run as the user can write. A profile that allows
    writes only where the checks need them, or a cache owned by another Unix user, could
    narrow it; that is for the owner to decide. Nothing else in the harness may start a
    process while the cache is in use (platform.platform() did, running `uname -p` and
    `file -b` from the PATH: environment), nor import a module but a builtin, which
    Python would look for first in the harness's own directory (so plistlib, and tomllib
    on a supported interpreter, which mac_ver and the allow-list imported late, are
    imported with the rest at the top)."""
    # A push sends the original objects, but git reads a replacement (refs/replace/, or a
    # ref under GIT_REPLACE_REF_BASE) in their place: so git runs here with replacements
    # off, by its environment and by its command line, lest the scan or the hand-over read
    # a clean stand-in (#256). No command, git's or another's, gets one of the caller's
    # variables that tie git to one repository, but GIT_NO_REPLACE_OBJECTS; only a name in
    # `keep`, which the harness sets itself (base_tree's GIT_INDEX_FILE), passes (#357).
    if cmd and os.path.basename(cmd[0]) == "git":
        cmd = [cmd[0], *NO_REPLACE_REFS, *cmd[1:]]
        env = without_replacements(env, keep)
    else:
        env = own_env(env, keep)
    if SANDBOX is not None:
        cmd = [SANDBOX_EXEC, "-p", SANDBOX, *cmd]
    # A time limit only when one is given: the CI watch, among others, has none, and its
    # call carries none (tests/test_release_gate.py).
    limit = {} if timeout is None else {"timeout": timeout}
    return subprocess.run(cmd, cwd=cwd, env=env, input=input, capture_output=capture,
                          text=not binary, **limit)


def git(repo, *args, check=True, binary=False) -> str | bytes:
    """git's stdout, run in `repo` with paths printed as they are."""
    r = run(["git", "-c", "core.quotePath=false", *args], repo, binary=binary)
    if check and r.returncode != 0:
        err = r.stderr.decode(errors="replace") if binary else r.stderr
        raise Refusal(f"`git {' '.join(args)}` failed: {err.strip()}")
    return r.stdout


def git_ok(repo, *args) -> bool:
    return run(["git", *args], repo).returncode == 0


def show_bytes(repo, rev: str, path: str) -> bytes | None:
    r = run(["git", "show", f"{rev}:{path}"], repo, binary=True)
    return r.stdout if r.returncode == 0 else None


def show(repo, rev: str, path: str) -> str | None:
    """A file's text at a revision, or None if it is not there."""
    data = show_bytes(repo, rev, path)
    return data.decode("utf-8", errors="replace") if data is not None else None


def rev_parse(repo, rev: str) -> str | None:
    r = run(["git", "rev-parse", "--verify", "--quiet", rev], repo)
    return r.stdout.strip() if r.returncode == 0 else None


# Of the variables that tie git to one repository, the one the checks keep: safe_push sets
# it on purpose (under the launcher and after a hand-over). Every other GIT_* is dropped
# but CONFIG_FILE_VARIABLES, since a hook sets GIT_DIR, GIT_INDEX_FILE and their kin for
# the repository it runs in, and a check that builds a repository of its own (git init,
# add, commit) would act on that one (#355).
KEPT_GIT_VARIABLES = frozenset({"GIT_NO_REPLACE_OBJECTS"})

# The variables that name git's global and system configuration files, or shut them, or
# the system attributes file, out: the checks keep them too (#430). None ties git to a
# repository, and none is in REPOSITORY_VARIABLES: safe_push's own git already keeps all
# four, and a check reads the same configuration files as that git, but for a relative
# path (below). Dropped, they let a check read ~/.gitconfig and the system's files where
# the caller had shut them out, as the test module's hermetic_git() does. Kept,
# GIT_CONFIG_GLOBAL or GIT_CONFIG_SYSTEM may name a file that sets core.hooksPath,
# safe.directory, a url rewrite or an includeIf; but so may the files git reads in their
# place: the global files that HOME and XDG_CONFIG_HOME locate, ~/.gitconfig and
# $XDG_CONFIG_HOME/git/config (the checks keep both variables from the same caller), and
# the system file of the git that the caller's PATH finds. A relative GIT_CONFIG_GLOBAL or
# GIT_CONFIG_SYSTEM is dropped, though: git would read it from the directory it is in,
# for most settings the top of the commit's worktree, so the commit under check could
# supply the file. Without it, git reads the files it reads when the variable is unset,
# as before #430. An empty one, which shuts its file out, is kept, as an absolute one is.
# GIT_CONFIG_NOSYSTEM and GIT_ATTR_NOSYSTEM only take a file away. GIT_CONFIG_COUNT and
# GIT_CONFIG_PARAMETERS, which carry settings themselves, stay dropped with the
# repository variables. Still open, as on main: a relative HOME or XDG_CONFIG_HOME
# reaches the checks, and safe_push's own git keeps a relative GIT_CONFIG_GLOBAL or
# GIT_CONFIG_SYSTEM (its git status in the commit's worktree among them); #442 is to
# have step 1 refuse all four.
CONFIG_FILE_VARIABLES = frozenset({"GIT_CONFIG_GLOBAL", "GIT_CONFIG_SYSTEM",
                                   "GIT_CONFIG_NOSYSTEM", "GIT_ATTR_NOSYSTEM"})


def tool_env() -> dict:
    """The environment for the checks: elan's lake on the PATH, as CI and AGENTS.md set it,
    and no variable of git's but those KEPT_GIT_VARIABLES and CONFIG_FILE_VARIABLES name,
    so that each check finds its repository by its working directory, never by what a hook
    left set (#355), and reads no global or system configuration, and no system
    attributes file, that the caller shut out (#430), but where a relative
    GIT_CONFIG_GLOBAL or GIT_CONFIG_SYSTEM shut them out: that it drops, as
    CONFIG_FILE_VARIABLES says."""
    env = {name: value for name, value in os.environ.items()
           if not name.startswith("GIT_") or name in KEPT_GIT_VARIABLES
           or name in CONFIG_FILE_VARIABLES}
    for name in ("GIT_CONFIG_GLOBAL", "GIT_CONFIG_SYSTEM"):
        if env.get(name) and not os.path.isabs(env[name]):
            del env[name]       # a relative path, which the commit could supply
    elan = str(Path.home() / ".elan" / "bin")
    env["PATH"] = elan + os.pathsep + env.get("PATH", "")
    return env


def blob_id(data: bytes) -> str:
    """git's id of a blob holding `data`."""
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def plural(n: int, word: str) -> str:
    return f"{n} {word}" + ("" if n == 1 else "s")


def tail(text: str, n: int = TAIL) -> str:
    lines = text.rstrip().splitlines()
    shown = lines[-n:]
    more = f"    … {len(lines) - n} lines before these\n" if len(lines) > n else ""
    return more + "\n".join("    " + line for line in shown)


# --------------------------------------------------------------------------------------
# The report: every step's outcome and time, printed as it happens and summed up at the end


class Step(NamedTuple):
    stage: str
    name: str
    outcome: str      # "ok", "FAIL", "skip", "note"
    seconds: float | None
    detail: str


class Report:
    def __init__(self):
        self.steps: list[Step] = []
        self.started = time.time()

    def add(self, stage, name, outcome, detail="", seconds=None):
        self.steps.append(Step(stage, name, outcome, seconds, detail))
        took = f"  ({seconds:.1f} s)" if seconds is not None else ""
        label = {"ok": "ok  ", "FAIL": "FAIL", "skip": "skip", "note": "note"}[outcome]
        first, *rest = (detail or "").splitlines() or [""]
        print(f"  {label}  {name}: {first}{took}" if first else f"  {label}  {name}{took}",
              flush=True)
        for line in rest:
            print(f"        {line}", flush=True)

    def heading(self, text):
        print(f"\n{text}", flush=True)

    def failed(self) -> list[Step]:
        return [s for s in self.steps if s.outcome == "FAIL"]


# --------------------------------------------------------------------------------------
# The diff, read once and parsed exactly


class Added(NamedTuple):
    path: str
    line: int       # line number in the new file
    text: str


def _unquote(path: str) -> str:
    """A path as git prints it in a header: quoted, with C escapes, when unusual."""
    if path.startswith('"') and path.endswith('"'):
        raw = path[1:-1].encode("latin-1", errors="backslashreplace")
        return raw.decode("unicode_escape").encode("latin-1").decode("utf-8", errors="replace")
    return path


HUNK = re.compile(r"^@@ -\d+(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


class Hunk(NamedTuple):
    path: str | None        # the new file's path; None when the hunk deletes the file
    removed: list[str]
    added: list[Added]


def diff_hunks(repo, old: str, new: str, *pathspec: str) -> list[Hunk]:
    """Every hunk of the diff from `old` to `new` (commits or trees), with the lines it
    removes and the lines it adds, each added line with its file and line number. Every
    file is read as text (`--text`), whatever .gitattributes says of it, and with no
    external diff or text conversion. Parsed by the hunk counts, so an added line that
    itself begins "+++" is not taken for a header."""
    out = git(repo, "diff", "--no-color", "--text", "--no-ext-diff", "--no-textconv",
              "--no-renames", "--unified=0", "--src-prefix=a/", "--dst-prefix=b/", old, new,
              "--", *pathspec, binary=True).decode("utf-8", errors="replace")
    hunks: list[Hunk] = []
    path = None
    old_left = new_left = 0
    line_no = 0
    for line in out.split("\n"):
        if old_left > 0 or new_left > 0:
            if line.startswith("+"):
                if path is not None:
                    hunks[-1].added.append(Added(path, line_no, line[1:]))
                line_no += 1
                new_left -= 1
            elif line.startswith("-"):
                hunks[-1].removed.append(line[1:])
                old_left -= 1
            elif line.startswith("\\"):
                pass        # "\ No newline at end of file"
            else:
                old_left = new_left = 0
            continue
        if line.startswith("diff --git "):
            path = None
        elif line.startswith("+++ "):
            target = _unquote(line[4:].rstrip("\t"))
            path = None if target == "/dev/null" else target[2:]
        elif line.startswith("@@"):
            m = HUNK.match(line)
            if m:
                old_left = int(m.group(1)) if m.group(1) is not None else 1
                line_no = int(m.group(2))
                new_left = int(m.group(3)) if m.group(3) is not None else 1
                hunks.append(Hunk(path, [], []))
    return hunks


def added_lines(repo, old: str, new: str, *pathspec: str) -> list[Added]:
    """Every line the diff from `old` to `new` adds, with its file and line number."""
    return [a for h in diff_hunks(repo, old, new, *pathspec) for a in h.added]


def changed_files(repo, old: str, new: str, *pathspec: str) -> list[tuple[str, str]]:
    """(status, path) for each file the diff changes, renames shown as delete and add."""
    out = git(repo, "diff", "--name-status", "-z", "--no-renames", old, new, "--", *pathspec)
    parts = out.split("\0")
    return [(parts[i][0], parts[i + 1]) for i in range(0, len(parts) - 1, 2)]


class Change(NamedTuple):
    status: str     # A, M, D, T
    path: str
    mode: str       # the new mode: 100644, 100755, 120000 (a symlink), 160000 (a gitlink)
    blob: str       # the new blob


def raw_changes(repo, old: str, new: str) -> list[Change]:
    out = git(repo, "diff", "--raw", "-z", "--no-renames", "--no-abbrev", old, new)
    parts = out.split("\0")
    changes = []
    for meta, path in zip(parts[0::2], parts[1::2]):
        fields = meta.lstrip(":").split()
        if len(fields) >= 5:
            changes.append(Change(fields[4][0], path, fields[1], fields[3]))
    return changes


def read_blobs(repo, ids) -> dict[str, bytes]:
    """The bytes of each blob, read straight from the object store (`git cat-file`), so
    that no attribute, filter or conversion stands between the scan and the content."""
    ids = list(dict.fromkeys(ids))
    if not ids:
        return {}
    r = run(["git", "cat-file", "--batch"], repo, input=("\n".join(ids) + "\n").encode(),
            binary=True)
    out, pos, blobs = r.stdout, 0, {}
    for oid in ids:
        nl = out.find(b"\n", pos)
        if nl < 0:
            break
        header = out[pos:nl].decode(errors="replace").split()
        if len(header) < 3:          # "<oid> missing"
            pos = nl + 1
            continue
        size = int(header[2])
        blobs[oid] = out[nl + 1:nl + 1 + size]
        pos = nl + 1 + size + 1
    return blobs


def is_binary(data: bytes) -> bool:
    """A NUL byte anywhere. (git looks only at the first 8000 bytes, so a file of prose
    with UTF-16 text after it would read as text, and its tail, a NUL between every
    character, would match no rule. A binary file is read whole, so nothing is lost.)"""
    return b"\0" in data


def empty_tree(repo) -> str:
    return git(repo, "hash-object", "-t", "tree", os.devnull).strip()


def gains(hunks: list[Hunk], count) -> bool:
    """Does the diff add a new mention? True when some hunk's added lines hold more
    mentions (as `count` counts them in the lines joined, so that a name broken across a
    wrapped line is still found) than its removed lines: a line edited in place that
    still names the same thing adds none."""
    for h in hunks:
        added = " ".join(a.text.strip() for a in h.added)
        removed = " ".join(line.strip() for line in h.removed)
        if count(added) > count(removed):
            return True
    return False


def under(path: str, prefixes) -> bool:
    """Is `path` one of `prefixes`, or under one that ends in a slash?"""
    return any(path == p or (p.endswith("/") and path.startswith(p)) for p in prefixes)


def is_protected(path: str) -> bool:
    return under(path, PROTECTED)


# --------------------------------------------------------------------------------------
# Step 2: the secret scan

# Each pattern is written so that its own source text does not match it, so this file
# passes its own scan.
PRIVATE_KEY = re.compile(r"BEGIN (?:[A-Z0-9]+ )*PRIVATE KEY")
TOKEN_RULES = [
    ("private key", PRIVATE_KEY),
    ("GitHub token", re.compile(r"(?<![A-Za-z0-9_])(?:gh[pousr]_[A-Za-z0-9]{30,}"
                                r"|github_pat_[A-Za-z0-9_]{30,})")),
    ("sk- API key", re.compile(r"(?<![A-Za-z0-9_-])sk-[A-Za-z0-9_-]{20,}")),
    ("Slack token", re.compile(r"(?<![A-Za-z0-9_])xox[abposr]-[A-Za-z0-9-]{10,}")),
    ("AWS access key", re.compile(r"(?<![A-Z0-9])(?:AKIA|ASIA)[0-9A-Z]{16}(?![0-9A-Z])")),
    ("Authorization header", re.compile(
        r"(?i)\bauthorization\b[\"']?\s*[:=]\s*[\"']?\s*"
        r"(?:(?:bearer|basic|token|digest)\s+)?[A-Za-z0-9+/=._~-]{8,}")),
    ("bearer token", re.compile(r"(?i)\bbearer\s+[A-Za-z0-9+/=._~-]{20,}")),
]
WEAK_RULES = ("Authorization header", "bearer token")   # not looked for in binary files
# A long base64 or hex run after a word naming a key, token, secret or password, perhaps
# with an opening bracket between (a value continued in parentheses). The name is
# bounded, and must start a word, so a long run of letters (an image's base64 in an SVG)
# costs linear time, not quadratic.
KEYWORD = re.compile(
    r"(?i)(?<![\w-])[\w-]{0,40}(?:key|token|secret|passw(?:or)?d|bearer)[\w-]{0,40}[\"']?"
    r"\s*(?:=>|:=|[:=]|\s)\s*(?:[(\[{]\s*)?[\"'`]?([A-Za-z0-9+/_=.~-]{20,})")
# A run that may be base64 (standard or URL-safe): decoded, and scanned again, when it
# decodes to text.
B64_RUN = re.compile(r"[A-Za-z0-9+/_-]{24,}={0,2}")
B64_DEPTH = 2           # base64 within base64, and no deeper
# Where two lines join: a string closed at the end of one and reopened at the start of
# the next (with `+`, `.`, `&` or `||` between, or a backslash), so that "abc" "def"
# reads as abcdef.
QUOTE_END = re.compile(r"""(["'`])\s*(?:\+|\.|&|\|\|)?\s*\\?$""")
QUOTE_START = re.compile(r"""^(?:\+|\.|&|\|\|)?\s*(["'`])""")
# The owner's private paths, in pieces for the reason above.
PRIVATE_PATHS = [
    re.compile("(?i)secret" + "s20"),
    re.compile("/" + "Downloads" + "/"),
    re.compile("/" + "Users" + "/"),
    re.compile(r"(?i)\b[A-Z]:\\" + "Users" + r"\\"),
    # A home directory folded into one name, as an agent's project and scratchpad
    # directories fold it: a dash, the word, a dash and a name.
    re.compile("(?<![A-Za-z0-9])-" + "Users" + "-[A-Za-z0-9]"),
    # An agent's scratchpad, under the temporary directory.
    re.compile("(?:/private)?/tmp/" + "claude" + "-"),
]
# A private path is flagged whole, from the space, quote or bracket before it to the one
# after, so that an allow-list entry pins that path and no other on its line.
PATH_EDGE = frozenset(" \t\r\n\"'`<>()[]{},;|:=")


def path_span(text: str, a: int, b: int) -> tuple[int, int]:
    while a > 0 and text[a - 1] not in PATH_EDGE:
        a -= 1
    while b < len(text) and text[b] not in PATH_EDGE:
        b += 1
    return a, b


# An identity git made up from the machine's name, when none was configured.
MACHINE_IDENTITY = re.compile(r"(?i)@[^\s<>@]+\.(?:local|localdomain|lan)>?$|\(none\)")
SECRET_FILES = [
    (re.compile(r"(^|/)\.env(\.[^/]*)?$"), ".env file"),
    (re.compile(r"\.(key|pem|p12|pfx)$", re.I), "key file"),
    (re.compile(r"(^|/)id_(rsa|dsa|ecdsa|ed25519)$"), "SSH private key file"),
]
# Printable runs in a binary file, line breaks included, read as lines of text; and runs
# of UTF-16 text, little- and big-endian, wherever they stand in it.
PRINTABLE_RUN = re.compile(rb"[\x20-\x7e\t\r\n]{8,}")
UTF16_RUNS = ((re.compile(rb"(?:[\x20-\x7e\t\r\n]\x00){8,}"), "utf-16-le"),
              (re.compile(rb"(?:\x00[\x20-\x7e\t\r\n]){8,}"), "utf-16-be"))
WINDOW = 40             # bytes kept on each side of a hit in a binary file, for the report
KNOWN_RULES = ({rule for rule, _ in TOKEN_RULES} | {rule for _, rule in SECRET_FILES}
               | {"key, token or secret", "private path", "private path in a file name",
                  "private path in an identity", "machine-made identity",
                  "symlink out of the repository"})


def entropy(s: str) -> float:
    counts = {c: s.count(c) for c in set(s)}
    return -sum(k / len(s) * math.log2(k / len(s)) for k in counts.values())


def looks_secret(value: str) -> bool:
    """A value after a key word: a long hex run, or a long random-looking base64 run.
    Lean names, prose and paths are not."""
    value = value.strip("=.")
    if re.fullmatch(r"[0-9a-fA-F]{32,}", value):
        return True
    segments = re.split(r"[/.]", value)
    if len(segments) > 1 and all(re.fullmatch(r"[A-Za-z_-]*\d{0,2}[A-Za-z_-]*", s)
                                 for s in segments):
        return False    # a path or a dotted name
    digits = sum(c.isdigit() for c in value)
    letters = sum(c.isalpha() for c in value)
    return len(value) >= 20 and digits >= 2 and letters >= 4 and entropy(value) >= 3.5


class Finding(NamedTuple):
    rule: str
    path: str
    line: int | None
    text: str           # the whole line (or lines), for the allow-list to match
    span: tuple[int, int]
    end: int | None = None          # the last line, for a finding across lines
    commit: str | None = None       # the commit that brings it, if the push takes it out

    def where(self) -> str:
        """The file and line (or lines), and the commit that brings it, if named."""
        where = f"{self.path}:{self.line}" if self.line else self.path
        if self.end and self.end != self.line:
            where += f"-{self.end}"
        if self.commit:
            where += f" (in commit {self.commit[:12]})"
        return where

    def shown(self) -> str:
        """The line with the secret masked, so the report does not repeat it."""
        a, b = self.span
        secret = self.text[a:b]
        masked = secret[:4] + f"…({len(secret)} chars)" if b - a > 8 else secret
        line = (self.text[:a] + masked + self.text[b:]).strip()
        if len(line) > 140:
            line = line[:140] + "…"
        return f"{self.where()}: {self.rule}: {line}"


def readable(raw: bytes) -> bool:
    """Bytes that read as text: printable ASCII and line breaks, nearly all of them."""
    text = sum(32 <= b < 127 or b in (9, 10, 13) for b in raw)
    return len(raw) >= 12 and text >= 0.9 * len(raw)


def b64_text(run: str) -> str | None:
    """A base64 run decoded, if it decodes to readable text; else None. The first 48
    bytes are decoded first, so that an image's base64 costs little."""
    body = run.rstrip("=")
    if len(body) % 4 == 1:
        return None
    if "-" in body or "_" in body:
        if "+" in body or "/" in body:
            return None
        body = body.replace("-", "+").replace("_", "/")
    padded = body + "=" * (-len(body) % 4)
    try:
        if not readable(base64.b64decode(padded[:64], validate=True)):
            return None
        raw = base64.b64decode(padded, validate=True)
    except (binascii.Error, ValueError):
        return None
    return raw.decode("utf-8", errors="replace") if readable(raw) else None


def hits(text: str, *, strong_only=False, depth=0) -> list[tuple[str, tuple, tuple]]:
    """(rule, the span of the match, the span to mask) for each possible secret in text,
    base64 decoded and looked through too (not in binary files: `strong_only`)."""
    found = []
    for rule, pattern in TOKEN_RULES:
        if strong_only and rule in WEAK_RULES:
            continue
        for m in pattern.finditer(text):
            found.append((rule, m.span(), m.span()))
    if not strong_only:
        for m in KEYWORD.finditer(text):
            if looks_secret(m.group(1)):
                found.append(("key, token or secret", m.span(), m.span(1)))
    for pattern in PRIVATE_PATHS:
        for m in pattern.finditer(text):
            span = path_span(text, *m.span())
            found.append(("private path", span, span))
    if not strong_only and depth < B64_DEPTH:
        for m in B64_RUN.finditer(text):
            plain = b64_text(m.group(0))
            if plain is None:
                continue
            for rule in dict.fromkeys(r for r, _, _ in hits(plain, depth=depth + 1)):
                rule = rule.removeprefix("base64-encoded ")
                found.append((f"base64-encoded {rule}", m.span(), m.span()))
    return found


def scan_text(path: str, line_no: int | None, text: str, *, strong_only=False) -> list[Finding]:
    # One finding per place: a token can match two rules.
    found, seen = [], set()
    for rule, _, mask in hits(text, strong_only=strong_only):
        if mask not in seen:
            seen.add(mask)
            found.append(Finding(rule, path, line_no, text, mask))
    return found


def joined_views(texts: list[str]) -> list[tuple[str, list[int], list[int]]]:
    """A run of lines read as one, two ways: with a space between lines (a key word at the
    end of one line, its value on the next), and closed up (a value broken across lines,
    or a string continued with quotes, `+` or a backslash). Each view comes with the
    offset and length of each line's piece of it."""
    spaced = [t.strip() for t in texts]
    tight = list(spaced)
    for i in range(len(tight) - 1):
        a, b = tight[i], tight[i + 1]
        ma, mb = QUOTE_END.search(a), QUOTE_START.match(b)
        if ma and mb and ma.group(1) == mb.group(1):
            tight[i], tight[i + 1] = a[:ma.start()], b[mb.end():]
        elif a.endswith("\\"):
            tight[i] = a[:-1].rstrip()
    views = []
    for pieces, sep in ((spaced, " "), (tight, "")):
        starts, pos = [], 0
        for p in pieces:
            starts.append(pos)
            pos += len(p) + len(sep)
        views.append((sep.join(pieces), starts, [len(p) for p in pieces]))
    return views


def runs(numbered: list[tuple[int, str]]) -> list[list[tuple[int, str]]]:
    """Numbered lines cut into runs of consecutive line numbers."""
    out: list[list[tuple[int, str]]] = []
    for no, text in numbered:
        if out and no == out[-1][-1][0] + 1:
            out[-1].append((no, text))
        else:
            out.append([(no, text)])
    return out


def pieces_in(starts: list[int], lengths: list[int], a: int, b: int) -> list[int]:
    """The pieces of a joined view (by index) that the span a..b touches."""
    return [i for i, (s, n) in enumerate(zip(starts, lengths)) if s < b and s + n > a]


def scan_block(path: str, numbered: list[tuple[int, str]]) -> list[Finding]:
    """The lines a diff adds to one file (or a commit message's lines), each alone and
    then each run of consecutive lines read as one, for a secret split across lines.
    A finding across lines is kept unless what it masks lies in one line that is
    already flagged alone for the same text; and once, in the widest run of lines it is
    seen in: a wider finding stands in for it only by the same rule, masking what it
    masks (a private path, flagged whole, may run on into the next line, and must not
    stand in for a key there)."""
    found = []
    alone: set[tuple[int, str]] = set()
    for no, text in numbered:
        for f in scan_text(path, no, text):
            found.append(f)
            alone.add((no, text[f.span[0]:f.span[1]]))
    for run in runs(numbered):
        if len(run) < 2:
            continue
        across: dict[tuple, Finding] = {}
        for joined, starts, lengths in joined_views([t for _, t in run]):
            for rule, (a, b), (ma, mb) in hits(joined):
                lines = pieces_in(starts, lengths, a, b)
                if len(lines) < 2:
                    continue
                first, last = lines[0], lines[-1]
                masked = pieces_in(starts, lengths, ma, mb)
                if len(masked) == 1 and (run[masked[0]][0], joined[ma:mb]) in alone:
                    continue
                lo, hi = starts[first], starts[last] + lengths[last]
                mask = (max(ma, lo) - lo, min(mb, hi) - lo)
                key = (run[first][0], run[last][0], mask)
                across.setdefault(key, Finding(rule, path, run[first][0], joined[lo:hi], mask,
                                               end=run[last][0]))
        wide = list(across.values())

        def covers(g: Finding, f: Finding) -> bool:
            return ((g.line, g.end) != (f.line, f.end) and g.line <= f.line
                    and g.end >= f.end and g.rule == f.rule
                    and f.text[f.span[0]:f.span[1]] in g.text[g.span[0]:g.span[1]])
        found += [f for f in wide if not any(covers(g, f) for g in wide)]
    return found


def utf16_text(data: bytes) -> str | None:
    """A blob that is UTF-16 text (a byte-order mark, or a NUL beside nearly every ASCII
    byte), decoded; else None."""
    if data[:2] in (b"\xff\xfe", b"\xfe\xff"):
        return data.decode("utf-16", errors="replace")
    head = data[:512]
    if len(head) >= 16:
        for nul_at, codec in ((1, "utf-16-le"), (0, "utf-16-be")):
            if head[nul_at::2].count(0) >= 0.9 * len(head[nul_at::2]):
                return data.decode(codec, errors="replace")
    return None


def printable(text: str) -> str:
    """Text with every character outside printable ASCII shown as a dot, one for one, so
    that spans into it still hold."""
    return re.sub(r"[^\x20-\x7e]", ".", text)


def scan_binary(path: str, data: bytes) -> list[Finding]:
    """A binary file, read whole: the strong rules over its bytes, each hit with a window
    of WINDOW bytes on each side as its text (never the whole file, which an allow-list
    match would otherwise find anywhere, and which the report would print); its
    printable runs, line breaks included, read as lines with every rule, so that a NUL
    planted in a text file does not hide it, nor a value split over two lines; its runs
    of UTF-16 text, wherever they stand, read the same way; and, if the whole of it is
    UTF-16 text, its lines."""
    raw = data.decode("latin-1")
    found = []
    for f in scan_text(path, None, raw, strong_only=True):
        a, b = f.span
        lo, hi = max(0, a - WINDOW), min(len(raw), b + WINDOW)
        found.append(f._replace(text=printable(raw[lo:hi]), span=(a - lo, b - lo)))
    seen = {(f.rule, f.text[f.span[0]:f.span[1]]) for f in found}

    def add(more: list[Finding]) -> None:
        for f in more:
            key = (f.rule, f.text[f.span[0]:f.span[1]])
            if key not in seen:
                seen.add(key)
                found.append(f)

    def lines_of(text: str, first: int) -> list[tuple[int, str]]:
        return list(enumerate(text.splitlines(), first))

    line, pos = 1, 0        # the line each run starts on, counted as the runs go
    for m in PRINTABLE_RUN.finditer(data):
        line, pos = line + data.count(b"\n", pos, m.start()), m.start()
        add(scan_block(path, lines_of(m.group(0).decode("ascii"), line)))
    for pattern, codec in UTF16_RUNS:
        for m in pattern.finditer(data):
            add(scan_block(path, lines_of(m.group(0).decode(codec, errors="replace"), 1)))
    text = utf16_text(data)
    if text is not None:
        add(scan_block(path, lines_of(text, 1)))
    return found


def scan_path(path: str) -> list[Finding]:
    found = [Finding(rule, path, None, path, (0, 0)) for pattern, rule in SECRET_FILES
             if pattern.search(path)]
    for pattern in PRIVATE_PATHS:
        for m in pattern.finditer(path):
            found.append(Finding("private path in a file name", path, None, path,
                                 path_span(path, *m.span())))
    return found


def scan_link(path: str, target: str) -> list[Finding]:
    """A symlink that points out of the repository: to an absolute path, to a home
    directory, or up past the top. (Its target is an added line too, so the text rules,
    the private paths among them, see it as well.)"""
    t = target.strip()
    up = posixpath.normpath(posixpath.join(posixpath.dirname(path), t.replace("\\", "/")))
    if t.startswith(("/", "\\", "~")) or re.match(r"^[A-Za-z]:", t) or up == ".." \
            or up.startswith("../"):
        text = f"{path} -> {t}"
        return [Finding("symlink out of the repository", path, None, text, (0, 0))]
    return []


def scan_identity(where: str, ident: str) -> list[Finding]:
    """A commit's author or committer: no private path, and not an identity git made up
    from the machine's name."""
    found = [Finding("private path in an identity", where, None, ident, m.span())
             for pattern in PRIVATE_PATHS for m in pattern.finditer(ident)]
    m = MACHINE_IDENTITY.search(ident)
    if m:
        found.append(Finding("machine-made identity", where, None, ident, m.span()))
    return found


class Allow(NamedTuple):
    path: str
    match: str
    rule: str
    reason: str
    sha256: str | None      # the SHA-256 of the flagged value, when match does not hold it


# Places the scan reads that no entry may allow: a flagged commit message or identity is
# rewritten, and the pull request's body, title and branch name are the coordinator's to
# change.
UNALLOWABLE = re.compile(r"^commit |^the pull request's body$|^the title$|^the branch name$")
SHA256 = re.compile(r"[0-9a-f]{64}")


def load_allowlist(repo, rev) -> list[Allow]:
    """The allow-list as `rev` (origin/main) has it. Each entry is narrow: one file named
    exactly (no glob, and never a commit's message or identity, nor the pull request's
    body), one rule, a part of the flagged line at least eight characters long, the
    flagged value pinned (held in that part, or named by its SHA-256), and a reason. A
    broad entry is refused, not read."""
    text = show(repo, rev, ALLOWLIST) if rev else None
    if text is None:
        return []
    try:
        data = tomllib.loads(text)
    except tomllib.TOMLDecodeError as e:
        raise Refusal(f"origin/main's {ALLOWLIST} is not valid TOML: {e}")
    entries, problems = [], []
    for i, entry in enumerate(data.get("allow", []), 1):
        if not isinstance(entry, dict):
            problems.append(f"entry {i} is not a table")
            continue
        path, match = entry.get("path"), entry.get("match")
        reason, rule, digest = entry.get("reason"), entry.get("rule"), entry.get("sha256")
        bad = []
        if not isinstance(path, str) or not path:
            bad.append("has no path")
        elif any(c in path for c in "*?["):
            bad.append("names more than one file (a glob in path)")
        elif UNALLOWABLE.search(path):
            bad.append(f"names {path!r}, which cannot be allowed (reword or rewrite it)")
        if not isinstance(match, str) or len(match) < 8:
            bad.append("has no match of at least 8 characters")
        if not isinstance(rule, str) or rule.removeprefix("base64-encoded ") not in KNOWN_RULES:
            bad.append("names no rule of the scan")
        if digest is not None and not (isinstance(digest, str) and SHA256.fullmatch(digest)):
            bad.append("has a sha256 that is not 64 lowercase hex digits")
        if not isinstance(reason, str) or not reason.strip():
            bad.append("has no reason")
        if bad:
            problems.append(f"entry {i} " + ", ".join(bad))
        else:
            entries.append(Allow(path, match, rule, reason.strip(), digest))
    if problems:
        raise Refusal(f"origin/main's {ALLOWLIST} has a broad or incomplete entry: "
                      + "; ".join(problems))
    return entries


def flagged_value(f: Finding) -> str:
    """What a finding flags: the matched text, or, for a rule on the whole file name or
    link (an empty span), its whole text."""
    a, b = f.span
    return f.text[a:b] if b > a else f.text


def value_sha256(f: Finding) -> str:
    return hashlib.sha256(flagged_value(f).encode("utf-8", errors="surrogatepass")).hexdigest()


def withheld(text: str) -> str:
    """Text for a line of the public body, or a placeholder when the scan flags it (a
    file whose name holds a private path, say)."""
    return "(withheld: the scan flags it)" if scan_text("", None, text) else text


def allowed(f: Finding, allow: list[Allow]) -> Allow | None:
    """The entry that excuses the finding: the same file and rule, a match found in the
    flagged line, and the flagged value itself pinned, held in the match or named by its
    SHA-256; so another value on a similar line is still refused. (A value written into
    the allow-list would be flagged there in turn, in the allow-list's own pull request,
    where its new entry does not count yet: hence the SHA-256.)"""
    if UNALLOWABLE.search(f.path):
        return None
    for a in allow:
        if a.path == f.path and a.rule == f.rule and a.match in f.text and (
                flagged_value(f) in a.match or a.sha256 == value_sha256(f)):
            return a
    return None


class Introduced(NamedTuple):
    """What a diff brings in: the files it adds or changes, the lines it adds to text
    files, the binary files ({path: bytes}), and the symlinks ({path: blob})."""
    files: set[str]
    lines: list[Added]
    binaries: dict[str, bytes]
    links: dict[str, str]


def introduced(repo, old: str, new: str) -> Introduced:
    """Text or binary is read from each blob's bytes, never from .gitattributes."""
    changes = [c for c in raw_changes(repo, old, new) if c.status != "D"]
    regular = {c.path: c.blob for c in changes if c.mode not in ("120000", "160000")}
    blobs = read_blobs(repo, regular.values())
    binaries = {p: blobs.get(b, b"") for p, b in regular.items() if is_binary(blobs.get(b, b""))}
    lines = [a for a in added_lines(repo, old, new) if a.path not in binaries]
    links = {c.path: c.blob for c in changes if c.mode == "120000"}
    return Introduced({c.path for c in changes}, lines, binaries, links)


def commit_introduced(repo, commit: str, parents: list[str]) -> Introduced:
    """What one commit brings in that none of its parents has. For a merge, that is what
    it adds against every parent (its own resolution): each side's commits are scanned
    on their own, or are on origin already."""
    each = [introduced(repo, p, commit) for p in parents or [empty_tree(repo)]]
    if len(each) == 1:
        return each[0]
    keys = set.intersection(*({(a.path, a.text) for a in e.lines} for e in each))
    return Introduced(set.intersection(*(e.files for e in each)),
                      [a for a in each[0].lines if (a.path, a.text) in keys],
                      {p: d for p, d in each[0].binaries.items()
                       if all(p in e.binaries for e in each)},
                      {p: b for p, b in each[0].links.items()
                       if all(e.links.get(p) == b for e in each)})


def scan_introduced(repo, d: Introduced) -> list[Finding]:
    found = []
    for path in sorted(d.files):
        found += scan_path(path)
    by_file: dict[str, list[tuple[int, str]]] = {}
    for a in d.lines:
        by_file.setdefault(a.path, []).append((a.line, a.text))
    for path, numbered in by_file.items():
        found += scan_block(path, numbered)
    for path, data in sorted(d.binaries.items()):
        found += scan_binary(path, data)
    for path, blob in sorted(d.links.items()):
        target = git(repo, "cat-file", "blob", blob, binary=True)
        found += scan_link(path, target.decode("utf-8", errors="replace"))
    return found


def secret_scan(repo, base: str | None, sha: str, rep: Report, allow_rev: str | None) -> None:
    """The net change of the push, then each commit's own change, its message and its
    identities: a secret added and taken out again, or a key file added and then
    renamed, is still in the history the push publishes. `base` None: no common history,
    so every commit is read."""
    rep.heading("2. Secret scan")
    t = time.time()
    allow = load_allowlist(repo, allow_rev)
    commits = [line.split() for line in
               git(repo, "rev-list", "--reverse", "--parents",
                   f"{base}..{sha}" if base else sha).splitlines()]
    diffs = [(None, introduced(repo, base or empty_tree(repo), sha))]
    if [c[1:] for c in commits] != [[base]]:    # one commit on origin/main: the same diff
        diffs += [(c, commit_introduced(repo, c, parents)) for c, *parents in commits]
    findings: list[Finding] = []
    for commit, d in diffs:
        findings += [f._replace(commit=commit) for f in scan_introduced(repo, d)]
    for c, *_ in commits:
        message = git(repo, "log", "-1", "--format=%B", c)
        findings += scan_block(f"commit {c[:12]} message",
                               list(enumerate(message.splitlines(), 1)))
        idents = git(repo, "log", "-1", "--format=%an <%ae>%x00%cn <%ce>", c).rstrip("\n")
        author, committer = (idents.split("\0") + ["", ""])[:2]
        findings += scan_identity(f"commit {c[:12]} author", author)
        findings += scan_identity(f"commit {c[:12]} committer", committer)
    # Each finding once: where the push leaves it if it does, else in its commit.
    unique: dict[tuple, Finding] = {}
    for f in findings:
        unique.setdefault((f.rule, f.path, f.text, f.span), f)
    findings = list(unique.values())
    refused = [f for f in findings if not allowed(f, allow)]
    passed = [(f, allowed(f, allow)) for f in findings if allowed(f, allow)]
    seconds = time.time() - t
    net = diffs[0][1]
    scanned = (f"{plural(len(net.lines), 'added line')} in {plural(len(net.files), 'file')} "
               f"({len(net.binaries)} binary), and each of {plural(len(commits), 'commit')} "
               "on its own, with its message and identities")
    # The note's first line alone goes into the public body: it names the finding by its
    # place, rule and value's SHA-256, never by its line, which may hold other flagged
    # values, or a short one that shown() cannot mask; the console has the line after it.
    for f, a in passed:
        rep.add("2", "allow-listed", "note",
                f"{withheld(f.where())}: {f.rule} (value sha256 {value_sha256(f)[:12]}); "
                f"reason: {withheld(a.reason)}\n{f.shown()}")
    if refused:
        detail = "\n".join(f.shown() for f in refused)
        rep.add("2", "secrets", "FAIL", f"{len(refused)} found in {scanned}:\n{detail}", seconds)
        raise Refusal(f"the secret scan found {len(refused)} possible secret(s) or private "
                      f"path(s). Remove them (and rewrite the commits that hold them), or, for "
                      f"a false positive, add a narrow entry with its reason to {ALLOWLIST} "
                      "in a pull request of its own, before this one, pinning the value by "
                      "its SHA-256 (printf %s '<the value>' | shasum -a 256).")
    rep.add("2", "secrets", "ok", f"nothing found in {scanned}", seconds)


# --------------------------------------------------------------------------------------
# Step 3: the invariant guards


OPEN, CLOSE = "([{⟨⦃⦗", ")]}⟩⦄⦘"
# A «…» name, to the `»` that ends it or the end of the text, as read_lean reads one.
LEAN_NAME = re.compile(r"«[^»]*(?:»|\Z)")


def statement_end(text: str) -> int:
    """Where a declaration's statement ends: at its own `:=`, the first one outside
    brackets, comments and strings, so that a binder's default value (`(h : p := by
    simp)`) or a comment holding `:=` does not end it early. The end of `text` if none.
    Comments and string and character literals are read as Lean reads them, by the
    scripts' one reader (heath.read_lean, #206, #349), which blanks them in place: so
    `/-/- -/` is a whole comment, a `'"'` is a character, not a string, and a `'('` is a
    character, not a bracket. Each «…» name is blanked here too, whole (LEAN_NAME), as
    check_fidelity blanks them, since the reader blanks only a name's `[` and `]`: so a
    `:=` or a bracket within a name is no `:=` and no bracket. Where the reader cannot
    read a literal for certain before the `:=` it finds, or a string holds a `{`, whose
    braces the reader may keep as a hole of code, the statement runs to the end of the
    text, so that the guard compares more of it, never less."""
    strings: list = []
    code, unsure = heath.read_lean(text, strings)
    unsure = unsure + [k for k, s in strings if "{" in s]
    code = LEAN_NAME.sub(lambda m: re.sub(r"[^\n]", " ", m[0]), code)
    n, depth = len(text), 0
    for i, c in enumerate(code):
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and code.startswith(":=", i):
            return n if any(k < i for k in unsure) else i
    return n


def source_statement(src: str, n: int, name: str | None) -> str | None:
    """The statement of `theorem PropN` (or `PropN.<name>`) as written in the Lean: its
    binders and type, up to its own `:=`, whitespace made single (so a re-wrapped
    statement is the same statement, and a changed binder on a re-wrapped line is not).
    The docstring is left out: it is Heath's enunciation, which check_fidelity compares
    with heath/."""
    if name is None:
        span = heath.theorem_span(src, n)
        if span is None:
            return None
        text = src[span.body:span.end]
    else:
        m = re.search(r"(?m)^theorem Prop%d\.%s\s" % (n, re.escape(name)), src)
        if not m:
            return None
        text = src[m.end():]
    return " ".join(text[:statement_end(text)].split())


def facts_statements(text: str | None) -> dict[str, str | None]:
    if not text:
        return {}
    try:
        facts = json.loads(text)
    except json.JSONDecodeError:
        return {}
    return {p["ref"]: p.get("statement") for p in facts.get("propositions", []) if "ref" in p}


LEAN_FILE = re.compile(r"^Elements/Book([IVX]+)/Prop(\d+)\.lean$")


def lean_files(repo, rev) -> dict[tuple[str, int], str]:
    out = git(repo, "ls-tree", "-r", "--name-only", rev, "--", "Elements")
    found = {}
    for path in out.splitlines():
        m = LEAN_FILE.match(path)
        if m:
            found[(m.group(1), int(m.group(2)))] = path
    return found


def ref_count(text: str, ref: str) -> int:
    """How often `text` names the proposition of `ref`: "III.16", "III. 16" or
    `BookIII.Prop16`. A porism or companion is named by its proposition. "III.1" is
    not named by "III.16", nor "I.1" by "III.1" or "I.10"."""
    r = heath.parse_ref(ref)
    plain = r"(?<![\w.])%s\.\s?%d(?!\d)" % (r.book, r.n)
    lean = r"(?<!\w)Book%s\.Prop%d(?!\d)" % (r.book, r.n)
    return len(re.findall(plain, text)) + len(re.findall(lean, text))


def names_ref(text: str, ref: str) -> bool:
    return ref_count(text, ref) > 0


def invisible(char: str) -> bool:
    """Is `char` one that an entry, or the folder's README, may not hold? A control
    character but a tab and a line feed (a carriage return among them), a format character
    (Unicode's Cf, as a zero-width space or a byte-order mark), a line or paragraph
    separator, another default-ignorable character (IGNORABLE), a character of the fixed
    list BLANK_GLYPHS, which render blank, or a code point Unicode keeps for private use or
    leaves unassigned (its Co and Cn, as this Python's Unicode data has them), which no
    font is bound to draw: each could hide a copy of an older entry from the comparison,
    or make Git and a reader see different lines. render.py refuses the same characters."""
    category = unicodedata.category(char)
    return ((category == "Cc" and char not in "\t\n")
            or category in ("Cf", "Zl", "Zp", "Co", "Cn") or char in BLANK_GLYPHS
            or any(a <= ord(char) <= b for a, b in IGNORABLE))


def skeleton(text: str) -> str:
    """`text` as the decisions record compares it, so that a copy of an older entry that
    only looks different is read as the same: in Unicode's NFKC form, casefolded, each
    Cyrillic or Greek letter that looks like a Latin one read as that letter
    (LOOK_ALIKES), and every space separator (Unicode's Zs), and each character of
    BLANKS, read as a space. The letters are read so before NFKC, after it and after
    casefolding, since each step can turn one letter into another: NFKC turns the Greek
    lunate sigma into a final sigma, and a mathematical alpha into a Greek one, and
    casefolding a Greek iota with perispomeni gives an iota. Letters of other scripts
    that look like Latin ones are read as they are."""
    text = unicodedata.normalize("NFKC", text.translate(LOOK_ALIKES))
    text = text.translate(LOOK_ALIKES).casefold().translate(LOOK_ALIKES)
    return "".join(" " if char in BLANKS or unicodedata.category(char) == "Zs" else char
                   for char in text)


def record_words(text: str) -> list[str]:
    """`text`'s words as the decisions record compares them: its skeleton, split at
    whitespace."""
    return skeleton(text).split()


def record_line(text: str) -> str:
    """A line of the decisions record as the guards compare it: its words, read as
    `skeleton` reads them, joined by single spaces, so that its whitespace is collapsed
    inside the line and at its ends."""
    return " ".join(record_words(text))


class Record(NamedTuple):
    lines: set[str]     # every line of the record, as record_line gives it
    runs: set[str]      # every SHARED_RUN consecutive words of each file, across its lines


def record_at(repo, base) -> Record:
    """The decisions record at the base: the page and every file under docs/decisions/,
    the README's included."""
    lines, runs = set(), set()
    tree = git(repo, "ls-tree", "-r", "-z", base, "--", DECISIONS, ENTRIES, binary=True)
    for item in tree.split(b"\0"):
        if not item:
            continue
        metadata, separator, path = item.partition(b"\t")
        fields = metadata.split()
        if (not separator or len(fields) != 3
                or fields[0] not in (b"100644", b"100755")
                or fields[1] != b"blob"
                or not (path == DECISIONS.encode() or path.startswith(ENTRIES.encode()))):
            raise Refusal(f"could not read the decisions record at {base}")
        try:
            text = git(repo, "cat-file", "blob", fields[2].decode("ascii"),
                       binary=True).decode("utf-8")
        except UnicodeError:
            raise Refusal(f"could not decode the decisions record at {base}") from None
        lines.update(record_line(line) for line in text.split("\n"))
        words = record_words(text)
        runs.update(" ".join(words[i:i + SHARED_RUN])
                    for i in range(len(words) - SHARED_RUN + 1))
    return Record(lines, runs)


IN_RECORD = "a line the decisions record holds already"
IN_RUN = f"in a run of {SHARED_RUN} or more words the decisions record holds too"


class Uncounted(NamedTuple):
    """A line of an entry that holds a word and does not count, and why: shown as a
    refusal names it, by its place and why, never by its text."""
    path: str
    number: int     # its line number in the entry
    text: str
    why: str        # IN_RECORD or IN_RUN

    def __str__(self) -> str:
        return f"{printable_text(self.path)}:{self.number}: {self.why}"


class EntryLines(NamedTuple):
    runs: list[Hunk]            # its runs of consecutive lines that count, each for gains()
    uncounted: list[Uncounted]  # each line that holds a word and does not count


def entry_lines(path: str, text: str, record: Record) -> EntryLines:
    """The lines of an entry the push adds, read against the record. A line counts when
    it holds a word, no line of the record matches it (record_line: IN_RECORD), and none
    of its words lies in a run of SHARED_RUN or more consecutive words, read across the
    entry's lines, that a file of the record holds too, read across its lines (IN_RUN):
    so a copy of an older entry, re-wrapped, recased or written with look-alike letters
    (skeleton), counts for nothing, whether kept beside its original or not. A copy with a
    word put in after every SHARED_RUN - 1 words holds no such run, nor does one reworded
    throughout, and this comparison cannot tell either from an entry of its own words.
    The runs of consecutive lines that count are hunks of their own, so that no words are
    joined across a line that does not count, or a blank line; each line that holds a
    word and does not count is kept with why, for a guard's refusal, which names those of
    them in which it finds a mention of what it asks for (uncounted)."""
    lines = text.split("\n")
    words = [(n, word) for n, line in enumerate(lines) for word in record_words(line)]
    copied = set()
    for i in range(len(words) - SHARED_RUN + 1):
        window = words[i:i + SHARED_RUN]
        if " ".join(word for _, word in window) in record.runs:
            copied.update(n for n, _ in window)
    hunks, run, uncounted = [], [], []
    for n, line in enumerate(lines):
        read = record_line(line)
        why = IN_RECORD if read in record.lines else IN_RUN if n in copied else None
        if read and not why:
            run.append(Added(path, n + 1, line))
            continue
        if read:
            uncounted.append(Uncounted(path, n + 1, line, why))
        if run:
            hunks.append(Hunk(path, [], run))
        run = []
    if run:
        hunks.append(Hunk(path, [], run))
    return EntryLines(hunks, uncounted)


def committed_on(repo, sha) -> datetime.date:
    """The day of `sha`'s committer date, on the committer's own calendar (in the time
    zone Git records with it); a refusal when Git gives none that can be read."""
    out = git(repo, "log", "-1", "--format=%cI", sha, "--").strip()
    try:
        return datetime.datetime.fromisoformat(out).date()
    except ValueError:
        raise Refusal(f"could not read the committer date of {sha}") from None


def today() -> datetime.date:
    """The runner's own date, on its own calendar, which bounds an entry's date with its
    commit's (entry_changes): the pusher sets the committer date, not this clock. A test
    puts a clock of its own in its place."""
    return datetime.date.today()


def spelled_otherwise(path: str) -> bool:
    """Is `path` one that a Mac's file system finds under docs/decisions/, though Git and
    GitHub do not? Its first two components, each in Unicode's NFD form and casefolded,
    as such a file system compares names, read as docs and decisions, but are spelled
    otherwise: docs/Decisions/, or docs/deciſions/ with a long s (U+017F), which
    casefolds to an s, as Git's own case-blind matching (:(icase)) does not see."""
    parts = path.split("/")[:2]
    read = [unicodedata.normalize("NFD", unicodedata.normalize("NFD", part).casefold())
            for part in parts]
    return read == ENTRIES.split("/")[:2] and parts != ENTRIES.split("/")[:2]


# A character that `invisible` refuses, as a refusal names it.
HIDDEN = ("a character an entry or the README may not hold (a control character but a tab "
          "and a line feed, a format character, a line or paragraph separator, another "
          "default-ignorable one, one that renders blank, or a private-use or unassigned "
          "code point)")


def folder_text(repo, sha, path: str, refused: list[str]) -> str | None:
    """The text of `path`, a regular file of docs/decisions/ that the commit `sha` adds or
    changes; or None, with the refusal added to `refused`, when it is no UTF-8 text, or
    holds a character that `invisible` refuses, named by its line."""
    try:
        text = git(repo, "cat-file", "blob", f"{sha}:{path}", binary=True).decode("utf-8")
    except UnicodeError:
        refused.append(f"{printable_text(path)}: not UTF-8 text")
        return None
    hidden = next(((n, c) for n, line in enumerate(text.split("\n"), 1) for c in line
                   if invisible(c)), None)
    if hidden:
        refused.append(f"{printable_text(path)}:{hidden[0]}: U+{ord(hidden[1]):04X}, {HIDDEN}")
        return None
    return text


def entry_changes(repo, base, sha) -> tuple[list[str], dict[str, EntryLines]]:
    """What the commit does under docs/decisions/: the changes refused, and the entries it
    adds, each read against the record (entry_lines). An entry is dated history, added
    once and never changed: an entry at the base may not be modified, deleted or renamed,
    and Git's rename detection (every file there at the base a source, with no limit)
    finds a move with edits. An entry that copies another, or the page, in part or whole,
    is not refused for it: the lines entry_lines finds copied count for nothing, and a
    short entry that shares a line with an older one is still an entry. The README is no
    entry: it may be edited, and supplies no approval, but once added it stays, a regular
    file, never a link, so that the folder origin/main holds is never taken away (the
    revert that revert_advice gives restores it); added or changed, it is UTF-8 text
    holding no character that `invisible` refuses, so that a later push can read the
    record. A file added there is a regular file: the README, or an entry named
    <YYYY-MM-DD>-<slug>.md with a valid date, from FIRST_ENTRY to the day after the
    earlier of the committer date of `sha`, which the pusher sets, and the runner's own
    date (today), a day's grace for the time zones between the entry's writer and the
    runner; and UTF-8 text holding no character that `invisible` refuses. Every path the
    commit changes, in or out of the folder, is read as a Mac's file system reads it, and
    one spelled otherwise than docs/decisions/ is refused (spelled_otherwise): such a
    file system finds it there, and Git does not. Each path a refusal names is printed
    with its control and format characters, and any other a terminal could act on,
    written as escapes (printable_text)."""
    names = git(repo, "diff", "--name-only", "-z", "--no-renames", base, sha)
    refused = [f"{printable_text(path)}: spelled otherwise than {ENTRIES}, which Git and "
               "GitHub tell apart by case" for path in names.split("\0")
               if path and spelled_otherwise(path)]
    out = git(repo, "diff", "--raw", "-z", "--no-abbrev", "-M", "-l0", base, sha,
              "--", ENTRIES)
    parts = out.split("\0")
    added, i = [], 0
    while i < len(parts) - 1:
        fields = parts[i].lstrip(":").split()
        if len(fields) != 5 or not fields[4]:
            raise Refusal(f"could not read the changes to {ENTRIES} from {base} to {sha}")
        status, mode = fields[4][0], fields[1]
        path = parts[i + 2] if status in "RC" else parts[i + 1]
        shown = printable_text(path)
        if not path.startswith(ENTRIES):
            refused.append(f"{shown}: spelled otherwise than {ENTRIES}, which Git and GitHub "
                           "tell apart by case")
        if status in "RC":
            refused.append(f"{shown}: {'renamed' if status == 'R' else 'copied'} "
                           f"from {printable_text(parts[i + 1])}")
            i += 3
            continue
        i += 2
        if path == ENTRIES_README:
            if status == "D":
                refused.append(f"{shown}: deleted (the README, once added, stays)")
            elif status not in "AMT":
                refused.append(f"{shown}: changed ({status})")
            elif mode not in ("100644", "100755"):
                refused.append(f"{shown}: not a regular file (mode {mode})")
            else:
                folder_text(repo, sha, path, refused)
            continue
        if status in "MT":
            refused.append(f"{shown}: changed")
        elif status == "D":
            refused.append(f"{shown}: deleted")
        elif status != "A":
            refused.append(f"{shown}: changed ({status})")
        elif mode not in ("100644", "100755"):
            refused.append(f"{shown}: not a regular file (mode {mode})")
        elif path.startswith(ENTRIES):
            added.append(path)
    entries, record, last = {}, None, None
    for path in added:
        shown = printable_text(path)
        match = DECISION_ENTRY.fullmatch(path)
        if match:
            try:
                day = datetime.date.fromisoformat(match.group(1))
            except ValueError:
                match = None
        if not match:
            refused.append(f"{shown}: neither the README nor an entry named "
                           "<YYYY-MM-DD>-<slug>.md with a valid date")
            continue
        if day < FIRST_ENTRY:
            refused.append(f"{shown}: dated before {FIRST_ENTRY}, the day the entries began")
            continue
        if last is None:
            last = min(committed_on(repo, sha), today()) + datetime.timedelta(days=1)
        if day > last:
            refused.append(f"{shown}: dated after {last}, the day after the earlier of "
                           f"{sha[:12]}'s committer date and this machine's date")
            continue
        text = folder_text(repo, sha, path, refused)
        if text is None:
            continue
        if not text.strip():
            refused.append(f"{shown}: holds no text")
            continue
        if record is None:
            record = record_at(repo, base)
        entries[path] = entry_lines(path, text, record)
    return list(dict.fromkeys(refused)), entries


def entry_hunks(repo, base, sha) -> list[Hunk]:
    """The runs of lines that count in the entries the commit adds; none while it
    refuses anything under docs/decisions/ (guard_entries refuses it), so that a rename,
    or a deletion and re-addition of an entry, renews no approval."""
    refused, entries = entry_changes(repo, base, sha)
    return [] if refused else [h for e in entries.values() for h in e.runs]


def uncounted(repo, base, sha, finds) -> str:
    """For the refusal of a guard that asks for a new line: the lines of the entries the
    commit adds that hold a word and did not count (entry_lines), each with why, those
    alone in which `finds`, the guard's own reading of a line given its text and its
    entry's path, finds a mention of something the guard found no new line naming, so
    that a code fence, or a line that names nothing it asks for, is never named; and how
    an entry names a thing so that it counts. Or, while guard_entries refuses a change
    under docs/decisions/, that no line of an entry counted. Empty when there is neither.
    A line added to the decisions page is compared with nothing, and is never named
    here."""
    refused, entries = entry_changes(repo, base, sha)
    if refused:
        return (f"\nno line of an entry counts while the guard of the decision entries "
                f"refuses a change under {ENTRIES}")
    lines = [line for e in entries.values() for line in e.uncounted
             if finds(line.text, line.path)]
    if not lines:
        return ""
    return ("\nlines of the entries added that did not count, each naming what is missing "
            "here (an entry names each file, statement and lock in a sentence of its own, "
            "never on a line or in a list repeated from an older entry):\n"
            + "\n".join(f"  {line}" for line in lines))


def decision_hunks(repo, base, sha) -> list[Hunk]:
    """The decisions record's changes, as gains() reads them: the page's hunks, removed
    lines kept, so that editing an old mention adds none; and the entries' runs of lines
    that count (entry_hunks)."""
    return diff_hunks(repo, base, sha, DECISIONS) + entry_hunks(repo, base, sha)


def guard_statements(repo, base, sha, wt: Path, rep: Report) -> list[str]:
    """The statements changed with a brief or decision naming them, for the body."""
    t = time.time()
    old_facts = facts_statements(show(repo, base, "facts.json"))
    new_facts = facts_statements((wt / "facts.json").read_text()
                                 if (wt / "facts.json").exists() else None)
    old_files, new_files = lean_files(repo, base), lean_files(repo, sha)
    refs = set(old_facts) | set(new_facts)
    sources = {}
    for files, rev in ((old_files, base), (new_files, sha)):
        for (book, n), path in files.items():
            src = show(repo, rev, path) or ""
            sources[(rev, path)] = src
            refs.add(f"{book}.{n}")
            if re.search(r"(?m)^theorem Prop%d\.porism\s" % n, src):
                refs.add(f"{book}.{n} Por.")
    briefs = diff_hunks(repo, base, sha, BRIEFS)
    entries = entry_hunks(repo, base, sha)
    changed, approved, new, unnamed = [], [], [], []
    for ref in sorted(refs, key=lambda r: (heath.prop_key(r), r)):
        r = heath.parse_ref(ref)
        path = f"Elements/Book{r.book}/Prop{r.n:02d}.lean"
        old_src = sources.get((base, path))
        new_src = sources.get((sha, path))
        old_sig = source_statement(old_src, r.n, r.name) if old_src else None
        new_sig = source_statement(new_src, r.n, r.name) if new_src else None
        why = []
        if old_sig is not None and new_sig is None:
            why.append("its theorem is gone from the Lean")
        elif old_sig is not None and old_sig != new_sig:
            why.append("the Lean statement changed")
        if old_facts.get(ref) and new_facts.get(ref) and old_facts[ref] != new_facts[ref]:
            why.append("facts.json's statement changed")
        if ref in old_facts and ref not in new_facts:
            why.append("its facts.json entry is gone")
        if not why:
            if old_sig is None and ref not in old_facts:
                new.append(ref)
            continue
        brief_named = gains(briefs, lambda text: ref_count(text, ref))
        entry_named = gains(entries, lambda text: ref_count(text, ref))
        if brief_named or entry_named:
            source = BRIEFS if brief_named else "docs/decisions/"
            approved.append(f"{ref} ({'; '.join(why)}), named in the {source} lines added")
        else:
            unnamed.append(ref)
            changed.append(f"{ref}: {'; '.join(why)}, and no new line in docs/briefs/ "
                           "or docs/decisions/ "
                           f"(a brief's revision or a decisions entry) names {r.parent}; "
                           "the push must add a mention: an old line that already named "
                           "it, edited in place, does not count")
    seconds = time.time() - t
    count = len(refs) - len(new)
    notes = []
    if approved:
        notes.append("changed with a brief or decision naming them: " + ", ".join(approved))
    if new:
        notes.append(f"new statements (not changes): {', '.join(new)}")
    if changed:
        def finds(text, source):
            return any(ref_count(text, ref) for ref in unnamed)

        rep.add("3", "statements", "FAIL",
                "\n".join(changed + notes) + uncounted(repo, base, sha, finds), seconds)
    else:
        rep.add("3", "statements", "ok",
                "\n".join([f"{count} statements compared in facts.json and the Lean"] + notes),
                seconds)
    return approved


LOCK_MENTION = re.compile(r"(?i)\baxioms\.lock\b|\baxiom lock\b")


def guard_lock(repo, base, sha, rep: Report) -> None:
    if git_ok(repo, "diff", "--quiet", f"{base}..{sha}", "--", LOCK):
        rep.add("3", "axiom lock", "ok", f"{LOCK} unchanged")
        return
    if gains(decision_hunks(repo, base, sha), lambda t: len(LOCK_MENTION.findall(t))):
        rep.add("3", "axiom lock", "ok", f"{LOCK} changed, and {DECISIONS} or an entry in "
                "docs/decisions/ gains a line mentioning the lock")
    else:
        rep.add("3", "axiom lock", "FAIL", f"{LOCK} changed, and no new line in {DECISIONS} "
                "or an entry in docs/decisions/ mentions the lock (\"axioms.lock\" or "
                "\"axiom lock\"; the push must add a "
                "mention: an old line that already mentioned it, edited in place, does not "
                "count)" + uncounted(repo, base, sha,
                                     lambda text, source: bool(LOCK_MENTION.search(text))))


# Where a mention of a path may start (mention): at the start of the text, or after
# whitespace or one of ( < [ ` " ' *, as prose and Markdown set a path down; after no other
# character, so that ~/mishnah/test/, C:/mishnah/test/, @/mishnah/test/,
# https://example.com/mishnah/test/ or x+mishnah/test/ names no mishnah/test/. An
# underscore is a word character, after which origin/main's guards counted no path:
# _mishnah/test/ names the longer path _mishnah/test/, and an emphasis made with
# underscores ends in one, which no mention may be followed by either.
MENTION_START = r"(?<![^\s(<\[`\"'*])"


def mention(path: str, directory: bool = False) -> re.Pattern:
    """A mention of `path`, for path_mentions: whole, starting where MENTION_START allows,
    its group `prefix` a / that anchors it at the root or the ./ and ../ steps of a
    relative link (its group `anchor` when there is either), and never the head of a
    longer path. A file may be followed by a full stop that ends a sentence, or by 's, but
    by no word character, / or -, after a full stop or not, so that Audit.lean.orig names
    no Audit.lean. A directory may close with its slash or not, and be followed by no word
    character, / or -; and by a full stop that ends a sentence only when its mention holds
    a slash (mishnah/test., figures/. or /figures.), never with one of those or another
    full stop after it, so that mishnah/test/note.md, mishnah/tests/, mishnah/test-old/,
    mishnah/test.md or mishnah/test.. names no mishnah/test/. A directory at the root
    named bare, as figures, is a word of prose too, and may be followed by no full stop,
    as origin/main's guards read it: "the figures." names no figures/."""
    after = r"(?![\w/-]|\.[\w./-])"
    if not directory:
        end = r"(?!\.?[\w/-])"
    elif "/" in path:
        end = r"/?" + after
    else:
        end = r"(?(anchor)/?%s|(?:/%s|(?![\w./-])))" % (after, after)
    return re.compile(r"%s(?P<prefix>(?P<anchor>/|(?:\.\.?/)+)?)%s%s"
                      % (MENTION_START, re.escape(path), end))


def path_mentions(text: str, source: str, path: str, pattern: re.Pattern) -> int:
    """How many mentions of `path` `text`, a line or lines of `source`, a file of the
    decisions record, holds, as `pattern` finds them (mention), its group `prefix` what
    stands before the path. The path counts whole, from the repository's root or anchored
    there (/model/lock.sha256), or by a relative link that resolves from the folder of
    `source`, docs/briefs/ for the page and docs/decisions/ for an entry, to exactly
    `path`, as check_links.py reads one."""
    return sum(not m.group("prefix").startswith(".")
               or posixpath.normpath(posixpath.join(posixpath.dirname(source), m.group()))
               == path
               for m in pattern.finditer(text))


def names_path(hunks: list[Hunk], path: str, pattern: re.Pattern) -> bool:
    """Does a hunk of the decisions record gain a mention of `path` (path_mentions)? Each
    hunk, and so each run of an entry's lines that count, is read on its own."""
    return any(gains([h], lambda text: path_mentions(text, h.path or DECISIONS, path, pattern))
               for h in hunks)


def guard_protected(repo, base, sha, rep: Report) -> list[str]:
    """A protected path changes only with a new line in the decisions page or an entry
    naming the file; the pull request then carries the label security-review.
    The files, for the body and the merge."""
    files = protected_files(repo, base, sha)
    if not files:
        rep.add("3", "protected paths", "ok", "none changed")
        return []
    decisions = decision_hunks(repo, base, sha)

    # The path whole, from the repository's root, or from the decision's file by a relative
    # link resolved from its folder (../../), or anchored at the root (/model/lock.sha256), as
    # check_links.py reads one (names_path); never the tail of a longer path (mention), so
    # that a line naming tests/model/lock.sha256 or ~/model/lock.sha256 names no
    # model/lock.sha256, nor one naming model/lakefile.toml the root's lakefile.toml; nor its
    # head, so that a line naming Audit.lean.orig names no Audit.lean, though Audit.lean.
    # ending a sentence, or Audit.lean's, does.
    def named(path):
        return names_path(decisions, path, mention(path))

    unnamed = [p for p in files if not named(p)]
    if unnamed:
        def finds(text, source):
            return any(path_mentions(text, source, p, mention(p)) for p in unnamed)

        rep.add("3", "protected paths", "FAIL",
                f"changed with no new line in {DECISIONS} or an entry in docs/decisions/ "
                f"naming them: {', '.join(unnamed)} "
                f"(a protected change is named file by file in a decisions entry, and its "
                f"pull request carries the label {SECURITY_LABEL})"
                + uncounted(repo, base, sha, finds))
    else:
        source = (f"{DECISIONS} or {ENTRIES}" if any(under(h.path or "", (ENTRIES,))
                                                     for h in decisions) else DECISIONS)
        rep.add("3", "protected paths", "ok",
                f"changed, each named in {source}: {', '.join(files)}; the pull request "
                f"carries the label {SECURITY_LABEL}, and needs /security-review")
    return files


COMMENT = re.compile(r"<!--.*?-->", re.S)
LEAF_RANGE = re.compile(r"\bn(\d+)\s*[–-]\s*n(\d+)\b")
LEAF = re.compile(r"\bn(\d+)\b")
LEAF_WORD = re.compile(r"(?i)\bleaf\b|\bleaves\b")
SOURCE_COMMENT = re.compile(r"(?i)<!--\s*source\s*:")


def own_leaves(text: str) -> set[int]:
    """The scan leaves a heath file's source comment (its first comment) names."""
    m = COMMENT.search(text)
    if not m:
        return set()
    source = m.group(0)
    leaves = set()
    for a, b in LEAF_RANGE.findall(source):
        leaves |= set(range(int(a), int(b) + 1))
    leaves |= {int(x) for x in LEAF.findall(source)}
    return leaves


def guard_heath(repo, base, sha, wt: Path, rep: Report) -> None:
    files = changed_files(repo, base, sha, "heath")
    if not files:
        rep.add("3", "heath/", "ok", "unchanged")
        return
    added: dict[str, set[int]] = {}
    for a in added_lines(repo, base, sha, "heath"):
        added.setdefault(a.path, set()).add(a.line)
    bad, good = [], []
    for status, path in files:
        if status == "D":
            bad.append(f"{path}: deleted (a change to heath/ is made against the page image "
                       "and carries a comment naming the leaf checked)")
            continue
        text = (wt / path).read_text(errors="replace")
        # The leaves are origin/main's: a change cannot widen its own source comment.
        old = show(repo, base, path)
        leaves = own_leaves(old if old is not None else text)
        lines = added.get(path, set())
        named = set()
        source = COMMENT.search(text)
        for m in COMMENT.finditer(text):
            # The source comment, the file's first, lists the leaves; it does not check
            # one. It is known by its place, so that "Source:" rewritten as "source:"
            # does not make it count; and any comment that reads as one is skipped too.
            if m.start() == source.start() or SOURCE_COMMENT.match(m.group(0)):
                continue
            first = text.count("\n", 0, m.start()) + 1
            last = first + m.group(0).count("\n")
            if lines & set(range(first, last + 1)) and LEAF_WORD.search(m.group(0)):
                named |= {int(x) for x in LEAF.findall(m.group(0))}
        checked = named & leaves if leaves else named
        if checked:
            good.append(f"{path} (leaf {', '.join(f'n{x}' for x in sorted(checked))})")
        elif named:
            bad.append(f"{path}: the comment added names leaf "
                       f"{', '.join(f'n{x}' for x in sorted(named))}, not one of its own "
                       f"pages' leaves ({', '.join(f'n{x}' for x in sorted(leaves))}, as "
                       "origin/main's copy of its source comment lists them)")
        else:
            bad.append(f"{path}: changed, with no comment in the change naming the scan leaf "
                       "checked (docs/STYLE.md, section 5)")
    if bad:
        rep.add("3", "heath/", "FAIL", "\n".join(bad + [f"checked: {g}" for g in good]))
    else:
        rep.add("3", "heath/", "ok", "each change names a leaf checked: " + ", ".join(good))


def guard_directories(repo, base, sha, rep: Report) -> None:
    def dirs(rev):
        out = git(repo, "ls-tree", "-r", "-d", "--name-only", rev, "--", *GUARDED_DIRS)
        return set(out.splitlines())

    gone = sorted(dirs(base) - dirs(sha))
    top = [d for d in gone if not any(d.startswith(p + "/") for p in gone)]
    if not top:
        rep.add("3", "directories", "ok", f"none deleted under {', '.join(GUARDED_DIRS)}")
        return
    decisions = decision_hunks(repo, base, sha)

    # The directory whole, with its closing slash or without, read as guard_protected reads
    # a path (names_path, mention): never the tail of a longer path, nor its head, so that a
    # line naming tests/mishnah/test/, ~/mishnah/test/, mishnah/test/note.md or
    # mishnah/tests/ names no mishnah/test/, though mishnah/test. ending a sentence does;
    # and "the figures." names no figures/, though figures/. does.
    def named(d):
        return names_path(decisions, d, mention(d, directory=True))

    unnamed = [d for d in top if not named(d)]
    if unnamed:
        def finds(text, source):
            return any(path_mentions(text, source, d, mention(d, directory=True))
                       for d in unnamed)

        rep.add("3", "directories", "FAIL", f"deleted with no new line in {DECISIONS} "
                "or an entry in docs/decisions/ "
                f"naming them: {', '.join(d + '/' for d in unnamed)}"
                + uncounted(repo, base, sha, finds))
    else:
        rep.add("3", "directories", "ok", f"deleted, each named in {DECISIONS} or "
                "docs/decisions/: "
                f"{', '.join(d + '/' for d in top)}")


PLAIN_PATH = re.compile(r"[\x21-\x7e]+")      # printable ASCII, the space excluded


def path_fold(s: str) -> str:
    """A path as a case-insensitive disk compares it: NFC, casefolded, then NFC again."""
    return unicodedata.normalize("NFC", unicodedata.normalize("NFC", s).casefold())


def path_shown(path: str) -> str:
    """A path as it is when plain, else escaped, so that a space shows, and two spellings
    that look alike (é, and e with a combining accent) differ on the page."""
    return path if PLAIN_PATH.fullmatch(path) else ascii(path)


def path_faults(paths: list[str], directories: list[str] | tuple[str, ...] = ()) -> list[str]:
    """What guard_paths refuses in a tree's paths, a line each: a path that is not plain
    printable ASCII, since HFS+ and APFS ignore or fold some code points that casefolding
    and NFC keep; a protected path or a check input spelt otherwise (LAKEFILE.lean,
    Scripts/x.py), which such a disk opens as the one the rules name, whether or not the
    tree holds that one; and paths, or folders of them, equal under path_fold (a file or a
    folder listed twice, or a file and a folder of one name, among them), named where they
    first meet, with their twins. The directories are the tree's own folder entries, an
    empty one among them, judged as its paths are."""
    def listing(under: list[str]) -> str:
        more = f" and {len(under) - 3} more" if len(under) > 3 else ""
        return ", ".join(path_shown(f) for f in under[:3]) + more

    faults = []
    all_paths = [*paths, *directories]
    for p in all_paths:
        odd = sorted({c for c in p if not PLAIN_PATH.fullmatch(c)})
        if odd:
            faults.append(f"{path_shown(p)}: not plain printable ASCII "
                          f"({', '.join(f'U+{ord(c):04X}' for c in odd)})")
    # #186: the protected-path rule and keep_apart compare spellings, so a
    # name they protect, spelt otherwise, is refused here, its twin in the tree or not.
    named = {path_fold(q.rstrip("/")): q for q in PROTECTED + CHECK_INPUTS}
    respelt: dict[str, tuple[str, list[str]]] = {}   # a spelling -> (the name, paths under it)
    for p in all_paths:
        parts = p.split("/")
        for i in range(1, len(parts) + 1):
            name = "/".join(parts[:i])
            own = named.get(path_fold(name))
            if own is not None and name != own.rstrip("/"):
                key = name + "/" if i < len(parts) else name
                respelt.setdefault(key, (own, []))[1].append(p)
                break
    for key in sorted(respelt):
        own, under = respelt[key]
        shown = f"{path_shown(key)} ({listing(under)})" if key.endswith("/") else path_shown(key)
        faults.append(f"{shown}: the protected path {own}, spelt otherwise, which a "
                      f"case-insensitive disk (macOS's default) opens as {own}, unseen by the "
                      "protected-path rule and keep_apart")
    met: dict[str, list[str]] = {}       # a fold -> its spellings: a folder once, with "/"
    files: dict[str, list[str]] = {}     # a folder, with "/" -> the paths under it
    directory_names = set()
    for directory in directories:
        folder = directory + "/"
        if folder not in directory_names:
            met.setdefault(path_fold(directory), []).append(folder)
            directory_names.add(folder)
        parts = directory.split("/")
        for i in range(1, len(parts)):
            parent = "/".join(parts[:i]) + "/"
            if parent not in directory_names:
                met.setdefault(path_fold(parent[:-1]), []).append(parent)
                directory_names.add(parent)
            files.setdefault(parent, []).append(directory)
    for directory, n in Counter(directories).items():
        if n > 1:
            met.setdefault(path_fold(directory), []).extend([directory + "/"] * (n - 1))
    for p in paths:
        parts = p.split("/")
        for i in range(1, len(parts)):
            folder = "/".join(parts[:i]) + "/"
            if folder not in directory_names:
                met.setdefault(path_fold(folder[:-1]), []).append(folder)
                directory_names.add(folder)
            files.setdefault(folder, []).append(p)
        met.setdefault(path_fold(p), []).append(p)
    twins = {key for key, spellings in met.items() if len(spellings) > 1}
    for key in sorted(twins):
        if "/" in key and key.rsplit("/", 1)[0] in twins:
            continue        # met already, at a folder above
        names = []
        for s in sorted(met[key]):
            under = files.get(s, [])
            names.append(f"{path_shown(s)} ({listing(under)})" if under else path_shown(s))
        faults.append(f"{' and '.join(names)}: equal once casefolded and NFC-normalised, "
                      "so a case-insensitive disk (macOS's default) checks them out as one, "
                      "the one over the other")
    return faults


PATH_STANDARD = "scripts/check_paths.py"


@contextlib.contextmanager
def off_path(repo):
    """sys.path without '', any entry that is not a string, and any entry inside the
    repository judged or this file's folder, so that origin/main's code run within imports
    no module planted there. An entry is inside when it, or a folder above it, is one of
    the two by file identity (os.path.samestat), followed as written and as resolved: a
    case variant on a case-insensitive disk, or a link into the repository, is caught. The
    same list, with its contents, is put back afterwards, whatever the code did to it."""
    roots = []
    for root in (repo, os.path.dirname(os.path.realpath(__file__))):
        with contextlib.suppress(OSError):
            roots.append(os.stat(root))

    def inside(entry) -> bool:
        if not isinstance(entry, str) or not entry:
            return True
        for start in (os.path.abspath(entry), os.path.realpath(entry)):
            here = start
            while True:
                with contextlib.suppress(OSError):      # a missing path is skipped
                    if any(os.path.samestat(os.stat(here), r) for r in roots):
                        return True
                if os.path.dirname(here) == here:
                    break
                here = os.path.dirname(here)
        return False

    kept, saved = sys.path, list(sys.path)
    try:
        sys.path = [p for p in saved if not inside(p)]
        yield
    finally:
        kept[:] = saved
        sys.path = kept


def base_standard(repo, base):
    """origin/main's scripts/check_paths.py, loaded from its blob as a module, or None when
    origin/main has none, as before the pull request that brings it. Nothing is written to
    disk; it is compiled as an import compiles it, without this file's __future__ import,
    and loaded as a module, not run as a script, so its trim of sys.path, which is a
    script's alone, never runs. It is loaded, and guard_paths calls its `findings`, under
    off_path, so that its imports find no module planted in the repository. `findings`
    judges a tree's (mode, path) entries, as its --rev does. A copy that cannot be read or
    loaded raises (SystemExit too), and guard_paths refuses on it."""
    if not git_ok(repo, "cat-file", "-e", f"{base}:{PATH_STANDARD}"):
        return None
    source = git(repo, "cat-file", "blob", f"{base}:{PATH_STANDARD}", binary=True)
    standard = types.ModuleType("origin_main_check_paths")
    # It reads __file__ only to find the repository it is run in, which is never asked here.
    standard.__file__ = str(Path(repo) / PATH_STANDARD)
    with off_path(repo):
        exec(compile(source, f"origin/main:{PATH_STANDARD}", "exec", dont_inherit=True),
             vars(standard))
    return standard


def guard_paths(repo, base, sha, rep: Report) -> bool:
    """Every path plain printable ASCII, no two of them, nor two folders of them, one name
    on a case-insensitive disk, and none a protected path or a check input spelt otherwise
    (#186): such a twin of a protected file or a check input is checked out over it, unseen
    by the protected-path rule and keep_apart. And every path kept to origin/main's own
    standard (base_standard), which judges the trees before any of the commit's code has
    run, so none can keep a path from it. It judges the tree of each commit the push brings
    (base..sha), each tree once, since the merge puts them all in main's history; a finding
    names, for each tree that holds it, the first commit with that tree, at most three and
    then "and N more". It reads the trees, not a worktree, which such a disk cannot hold,
    and check_commit runs it before the commit is checked out. A standard that does not
    load, or that fails on a tree (its fail() exits), refuses, naming the error. Whether
    both passed."""
    def judge(call):
        """call(), or None and the error it ends in, SystemExit too (check_paths' fail()),
        with what it printed: a crash refuses, and is never a traceback or a pass."""
        err = io.StringIO()
        try:
            with contextlib.redirect_stderr(err):
                return call(), None
        except (Exception, SystemExit) as e:
            said = err.getvalue().strip()
            return None, f"{e!r}" + (f": {said}" if said else "")

    standard, unloaded = judge(lambda: base_standard(repo, base))
    # "commit <sha>" and then its tree, for each commit, the oldest first and sha last.
    words = git(repo, "rev-list", "--reverse", "--format=%T", f"{base}..{sha}").split()
    commits = list(zip(words[1::3], words[2::3])) or [(sha, f"{sha}^{{tree}}")]
    found: dict[str, list[str]] = {}     # a fault -> the first commit of each tree holding it
    theirs: dict[str, list[str]] = {}    # the same, for origin/main's standard's findings
    counted: dict[str, int] = {}         # a tree judged -> its paths
    for commit, tree in commits:
        if tree in counted:
            continue
        out = git(repo, "ls-tree", "-r", "-t", "-z", "--full-tree", tree, binary=True)
        # Each entry: its mode, type and object, a tab and its path, as --rev reads them.
        records = [(fields.split(), path.decode("utf-8", "surrogateescape"))
                   for fields, tab, path in (e.partition(b"\t") for e in out.split(b"\0") if e)
                   if tab]
        entries = [(fields[0].decode("ascii", "replace"), path)
                   for fields, path in records if len(fields) == 3 and fields[1] != b"tree"]
        directories = [path for fields, path in records
                       if len(fields) == 3 and fields[1] == b"tree"]
        paths = [p for _, p in entries]
        counted[tree] = len(set(paths))
        for fault in path_faults(paths, directories):
            found.setdefault(fault, []).append(commit)
        if standard is not None:
            with off_path(repo):        # its imports in findings, too, read nothing planted
                # A copy from before its findings took the tree's folders judges the leaves;
                # asked inside judge, so a findings missing or uncallable refuses by name.
                def theirs_of():
                    if "directories" in inspect.signature(standard.findings).parameters:
                        named = standard.findings(entries, directories=directories)
                        return [str(f) for f in named]
                    return [str(f) for f in standard.findings(entries)]
                judged, crash = judge(theirs_of)
            if crash is not None:       # a crash of origin/main's check refuses, as a finding
                judged = [f"origin/main's {PATH_STANDARD} fails on the tree: {crash}"]
            for finding in judged:
                theirs.setdefault(finding, []).append(commit)

    def listed(faults: dict[str, list[str]]) -> str:
        lines = []
        for fault, held in faults.items():
            more = f" and {len(held) - 3} more" if len(held) > 3 else ""
            lines.append(f"{fault} (in {'commit' if len(held) == 1 else 'commits'} "
                         f"{', '.join(c[:12] for c in held[:3])}{more})")
        return "\n".join(lines)

    trees = f"the trees of {plural(len(commits), 'commit')}"
    if found:
        rep.add("3", "paths", "FAIL", listed(found))
    else:
        rep.add("3", "paths", "ok", f"{plural(counted[commits[-1][1]], 'path')} at {sha[:12]}, "
                f"and {trees}: each path plain printable ASCII, none a protected path spelt "
                "otherwise, and no two of them, nor two folders, equal once casefolded and "
                "NFC-normalised")
    name = "paths (origin/main's standard)"
    if unloaded is not None:
        rep.add("3", name, "FAIL", f"origin/main's {PATH_STANDARD} does not load: {unloaded}")
    elif standard is None:
        rep.add("3", name, "note", f"origin/main has no {PATH_STANDARD}, as before the pull "
                "request that brings it: there is no standard of origin/main's to judge the "
                "trees by")
    elif theirs:
        rep.add("3", name, "FAIL", listed(theirs))
    else:
        rep.add("3", name, "ok", f"origin/main's {PATH_STANDARD}, run before any of the "
                f"commit's code, finds nothing in {trees} (docs/WORKFLOW.md, \"File names\")")
    return not (found or theirs or unloaded)


def guard_entries(repo, base, sha, rep: Report) -> None:
    """Decision entries are dated history: a commit only adds them, beside the README,
    which stays once added. "no entry added" when it adds none, whatever edit it makes to
    the README."""
    refused, added = entry_changes(repo, base, sha)
    if refused:
        rep.add("3", "decision entries", "FAIL",
                f"{ENTRIES} holds its README and dated entries, regular files; an entry is "
                "history, added once and never changed or moved, and a correction is a new "
                "entry, in words of its own:\n" + "\n".join(refused))
    else:
        rep.add("3", "decision entries", "ok",
                f"added: {', '.join(added)}" if added else "no entry added")


def status_lines(wt: Path, excludes: list[str]) -> subprocess.CompletedProcess:
    return run(["git", "status", "--porcelain", "--", ".", *excludes], wt)


def guard_fidelity(wt: Path, rep: Report, logs: Path, label="", fail="FAIL") -> None:
    t = time.time()
    r = run([PY, "scripts/check_fidelity.py"], wt, env=tool_env())
    out = (r.stdout or "") + (r.stderr or "")
    (logs / f"03-check_fidelity{slug_of(label)}.log").write_text(out)
    seconds = time.time() - t
    if r.returncode == 0:
        rep.add("3", "review records" + label, "ok", "check_fidelity.py passes on the commit "
                "as committed: no record stale", seconds)
    else:
        rep.add("3", "review records" + label, fail,
                "check_fidelity.py fails on the commit as committed:\n" + tail(out, 25), seconds)


def guard_generated(wt: Path, rep: Report, logs: Path, label="", fail="FAIL",
                    excludes=()) -> None:
    """The generated pages are current: render.py, run on the commit as committed (its
    facts.json as committed), changes nothing. It needs no Lean, so it runs here, before
    the full checks, which run it again after the build. A failure of render.py itself
    (its check of docs/program.toml, say) is reported as "render.py", a verdict; stale
    pages as "generated pages", which keep_apart counts as freshness."""
    t = time.time()
    r = run([PY, "scripts/render.py"], wt, env=tool_env())
    out = (r.stdout or "") + (r.stderr or "")
    status = status_lines(wt, list(excludes))
    (logs / f"03-render{slug_of(label)}.log").write_text(
        f"{out}\n$ git status --porcelain\n{status.stdout}")
    seconds = time.time() - t
    name = "generated pages" + label
    if r.returncode != 0:
        rep.add("3", "render.py" + label, fail, "render.py fails on the commit as "
                "committed:\n" + tail(out, 25), seconds)
    elif status.returncode != 0 or status.stdout.strip():
        rep.add("3", name, fail, "stale: render.py, on the commit as committed, changes "
                "them; regenerate with python3 scripts/render.py and commit the result with "
                "its sources (docs/WORKFLOW.md, section 8):\n"
                + tail(status.stdout + status.stderr, 25), seconds)
    else:
        rep.add("3", name, "ok", "render.py changes nothing on the commit as committed", seconds)


def guard_foundations(repo, base, sha, rep: Report) -> None:
    """Not a guard: the foundations are the coordinator's, so their changes are listed."""
    files = changed_files(repo, base, sha, "Elements/Foundations")
    if files:
        rep.add("3", "foundations", "note", "changed (the coordinator's files): "
                + ", ".join(p for _, p in files))


def slug_of(label: str) -> str:
    """A pass's label, for a log file's name: " (the commit's checks)" -> "-the-commit-s-checks"."""
    s = re.sub(r"[^A-Za-z0-9]+", "-", label).strip("-")
    return f"-{s}" if s else ""


@contextlib.contextmanager
def base_copies(repo, base, sha, wt: Path, changes: list[tuple[str, str]]):
    """origin/main's copies of the check inputs the commit changes, put in place in the
    worktree (and the files the commit adds to them taken out); the worktree is reset
    to the commit, `sha`, afterwards, never to HEAD, which the checks run could move.
    Yields the pathspecs that keep them out of `git status`."""
    for status, path in changes:
        target = wt / path
        if target.is_symlink() or target.is_file():
            target.unlink()
        if status == "A":
            continue
        entry = git(repo, "ls-tree", "-z", base, "--", path).split("\0")[0]
        if not entry:
            continue
        mode, _, oid = entry.split("\t", 1)[0].split()
        data = git(repo, "cat-file", "blob", oid, binary=True)
        target.parent.mkdir(parents=True, exist_ok=True)
        if mode == "120000":
            os.symlink(data.decode(errors="replace"), target)
        else:
            target.write_bytes(data)
            os.chmod(target, 0o755 if mode == "100755" else 0o644)
    try:
        yield [f":(exclude,literal){p}" for _, p in changes]
    finally:
        run(["git", *DISK_AS_IS, "reset", "-q", "--hard", sha], wt)
        run(["git", *DISK_AS_IS, "clean", "-fdq"], wt)


BASE_PASS = " (origin/main's checks)"
# Steps whose failure with origin/main's copies shows only that the pages' generator
# changed (render.py's output, or the certificate that writes facts.json), not a check's
# verdict. render.py failing outright (step 3's "render.py", step 4's "python3
# scripts/render.py") is a verdict: it checks docs/program.toml, for one.
FRESHNESS = ("generated pages", EMPTY_CHECK)


# For `git worktree add`, and with DISK_AS_IS: files written and compared as the commit
# holds them, whatever the shared .git/config says. Code of this commit or one checked
# before can write that config, where core.fileMode=false lets git status pass a changed
# executable bit, and core.autocrlf=true, or attributes in the global attributes file
# (core.attributesFile, by default ~/.config/git/attributes) or in a tree attr.tree
# names, make git's own checkout write bytes the commit does not hold (eol,
# working-tree-encoding, a smudge filter), which git status then compares through, or
# git status pass a changed file (a clean filter). attr.tree is pinned to the empty
# tree, which git then reads in place of every .gitattributes, an ignored one on disk
# among them, so that none applies. The id is SHA-1's empty tree, as this repository and
# every clone of it are SHA-1, and git knows it without the object; a value git cannot
# resolve it ignores, reading .gitattributes again. The shared .git/info/attributes,
# which no setting turns off, at_commit refuses; the system attributes file, outside the
# clone, is not pinned.
AS_COMMITTED = ("-c", "core.fileMode=true", "-c", "core.autocrlf=false",
                "-c", "core.attributesFile=/dev/null",
                "-c", "attr.tree=4b825dc642cb6eb9a060e54bf8d69288fbee4904")
# Git's stat settings at their defaults, no fsmonitor, untracked cache or hook, and
# AS_COMMITTED's pins, for at_commit's commands and base_copies' reset and clean:
# in the shared .git/config, core.checkStat=minimal or core.trustctime=false lets git
# status pass a change of the same size with its time put back; the untracked cache or
# an fsmonitor hook can answer in git's place; and a hook in the shared .git/hooks
# (post-index-change, which git status and a reset run) can write a file once git has
# looked. core.hooksPath=/dev/null runs no hook, as git-config(1) documents.
DISK_AS_IS = ("-c", "core.checkStat=default", "-c", "core.trustctime=true",
              "-c", "core.fsmonitor=false", "-c", "core.untrackedCache=false",
              "-c", "core.hooksPath=/dev/null", *AS_COMMITTED)
# The build's caches, which a pass keeps; at_commit removes every other ignored file.
CACHES = ("/.lake", "/model/.lake")


def at_commit(wt: Path, sha: str) -> None:
    """Refused unless the worktree is the commit: its HEAD the commit, its index the
    commit's tree, no entry of the index flagged skip-worktree or assume-unchanged (which
    keep git from looking at the file on disk), and `git status --porcelain
    --untracked-files=all` empty, so that no file on disk differs from the index and none
    stands untracked beside them. Each is asked of git with stat settings at their
    defaults, no fsmonitor, untracked cache or hook, and, as worktrees are made, file
    modes compared and no conversion or attributes but the system's (DISK_AS_IS, attr.tree
    the empty tree), whatever the shared .git/config says, and refused while the shared
    .git/info/attributes exists; then every ignored file but the build's caches, .lake/
    and model/.lake/ (CACHES, a channel the commit's build already has, #197), is removed,
    so the next pass reads no scripts/json.pyc left behind. The commit's own code, run in
    an earlier pass (its render.py, say), could have changed any of these, and
    origin/main's checks, which read the index and the files, would judge another tree.
    This asks git and compares no bytes, so routes past it remain (a hand-edited index, a
    process left running, a .git below the root among them; #218), each needing code of
    this commit or one checked before to have run first, through a change to a protected
    script or its Lean at elaboration (#197)."""
    head = run(["git", *DISK_AS_IS, "rev-parse", "--verify", "--quiet", "HEAD"],
               wt).stdout.strip()
    indexed = git_ok(wt, *DISK_AS_IS, "diff-index", "--cached", "--quiet", sha, "--")
    if head != sha or not indexed:
        raise Refusal(f"before a pass of the checks, the worktree {wt} is no longer the "
                      f"commit {sha[:12]} (its HEAD is {head[:12] or 'unreadable'}, or its "
                      "index differs): something run in an earlier pass changed it")
    # The shared .git/info/attributes applies to every worktree whatever the settings say:
    # working-tree-encoding or eol there makes git's own checkout write bytes the commit
    # does not hold, and git status compare through them.
    found = run(["git", *DISK_AS_IS, "rev-parse", "--path-format=absolute", "--git-path",
                 "info/attributes"], wt)
    attributes = found.stdout.strip()
    if found.returncode != 0 or not attributes:
        raise Refusal("before a pass of the checks, git cannot name the info/attributes of "
                      f"the worktree {wt}")
    if os.path.lexists(attributes):
        raise Refusal(f"before a pass of the checks, {attributes} exists: attributes there "
                      "apply to every worktree of the clone, whatever git's settings say, "
                      f"and can make git's own checkout write bytes the commit {sha[:12]} "
                      "does not hold; remove it")
    # ls-files -v tags an entry H, S when skip-worktree, M when unmerged, and in lower case
    # when assume-unchanged: any tag but H is refused. A fresh worktree's entries are all H.
    tags = run(["git", *DISK_AS_IS, "ls-files", "-v", "-z"], wt, binary=True)
    flagged = [e[2:].decode(errors="replace") for e in tags.stdout.split(b"\0")
               if e and not e.startswith(b"H ")]
    status = run(["git", *DISK_AS_IS, "status", "--porcelain", "--untracked-files=all"], wt)
    listed = status.stdout.splitlines()

    def some(items: list[str]) -> str:
        return ", ".join(items[:3]) + (f" and {len(items) - 3} more" if len(items) > 3 else "")

    if tags.returncode != 0 or status.returncode != 0:
        why = "git ls-files -v or git status fails in it"
    elif flagged:
        why = f"flagged skip-worktree or assume-unchanged: {some(flagged)}"
    elif listed:
        why = f"git status lists {some(listed)}"
    else:
        # Only now, with nothing untracked but what is ignored: -x reads no ignore file,
        # so each ignored file goes, and only the -e patterns, the caches, are kept.
        keep = [arg for cache in CACHES for arg in ("-e", cache)]
        if run(["git", *DISK_AS_IS, "clean", "-ffdxq", *keep], wt).returncode == 0:
            return
        why = "git clean of its ignored files fails in it"
    raise Refusal(f"before a pass of the checks, the files on disk in the worktree {wt} may "
                  f"no longer be the commit {sha[:12]} ({why}): something run in an earlier "
                  "pass changed them")


def passes(repo, base, sha, wt: Path, changes: list[tuple[str, str]]):
    """(label, the outcome of a failure, status excludes) for each pass of the checks:
    with origin/main's copies of the check inputs; and, when the commit changes any,
    with the commit's own, which must pass, while a failure with origin/main's is noted
    for the security review (and refuses the commit, if it changes what the checks
    judge as well: keep_apart). Each begins at the commit, `sha` (at_commit)."""
    at_commit(wt, sha)
    if not changes:
        yield "", "FAIL", []
        return
    with base_copies(repo, base, sha, wt, changes) as excludes:
        yield BASE_PASS, "note", excludes
    at_commit(wt, sha)
    yield " (the commit's checks)", "FAIL", []


# The guides: the rules' text, which changes with the checks it describes; the decisions
# page, its dated entries and the briefs among them. The edition itself stays judged: the
# Lean, Heath's text, the commentary, the records, the figures, the reports and the reading
# list.
GUIDES = ("AGENTS.md", "CLAUDE.md", "CONTRIBUTING.md", "docs/WORKFLOW.md",
          "docs/FORMALIZATION.md", "docs/STYLE.md", "docs/briefs/", "docs/templates/",
          "docs/decisions/")
# A review record's stamp: its reviewer's reading of a statement, a Lean file and the
# record's own text, as a change to the certificate's output asks for (WORKFLOW, section
# 6). Not its stage. STAMPS: the stamp keys of each section.
STAMP_LINE = re.compile(r'(?m)^(?:fingerprint|commit|lean|text|reviewer)\s*=\s*"[^"]*"[ \t]*$\n?')
STAMPS = {"statement": ("fingerprint",), "review": ("commit", "lean", "text", "reviewer")}


def stamp_only(repo, base, sha, path: str) -> bool:
    """Is the change to `path` a review record's stamp alone: stamp lines rewritten, added
    or moved within their own section, none taken away from it, and nothing else changed,
    in the lines or in the record as TOML reads it (so a stamp-shaped line inside a
    multi-line string is no stamp)? A record TOML cannot read is judged."""
    if not re.fullmatch(r"review/[IVX]+/\d+\.toml", path):
        return False
    old, new = show(repo, base, path), show(repo, sha, path)
    if old is None or new is None or STAMP_LINE.sub("", old) != STAMP_LINE.sub("", new):
        return False
    try:
        before, after = tomllib.loads(old), tomllib.loads(new)
    except tomllib.TOMLDecodeError:
        return False
    for section, keys in STAMPS.items():
        if isinstance(before.get(section), dict) and isinstance(after.get(section), dict):
            if any(key in before[section] and key not in after[section] for key in keys):
                return False
            for table in (before[section], after[section]):
                for key in keys:
                    table.pop(key, None)
    return before == after


def judged_files(repo, base, sha) -> list[str]:
    """The files the commit changes that the checks judge: all but the protected paths
    (the check inputs among them, but not PROTECTED_JUDGED), the guides, what render.py
    writes, and a review record's stamp alone."""
    return sorted(p for _, p in changed_files(repo, base, sha)
                  if not (under(p, PROTECTED + GUIDES) and not under(p, PROTECTED_JUDGED))
                  and not (under(p, GENERATED) and not generated_parts(repo, base, sha, p)[1])
                  and not stamp_only(repo, base, sha, p))


def kept_expectations(old: str | None, new: str | None) -> bool:
    """Does the expectations file `new` keep every expectation of `old`, origin/main's
    (None when it has none)? Each of old's is still there, matched by its ref, field and
    law, which say what it reads: a ref or a law added or dropped makes it read something
    else. Its includes and excludes the same or grown, its count's prefix the same, its
    equals still there; only the values of count.is and equals may differ, and its why, the
    words shown when it fails. New expectations are fine. A removed expectation or field, a
    list shrunk, or a file that does not read, is not kept."""
    def entries(text: str | None) -> list[dict] | None:
        try:
            found = json.loads(text)["expectations"]
        except (TypeError, KeyError, json.JSONDecodeError):
            return None
        ok = isinstance(found, list) and all(isinstance(x, dict) for x in found)
        return found if ok else None

    def asks_as_much(y: dict, x: dict) -> bool:
        if any((key in y) != (key in x) for key in ("ref", "law")):
            return False
        for key, want in x.items():
            have = y.get(key)
            if key == "why":
                continue
            if key not in y:
                return False
            if key in ("includes", "excludes") and isinstance(want, list) \
                    and isinstance(have, list):
                if any(name not in have for name in want):
                    return False
            elif key == "count" and isinstance(want, dict) and isinstance(have, dict):
                if want.keys() != have.keys() or any(want[k] != have[k] for k in want
                                                     if k != "is"):
                    return False
            elif key != "equals" and have != want:
                return False
        return True

    olds, news = ([] if old is None else entries(old)), entries(new)
    if olds is None or news is None:
        return False
    return all(any(asks_as_much(y, x) for y in news) for x in olds)


def locked_axioms(text: str | None) -> dict | None:
    """The lock's [axioms] table, {name: statement}; None when it does not read, or the
    file is absent (`text` None: tomllib.loads(None) raises AttributeError before Python
    3.14, and TypeError from it)."""
    if text is None:
        return None
    try:
        table = tomllib.loads(text)["axioms"]
    except (TypeError, KeyError, tomllib.TOMLDecodeError):
        return None
    return table if isinstance(table, dict) else None


def model_laws(text: str | None) -> dict | None:
    """laws.toml, as {axiom: (the name of its law, whether it must fail in the hyperbolic
    plane)}; None unless it is a [laws] table of names and a [hyperbolic] table holding
    `fails`, a list of some of those axioms, and nothing else; None, too, when the file is
    absent (`text` None, as in locked_axioms)."""
    if text is None:
        return None
    try:
        data = tomllib.loads(text)
    except (TypeError, tomllib.TOMLDecodeError):
        return None
    laws, hyperbolic = data.get("laws"), data.get("hyperbolic")
    fails = hyperbolic.get("fails") if isinstance(hyperbolic, dict) else None
    if set(data) != {"laws", "hyperbolic"} or not isinstance(hyperbolic, dict) \
            or set(hyperbolic) != {"fails"} or not isinstance(laws, dict) \
            or not all(isinstance(v, str) for v in laws.values()) \
            or not isinstance(fails, list) or not all(isinstance(k, str) for k in fails) \
            or not set(fails) <= set(laws):
        return None
    return {k: (v, k in fails) for k, v in laws.items()}


def law_of(node: ast.stmt) -> str | None:
    """The law a statement of a harness defines: a function named `_` whose one decorator is
    `axiom('<name>', …)`; None for any other statement."""
    if not isinstance(node, ast.FunctionDef) or node.name != "_" or len(node.decorator_list) != 1:
        return None
    d = node.decorator_list[0]
    if isinstance(d, ast.Call) and isinstance(d.func, ast.Name) and d.func.id == "axiom" \
            and d.args and isinstance(d.args[0], ast.Constant) and isinstance(d.args[0].value, str):
        return d.args[0].value
    return None


def law_code(text: str | bytes | None) -> tuple[list[str], dict] | None:
    """A harness file's code: the statements at its top level that are not laws, each as
    its syntax tree prints (comments and its docstring, which are prose, aside); and its
    laws, by name. It reads the file as Python does, from its bytes, so a coding cookie is
    honoured: a line that reads as a comment in UTF-8 may be code under another encoding.
    None when it does not parse, or defines a law twice."""
    try:
        tree = ast.parse(text)
    except (TypeError, ValueError, SyntaxError):
        return None
    body = tree.body
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) \
            and isinstance(body[0].value.value, str):
        body = body[1:]
    rest, laws = [], {}
    for node in body:
        name = law_of(node)
        if name is None:
            rest.append(ast.dump(node))
        elif name in laws:
            return None
        else:
            laws[name] = node
    return rest, laws


# What a law's code may use: an allow-list, and anything it does not name is refused.
# Beside its own parameters and the names it binds, a global name in one role only, as
# each harness's laws use it: a function called (the model's helpers, each of which reads
# its arguments, draws from the random numbers it is given, and returns a value, while
# hyperbolic.py's make_circle also notes a point of the circle it makes in SEEDS, which
# the harness empties before every configuration); a value (search.py's right angle, RA);
# a table, only read through a subscript (hyperbolic.py's SEEDS); a module, only for an
# attribute in LAW_MATH; and, in a law's decorator, a generator named, or one made by a
# call with constants. The builtins the laws call, in either harness. The attributes they
# take of what they are given: of the random numbers the harness hands every law, which a
# law draws from and never reseeds (LAW_ATTRIBUTES); and the one method that changes a
# container, on a container the law made (LAW_MUTATORS). The letters of a decorator's
# kinds. Each entry is one some law needs: a test takes each away in turn, and a law is
# refused. Widening a list is a check change, in a pull request of its own.
LAW_GLOBALS = {
    "tests/model/search.py": {
        "call": frozenset({
            "Fr", "_angle_inside_hyp", "_area_line_hyp", "_cm_side", "ang",
            "area2", "between", "circles_meet", "collinear", "d2", "dot", "f_ang",
            "f_between", "f_lval", "f_on_circle", "f_on_line", "f_same_side", "feq", "fl",
            "inside", "is_centre", "is_right_angle", "lattice_on_line",
            "length", "line_circle_points", "line_through",
            "lines_meet", "mag_vals", "on_circle", "on_line", "opposite", "outside",
            "same_side", "sub", "triangle"}),
        "value": frozenset({"RA"}),
    },
    "tests/model/hyperbolic.py": {
        "call": frozenset({
            "F_circ", "Fr", "H", "K", "_angle_inside_hyp", "_area_line_hyp", "_cm_side",
            "ang", "ang_eq", "ang_zero", "area", "area_zero", "between", "centre",
            "ch2", "circles_meet", "collinear", "dist", "expmap", "f_ang", "f_dist",
            "f_on_circle", "f_point", "f_side", "feq", "in_disc", "inside",
            "is_centre", "is_right", "line_through", "lines_meet",
            "mag_vals", "make_circle", "meet_point", "mink", "on_circle", "on_line",
            "opposite", "outside", "pt_on_line", "pts_on_line",
            "roots_along", "same_side", "triangle", "unit_toward"}),
        "table": frozenset({"SEEDS"}),
        "generator": frozenset({
            "gs_angle", "gs_area_line", "gs_between", "gs_chord", "gs_circ_pts",
            "gs_cong", "gs_lc", "gs_lines_meet", "gs_p4", "gs_p5", "gs_pasch",
            "gs_rays", "gs_sup"}),
        "generator maker": frozenset({"gs_cm"}),
    },
}
LAW_BUILTINS = frozenset({"abs", "all", "any", "float", "len", "range", "set", "tuple"})
LAW_MODULES = frozenset({"math"})
LAW_MATH = frozenset({"cos", "dist", "hypot", "pi", "sin", "sqrt"})
LAW_ATTRIBUTES = frozenset({"randint", "random"})
LAW_MUTATORS = frozenset({"append"})
LAW_KINDS = frozenset({"P", "L_", "C_"})
# The syntax a law's body may hold: the statements, expressions and parts of them that the
# laws use, and the plain ones beside them (`break`, `continue`, `pass`, a conditional
# expression, a slice, a dict display or comprehension). Not an import, `global`,
# `nonlocal`, `:=`, `lambda`, `del`, `try`, `with`, `raise`, `assert`, `yield`, `await`,
# a class, a starred or annotated name, nor an f-string.
LAW_SYNTAX = (ast.Assign, ast.AugAssign, ast.Expr, ast.If, ast.For, ast.While, ast.Break,
              ast.Continue, ast.Pass, ast.Return, ast.FunctionDef, ast.BoolOp, ast.BinOp,
              ast.UnaryOp, ast.Compare, ast.IfExp, ast.Call, ast.Constant, ast.Name,
              ast.Attribute, ast.Subscript, ast.Slice, ast.Tuple, ast.List, ast.Set, ast.Dict,
              ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp, ast.comprehension,
              ast.keyword, ast.arguments, ast.arg, ast.expr_context, ast.operator,
              ast.boolop, ast.unaryop, ast.cmpop)
COMPREHENSIONS = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
# The calls that make a new container, beside a display or a comprehension; and the
# augmented assignments that a container of Python's own makes in place (a list's `+=`, a
# set's `|=`).
CONSTRUCTORS = frozenset({"list", "dict", "set", "bytearray"})
IN_PLACE = (ast.Add, ast.Sub, ast.Mult, ast.BitOr, ast.BitAnd, ast.BitXor)


def law_globals(path: str, role: str) -> frozenset:
    """The global names a law in the harness `path` may use in `role` (LAW_GLOBALS), the
    builtins among the calls and `math` among the modules."""
    common = {"call": LAW_BUILTINS, "module": LAW_MODULES}.get(role, frozenset())
    return LAW_GLOBALS.get(path, {}).get(role, frozenset()) | common


def law_decorator(d: ast.Call, path: str) -> bool:
    """Is a law's decorator, which law_of found to be `axiom('<name>', …)`, one the allow-list
    takes? Its kinds a `dict` of letters, `dict(A=P, L=L_, al=C_)`; and, where the harness
    takes a generator, one it names (`gs_p4`), or makes with constants (`gs_cm('side')`)."""
    gens, makers = law_globals(path, "generator"), law_globals(path, "generator maker")
    if d.keywords or len(d.args) not in ((2, 3) if gens or makers else (2,)):
        return False
    kinds, *gen = d.args[1:]
    if not (isinstance(kinds, ast.Call) and isinstance(kinds.func, ast.Name)
            and kinds.func.id == "dict" and not kinds.args
            and all(k.arg is not None and isinstance(k.value, ast.Name)
                    and k.value.id in LAW_KINDS for k in kinds.keywords)):
        return False
    if not gen:
        return True
    g = gen[0]
    return (isinstance(g, ast.Name) and g.id in gens) or (
        isinstance(g, ast.Call) and isinstance(g.func, ast.Name) and g.func.id in makers
        and not g.keywords and all(isinstance(a, ast.Constant) for a in g.args))


def scope_binds(nodes) -> set[str]:
    """The names a scope binds itself, from its statements (or a comprehension's targets):
    the names stored and the functions defined, and none bound in a scope inside it."""
    out, todo = set(), list(nodes)
    while todo:
        node = todo.pop()
        if isinstance(node, ast.Name) and not isinstance(node.ctx, ast.Load):
            out.add(node.id)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            out.add(node.name)
        elif isinstance(node, COMPREHENSIONS):
            todo.append(node.generators[0].iter)    # its first iterable is the scope's
        elif not isinstance(node, ast.Lambda):
            todo.extend(ast.iter_child_nodes(node))
    return out


def own_names(fn: ast.FunctionDef) -> tuple[set[str], set[str]]:
    """The names of a law that hold only a container it made, and those that hold only a
    constant. A container it made: a name that every binding in the law gives a new
    container (a list, dict or set display, a comprehension, or a call of one of
    CONSTRUCTORS that nothing in the law rebinds); a constant, a name every binding gives
    a literal. A name bound by a loop, a comprehension, a parameter or a function is
    neither."""
    bound = {node.id for node in ast.walk(fn) if isinstance(node, ast.Name)
             and not isinstance(node.ctx, ast.Load)}
    makers = CONSTRUCTORS - bound

    def new_container(value) -> bool:
        return isinstance(value, (ast.List, ast.Dict, ast.Set, ast.ListComp, ast.DictComp,
                                  ast.SetComp)) \
            or (isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
                and value.func.id in makers)

    made, constant, other, seen = set(), set(), set(), set()

    def bind(target, value) -> None:
        """A target of an assignment and its value, where it is known; a tuple or list
        target takes a display of as many values, one each."""
        seen.add(id(target))
        if isinstance(target, ast.Name):
            kind = made if new_container(value) else \
                constant if isinstance(value, ast.Constant) else other
            kind.add(target.id)
        elif isinstance(target, (ast.Tuple, ast.List)):
            elts = value.elts if isinstance(value, (ast.Tuple, ast.List)) \
                and len(value.elts) == len(target.elts) \
                and not any(isinstance(e, ast.Starred) for e in value.elts) else None
            for i, t in enumerate(target.elts):
                bind(t, elts[i] if elts else None)
        elif isinstance(target, ast.Starred):
            bind(target.value, None)

    for node in ast.walk(fn):
        if isinstance(node, ast.Assign):
            for target in node.targets:
                bind(target, node.value)
        elif isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
            seen.add(id(node.target))   # the same name, judged by self_contained
    for node in ast.walk(fn):
        if isinstance(node, ast.Name) and not isinstance(node.ctx, ast.Load) \
                and id(node) not in seen:
            other.add(node.id)  # a loop, a comprehension
        elif isinstance(node, ast.arg):
            other.add(node.arg)
        elif isinstance(node, ast.FunctionDef) and node is not fn:
            other.add(node.name)
    return made - constant - other, constant - made - other


def self_contained(fn: ast.FunctionDef, path: str) -> bool:
    """Does a law's code in the harness `path` keep to itself, so that it changes no other
    law's check when it runs? It is read against an allow-list, not run, and what the list
    does not name is refused, so a route the list never thought of is refused too. Its
    decorator is one law_decorator takes. It and every function it defines take plain
    positional parameters (no default, annotation, `/` or `*`), and only it has a
    decorator. Its body holds only the syntax of LAW_SYNTAX, with no `**` argument or
    display, no `async` comprehension, no dunder name, and a generator expression only as
    an argument, or unpacked as it is made. Each name is its own (a parameter, or bound in
    the law or a scope of it, as Python resolves it: a name bound only in a comprehension
    or an inner function is the global outside it), or a global in a role LAW_GLOBALS gives
    it (law_globals): called, read through a subscript, a module before an attribute, or a
    value. An attribute is never stored or deleted: on a module it is in LAW_MATH, on
    anything else in LAW_ATTRIBUTES, or in LAW_MUTATORS on a container of the law's own. So
    no frame, namespace, other module or lookup by string can be reached: none is on the
    list. And it changes only a container it made in its own body (own_names), under a name
    of the law's own scopes, and through that name itself: by a subscript stored, a method
    in LAW_MUTATORS, or an augmented assignment in IN_PLACE. So a second name for a shared
    container (`d = SEEDS[k]`, `for d in …`, an argument), an element of its own
    (`x[0] += [1]`), or a global of the same name as one of its own, changes nothing. An
    augmented assignment that a container of Python's own never makes in place (`t /= 2`),
    or one to a name every binding gives a constant (`j += 1`), changes nothing either."""
    if not law_decorator(fn.decorator_list[0], path):
        return False
    local = set()   # the names, as nodes, that the law's own scopes bind

    def resolve(node, chain: tuple) -> None:
        if isinstance(node, ast.FunctionDef):
            params = {a.arg for a in ast.walk(node.args) if isinstance(a, ast.arg)}
            inner = chain + (params | scope_binds(node.body),)
            for statement in node.body:
                resolve(statement, inner)
            return
        if isinstance(node, COMPREHENSIONS):
            first = node.generators[0]
            resolve(first.iter, chain)
            inner = chain + (scope_binds(g.target for g in node.generators),)
            parts = [node.key, node.value] if isinstance(node, ast.DictComp) else [node.elt]
            for g in node.generators:
                parts += [g.target, *g.ifs] + ([] if g is first else [g.iter])
            for part in parts:
                resolve(part, inner)
            return
        if isinstance(node, ast.Name) and any(node.id in names for names in chain):
            local.add(node)
        for child in ast.iter_child_nodes(node):
            resolve(child, chain)

    resolve(fn, ())
    own, constants = own_names(fn)
    parents = {child: node for node in ast.walk(fn) for child in ast.iter_child_nodes(node)}

    def mine(node) -> bool:
        return isinstance(node, ast.Name) and node in local and node.id in own

    def plain(f: ast.FunctionDef) -> bool:
        a = f.args
        return not (a.posonlyargs or a.vararg or a.kwonlyargs or a.kwarg or a.defaults
                    or a.kw_defaults or f.returns or getattr(f, "type_params", None)
                    or any(x.annotation or x.arg.startswith("__") for x in a.args)
                    or f.name.startswith("__"))

    def role(node: ast.Name) -> str:
        up = parents.get(node)
        if isinstance(up, ast.Call) and up.func is node:
            return "call"
        if isinstance(up, ast.Attribute):
            return "module"
        if isinstance(up, ast.Subscript) and up.value is node and isinstance(up.ctx, ast.Load):
            return "table"
        return "value"

    if not plain(fn):
        return False
    for node in (n for statement in fn.body for n in ast.walk(statement)):
        if not isinstance(node, LAW_SYNTAX):
            return False
        if isinstance(node, ast.FunctionDef) and (node.decorator_list or not plain(node)):
            return False
        if (isinstance(node, ast.keyword) and node.arg is None) \
                or (isinstance(node, ast.Dict) and None in node.keys) \
                or (isinstance(node, ast.comprehension) and node.is_async):
            return False
        if isinstance(node, ast.GeneratorExp):
            up = parents.get(node)
            if not ((isinstance(up, ast.Call) and node in up.args)
                    or (isinstance(up, ast.Assign) and up.value is node
                        and len(up.targets) == 1
                        and isinstance(up.targets[0], (ast.Tuple, ast.List)))):
                return False
        if isinstance(node, ast.Name) and (node.id.startswith("__") or (
                node not in local and node.id not in law_globals(path, role(node)))):
            return False
        if isinstance(node, ast.Attribute):
            on_module = isinstance(node.value, ast.Name) and node.value not in local
            if not isinstance(node.ctx, ast.Load) or not (
                    node.attr in LAW_MATH if on_module else
                    node.attr in LAW_ATTRIBUTES
                    or (node.attr in LAW_MUTATORS and mine(node.value))):
                return False
        if isinstance(node, ast.Subscript) and not isinstance(node.ctx, ast.Load) \
                and not mine(node.value):
            return False
        if isinstance(node, ast.AugAssign) and isinstance(node.op, IN_PLACE) \
                and not mine(node.target) and not (isinstance(node.target, ast.Name)
                                                   and node.target.id in constants):
            return False
    return True


def laws_move_with_axioms(repo, base, sha, path: str) -> bool:
    """Does each law the commit changes in `path` move with its axiom, whose entry in the
    lock the commit adds, removes or restates? In laws.toml, a line: the law's name, or
    whether it must fail in the hyperbolic plane. In one of MODEL_LAW_CODE, a law's code
    (law_of), which must keep to itself (self_contained), while the rest of the file, its
    comments and docstring aside, stays as it was, and the laws that stay keep their order.
    Anything else, a law changed while its axiom stands among them, is a check change."""
    old_lock, new_lock = locked_axioms(show(repo, base, LOCK)), locked_axioms(show(repo, sha, LOCK))
    old_laws = model_laws(show(repo, base, MODEL_LAWS))
    new_laws = model_laws(show(repo, sha, MODEL_LAWS))
    if None in (old_lock, new_lock, old_laws, new_laws):
        return False
    moved = {k for k in old_lock.keys() | new_lock.keys() if old_lock.get(k) != new_lock.get(k)}
    if path == MODEL_LAWS:
        return all(k in moved for k in old_laws.keys() | new_laws.keys()
                   if old_laws.get(k) != new_laws.get(k))
    old, new = law_code(show_bytes(repo, base, path)), law_code(show_bytes(repo, sha, path))
    if old is None or new is None or old[0] != new[0]:
        return False
    if [name for name in old[1] if name in new[1]] != \
            [name for name in new[1] if name in old[1]]:
        return False
    for name in old[1].keys() | new[1].keys():
        was, now = old[1].get(name), new[1].get(name)
        if was is not None and now is not None and ast.dump(was) == ast.dump(now):
            continue
        if now is not None and not self_contained(now, path):
            return False
        axioms = {k for laws in (old_laws, new_laws) for k, (law, _) in laws.items()
                  if law == name}
        if not axioms or not axioms <= moved:
            return False
    return True


def count_markers(repo, base):
    """origin/main's reader of count markers, generated_counts.markers, or None when its
    copy is missing or does not load. The harness is safe_push.py and heath.py alone, so
    the module is read from origin/main's tree, never the commit's or the checkout's. It
    is the reader render.py and check_fidelity.py use, and the commit's own pass reads
    with the same one, since a commit that changes it changes scripts/, which is never
    pinned."""
    key = os.path.realpath(repo), base
    if key in COUNT_READERS:
        return COUNT_READERS[key]
    source = show_bytes(repo, base, COUNT_READER)
    if source is None:
        COUNT_READERS[key] = None
        return None
    module = types.ModuleType("generated_counts")
    try:        # compiled as an import compiles it, without this file's __future__ import
        exec(compile(source, f"origin/main:{COUNT_READER}", "exec", dont_inherit=True),
             vars(module))
    except Exception:       # a copy that does not load reads no marker: nothing is pinned
        COUNT_READERS[key] = None
        return None
    COUNT_READERS[key] = getattr(module, "markers", None)
    return COUNT_READERS[key]


def counts_moved(repo, base, sha, path: str) -> bool:
    """Is the commit's change to `path`, Markdown of COUNTED_PROSE, confined to the values
    between its count markers, as origin/main's generated_counts reads them
    (count_markers)? (For the model's page, do those markers stand?) The file stays a
    regular file of the same mode, the same markers stand by name and in order, every byte
    outside their values is as it was, and a value moves. The model's page (MODEL_PAGE) is
    its account of the laws, pinned whole for its prose, so there only the markers must
    stand (#187). A marker added, removed, renamed or reordered, any other byte changed but
    in the model's page, a file added or deleted, or one either side cannot read, is not.
    The commit's own check_fidelity.py holds each value to the files it counts."""
    if not (path.endswith(".md") and under(path, COUNTED_PROSE)):
        return False
    raw = git(repo, "diff", "--raw", "-z", "--no-renames", base, sha, "--", f":(literal){path}")
    modes = raw.split("\0")[0].lstrip(":").split()[:2]
    if len(modes) != 2 or modes[0] != modes[1] or modes[0] not in ("100644", "100755"):
        return False
    old, new = show_bytes(repo, base, path), show_bytes(repo, sha, path)
    read = count_markers(repo, base)
    if old is None or new is None or old == new or read is None:
        return False
    try:
        texts = old.decode(), new.decode()
        found = [read(text, path) for text in texts]
    except (UnicodeDecodeError, ValueError):
        return False
    if path == MODEL_PAGE:
        return [m.name for m in found[0]] == [m.name for m in found[1]]

    def outside(text: str, markers) -> list[str]:
        cuts = [0, *(i for m in markers for i in (m.value_start, m.value_end)), len(text)]
        return [text[a:b] for a, b in zip(cuts[0::2], cuts[1::2])]
    return outside(texts[0], found[0]) == outside(texts[1], found[1])


def pinned(repo, base, sha, path: str) -> bool:
    """Is the commit's change to the check input `path` a value pinned to the edition? The
    lock, the model's hash of it, and its results, always; its page, while the same count
    markers stand in it (counts_moved); the certificate's expectations, while the change
    keeps every one origin/main has (kept_expectations); the model's law names, and a
    law's code in the two harnesses that check every law, while each law changed moves
    with its axiom (laws_move_with_axioms); and the Markdown of the check inputs that are
    not code, while nothing but the values between its count markers changes
    (counts_moved). A file under scripts/ never is."""
    if path == EXPECTATIONS:
        return kept_expectations(show(repo, base, path), show(repo, sha, path))
    if path == MODEL_LAWS or path in MODEL_LAW_CODE:
        return laws_move_with_axioms(repo, base, sha, path)
    if path == MODEL_PAGE:
        return counts_moved(repo, base, sha, path)
    return under(path, PINNED) or counts_moved(repo, base, sha, path)


# origin/main's path check and its cases, by the names of their entries in the registry
# (checks/, as check_sequence reads it; each name is its command's words): every path of
# the tree is what they judge, so a failure of either is a verdict whatever else the
# commit changes (keep_apart). Units holds them to the registry's names, so that an entry
# reworded there cannot drop the rule unseen.
PATH_CHECKS = ("python3 -I tests/test_check_paths.py",
               "python3 scripts/check_paths.py --self-test")


def base_pass_failures(rep: Report, stage: str) -> list[str]:
    """The checks noted at `stage` as failing with origin/main's copies, less the two that
    show only stale pages (FRESHNESS): the failures keep_apart judges."""
    return [name for s in rep.steps
            if s.stage == stage and s.outcome == "note" and s.name.endswith(BASE_PASS)
            and (name := s.name.removesuffix(BASE_PASS)) not in FRESHNESS]


def review_notes(rep: Report) -> list[str]:
    """The pre-flight's notes that origin/main's checks fail on the commit, which WORKFLOW
    sends to the security review: a failure keep_apart judges, at step 3 or 4, and the
    "pinned values" note it writes when it lets one pass."""
    names = [name + BASE_PASS for stage in ("3", "4")
             for name in base_pass_failures(rep, stage)]
    names += [s.name for s in rep.steps if s.stage in ("3", "4") and s.outcome == "note"
              and s.name == "pinned values"]
    return list(dict.fromkeys(names))


def keep_apart(repo, base, sha, rep: Report, stage: str) -> bool:
    """A check change is a pull request of its own, landed before the code it checks
    (docs/WORKFLOW.md, "Landing work: pull requests"). So when a check fails with
    origin/main's copies, the commit may change nothing the checks judge: a check
    weakened in the same pull request as the code it would catch is refused, not only
    noted. A failure of origin/main's path check (PATH_CHECKS) refuses the commit
    whatever else it changes, even when that is only protected paths and guides, which
    are not judged: every path is what it judges, so a looser check_paths.py cannot land
    with the path it would let in. This is a second line: step 3 has already judged every
    commit's tree by origin/main's standard (guard_paths), before any of the commit's code
    ran. Two failures are not a verdict, and do not count. Pages gone stale under
    origin/main's copies (FRESHNESS): a renderer's change shows in the pages it
    regenerates, and the commit's own pass still needs them current. And any failure on a
    commit whose only check inputs changed are pinned values (pinned): a re-proof that
    moves an expected count, or a new word in the lock and the count of the words that
    Certificate/FIELDS.md gives between its count markers, changes the value with the
    content, in no other order, and the commit's own pass still needs them to agree. An
    expectation dropped or loosened is no pinned value: check_fidelity.py checks only
    what each expectation says, so the commit's own pass could never catch it. Nor is a
    count marker added, removed, renamed or reordered, in that Markdown or in the model's
    page, nor any other byte of that Markdown changed (the page's prose moves with its
    laws): the commit's own pass checks the values alone, each against the marker that
    holds it. Check code changed with judged content is kept apart, pinned values or
    not; and so is a law of the model changed while its axiom stands, for the commit's own
    pass could not catch that either. True when it refuses."""
    failed = base_pass_failures(rep, stage)
    paths = [name for name in failed if name in PATH_CHECKS]
    if paths:       # #186, a looser path check: no judged file needed, no pinned value excuses it
        rep.add(stage, "check change kept apart", "FAIL",
                f"origin/main's path check fails on the commit ({', '.join(paths)}): every "
                "path is what it judges, so the commit is refused whatever else it changes. "
                "Land a change to scripts/check_paths.py first, in a pull request of its "
                "own, and the paths it lets in after it (docs/WORKFLOW.md, \"Landing work: "
                "pull requests\")")
        return True
    judged = judged_files(repo, base, sha) if failed else []
    if not judged:
        return False
    inputs = sorted(p for _, p in changed_files(repo, base, sha) if under(p, CHECK_INPUTS))
    if inputs and all(pinned(repo, base, sha, p) for p in inputs):
        if not any(s.stage == stage and s.name == "pinned values" for s in rep.steps):
            rep.add(stage, "pinned values", "note", f"origin/main's checks fail on the commit "
                    f"({', '.join(failed)}), and the only check inputs it changes are values "
                    f"pinned to the edition, the values between count markers, and laws of "
                    f"the model that move with their axioms "
                    f"({', '.join(inputs)}), which move with the content they pin: for the "
                    "security review, which reads each law's code")
        return False
    shown = ", ".join(judged[:8]) + (f" and {len(judged) - 8} more" if len(judged) > 8 else "")
    loosened = EXPECTATIONS in inputs and not pinned(repo, base, sha, EXPECTATIONS)
    laws = [p for p in inputs if (p == MODEL_LAWS or p in MODEL_LAW_CODE)
            and not pinned(repo, base, sha, p)]
    counted = [p for p in inputs if p.endswith(".md") and under(p, COUNTED_PROSE)
               and p != MODEL_PAGE and not pinned(repo, base, sha, p)]
    marked = MODEL_PAGE in inputs and not pinned(repo, base, sha, MODEL_PAGE)
    rep.add(stage, "check change kept apart", "FAIL",
            f"origin/main's checks fail on the commit ({', '.join(failed)}), and it changes "
            f"what they judge as well as the checks: {shown}"
            + (f"; and it drops or loosens an expectation of {EXPECTATIONS}, which is a "
               "check change" if loosened else "")
            + (f"; and it changes the model's laws in {', '.join(laws)} beyond the laws that "
               "move with their axioms (or a law's code uses what its allow-list does not "
               "name), which is a check change" if laws else "")
            + (f"; and it changes {', '.join(counted)} beyond the values between count "
               "markers, which is a check change" if counted else "")
            + (f"; and it adds, removes, renames or reorders a count marker of {MODEL_PAGE} "
               "(or adds or deletes the file, changes its mode, or leaves it unreadable), "
               "which is a check change" if marked else "")
            + ". Land the check change first, in a pull request of its own (the check code, "
            "the guides, the regenerated pages and the records' stamps), and the rest after "
            f"it; values pinned to the edition ({LOCK}, {MODEL_HASH}, the counts and values "
            f"of {EXPECTATIONS}, none of its expectations dropped or loosened, the values "
            f"between count markers in the Markdown of {', '.join(COUNTED_PROSE[:-1])} and "
            f"{COUNTED_PROSE[-1]}, nothing else of it changed, and the model's account, "
            f"{MODEL_PAGE}, its count markers standing, and {MODEL_RESULTS}) move with the "
            f"content they pin, and so does a law of the model, its line of {MODEL_LAWS} and "
            f"its code in {' and '.join(MODEL_LAW_CODE)}, with its axiom (docs/WORKFLOW.md, "
            "\"Landing work: pull requests\")")
    return True


class Guarded(NamedTuple):
    statements: list[str]       # changed with a brief or decision naming them
    protected: list[str]        # protected paths changed
    check_inputs: list[tuple[str, str]]   # check inputs changed: (status, path)


# --------------------------------------------------------------------------------------
# The risk class, by origin/main's scripts/risk.py


class Risk(NamedTuple):
    cls: str                    # R0 to R5
    why: str                    # how it was found, for the step line and the record
    seconds: float | None = None


CLASS_LINE = re.compile(r"(R[0-5]) (\S.*)")
PATH_LINE = re.compile(r"  (R[0-5]) (.+)")


def risk_class(repo, base: str, sha: str, labels: set[str] | None, *,
               diff_base: str | None = None) -> Risk:
    """The class of the change `git diff base...sha`, as origin/main's scripts/risk.py
    gives it (`risk.py --diff`, as CI's risk job runs it): its copy at `base`, read out of
    git and run from a temporary directory, never the commit's, so that a change cannot
    lower its own class by editing the classifier. With `diff_base`, the change classed is
    `git diff diff_base...sha` instead, the classifier still read at `base`: so the queue's
    judge classes an entry's block and its merge into the group by main's copy. A label
    can only raise the class: a pull request labelled release is R5, and so is one whose
    labels cannot be read. A base with no scripts/risk.py is R5, and so is any failure to
    compute the class (fail closed): Git failing, the script failing or printing no class,
    a class below that of a file it lists, a timeout; with `diff_base` or without."""
    t = time.time()

    def r5(why: str) -> Risk:
        return Risk("R5", why, time.time() - t)
    if labels is None:
        return r5("the pull request's labels could not be read, so it may be a release")
    if RELEASE_LABEL in {label.lower() for label in labels}:
        return r5(f"the pull request is labelled {RELEASE_LABEL}")
    listed = run(["git", "ls-tree", "-z", base, "--", RISK], repo, binary=True)
    if listed.returncode != 0:
        return r5(f"git could not read origin/main {base[:12]}: "
                  f"{printable_text(listed.stderr.decode(errors='replace').strip())}")
    if not listed.stdout:
        return r5(f"origin/main {base[:12]} has no {RISK} to class it")
    meta = listed.stdout.split(b"\t", 1)[0].split()
    if len(meta) != 3 or meta[0] not in (b"100644", b"100755") or meta[1] != b"blob":
        return r5(f"origin/main's {RISK} is not a regular file")
    source = run(["git", "cat-file", "blob", meta[2].decode()], repo, binary=True)
    if source.returncode != 0:
        return r5(f"git could not read origin/main's {RISK}")
    start = base if diff_base is None else diff_base
    with tempfile.TemporaryDirectory(prefix="stoicheia-risk-") as tmp:
        script = Path(tmp) / "risk.py"
        script.write_bytes(source.stdout)
        try:
            r = subprocess.run([PY, "-I", str(script), "--diff", start, sha], cwd=repo,
                               env=without_replacements(), capture_output=True, text=True,
                               errors="replace", timeout=RISK_TIMEOUT)
        except (OSError, subprocess.TimeoutExpired) as e:
            return r5(f"origin/main's {RISK} could not be run: {type(e).__name__}")
    if r.returncode != 0:
        said = (r.stderr.strip().splitlines() or [""])[-1]
        return r5(f"origin/main's {RISK} could not class it (exit {r.returncode}"
                  + (f": {printable_text(said)[:300]}" if said else "") + ")")
    lines = r.stdout.splitlines()
    m = CLASS_LINE.fullmatch(lines[0]) if lines else None
    if not m:
        return r5(f"origin/main's {RISK} printed no class")
    cls, name = m.groups()
    # The class is the highest of its files': a class below one of the files it lists is
    # no class.
    listed = [(p.group(1), p.group(2)) for line in lines[1:]
              if (p := PATH_LINE.fullmatch(line))]
    higher = max(((c, path) for c, path in listed if c > cls), default=None)
    if higher:
        return r5(f"origin/main's {RISK} gave {cls}, below the {higher[0]} it gave "
                  f"{printable_text(higher[1])[:200]}")
    top = [path for c, path in listed if c == cls]
    files = ("no file changed" if not top else top[0] if len(top) == 1
             else f"{top[0]} and {len(top) - 1} more at {cls}")
    return Risk(cls, f"{name}, by origin/main's {RISK} (blob {meta[2].decode()[:12]}): "
                     f"{printable_text(files)}", time.time() - t)


def beyond_low(repo, base, sha) -> list[str]:
    """The paths the change touches that no change of R0 to R2 may: the check inputs
    (CHECK_INPUTS), and the protected paths that are not content the checks judge (the
    workflows, the hooks and the launcher, the build files, .gitignore and
    .gitattributes). risk.py classes every one of them R3 or above; should origin/main's
    copy ever class such a change lower, the full checks run, as for R3 to R5. So
    keep_apart, which needs a check input changed, cannot arise on the short path."""
    return sorted(p for _, p in changed_files(repo, base, sha) if under(p, CHECK_INPUTS)
                  or (is_protected(p) and not under(p, PROTECTED_JUDGED)))


def guards(ctx, wt: Path, rep: Report, logs: Path) -> Guarded:
    repo, base, sha = ctx.repo, ctx.base, ctx.sha
    print(f"  in a fresh worktree of the commit, {wt}", flush=True)
    statements = guard_statements(repo, base, sha, wt, rep)
    guard_lock(repo, base, sha, rep)
    protected = guard_protected(repo, base, sha, rep)
    guard_heath(repo, base, sha, wt, rep)
    guard_directories(repo, base, sha, rep)
    guard_entries(repo, base, sha, rep)
    guard_registry(repo, sha, rep, base)
    inputs = [(s, p) for s, p in changed_files(repo, base, sha) if under(p, CHECK_INPUTS)]
    with contextlib.closing(passes(repo, base, sha, wt, inputs)) as each:
        for label, fail, excludes in each:
            guard_fidelity(wt, rep, logs, label, fail)
            guard_generated(wt, rep, logs, label, fail, excludes)
    keep_apart(repo, base, sha, rep, "3")
    guard_foundations(repo, base, sha, rep)
    failed = [s.name for s in rep.failed() if s.stage == "3"]
    if failed:
        raise Refusal(f"the invariant guards refused: {', '.join(failed)}")
    return Guarded(statements, protected, inputs)


# --------------------------------------------------------------------------------------
# Step 4: the full local checks, in disposable worktrees


@contextlib.contextmanager
def worktree(repo, sha, parent: Path, name: str):
    """A fresh detached worktree of the commit, removed afterwards, on a failure too."""
    path = parent / name
    # No hooksPath: the tests' checkout_marker needs post-checkout; hooks left over: #218.
    git(repo, *AS_COMMITTED, "worktree", "add", "--detach", "--quiet", str(path), sha)
    try:
        yield path
    finally:
        r = run(["git", "worktree", "remove", "--force", str(path)], repo)
        if r.returncode != 0:
            shutil.rmtree(path, ignore_errors=True)
            run(["git", "worktree", "prune"], repo)


def run_step(stage, name, cmd, cwd: Path, rep: Report, logs: Path, index: int,
             fail="FAIL", excludes=()) -> str:
    """One step of the full checks, timed and logged; its output, which the main-checks
    cache keeps for origin/main's pass."""
    t = time.time()
    log = logs / f"{index:02d}{slug_of(name)}.log"
    if cmd is None:     # the generated pages are current
        r = status_lines(cwd, list(excludes))
        out, ok = r.stdout + r.stderr, r.returncode == 0 and not r.stdout.strip()
    else:
        r = run(cmd, cwd, env=tool_env())
        out, ok = (r.stdout or "") + (r.stderr or ""), r.returncode == 0
    log.write_text(out)
    seconds = time.time() - t
    if ok:
        rep.add(stage, name, "ok", "", seconds)
        return out
    rep.add(stage, name, fail, f"full output in {log}\n{tail(out)}", seconds)
    if fail == "FAIL":
        raise Refusal(f"`{name}` failed on the commit")
    return out


def copy_build(src: Path, dst: Path) -> None:
    """Give the second worktree the first one's build of the same commit (a clone of the
    files on APFS); lake rebuilds whatever it finds out of date."""
    if not (src / ".lake").exists():
        return
    flags = ["-Rc"] if sys.platform == "darwin" else ["-R"]
    if run(["cp", *flags, str(src / ".lake"), str(dst / ".lake")], dst).returncode != 0:
        shutil.rmtree(dst / ".lake", ignore_errors=True)


class CheckList(NamedTuple):
    steps: list[tuple[str, list[str] | None]]   # (name, argv); None: `git status` is empty
    why: str                                     # where they came from, for the step line
    built_in: bool = False                       # CHECKS: the revision holds no registry


def check_sequence(repo, base: str, whose: str = "origin/main") -> CheckList:
    """The checks step 4 runs on a commit against `base`, origin/main: the `check` job's,
    as base's registry lists them, then the `model` job's (MODEL_JOB). The registry,
    checks/, and its reader, scripts/registry.py, are base's: the reader is read out of git
    and run from a temporary directory, and reads the registry out of git at base, both
    with git's replacement objects off; never the commit's registry or reader, nor the
    worktree's, so that a change cannot alter the checks its own pre-flight runs. With
    neither at base (the train that adds them), the built-in CHECKS (built_in). A Refusal
    when base holds either and the registry cannot be read: the other missing or not a
    regular file or folder, the reader failing, outlasting its time or printing anything
    but a list of checks of the `check` job, or no check at all. Never an empty list.

    The names are held here as well as by the reader, which a train may change: the
    `empty` entry, and only it, is named EMPTY_CHECK, and every other entry's name is its
    command's words joined by spaces, so that no command is ever named as a step whose
    failure FRESHNESS passes over. Step 3 reads the commit's own registry so too, `whose`
    naming it (guard_registry)."""
    def refuse(why: str):
        raise Refusal(f"{whose}'s registry of checks could not be read: {why}")

    listed = run(["git", "ls-tree", "-z", "--full-tree", base, "--", REGISTRY,
                  REGISTRY_READER], repo, binary=True)
    if listed.returncode != 0:
        refuse(f"git could not list {whose} {base[:12]}: "
               f"{printable_text(listed.stderr.decode(errors='replace').strip())}")
    found = {}
    for record in listed.stdout.split(b"\0"):
        if record:
            meta, _, path = record.partition(b"\t")
            found[os.fsdecode(path)] = meta.split()
    if not found:
        return CheckList(CHECKS + MODEL_JOB, f"the {len(CHECKS)} built into this harness, "
                         f"since {whose} {base[:12]} holds no registry yet ({REGISTRY}/ "
                         f"and {REGISTRY_READER}), then the model job's", True)
    reader, folder = found.get(REGISTRY_READER), found.get(REGISTRY)
    if (reader is None or len(reader) != 3 or reader[0] not in (b"100644", b"100755")
            or reader[1] != b"blob"):
        refuse(f"{whose} {base[:12]} holds {REGISTRY}/ but no regular file "
               f"{REGISTRY_READER} to read it")
    if folder is None or len(folder) != 3 or folder[1] != b"tree":
        refuse(f"{whose} {base[:12]} holds {REGISTRY_READER} but no folder {REGISTRY}/")
    source = run(["git", "cat-file", "blob", reader[2].decode()], repo, binary=True)
    if source.returncode != 0:
        refuse(f"git could not read {whose}'s {REGISTRY_READER}")
    with tempfile.TemporaryDirectory(prefix="stoicheia-registry-") as tmp:
        script = Path(tmp) / "registry.py"
        script.write_bytes(source.stdout)
        # Through run(), so that under the main-checks cache's sandbox it runs sandboxed,
        # as every command does (#392): read as bytes, decoded leniently, as before.
        try:
            r = run([PY, "-I", str(script), "--rev", base, "--json", str(repo)], repo,
                    env=without_replacements(), binary=True, timeout=REGISTRY_TIMEOUT)
        except (OSError, subprocess.TimeoutExpired) as e:
            refuse(f"its {REGISTRY_READER} could not be run: {type(e).__name__}")
    out = r.stdout.decode(errors="replace")
    err = r.stderr.decode(errors="replace")
    if r.returncode != 0:
        said = (err.strip().splitlines() or [""])[-1]
        refuse(f"its {REGISTRY_READER} exited {r.returncode}"
               + (f": {printable_text(said)[:300]}" if said else ""))
    try:
        entries = json.loads(out)
    except json.JSONDecodeError:
        entries = None
    if not isinstance(entries, list):
        refuse(f"its {REGISTRY_READER} printed no list of checks")
    steps: list[tuple[str, list[str] | None]] = []
    for item in entries:
        name = item.get("name") if isinstance(item, dict) else None
        command, empty = (item.get("command"), item.get("empty")) if name else (None, None)
        words = isinstance(command, list) and bool(command) and all(
            isinstance(w, str) and w for w in command)
        if (not isinstance(name, str) or not name or not name.isprintable()
                or not ((empty is True and command is None) or (empty is False and words))):
            refuse(f"its {REGISTRY_READER} printed an entry that is not a check: "
                   f"{printable_text(str(item))[:200]}")
        if item.get("job") != "check":
            refuse(f"its {REGISTRY_READER} gives {printable_text(name)} to the job "
                   f"{printable_text(str(item.get('job')))}, which the pre-flight does not run")
        if empty and name != EMPTY_CHECK:
            refuse(f"its {REGISTRY_READER} gives the `empty` check the name "
                   f"{printable_text(name)[:200]!r}, not {EMPTY_CHECK!r}")
        if not empty and name != " ".join(command):
            refuse(f"its {REGISTRY_READER} names a check {printable_text(name)[:200]!r}, "
                   "not its command's words joined by spaces")
        if not empty and name in FRESHNESS:
            refuse(f"its {REGISTRY_READER} gives a command the name {name!r}, which only "
                   "the `empty` check may bear: a failure of a step of that name is "
                   "passed over when a check change is kept apart (FRESHNESS)")
        steps.append((name, None if empty else
                       [PY if i == 0 and w == "python3" else w for i, w in enumerate(command)]))
    if not steps:
        refuse(f"its {REGISTRY_READER} gives no check")
    if len({name for name, _ in steps}) != len(steps):
        refuse(f"its {REGISTRY_READER} gives two checks of one name")
    return CheckList(steps + MODEL_JOB, f"the {len(steps)} of {whose}'s registry, "
                     f"{REGISTRY}/ (tree {folder[2].decode()[:12]}), as its {REGISTRY_READER} "
                     f"(blob {reader[2].decode()[:12]}) reads them, then the model job's")


def guard_registry(repo, sha, rep: Report, base: str | None = None) -> None:
    """The commit's registry of checks reads as the pre-flight of every later train will
    read it once the commit is origin/main's: by check_sequence at the commit, the
    commit's own scripts/registry.py taken out of git and run alone from a temporary
    directory, reading the commit's checks/ out of git. render.py and CI's run_checks.py
    load the reader from scripts/ and read the worktree, so a reader that imports a module
    beside it, or that fails only on a revision, passes them both, and once merged would
    refuse every train, its own repair among them. Every class runs this.
    Skipped only while the commit holds neither the registry nor its reader, when the lists
    built in stand in for it, as they did before the registry came."""
    t = time.time()
    try:
        own = check_sequence(repo, sha, "the commit")
    except Refusal as e:
        # Against origin/main (or, without it, the commit's parent): a commit that changes
        # neither the folder nor the reader holds origin/main's registry, and the fault is
        # main's; else the commit's own. Any doubt reads as the commit's.
        old = base or (f"{sha}^" if git_ok(repo, "rev-parse", "--verify", "-q", f"{sha}^")
                       else None)
        try:
            changed = changed_files(repo, old, sha, REGISTRY, REGISTRY_READER) if old \
                else [("?", REGISTRY)]
        except Exception:
            changed = [("?", REGISTRY)]
        whose = (f"{e}; so it would refuse the pre-flight of every train once it is "
                 f"origin/main's, as {REGISTRY_READER} reads it there, alone and out of git "
                 "(check_sequence)") if changed else (
                 f"{e}; the commit changes neither {REGISTRY}/ nor {REGISTRY_READER}, so the "
                 "registry it holds is origin/main's, which fails to read: a repair of the "
                 "registry on main comes first")
        rep.add("3", "registry of checks", "FAIL", whose, time.time() - t)
        return
    if own.built_in:
        rep.add("3", "registry of checks", "skip", f"the commit holds neither {REGISTRY}/ "
                f"nor {REGISTRY_READER}", time.time() - t)
    else:
        rep.add("3", "registry of checks", "ok", f"{len(own.steps) - len(MODEL_JOB)} checks, "
                f"as the commit's own {REGISTRY_READER} reads them alone and out of git, as "
                "a later pre-flight will", time.time() - t)


def check_list(ctx, rep: Report) -> list[tuple[str, list[str] | None]]:
    """check_sequence for the commit, as a step line: ok with how many and from where, or
    FAIL and a Refusal."""
    t = time.time()
    try:
        checks = check_sequence(ctx.repo, ctx.base)
    except Refusal as e:
        rep.add("4", "check list", "FAIL", str(e), time.time() - t)
        raise
    rep.add("4", "check list", "ok", f"{len(checks.steps)} checks: {checks.why}",
            time.time() - t)
    return checks.steps


def full_checks(ctx, wt: Path, parent: Path, inputs, rep: Report, logs: Path,
                sequence: list[tuple[str, list[str] | None]]) -> None:
    def kept_apart(label):
        if label == BASE_PASS and keep_apart(ctx.repo, ctx.base, ctx.sha, rep, "4"):
            raise Refusal("a check changed together with what it checks")

    # With --main-checks-cache, origin/main's pass is taken from the cache on a hit, and
    # kept for it on a miss; keep_apart then reads its steps as it reads them run.
    cache = main_checks(ctx, wt, inputs, rep, sequence) if CACHE is not None else None

    def checks(steps, where: Path, label, fail, excludes, first: int) -> None:
        if label == BASE_PASS and cache is not None and cache.hit:
            cache.replay(steps, first, rep, logs)
            return
        for i, (name, cmd) in enumerate(steps, 1):
            out = run_step("4", name + label, cmd, where, rep, logs, first + i, fail, excludes)
            if label == BASE_PASS and cache is not None:
                cache.collect(rep, out)
        if label == BASE_PASS and cache is not None:
            cache.save(rep)

    # A refusal inside origin/main's pass leaves passes() at its yield: closing it puts
    # the worktree back before the worktree is removed.
    with contextlib.closing(passes(ctx.repo, ctx.base, ctx.sha, wt, inputs)) as each:
        for label, fail, excludes in each:
            checks(sequence, wt, label, fail, excludes, 10)
            kept_apart(label)
    with worktree(ctx.repo, ctx.sha, parent, "negative") as neg:
        copy_build(wt, neg)
        with contextlib.closing(passes(ctx.repo, ctx.base, ctx.sha, neg, inputs)) as each:
            for label, fail, excludes in each:
                checks(NEGATIVE, neg, label, fail, excludes, 30)
                kept_apart(label)


# --------------------------------------------------------------------------------------
# Step 4's main-checks cache (--main-checks-cache): origin/main's pass, reused for the same
# trees. Its directory is beside the log (~/.cache/stoicheia/main-checks/), outside every
# worktree; each entry is <key>.json, written by the harness alone, while every command the
# run starts runs under a sandbox that may not write the directory (open_cache, run).


def canonical(value) -> bytes:
    """The JSON a key and a digest are taken of: its keys sorted, no spaces, ASCII."""
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
                      allow_nan=False).encode()


def sha256_of(value) -> str:
    return hashlib.sha256(canonical(value)).hexdigest()


def dir_problem(path: Path) -> str | None:
    """Why the cache's directory may not be used, or None: it is a directory, no symbolic
    link and reached through none (its real path is its path), owned by this user, of
    mode 0700 exactly, and on the device of the directory above it, so that nothing
    mounted over it stands in for it."""
    try:
        st = os.lstat(path)
        above = os.lstat(path.parent)
    except OSError as e:
        return f"{path} cannot be read ({e.strerror or e})"
    if stat.S_ISLNK(st.st_mode):
        return f"{path} is a symbolic link"
    if not stat.S_ISDIR(st.st_mode):
        return f"{path} is not a directory"
    if os.path.realpath(path) != str(path):
        return (f"{path} is reached through a symbolic link (its real path is "
                f"{os.path.realpath(path)})")
    if st.st_uid != os.getuid():
        return f"{path} is owned by another user"
    if stat.S_IMODE(st.st_mode) != 0o700:
        return f"{path} has mode {stat.S_IMODE(st.st_mode):04o}, not 0700 (chmod 700 it)"
    if st.st_dev != above.st_dev:
        return f"{path} is on another device than {path.parent}, as when one is mounted there"
    return None


def sandbox_profile(cache: Path) -> str | None:
    """The profile every command runs under while the cache is in use: anything but a
    write to the cache's directory or within it, or to a directory above it, since a
    rename of one would carry the cache out from under the rule, to be written and put
    back. None when the path holds what the profile's quoted strings could not."""
    path = str(cache)
    if '"' in path or "\\" in path or not path.isprintable():
        return None
    rules = [f'(subpath "{path}")'] + [f'(literal "{p}")' for p in map(str, cache.parents)
                                      if p != "/"]
    return f"(version 1) (allow default) (deny file-write* {' '.join(rules)})"


def sandbox_problem(profile: str, cache: Path) -> str | None:
    """Why the sandbox cannot be had, or None: sandbox-exec runs a command under the
    profile, stops a write to the cache, leaving no file, and stops a harmless write to
    the directory above it (`touch -c`, which makes nothing) with its own refusal,
    "Operation not permitted", so that a profile that has lost the rules above the cache
    is caught here, and a write that fails for another reason passes nothing. It runs
    before SANDBOX is set, so run() adds no sandbox of its own."""
    if sys.platform != "darwin":
        return "the sandbox is macOS's sandbox-exec, and this is not macOS"
    if not (os.path.isfile(SANDBOX_EXEC) and os.access(SANDBOX_EXEC, os.X_OK)):
        return f"{SANDBOX_EXEC} is not there"
    probe = cache / f".probe-{secrets.token_hex(8)}"
    try:
        r = run([SANDBOX_EXEC, "-p", profile, "/usr/bin/true"], cache)
        if r.returncode != 0:
            said = (r.stderr.strip().splitlines() or ["no message"])[-1]
            return ("sandbox-exec cannot run a command under the profile, as when it runs "
                    f"inside another sandbox ({said})")
        r = run([SANDBOX_EXEC, "-p", profile, "/bin/sh", "-c", 'echo x > "$1"', "sh",
                 str(probe)], cache)
        above = run([SANDBOX_EXEC, "-p", profile, "/usr/bin/touch", "-c", str(cache.parent)],
                    cache)
    except OSError as e:
        return f"sandbox-exec could not be run ({e.strerror or e})"
    left = os.path.lexists(probe)
    if left:
        with contextlib.suppress(OSError):
            os.unlink(probe)
    if r.returncode == 0 or left:
        return "sandbox-exec did not stop a write to the cache"
    if above.returncode == 0:
        return (f"sandbox-exec did not stop a write to {cache.parent}, the directory above "
                "the cache")
    # The sandbox's refusal, EPERM, and no other failure: one that fails for a reason of
    # its own proves nothing of the rule.
    if DENIED not in above.stderr:
        said = (above.stderr.strip().splitlines() or ["no message"])[-1]
        return (f"the trial's write to {cache.parent}, the directory above the cache, failed "
                f"otherwise than by the sandbox's refusal ({printable_text(said)[:200]})")
    return None


def open_cache(rep: Report, risk: Risk, train: bool = False) -> None:
    """--main-checks-cache, once the change's class is known and before any check runs:
    for R3 to R5, whose pre-flight runs step 4 in full, the cache's directory, beside the
    log (made here, mode 0700, when it is missing), and the sandbox that keeps every
    command this run starts from writing it (run). Without either, the run goes on as it
    would without the flag, and says why. For R0 to R2, which leave step 4 to CI, there is
    no pass to reuse: nothing is read, written or made, and no sandbox is set (should the
    check inputs overrule the class, short_path, origin/main's pass runs uncached). Nor
    for a train/* branch: its train check runs origin/main's check_train.py in this
    process after the guards have run the commit's code (train_check), and so after a
    sandboxed command could have written the harness's directory, from which it and what
    it imports are read; so a train runs uncached, with no sandbox, as without the flag."""
    global CACHE, SANDBOX
    if train:
        rep.add("1", "main-checks cache", "note", "not used this run: a train/* branch's train "
                "check runs origin/main's check_train.py in this process after the commit's "
                "code has run, so the run goes on as without --main-checks-cache")
        return
    if risk.cls in LOW_CLASSES:
        rep.add("1", "main-checks cache", "skip", f"not used this run: the class {risk.cls} "
                "leaves step 4 to CI, and the cache serves only step 4 run in full (R3 to R5)")
        return
    path = Path(os.path.abspath(log_path().parent / "main-checks"))
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        if not os.path.lexists(path):
            os.mkdir(path, 0o700)
            os.chmod(path, 0o700)       # whatever the umask took away
        why = dir_problem(path)
    except OSError as e:
        why = f"{path} could not be made ({e.strerror or e})"
    profile = None
    if why is None:
        profile = sandbox_profile(path)
        why = sandbox_problem(profile, path) if profile else (
            f"{path} holds a quotation mark, a backslash or an unprintable character, which "
            "the sandbox's profile cannot hold")
    if why:
        rep.add("1", "main-checks cache", "note", f"not used this run: {why}; origin/main's "
                "checks run in full, as without --main-checks-cache")
        return
    CACHE, SANDBOX = path, profile
    rep.add("1", "main-checks cache", "ok", f"{path}: from here on, every command this run "
            "starts runs under sandbox-exec, which may not write it")


def base_tree(repo, base, sha, changes: list[tuple[str, str]]) -> str:
    """The tree base_copies lays down in the worktree, made in a temporary index: the
    commit's, with origin/main's entry for each check input the commit changes, and those
    it adds taken out. Neither the worktree nor the repository's own index is touched."""
    with tempfile.TemporaryDirectory(prefix="stoicheia-index-") as tmp:
        # Besides GIT_NO_REPLACE_OBJECTS, the one repository variable the harness sets on
        # purpose, kept by run() (#357): every other but GIT_NO_REPLACE_OBJECTS is
        # dropped, a hook's GIT_INDEX_FILE among them.
        env = dict(own_env(), GIT_INDEX_FILE=str(Path(tmp) / "index"))

        def index(*args, input=None) -> str:
            r = run(["git", *args], repo, env=env, input=input, keep=("GIT_INDEX_FILE",))
            if r.returncode != 0:
                raise Refusal(f"`git {' '.join(args)}` failed: {r.stderr.strip()}")
            return r.stdout

        index("read-tree", sha)
        removed, restored = [], []
        for status, path in changes:
            entry = "" if status == "A" else \
                git(repo, "ls-tree", "-z", base, "--", path).split("\0")[0]
            if entry:
                restored.append(entry)      # "<mode> <type> <oid>\t<path>", as ls-tree gives it
            else:
                removed.append(path)
        if removed:
            index("update-index", "-z", "--force-remove", "--stdin",
                  input="".join(p + "\0" for p in removed))
        if restored:
            index("update-index", "-z", "--index-info",
                  input="".join(e + "\0" for e in restored))
        return index("write-tree").strip()


def toolchain(repo, sha, wt: Path) -> dict | None:
    """The Lean the checks run with: the tree's lean-toolchain, `lean --version` and
    `lake --version` as run in the worktree, and the real path of the lean that elan
    resolves, when elan is there; None when any of them cannot be read."""
    env = tool_env()
    found: dict = {"lean-toolchain": show(repo, sha, "lean-toolchain")}
    try:
        for tool in ("lean", "lake"):
            r = run([tool, "--version"], wt, env=env)
            if r.returncode != 0 or not r.stdout.strip():
                return None
            found[f"{tool} --version"] = r.stdout.strip()
        found["elan which lean"] = None
        elan = shutil.which("elan", path=env["PATH"])
        if elan:
            r = run([elan, "which", "lean"], wt, env=env)
            if r.returncode != 0 or not r.stdout.strip():
                return None
            found["elan which lean"] = os.path.realpath(r.stdout.strip())
    except OSError:
        return None
    return found


# The variables the key holds, with their values: each whose name begins so (the Python
# variables reach the steps run without -I, and the locale's reach the checks' reading
# and writing of text), ONLY by name, and LANG and LANGUAGE by name, so that no other
# variable that merely begins LANG is written into an entry.
KEYED_VARIABLES = ("STOICHEIA_", "LEAN", "LAKE", "PYTHON", "LC_")
KEYED_NAMES = frozenset({"LANG", "LANGUAGE", "ONLY"})
# The harness's own plumbing, which no check reads: which copy runs (STOICHEIA_HARNESS,
# set on a hand-over and not by the launcher), where the log is (STOICHEIA_PUSH_LOG, which
# places the cache itself), and the interpreter the launcher picks (STOICHEIA_PYTHON,
# whose real path is keyed as "executable"). Keyed, a run handed over from a worktree and
# a run of the launcher would never share an entry.
UNKEYED_VARIABLES = frozenset({"STOICHEIA_HARNESS", "STOICHEIA_PUSH_LOG",
                               "STOICHEIA_PYTHON"})
# The terminal's, which begin LC_ and are no locale: iTerm2 names itself and its version in
# them. Keyed, a dry run and a push from two terminals would never share an entry.
TERMINAL_VARIABLES = frozenset({"LC_TERMINAL", "LC_TERMINAL_VERSION"})


def environment(repo) -> dict:
    """What else the checks' outcomes could turn on: the Python, the platform, Git, the
    PATH the checks run with, and the variables KEYED_VARIABLES and KEYED_NAMES name,
    with their values, but the harness's own (UNKEYED_VARIABLES) and the terminal's
    (TERMINAL_VARIABLES). The platform is read from os.uname() and macOS's version file,
    never with platform.platform(), which starts `uname -p` and `file -b` from the PATH,
    outside run() and so outside the sandbox; mac_ver's plistlib is imported at the top
    (run)."""
    env = tool_env()
    try:
        git_version = run(["git", "--version"], repo, env=env)
    except OSError as e:
        raise Refusal(f"`git --version` failed: {e.strerror or e}") from e
    if git_version.returncode != 0:
        raise Refusal(f"`git --version` failed: {git_version.stderr.strip() or 'no message'}")
    return {
        "python": sys.version,
        "executable": os.path.realpath(sys.executable),
        "platform": [platform.system(), platform.release(), platform.machine(),
                     platform.mac_ver()[0]],
        "git --version": git_version.stdout.strip(),
        "PATH": env["PATH"],
        "variables": sorted([name, value] for name, value in os.environ.items()
                            if (name.startswith(KEYED_VARIABLES) or name in KEYED_NAMES)
                            and name not in UNKEYED_VARIABLES | TERMINAL_VARIABLES),
    }


def main_checks_fields(ctx, wt: Path, inputs, sequence: list[tuple[str, list[str] | None]]
                       ) -> tuple[dict | None, str]:
    """The fields of the key of origin/main's pass on this commit, computed by the harness
    and never read from the tree as code; or None, and why there is no key. Its checks are
    `sequence`, the checks step 4 runs (check_list), and its negative tests NEGATIVE."""
    if HARNESS_BLOB is None:
        return None, "the harness running is not origin/main's"
    lean = toolchain(ctx.repo, ctx.sha, wt)
    if lean is None:
        return None, ("the toolchain could not be read (`lean --version`, `lake --version` "
                      "or `elan which lean` failed)")
    try:
        fields = {
            "format": MAIN_CHECKS_FORMAT,
            "main": ctx.base,
            "base_tree": base_tree(ctx.repo, ctx.base, ctx.sha, inputs),
            # The checks compare the tree they run on with the commit's own (git status,
            # git ls-files), so two commits with one base tree may still differ there.
            "commit_tree": git(ctx.repo, "rev-parse", f"{ctx.sha}^{{tree}}").strip(),
            "harness_blob": HARNESS_BLOB,
            "toolchain": lean,
            "environment": environment(ctx.repo),
            "checks": [[name, cmd] for name, cmd in sequence],
            "negative": [[name, cmd] for name, cmd in NEGATIVE],
        }
    except Refusal as e:
        return None, f"the trees could not be read ({e})"
    return json.loads(canonical(fields)), ""


ENTRY_FIELDS = frozenset({"key", "written", "steps", "digest"})
STEP_FIELDS = frozenset({"name", "outcome", "detail", "seconds", "log"})


def base_pass_names(fields: dict) -> list[str]:
    """origin/main's pass of step 4, step by step, as the key `fields` names it: its checks,
    then its negative tests."""
    return [name + BASE_PASS for name, _ in [*fields["checks"], *fields["negative"]]]


STEP_SECONDS = 7 * 24 * 3600    # the longest a recorded step may have taken: a week
WRITTEN_TIME = re.compile(
    r"([0-9]{4})-([0-9]{2})-([0-9]{2}) ([0-9]{2}):([0-9]{2}) UTC")


def step_time(seconds) -> bool:
    """Is `seconds` a time a step could have taken: none recorded, or an int or a float
    from 0 to STEP_SECONDS? Compared, not passed to math.isfinite, which overflows on an
    integer of 400 digits; NaN and the infinities fail the comparison."""
    return seconds is None or (isinstance(seconds, (int, float))
                               and not isinstance(seconds, bool)
                               and 0 <= seconds <= STEP_SECONDS)


def written_time(value) -> bool:
    """Is `value` the cache's UTC minute format, with a valid date and time?"""
    match = WRITTEN_TIME.fullmatch(value) if isinstance(value, str) else None
    if match is None:
        return False
    try:
        datetime.datetime(*(int(part) for part in match.groups()),
                          tzinfo=datetime.timezone.utc)
    except (OverflowError, ValueError):
        return False
    return True


def writable_text(value) -> bool:
    """Is `value` a string this run can write to a log as UTF-8 and print? A lone
    surrogate, which JSON may carry, is neither."""
    if not isinstance(value, str):
        return False
    out = sys.stdout
    try:
        value.encode("utf-8")
        value.encode(getattr(out, "encoding", None) or "utf-8",
                     getattr(out, "errors", None) or "strict")
    except (UnicodeError, LookupError):
        return False
    return True


def entry_problem(entry, key: str, fields: dict) -> str | None:
    """Why an entry read for `key` may not stand in for origin/main's pass, or None. Its
    key fields must be this run's, exactly, and hash to its name; its digest must match the
    rest of it; its harness must be this one; and its steps must be origin/main's pass,
    each once, in order, each "ok" or "note", with a time a step could take and text this
    run can write and print. So no entry turns a note into an ok, and replay cannot
    fail on what it reads."""
    if not isinstance(entry, dict) or set(entry) != ENTRY_FIELDS:
        return "it is not an entry of this format"
    if entry["key"] != fields:
        return "its key fields are not this run's"
    if sha256_of(entry["key"]) != key:
        return "its key fields do not hash to its name"
    if entry["digest"] != sha256_of({k: v for k, v in entry.items() if k != "digest"}):
        return "its digest does not match its contents"
    if HARNESS_BLOB is None or entry["key"].get("harness_blob") != HARNESS_BLOB:
        return "it was written by another harness"
    if not written_time(entry["written"]):
        return "its written time is not of this format"
    steps = entry["steps"]
    if not isinstance(steps, list) or not all(
            isinstance(s, dict) and set(s) == STEP_FIELDS for s in steps):
        return "its steps are not of this format"
    if [s["name"] for s in steps] != base_pass_names(fields):
        return "its steps are not origin/main's pass, each step once and in order"
    for s in steps:
        if s["outcome"] not in ("ok", "note"):
            return (f"its step {s['name']} is not of this format (outcome "
                    f"{ascii(s['outcome'])[:40]})")
        if not step_time(s["seconds"]):
            return (f"its step {s['name']} is not of this format (its seconds are no time a "
                    "step could take)")
        if not (writable_text(s["detail"]) and writable_text(s["log"])):
            return (f"its step {s['name']} is not of this format (its detail or its log is "
                    "not text this run can write as UTF-8 and print)")
    return None


def read_entry(cache: Path, key: str, fields: dict) -> tuple[dict | None, str]:
    """The entry for `key`, when it may stand in for origin/main's pass; else None, and
    why: it is a regular file, no symbolic link, owned by this user, of mode 0600, no
    larger than ENTRY_BYTES (16 MiB), in a directory that may be used (dir_problem), and
    its contents pass entry_problem. A larger entry is refused unread, and no more than
    ENTRY_BYTES and a byte is ever read; any error in reading its contents, whatever they
    hold, refuses it, and the pass runs again: never a crash or a hang."""
    why = dir_problem(cache)
    if why:
        return None, why
    path = cache / f"{key}.json"
    try:
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except FileNotFoundError:
        return None, "no entry for this key"
    except OSError as e:
        if os.path.islink(path):
            return None, "the entry is a symbolic link"
        return None, f"the entry cannot be opened ({e.strerror or e})"
    large = f"it is larger than {ENTRY_BYTES} bytes (16 MiB)"
    entry = None
    try:
        with os.fdopen(fd, "rb") as f:
            st = os.fstat(f.fileno())
            if not stat.S_ISREG(st.st_mode):
                return None, "the entry is not a regular file"
            if st.st_uid != os.getuid():
                return None, "the entry is owned by another user"
            if stat.S_IMODE(st.st_mode) != 0o600:
                return None, f"the entry has mode {stat.S_IMODE(st.st_mode):04o}, not 0600"
            # Its size by fstat, and the read itself bounded, should it grow meanwhile.
            data = f.read(ENTRY_BYTES + 1) if st.st_size <= ENTRY_BYTES else None
        if data is None or len(data) > ENTRY_BYTES:
            why = large
        else:
            entry = json.loads(data)
            why = entry_problem(entry, key, fields)
    except Exception as e:      # whatever the file holds: a doubt, never a crash
        why = f"it is not an entry of this format ({type(e).__name__})"
    return (None, f"the entry was refused: {why}") if why else (entry, "")


def write_entry(cache: Path, key: str, entry: dict) -> str | None:
    """`entry`, written as <key>.json through a temporary file in the directory, synced
    and renamed into place, mode 0600; or why it could not be."""
    tmp = None
    try:
        fd, tmp = tempfile.mkstemp(prefix=f".{key[:12]}-", suffix=".tmp", dir=cache)
        with os.fdopen(fd, "wb") as f:
            f.write(canonical(entry))
            f.flush()
            os.fsync(f.fileno())
        os.chmod(tmp, 0o600)
        os.replace(tmp, cache / f"{key}.json")
        tmp = None
    except (OSError, ValueError) as e:
        return f"{getattr(e, 'strerror', None) or e}"
    finally:
        if tmp is not None:
            with contextlib.suppress(OSError):
                os.unlink(tmp)
    with contextlib.suppress(OSError):
        fd = os.open(cache, os.O_RDONLY)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)
    return None


class MainChecks:
    """origin/main's pass of step 4 for one key. On a hit it holds the entry, whose steps
    stand in for the pass (replay); on a miss it records the pass as it runs (collect),
    and writes it as an entry once both its loops are done in this run (save)."""

    def __init__(self, key: str, fields: dict, entry: dict | None):
        self.key, self.fields, self.entry = key, fields, entry
        self.hit = entry is not None
        self.steps: list[dict] = []     # on a miss, the steps recorded as they ran
        self.spoiled = ""               # why they may not be written
        self.done = False               # written, or given up
        self.next = 0                   # on a hit, the recorded steps replayed so far

    def replay(self, steps, first: int, rep: Report, logs: Path) -> None:
        """The recorded steps standing for `steps`, reported with their outcomes as
        recorded, notes as notes, and their logs written among this run's, each note
        pointing to the copy this run writes rather than to the log of the run that
        wrote the entry; none is run."""
        recorded = self.entry["steps"][self.next:self.next + len(steps)]
        self.next += len(steps)
        for i, step in enumerate(recorded, 1):
            log = logs / f"{first + i:02d}{slug_of(step['name'])}.log"
            log.write_text(step["log"], encoding="utf-8")
            then = f"{step['seconds']:.1f} s" if step["seconds"] is not None else "untimed"
            said, newline, rest = step["detail"].partition("\n")
            if said.startswith("full output in "):     # as run_step words it
                said = f"full output in {log}"
            detail = said + newline + rest
            rep.add("4", step["name"], step["outcome"],
                    f"reused from the cache, entry {self.key[:12]}, written "
                    f"{self.entry['written']}: " + (detail or f"it passed then ({then})"))

    def collect(self, rep: Report, out) -> None:
        """The step origin/main's pass has just run, recorded for the entry."""
        names = base_pass_names(self.fields)
        s = rep.steps[-1] if rep.steps else None
        if self.spoiled or s is None or len(self.steps) >= len(names) \
                or s.name != names[len(self.steps)] or s.outcome not in ("ok", "note") \
                or not isinstance(out, str):
            self.spoiled = self.spoiled or "a step of origin/main's pass was not recorded as it ran"
            return
        self.steps.append({"name": s.name, "outcome": s.outcome, "detail": s.detail,
                           "seconds": s.seconds, "log": out})

    def save(self, rep: Report) -> None:
        """The entry, written once both loops of origin/main's pass have run in this run,
        under the sandbox, by the harness its key names; a note if it cannot be."""
        if self.hit or self.done:
            return
        if not self.spoiled and len(self.steps) < len(base_pass_names(self.fields)):
            return      # the negative tests' loop is still to run
        self.done = True
        why = self.spoiled or self.unwritable()
        if not why:
            entry = {"key": self.fields, "steps": self.steps,
                     "written": datetime.datetime.now(datetime.timezone.utc)
                     .strftime("%Y-%m-%d %H:%M UTC")}
            entry["digest"] = sha256_of(entry)
            why = write_entry(CACHE, self.key, entry)
        if why:
            rep.add("4", "main-checks cache", "note", f"entry {self.key[:12]} not written: {why}")

    def unwritable(self) -> str:
        """Why this run may not write the entry, or "": the sandbox was on throughout, the
        harness is the one the key names and its file is unchanged, and the directory may
        still be used."""
        if SANDBOX is None or CACHE is None:
            return "the sandbox was not on"
        if HARNESS_BLOB is None or HARNESS_BLOB != self.fields["harness_blob"]:
            return "the harness is not the one its key names"
        try:
            here = blob_id(Path(__file__).read_bytes())
        except OSError:
            here = None
        if here != HARNESS_BLOB:
            return "the harness's file changed while it ran"
        return dir_problem(CACHE) or ""


def main_checks(ctx, wt: Path, inputs, rep: Report,
                sequence: list[tuple[str, list[str] | None]]) -> MainChecks | None:
    """The cache's answer for origin/main's pass on this commit, reported in one line, for
    the pull request's record: a hit; a miss, and why; or why the cache does not serve."""
    global CACHE_HIT
    if not inputs:
        rep.add("4", "main-checks cache", "skip", "the commit changes no check input: there "
                "is no pass with origin/main's copies to reuse")
        return None
    fields, why = main_checks_fields(ctx, wt, inputs, sequence)
    if fields is None:
        rep.add("4", "main-checks cache", "note", f"not used for this commit: {why}; "
                "origin/main's checks run in full")
        return None
    key = sha256_of(fields)
    entry, why = read_entry(CACHE, key, fields)
    if entry is not None:
        CACHE_HIT = True
        rep.add("4", "main-checks cache", "note", f"hit: origin/main's checks of these trees "
                f"reused from entry {key[:12]}, written {entry['written']} by this harness; "
                "the commit's own checks run in full")
        return MainChecks(key, fields, entry)
    rep.add("4", "main-checks cache", "note", f"miss ({why}): origin/main's checks run, and "
            f"once both their loops have run they are kept as entry {key[:12]}, for the next "
            "run on the same trees")
    return MainChecks(key, fields, None)


class Preflight(NamedTuple):
    statements: list[str]
    protected: list[str]
    short: bool = False         # step 4 left to CI for the change's class


class HarnessSnapshot(NamedTuple):
    safe_push: bytes
    heath: bytes
    train: bytes | None


def short_path(ctx, risk: Risk, g: Guarded, rep: Report) -> bool:
    """Whether step 4 is left to CI: for a change of R0 to R2 by origin/main's risk.py,
    which changes no check input nor any protected path but judged content (beyond_low).
    No check input changes, so keep_apart cannot arise. Should the classifier and those
    lists ever disagree, the full checks run, as for R3 to R5, and it is noted."""
    if risk.cls not in LOW_CLASSES:
        return False
    beyond = sorted(set(beyond_low(ctx.repo, ctx.base, ctx.sha)) | {p for _, p in g.check_inputs})
    if beyond:
        shown = ", ".join(beyond[:8]) + (f" and {len(beyond) - 8} more" if len(beyond) > 8
                                         else "")
        rep.add("4", "class and check inputs", "note", f"origin/main's {RISK} classes the "
                f"change {risk.cls}, but it changes {printable_text(shown)}, which no change "
                "of R0 to R2 may: the full local checks run, as for R3 to R5")
        return False
    return True


def check_commit(ctx, rep: Report, logs: Path, test_mode: bool, risk: Risk,
                 checked: dict | None = None, train_body: str | None = None,
                 trusted_harness: HarnessSnapshot | None = None,
                 revalidate: Callable[[], None] | None = None) -> Preflight:
    """Steps 2 to 4 on the commit: the secret scan, the guards and the full checks.
    The class `risk` (risk_class) is reported at the head of step 4: for R0 to R2 the full
    checks are skipped (short_path), CI running the rest of section 8's sequence before the
    merge and the negative tests running on main after it and on the cadence; for R3 to R5
    they run. `checked`, a record of this commit against this origin/main by origin/main's
    harness, stands in for step 4 alone (--merge; checks_record); steps 2 and 3,
    including the train check when given, always run."""
    secret_scan(ctx.repo, ctx.base, ctx.sha, rep, allow_rev=ctx.base)
    rep.heading("3. Invariant guards against origin/main")
    # Before the commit is checked out (#186): on a case-insensitive disk a twin is written
    # over what it shadows, and a module in a twin folder (Scripts/json.py) would run in the
    # checks; checking out a hostile tree is where git's own flaws have been; and no code of
    # the commit has run yet to keep a path from origin/main's standard. So a refusal here
    # comes before any worktree is made.
    if not guard_paths(ctx.repo, ctx.base, ctx.sha, rep):
        failed = [s.name for s in rep.failed() if s.stage == "3"]
        raise Refusal(f"the invariant guards refused: {', '.join(failed)}")
    with tempfile.TemporaryDirectory(prefix="stoicheia-push-") as tmp:
        parent = Path(tmp)
        with worktree(ctx.repo, ctx.sha, parent, "check") as wt:
            g = guards(ctx, wt, rep, logs)
            if revalidate is not None:
                revalidate()
            if train_body is not None:
                train_check(ctx, train_body, rep, trusted_harness)
            rep.heading("4. The full local checks (docs/WORKFLOW.md, section 8)")
            rep.add("4", "class", "ok", f"{risk.cls}, {risk.why}", risk.seconds)
            short = short_path(ctx, risk, g, rep)
            if checked is not None and not checked.get("short"):
                short = False
                rep.add("4", "full local checks", "skip", f"run on {ctx.sha[:12]} against "
                        f"origin/main {ctx.base[:12]} by {checked.get('harness')}, "
                        f"{checked.get('time')}")
            elif short:
                rep.add("4", "full local checks", "skip", f"class {risk.cls}: left to CI, "
                        "whose check and model jobs run the builds, Facts.lean, the kernel "
                        "self-test and the rest of section 8 on the pull request before "
                        "the merge, and --merge waits for them green; the negative tests "
                        "run on main after the merge and on the cadence")
            else:
                # origin/main's registry, read under the internal test flag too, so that
                # the tests see which checks the full path would run.
                checks = check_list(ctx, rep)
                if test_mode:
                    rep.add("4", "full local checks", "skip", "internal test flag, local origin")
                else:
                    full_checks(ctx, wt, parent, g.check_inputs, rep, logs, checks)
            if revalidate is not None:
                revalidate()
    return Preflight(g.statements, g.protected, short)


# --------------------------------------------------------------------------------------
# Step 1: preconditions, and the harness


class Context(NamedTuple):
    repo: Path
    sha: str
    base: str
    commits: int
    origin: str
    github: str | None       # "owner/repo" when origin is on GitHub
    tags: dict[str, str]     # origin's tags before the push
    branch: str | None = None
    gh: tuple = ("gh",)
    remote_branch: str | None = None    # the branch on origin before the push
    queue: bool = False
    harness_sha: str | None = None     # origin/main's tip, before queue_base changes base
    trusted_harness: HarnessSnapshot | None = None
    pinned_origin: str | None = None


def is_local(url: str) -> bool:
    if url.startswith("file://"):
        return True
    if re.match(r"^[A-Za-z][A-Za-z0-9+.-]*://", url) or re.match(r"^[^/]+@[^/:]+:", url):
        return False
    return Path(url).exists()


def github_slug(url: str) -> str | None:
    m = re.search(r"github\.com[:/]([^/]+)/([^/]+?)(?:\.git)?/?$", url)
    return f"{m.group(1)}/{m.group(2)}" if m else None


def remote_refs(repo, *args, remote: str = "origin") -> dict[str, str]:
    command = ("ls-remote", "origin", *args) if remote == "origin" else \
        ("ls-remote", "--", remote, *args)
    out = git(repo, *command)
    refs = {}
    for line in out.splitlines():
        sha, _, ref = line.partition("\t")
        refs[ref] = sha
    return refs


HOOK, LAUNCHER = "scripts/hooks/pre-push", "scripts/hooks/safe-push"


def installed_paths(repo) -> dict[str, Path]:
    """Where install_hooks.sh puts the pre-push hook and the launcher, outside the
    tracked tree, shared by every worktree of the clone."""
    out = git(repo, "rev-parse", "--git-path", "hooks", check=False).strip()
    hooks = Path(out) if os.path.isabs(out) else Path(repo) / out
    common = git(repo, "rev-parse", "--path-format=absolute", "--git-common-dir",
                 check=False).strip()
    return {HOOK: hooks / "pre-push", LAUNCHER: Path(common) / "stoicheia" / "safe-push"}


def check_installed(repo, base: str, rep: Report) -> None:
    """A note when the hook or the launcher is missing, or differs from origin/main's
    copy: code the pre-flight ran (a commit's checks, Lean at elaboration) could have
    rewritten either, and the marker alone would not show it."""
    for source, path in installed_paths(repo).items():
        name = "pre-push hook" if source == HOOK else "launcher (git safe-push)"
        try:
            data = path.read_bytes()
        except OSError:
            data = None
        theirs = show_bytes(repo, base, source)
        if data is None:
            rep.add("1", name, "note", "not installed here (sh scripts/install_hooks.sh)")
        elif theirs is not None and data != theirs:
            rep.add("1", name, "note", f"the installed copy differs from origin/main's "
                    f"{source}: install it again, from a checkout of origin/main "
                    "(sh scripts/install_hooks.sh --force)")


def harness_train(repo: Path, base: str) -> bytes | None:
    """origin/main's train module, distinguishing absent from unreadable."""
    entry = git(repo, "ls-tree", base, "--", "scripts/check_train.py").strip()
    if not entry:
        return None
    if not re.fullmatch(r"100(?:644|755) blob [0-9a-f]{40,64}\tscripts/check_train\.py",
                        entry):
        raise Refusal("origin/main's scripts/check_train.py is not a regular file")
    return git(repo, "cat-file", "blob", f"{base}:scripts/check_train.py", binary=True)


def harness_copy(theirs: bytes, theirs_heath: bytes,
                 theirs_train: bytes | None = None) -> Path:
    """origin/main's harness modules, written to a directory named by their
    blobs, beside the log (~/.cache/stoicheia/harness/): it needs no
    cleaning up, since the same harness always lands in the same place, and each file is
    written afresh, through a rename, so that nothing left there earlier is run."""
    train_id = blob_id(theirs_train) if theirs_train is not None else "no-train"
    path = log_path().parent / "harness" / \
        f"{blob_id(theirs)}-{blob_id(theirs_heath)}-{train_id}"
    path.mkdir(parents=True, exist_ok=True)
    for name, data in (("safe_push.py", theirs), ("heath.py", theirs_heath),
                       ("check_train.py", theirs_train)):
        if data is None:
            (path / name).unlink(missing_ok=True)
            continue
        fd, tmp = tempfile.mkstemp(prefix=f".{name}.", dir=path)
        with os.fdopen(fd, "wb") as f:
            f.write(data)
        os.replace(tmp, path / name)
    return path


def harness(repo, base: str, rep: Report, hand_over: bool = True) -> None:
    """origin/main's safe_push.py, heath.py and optional check_train.py judge the commit.
    When this copy differs from them, origin/main's replaces this process (os.execve),
    with the same arguments:
    its signals, its summary and its exit status are the run's own, so an interruption
    after its push is still "pushed; CI not followed". A copy of origin/main's that
    predates the marker is not run: this copy runs, once, while the harness that runs
    from origin/main lands. STOICHEIA_HARNESS, which the hand-over sets, is believed only
    when this file's bytes are origin/main's. Without `hand_over` (the merge of --land,
    whose arguments are the push's), a copy that differs is refused, never replaced, in a
    run handed over too."""
    global HARNESS, HARNESS_BLOB
    here = Path(__file__).resolve().parent
    own, own_heath = (here / "safe_push.py").read_bytes(), (here / "heath.py").read_bytes()
    theirs = show_bytes(repo, base, "scripts/safe_push.py")
    theirs_heath = show_bytes(repo, base, "scripts/heath.py")
    theirs_train = harness_train(repo, base)
    own_train = (here / "check_train.py").read_bytes() if (here / "check_train.py").exists() \
        else None
    # Older launchers carry only the first two modules. train_check copies main's train
    # module afresh before importing it, so an absent local copy needs no hand-over.
    same = (theirs, theirs_heath) == (own, own_heath) and \
        (own_train is None or own_train == theirs_train)
    if not hand_over and not same:
        # Run again with the push's arguments, origin/main's harness would push again. The
        # merge has refused a moved main already, so the copy on disk was rewritten since
        # the run started, or origin/main's predates running from origin/main; a handed-over
        # run is refused here too, before STOICHEIA_HARNESS is read.
        raise Refusal("this copy of safe_push.py, heath.py or check_train.py on disk no "
                      "longer matches origin/main's: it was rewritten since the run "
                      "started, or origin/main's predates running from origin/main; the "
                      "merge of --land runs no other copy, so nothing is merged: run "
                      "--merge")
    if os.environ.get("STOICHEIA_HARNESS"):
        if not same:
            raise Refusal("STOICHEIA_HARNESS says this is origin/main's harness, but this "
                          "copy of safe_push.py, heath.py or check_train.py is not "
                          f"origin/main's (blob {blob_id(own)[:12]}): origin/main moved "
                          "since the hand-over, or the variable was set by hand. Run "
                          "safe_push again, with the variable unset.")
        HARNESS = f"origin/main's `scripts/safe_push.py` (blob `{blob_id(own)[:12]}`)"
        HARNESS_BLOB = blob_id(own)
        rep.add("1", "harness", "ok", f"origin/main's scripts/safe_push.py (blob "
                f"{blob_id(own)[:12]}), run in place of a copy that differs from it")
        return
    if theirs is None or theirs_heath is None or b"HARNESS_PROTOCOL" not in theirs:
        HARNESS = (f"this copy of `scripts/safe_push.py` (blob `{blob_id(own)[:12]}`), since "
                   "origin/main's predates running from origin/main")
        rep.add("1", "harness", "note", "origin/main's scripts/safe_push.py does not yet run "
                "from origin/main: this copy runs, while the change that makes it do so lands")
        return
    if same:
        HARNESS = f"origin/main's `scripts/safe_push.py` (blob `{blob_id(own)[:12]}`)"
        HARNESS_BLOB = blob_id(own)
        rep.add("1", "harness", "ok", f"origin/main's scripts/safe_push.py "
                f"(blob {blob_id(own)[:12]})")
        return
    print("  this copy of safe_push.py, heath.py or check_train.py differs from "
          "origin/main's: running origin/main's in its place", flush=True)
    path = harness_copy(theirs, theirs_heath, theirs_train) / "safe_push.py"
    # GIT_NO_REPLACE_OBJECTS=1, and no GIT_REPLACE_REF_BASE, for its git commands and its
    # checks: so an older harness, whose run() sets neither, has them too (#256). No other
    # variable that ties git to one repository goes with them (#357).
    env = without_replacements(dict(os.environ, STOICHEIA_HARNESS="origin/main"))
    sys.stdout.flush()
    sys.stderr.flush()
    os.execve(PY, [PY, str(path), *ARGV], env)


def harness_snapshot(repo: Path, base: str) -> HarnessSnapshot:
    safe_source = show_bytes(repo, base, "scripts/safe_push.py")
    heath_source = show_bytes(repo, base, "scripts/heath.py")
    if safe_source is None or heath_source is None:
        raise Refusal("origin/main's safe_push.py or heath.py could not be read")
    return HarnessSnapshot(safe_source, heath_source, harness_train(repo, base))


def land_state_unchanged(repo: Path, origin: str, harness_snapshot: HarnessSnapshot) -> None:
    current_origin = git(repo, "remote", "get-url", "origin", check=False).strip()
    if current_origin != origin:
        raise Refusal(f"origin's URL changed during the run, from {origin} to "
                      f"{current_origin}; nothing is merged: set it back, then --merge")
    here = Path(__file__).resolve().parent
    current = HarnessSnapshot(
        (here / "safe_push.py").read_bytes(),
        (here / "heath.py").read_bytes(),
        (here / "check_train.py").read_bytes() if (here / "check_train.py").exists()
        else None)
    same = (current.safe_push, current.heath) == \
        (harness_snapshot.safe_push, harness_snapshot.heath) and \
        (current.train is None or current.train == harness_snapshot.train)
    if not same:
        raise Refusal("this copy of safe_push.py, heath.py or check_train.py on disk no "
                      "longer matches origin/main's: it was rewritten since the run "
                      "started, or origin/main's predates running from origin/main; the "
                      "merge of --land runs no other copy, so nothing is merged: run "
                      "--merge")


def body_input(args) -> str | None:
    """--body-file's text, read once, as UTF-8, before the checks: the train check, the
    dry run's body and the pull request's body are all that same text."""
    if not args.body_file:
        return None
    try:
        return Path(args.body_file).read_text(encoding="utf-8")
    except (OSError, UnicodeError) as e:
        raise Refusal(f"could not read --body-file: {e}") from e


def train_input(ctx: Context, body: str | None) -> str | None:
    """A train needs an explicit body, including on a dry run or an update."""
    if not (ctx.branch or "").startswith("train/"):
        return None
    if body is None:
        raise Refusal("a train/* branch requires --body-file")
    return body


def train_check(ctx: Context, body: str, rep: Report,
                trusted_harness: HarnessSnapshot | None = None) -> None:
    """Run origin/main's train checker on the commit and the body. While origin/main has
    none, every train is refused: no commit's own copy ever runs in its place. In queue
    mode the base compared against is the newest commit of main's chain that the head
    contains (queue_base), the judge's base too, perhaps older than main's tip, whose
    checker (ctx.harness_sha's) is the one that runs."""
    rep.heading("3. train")
    started = time.time()
    try:
        if SANDBOX is not None:
            # open_cache sets none for a train: never run check_train in this process once
            # the commit's code may have written the harness's directory under the sandbox.
            raise Refusal("the train check cannot run once the main-checks cache's sandbox "
                          "is set")
        source = trusted_harness.train if trusted_harness is not None else \
            harness_train(ctx.repo, ctx.harness_sha or ctx.base)
        if source is None:
            raise Refusal("origin/main has no scripts/check_train.py, so no train can be "
                          "checked: land the train checker first, then the train")
        here = Path(__file__).resolve().parent
        safe_source = trusted_harness.safe_push if trusted_harness is not None else \
            (here / "safe_push.py").read_bytes()
        heath_source = trusted_harness.heath if trusted_harness is not None else \
            (here / "heath.py").read_bytes()
        path = harness_copy(safe_source, heath_source, source)
        spec = importlib.util.spec_from_file_location("check_train", path / "check_train.py")
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        problems = module.check_train(ctx.repo, ctx.base, ctx.sha, body)
        if not isinstance(problems, list) or any(not isinstance(p, str) or not p.strip()
                                                 for p in problems):
            raise Refusal("check_train returned an unreadable problem list")
        if problems:
            raise Refusal("\n".join(problems))
    except (Exception, SystemExit) as e:
        rep.add("3", "train", "FAIL", str(e), time.time() - started)
        raise Refusal(f"the train check refused: {e}") from e
    rep.add("3", "train", "ok", "origin/main's check_train passed", time.time() - started)


def block_current(ctx: Context, m, record: dict) -> bool:
    """Is the body's pre-flight summary a true account of this head? It must name this
    head and, for a train, show the train step passing. Its base and harness are held to
    the queue's judge's rule (check_queue.preflight), read on this run's main: the base
    is the newest commit of main's first-parent chain that the head contains, which is
    what the pre-flight records (origin/main's tip, which the head held), and the
    harness that base or a later commit of the same chain. So a summary the judge would
    refuse is never current here, and one it would accept is current; in queue mode its
    base is the one this merge checks against (queue_base), even when the head's merge
    base with main lies off main's chain (a member merged before its train). Without the
    queue the base and the harness are both main's tip, as the head holds it. That the
    full checks ran again here, and passed, leaves a summary of the same head and base
    true."""
    if not m:
        return False
    sha, base, harness = m.group(1), m.group(2), m.group(3) or m.group(2)
    if sha != ctx.sha:
        return False
    # A branch renamed train/ after its pre-flight has a summary with no train step.
    if (ctx.branch or "").startswith("train/") and not TRAIN_ROW.search(m.group(0)):
        return False
    main = record.get("harness_sha") or ctx.harness_sha or ctx.base
    chain = git(ctx.repo, "rev-list", "--first-parent", main).split()
    held = set(git(ctx.repo, "rev-list", ctx.sha).split())
    newest = next((tip for tip in chain if tip in held), None)
    if base != newest or harness not in chain or chain.index(harness) > chain.index(base):
        return False
    return ctx.queue or (base, harness) == (ctx.base, main)


def merge_train_input(ctx: Context, view: dict) -> str | None:
    """Read a train's current pull request body; an unreadable body cannot skip its check."""
    if not (ctx.branch or "").startswith("train/"):
        return None
    body = view.get("body")
    if not isinstance(body, str):
        raise Refusal("could not read the train's current pull request body")
    return body


def gh_command(test_mode: bool) -> tuple:
    """gh, or, under the internal test flag, the stand-in the tests name; never the real
    gh under that flag."""
    if not test_mode:
        return ("gh",)
    stand_in = os.environ.get("STOICHEIA_TEST_GH")
    if not stand_in:
        raise Refusal("the internal test flag needs STOICHEIA_TEST_GH, a stand-in for gh")
    return (stand_in,)


def gh_ready(gh: tuple, repo, test_mode: bool) -> None:
    if not test_mode and shutil.which("gh") is None:
        raise Refusal("gh is not installed: the pull request needs it")
    r = run([*gh, "auth", "status", "--hostname", "github.com"], repo)
    if r.returncode != 0:
        raise Refusal("gh is not logged in to github.com (`gh auth login`)")


def fetch_base(repo, origin: str, test_mode: bool, rep: Report,
               remote: str = "origin") -> str:
    if test_mode and not is_local(origin):
        raise Refusal("the internal test flag works only against a local origin")
    t = time.time()
    command = ["git", "fetch", "origin"] if remote == "origin" else \
        ["git", "fetch", "--", remote, "+refs/heads/*:refs/remotes/origin/*"]
    r = run(command, repo)
    if r.returncode != 0:
        raise Refusal(f"`git fetch origin` failed: {r.stderr.strip()}")
    rep.add("1", "fetch", "ok", f"git fetch origin ({origin})", time.time() - t)
    base = rev_parse(repo, "refs/remotes/origin/main^{commit}")
    if base is None:
        raise Refusal("origin has no main branch")
    return base


def check_branch_name(repo, branch: str) -> None:
    name = branch.removeprefix("refs/heads/")
    if name.lower() in ("main", "head") or branch.startswith("refs/") and \
            not branch.startswith("refs/heads/"):
        raise Refusal(f"refusing --branch {branch}: main changes only by a pull request's "
                      "merge commit; name a branch of its own")
    if name.startswith("refs/") or name.startswith("-") or \
            not git_ok(repo, "check-ref-format", "--branch", name):
        raise Refusal(f"refusing --branch {branch}: not a branch name git accepts")


def preconditions(repo: Path, commit: str, branch: str | None, dry_run: bool,
                  test_mode: bool, rep: Report, title: str | None = None) -> Context:
    rep.heading("1. Preconditions")
    if branch:
        check_branch_name(repo, branch)
        branch = branch.removeprefix("refs/heads/")
    r = run(["git", "rev-parse", "--verify", "--quiet", f"{commit}^{{commit}}"], repo)
    if r.returncode != 0:
        raise Refusal(f"{commit!r} is not a commit in {repo}")
    sha = r.stdout.strip()
    subject = git(repo, "log", "-1", "--format=%s", sha).strip()
    rep.add("1", "commit", "ok", f"{sha[:12]} \"{subject}\" (read from git, not from the "
            "working tree)")
    origin = git(repo, "remote", "get-url", "origin", check=False).strip()
    if not origin:
        raise Refusal("this repository has no remote called origin")
    base = fetch_base(repo, origin, test_mode, rep)
    harness(repo, base, rep)
    if branch or title:
        check_public_names(branch, title)
        rep.add("1", "public names", "ok", "nothing the scan refuses in "
                + " or ".join(n for n, v in (("the branch name", branch), ("the title", title))
                              if v))
    if base == sha:
        rep.add("1", "fast-forward", "ok", f"origin/main is already {sha[:12]}")
        raise NothingToPush(sha)
    if not git_ok(repo, "merge-base", "--is-ancestor", base, sha):
        rep.add("1", "fast-forward", "FAIL", f"origin/main {base[:12]} is not an ancestor of "
                f"{sha[:12]}")
        raise Refusal(f"not a fast-forward: origin/main ({base[:12]}) is not an ancestor of "
                      f"{sha[:12]}. Merge origin/main into the branch first (a merge commit), "
                      "so that the merge holds exactly the tree checked; nothing is forced.")
    commits = int(git(repo, "rev-list", "--count", f"{base}..{sha}").strip())
    rep.add("1", "fast-forward", "ok", f"origin/main {base[:12]} is an ancestor: "
            f"{plural(commits, 'commit')} to propose")
    remote_branch = None
    if branch:
        remote_branch = remote_refs(repo, f"refs/heads/{branch}").get(f"refs/heads/{branch}")
        if remote_branch is None:
            rep.add("1", "branch", "ok", f"{branch}: new on origin")
        elif remote_branch == sha:
            rep.add("1", "branch", "ok", f"{branch}: already at {sha[:12]} on origin")
        elif rev_parse(repo, f"{remote_branch}^{{commit}}") is None or \
                not git_ok(repo, "merge-base", "--is-ancestor", remote_branch, sha):
            rep.add("1", "branch", "FAIL", f"origin's {branch} ({remote_branch[:12]}) is not "
                    f"an ancestor of {sha[:12]}")
            raise Refusal(f"origin's {branch} has commits {sha[:12]} lacks: merge them in (a "
                          "merge commit; review records stamp the branch's commits), or use "
                          "another branch name. Nothing is forced.")
        else:
            rep.add("1", "branch", "ok", f"{branch}: a fast-forward from {remote_branch[:12]}")
    rep.add("1", "tags and releases", "ok", "none is made: tags, releases and their notes "
            "stay manual, with the owner's OK")
    slug = "test/stoicheia" if test_mode else github_slug(origin)
    if not test_mode and shutil.which("lake", path=tool_env()["PATH"]) is None:
        raise Refusal("lake is not on the PATH, nor in ~/.elan/bin: the full checks need it")
    tags: dict[str, str] = {}
    gh: tuple = ("gh",)
    if branch and not dry_run:
        if not slug:
            raise Refusal(f"origin ({origin}) is not on GitHub: no pull request can be opened")
        gh = gh_command(test_mode)
        gh_ready(gh, repo, test_mode)
        tags = remote_refs(repo, "--tags")
    check_installed(repo, base, rep)
    return Context(repo, sha, base, commits, origin, slug, tags, branch, gh, remote_branch,
                   harness_sha=base)


# --------------------------------------------------------------------------------------
# Step 5: the push of the branch, the pull request, and its CI


def push_branch(ctx: Context, rep: Report) -> bool:
    """The push of the branch, after a last look at origin. True when it pushed; False
    when origin's branch was already the commit. Nothing after `git push` returns 0 is
    done here, so that the caller counts the branch as pushed from that moment on."""
    rep.heading("5. Push")
    now = remote_refs(ctx.repo, "refs/heads/main").get("refs/heads/main")
    if now != ctx.base:
        raise Refusal(f"origin/main moved from {ctx.base[:12]} to {str(now)[:12]} during the "
                      "checks: run safe_push again, against the new main")
    ref = f"refs/heads/{ctx.branch}"
    remote = remote_refs(ctx.repo, ref).get(ref)
    if remote == ctx.sha:
        rep.add("5", "git push", "ok", f"origin's {ctx.branch} is already {ctx.sha[:12]}")
        return False
    if remote != ctx.remote_branch:
        raise Refusal(f"origin's {ctx.branch} moved during the checks: run safe_push again")
    t = time.time()
    r = run(["git", "push", "--no-follow-tags", "--porcelain", "origin", f"{ctx.sha}:{ref}"],
            ctx.repo)
    if r.returncode != 0:
        rep.add("5", "git push", "FAIL", (r.stdout + r.stderr).strip(), time.time() - t)
        raise Refusal("git push failed; nothing was forced")
    rep.add("5", "git push", "ok", f"origin's {ctx.branch} "
            f"{(ctx.remote_branch or 'new')[:12]} -> {ctx.sha[:12]}, never forced",
            time.time() - t)
    return True


def verify_push(ctx: Context, rep: Report) -> None:
    """After the push: origin's branch is the commit, and origin's tags are as they were."""
    ref = f"refs/heads/{ctx.branch}"
    after = remote_refs(ctx.repo, ref).get(ref)
    if after != ctx.sha:
        rep.add("5", "branch on origin", "FAIL", f"origin's {ctx.branch} is {after}, not "
                f"{ctx.sha}")
        raise Refusal(f"the push did not leave origin's {ctx.branch} at the commit")
    tags = remote_refs(ctx.repo, "--tags")
    if tags != ctx.tags:
        new = sorted(set(tags) - set(ctx.tags))
        rep.add("5", "tags", "FAIL", f"origin's tags changed during the push: {new}")
    else:
        rep.add("5", "tags", "ok", "origin's tags unchanged")


def gh_run(ctx: Context, *args) -> subprocess.CompletedProcess:
    return run([*ctx.gh, *args, "-R", ctx.github], ctx.repo)


def gh_json(ctx: Context, *args):
    r = gh_run(ctx, *args)
    if r.returncode != 0 and not r.stdout.strip():
        raise Refusal(f"`gh {' '.join(args)}` failed: {(r.stderr or r.stdout).strip()}")
    try:
        return json.loads(r.stdout or "null")
    except json.JSONDecodeError:
        raise Refusal(f"`gh {' '.join(args)}` did not print JSON: {r.stdout.strip()[:200]}")


def ensure_labels(ctx: Context, labels) -> None:
    present = {item.get("name") for item in
               gh_json(ctx, "label", "list", "--json", "name", "--limit", "500") or []}
    for name in sorted(set(labels) - present):
        r = gh_run(ctx, "label", "create", name, "--description", LABELS.get(name, ""),
                   "--color", "b60205" if name == SECURITY_LABEL else "c5def5")
        if r.returncode != 0:
            raise Refusal(f"could not create the label {name}: {r.stderr.strip()}")


# The parts safe_push writes in the body stand between markers on lines of their own
# (describe, preflight_block), and the template's places for them are lines of their own:
# a marker counts only there, so one quoted in the coordinator's words (in a code span,
# say) is not one, and a part never runs over another begin marker of its name. A line may
# end in "\r": GitHub keeps a body edited in its page with CRLF line ends.
OWN_PART = re.compile(r"(?ms)^<!-- safe_push:(\w+) begin\b[^\n]*?-->[ \t\r]*$"
                      r"(?:(?!<!-- safe_push:\1 begin).)*?"
                      r"^<!-- safe_push:\1 end -->[ \t\r]*$")
# The pre-flight's summary, one of those parts, is replaced there.
BLOCK = re.compile(r"(?ms)^<!-- safe_push:preflight begin"
                   r"(?: sha=(\w+) base=(\w+)(?: harness=(\w+))?)? -->"
                   r"[ \t\r]*$(?:(?!<!-- safe_push:preflight begin).)*?"
                   r"^<!-- safe_push:preflight end -->[ \t\r]*$")
# The train step's row in that summary, as preflight_block writes it when it passed.
TRAIN_ROW = re.compile(r"(?m)^\| 3\. train \| ok \| [0-9.]* \|[ \t\r]*$")
PLACEHOLDER = re.compile(r"(?m)^<!-- safe_push: (\w+) -->[ \t\r]*$")
STAMP_FIELD = re.compile(r'(?m)^(fingerprint|commit|lean|text)\s*=\s*"([^"]*)"')


def sanitized(text: str) -> str:
    """A line for the public body: the home directory written as ~."""
    return text.replace(str(Path.home()), "~")


def preflight_block(sha: str, base: str, record: dict) -> str:
    if record.get("short"):
        skipped = (f"; the full local checks left to CI, for the class "
                   f"{record.get('class')}")
    else:
        skipped = "; the full checks skipped (the internal test flag)" \
            if not record.get("full") else ""
    harness_sha = record.get("harness_sha", base)
    lines = [f"<!-- safe_push:preflight begin sha={sha} base={base} harness={harness_sha} -->",
             f"Pre-flight of `{sha[:12]}` against origin/main `{base[:12]}`, "
             f"{record.get('time', '')}, by {record.get('harness', 'safe_push.py')}"
             + skipped + ".", "", "Verdict: PASS."]
    if record.get("class"):
        lines += ["", f"Risk class {record['class']}: {sanitized(record.get('class_why', ''))}."]
    lines += ["",
              "| Step | Outcome | Seconds |",
              "|---|---|---|"]
    for stage, name, outcome, seconds in record.get("steps", []):
        took = f"{seconds:.1f}" if seconds is not None else ""
        lines.append(f"| {stage}. {name} | {outcome} | {took} |")
    notes = record.get("notes", [])
    if notes:
        lines += ["", "Noted by the pre-flight:"]
        lines += [f"- {sanitized(name)}: {sanitized(first)}" for name, first in notes]
    if record.get("protected"):
        lines += ["", f"Protected paths changed: {', '.join(f'`{p}`' for p in record['protected'])}"
                  f"; label `{SECURITY_LABEL}`; /security-review required."]
    lines.append("<!-- safe_push:preflight end -->")
    return "\n".join(lines)


def put_block(body: str, block: str) -> str:
    """The body with the pre-flight's summary in place: between its markers, at the
    template's placeholder, or appended."""
    if BLOCK.search(body):
        return BLOCK.sub(lambda m: block, body, count=1)
    place = next((m for m in PLACEHOLDER.finditer(body) if m.group(1) == "preflight"), None)
    if place:
        return body[:place.start()] + block + body[place.end():]
    return body.rstrip() + "\n\n## Checks run on the exact commit\n\n" + block + "\n"


def generated_parts(repo, base, sha, path: str) -> tuple[bool, bool]:
    """Does the change touch what render.py writes in `path`, and does it touch the rest,
    written by hand? Only the files of GENERATED_REGIONS have a rest (README.md,
    docs/PROGRAM.md and docs/WORKFLOW.md): render.py writes them only between their
    markers, and every other generated file whole."""
    pattern = GENERATED_REGIONS.get(path)
    if pattern is None:
        return True, False
    old, new = show(repo, base, path) or "", show(repo, sha, path) or ""
    return ([m.group(0) for m in pattern.finditer(old)]
            != [m.group(0) for m in pattern.finditer(new)],
            pattern.sub("", old) != pattern.sub("", new))


def generated_changed(repo, base, sha, path: str) -> bool:
    return generated_parts(repo, base, sha, path)[0]


def describe(ctx: Context, pre: Preflight) -> dict[str, str]:
    """The parts of the body the pre-flight knows: commits, statements, records,
    generated files, protected paths."""
    repo, base, sha = ctx.repo, ctx.base, ctx.sha
    log = git(repo, "log", "--reverse", "--format=- `%h` %s", f"{base}..{sha}").strip()
    records = []
    for status, path in changed_files(repo, base, sha, "review"):
        if not re.fullmatch(r"review/[IVX]+/\d+\.toml", path):
            continue
        old = dict(STAMP_FIELD.findall(show(repo, base, path) or ""))
        new = dict(STAMP_FIELD.findall(show(repo, sha, path) or ""))
        lost = sorted(old.keys() - new.keys())
        if status == "D":
            records.append(f"- `{path}`: deleted")
        elif lost:
            records.append(f"- `{path}`: {'a stamp' if len(lost) == 1 else 'stamps'} taken "
                           f"away ({', '.join(f'`{key}`' for key in lost)})")
        elif old != new and new.get("commit") and new["commit"] == old.get("commit"):
            records.append(f"- `{path}`: its stamps written, its commit kept at "
                           f"`{new['commit'][:12]}`" if stamp_only(repo, base, sha, path)
                           else f"- `{path}`: touched, not re-stamped")
        elif old != new and new.get("commit"):
            records.append(f"- `{path}`: re-stamped at `{new['commit'][:12]}`")
        else:
            records.append(f"- `{path}`: touched, not re-stamped")
    generated = [p for _, p in changed_files(repo, base, sha) if under(p, GENERATED)
                 and generated_changed(repo, base, sha, p)]
    gen_dirs = sorted({p.split("/")[0] + "/" if p.startswith("book/") else p for p in generated})
    parts = {
        "commits": f"Commits (`{base[:12]}..{sha[:12]}`):\n\n{log}",
        "statements": "\n".join(f"- {s}" for s in pre.statements) or "None.",
        "records": "\n".join(records) or "None.",
        "generated": ("Changed: " + ", ".join(f"`{p}`" for p in gen_dirs)) if gen_dirs
                     else "None.",
        "protected": (", ".join(f"`{p}`" for p in pre.protected)
                      + f": the label `{SECURITY_LABEL}`, and /security-review before merge."
                      if pre.protected else "None."),
    }
    # Each between markers of its own, so that a later pre-flight finds it and writes it
    # afresh (refreshed, below).
    return {name: f"<!-- safe_push:{name} begin -->\n{text}\n<!-- safe_push:{name} end -->"
            for name, text in parts.items()}


def refreshed(body: str, parts: dict[str, str]) -> str:
    """The body with each part safe_push wrote, between its markers, written afresh from
    `parts` (the pre-flight's summary aside, which put_block places); the coordinator's
    words, outside the markers, are left as they are."""
    return OWN_PART.sub(lambda m: m.group(0) if m.group(1) == "preflight"
                        else parts.get(m.group(1), m.group(0)), body)


def fallback_template() -> str:
    return ("## What and why\n\n<!-- safe_push: commits -->\n\n"
            "## Checks run on the exact commit\n\n<!-- safe_push: preflight -->\n")


def fill_body(ctx: Context, pre: Preflight, record: dict, text: str) -> str:
    """A body with the template's `safe_push` placeholders filled, and the pre-flight's
    summary in place."""
    parts = describe(ctx, pre)
    body = PLACEHOLDER.sub(lambda m: parts.get(m.group(1), m.group(0))
                           if m.group(1) != "preflight" else m.group(0), text)
    return put_block(body, preflight_block(ctx.sha, ctx.base, record))


def generated_body(ctx: Context, pre: Preflight, record: dict) -> str:
    """The body from origin/main's template (the commit's, while origin/main has none)."""
    template = show(ctx.repo, ctx.base, TEMPLATE) or show(ctx.repo, ctx.sha, TEMPLATE) \
        or fallback_template()
    return fill_body(ctx, pre, record, template)


def check_body(body: str) -> None:
    """The body is public: it is scanned before it is posted."""
    found = scan_block("the pull request's body", list(enumerate(body.splitlines(), 1)))
    if found:
        raise Refusal("the pull request's body holds what the secret scan refuses: "
                      + "; ".join(f.shown() for f in found))


def check_public_names(branch: str | None, title: str | None) -> None:
    """The branch name is pushed as a public ref, and the title is posted: each is
    scanned, with no allow-list, before anything is pushed."""
    found = []
    if title:
        found += scan_text("the title", None, title)
    if branch:
        found += scan_text("the branch name", None, branch)
    if found:
        raise Refusal("a public name holds what the secret scan refuses: "
                      + "; ".join(f.shown() for f in found))


class PR(NamedTuple):
    number: int
    url: str
    created: bool


class PRPlan(NamedTuple):
    """The pull request as it will be: the open one of ours to update, if any, and its
    body, labels and title, all known and checked before the push."""
    existing: dict | None
    body: str
    labels: set
    title: str


def own_prs(ctx: Context, prs: list[dict]) -> list[dict]:
    """The pull requests whose head is a branch of origin itself. `gh pr list --head`
    matches on the branch's name alone, so it finds a fork's pull request of the same
    name too; and on a public repository anyone can open one in advance. GitHub's
    isCrossRepository tells them apart: it is false only when the head is a branch of the
    base repository itself, which only those who may push to it can make. The head's
    owner is not compared with the owner in origin's URL: after a rename or a transfer,
    which GitHub redirects, the URL names the old owner, and our own pull request would be
    missed, the branch pushed, and `gh pr create` refused."""
    return [p for p in prs if p.get("isCrossRepository") is False
            and p.get("headRefName", ctx.branch) == ctx.branch]


def find_own_pr(ctx: Context) -> dict | None:
    """Our open pull request for the branch, if any (never a fork's of the same name)."""
    listed = gh_json(ctx, "pr", "list", "--head", ctx.branch, "--base", "main", "--state",
                     "open", "--json", "number,url,isDraft,labels,isCrossRepository,"
                     "headRefName") or []
    mine = own_prs(ctx, listed)
    return mine[0] if mine else None


def kind_problem(labels) -> str | None:
    """What is wrong with a pull request's labels, or None: it needs one for its kind."""
    if set(labels) & set(KIND_LABELS):
        return None
    return (f"no label for its kind, one of {', '.join(KIND_LABELS)}: --label <kind> "
            "(docs/WORKFLOW.md, \"Landing work: pull requests\")")


def pr_labels(value) -> set[str]:
    """Read gh's label objects strictly."""
    if not isinstance(value, list) or any(
            not isinstance(label, dict) or not isinstance(label.get("name"), str)
            or not label["name"].strip() for label in value):
        raise ValueError("the pull request's labels are unreadable")
    return {label["name"].lower() for label in value}


def check_kind_label(ctx: Context, args, rep: Report) -> set[str]:
    """The label for the pull request's kind, given or on the open one, settled before
    the checks, so that a forgotten --label costs no Lean run. A dry run does not ask
    GitHub, and notes a missing one. Returns the labels the pull request will carry, as
    far as they are known before the checks: those given, and the open one's, which a dry
    run does not ask for; `release` among them makes the class R5 (risk_class)."""
    given = {label.lower() for label in args.label}
    if args.dry_run:
        if kind_problem(args.label):
            rep.add("1", "kind label", "note", f"none given ({kind_problem([])}); enough if "
                    "the open pull request has one")
        return given
    existing = find_own_pr(ctx)
    try:
        theirs = pr_labels([] if existing is None else existing.get("labels"))
    except ValueError as e:
        raise Refusal(str(e)) from None
    if kind_problem(args.label):
        problem = kind_problem(theirs)
        if problem:
            rep.add("1", "kind label", "FAIL", f"the pull request has {problem}")
            raise Refusal(f"the pull request has {problem}")
        rep.add("1", "kind label", "ok", f"on #{existing['number']}")
    return given | theirs


def plan_pr(ctx: Context, pre: Preflight, record: dict, args,
            body_text: str | None) -> PRPlan:
    """Everything the pull request will carry, settled before the push: our open pull
    request for the branch (never a fork's of the same name), and the body, scanned. A
    new pull request's body, or --body-file's text (body_input, read once before the
    checks), is known in full; an open one's is fetched."""
    labels = set(args.label) | ({SECURITY_LABEL} if pre.protected else set())
    existing = find_own_pr(ctx)
    try:
        pr_labels([] if existing is None else existing.get("labels"))
    except ValueError as e:
        raise Refusal(str(e)) from None
    if body_text is not None:
        body = fill_body(ctx, pre, record, body_text)
    elif existing:
        view = gh_json(ctx, "pr", "view", str(existing["number"]), "--json", "body")
        body = put_block(refreshed(view.get("body") or "", describe(ctx, pre)),
                         preflight_block(ctx.sha, ctx.base, record))
    else:
        body = generated_body(ctx, pre, record)
    check_body(body)
    title = args.title or git(ctx.repo, "log", "-1", "--format=%s", ctx.sha).strip()
    return PRPlan(existing, body, labels, title)


def open_pr(ctx: Context, plan: PRPlan, args, rep: Report, logs: Path) -> PR:
    rep.heading("6. Pull request")
    t = time.time()
    labels, existing = plan.labels, plan.existing
    ensure_labels(ctx, labels)
    body_path = logs / "pr-body.md"
    body_path.write_text(plan.body)
    if existing:
        pr = PR(int(existing["number"]), existing.get("url", ""), False)
        edit = ["pr", "edit", str(pr.number), "--body-file", str(body_path)]
        if args.title:
            edit += ["--title", args.title]
        for label in sorted(labels):
            edit += ["--add-label", label]
        r = gh_run(ctx, *edit)
        if r.returncode != 0:
            raise Refusal(f"`gh pr edit` failed: {r.stderr.strip()}")
        if args.ready and existing.get("isDraft"):
            r = gh_run(ctx, "pr", "ready", str(pr.number))
            if r.returncode != 0:
                raise Refusal(f"`gh pr ready` failed: {r.stderr.strip()}")
    else:
        create = ["pr", "create", "--base", "main", "--head", ctx.branch, "--title",
                  plan.title, "--body-file", str(body_path)]
        if not args.ready:
            create.append("--draft")
        for label in sorted(labels):
            create += ["--label", label]
        r = gh_run(ctx, *create)
        if r.returncode != 0:
            raise Refusal(f"`gh pr create` failed: {r.stderr.strip()}")
        url = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else ""
        m = re.search(r"/pull/(\d+)", url)
        if not m:
            raise Refusal(f"`gh pr create` printed no pull request URL: {r.stdout.strip()}")
        pr = PR(int(m.group(1)), url, True)
    # GitHub may take a moment to see the branch's new head.
    deadline = time.time() + HEAD_TIMEOUT
    while True:
        view = gh_json(ctx, "pr", "view", str(pr.number), "--json",
                       "headRefOid,baseRefName,isCrossRepository,url")
        if view.get("headRefOid") == ctx.sha or time.time() > deadline:
            break
        time.sleep(3)
    if view.get("headRefOid") != ctx.sha or view.get("baseRefName") != "main" \
            or view.get("isCrossRepository"):
        rep.add("6", "pull request", "FAIL", f"#{pr.number}'s head is "
                f"{str(view.get('headRefOid'))[:12]}, base {view.get('baseRefName')}, not "
                f"{ctx.sha[:12]} onto main", time.time() - t)
        raise Refusal(f"pull request #{pr.number} does not propose the commit checked")
    pr = pr._replace(url=view.get("url") or pr.url)
    rep.add("6", "pull request", "ok", f"#{pr.number} {'opened' if pr.created else 'updated'}"
            f"{' as a draft' if pr.created and not args.ready else ''}: {pr.url}"
            + (f"; labels {', '.join(sorted(labels))}" if labels else ""), time.time() - t)
    return pr


def judge_checks(checks: list[dict]) -> tuple[str, str]:
    """("success", …) when check, model, negative, formal-model and acceptance each have
    a passing run and nothing fails or waits. A skipped run is not a pass, though GitHub
    takes one for a required check: `acceptance` runs only on a pull request, so it is the
    pull request's own run that passes it, and a required check whose every run was
    skipped is "missing"."""
    buckets: dict[str, list[str]] = {}
    for c in checks:
        buckets.setdefault(str(c.get("name")), []).append(str(c.get("bucket")))
    failing = sorted(n for n, b in buckets.items() if {"fail", "cancel"} & set(b))
    pending = sorted(n for n, b in buckets.items() if "pending" in b)
    missing = [n for n in REQUIRED_CHECKS if "pass" not in buckets.get(n, [])]
    shown = ", ".join(f"{n} {'/'.join(sorted(set(b)))}" for n, b in sorted(buckets.items()))
    if failing:
        return "failure", f"failing: {', '.join(failing)} ({shown})"
    if pending:
        return "pending", f"still running: {', '.join(pending)} ({shown})"
    if missing:
        return "missing", f"no passing run of {', '.join(missing)} ({shown or 'no checks'})"
    return "success", shown


def judged_checks(checks: list[dict], labels: set[str] | None) -> list[dict]:
    """Ignore only the known release job on an ordinary pull request. None means
    unreadable labels, so every check still counts."""
    if labels is None or RELEASE_LABEL in {label.lower() for label in labels}:
        return checks
    return [c for c in checks if not (
        c.get("name") == "release-gate" and c.get("workflow") == "Release gate")]


def pr_checks(ctx: Context, number: int) -> list[dict]:
    r = gh_run(ctx, "pr", "checks", str(number), "--json", "name,bucket,state,workflow")
    try:
        return json.loads(r.stdout or "[]") or []
    except json.JSONDecodeError:
        return []


def read_pr_labels(ctx: Context, number: int) -> set[str]:
    r = gh_run(ctx, "pr", "view", str(number), "--json", "labels")
    if r.returncode:
        raise ValueError("the pull request's labels could not be read")
    try:
        view = json.loads(r.stdout)
    except json.JSONDecodeError:
        raise ValueError("the pull request's labels are unreadable") from None
    if not isinstance(view, dict):
        raise ValueError("the pull request's labels are unreadable")
    return pr_labels(view.get("labels"))


def watch_checks(ctx: Context, pr: PR, rep: Report) -> str:
    """Wait for the pull request's checks on the commit and follow them; return the
    verdict, judged as the merge judges it (judged_checks): on an ordinary pull request
    a release-gate run left from an earlier label is waited for, never counted."""
    rep.heading("CI")
    t = time.time()
    checks: list[dict] = []
    while time.time() - t < CI_APPEAR_TIMEOUT:
        checks = pr_checks(ctx, pr.number)
        if checks:
            break
        time.sleep(CI_POLL)
    if not checks:
        rep.add("6", "CI", "FAIL", f"no checks appeared for #{pr.number} in "
                f"{CI_APPEAR_TIMEOUT} s: `gh pr checks {pr.number}`")
        return "unknown"
    print(f"  following the checks of #{pr.number}: {pr.url}", flush=True)
    run([*ctx.gh, "pr", "checks", str(pr.number), "--watch", "--interval",
         CI_WATCH_INTERVAL, "-R", ctx.github], ctx.repo, capture=False)
    checks = pr_checks(ctx, pr.number)
    label_problem = None
    try:
        labels = read_pr_labels(ctx, pr.number)
    except ValueError as e:
        labels, label_problem = None, str(e)
    verdict, detail = judge_checks(judged_checks(checks, labels))
    if label_problem:
        detail = f"{label_problem}; every check retained ({verdict}: {detail})"
        verdict = "unknown"
    rep.add("6", "CI", "ok" if verdict == "success" else "FAIL", f"{verdict}: {detail}",
            time.time() - t)
    return verdict


# --------------------------------------------------------------------------------------
# The pre-flight's record, for --merge


def log_path() -> Path:
    env = os.environ.get("STOICHEIA_PUSH_LOG")
    return Path(env) if env else Path.home() / ".cache" / "stoicheia" / "pushes.log"


def record_path(sha: str, base: str) -> Path:
    return log_path().parent / "preflight" / f"{sha}-{base}.json"


def make_record(ctx: Context, pre: Preflight, rep: Report, full: bool, risk: Risk,
                checked: dict | None = None) -> dict:
    """The pre-flight's record. `checked`, the earlier record that stood in for step 4
    (--merge), gives its step 4 and its notes. "class" is the change's class, by
    origin/main's risk.py when this record was made, and "short" says that step 4 was left
    to CI for it; "full", that step 4 ran in full (here or in `checked`)."""
    steps = [[s.stage, s.name, s.outcome, s.seconds] for s in rep.steps
             if s.outcome in ("ok", "FAIL", "skip") and s.stage in ("2", "3", "4")]
    notes = [[s.name, (s.detail.splitlines() or [""])[0]] for s in rep.steps
             if s.outcome == "note"]
    if checked is not None:
        steps = [s for s in steps if s[0] != "4"] + \
            [list(s) for s in checked.get("steps", []) if s and s[0] == "4"]
        notes += [[s.name, f"{s.outcome}, {s.detail}"] for s in rep.steps
                  if s.stage == "4" and s.outcome == "skip"]
        notes += [list(n) for n in checked.get("notes", [])
                  if n[0] != "full local checks" and list(n) not in notes]
    return {
        "sha": ctx.sha, "base": ctx.base, "branch": ctx.branch,
        "full": (full and not pre.short) or bool(checked and checked.get("full")),
        "class": risk.cls, "class_why": risk.why, "short": pre.short,
        "time": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
        "harness": HARNESS, "harness_blob": HARNESS_BLOB,
        "harness_sha": ctx.harness_sha or ctx.base,
        "steps": steps, "notes": notes,
        "protected": pre.protected, "statements": pre.statements,
    }


def checks_record(record: dict | None, test_mode: bool, risk: Risk) -> dict | None:
    """The record, if it may stand in for step 4 at the merge: made by origin/main's
    harness, the one running now, and either of the full checks, run (or skipped by the
    internal test flag, under it), or of a pre-flight that left them to CI for its class,
    while the class, `risk`, recomputed now by origin/main's risk.py for that commit
    against that base, is still R0 to R2. The record is a local file anything run as the
    user could write, so it never stands in for the secret scan or the guards, and CI runs
    the same checks. A record of any other shape stands in for nothing."""
    if not isinstance(record, dict) or HARNESS_BLOB is None \
            or record.get("harness_blob") != HARNESS_BLOB:
        return None
    steps = record.get("steps")
    if not isinstance(steps, list) or any(
            not isinstance(s, list) or len(s) != 4 or s[0] not in ("2", "3", "4")
            or not isinstance(s[1], str) or not s[1] or s[2] not in ("ok", "skip")
            or (s[3] is not None and (type(s[3]) not in (int, float)
                                     or not math.isfinite(s[3]) or s[3] < 0))
            for s in steps):
        return None
    notes = record.get("notes")
    if not isinstance(notes, list) or any(
            not isinstance(n, list) or len(n) != 2
            or any(not isinstance(x, str) for x in n) for n in notes):
        return None
    if any(not isinstance(record.get(k), str) or not record[k].strip()
           for k in ("harness", "time")):
        return None
    if record.get("short"):
        low = record.get("class") in LOW_CLASSES and risk.cls in LOW_CLASSES
        return record if low else None
    if not (record.get("full") is True or test_mode):
        return None
    full_steps = [s for s in steps if s[0] == "4"]
    if not full_steps or any(s[2] != "ok" and not test_mode for s in full_steps):
        return None
    return record


def full_record(record: dict | None, test_mode: bool) -> bool:
    """Does the record hold step 4 in full: run (or, under the internal test flag, skipped
    by it), never left to CI for the change's class? A release needs one."""
    return bool(record) and not record.get("short") and bool(record.get("full") or test_mode)


def save_record(record: dict) -> None:
    path = record_path(record["sha"], record["base"])
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(record, indent=1) + "\n")


def load_record(sha: str, base: str) -> dict | None:
    try:
        record = json.loads(record_path(sha, base).read_text())
    except (OSError, UnicodeError, json.JSONDecodeError):
        return None
    return record if isinstance(record, dict) and record.get("sha") == sha \
        and record.get("base") == base else None


class Held(NamedTuple):
    """What this run's pre-flight left in memory for its merge (--land), never read back
    from a file: the commit pushed, origin/main then, a copy of the record taken as it was
    made, before it was saved, whether origin/main's pass of step 4 was taken from the
    main-checks cache in this run (a hit), and origin's URL as git gave it before any of
    the commit's code ran. The merge refuses an origin with another URL before it fetches,
    and an origin/main other than this one once it has (merge_preconditions)."""
    sha: str
    base: str
    record: dict
    cached: bool
    origin: str


def held_record(held: Held, ctx: Context, risk: Risk) -> tuple[dict | None, str]:
    """The earlier record for --land's merge, from memory alone: the disk is never read
    here, whatever it holds. None, and why, when origin/main's pass of step 4 was taken
    from the main-checks cache, a file, or when the record is not of the head and the base
    the merge checks (ctx.sha and ctx.base), which backs up the merge's refusal of a head
    that is not the commit pushed. checks_record then judges it, as it judges a file's."""
    again = "the full checks run now" if risk.cls not in LOW_CLASSES else \
        f"step 4 runs again now, and leaves the full checks to CI for the class {risk.cls}"
    if held.cached:
        return None, ("origin/main's pass of step 4 was taken from the main-checks cache, a "
                      "file, so the record kept in memory does not stand in for it: "
                      f"{again}")
    if held.record.get("sha") != ctx.sha or held.record.get("base") != ctx.base:
        return None, (f"the record kept in memory is not of {ctx.sha[:12]} against "
                      f"origin/main {ctx.base[:12]}, so it stands in for nothing: {again}")
    return held.record, ""


# --------------------------------------------------------------------------------------
# --merge: the gates, then a merge commit


# A required box of a checklist: the first line of a list item (boxes, below).
BOX = re.compile(r"^\s*[-*][ \t]{1,4}\[([ xX])\]\s+\*\*(Required(?: if protected)?):\*\*"
                 r"\s*(.*?)\s*$")


def boxes(body: str) -> list[tuple[bool, str, str]]:
    """(ticked, kind, text) for each required box of a checklist, where GitHub shows one:
    a task-list item, so the first line of a list item as shown reads it, never a line of
    a paragraph, of code or of HTML."""
    found = []
    for line, item in shown(body or ""):
        m = BOX.match(line) if item else None
        if m:
            found.append((m.group(1) != " ", m.group(2), " ".join(m.group(3).split())))
    return found


def checklist_problems(body: str, template: str | None, protected: bool) -> list[str]:
    """The required boxes unticked, or missing from the body, counted where GitHub shows
    them (boxes): a box in a comment, in code or in a paragraph is not a box."""
    def needed(kind):
        return kind == "Required" or protected

    have = boxes(body)
    wanted = [(k, x) for _, k, x in boxes(template or "") if needed(k)]
    if not have and not wanted:
        return ["the body has no checklist of required boxes: use "
                f"{TEMPLATE}"]
    problems = [f"unticked: {k}: {x}" for ticked, k, x in have if needed(k) and not ticked]
    present = {(k, x) for _, k, x in have}
    problems += [f"missing from the body: {k}: {x}" for k, x in wanted if (k, x) not in present]
    return problems


SECTION = re.compile(r"(?m)^## +(.+?) *$")
# The sections the coordinator writes, which --merge needs written when the template has them.
WRITTEN = ("What and why", "Reviews", "Needs the owner's OK")
# CommonMark's blocks, read from a line less the indentation of its containers (shown,
# below). A fence opens with three or more backticks or tildes, and, after backticks, an
# info string with no backtick in it; it closes with the same character, at least as
# many, and nothing after them.
FENCE_OPEN = re.compile(r"(`{3,}(?=[^`]*$)|~{3,})")
FENCE_CLOSE = re.compile(r"(`{3,}|~{3,})[ \t]*$")
LIST_ITEM = re.compile(r"(?:[-*+]|\d{1,9}[.)])(?=[ \t]|$)")
HEADING = re.compile(r"#{1,6}(?:[ \t]|$)")
# The HTML blocks (CommonMark 0.29, section 4.6, which GitHub follows): what starts one,
# and what ends it, None for a blank line. GitHub shows their lines as HTML, never as
# Markdown, so a box or a heading in one is neither. A seventh kind, a whole tag alone on
# its line, cannot interrupt a paragraph.
BLOCK_TAGS = ("address|article|aside|base|basefont|blockquote|body|caption|center|col|"
              "colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|"
              "form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|"
              "menu|menuitem|nav|noframes|ol|optgroup|option|p|param|section|source|summary|"
              "table|tbody|td|tfoot|th|thead|title|tr|track|ul")
HTML_BLOCKS = (
    (re.compile(r"<(?:pre|script|style|textarea)(?:[ \t>]|$)", re.I),
     re.compile(r"</(?:pre|script|style|textarea)>", re.I)),
    (re.compile(r"<!--"), re.compile(r"-->")),
    (re.compile(r"<\?"), re.compile(r"\?>")),
    (re.compile(r"<![A-Za-z]"), re.compile(r">")),
    (re.compile(r"<!\[CDATA\["), re.compile(r"\]\]>")),
    (re.compile(rf"</?(?:{BLOCK_TAGS})(?:[ \t>]|/>|$)", re.I), None),
)
HTML_TAG_LINE = re.compile(r"(?:<[A-Za-z][A-Za-z0-9-]*(?:\s+[A-Za-z_:][\w.:-]*"
                           r"(?:\s*=\s*(?:[^\s\"'=<>`]+|'[^']*'|\"[^\"]*\"))?)*\s*/?>"
                           r"|</[A-Za-z][A-Za-z0-9-]*\s*>)[ \t]*$")
# Inline, in a paragraph (CommonMark, section 6), left to right, whichever starts first: a
# backslash escape; a code span, a run of backticks to the next run of as many; a run of
# backticks left unmatched, which is text; an HTML comment closed within the paragraph.
# So "<!--" in a code span is code, and an unclosed "<!--" is text.
INLINE = re.compile(r"\\[!-/:-@\[-`{-~]|(`+)(?!`).*?(?<!`)\1(?!`)|`+|<!--.*?-->", re.S)
# Cells that hold a place, not a review's commit or findings.
EMPTY_CELL = {"", "-", "–", "—", "...", "…", "tbd", "todo"}


def shown(body: str, keep_own: bool = False) -> list[tuple[str, bool]]:
    """The lines of the body GitHub shows as Markdown, less what is not the coordinator's,
    each with whether it starts a list item: CommonMark's blocks, read line by line. The
    parts safe_push wrote go first, unless keep_own: GitHub shows them too, so whether a
    line is shown at all is read with them in place. Then fenced code (closed only by its
    own character, at least as many, and nothing after them; never closed, it runs to the
    end), indented code
    (four spaces or more past its container, unless it goes on with a paragraph) and HTML
    blocks, a comment among them: a line that starts with "<!--", three spaces in at most,
    hides the lines to the one that holds "-->", or to the end. A list item starts three
    spaces at most past its container: the top level, or the list item it is nested in, by
    that item's content column. In a paragraph, a code span is kept as it is and a comment
    closed within the paragraph is dropped; an unclosed "<!--" there is text (INLINE)."""
    lines: list[tuple[str, bool]] = []
    para: list[tuple[str, bool]] = []       # the open paragraph's lines
    items: list[int] = []   # the content columns of the open list items, outermost first
    fence = None            # an open fence: its marker, and its container's column
    html = None             # an open HTML block: its end (None, a blank line), and column

    def close() -> None:
        """The paragraph ends: its lines as GitHub shows them."""
        if para:
            text = INLINE.sub(lambda m: "" if m.group(0).startswith("<!--") else m.group(0),
                              "\n".join(t for t, _ in para)).split("\n")
            lines.append((text[0], para[0][1]))
            lines.extend((t, False) for t in text[1:])
            para.clear()

    body = body or ""
    for line in (body if keep_own else OWN_PART.sub("", body)).splitlines():
        text = line.expandtabs(4)
        spaces = len(text) - len(text.lstrip(" "))
        blank = not text.strip()
        if fence is not None:
            marker, col = fence
            if blank or spaces >= col:
                m = FENCE_CLOSE.match(text[spaces:])
                if m and spaces - col <= 3 and m.group(1)[0] == marker[0] \
                        and len(m.group(1)) >= len(marker):
                    fence = None
                continue
            fence = None                    # its container ends, and the fence with it
        if html is not None:
            end, col = html
            if blank and end is None:
                html = None                 # a blank line ends it, and is read below
            elif blank or spaces >= col:
                if end is not None and end.search(text):
                    html = None
                continue
            else:
                html = None                 # its container ends, and the block with it
        if blank:
            close()
            lines.append(("", False))
            continue
        depth = 0
        while depth < len(items) and spaces >= items[depth]:
            depth += 1
        col = items[depth - 1] if depth else 0
        content = text[spaces:]
        starts = spaces - col <= 3 and bool(
            FENCE_OPEN.match(content) or HEADING.match(content) or LIST_ITEM.match(content)
            or any(start.match(content) for start, _ in HTML_BLOCKS))
        if depth < len(items):
            if para and not starts:
                para.append((line, False))  # a lazy line: it goes on with the paragraph
                continue
            del items[depth:]
            close()
        if spaces - col >= 4:
            if para:
                para.append((line, False))  # it goes on with the paragraph; else code
            continue
        m = FENCE_OPEN.match(content)
        if m:
            close()
            fence = (m.group(1), col)
            continue
        end = next((e for start, e in HTML_BLOCKS if start.match(content)), False)
        if end is False and not para and HTML_TAG_LINE.match(content):
            end = None
        if end is not False:
            close()
            if end is None or not end.search(content):
                html = (end, col)
            continue
        m = LIST_ITEM.match(content)
        if HEADING.match(content) or content.startswith("|"):
            close()                         # a heading, or a table's row: read alone
            para.append((line, False))
            close()
        elif m:
            close()
            rest = content[m.end():]
            gap = len(rest) - len(rest.lstrip(" "))
            items.append(spaces + m.end() + (gap if 1 <= gap <= 4 else 1))
            para.append((line, True))
            if not rest.strip():
                close()
        else:
            para.append((line, False))
    close()
    return lines


def visible(body: str) -> str:
    """The body as GitHub shows it, less what is not the coordinator's (shown): without the
    parts safe_push wrote, HTML comments and blocks, and code. Both checklist_problems and
    sections read the body through it, so a box or a heading in a comment or in code does
    not count."""
    return "\n".join(line for line, _ in shown(body))


def sections(body: str) -> dict[str, str]:
    """{heading: words} for the body's `## ` sections, the first of each name, read as
    GitHub shows them, without what safe_push wrote (visible): the coordinator's own
    words."""
    parts = SECTION.split(visible(body))
    found: dict[str, str] = {}
    for i in range(1, len(parts) - 1, 2):
        found.setdefault(parts[i].strip(), parts[i + 1].strip())
    return found


def review_rows(text: str) -> dict[str, list[str]]:
    """{review: its cells after the first} for each row of a Reviews table, the first
    row of each review."""
    rows: dict[str, list[str]] = {}
    for line in text.splitlines():
        if not line.strip().startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        name = cells[0].strip("`*_ ")
        if name.startswith("/"):
            rows.setdefault(name, cells[1:])
    return rows


def written(cell: str) -> bool:
    return cell.strip("`*_ ").lower() not in EMPTY_CELL


def section_problems(body: str, template: str | None, protected: bool) -> list[str]:
    """The coordinator's Markdown sections. Unfinished work has its own raw-text gate."""
    wanted, have = sections(template or ""), sections(body)
    problems = []
    for name in (n for n in WRITTEN if n in wanted):
        if name not in have:
            problems.append(f"missing from the body: the section \"{name}\"")
        elif name == "Reviews":
            rows = review_rows(have[name])
            for review in review_rows(wanted[name]):
                cells = rows.get(review, [])
                if (review != "/security-review" or protected) and not (
                        len(cells) >= 2 and all(written(c) for c in cells[:2])):
                    problems.append(f"not written: the review {review}, its commit and its "
                                    "findings")
        elif not have[name]:
            problems.append(f"not written: the section \"{name}\"")
    return problems


# "Unfinished work" is read as raw text, never through `shown`: whatever GitHub might hide
# or show differently is refused, so that what the gate reads is what a reader sees. The
# one heading is this line exactly, outside the parts safe_push writes, and `shown`, which
# reads those parts in place as GitHub does, must find it too, so that one in a comment,
# an HTML block, code or such a part, which GitHub would not show, cannot stand in for the
# section. The section runs to the next of the template's own headings; only the
# template's own comment for it may stay, and nothing else but plain ASCII: "None", or a
# list whose items each name an issue as #N.
UNFINISHED_HEADING = "## Unfinished work"
# A token naming an issue: #N, perhaps in parentheses or before punctuation.
ISSUE_TOKEN = re.compile(r"\(?#([1-9][0-9]*)[).,;:]*")
# Characters GitHub reads as markup, or as a break or nothing, refused in the section.
UNFINISHED_FORBIDDEN = (("`", "a backtick (code)"), ("<", "HTML or a comment"),
                        (">", "HTML or a block quote"), ("[", "a bracket (link)"),
                        ("]", "a bracket (link)"), ("~", "a tilde"), ("|", "a pipe"),
                        ("_", "an underscore (emphasis)"), ("\\", "a backslash escape"),
                        ("://", "a URL"),
                        ("www.", "a URL"), ("&", "an entity"))
SCHEMELESS_URL = re.compile(
    r"(?i)(?<![A-Za-z0-9_.-])(?:(?:(?:[A-Za-z0-9](?:[A-Za-z0-9-]{0,62}"
    r"[A-Za-z0-9])?\.)+[A-Za-z]{2,63}|(?:[0-9]{1,3}\.){3}[0-9]{1,3})"
    r"(?::[0-9]{1,5})?(?:/\S*)?|[A-Za-z](?:[A-Za-z0-9-]{0,62}[A-Za-z0-9])?"
    r":[0-9]{1,5}(?:/\S*)?)")


def raw_lines(text: str) -> list[str]:
    """Lines as CommonMark breaks them, at a line feed (a carriage return before it
    dropped), never at the other separators str.splitlines knows; a carriage return or
    separator left inside a line is refused by the callers."""
    return [line[:-1] if line.endswith("\r") else line for line in text.split("\n")]


# Inside a line, a break CommonMark makes (a carriage return) or one str.splitlines makes
# and GitHub does not: either would let the gate and a reader see different lines.
ODD_BREAK = re.compile("[\r\x0b\x0c\x1c-\x1e\x85  ]")


def reads_as_heading(line: str) -> bool:
    """A line that may be the section's heading written another way: its letters, with
    tags and entities taken out and compatibility forms folded, begin "unfinished work"
    (or are "unfinished", the first line of a heading split over two). A heading
    disguised on purpose, in another alphabet or in crafted markup, is the reviews'."""
    text = unicodedata.normalize("NFKC", html.unescape(re.sub(r"<[^>]*>", "", line)))
    letters = "".join(c for c in text.lower() if "a" <= c <= "z")
    return letters.startswith("unfinishedwork") or letters == "unfinished"


def template_section(template: str | None) -> tuple[str | None, set[str]]:
    """The template's own comment for "Unfinished work" (None when the template has no
    such section), and the headings that follow it, any of which ends the section."""
    lines = [line.rstrip() for line in raw_lines(template or "")]
    if UNFINISHED_HEADING not in lines:
        return None, set()
    start = lines.index(UNFINISHED_HEADING) + 1
    after = [i for i in range(start, len(lines)) if lines[i].startswith("## ")]
    end = after[0] if after else len(lines)
    return "\n".join(lines[start:end]).strip(), {lines[i] for i in after}


def unfinished_section(body: str, template: str | None = None) -> tuple[str, list[str]]:
    """The section's raw text, from its one heading to the next of the template's
    headings (to the end, with no template). Refused: a second heading, or any other
    line reads_as_heading finds; a heading GitHub does not show, read with the parts
    safe_push wrote in place (shown), or one in such a part; a break GitHub makes where a
    line does not, or the reverse; no following heading when the template has some."""
    _, ends = template_section(template)
    lines = raw_lines(body or "")
    odd = [n for n, line in enumerate(lines, 1) if ODD_BREAK.search(line)]
    if odd:
        return "", [f"line {odd[0]} of the body holds a carriage return, form feed or line "
                    "separator inside it, which GitHub and the gate would break differently"]
    starts = [i for i, line in enumerate(lines) if line.rstrip() == UNFINISHED_HEADING]
    alike = [line for line in lines
             if line.rstrip() != UNFINISHED_HEADING and reads_as_heading(line)]
    if len(starts) != 1 or alike:
        return "", ["the body must have exactly one ## Unfinished work heading, at the left "
                    "edge, and no other line whose letters begin \"unfinished work\" or "
                    "are just \"unfinished\""
                    + "".join(f": {printable_text(line.strip())}" for line in alike[:1])]
    owned = any(body.count("\n", 0, m.start()) <= starts[0] <= body.count("\n", 0, m.end())
                for m in OWN_PART.finditer(body))
    if owned or not any(line.rstrip() == UNFINISHED_HEADING
                        for line, _ in shown(body, keep_own=True)):
        return "", ["the ## Unfinished work heading must be one GitHub shows: not in an HTML "
                    "comment or block, in code, or in a part safe_push writes"]
    start = starts[0] + 1
    end = next((i for i in range(start, len(lines)) if lines[i].rstrip() in ends), None)
    if ends and end is None:
        return "", ["Unfinished work must end at the template's next heading"]
    return "\n".join(lines[start:end]), []


def unfinished_refs(text: str, comment: str | None = None) -> tuple[list[int], list[str]]:
    """The issues the section names, and its problems. The template's own comment for the
    section, given, is taken out once, exactly; then the text must be plain ASCII with no
    markup, and either "None" (case aside, with an optional full stop) or a list: each
    item `- ` or `* ` at the left edge with one space, wrapped with two to five spaces and
    no blank line, naming its issue as a token #N. Every other `#`, or GH-N, is refused."""
    if comment:
        # Only where it stands on lines of its own: text after its "-->" on the same line
        # is shown by GitHub outside any list, so the comment is then refused instead.
        text = re.sub(r"(?m)^" + re.escape(comment) + r"[ \t]*$", "", text, count=1)
    for n, line in enumerate(text.split("\n"), 1):
        odd = next((c for c in line if ord(c) > 126 or ord(c) < 32), None)
        if odd is not None:
            return [], [f"Unfinished work must be plain ASCII text, with no tab or control "
                        f"character: U+{ord(odd):04X} on line {n} of the section"]
    if "<!--" in text:
        return [], ["Unfinished work holds a comment other than the template's own for it "
                    "(origin/main's wording, which may have changed): delete it"]
    for token, reason in UNFINISHED_FORBIDDEN:
        if token.lower() in text.lower():
            return [], [f"Unfinished work must be a plain list: {reason} is forbidden"]
    if SCHEMELESS_URL.search(text):
        return [], ["Unfinished work must be a plain list: a URL is forbidden"]
    if re.fullmatch(r"None\.?", text.strip(), re.I):
        return [], []
    refs, problems, items = set(), [], []
    can_continue = False
    for line in text.split("\n"):
        if not line.strip():
            can_continue = False
            continue
        item = re.fullmatch(r"[-*] (\S.*)", line)
        continuation = re.fullmatch(r" {2,5}(\S.*)", line)
        if item:
            content = item[1]
            items.append(content)
        elif continuation and can_continue:
            content = continuation[1]
            items[-1] += " " + content
        else:
            problems.append(f"Unfinished work must be a plain list: invalid line: {line}")
            can_continue = False
            continue
        can_continue = True
        if re.match(r"(?:[-*+]|[0-9]+[.)])(?:\s|$)", content):
            problems.append(f"Unfinished work forbids a nested list or rule: {line}")
        elif re.fullmatch(r"(?:[-*_=] *)+", content):
            problems.append(f"Unfinished work forbids a heading or rule: {line}")
    for item in items:
        local = []
        for token in item.split():
            match = ISSUE_TOKEN.fullmatch(token)
            if match:
                local.append(int(match[1]))
            elif "#" in token or re.search(r"gh-[0-9]", token, re.I):
                problems.append(f"write the issue as #N on its own: {token}")
            elif re.search(r"github\.com|/issues/|/pull/", token, re.I):
                problems.append(f"Unfinished work names issues as #N, never by an address: "
                                f"{token}")
            elif "*" in token:
                problems.append(f"Unfinished work must be plain text, with no emphasis: "
                                f"{token}")
        refs.update(local)
        if not local:
            problems.append(f"list item names no local issue: {item}")
    if not refs and not problems:
        problems.append("Unfinished work must say None or name an open issue with blocks-release")
    return sorted(refs), problems


def issue_labels(issue: dict) -> set[str]:
    """Validate the fields both gates need; an incomplete response is never an empty
    list of blockers. REST and gh's issue list spell labels and state differently."""
    if not isinstance(issue, dict) or type(issue.get("number")) is not int \
            or issue["number"] <= 0:
        raise ValueError("issue has no valid number")
    if not isinstance(issue.get("state"), str) or issue["state"].lower() not in {
            "open", "closed"}:
        raise ValueError(f"#{issue['number']} has no valid state")
    labels = issue.get("labels")
    if not isinstance(labels, list):
        raise ValueError(f"#{issue['number']} has no valid labels")
    names = set()
    for label in labels:
        name = label.get("name") if isinstance(label, dict) else label
        if not isinstance(name, str) or not name.strip():
            raise ValueError(f"#{issue['number']} has an unreadable label")
        names.add(name.lower())
    return names


def unfinished_issue_problems(number: int, issue: dict, repository_url: str) -> list[str]:
    """A named issue must belong to the canonical repository, have this number, be
    open and labelled, and not be a pull request."""
    try:
        labels = issue_labels(issue)
    except ValueError as e:
        return [f"#{number} unreadable: {e}"]
    if issue["number"] != number:
        return [f"#{number} unreadable: GitHub returned another number"]
    url = issue.get("repository_url")
    if not isinstance(url, str) or not url:
        return [f"#{number} unreadable: no repository_url"]
    if url.lower() != repository_url.lower():
        return [f"#{number} belongs to another repository"]
    problems = []
    if "pull_request" in issue:
        problems.append(f"#{number} is a pull request, not an issue")
    if issue["state"].lower() != "open":
        problems.append(f"#{number} is closed")
    if BLOCKS_RELEASE not in labels:
        problems.append(f"#{number} lacks the label {BLOCKS_RELEASE}")
    return problems


def issue_pages(text: str) -> list[dict]:
    """Read every concatenated JSON array from gh api --paginate, refusing empty,
    malformed or non-array output, including a bad page after good pages."""
    decoder = json.JSONDecoder()
    rest, issues = text.strip(), []
    if not rest:
        raise ValueError("GitHub printed no issue pages")
    while rest:
        try:
            page, end = decoder.raw_decode(rest)
        except json.JSONDecodeError:
            raise ValueError("GitHub printed malformed issue JSON") from None
        if not isinstance(page, list):
            raise ValueError("GitHub did not return an array of issues")
        issues.extend(page)
        rest = rest[end:].lstrip()
    return issues


def printable_text(text: str) -> str:
    """Text another may write, as an issue's title or a path a commit names, with every
    character a terminal could take for a command (controls, format characters as the
    bidirectional marks), and every other that Python counts unprintable, written as an
    escape."""
    return "".join(c if c.isprintable() else c.encode("unicode_escape").decode("ascii")
                   for c in text)


def open_blockers(issues: list[dict]) -> list[dict]:
    """The open labelled issues, pull requests included. Validate every entry, even
    one that would not block, so a partial response cannot pass as a complete reading."""
    if not isinstance(issues, list):
        raise ValueError("expected an array of issues")
    blockers = []
    for issue in issues:
        labels = issue_labels(issue)
        if not isinstance(issue.get("title"), str) or not issue["title"].strip():
            raise ValueError(f"#{issue['number']} has no title")
        url = issue.get("html_url") or issue.get("url")
        if not isinstance(url, str) or not url.strip():
            raise ValueError(f"#{issue['number']} has no URL")
        if issue["state"].lower() == "open" and BLOCKS_RELEASE in labels:
            blockers.append(issue)
    return blockers


def read_issues(ctx: Context, path: str, *, paginate=False):
    """Read issues, their repository or a workflow's runs and jobs through ctx.gh
    directly: gh api has no -R flag. Never accept stdout on failure or print gh's errors,
    which may contain credentials."""
    try:
        r = run([*ctx.gh, "api", *(["--paginate"] if paginate else []), path], ctx.repo)
    except (OSError, UnicodeError):
        raise ValueError("GitHub could not be read") from None
    if r.returncode:
        raise ValueError(f"GitHub API read failed (exit {r.returncode})")
    if paginate:
        return issue_pages(r.stdout)
    try:
        return json.loads(r.stdout)
    except json.JSONDecodeError:
        raise ValueError("GitHub printed malformed API JSON") from None


def unfinished_gate(ctx: Context, body: str, template: str | None) -> tuple[str, str]:
    """The section is required only once the template in force has it."""
    comment, _ = template_section(template)
    if comment is None:
        return "skip", "the template in force has no Unfinished work section"
    text, problems = unfinished_section(body, template)
    if problems:
        return "FAIL", "\n".join(problems)
    refs, problems = unfinished_refs(text, comment)
    if problems:
        return "FAIL", "\n".join(problems)
    if not refs:
        return "ok", "None"
    try:
        repository = read_issues(ctx, f"repos/{ctx.github}")
        url = repository.get("url") if isinstance(repository, dict) else None
        if not isinstance(url, str) or not re.fullmatch(
                r"https://api\.github\.com/repos/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", url, re.I):
            raise ValueError("GitHub returned no canonical repository URL")
    except ValueError as e:
        return "FAIL", f"repository unreadable: {e}"
    for number in refs:
        try:
            issue = read_issues(ctx, f"repos/{ctx.github}/issues/{number}")
            problems.extend(unfinished_issue_problems(number, issue, url))
        except ValueError as e:
            problems.append(f"#{number} unreadable: {e}")
    return ("FAIL", "\n".join(problems)) if problems else (
        "ok", ", ".join(f"#{n}" for n in refs) or "None")


def release_gate(ctx: Context, labels: set[str] | None) -> tuple[str, str]:
    """Only a release pull request reads the open blockers; an ordinary one may land
    unfinished work. Every read failure holds the release."""
    if labels is None:
        return "FAIL", "the pull request's labels are unreadable"
    if RELEASE_LABEL not in {label.lower() for label in labels}:
        return "skip", "not a release pull request"
    try:
        blockers = open_blockers(read_issues(
            ctx, f"repos/{ctx.github}/issues?labels={BLOCKS_RELEASE}&state=open&per_page=100",
            paginate=True))
    except ValueError as e:
        return "FAIL", f"release issues unreadable: {e}"
    if blockers:
        return "FAIL", "open blocks-release:\n" + "\n".join(
            f"#{issue['number']}: {printable_text(issue['title'])}" for issue in blockers)
    return "ok", "no open blocks-release issue"


def release_needs_full_record(ctx: Context, number: int, labels: set[str] | None,
                              usable: dict | None, earlier: dict | None, test_mode: bool,
                              rep: Report) -> None:
    """A pull request labelled release merges only on a record of the full pre-flight of
    its head against this origin/main (full_record, by origin/main's harness), never on one
    that left step 4 to CI for its class, nor on none, with the full checks left for
    --merge itself to run: refused otherwise, saying to run the pre-flight again, whose
    class the label makes R5. `usable` is the record that may stand in for step 4
    (checks_record), `earlier` the record found, for the message."""
    if labels is None or RELEASE_LABEL not in labels or full_record(usable, test_mode):
        return
    if earlier is None:
        why = f"there is no record of its pre-flight against origin/main {ctx.base[:12]}"
    elif earlier.get("short"):
        why = (f"its pre-flight left the full checks to CI, for the class "
               f"{earlier.get('class')}")
    else:
        why = "its record is not of the full checks by origin/main's harness"
    rep.add("1", "release record", "FAIL", why)
    raise Refusal(f"#{number} is labelled {RELEASE_LABEL}, and a release merges only on the "
                  f"full pre-flight of its head, {ctx.sha[:12]}, against origin/main "
                  f"{ctx.base[:12]}: {why}. Run the pre-flight again (`git safe-push --branch "
                  f"{ctx.branch}`; with the label on the pull request, or --label "
                  f"{RELEASE_LABEL}, its class is R5 and the full checks run), then --merge")


def suite_gate(ctx: Context, labels: set[str] | None) -> tuple[str, str]:
    """A release pull request merges only with a green run of the safe-push-tests workflow
    at its exact head (#301): a completed, successful run of
    .github/workflows/safe-push-tests.yml whose head is the pull request's, in which each
    job of SUITE_JOBS is there and passed, and every other job passed too, save `report`,
    which runs only for a red run on main and so is skipped in a green one. The jobs of
    SUITE_JOBS are the verdict on the shards of scripts/test_safe_push.py, the negative
    tests in full and the formal model's build and kernel re-check, which CI runs on a pull
    request only by its class; the shards, the eight jobs of the matrix the verdict needs,
    are among the others, each held to have passed.
    A run at the head runs the head's copy of the workflow, which could drop or empty a
    job, so the head's copy must be origin/main's: a change to it lands first, in a pull
    request of its own. An ordinary pull request asks GitHub nothing here; unreadable
    labels and every unreadable answer hold the merge."""
    if labels is None:
        return "FAIL", "the pull request's labels are unreadable"
    if RELEASE_LABEL not in {label.lower() for label in labels}:
        return "skip", "not a release pull request"

    def entry(rev: str) -> str | None:
        """The workflow's tree entry at `rev` (its mode, type and object), "" if absent."""
        r = run(["git", "ls-tree", "--full-tree", rev, "--", SUITE_PATH], ctx.repo)
        return r.stdout.strip() if r.returncode == 0 else None
    mains, ours = entry(ctx.base), entry(ctx.sha)
    if not mains:
        return "FAIL", (f"origin/main {ctx.base[:12]} has no {SUITE_PATH}, or Git could not "
                        "read it: no run can show that the suite passed")
    if ours is None:
        return "FAIL", f"Git could not read {SUITE_PATH} at the head {ctx.sha[:12]}"
    if ours != mains:
        return "FAIL", (f"the head {ctx.sha[:12]} changes {SUITE_PATH}, and a run at the head "
                        "runs the head's copy of it, not origin/main's, so no run there can "
                        "show that main's jobs passed: land that change first, in a pull "
                        f"request of its own, then merge origin/main into {ctx.branch} and "
                        "run the workflow at the new head")
    how = (f"run it at the head (`gh workflow run {SUITE_WORKFLOW} --ref {ctx.branch}`), "
           "wait for every job to pass, then --merge again")
    try:
        found = read_issues(ctx, f"repos/{ctx.github}/actions/workflows/{SUITE_WORKFLOW}/"
                                 f"runs?head_sha={ctx.sha}&per_page=100")
        runs = found.get("workflow_runs") if isinstance(found, dict) else None
        if not isinstance(runs, list) or any(not isinstance(r, dict) for r in runs):
            raise ValueError("GitHub returned no list of runs")
        here = [r for r in runs if r.get("head_sha") == ctx.sha]
        green = [r for r in here if r.get("status") == "completed"
                 and r.get("conclusion") == "success"]
        if not green:
            seen = ", ".join(sorted({f"{r.get('status')}/{r.get('conclusion')}"
                                     for r in here})) or "none"
            return "FAIL", (f"no green run of {SUITE_WORKFLOW} at the head {ctx.sha[:12]} "
                            f"(runs there: {printable_text(seen)[:200]}): {how}")
        problems = []
        for r in green:
            if type(r.get("id")) is not int:
                raise ValueError("a run has no id")
            listed = read_issues(ctx, f"repos/{ctx.github}/actions/runs/{r['id']}/"
                                      "jobs?per_page=100")
            jobs = listed.get("jobs") if isinstance(listed, dict) else None
            if not isinstance(jobs, list) or not jobs \
                    or listed.get("total_count") != len(jobs) \
                    or any(not isinstance(j, dict) or not isinstance(j.get("name"), str)
                           for j in jobs):
                raise ValueError(f"the jobs of run {r['id']} are unreadable")
            red = [f"{j['name']} {j.get('conclusion')}" for j in jobs
                   if j.get("conclusion") != "success"
                   and not (j["name"] == SUITE_REPORT_JOB and j.get("conclusion") == "skipped")]
            missing = [f"{name} missing" for name in SUITE_JOBS
                       if name not in {j["name"] for j in jobs}]
            if not red and not missing:
                passed = ", ".join(sorted(j["name"] for j in jobs if j["name"] != SUITE_REPORT_JOB))
                return "ok", (f"run {r['id']} of {SUITE_WORKFLOW} at {ctx.sha[:12]}: "
                              f"{printable_text(passed)[:300]} passed")
            problems.append(f"run {r['id']}: " + printable_text(", ".join(red + missing)))
    except ValueError as e:
        return "FAIL", f"the runs of {SUITE_WORKFLOW} unreadable: {e}"
    return "FAIL", (f"no run of {SUITE_WORKFLOW} at the head {ctx.sha[:12]} has every job "
                    f"green ({'; '.join(problems)[:300]}): {how}")


def protected_files(repo, base, sha) -> list[str]:
    return sorted({p for _, p in changed_files(repo, base, sha) if is_protected(p)})


def merge_preconditions(repo: Path, number: int, test_mode: bool, rep: Report,
                        held: Held | None = None):
    """`held`, for the merge of --land: origin and origin/main as the push left them, each
    refused at once when it is not, and a harness that never hands over."""
    rep.heading("1. Preconditions")
    origin = git(repo, "remote", "get-url", "origin", check=False).strip()
    if not origin:
        raise Refusal("this repository has no remote called origin")
    # Before the fetch: the commit's code could have pointed the clone's origin at a copy
    # where main is never seen to move. Only the URL is compared, as git gives it
    # (insteadOf expanded); settings that redirect a fetch with the URL unchanged
    # (core.sshCommand, http.proxy, include.path and the like) are no more checked here
    # than for a separate --merge.
    if held is not None and origin != held.origin:
        raise Refusal(f"origin's URL changed during the run, from {held.origin} to "
                      f"{origin}; nothing is merged: set it back, then --merge")
    base = fetch_base(repo, origin, test_mode, rep,
                      remote=held.origin if held is not None else "origin")
    # Before the harness is compared or anything judged against the new main. Run on, the
    # full checks would take about 36 minutes, and then the body's summary, of the old
    # main, refuses the merge, or these preconditions refuse it for a main the head lacks.
    # And harness() compares the new main's harness with the copy on disk, which code left
    # running by the commit could have rewritten to match, so a superseded harness, in
    # memory, would run the merge. In queue mode `base` is the tip too (ctx.harness_sha),
    # so the same refusal holds; there a queued head is checked against the base it holds,
    # so a moved main a separate --merge would check in full and enqueue waits for it.
    if held is not None and base != held.base:
        raise Refusal(f"origin/main moved from {held.base[:12]} to {base[:12]} during CI; "
                      "nothing is merged, nor judged against the new main: run the "
                      "pre-flight again against it (`git safe-push --branch <name>`, merging "
                      "origin/main in first if the head lacks it), then --merge; in a merge "
                      "queue, --merge alone")
    harness(repo, base, rep, hand_over=held is None)
    trusted_harness = harness_snapshot(repo, base) if held is not None else None
    slug = "test/stoicheia" if test_mode else github_slug(origin)
    if not slug:
        raise Refusal(f"origin ({origin}) is not on GitHub: there is no pull request to merge")
    gh = gh_command(test_mode)
    gh_ready(gh, repo, test_mode)
    ctx = Context(repo, "", base, 0, origin, slug, {}, None, gh, harness_sha=base,
                  trusted_harness=trusted_harness,
                  pinned_origin=held.origin if held is not None else None)
    queued = queue_enabled(ctx, rep)
    view = gh_json(ctx, "pr", "view", str(number), "--json",
                   "number,state,isDraft,headRefName,headRefOid,baseRefName,body,labels,url,"
                   "isCrossRepository,title")
    main_health(ctx, rep, (view or {}).get("body"))
    if not view or view.get("state") != "OPEN":
        raise Refusal(f"pull request #{number} is not open ({(view or {}).get('state')})")
    if view.get("baseRefName") != "main" or view.get("isCrossRepository"):
        raise Refusal(f"pull request #{number} does not propose a branch of origin onto main")
    head, branch = view.get("headRefOid", ""), view.get("headRefName", "")
    if branch.lower() == "main":
        raise Refusal(f"pull request #{number}'s head is main")
    if rev_parse(repo, f"{head}^{{commit}}") is None:
        run(["git", "fetch", "origin", f"refs/heads/{branch}"], repo)
    if rev_parse(repo, f"{head}^{{commit}}") is None:
        raise Refusal(f"the head {head[:12]} of #{number} is not here after `git fetch origin`")
    if queued:
        base = queue_base(ctx, head)
        ctx = ctx._replace(base=base, queue=True)
    if not git_ok(repo, "merge-base", "--is-ancestor", base, head):
        raise Refusal(f"origin/main ({base[:12]}) is not an ancestor of #{number}'s head "
                      f"({head[:12]}): merge origin/main into {branch} (a merge commit), run "
                      f"the pre-flight again (--branch {branch}), then --merge")
    commits = int(git(repo, "rev-list", "--count", f"{base}..{head}").strip())
    rep.add("1", "pull request", "ok", f"#{number} \"{view.get('title')}\": {branch} at "
            f"{head[:12]}, {plural(commits, 'commit')} onto origin/main {base[:12]}")
    # The installed copies are compared with current main's, not with the older base a
    # queued head is checked against.
    check_installed(repo, ctx.harness_sha, rep)
    return ctx._replace(sha=head, commits=commits, branch=branch), view


def gates(ctx: Context, number: int, rep: Report, record: dict | None = None) -> dict:
    """Not a draft; every required box ticked; the coordinator's sections written; the
    title and the branch name, which go into main's merge commit, clean; an owner GitHub
    names for the head, which the merge commit's subject names (merge_subject); a label
    for its kind, and security-review when a protected path changes; unfinished work
    says None or names issues open with blocks-release; a release pull request has no
    open blocks-release issues or pull requests, and a green run of safe-push-tests at its
    head (suite_gate), with unreadable GitHub data refusing those gates; CI green on the
    head. Each is reported; any failure refuses the merge.
    The template is origin/main's,
    or the head's while origin/main has none (as generated_body reads it): any template
    is stricter than none. The record's notes are shown beside the checklist: a check that
    failed with origin/main's copies, on a commit that changes nothing the checks judge
    (keep_apart refuses the rest), is for the security review to weigh. A head moved, a
    branch renamed or a pull request no longer open since the merge first read it is
    refused. Returns the pull request as read, for the merge: its title and its branch
    name are the ones scanned, and its owner the one the subject gate showed."""
    rep.heading("2. The gates")
    view = gh_json(ctx, "pr", "view", str(number), "--json",
                   "isDraft,headRefOid,headRefName,headRepositoryOwner,body,labels,state,title")
    if view.get("headRefOid") != ctx.sha or view.get("headRefName") != ctx.branch \
            or view.get("state") != "OPEN":
        raise Refusal(f"#{number} changed meanwhile (head {str(view.get('headRefOid'))[:12]}, "
                      f"branch {view.get('headRefName')}, {view.get('state')}): run --merge "
                      "again")
    protected = protected_files(ctx.repo, ctx.base, ctx.sha)
    if view.get("isDraft"):
        rep.add("G", "draft", "FAIL", f"#{number} is a draft: when it is ready, "
                f"`gh pr ready {number}`")
    else:
        rep.add("G", "draft", "ok", "ready for review")
    try:
        check_public_names(view.get("headRefName") or "", view.get("title") or "")
        rep.add("G", "public names", "ok", "nothing the scan refuses in the title or the "
                "branch name, which go into main's merge commit")
    except Refusal as e:
        rep.add("G", "public names", "FAIL", f"{e}; they would go into main's merge commit "
                f"for good: rename them (`gh pr edit {number} --title`, or a branch of "
                "another name)")
    subject = merge_subject(number, view)
    if subject:
        rep.add("G", "subject", "ok", f"\"{subject}\", GitHub's own words, with the owner "
                "GitHub names for the head")
    else:
        rep.add("G", "subject", "FAIL", f"GitHub names no owner for #{number}'s head, or none "
                "an account could have, and the merge commit's subject names it: look with "
                f"`gh pr view {number} --json headRepositoryOwner`")
    body = view.get("body") or ""
    # The template in force is current main's (the harness's), also in queue mode, where
    # ctx.base may be an older main (queue_base): a box main added since binds this merge.
    policy = ctx.harness_sha or ctx.base
    template = show(ctx.repo, policy, TEMPLATE) or show(ctx.repo, ctx.sha, TEMPLATE)
    problems = checklist_problems(body, template, bool(protected))
    if problems:
        rep.add("G", "checklist", "FAIL", "\n".join(problems))
    else:
        rep.add("G", "checklist", "ok", "every required box ticked")
    unwritten = section_problems(body, template, bool(protected))
    if unwritten:
        rep.add("G", "sections", "FAIL", "\n".join(unwritten))
    else:
        rep.add("G", "sections", "ok", "the coordinator's required sections written")
    verdict, detail = unfinished_gate(ctx, body, template)
    rep.add("G", "unfinished work", verdict, detail)
    notes = [n for n in (record or {}).get("notes", []) if len(n) == 2 and n[0] != "pre-flight"]
    if notes:
        rep.add("G", "pre-flight notes", "note", f"{plural(len(notes), 'note')} of the "
                "pre-flight, for the reviews:\n" + "\n".join(f"{n}: {d}" for n, d in notes))
    try:
        labels = pr_labels(view.get("labels"))
    except ValueError as e:
        labels = None
        rep.add("G", "labels", "FAIL", str(e))
    verdict, detail = release_gate(ctx, labels)
    rep.add("G", "release", verdict, detail)
    verdict, detail = suite_gate(ctx, labels)
    rep.add("G", "safe-push tests", verdict, detail)
    if protected and labels is None:
        rep.add("G", "label", "FAIL", f"protected paths change ({', '.join(protected)}), and "
                f"#{number}'s labels are unreadable")
    elif protected and SECURITY_LABEL not in labels:
        rep.add("G", "label", "FAIL", f"protected paths change ({', '.join(protected)}), and "
                f"#{number} lacks the label {SECURITY_LABEL}")
    elif protected:
        rep.add("G", "label", "ok", f"{SECURITY_LABEL}, for {', '.join(protected)}")
    problem = "unreadable labels" if labels is None else kind_problem(labels)
    rep.add("G", "kind label", "FAIL" if problem else "ok", f"#{number} has {problem}"
            if problem else ", ".join(sorted(labels & set(KIND_LABELS))))
    verdict, detail = judge_checks(judged_checks(pr_checks(ctx, number), labels))
    rep.add("G", "CI", "ok" if verdict == "success" else "FAIL",
            f"{verdict} on {ctx.sha[:12]}: {detail}")
    failed = [s.name for s in rep.failed() if s.stage == "G"]
    if failed:
        raise Refusal(f"the merge gates refused: {', '.join(failed)}")
    return view


def merge_subject(number: int, view: dict) -> str | None:
    """GitHub's own subject for a pull request's merge commit, "Merge pull request #<n> from
    <owner>/<branch>", with the owner GitHub names for the head (headRepositoryOwner), never
    the owner in origin's URL, which after a transfer or a rename, both of which GitHub
    redirects, names the old one (issue #41). None when GitHub names no owner, or none an
    account could have (a login of letters, digits and hyphens), or no branch."""
    owner = view.get("headRepositoryOwner")
    login = owner.get("login") if isinstance(owner, dict) else None
    branch = view.get("headRefName")
    if not isinstance(login, str) or not GITHUB_LOGIN.fullmatch(login) \
            or not isinstance(branch, str) or not branch:
        return None
    return f"Merge pull request #{number} from {login}/{branch}"


def revert_advice(ctx: Context, kind: str | None = None) -> str:
    """How to undo a merge commit `ctx.sha`, through a pull request of its own, with the
    merged pull request's label for its kind. The decisions record stays as origin/main
    has it: the revert alone would delete the merge's entries, which guard_entries
    refuses, so the record is restored from origin/main, docs/decisions/ and the page
    each named only when origin/main holds it (git restore stops at a path its source
    lacks), and an entry of today's date records the revert, naming what it changes as
    any change's entry must: in sentences of its own, since a line or a list repeated
    from the merge's entry counts for nothing (entry_lines)."""
    branch = f"revert-{ctx.sha[:12]}"
    entry = f"{ENTRIES}{today().isoformat()}-revert-{ctx.sha[:12]}.md"
    held = [p for p in (ENTRIES, DECISIONS)
            if git_ok(ctx.repo, "cat-file", "-e", f"origin/main:{p.rstrip('/')}")]
    restore = ([f"    git restore --source=origin/main --staged --worktree -- {' '.join(held)}"]
               if held else [])
    return "\n".join([
        "Nothing has been reverted. To undo the merge, in a pull request of its own, with "
        "the decisions record kept as origin/main has it:",
        f"    git switch -c {branch} origin/main",
        f"    git revert --no-commit -m 1 {ctx.sha}",
        *restore,
        f"    # write {entry}: the revert and why, naming each protected file, statement",
        "    # and lock that it changes, as an entry of any change must, each in a sentence",
        "    # of the entry's own, never on a line or in a list repeated from an older entry",
        f"    git add -- {entry}",
        "    git commit --no-edit",
        f"    git safe-push --branch {branch} --label {kind or '<kind>'}"])


GITHUB_LOGIN = re.compile(r"[A-Za-z0-9][A-Za-z0-9-]{0,38}")    # an account's name
PR_STATES = ("OPEN", "CLOSED", "MERGED")                        # GitHub's, for a pull request
FULL_OID = re.compile(r"[0-9a-f]{40}|[0-9a-f]{64}")            # a commit's full object name


class NotMerged(Refusal):
    """GitHub says the pull request is not merged, after `gh pr merge` failed: nothing was
    merged, for certain."""


class MergeUnknown(Refusal):
    """GitHub's word shows no merge on main, though gh was asked to merge and nothing says
    it refused: gh exited 0 with the pull request not merged (a merge queue or auto-merge
    may merge it later), or GitHub says merged but names no merge commit, or one that
    origin/main does not hold. The merge state is unknown, and no revert is advised, for
    nothing on main is known to be the merge (issue #42)."""


def landing_remote(ctx: Context) -> str:
    if ctx.pinned_origin is None:
        return "origin"
    current = git(ctx.repo, "remote", "get-url", "origin", check=False).strip()
    if current != ctx.pinned_origin:
        raise Refusal(f"origin's URL changed during the run, from {ctx.pinned_origin} to "
                      f"{current}; nothing is merged: set it back, then --merge")
    return ctx.pinned_origin


def main_unmoved(ctx: Context) -> None:
    """The last look at main before the merge: --match-head-commit pins the head, not the
    base, so origin/main must still be the base checked."""
    remote = landing_remote(ctx)
    now = remote_refs(ctx.repo, "refs/heads/main", remote=remote).get("refs/heads/main")
    if now != ctx.base:
        raise Refusal(f"origin/main moved from {ctx.base[:12]} to {str(now)[:12]}: run "
                      "--merge again")


def merge(ctx: Context, number: int, view: dict) -> subprocess.CompletedProcess:
    """`gh pr merge`: a merge commit whose message is exactly what was scanned, GitHub's
    own subject for it (merge_subject), of the owner and the branch name the gates read
    (`view`, as gates returns it, which refuses one with no owner), and the title they
    read. gh's result, and nothing done after it returns, so that the caller records the
    outcome before GitHub is asked about it (as push_branch does the push)."""
    return gh_run(ctx, "pr", "merge", str(number), "--merge", "--delete-branch",
                  "--match-head-commit", ctx.sha,
                  "--subject", merge_subject(number, view) or "", "--body",
                  view.get("title") or "")


def merge_outcome(ctx: Context, number: int, rep: Report, r: subprocess.CompletedProcess,
                  started: float) -> str | None:
    """What came of `gh pr merge` (its result `r`), by GitHub's word alone: gh's exit
    status is never believed by itself. gh can fail after the merge (in deleting the
    branch, say), and can exit 0 without merging, when a merge queue or auto-merge takes
    the pull request to merge later (issue #42). So GitHub is asked whatever gh's exit.
    Merged: the merge commit GitHub names is returned, a full object name; when it names
    none, MergeUnknown, before anything else, since nothing on main is known to be the
    merge. Not merged (OPEN or CLOSED) after gh failed: NotMerged, for nothing was merged.
    Not merged after gh exited 0: MergeUnknown, since it may merge yet. GitHub not to be
    asked, or giving no state, or one that is none of its own: a refusal with the merge
    state unknown, since the merge may have happened."""
    said = (r.stdout + r.stderr).strip()
    exited = "exited 0" if r.returncode == 0 else "failed"
    try:
        view = gh_json(ctx, "pr", "view", str(number), "--json", "state,mergeCommit")
        state = view.get("state") if isinstance(view, dict) else None
        if not state:
            raise Refusal(f"it gave no state for #{number}")
        if state not in PR_STATES:
            raise Refusal(f"it gave #{number} a state that is none of "
                          f"{', '.join(PR_STATES)}: {str(state)[:40]!r}")
    except Refusal as e:
        rep.add("4", "gh pr merge", "FAIL", said or f"gh {exited}", time.time() - started)
        raise Refusal(f"`gh pr merge` {exited}, and GitHub could not be asked whether "
                      f"#{number} merged ({e}): look with `gh pr view {number}` before "
                      "anything else")
    if state == "MERGED":
        if r.returncode == 0:
            rep.add("4", "gh pr merge", "ok", f"#{number} merged with a merge commit",
                    time.time() - started)
        else:
            rep.add("4", "gh pr merge", "note", f"gh exited {r.returncode}, but GitHub says "
                    f"#{number} is merged: {(said.splitlines() or [''])[0]}",
                    time.time() - started)
        commit = view.get("mergeCommit")
        oid = commit.get("oid") if isinstance(commit, dict) else None
        if not isinstance(oid, str) or not FULL_OID.fullmatch(oid):
            named = "names no merge commit" if not oid else \
                f"names no merge commit by its full object name ({str(oid)[:40]!r})"
            rep.add("5", "main", "FAIL", f"GitHub says #{number} is merged, but it {named}")
            raise MergeUnknown(f"GitHub says #{number} is merged, but it {named}: look with "
                               f"`gh pr view {number}` and at origin/main before anything else")
        return oid
    rep.add("4", "gh pr merge", "FAIL", said or f"gh {exited}", time.time() - started)
    if r.returncode != 0:
        raise NotMerged(f"`gh pr merge` refused; nothing was merged (#{number} is {state})")
    raise MergeUnknown(f"`gh pr merge` exited 0, but GitHub says #{number} is {state}, not "
                       "merged: a merge queue or auto-merge may merge it later, and this run "
                       f"does not follow it; look with `gh pr view {number}` before anything "
                       "else")


def verify_merge(ctx: Context, rep: Report, number: int, merged: str) -> str | None:
    """The merge commit GitHub names (`merged`, a full object name, as merge_outcome
    returns it) is on origin/main, and joins the base checked and the head checked, with
    the head's tree; the branch is gone. When origin/main does not hold it, nothing on main
    is known to be the merge, so MergeUnknown, and no revert is advised: it would name
    origin/main's last commit in place of the merge (issue #42). Returns the merge commit,
    or None when origin could not be read."""
    remote = landing_remote(ctx)
    command = ["git", "fetch", "origin"] if remote == "origin" else \
        ["git", "fetch", "--", remote, "+refs/heads/*:refs/remotes/origin/*"]
    r = run(command, ctx.repo)
    if r.returncode != 0:
        rep.add("5", "main", "FAIL", f"not checked: `git fetch origin` failed after the merge: "
                f"{r.stderr.strip()}")
        return None
    main = rev_parse(ctx.repo, "refs/remotes/origin/main^{commit}") or ""
    if not isinstance(merged, str) or not FULL_OID.fullmatch(merged) \
            or rev_parse(ctx.repo, f"{merged}^{{commit}}") is None \
            or not git_ok(ctx.repo, "merge-base", "--is-ancestor", merged, main):
        named = f"names {merged[:12]} as its merge commit, which origin/main ({main[:12]}) " \
            "does not hold" if merged else "names no merge commit"
        rep.add("5", "main", "FAIL", f"GitHub says #{number} is merged, but it {named}")
        raise MergeUnknown(f"GitHub says #{number} is merged, but it {named}: look with "
                           f"`gh pr view {number}` and at origin/main before anything else")
    commit = merged
    parents = git(ctx.repo, "rev-list", "--parents", "-n", "1", commit).split()[1:]
    same_tree = rev_parse(ctx.repo, f"{commit}^{{tree}}") == \
        rev_parse(ctx.repo, f"{ctx.sha}^{{tree}}")
    if parents == [ctx.base, ctx.sha] and same_tree:
        rep.add("5", "main", "ok", f"{commit[:12]}, on origin/main: a merge commit of "
                f"{ctx.base[:12]} and {ctx.sha[:12]}, with the tree checked")
    else:
        rep.add("5", "main", "FAIL", f"{commit[:12]}, on origin/main ({main[:12]}), has parents "
                f"{', '.join(p[:12] for p in parents)}, and "
                f"{'the' if same_tree else 'not the'} tree checked")
    gone = not remote_refs(ctx.repo, f"refs/heads/{ctx.branch}", remote=landing_remote(ctx))
    rep.add("5", "branch", "ok" if gone else "note",
            f"{ctx.branch} deleted on origin" if gone else f"{ctx.branch} is still on origin")
    return commit


def api_json(ctx: Context, endpoint: str, *args, missing: bool = False):
    """Read the API strictly. `gh api` takes a full endpoint, not the pr command's -R."""
    try:
        r = run([*ctx.gh, "api", endpoint, *args], ctx.repo)
    except (OSError, UnicodeError) as e:
        raise Refusal(f"could not read GitHub's {endpoint}: {e}") from e
    try:
        answer = json.loads(r.stdout)
    except (ValueError, TypeError):
        answer = None
    if r.returncode:
        absent = (isinstance(answer, dict) and answer.get("status") in (404, "404")) or \
            re.search(r"\bHTTP 404\b", r.stderr)
        if missing and absent:
            return None
        raise Refusal(f"could not read GitHub's {endpoint}: {r.stderr.strip() or r.stdout[:200]}")
    if answer is None:
        raise Refusal(f"GitHub's {endpoint} did not give a readable JSON answer")
    if isinstance(answer, dict) and answer.get("errors"):
        raise Refusal(f"GitHub's {endpoint} reported errors")
    return answer


def api_pages(answer, name: str) -> list:
    """Flatten a paginated, slurped array only after validating every page."""
    if not isinstance(answer, list) or not answer or any(not isinstance(p, list) for p in answer):
        raise Refusal(f"unreadable {name}: expected pages of entries")
    return [entry for page in answer for entry in page]


def queue_enabled(ctx: Context, rep: Report) -> bool:
    """Read main's effective rules, refusing an unreadable rule even after a queue rule."""
    rules = api_pages(api_json(ctx, f"repos/{ctx.github}/rules/branches/main",
                               "--paginate", "--slurp"), "main rules")
    for rule in rules:
        if not isinstance(rule, dict) or not isinstance(rule.get("type"), str) \
                or not rule["type"].strip() or \
                ("parameters" in rule and not isinstance(rule["parameters"], dict)):
            raise Refusal("unreadable main rules: each rule must name its type")
    queued = any(rule["type"] == "merge_queue" for rule in rules)
    rep.add("1", "merge queue", "ok", "required by main's rules" if queued else
            "not required by main's rules")
    return queued


# A pull request that fixes a red main says so in its body, on a line of its own that
# GitHub shows: "Fixes main-red: #12", or "Fixes main-red: #12, #15".
MAIN_RED_FIX = re.compile(r"Fixes main-red: (#[1-9][0-9]*(?:, #[1-9][0-9]*)*)\.?")


def main_red_fix(body: str) -> set[int] | None:
    """The main-red issues a pull request's body declares it fixes, read as GitHub shows
    the body (visible), so that a line in a comment or in code is not one; None when it
    declares none. More than one such line, or one not in the form, refuses."""
    lines = [line.strip() for line in visible(body or "").splitlines()
             if line.strip().startswith("Fixes main-red")]
    if not lines:
        return None
    m = MAIN_RED_FIX.fullmatch(lines[0]) if len(lines) == 1 else None
    numbers = [int(n) for n in re.findall(r"#([0-9]+)", m.group(1))] if m else []
    if not m or len(set(numbers)) != len(numbers):
        raise Refusal("unreadable main-red fix: write one line `Fixes main-red: #<n>`, "
                      "naming each open main-red issue once")
    return set(numbers)


def main_health(ctx: Context, rep: Report, body: str | None = None) -> None:
    """Refuse red or unreadable main: open issues and completed post-merge runs at its tip.
    While main is red, only its fix lands: a pull request whose body (`body`) declares it
    fixes every open main-red issue, and no other (main_red_fix). Its own CI, which the
    gates require to pass, and in queue mode its group's, then check it on main."""
    issues = api_pages(api_json(
        ctx, f"repos/{ctx.github}/issues?state=open&labels=main-red&per_page=100",
        "--paginate", "--slurp"), "main-red issues")
    red = []
    for issue in issues:
        if not isinstance(issue, dict) or type(issue.get("number")) is not int \
                or issue["number"] < 1 or issue.get("state") != "open" \
                or not isinstance(issue.get("labels"), list) \
                or any(not isinstance(label, dict) or not isinstance(label.get("name"), str)
                       or not label["name"].strip() for label in issue["labels"]) \
                or "main-red" not in {label["name"] for label in issue["labels"]} \
                or ("pull_request" in issue and not isinstance(issue["pull_request"], dict)):
            raise Refusal("unreadable main-red issue entry")
        if "pull_request" not in issue:
            red.append(issue["number"])
    workflow = ".github/workflows/post-merge.yml"
    absent = not git(ctx.repo, "ls-tree", ctx.base, "--", workflow).strip()
    pages = api_json(ctx, f"repos/{ctx.github}/actions/workflows/post-merge.yml/runs"
                     f"?branch=main&head_sha={ctx.base}&per_page=100",
                     "--paginate", "--slurp", missing=absent)
    if pages is None:
        red_or_fix(rep, red, None, "no post-merge workflow", body)
        return
    if not isinstance(pages, list) or not pages:
        raise Refusal("unreadable post-merge runs: expected pages")
    completed, seen = [], set()
    total = None
    for page in pages:
        if not isinstance(page, dict) or type(page.get("total_count")) is not int \
                or page["total_count"] < 0 or not isinstance(page.get("workflow_runs"), list):
            raise Refusal("unreadable post-merge runs page")
        if total is not None and page["total_count"] != total:
            raise Refusal("unreadable post-merge runs: the count changed between pages")
        total = page["total_count"]
        for entry in page["workflow_runs"]:
            if not isinstance(entry, dict) or any(type(entry.get(key)) is not int
                    or entry[key] < 1 for key in ("id", "run_number", "run_attempt")) \
                    or entry.get("head_sha") != ctx.base or entry.get("head_branch") != "main" \
                    or entry.get("status") not in ("completed", "queued", "in_progress",
                                                   "waiting", "requested", "pending"):
                raise Refusal("unreadable post-merge run entry")
            if entry["id"] in seen:
                raise Refusal("unreadable post-merge runs: a run appears twice")
            seen.add(entry["id"])
            if entry["status"] == "completed":
                if entry.get("conclusion") not in ("success", "failure", "neutral", "cancelled",
                        "skipped", "timed_out", "action_required", "stale", "startup_failure"):
                    raise Refusal("unreadable post-merge run conclusion")
                completed.append(entry)
            elif entry.get("conclusion") is not None:
                raise Refusal("unreadable unfinished post-merge run conclusion")
    if len(seen) != total:
        raise Refusal("unreadable post-merge runs: the pages do not cover the reported count")
    failed = None
    if completed:
        latest = max(completed, key=lambda entry: (entry["run_number"], entry["run_attempt"]))
        if latest["conclusion"] not in ("success", "neutral", "skipped"):
            failed = (f"post-merge run {latest['id']} at {ctx.base[:12]} "
                      f"concluded {latest['conclusion']}")
        detail = f"latest completed post-merge run {latest['id']} concluded {latest['conclusion']}"
    else:
        detail = "no completed post-merge run at main's tip"
    red_or_fix(rep, red, failed, detail, body)


def red_or_fix(rep: Report, red: list[int], failed: str | None, detail: str,
               body: str | None) -> None:
    """main_health's verdict: green; or red, refused, unless the pull request's body
    declares it fixes exactly the open main-red issues. A failed run with no open issue
    has none to declare: its issue is labelled main-red again first."""
    if not red and failed is None:
        rep.add("1", "main health", "ok", "no main-red issues; " + detail)
        return
    why = "main is red: " + "; ".join(
        (["open main-red issues " + ", ".join(f"#{n}" for n in red)] if red else [])
        + ([failed] if failed else []))
    fixes = main_red_fix(body or "")
    if fixes is None:
        raise Refusal(f"{why}. Only its fix lands: a pull request whose body has the line "
                      "`Fixes main-red: #<n>`, naming every open main-red issue")
    if not red:
        raise Refusal(f"{why}, and no open main-red issue names it for this fix to declare: "
                      "label the failed run's issue main-red again")
    if fixes != set(red):
        raise Refusal(f"{why}; this pull request declares it fixes "
                      + ", ".join(f"#{n}" for n in sorted(fixes))
                      + ", which is not every open main-red issue and no other")
    rep.add("1", "main health", "note", f"{why}; this pull request declares it fixes them, "
            "and lands as their fix, its own CI passing")


def queue_base(ctx: Context, head: str) -> str:
    """A queued head is checked against the newest commit of current main's first-parent
    chain that it contains: the base its pre-flight recorded, origin/main's tip then, and
    the base the queue's judge holds that summary to and runs its train check against
    (check_queue.preflight). So --merge's own checks, its train check and the judge
    compare against one base, even when the head's merge base with main lies off the
    chain (a member merged on its own before its train)."""
    held = set(git(ctx.repo, "rev-list", head).split())
    chain = git(ctx.repo, "rev-list", "--first-parent", ctx.base).split()
    base = next((tip for tip in chain if tip in held), None)
    if base is None or not FULL_OID.fullmatch(base):
        raise Refusal("the queued head contains no commit of origin/main's first-parent chain")
    return base


QUEUE_POLL = 10
# A group's CI can take as long as the queue's status check timeout, 150 minutes
# (WORKFLOW, section 10, "Turning it on"), and a train behind a group that fails waits
# for its own group to be built and run again: twice that, in seconds.
QUEUE_TIMEOUT = 18000


def queue_view(ctx: Context, number: int) -> dict:
    """Read the pull request and its queue entry in one GraphQL snapshot."""
    owner, name = ctx.github.split("/")
    query = """query($owner:String!, $name:String!, $number:Int!) {
      repository(owner:$owner, name:$name) { pullRequest(number:$number) {
        id state headRefOid headRefName baseRefName mergeCommit { oid }
        mergeQueueEntry { id headCommit { oid } }
      } }
    }"""
    answer = api_json(ctx, "graphql", "-f", f"query={query}", "-f", f"owner={owner}",
                      "-f", f"name={name}", "-F", f"number={number}")
    try:
        view = answer["data"]["repository"]["pullRequest"]
        if not isinstance(view, dict) or not isinstance(view.get("id"), str) or not view["id"] \
                or view.get("state") not in PR_STATES or view.get("headRefOid") != ctx.sha \
                or view.get("headRefName") != ctx.branch or view.get("baseRefName") != "main" \
                or "mergeQueueEntry" not in view:
            raise ValueError("missing or changed pull request fields")
        entry = view["mergeQueueEntry"]
        if entry is not None and (not isinstance(entry, dict)
                or not isinstance(entry.get("id"), str) or not entry["id"]):
            raise ValueError("malformed queue entry")
        if entry is not None:
            queue_group(entry)
    except (KeyError, TypeError, ValueError) as e:
        raise Refusal(f"unreadable queue state for #{number}: {e}") from e
    return view


def enqueue(ctx: Context, view: dict) -> dict:
    """Pin the checked head in the enqueue mutation and validate its acknowledgement."""
    query = """mutation($id:ID!, $head:GitObjectID!) {
      enqueuePullRequest(input:{pullRequestId:$id, expectedHeadOid:$head}) {
        mergeQueueEntry { id headCommit { oid } pullRequest { id headRefOid } }
      }
    }"""
    answer = api_json(ctx, "graphql", "-f", f"query={query}", "-f", f"id={view['id']}",
                      "-f", f"head={ctx.sha}")
    try:
        entry = answer["data"]["enqueuePullRequest"]["mergeQueueEntry"]
        if not isinstance(entry["id"], str) or not entry["id"] \
                or entry["pullRequest"]["id"] != view["id"] \
                or entry["pullRequest"]["headRefOid"] != ctx.sha:
            raise ValueError("the acknowledgement does not name the checked head")
        queue_group(entry)
    except (KeyError, TypeError, ValueError) as e:
        raise Refusal(f"unreadable enqueue acknowledgement: {e}") from e
    return entry


def queue_group(entry: dict) -> str | None:
    """Read a queue entry's current group head, which may not have been made yet."""
    commit = entry.get("headCommit")
    if commit is None:
        return None
    if not isinstance(commit, dict) or not isinstance(commit.get("oid"), str) \
            or not FULL_OID.fullmatch(commit["oid"]):
        raise Refusal("unreadable queue group head")
    return commit["oid"]


def queue_checks(ctx: Context, group: str | None) -> str:
    """Include checks of the last observed group, if readable, after its entry is gone."""
    if group is None:
        return "the failing group's checks are not readable"
    try:
        pages = api_json(ctx, f"repos/{ctx.github}/commits/{group}/check-runs?per_page=100",
                         "--paginate", "--slurp")
        if not isinstance(pages, list) or not pages:
            raise ValueError("missing check pages")
        checks = []
        for page in pages:
            if not isinstance(page, dict) or not isinstance(page.get("check_runs"), list):
                raise ValueError("unreadable check page")
            for check in page["check_runs"]:
                if not isinstance(check, dict) or not isinstance(check.get("name"), str) \
                        or check.get("status") not in ("queued", "in_progress", "completed") \
                        or not isinstance(check.get("conclusion"), (str, type(None))):
                    raise ValueError("unreadable check entry")
                checks.append(f"{check['name']}: {check.get('conclusion') or check['status']}")
        return f"group {group[:12]} checks: " + "; ".join(checks) if checks else \
            "the failing group's checks are not readable"
    except Exception:
        return "the failing group's checks are not readable"


def verify_queue_merge(ctx: Context, number: int, view: dict, rep: Report) -> str:
    """The named merge must be on main, with exactly two parents and the checked head second."""
    merged = view.get("mergeCommit")
    oid = merged.get("oid") if isinstance(merged, dict) else None
    if not isinstance(oid, str) or not FULL_OID.fullmatch(oid):
        raise Refusal(f"GitHub names no full merge commit for queued #{number}")
    remote = landing_remote(ctx)
    if remote == "origin":
        git(ctx.repo, "fetch", "origin")
    else:
        git(ctx.repo, "fetch", "--", remote,
            "+refs/heads/*:refs/remotes/origin/*")
    main = rev_parse(ctx.repo, "refs/remotes/origin/main^{commit}")
    if not main or rev_parse(ctx.repo, f"{oid}^{{commit}}") is None \
            or not git_ok(ctx.repo, "merge-base", "--is-ancestor", oid, main):
        raise Refusal(f"origin/main does not hold the merge commit GitHub names for #{number}")
    parents = git(ctx.repo, "rev-list", "--parents", "-n", "1", oid).split()[1:]
    if len(parents) != 2 or parents[1] != ctx.sha:
        raise Refusal(f"queued merge {oid[:12]} does not have the checked head as second parent")
    rep.add("5", "main", "ok", f"{oid[:12]} on origin/main, with {ctx.sha[:12]} as second parent")
    return oid


def queue_main(ctx: Context, number: int, rep: Report, dry_run: bool, test_mode: bool,
               body: str | None) -> int:
    """Enqueue once, then follow a known entry to merge or ejection, with bounded polling.
    `body`, the gates' last read, may declare the pull request a red main's fix."""
    asked = False
    result, code = "refused", 1
    try:
        if dry_run:
            rep.add("4", "enqueue", "skip", f"dry run: would enqueue #{number}, head {ctx.sha}")
            result, code = "passed every gate (dry run, not queued)", 0
        else:
            tip = fetch_base(ctx.repo, ctx.origin, test_mode, rep,
                             remote=landing_remote(ctx))
            main_health(ctx._replace(base=tip), rep, body)
            view = queue_view(ctx, number)
            if view["state"] != "OPEN":
                raise Refusal(f"#{number} is no longer open")
            entry = view["mergeQueueEntry"]
            asked = True
            if entry is None:
                entry = enqueue(ctx, view)
            group = queue_group(entry)
            rep.add("4", "enqueue", "ok", f"#{number} queued with head {ctx.sha}")
            deadline = time.time() + QUEUE_TIMEOUT
            while True:
                view = queue_view(ctx, number)
                if view["state"] == "MERGED":
                    oid = verify_queue_merge(ctx, number, view, rep)
                    result, code = f"merged #{number} as {oid[:12]}", 0
                    break
                if view["state"] == "OPEN" and view["mergeQueueEntry"] is None:
                    detail = queue_checks(ctx, group)
                    rep.add("4", "merge queue", "FAIL", f"#{number} ejected; {detail}")
                    result, code = f"ejected #{number}; {detail}", 1
                    break
                if view["state"] != "OPEN":
                    raise Refusal(f"#{number} is {view['state']}; no queue verdict is known")
                group = queue_group(view["mergeQueueEntry"]) or group
                if time.time() >= deadline:
                    raise Refusal(f"timed out following #{number}")
                time.sleep(QUEUE_POLL)
    except (Exception, KeyboardInterrupt) as e:
        if asked:
            result, code = f"queued; verdict not followed ({e})", 3
            print(f"\nQueued; verdict not followed: {e}")
        else:
            result, code = f"refused ({e})", 1
            print(f"\nREFUSED: {e}")
    summary(rep, "queue dry run" if dry_run else "queue", ctx.sha, ctx.base, result, "")
    return code


# --------------------------------------------------------------------------------------
# Step 6: the summary and the log outside the repository


def summary(rep: Report, mode: str, sha: str, base: str, result: str, ci: str) -> None:
    total = time.time() - rep.started
    print(f"\nSummary: {mode} of {sha[:12] or '?'} against origin/main {base[:12] or '?'}: "
          f"{result}" + (f"; CI {ci}" if ci else "") + f" ({total:.0f} s)")
    timed = [s for s in rep.steps if s.outcome in ("ok", "FAIL", "skip")]
    width = max((len(s.name) for s in timed), default=10)
    for s in timed:
        took = f"{s.seconds:8.1f} s" if s.seconds is not None else " " * 10
        print(f"  {s.stage}  {s.outcome:4}  {s.name:<{width}}  {took}")
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    steps = "; ".join(f"{s.name}={s.outcome}" + (f" {s.seconds:.1f}s" if s.seconds else "")
                      for s in timed)
    line = (f"{stamp} {mode} {sha[:12] or '?'} against {base[:12] or '?'}: {result}"
            + (f"; CI {ci}" if ci else "") + f"; {total:.0f}s; {steps}\n")
    path = log_path()
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a") as f:
            f.write(line)
        print(f"Logged to {path}")
    except OSError as e:
        print(f"Could not write the log {path}: {e}")


# --------------------------------------------------------------------------------------
# The three ways in: the pre-flight, the merge, and the hook's scan


def _terminate(signum, frame):
    raise KeyboardInterrupt(f"signal {signum}")


def logs_dir(sha: str) -> Path:
    stamp = datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
    path = log_path().parent / "logs" / f"{stamp}-{sha[:12]}"
    path.mkdir(parents=True, exist_ok=True)
    return path


def preflight_main(repo: Path, args) -> int:
    global CACHE, SANDBOX
    mode = "dry run" if args.dry_run else "push"
    print(f"safe_push: {mode} of {args.commit} from {repo}"
          + (f", for the branch {args.branch}" if args.branch else ""), flush=True)
    rep = Report()
    sha = base = ""
    result, ci, code = "refused", "", 1
    pushed, pr = False, None
    held = None         # --land: what the merge takes from this run, once CI is green
    noted: list[str] = []   # --land: notes for the security review, which hold the merge
    try:
        ctx = preconditions(repo, args.commit, args.branch, args.dry_run, args.test_mode, rep,
                            title=args.title)
        sha, base = ctx.sha, ctx.base
        labels = check_kind_label(ctx, args, rep) if ctx.branch else set()
        risk = risk_class(ctx.repo, ctx.base, ctx.sha, labels)
        # After the class, which serves the cache (R3 to R5 alone), and after risk_class
        # runs origin/main's risk.py, outside run(); before any of the commit's code runs.
        if args.main_checks_cache:
            if risk.cls not in LOW_CLASSES:
                count_markers(ctx.repo, ctx.base)
            open_cache(rep, risk, train=(ctx.branch or "").startswith("train/"))
        logs = logs_dir(sha)
        body_text = body_input(args)
        pre = check_commit(ctx, rep, logs, args.test_mode, risk,
                           train_body=train_input(ctx, body_text))
        record = make_record(ctx, pre, rep, full=not args.test_mode, risk=risk)
        # For --land, the record as made, before it is saved: nothing done to the saved
        # one, or to its file, reaches this copy.
        kept = copy.deepcopy(record) if args.land else None
        save_record(record)
        if args.dry_run:
            rep.heading("5. Push")
            where = f"refs/heads/{ctx.branch}, and open or update its pull request" \
                if ctx.branch else "nowhere: no --branch given"
            if ctx.branch:
                body = fill_body(ctx, pre, record, body_text) \
                    if body_text is not None else generated_body(ctx, pre, record)
                check_body(body)
                (logs / "pr-body.md").write_text(body)
                print(f"  the body it would post: {logs / 'pr-body.md'}")
            rep.add("5", "git push", "skip", f"dry run: would push {sha[:12]} to {where}")
            result, code = "passed every check (dry run, not pushed)", 0
        else:
            # The pull request is settled, its body scanned, before anything is public.
            plan = plan_pr(ctx, pre, record, args, body_text)
            fresh = push_branch(ctx, rep)
            pushed = True       # from here on, a refusal or an interruption is exit 3
            result = f"pushed to {ctx.branch}"
            if fresh:
                verify_push(ctx, rep)
            pr = open_pr(ctx, plan, args, rep, logs)
            result = f"pushed to {ctx.branch}; pull request #{pr.number} " \
                     f"{'opened' if pr.created else 'updated'}"
            ci = watch_checks(ctx, pr, rep)
            if ci == "success" and not rep.failed():
                code = 0
                # The body is final at the push, and the merge would follow at once: a note
                # that origin/main's checks fail on the head, which WORKFLOW sends to the
                # security review, would be read by no one first. So it holds the merge.
                noted = review_notes(rep) if args.land else []
                if args.land and not noted:
                    held = Held(ctx.sha, ctx.base, kept, CACHE_HIT, ctx.origin)
            else:
                code = 3
                print("\nCI did not pass for the pull request. Nothing is merged, and main is "
                      f"unchanged: fix {ctx.branch}, then run the pre-flight again.")
    except NothingToPush as e:
        sha = base = str(e)
        result, code = "nothing to push", 0
        print(f"\nNothing to push: origin/main is already {sha[:12]}.")
    except Refusal as e:
        if pushed:
            result, code = f"pushed; CI not followed ({e})", 3
            print(f"\nPushed; CI not followed: {e}")
        else:
            result = f"refused ({e})"
            print(f"\nREFUSED: {e}")
    except KeyboardInterrupt as e:
        if pushed:
            result, code = f"pushed; CI not followed (interrupted: {e or 'Ctrl-C'})", 3
            print(f"\nPushed; CI not followed: interrupted ({e or 'Ctrl-C'})."
                  + (f" Follow it with `gh pr checks {pr.number} --watch`." if pr else
                     " Run the pre-flight again to open the pull request."))
        else:
            result = f"interrupted ({e or 'Ctrl-C'})"
            print(f"\nInterrupted: {result}. The temporary worktrees are removed.")
            code = 1
    except Exception as e:      # after the push, a failure to follow CI is not a refusal
        if not pushed:
            raise
        result, code = f"pushed; CI not followed ({type(e).__name__}: {e})", 3
        print(f"\nPushed; CI not followed: {type(e).__name__}: {e}")
    if held is None and not noted:
        summary(rep, mode, sha, base, result, ci)
        return code
    # --land, CI green: from the push's summary on, an interruption or a crash is exit 3,
    # never 1, "refused", nor a signal's death; once the merge has started, it may have
    # merged.
    started = False
    try:
        summary(rep, mode, sha, base, result, ci)
        if noted:
            print(f"\nCI is green, but the pre-flight noted origin/main's checks failing "
                  f"on the head ({', '.join(noted)}), for the security review, which must "
                  "read the notes before a separate merge: nothing is merged. Record that "
                  f"review in #{pr.number}, then run `git safe-push --merge {pr.number}`.")
            return 3
        # The merge runs as a separate --merge runs, which takes no --main-checks-cache: so
        # its checks, when they run, run uncached and without the cache's sandbox.
        CACHE = SANDBOX = None
        started = True
        code = merge_main(repo, pr.number, False, args.test_mode, held=held)
    except (Exception, KeyboardInterrupt) as e:
        why = f"interrupted ({e or 'Ctrl-C'})" if isinstance(e, KeyboardInterrupt) \
            else f"{type(e).__name__}: {e}"
        if started:
            print(f"\nPushed; the merge stopped: {why}. It may have merged: look with "
                  f"`gh pr view {pr.number}` before anything else.")
        else:
            then = f"the security review reads {', '.join(noted)} first, then" if noted \
                else "run"
            print(f"\nPushed, CI green; stopped before the merge: {why}. Nothing is "
                  f"merged: {then} `git safe-push --merge {pr.number}`.")
        return 3
    return 3 if code == 1 else code     # refused, nothing merged; but the branch was pushed


def merge_main(repo: Path, number: int, dry_run: bool, test_mode: bool,
               held: Held | None = None) -> int:
    """--merge <number>; or, with `held`, the merge --land goes on to in the same process,
    which takes the pre-flight's record from memory (held_record), never from a file, and
    merges only the commit it pushed (never a dry run)."""
    mode = "merge dry run" if dry_run else "merge"
    print(f"safe_push: {mode} of pull request #{number} from {repo}", flush=True)
    rep = Report()
    sha = base = ""
    result, code = "refused", 1
    # "asked" once gh is asked to merge, "merged" once GitHub says it has (gh's exit
    # status alone is never believed: issue #42): from "asked" on, the run says nothing
    # merged only when GitHub says so (NotMerged), and success only once origin/main holds
    # the merge commit GitHub names (MergeUnknown, when it does not).
    merging = ""
    kept = held.record if held is not None else None
    try:
        # --land's merge refuses a changed origin or a moved main, and never hands over:
        # re-run with the push's arguments, origin/main's harness would run the whole push
        # again.
        ctx, view = merge_preconditions(repo, number, test_mode, rep, held=held)
        sha, base = ctx.sha, ctx.base
        # --land merges only the commit it pushed: never re-run on another.
        if held is not None and ctx.sha != held.sha:
            raise Refusal(f"the head of #{number} moved from {held.sha[:12]} to "
                          f"{ctx.sha[:12]} during CI; nothing is merged: run the pre-flight "
                          "on the new head")
        try:
            labels = pr_labels(view.get("labels"))
        except ValueError:
            labels = None       # the gates refuse it; the class is R5 meanwhile
        # The class, recomputed now by origin/main's risk.py for this head against this
        # base: a record that left step 4 to CI stands in for it only while that is still
        # R0 to R2 (checks_record).
        risk = risk_class(ctx.repo, ctx.base, ctx.sha, labels)
        dropped = ""
        if held is None:
            earlier = load_record(ctx.sha, ctx.base)
        else:
            earlier, dropped = held_record(held, ctx, risk)
        checked = checks_record(earlier, test_mode, risk)
        release_needs_full_record(ctx, number, labels, checked, earlier, test_mode, rep)
        # The record is a file the checks it ran could have written. When the head
        # changes the checks themselves, CI runs the head's copies, never origin/main's,
        # so only the pre-flight can find that origin/main's checks fail on it: the full
        # checks run again here rather than trust the record.
        # So too for a head that changes any protected path: CI runs the head's own
        # workflow (.github/) as well as its own checks.
        # A record kept in memory by this same run (--land) was never a file, so nothing
        # the head's code ran could have written it: the reason does not hold for it.
        if checked is not None and checked is not kept \
                and any(under(p, CHECK_INPUTS) or is_protected(p)
                        for _, p in changed_files(repo, ctx.base, ctx.sha)):
            rep.add("3", "full checks record", "note", "the head changes the checks or a "
                    "protected path, so the full checks run again, not the record of the "
                    "pre-flight")
            checked = None
        if checked is None:
            view = gates(ctx, number, rep)   # before long checks, so a draft fails at once
        rep.heading("3. The pre-flight of the head")
        # The secret scan and the guards run on the head every time: the record is a
        # local file, and the pre-flight ran the commit's own code (its checks, and Lean
        # at elaboration), which could have written it. Only the full checks, which CI
        # runs as well, may be taken from it.
        if dropped:
            rep.add("3", "pre-flight", "note", dropped)
        elif checked is not None and checked is kept and checked.get("short"):
            rep.add("3", "pre-flight", "ok", f"{ctx.sha[:12]} checked against origin/main "
                    f"{ctx.base[:12]} in this run's pre-flight, its record kept in memory, "
                    f"never read from a file, its class {checked.get('class')} then and "
                    f"{risk.cls} now: the secret scan and the guards run again; the full "
                    "checks stay with CI, as for any change of R0 to R2")
        elif checked is not None and checked is kept:
            rep.add("3", "pre-flight", "ok", f"{ctx.sha[:12]} checked against origin/main "
                    f"{ctx.base[:12]} in this run's pre-flight, its record kept in memory, "
                    "never read from a file: the secret scan and the guards run again; the "
                    "full checks are not repeated")
        elif earlier is None:
            rep.add("3", "pre-flight", "note", f"none of {ctx.sha[:12]} against origin/main "
                    f"{ctx.base[:12]}: it runs now")
        elif checked is None:
            again = "they run now" if risk.cls not in LOW_CLASSES else \
                f"it runs again now, and leaves them to CI for the class {risk.cls}"
            rep.add("3", "pre-flight", "note", f"the record of {ctx.sha[:12]} against "
                    f"origin/main {ctx.base[:12]} is not of the full checks by origin/main's "
                    f"harness: {again}")
        elif checked.get("short"):
            rep.add("3", "pre-flight", "ok", f"{ctx.sha[:12]} checked against origin/main "
                    f"{ctx.base[:12]} ({checked.get('time')}), its class "
                    f"{checked.get('class')} then and {risk.cls} now: the secret scan and "
                    "the guards run again; the full checks stay with CI, as for any change "
                    "of R0 to R2")
        else:
            rep.add("3", "pre-flight", "ok", f"{ctx.sha[:12]} checked against origin/main "
                    f"{ctx.base[:12]} ({checked.get('time')}): the secret scan and the guards "
                    "run again; the full checks are not repeated")
        logs = logs_dir(ctx.sha)
        train_body = merge_train_input(ctx, view)
        revalidate = None if held is None else \
            lambda: land_state_unchanged(repo, held.origin, ctx.trusted_harness)
        pre = check_commit(ctx, rep, logs, test_mode, risk, checked=checked,
                           train_body=train_body, trusted_harness=ctx.trusted_harness
                           if held is not None else None, revalidate=revalidate)
        record = make_record(ctx, pre, rep, full=not test_mode and checked is None,
                             risk=risk, checked=checked)
        save_record(record)
        view = gates(ctx, number, rep, record)
        if merge_train_input(ctx, view) != train_body:
            raise Refusal("the train's body changed during the checks: run --merge again")
        labels = pr_labels(view.get("labels"))
        # A release label given after the class was read: the record must still be full.
        release_needs_full_record(ctx, number, labels, record, record, test_mode, rep)
        # The body must already be of this head: --merge never writes it.
        body_view = gh_json(ctx, "pr", "view", str(number), "--json", "body")
        if merge_train_input(ctx, body_view) != train_body:
            raise Refusal("the train's body changed during the checks: run --merge again")
        body = body_view.get("body") or ""
        template = show(ctx.repo, ctx.harness_sha or ctx.base, TEMPLATE) \
            or show(ctx.repo, ctx.sha, TEMPLATE)
        if unfinished_section(body, template) != unfinished_section(view.get("body") or "",
                                                                    template):
            raise Refusal(f"#{number}'s Unfinished work changed after the gates read it: "
                          "run --merge again")
        m = BLOCK.search(body)
        new = refreshed(body, describe(ctx, pre))
        if not block_current(ctx, m, record):
            new = put_block(new, preflight_block(ctx.sha, ctx.base, record))
        if unfinished_section(new, template) != unfinished_section(body, template):
            raise Refusal(f"refreshing #{number}'s parts would change its Unfinished work: "
                          "put safe_push's markers back where the template has them")
        # A body edited in GitHub's page has CRLF line ends, and the parts are written
        # afresh with LF: the parts are up to date when they differ by line ends alone.
        if new.replace("\r\n", "\n") != body.replace("\r\n", "\n"):
            rep.add("3", "body", "FAIL", "its pre-flight summary or the parts safe_push "
                    f"wrote are out of date: run `git safe-push --branch {ctx.branch}` to "
                    "refresh them, then run --merge again")
        if rep.failed():
            raise Refusal("the pull request's body could not be brought up to date")
        try:
            refreshed_labels = read_pr_labels(ctx, number)
        except ValueError as e:
            raise Refusal(f"#{number}: {e}") from None
        if refreshed_labels != labels:
            raise Refusal(f"#{number}'s labels changed after the gates read them "
                          f"({', '.join(sorted(labels)) or 'none'} to "
                          f"{', '.join(sorted(refreshed_labels)) or 'none'}): run --merge again")
        current_view = gates(ctx, number, rep, record)
        if merge_train_input(ctx, current_view) != train_body:
            raise Refusal("the train's body changed during the checks: run --merge again")
        current_labels = pr_labels(current_view.get("labels"))
        if current_labels != labels:
            raise Refusal(f"#{number}'s labels changed after the gates read them "
                          f"({', '.join(sorted(labels)) or 'none'} to "
                          f"{', '.join(sorted(current_labels)) or 'none'}): run --merge again")
        view = current_view
        labels = current_labels
        kind = next((k for k in KIND_LABELS if k in labels), None)
        if revalidate is not None:
            revalidate()
        rep.heading("4. Merge")
        if ctx.queue:
            return queue_main(ctx, number, rep, dry_run, test_mode, view.get("body"))
        if dry_run:
            rep.add("4", "gh pr merge", "skip", f"dry run: would merge #{number} "
                    f"({ctx.sha[:12]}) with a merge commit, and delete {ctx.branch}")
            result, code = "passed every gate (dry run, not merged)", 0
        else:
            main_unmoved(ctx)
            main_health(ctx, rep, view.get("body"))
            merging, started = "asked", time.time()
            r = merge(ctx, number, view)
            oid = merge_outcome(ctx, number, rep, r, started)
            merging = "merged"
            main_sha = verify_merge(ctx, rep, number, oid)
            code = 0 if not rep.failed() else 3
            if main_sha is None:
                result = f"merged #{number}; main not checked"
                print(f"\nMerged #{number}, but main could not be checked: `git fetch origin` "
                      "failed. Look at origin/main before anything else.")
            else:
                result = f"merged #{number} as {main_sha[:12]}"
                if code:
                    print("\nMerged, but main is not what was checked.\n"
                          + revert_advice(ctx._replace(sha=main_sha), kind))
    except Refusal as e:
        if isinstance(e, MergeUnknown) or (merging == "asked" and not isinstance(e, NotMerged)):
            result, code = f"merge state unknown ({e})", 3
            print(f"\nThe merge state is unknown: {e}" if isinstance(e, MergeUnknown)
                  else f"\nThe merge may have happened: {e}")
        else:
            done = merging == "merged"
            result, code = (f"merged, then {e}", 3) if done else (f"refused ({e})", 1)
            print(f"\nREFUSED: {e}")
    except KeyboardInterrupt as e:
        if merging == "asked":
            result, code = f"merge state unknown (interrupted: {e or 'Ctrl-C'})", 3
            print(f"\nInterrupted once `gh pr merge` was run: the merge may have happened. "
                  f"Look with `gh pr view {number}` before anything else.")
        else:
            done = merging == "merged"
            result = f"interrupted ({e or 'Ctrl-C'})" + ("; merged" if done else "")
            code = 3 if done else 1
            print(f"\nInterrupted: {result}.")
    summary(rep, mode, sha, base, result, "")
    return code


def scan_push_main(repo: Path, local: str, remote: str, ref: str) -> int:
    """The pre-push hook's scan of a push to any branch, or of a tag the owner allowed:
    the commits it carries that the branch on origin, or else origin/main, lacks, with
    origin/main's allow-list; an annotated tag's message; and the ref's own name, which
    is published with it."""
    print(f"pre-push: the secret scan of the push to {ref}", flush=True)
    kind = "the tag name" if ref.startswith("refs/tags/") else "the branch name"
    named = scan_text(kind, None, ref.removeprefix("refs/heads/").removeprefix("refs/tags/"))
    if named:
        print(f"pre-push: refusing the push to {ref}: its name holds what the secret scan "
              "refuses: " + "; ".join(f.shown() for f in named), file=sys.stderr)
        return 1
    rep = Report()
    main = rev_parse(repo, "refs/remotes/origin/main^{commit}")
    tag_message: list[Finding] = []
    if git(repo, "cat-file", "-t", local, check=False).strip() == "tag":
        # An annotated tag: its message is published with it, and its target is scanned.
        body = git(repo, "cat-file", "tag", local, check=False).split("\n\n", 1)
        tag_message = scan_block(f"tag {ref.removeprefix('refs/tags/')} message",
                                 list(enumerate((body[1] if len(body) > 1 else "")
                                                .splitlines(), 1)))
    commit = rev_parse(repo, f"{local}^{{commit}}")
    if commit is None:
        print(f"pre-push: refusing the push to {ref}: {local[:12]} is not a commit, nor a tag "
              "of one", file=sys.stderr)
        return 1
    local = commit
    if tag_message:
        print(f"pre-push: refusing the push to {ref}: its message holds what the secret scan "
              "refuses: " + "; ".join(f.shown() for f in tag_message), file=sys.stderr)
        return 1
    base = None
    if remote.strip("0") and rev_parse(repo, f"{remote}^{{commit}}"):
        base = remote if git_ok(repo, "merge-base", "--is-ancestor", remote, local) else \
            (git(repo, "merge-base", remote, local, check=False).strip() or None)
    if base is None and main:
        base = git(repo, "merge-base", main, local, check=False).strip() or None
    try:
        secret_scan(repo, base, local, rep, allow_rev=main)
    except Refusal as e:
        print(f"pre-push: refusing the push to {ref}: {e}", file=sys.stderr)
        return 1
    return 0


REFUSE_DIRECT = """REFUSED: safe_push.py no longer pushes to main: main changes only by a pull
request's merge commit (docs/WORKFLOW.md, "Landing work: pull requests"). Open one with
the pre-flight, and merge it when its gates pass:

    git safe-push --branch <name> --label <kind> [--title T] [--body-file F] [--ready]
                  [--land]
    git safe-push --merge <pr-number>

or check the commit alone, pushing nothing: git safe-push --dry-run
(`git safe-push` runs origin/main's copy of this script: sh scripts/install_hooks.sh)"""

# The variables that place a repository, its work tree, its index or its objects: git's own
# `git rev-parse --local-env-vars`, less the `-c` settings it passes on to a submodule too
# and the two that choose whether replacement refs apply, with the namespace and the
# bounds of discovery. main() drops them once they have found the repository.
GIT_LOCATION = ("GIT_DIR", "GIT_WORK_TREE", "GIT_IMPLICIT_WORK_TREE", "GIT_INDEX_FILE",
                "GIT_COMMON_DIR", "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES",
                "GIT_GRAFT_FILE", "GIT_SHALLOW_FILE", "GIT_CONFIG", "GIT_PREFIX",
                "GIT_NAMESPACE", "GIT_CEILING_DIRECTORIES", "GIT_DISCOVERY_ACROSS_FILESYSTEM")


def main(argv=None) -> int:
    global ARGV, CI_POLL, CI_APPEAR_TIMEOUT
    ARGV = list(sys.argv[1:] if argv is None else argv)
    if sys.version_info < (3, 11):
        print(f"safe_push needs Python 3.11 or later (tomllib); this is {sys.version.split()[0]}"
              f" at {sys.executable}", file=sys.stderr)
        return 2
    parser = argparse.ArgumentParser(
        description="The pre-flight of a pull request (--branch), and its merge (--merge).")
    parser.add_argument("--branch", help="push the commit to this branch, and open or update "
                        "its pull request onto main")
    parser.add_argument("--title", help="the pull request's title (default: the commit's subject)")
    parser.add_argument("--body-file", help="the pull request's body (default: generated from "
                        f"{TEMPLATE})")
    parser.add_argument("--ready", action="store_true", help="open the pull request ready for "
                        "review, or mark the open one ready (a new one is otherwise a draft)")
    parser.add_argument("--land", action="store_true", help="with --branch and --ready, the "
                        "body final at the push: once CI is green, merge the pull request in "
                        "the same run, as --merge would. Refused: a head that is not the "
                        "commit pushed, origin's URL changed or origin/main moved during "
                        "CI, a copy of the harness on disk that no longer matches "
                        "origin/main's. Held for the security review when the pre-flight "
                        "noted origin/main's checks failing. Else the pre-flight's record, "
                        "kept in memory (never read from a file), stands in for step 4 "
                        "while no main-checks cache hit served origin/main's pass and "
                        "checks_record accepts it")
    parser.add_argument("--label", action="append", default=[], choices=sorted(LABELS),
                        help="a label for the pull request (repeatable); one names its kind, "
                        f"{', '.join(KIND_LABELS)}, unless the open one has it")
    parser.add_argument("--merge", type=int, metavar="PR", help="merge this pull request, if "
                        "its gates pass")
    parser.add_argument("--commit", default="HEAD", help="the commit to check (default HEAD)")
    parser.add_argument("--dry-run", action="store_true",
                        help="everything but the push, the pull request and the merge")
    parser.add_argument("--main-checks-cache", action="store_true",
                        help="the pre-flight only, for a change of R3 to R5, whose step 4 "
                        "runs in full, not on a train/* branch, whose train check runs in "
                        "the harness's own process: reuse origin/main's pass of the full "
                        "checks from ~/.cache/stoicheia/main-checks/ when an earlier run "
                        "checked the same trees with the same harness, toolchain and "
                        "environment, every command the run starts then running under "
                        "macOS's sandbox-exec, which stops it writing there (no sandbox, "
                        "no cache). The sandbox does not stop a run without the flag, nor "
                        "what a flagged run's code leaves for a later command or run to "
                        "load before its sandbox starts. Only the runs that land a train pass "
                        "it (the coordinator ruled): the coordinator's dry run of the "
                        "train and its push")
    # The pre-push hook's entry point: the secret scan of one ref's push.
    parser.add_argument("--scan-push", nargs=3, metavar=("LOCAL", "REMOTE", "REF"),
                        help=argparse.SUPPRESS)
    # Used ONLY by scripts/test_safe_push.py: skips step 4, works only against a local
    # origin, never GitHub, and calls the gh stand-in STOICHEIA_TEST_GH names.
    parser.add_argument("--_test-skip-checks", dest="test_mode", action="store_true",
                        help=argparse.SUPPRESS)
    args = parser.parse_args(ARGV)
    if args.merge is not None and (args.branch or args.title or args.body_file or args.ready
                                   or args.label or args.commit != "HEAD"
                                   or args.main_checks_cache):
        parser.error("--merge takes only --dry-run")
    if not args.branch and (args.title or args.body_file or args.ready or args.label):
        parser.error("--title, --body-file, --ready and --label go with --branch")
    if args.land and (args.merge is not None or args.dry_run):
        parser.error("--land pushes and merges in one run: it takes neither --merge nor "
                     "--dry-run")
    if args.land and not (args.branch and args.ready):
        parser.error("--land needs --branch and --ready: nothing comes between the push and "
                     "the merge, so the pull request must be ready")
    if args.body_file and not Path(args.body_file).is_file():
        parser.error(f"--body-file {args.body_file}: no such file")
    if args.test_mode:
        # The tests' stand-in for gh answers at once: the waits for CI shortened.
        CI_POLL = float(os.environ.get("STOICHEIA_TEST_CI_POLL", CI_POLL))
        CI_APPEAR_TIMEOUT = float(os.environ.get("STOICHEIA_TEST_CI_APPEAR", CI_APPEAR_TIMEOUT))

    original_cwd = Path.cwd()
    if args.scan_push:
        # The scan reads the repository Git hands the hook, never its work tree, so it runs
        # as on origin/main, before the location check below: Git hands a hook a relative
        # GIT_WORK_TREE unchanged (#186).
        r = run(["git", "rev-parse", "--show-toplevel"], original_cwd)
        if r.returncode != 0:
            print("safe_push: run it inside the repository", file=sys.stderr)
            return 2
        return scan_push_main(Path(r.stdout.strip()), *args.scan_push)
    # #186, a linked worktree's GIT_DIR: a shell alias run from one, as `git safe-push`
    # is, sets GIT_DIR (and GIT_PREFIX). Left set, it would point every git command in the
    # fresh worktrees at the caller's index and HEAD, and check_paths.py would refuse to
    # run. Every git call here names its directory, so the variables go, once they have
    # found the repository; and it must be the one git finds from there without them.
    def located(env=None, options=()) -> tuple[Path, Path] | None:
        r = run(["git", *options, "rev-parse", "--show-toplevel", "--absolute-git-dir"],
                original_cwd, env=env)
        lines = r.stdout.splitlines() if r.returncode == 0 else []
        if len(lines) != 2 or not all(line.strip() for line in lines):
            return None
        return Path(lines[0]).resolve(), Path(lines[1]).resolve()

    discovery_env = os.environ.copy()
    for name in GIT_LOCATION:
        discovery_env.pop(name, None)
    expected = located(discovery_env)
    # run() gives no command the caller's GIT_DIR or GIT_WORK_TREE (#357), so this read
    # passes them as git's own options, which git reads as it reads the variables, to see
    # the repository they name; the bounds of discovery reach it as they are.
    options = [f"{option}={os.environ[name]}" for name, option in
               (("GIT_DIR", "--git-dir"), ("GIT_WORK_TREE", "--work-tree"))
               if name in os.environ]
    active = located(options=options)
    if expected is None:
        print("safe_push: cannot independently find the repository from the current "
              "directory with Git location variables unset", file=sys.stderr)
        return 2
    if active is None:
        print("safe_push: cannot read the repository selected by Git location variables",
              file=sys.stderr)
        return 2
    if active != expected:
        print(f"safe_push: GIT_DIR, GIT_WORK_TREE or another such variable names a "
              f"repository other than the one git finds from {original_cwd}: run it from "
              "inside the checkout, with them unset", file=sys.stderr)
        return 2
    for name in GIT_LOCATION:
        os.environ.pop(name, None)
    if located() != expected:
        print("safe_push: the repository changed after Git location variables were unset",
              file=sys.stderr)
        return 2
    repo = expected[0]
    signal.signal(signal.SIGTERM, _terminate)
    signal.signal(signal.SIGHUP, _terminate)
    if args.merge is not None:
        return merge_main(repo, args.merge, args.dry_run, args.test_mode)
    if not args.branch and not args.dry_run:
        print(REFUSE_DIRECT)
        return 1
    return preflight_main(repo, args)


if __name__ == "__main__":
    sys.exit(main())
