#!/usr/bin/env python3
"""Check a train's members, merge trees, evidence and declared changes.

    python3 scripts/check_train.py --base <rev> --head <rev> --body-file <path>

Exit 0 means pass, 1 a refused train, and 2 an unreadable input. The check reads
committed trees; merge-tree writes temporary tree objects, never a checkout, and reads
merge attributes from the base, never from the checkout or the train, so a member's
.gitattributes cannot turn a resolved conflict into an automatic merge. Python 3.11 or
later, the standard library and Git 2.42 or later (merge-tree --write-tree came in 2.38,
--attr-source in 2.42); an older Git makes every train unreadable.
"""

from __future__ import annotations

import argparse
import html
import re
import sys
import unicodedata
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from safe_push import (
    CHECK_INPUTS, DECISIONS, GENERATED, GENERATED_REGIONS, IGNORABLE, SECTION, Refusal,
    changed_files, generated_parts, git,
    is_protected, judged_files, pinned, run, sections, shown, under, visible, written,
)

OID = re.compile(r"[0-9a-f]{40}")
HEAD = re.compile(r"[0-9a-f]{12,40}")
PASSED = re.compile(r"passed at ([0-9a-f]{12,40})(?:[ \t]+.*)?")
FIELDS = ("branch", "head", "code_review", "security_review", "no_mistakes")
# A review cell that is only a placeholder, as a whole, is no review's evidence; a finding
# that begins "To do so" or "Later commits" is not one. (/no-mistakes has its own two
# forms, "passed at" and "not run:", read below.)
PLACEHOLDER = re.compile(
    r"(?:pending|waiting|awaiting(?: (?:review|the review))?|(?:still )?to come|to ?do|"
    r"tbd|tbc|wip|queued|skipped|later|soon|in progress|n/?a|none|nothing|-+|\?+|"
    r"not (?:yet )?(?:run|done|started|reviewed)(?: yet)?|will run after (?:the )?merge)")
# Words that say a review is absent, incomplete or still to come, which a review cell may
# not hold anywhere, beside the member's commit too: in any case, with any separators
# between words, through character references, compatibility forms and invisible marks,
# and in each of the cell's readings (_readings, and _kept), so that HTML tags, emphasis,
# code, strikethrough or a link inside a word ("w<i></i>ill", "w*i*ll", "pen**d**ing",
# "pen[d](#x)ing") cannot hide it from all of them: one reading or another reads it
# whole. They are a second layer,
# under the verdict that must stand beside the commit (CLAUSE), since a rule read from
# prose cannot list every way of saying that a review is not done. "To do" counts but
# not "to do so", "later" where it says when, not which ("Later commits" pass), "yet"
# but not "yet exist" ("checks/ does not yet exist" passes), "unread" after "still",
# "is" and their like ("the records were unread" passes), "after the merge" but not
# "after the merge of main", and a question mark unless a name and "=" follow it, as in
# a link's query ("?pr=2"). Each repeated part is followed by a character it cannot take, so no
# match backtracks over more than one run of separators.
LATER_WHEN = ("at", "on", "in", "by", "today", "tonight", "tomorrow", "this", "next",
              "when", "once", "after", "with", "for", "if", "and", "or", "but")
PLACEHOLDER_WORD = re.compile(r"\b(?:" + "|".join((
    *(r"[\W_]*".join(phrase.split()) for phrase in (
        "pending", "tbd", "tbc", "tba", "wip", "will", "to come", "not needed",
        "outstanding", "in progress", "under way", "underway", "ongoing", "awaiting",
        "waiting", "so far", "still to", "not started", "not finished", "not reviewed",
        "unreviewed", "preliminary", "provisional", "continues", "continuing", "resumes",
        "tomorrow", "next week", "for now", "still running", "half done",
        "in principle")),
    r"n(?:[^\w/]|_)*/(?:[^\w/]|_)*a",
    r"to[\W_]*do(?![\W_]*so\b)",
    r"to[\W_]*follow(?![\W_]*up\b)",
    r"to[\W_]*be[\W_]*(?:added|given|reported|reviewed|read|run|completed|finished|"
    r"confirmed|decided|determined|continued)",
    r"yet(?![\W_]*exists?\b)",
    r"(?:still|is|are|remains?|stays?|left|as)[\W_]+unread",
    r"after[\W_]*(?:the[\W_]*)?merge(?![\W_]*(?:of|with)\b)",
    r"later(?=\s*(?:$|[.,;:!?)\]]|(?:" + "|".join(LATER_WHEN) + r")\b))",
)) + r")\b|\?(?![\w-]+=)")
# Words that also describe other work ("the deferred hardening is filed as #221", "a
# partial switch", "a card to be done before the queue", "#116's interim texts") refuse
# in a phrase that names the review: "the full review follows", "PASS (review
# deferred)", "interim verdict". A phrase ends at a comma, colon, semicolon, bracket,
# sentence end, question mark, quotation mark or dash.
SUBJECT = re.compile(
    r"\b(?:reviews?|reviewed|readings?|verdicts?|findings?|rest|remainder)\b")
UNFINISHED = re.compile(
    r"\b(?:follows|deferred|incomplete|unfinished|partial(?:ly)?|partly|in[\W_]+part|"
    r"interim|not[\W_]+(?:yet|done|run|complete|completed|finished)|"
    r"to[\W_]+be[\W_]+done)\b")
PHRASE = re.compile("[,:;()\\[\\]{}.!?\"\N{LEFT DOUBLE QUOTATION MARK}"
                    "\N{RIGHT DOUBLE QUOTATION MARK}\N{EN DASH}\N{EM DASH}]|\\s-+\\s")
# A completed review's verdict, which a review cell must give in the clause that names
# the commit it reviewed (CLAUSE), in each of its three readings: pass, passes or passed;
# approve, approves or approved; fixed, resolved or stamped; "found no", "found nothing",
# "skipped nothing", "nothing blocking" or "nothing found"; and "no findings" or a number
# of findings ("one finding", "2 material findings"), "defect" standing for "finding".
# On /security-review, "not required" stands too. A verdict stands only as one: none
# after one of the NEGATIONS among the three words before it in its phrase ("not fully
# passed", "may have passed", "almost passed"), none straight before an UNFINISHED word
# ("passed (partial)"), and "pass" none as a noun, after one of the PASS_NOUN words ("a
# first pass") or "passes" after a number.
COUNT = r"(?:\d+|one|two|three|four|five|six|seven|eight|nine|ten|eleven|twelve)"
KINDS = (r"(?:(?:blocking|material|minor|editorial|major|new|further|other|open|"
         r"remaining|security|or|and|nor)[\W_]+)*")
VERDICT = re.compile(
    r"\b(?:pass(?:es|ed)?|approve[sd]?|fixed|resolved|stamped|"
    r"found[\W_]+no(?:thing)?|skipped[\W_]+nothing|nothing[\W_]+(?:blocking|found)|"
    rf"(?:no|{COUNT})[\W_]+{KINDS}(?:findings?|defects?))\b")
SECURITY_VERDICT = re.compile(r"\bnot[\W_]+required\b")
NEGATIONS = frozenset((
    "not", "no", "never", "neither", "nor", "nothing", "cannot", "without", "to", "be",
    "being", "will", "would", "could", "should", "might", "may", "must", "can", "shall",
    "yet", "if", "unless", "until", "once", "when", "whether", "almost", "nearly",
    "hardly", "barely", "probably", "possibly", "perhaps", "maybe", "likely",
    # The "t" of "n't", and the contracted negations written without their apostrophe.
    "t", "aint", "arent", "cant", "couldnt", "didnt", "doesnt", "dont", "hadnt", "hasnt",
    "havent", "isnt", "mightnt", "mustnt", "neednt", "shant", "shouldnt", "wasnt",
    "werent", "wont", "wouldnt"))
PASS_NOUN = frozenset((
    "a", "an", "the", "this", "that", "each", "every", "another", "one", "first", "second",
    "third", "next", "quick", "full", "fresh", "brief", "own", "its", "their", "further",
    "extra", "separate", "new", "light", "short", "single", "initial", "earlier", "later",
    "previous"))
WORD = re.compile(r"(?<![^\W_])[^\W_]+")
SEPARATORS = re.compile(r"[\W_]*")
# A clause, in which a review cell's verdict must stand beside the commit it is for
# ("Started at <sha>; CI passed" gives none), ends at every semicolon, line end, <br>
# and HTML block tag (each drawn on a line of its own), every exclamation mark, every
# question mark but one before a name and "=", as in a link's query ("?pr=2"), five
# other scripts' full stops, and every full stop but one between two letters or digits,
# inside a name or a number ("SCHEMA.md", "Claude Opus 5.5"), which reviewers' cells
# name beside their commits. A tag's pattern takes no "<" or ">", so it stays linear.
CLAUSE = re.compile(r"[;\n!\u3002\uff61\u0589\u06d4\u0964]|<br\b[^<>]*>|"
                    r"</?(?:p|div|hr|li|ul|ol|h[1-6]|blockquote|dl|dd|dt|table|tr|td|th|"
                    r"pre|details|summary)\b[^<>]*>|"
                    r"\?(?![\w-]+=)|(?<![^\W_])\.|\.(?![^\W_])")
# The inline Markdown markers, of emphasis, code, strikethrough and a link's text, which
# a reader of the rendered cell does not see, inside a word ("w*i*ll", "to co`m`e",
# "pen[d](#x)ing", its destination already cut) or at its edges.
MARKERS = re.compile(r"[*_`~\[\]]")
# Unicode's default-ignorable characters that are no format characters or marks (the
# Hangul fillers among them), which _fold drops with those.
IGNORED = dict.fromkeys(c for low, high in IGNORABLE for c in range(low, high + 1))
# A review cell names the commit it reviewed, by 7 to 40 lower-case hex digits that a
# reader sees (_review_text), and with a repository that commit must be one of the
# member's own (check_train); on /security-review, "Not required" stands instead, where
# no protected path changed.
COMMIT = re.compile(r"(?<![0-9A-Za-z])[0-9a-f]{7,40}(?![0-9A-Za-z])")
NOT_REQUIRED = re.compile(r"(?i)not required\b")
# "Not required" anywhere in the cell, however spelt: in any case, with any separators or
# none, and through character references, compatibility forms and invisible marks.
SAYS_NOT_REQUIRED = re.compile(r"not[\W_]*required")
HEADINGS = ("Branch", "Head", "/code-review", "/security-review", "/no-mistakes")
CHECK_PATHS = ("scripts/", "tests/", ".github/")
FOUNDATION_PATHS = ("Elements/Foundations/", "Certificate/axioms.lock", "model/")
PROPOSITION_PATHS = (
    re.compile(r"Elements/Book([IVX]+)/Prop(\d+)\.lean"),
    re.compile(r"review/([IVX]+)/(\d+)\.toml"),
    re.compile(r"(?:heath|mishnah)/([IVX]+)/(\d+)\.md"),
    re.compile(r"figures/([IVX]+)/(\d+)[^/]*"),
)


def _plain(text: str) -> str:
    """Strip the same cell decoration as safe_push's review tables."""
    return text.strip("`*_ ")


def _section(body: str, name: str) -> str:
    """Read one unambiguous, visible section."""
    if not isinstance(body, str) or "\0" in body:
        raise ValueError("the body is not readable text")
    found = sections(body)
    count = sum(m.group(1).strip() == name for m in SECTION.finditer(visible(body)))
    if count != 1 or not found.get(name):
        raise ValueError(f'expected one written "{name}" section')
    return found[name]


def members_table(body: str) -> list[dict]:
    """Read the five cells of each Members row; raise ValueError if unreadable."""
    lines = [line.strip() for line in _section(body, "Members").splitlines()
             if line.strip()]
    cells = []
    for line in lines:
        if not line.startswith("|") or not line.endswith("|"):
            raise ValueError("Members: expected a five-column table")
        row = [c.strip() for c in line[1:-1].split("|")]
        if len(row) != len(FIELDS):
            raise ValueError("Members: expected five cells in every row")
        cells.append(row)
    if len(cells) < 3 or tuple(_plain(c) for c in cells[0]) != HEADINGS \
            or not all(re.fullmatch(r":?-{3,}:?", c) for c in cells[1]):
        raise ValueError("Members: expected the header, separator and at least one member")
    return [dict(zip(FIELDS, (_plain(c) for c in row))) for row in cells[2:]]


def _new() -> dict:
    """An empty declaration, with fresh collections for each call."""
    return {"checks": set(), "rules": [], "propositions": set(),
            "foundations": set(), "none": False}


def _path(text: str) -> str:
    """Read a relative repository path without ambiguous components."""
    path = _plain(text)
    if not written(path) or "\\" in path or any(ord(c) < 32 for c in path) \
            or any(p in {"", ".", ".."} for p in path.split("/")):
        raise ValueError(f"What is new: invalid repository path {text!r}")
    return path


def declared_new(body: str) -> dict:
    """Read What is new into sets and rule text; raise ValueError if unreadable."""
    text = _section(body, "What is new")
    result = _new()
    if text == "None.":
        result["none"] = True
        return result
    for line, item in shown(text):
        if not line.strip():
            continue
        match = re.fullmatch(r"\s*[-*+]\s+(check|rule|propositions|foundations):\s+(.+)",
                             line)
        if not item or not match:
            raise ValueError("What is new: expected None. or a check, rule, propositions "
                             "or foundations bullet")
        kind, value = match.groups()
        if kind == "rule":
            if not written(value):
                raise ValueError("What is new: the rule is not written")
            result["rules"].append(value.strip())
        elif kind == "propositions":
            refs = [_plain(ref) for ref in value.split(",")]
            if not all(re.fullmatch(r"[IVX]+\.[1-9]\d*", ref) for ref in refs):
                raise ValueError("What is new: expected propositions such as I.5, II.3")
            result["propositions"].update(refs)
        else:
            result["checks" if kind == "check" else kind].add(_path(value))
    if not any(result[k] for k in ("checks", "rules", "propositions", "foundations")):
        raise ValueError("What is new: no declaration could be read")
    return result


def _commit(repo: Path, rev: str) -> str:
    """Resolve a commit without accepting command options as revisions."""
    value = git(repo, "rev-parse", "--verify", "--end-of-options", f"{rev}^{{commit}}")
    value = value.strip()
    if not OID.fullmatch(value):
        raise ValueError(f"could not read commit {rev!r}")
    return value


def derive_new(repo: Path, base: str, sha: str) -> dict:
    """Derive file coverage from base..sha; rule prose cannot be inferred from a diff."""
    base, sha = _commit(repo, base), _commit(repo, sha)
    result = _new()
    for _, path in changed_files(repo, base, sha):
        if under(path, CHECK_PATHS):
            result["checks"].add(path)
        if under(path, FOUNDATION_PATHS):
            result["foundations"].add(path)
        for pattern in PROPOSITION_PATHS:
            if match := pattern.fullmatch(path):
                book, number = match.groups()
                result["propositions"].add(f"{book}.{int(number)}")
                break
    result["none"] = not any(result[k] for k in ("checks", "propositions", "foundations"))
    return result


def undeclared(derived: dict, declared: dict) -> list[str]:
    """Report derived changes absent from the declaration; extra declarations are allowed."""
    problems = []
    for key, label in (("checks", "check"), ("propositions", "proposition"),
                       ("foundations", "foundation")):
        for value in sorted(derived[key] - declared[key]):
            problems.append(f"What is new: undeclared {label}: {value}")
    for rule in derived["rules"]:
        if rule not in declared["rules"]:
            problems.append(f"What is new: undeclared rule: {rule}")
    return problems


def _placeholder(cell: str) -> bool:
    """A cell that, as a whole, says only that the review is absent or still to come."""
    return bool(PLACEHOLDER.fullmatch(" ".join(_plain(cell).split())
                                      .rstrip(".!;:, ").casefold()))


def _fold(text: str, ignored: bool = True) -> str:
    """Text as it reads, its character references already decoded: NFKC, casefolding and
    NFKC again, then without format characters, combining marks and, unless `ignored` is
    false, Unicode's other default-ignorable characters (IGNORED). NFKC comes before
    casefolding as well as after, since a compatibility capital (the black-letter R) folds
    only once NFKC has made it a letter; and the marks are dropped last, since casefolding
    the dotted capital I adds one."""
    text = unicodedata.normalize("NFKC", unicodedata.normalize("NFKC", text).casefold())
    return "".join(c for c in (text.translate(IGNORED) if ignored else text)
                   if unicodedata.category(c) not in ("Cf", "Mn", "Me"))


def _kept(cell: str) -> str:
    """A fourth reading for the word lists: as written, with the default-ignorable
    characters that are no format characters or marks kept, as separators, so that one
    of them between two words ("review" U+2065 "pending"), which the other readings drop,
    does not join them in every reading."""
    return _fold(html.unescape(cell), ignored=False)


def _normal(cell: str) -> str:
    """A cell's text as it reads: character references decoded, then folded (_fold)."""
    return _fold(html.unescape(cell))


def _readings(cell: str, struck: bool = True) -> tuple[str, str, str]:
    """A review cell's three readings, each folded (_fold): as written (_normal); as a
    reader sees it (_review_text); and as a reader sees it rendered, without the inline
    Markdown markers (MARKERS) and, unless `struck`, without struck text ("~~passed~~"),
    each struck span cut to its nearest closing, since a struck verdict is none."""
    seen = _review_text(cell)
    shown = seen if struck else _cut(seen, "~", (("~~", "~~"), ("~", "~")), keep=0)
    return _normal(cell), _fold(seen), MARKERS.sub("", _fold(shown))


def _placeholder_word(cell: str) -> str | None:
    """The first word that says the review is absent, incomplete or to come, anywhere in
    the cell (PLACEHOLDER_WORD) or in a phrase that names the review (UNFINISHED), in any
    of its readings (_readings, and _kept)."""
    for text in (*_readings(cell), _kept(cell)):
        if match := PLACEHOLDER_WORD.search(text):
            return match.group()
        for phrase in PHRASE.split(text):
            if SUBJECT.search(phrase) and (match := UNFINISHED.search(phrase)):
                return match.group()
    return None


def _cut(text: str, opener: str, spans: tuple[tuple[str, str], ...], keep: int) -> str:
    """The text with spans cut out, as re.sub reads alternatives left to right: at each
    `opener`, the first span whose opening stands there and whose closing follows it is
    cut through that closing's nearest place, keeping the opening's first `keep`
    characters. A closing is searched for again only once passed, so the text is read
    in linear time, however many openings it holds."""
    parts, position, nearest = [], 0, {}
    while (start := text.find(opener, position)) >= 0:
        for opening, closing in spans:
            if not text.startswith(opening, start):
                continue
            found = nearest.get(closing, -2)
            if found != -1 and found < start + len(opening):
                found = nearest[closing] = text.find(closing, start + len(opening))
            if found >= 0:
                parts.append(text[position:start + keep])
                position = found + len(closing)
                break
        else:
            parts.append(text[position:start + 1])
            position = start + 1
    parts.append(text[position:])
    return "".join(parts)


def _review_text(cell: str) -> str:
    """A review cell's text as a reader sees it: character references decoded, after
    NFKC, without HTML comments and tags (<!-- to -->, < to >) and a link's destination
    or label (]( to ), ][ to ]), each to its nearest closing. The reviewed commit is
    read here, never in the raw cell, so a commit no reader sees names none."""
    text = unicodedata.normalize("NFKC", html.unescape(cell))
    text = _cut(text, "<", (("<!--", "-->"), ("<", ">")), keep=0)
    return _cut(text, "]", (("](", ")"), ("][", "]")), keep=1)


def _stands(text: str, match: re.Match) -> bool:
    """Whether a verdict in folded text stands as one: no NEGATIONS among the three words
    before it in its phrase (each read without its letters outside ASCII, so a
    modifier-letter apostrophe hides no "n't"), no "pass" after a PASS_NOUN word or
    "passes" after a number, and no UNFINISHED word straight after it ("passed
    (partial)", "PASS, incomplete"). Only the 60 characters before it and the 20 after
    are read, so a cell of many verdicts is still read in linear time; when those 60 cut
    a phrase before three whole words of it, the verdict does not stand, since the third
    word back is unread, and likewise when the 20 after it end inside a run of
    separators."""
    begin = max(0, match.start() - 60)
    capped = begin > 0
    for end in PHRASE.finditer(text, begin, match.start()):
        begin, capped = end.end(), False
    found = WORD.findall(text, begin, match.start())
    if capped and len(found) < 4:
        return False
    words = [w.encode("ascii", "ignore").decode() for w in found[-3:]]
    said = match.group()
    after = SEPARATORS.match(text, match.end(), match.end() + 20).end()
    if after == match.end() + 20 and SEPARATORS.match(text, after, after + 1).end() > after:
        return False  # The 20 end inside a run of separators, so what follows is unread.
    return not any(w in NEGATIONS for w in words) and not (words and (
        said == "pass" and words[-1] in PASS_NOUN
        or said == "passes" and re.fullmatch(COUNT, words[-1]))) \
        and not UNFINISHED.match(text, after)


def _anchors(cell: str, security: bool = False) -> list[set[str]]:
    """For each of a review cell's three readings (_readings, struck text taken out), the
    commit names that stand in a clause (CLAUSE) with a completed verdict that stands
    (VERDICT, or on /security-review "not required"; _stands). A name counts only if the
    commit reading reads it, in the cell as a reader sees it (COMMIT, in _review_text)."""
    patterns = (VERDICT, SECURITY_VERDICT) if security else (VERDICT,)
    seen = set(COMMIT.findall(_review_text(cell)))
    anchors = []
    for text in _readings(cell, struck=False):
        names = set()
        for clause in CLAUSE.split(text):
            if any(_stands(clause, match) for pattern in patterns
                   for match in pattern.finditer(clause)):
                names.update(name for name in COMMIT.findall(clause) if name in seen)
        anchors.append(names)
    return anchors


def _review_content(cell: str, security: bool = False) -> bool:
    """Whether a review cell gives, in each of its readings, a completed verdict that
    stands in a clause that names a reviewed commit (_anchors): a verdict that a reading
    lacks or negates, or gives only in a clause without the commit, is none."""
    return all(_anchors(cell, security))


def _evidence(rows: list[dict]) -> list[str]:
    """Check the evidence that can be read without a repository."""
    problems = []
    branches = Counter(row["branch"] for row in rows)
    for branch, count in branches.items():
        if count > 1:
            problems.append(f"Members: duplicate branch: {branch}")
    for row in rows:
        branch, head = row["branch"], row["head"]
        if not written(branch) or any(c.isspace() for c in branch):
            problems.append("Members: the branch is not written as one name")
        if not HEAD.fullmatch(head):
            problems.append(f"Members: {branch}: Head must be 12 to 40 lower-case hex digits")
        for key, label in zip(FIELDS[2:], HEADINGS[2:]):
            cell = row[key]
            if not written(cell) or (key != "no_mistakes" and _placeholder(cell)):
                problems.append(f"Members: {branch}: {label} is not written, or says the "
                                "review is not done")
            elif key != "no_mistakes":
                if word := _placeholder_word(cell):
                    problems.append(f"Members: {branch}: {label} says {word!r}: a review "
                                    "cell may not say a review is pending, to come, TBD, "
                                    "not needed, N/A, incomplete or still to follow, even "
                                    "beside the member's commit")
                not_required = key == "security_review" and NOT_REQUIRED.match(cell)
                if not COMMIT.search(_review_text(cell)) and not not_required:
                    problems.append(f"Members: {branch}: {label} names no reviewed commit "
                                    "(7 to 40 lower-case hex digits)")
                elif not not_required and not _review_content(
                        cell, security=key == "security_review"):
                    problems.append(f"Members: {branch}: {label} gives no visible review "
                                    "verdict or findings beyond the reviewed commit: it "
                                    "must say the review is done (pass, approved, fixed, "
                                    "no findings, a number of findings), not negated, in "
                                    "the clause that names the commit, which ends at every "
                                    "';', '!', <br> and block tag, every '?' but one before "
                                    "a name and '=' (as in a link's query), and every '.' "
                                    "but one between two letters or digits (SCHEMA.md, "
                                    "5.5)")
        evidence = row["no_mistakes"]
        if match := PASSED.fullmatch(evidence):
            checked = match.group(1)
            if not (head.startswith(checked) or checked.startswith(head)):
                problems.append(f"Members: {branch}: /no-mistakes names another head")
        elif evidence.startswith("not run:"):
            reason = evidence.removeprefix("not run:").strip()
            words = re.findall(r"[^\W_]+(?:['’-][^\W_]+)*", reason)
            if len(words) < 5:
                problems.append(f"Members: {branch}: /no-mistakes reason needs at least "
                                "five words")
        else:
            problems.append(f"Members: {branch}: /no-mistakes must say passed at <head> "
                            "or not run: <reason>")
    for i, row in enumerate(rows):
        head = row["head"]
        if HEAD.fullmatch(head) and any(
                HEAD.fullmatch(other["head"]) and
                (head.startswith(other["head"]) or other["head"].startswith(head))
                for other in rows[:i]):
            problems.append(f"Members: duplicate or ambiguous Head: {head}")
    return problems


def body_problems(body: str) -> list[str]:
    """Check the body's structure and evidence without git; protected paths need git."""
    problems = []
    try:
        problems.extend(_evidence(members_table(body)))
    except ValueError as error:
        problems.append(str(error))
    try:
        declared_new(body)
    except ValueError as error:
        problems.append(str(error))
    return problems


def _entries_on_main(repo: Path, base: str) -> bool:
    """Whether origin/main's tree has docs/decisions/ as a directory, where the decision
    entry files of tooling/decision-entries live. Absent, or anything but a directory,
    is false, and then no entry file has the decisions page's allowance."""
    entry = git(repo, "ls-tree", base, "--", "docs/decisions").strip()
    return bool(re.fullmatch(r"040000 tree [0-9a-f]{40,64}\tdocs/decisions", entry))


def _decision_path(path: str, entries: bool = False) -> bool:
    """The decisions page or, when origin/main has docs/decisions/ (entries), one of the
    Markdown entry files directly under it."""
    return path == DECISIONS or entries and bool(
        re.fullmatch(r"docs/decisions/[^/]+\.md", path))


def _coordinator_path(path: str, repo: Path | None = None, old: str | None = None,
                      new: str | None = None, entries: bool = False) -> bool:
    """Generated files and the decisions page, or a Markdown decision entry when origin/main
    has docs/decisions/. README.md and docs/PROGRAM.md are generated only between their
    markers: given the two revisions, a change to them counts only when it leaves the rest,
    written by hand, as it was."""
    if path in GENERATED_REGIONS:
        return repo is not None and not generated_parts(repo, old, new, path)[1]
    return under(path, (*GENERATED, "book/")) or _decision_path(path, entries)


def _merge_problems(repo: Path, merge: str, parents: list[str], attrs: str,
                    entries: bool = False) -> list[str]:
    """Compare a merge with git's automatic tree, including every conflicted path. Merge
    attributes (merge=union, say) are read from `attrs`, origin/main's commit, never from
    the checkout or the merged sides; `entries` says whether origin/main has
    docs/decisions/."""
    result = run(["git", f"--attr-source={attrs}", "merge-tree", "--write-tree",
                  "--name-only", "-z", "--no-messages", *parents], repo)
    if result.returncode not in (0, 1):
        raise ValueError(f"could not read automatic merge {merge} (Git 2.42 or later is "
                         f"needed): {result.stderr.strip()}")
    fields = result.stdout.split("\0")
    if not fields or not OID.fullmatch(fields[0]) or fields[-1] != "":
        raise ValueError(f"could not read automatic merge {merge}")
    tree = fields[0]
    conflicts = fields[1:-1]
    if conflicts and conflicts[-1] == "":
        conflicts.pop()
    if any(not path for path in conflicts) or bool(conflicts) != (result.returncode == 1):
        raise ValueError(f"could not read conflicted paths for merge {merge}")
    paths = set(conflicts) | {p for _, p in changed_files(repo, tree, merge)}
    return [f"merge {merge[:12]}: resolution or added content outside generated files "
            f"and decisions: {path}" for path in sorted(paths)
            if not _coordinator_path(path, repo, tree, merge, entries)]


def _merge_bases(repo: Path, left: str, right: str) -> list[str]:
    """Read every merge base, more than one after criss-cross merges; none is unreadable."""
    bases = git(repo, "merge-base", "--all", left, right).split()
    if not bases or not all(OID.fullmatch(b) for b in bases):
        raise ValueError("could not read a merge base")
    return bases


def _contains(repo: Path, older: str, newer: str) -> bool:
    """Whether `older` is an ancestor of `newer` or the same commit."""
    result = run(["git", "merge-base", "--is-ancestor", older, newer], repo)
    if result.returncode not in (0, 1):
        raise ValueError("could not read ancestry")
    return result.returncode == 0


def _commits(repo: Path, *args: str) -> set[str]:
    """Read full commit names, refusing unexpected revision-list output."""
    commits = git(repo, "rev-list", *args).splitlines()
    if not all(OID.fullmatch(commit) for commit in commits):
        raise ValueError("could not read commit history")
    return set(commits)


def _named_commits(repo: Path, cells: list[str]) -> set[str]:
    """The commits the cells' tokens name, each token resolved as `git rev-parse --verify
    <token>^{commit}` resolves it, all in one cat-file call. A token that is no commit, is
    ambiguous, or resolves (as a ref name, say) to a commit whose name does not begin
    with it, names none."""
    tokens = list(dict.fromkeys(t for cell in cells for t in COMMIT.findall(cell)))
    if not tokens:
        return set()
    result = run(["git", "cat-file", "--batch-check=%(objectname) %(objecttype)"], repo,
                 input="".join(f"{token}^{{commit}}\n" for token in tokens))
    lines = result.stdout.splitlines()
    if result.returncode != 0 or len(lines) != len(tokens):
        raise ValueError("could not resolve the commits the review cells name")
    named = set()
    for token, line in zip(tokens, lines):
        if line == f"{token}^{{commit}} missing":
            continue
        value, _, kind = line.partition(" ")
        if kind != "commit" or not OID.fullmatch(value):
            raise ValueError("could not resolve the commits the review cells name")
        if value.startswith(token):
            named.add(value)
    return named


def _says_not_required(cell: str) -> bool:
    """Whether the cell says "Not required" anywhere, however spelt, in any of its
    readings (_readings, and _kept), so markup ("not<i></i> required", "n*o*t required")
    cannot hide it from all at once."""
    return any(SAYS_NOT_REQUIRED.search(text) for text in (*_readings(cell), _kept(cell)))


def check_train(repo: Path, base: str, sha: str, body: str) -> list[str]:
    """Check rules 1 to 6, returning refusals; unreadable inputs raise ValueError or Refusal.

    The base is origin/main's supplied tip. The train's own first-parent chain is read:
    its merges and its own commits; a member's history is the member's. Each
    /code-review and /security-review cell must name a commit of the member's own
    history, its head or an ancestor of it not on origin/main, and a member that changes
    a protected path may not say "Not required" anywhere in its /security-review cell.
    Keep-apart is stricter than safe_push.keep_apart: check changes with judged content
    refuse even when origin/main's checks pass.
    """
    rows, declared = members_table(body), declared_new(body)
    base, sha = _commit(repo, base), _commit(repo, sha)
    if git(repo, "rev-parse", "--is-shallow-repository").strip() != "false":
        raise ValueError("could not read complete history: the repository is shallow")
    if not _contains(repo, base, sha):
        return ["train head does not contain the supplied base"]
    problems = _evidence(rows)
    history = _commits(repo, base)
    entries = _entries_on_main(repo, base)
    # Rules 1 to 3 read the train's own first-parent chain: its merges of members and of
    # main, and its own commits. A member's history inside it, merges of main with their
    # resolutions included, is the member's, judged by the member's own reviews.
    graph = []
    for line in git(repo, "rev-list", "--first-parent", "--parents",
                    f"{base}..{sha}").splitlines():
        fields = line.split()
        if not fields or not all(OID.fullmatch(field) for field in fields):
            raise ValueError("could not read the train's parents")
        graph.append((fields[0], fields[1:]))
    members = Counter()
    for commit, parents in graph:
        if len(parents) > 2:
            problems.append(f"merge {commit[:12]}: expected exactly two parents")
        elif len(parents) == 2:
            if parents[1] not in history:
                members[parents[1]] += 1
            problems.extend(_merge_problems(repo, commit, parents, base, entries))
    matched = Counter()
    for row in rows:
        heads = [head for head in members if HEAD.fullmatch(row["head"])
                 and head.startswith(row["head"])]
        if len(heads) != 1:
            problems.append(f"Members: {row['branch']}: row has no unique member merge "
                            f"for {row['head']}")
            continue
        head = heads[0]
        matched[head] += 1
        evidence = PASSED.fullmatch(row["no_mistakes"])
        if evidence and not head.startswith(evidence.group(1)):
            problem = f"Members: {row['branch']}: /no-mistakes names another head"
            if problem not in problems:
                problems.append(problem)
        # After criss-cross merges a member has several merge bases with main: the paths
        # it changes against any of them count, so more bases never mean fewer paths.
        try:
            protected = {p for member_base in _merge_bases(repo, base, head)
                         for _, p in changed_files(repo, member_base, head) if is_protected(p)}
            # The member's own history: its head and every ancestor not on origin/main.
            own = _commits(repo, head, "--not", base)
            named = {key: _named_commits(repo, [_review_text(row[key])])
                     for key in ("code_review", "security_review")}
        except (ValueError, Refusal) as error:
            raise ValueError(f"Members: {row['branch']} ({head[:12]}): {error}") from None
        for key, label in (("code_review", "/code-review"),
                           ("security_review", "/security-review")):
            if key == "security_review" and not protected \
                    and NOT_REQUIRED.match(row[key]):
                continue
            if not named[key] & own:
                problems.append(f"Members: {row['branch']}: {label} names no commit of the "
                                "member's own history (its head, or an ancestor of it not "
                                "on origin/main)")
        if protected and _says_not_required(row["security_review"]):
            problems.append(f"Members: {row['branch']}: /security-review says Not required "
                            f"for protected paths: {', '.join(sorted(protected))}")
    for head, count in sorted(members.items()):
        if count != 1:
            problems.append(f"member {head[:12]} merged more than once ({count} merges)")
        if not matched[head]:
            problems.append(f"member {head[:12]} has no Members row")
        elif matched[head] != 1:
            problems.append(f"member {head[:12]} has more than one Members row")
    for commit, parents in graph:
        if len(parents) < 2:
            if len(parents) != 1:
                raise ValueError(f"could not read a parent for coordinator commit {commit}")
            for _, path in changed_files(repo, parents[0], commit):
                if not _coordinator_path(path, repo, parents[0], commit, entries):
                    problems.append(f"coordinator commit {commit[:12]} changes forbidden "
                                    f"path: {path}")
    inputs = sorted(p for _, p in changed_files(repo, base, sha)
                    if under(p, CHECK_INPUTS + (".github/",))
                    and not pinned(repo, base, sha, p))
    # Decision entry files (tooling/decision-entries) have the same allowance as the
    # decisions page once origin/main has their directory, including when safe_push's
    # guides do not yet include it.
    judged = [p for p in judged_files(repo, base, sha)
              if not _decision_path(p, entries)] if inputs else []
    if inputs and judged:
        problems.append(f"check changes must be kept apart from judged content: "
                        f"{', '.join(inputs)}; judged: {', '.join(judged)}")
    problems.extend(undeclared(derive_new(repo, base, sha), declared))
    return problems


def main(argv=None) -> int:
    """Print the verdict, distinguishing refused trains from unreadable inputs."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--body-file", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        body = args.body_file.read_text(encoding="utf-8")
        problems = check_train(Path.cwd(), args.base, args.head, body)
    except (OSError, UnicodeError, ValueError, Refusal) as error:
        print(f"train: could not read: {error}", file=sys.stderr)
        return 2
    if problems:
        for problem in problems:
            print(f"train: REFUSED: {problem}")
        return 1
    print("train: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
