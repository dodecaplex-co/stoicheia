#!/usr/bin/env python3
"""Automatic reverts in temporary git repositories, with an injected GitHub.

    python3 -I tests/test_auto_revert.py

Standard library only, with git and openssl. No network requests are permitted.
The push stand-in pushes to a local bare repository; the HTTP stand-in records
tokens, labels, pull requests and queue requests for assertions.
"""

from __future__ import annotations

import base64
import contextlib
import copy
import io
import itertools
import json
import os
import re
import socket
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import auto_revert as ar  # noqa: E402


SLUG = "owner/edition"
WORKFLOW_TOKEN = "workflow-credential-for-tests"
APP_TOKEN = "installation-credential-for-tests"


def command(directory: Path, *args: str) -> str:
    env = ar.git_env()
    env["GIT_ALLOW_PROTOCOL"] = "file"
    result = subprocess.run(list(args), cwd=directory, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
    return result.stdout.strip()


def workflow_step(filename: str, name: str) -> str:
    """Extract an executable run block so the tests run the workflow's own shell."""
    lines = (ROOT / ".github/workflows" / filename).read_text(encoding="utf-8").splitlines()
    start = lines.index("      - name: " + name) + 1
    while start < len(lines) and not lines[start].startswith("        run: "):
        if lines[start].startswith("      - "):
            raise AssertionError(f"No run block for {name}")
        start += 1
    if start == len(lines):
        raise AssertionError(f"No run block for {name}")
    value = lines[start].removeprefix("        run: ")
    if value != "|":
        return value + "\n"
    end = start + 1
    while end < len(lines) and (not lines[end].strip() or lines[end].startswith("          ")):
        end += 1
    return textwrap.dedent("\n".join(lines[start + 1:end])) + "\n"


# A key of a YAML block mapping, and the value after it on its line, if any.
YAML_KEY = re.compile(r"([A-Za-z_][A-Za-z0-9_-]*):(?: +(.*))?")


def unread(line: str) -> AssertionError:
    return AssertionError(f"A workflow form this test does not read: {line!r}")


def yaml_block(lines: list[str], at: int, indent: int) -> tuple[dict | list, int]:
    """The block mapping, or list of mappings, whose entries start at column `indent` from
    lines[at], and the index of the line after it. Only the forms the workflows use are
    read: plain scalars, as text, `|` blocks and blocks of their own; any other form fails
    the test rather than being read as it was."""
    block = None
    while at < len(lines):
        line = lines[at]
        text = line.lstrip(" ")
        depth = len(line) - len(text)
        if not text or text.startswith("#"):
            at += 1
            continue
        if depth < indent:
            break
        if depth > indent:
            raise unread(line)
        if text.startswith("- "):
            block = [] if block is None else block
            if not isinstance(block, list):
                raise unread(line)
            # The item's first key stands after its dash: read the item as a mapping.
            lines[at] = " " * (indent + 2) + text[2:]
            item, at = yaml_block(lines, at, indent + 2)
            if not isinstance(item, dict):
                raise unread(line)
            block.append(item)
            continue
        block = {} if block is None else block
        match = YAML_KEY.fullmatch(text.rstrip(" "))
        if not isinstance(block, dict) or not match or match[1] in block:
            raise unread(line)
        key, value = match[1], match[2]
        at += 1
        if value == "|":
            # Its lines less the first one's indentation, and one final line feed.
            body = []
            while at < len(lines) and (not lines[at].strip()
                                       or lines[at].startswith(" " * (depth + 1))):
                body.append(lines[at])
                at += 1
            while body and not body[-1].strip():
                body.pop()
            first = next((row for row in body if row.strip()), "")
            margin = len(first) - len(first.lstrip(" "))
            if not first or any(row.strip() and not row.startswith(" " * margin)
                                for row in body):
                raise unread(line)
            block[key] = "\n".join(row[margin:] for row in body) + "\n"
        elif value is None:
            inner = at
            while inner < len(lines) and (not lines[inner].strip()
                                          or lines[inner].lstrip(" ").startswith("#")):
                inner += 1
            following = lines[inner] if inner < len(lines) else ""
            nested = len(following) - len(following.lstrip(" "))
            if not following or nested <= depth:
                raise unread(line)
            block[key], at = yaml_block(lines, inner, nested)
        elif (value[0] in "'\"[]{}>|*&!%@`#,?:-" or ": " in value or " #" in value
              or value.endswith(":")):
            raise unread(line)
        else:
            block[key] = value
    if block is None:
        raise unread(lines[at - 1] if at else "")
    return block, at


def workflow_job(filename: str, name: str) -> dict:
    """A job of a workflow, as yaml_block reads it. A key this test does not model, at the
    workflow's top (an env or defaults, say) or the job's, which could change how its
    steps run, fails the test; so do a key given twice at the top or among the jobs, and a
    line break other than a line feed, which YAML readers do not all read alike."""
    text = (ROOT / ".github/workflows" / filename).read_text(encoding="utf-8")
    if re.search("[\r\x85\u2028\u2029]", text):
        raise AssertionError(f"{filename} has a line break this test does not read")
    lines = text.split("\n")
    top = [line.split(":")[0] for line in lines if line[:1] not in ("", " ", "#")]
    jobs, at = [], lines.index("jobs:") + 1
    while at < len(lines) and lines[at][:1] in ("", " ", "#"):
        if re.match(r"  [^ #]", lines[at]):
            jobs.append(lines[at])
        at += 1
    if (len(set(top)) != len(top) or len(set(jobs)) != len(jobs)
            or not all(re.fullmatch(r"  [A-Za-z_][A-Za-z0-9_-]*:", line) for line in jobs)):
        raise AssertionError(f"{filename} has a key twice, or a job this test does not read")
    job, end = yaml_block(lines, lines.index(f"  {name}:") + 1, 4)
    if (set(top) - {"name", "on", "permissions", "jobs"} or not isinstance(job, dict)
            or set(job) - {"needs", "if", "runs-on", "environment", "permissions", "env",
                           "steps"}
            or end < len(lines) and not re.fullmatch(r"  [A-Za-z_][A-Za-z0-9_-]*:", lines[end])):
        raise AssertionError(f"{filename}: the job {name} has a form this test does not model")
    return job


def job_step(job: dict, name: str) -> dict:
    steps = [step for step in job["steps"] if step.get("name") == name]
    if len(steps) != 1:
        raise AssertionError(f"The job has {len(steps)} steps named {name!r}")
    return steps[0]


# The tokens of an if, as post-merge.yml writes one.
CONDITION = re.compile(r"\s*(always\(\)|success\(\)|failure\(\)|cancelled\(\)|'(?:[^']|'')*'"
                       r"|steps\.[A-Za-z_][A-Za-z0-9_-]*\.outputs\.[A-Za-z_][A-Za-z0-9_-]*"
                       r"|&&|\|\||==|!=|[()])")


def condition(text: str | None, outputs: dict, status: str) -> bool:
    """Whether a step or job whose if is `text` runs, as Actions decides it, given the
    steps' outputs so far ({id: {name: value}}; one never set reads as '', as in Actions)
    and the status so far, "success", "failure" or "cancelled": the job's, for a step, or
    that of the jobs it needs, for a job. Only the four status functions, outputs, '…'
    strings, == and != between strings (without regard to case), &&, || and parentheses
    are read; any other form fails the test. Without a status function, success() is
    implied, as Actions implies it."""
    tokens, at = [], 0
    while (text or "")[at:].strip():
        match = CONDITION.match(text, at)
        if not match:
            raise AssertionError(f"A condition this test does not read: {text!r}")
        tokens.append(match[1])
        at = match.end()
    if not tokens:
        return status == "success"
    tokens.append("")
    position = 0

    def take(*expected):
        nonlocal position
        if expected and tokens[position] not in expected:
            raise AssertionError(f"A condition this test does not read: {text!r}")
        position += 1
        return tokens[position - 1]

    def operand():
        token = take()
        if token == "(":
            value = either()
            take(")")
            return value
        if token.endswith("()"):
            return token in ("always()", status + "()")
        if token.startswith("'"):
            return token[1:-1].replace("''", "'")
        if token.startswith("steps."):
            _, step, _, name = token.split(".")
            return outputs.get(step, {}).get(name, "")
        raise AssertionError(f"A condition this test does not read: {text!r}")

    def comparison():
        left = operand()
        if tokens[position] not in ("==", "!="):
            return left
        same, right = take() == "==", operand()
        if not isinstance(left, str) or not isinstance(right, str):
            raise AssertionError(f"A condition this test does not read: {text!r}")
        return (left.lower() == right.lower()) == same

    # Each, as in Actions, gives the operand that decides it.
    def both():
        value = comparison()
        while tokens[position] == "&&":
            take()
            right = comparison()
            if value:
                value = right
        return value

    def either():
        value = both()
        while tokens[position] == "||":
            take()
            right = both()
            if not value:
                value = right
        return value

    result = bool(either())
    take("")
    if any(token.endswith("()") for token in tokens):
        return result
    return status == "success" and result


def expressions(text: str, values: dict) -> str:
    """`text` with each ${{ … }} given its value, as Actions substitutes it; an expression
    not in `values` fails the test."""
    def value(match):
        if match[1] not in values:
            raise AssertionError(f"An expression this test does not know: {match[0]}")
        return values[match[1]]

    result = re.sub(r"\$\{\{\s*(.*?)\s*\}\}", value, text)
    if "${{" in result:
        raise AssertionError(f"An unclosed expression: {text!r}")
    return result


# Put before a step's run text, this has bash write, before each command the step runs, a
# line to descriptor 37, a copy of stderr: the number of subshells the command runs in,
# XTRACE, and the command as written. Bash 3.2 and bash 5.2 write it alike. It is a DEBUG
# trap, which set -T carries into functions, subshells and command substitutions, and not
# set -x, which a group, subshell or function whose stderr goes elsewhere silences.
TRACE = ("exec 37>&2; set -T; "
         "trap 'printf \"%sXTRACE %s\\n\" \"$BASH_SUBSHELL\" \"$BASH_COMMAND\" >&37' DEBUG\n")


def commands(stderr: str) -> list[str]:
    """The commands a step run after TRACE ran, in order, from its stderr: each one's
    name, or the variable it sets and `=`, after a + for each subshell it ran in; a plain
    assignment before a name, as in `IFS= read`, is read with it. So each command the
    step runs on the path the test takes is seen, wherever its stderr goes, and whether
    or not it finds, in the test's checkout, a file it would run. Not seen: a command on
    a branch no test takes, and the commands of a step written against this test, which
    turns the trace off with descriptor 37 sent elsewhere, as
    `{ trap - DEBUG; } 37>/dev/null` does."""
    found = []
    for depth, text in re.findall(r"^(\d+)XTRACE (.*)$", stderr, re.M):
        plain = re.match(r"(?:[A-Za-z_][A-Za-z0-9_]*=[^\s'\"$`\\]*\s+)*", text)
        names = re.findall(r"([A-Za-z_][A-Za-z0-9_]*=)[^\s'\"$`\\]*\s+", plain[0])
        names.append(re.match(r"[A-Za-z_][A-Za-z0-9_]*=|\S*", text[plain.end():])[0])
        found += ["+" * int(depth) + name for name in names]
    return found


def run_step(job: dict, step: dict, values: dict, runner: Path, cwd: Path, path: str):
    """Run a step of a Linux job as Actions runs it: the job's env and then the step's,
    each expression in them and in run given its value, and run written to a file that
    the step's shell runs (`bash -e` when it names none, and bash with pipefail, without
    profile or rc files, for `shell: bash`), after TRACE. Returns the process and whether
    its exit fails the job. A step key or shell this does not model fails the test."""
    shells = {None: ["bash", "-e"],
              "bash": ["bash", "--noprofile", "--norc", "-eo", "pipefail"]}
    keep_going = step.get("continue-on-error", "false")
    if (set(step) - {"name", "id", "if", "env", "shell", "run", "continue-on-error"}
            or step.get("shell") not in shells or keep_going not in ("true", "false")
            or job.get("runs-on") != "ubuntu-latest"):
        raise AssertionError(f"A step this test does not model: {step}")
    env = {"PATH": path, "HOME": str(runner), "RUNNER_TEMP": str(runner)}
    for scope in (job.get("env", {}), step.get("env", {})):
        env.update({key: expressions(text, values) for key, text in scope.items()})
    script = runner / "step.sh"
    script.write_text(TRACE + expressions(step["run"], values), encoding="utf-8")
    result = subprocess.run([*shells[step.get("shell")], str(script)], cwd=cwd, env=env,
                            text=True, capture_output=True, check=False)
    return result, result.returncode != 0 and keep_going == "false"


# A stand-in for python3 and gh on the runner's PATH: it records each call, its name, its
# arguments and its environment, as a line of `calls`; python3 exits with the code in the
# file `exit` beside it, and gh answers the calls the revert job's fallback makes.
RECORDER = '''\
import json
import os
import sys
from pathlib import Path

calls = Path({calls!r})
name, args, root = Path(sys.argv[0]).name, sys.argv[1:], "repos/{slug}"
with calls.open("a", encoding="utf-8") as out:
    out.write(json.dumps([name, args, dict(os.environ)]) + "\\n")
if name == "python3":
    sys.exit(int(calls.with_name("exit").read_text()))
if args == ["api", "--paginate", root + "/labels?per_page=100", "--jq", ".[].name"]:
    print("blocks-release\\nmain-red")
elif args == ["api", root + "/pulls/11", "--jq", ".title"]:
    print("Train 11")
elif args[:4] == ["api", "--method", "POST", root + "/issues"]:
    print("Opened issue #1000")
else:
    sys.exit("Unexpected gh operation: " + repr(args))
'''

# Small Markdown files, each of the forms the link reading decides, which auto_revert.py
# and check_links.py must read alike.
LINK_CASES = {
    "schemes-and-plain": (
        "[web](https://example.invalid/a) [mail](mailto:a@example.invalid) [svn](svn+ssh://h/x)"
        " [drive](C:/x) [root](/README.md) [host](//host/x) [up](../x.md) [here](#top)\n"
    ),
    "fences": (
        "[before](a.md)\n```\n[in backticks](b.md)\n```\n~~~\n[in tildes](c.md)\n# Fenced\n~~~\n"
        "````python\n[four](d.md)\n```\n[still code](e.md)\n````\n"
        "   ```\n[indented three](f.md)\n   ```\n    ```\n[indented four](g.md)\n"
        "~~~\n[tildes](h.md)\n```\n[backticks close no tildes](i.md)\n~~~\n"
        "```\n[a close with text](j.md)\n``` text\n[still in](k.md)\n```\n[after](l.md)\n"
        "``two backticks are no fence``\n[after two](m.md)\n~~two tildes are none~~\n"
        "[after tildes](n.md)\n"
    ),
    "headings": (
        "# One\n## Two ##\n### Three ###   \n#### *Emphasis* and `code`\n"
        "##### [Linked](x.md) heading\n###### Six\n####### Seven\n#No space\n#\n"
        "    # Indented four\n   # Indented three\n#\tTabbed\n"
        "Setext one\n===\n\nSetext two\n---\n\n- Item\n---\n\n> Quote\n---\n\n1. Number\n---\n"
        "\nRepeated\n===\n\n# Repeated\n## Repeated\n"
        "Escaped \\# and \\_under\\_\n===\n\n# snake\\_case\n"
        "# Ελληνικά, digits 42 & signs!\n"
        "Three spaces\n   ===\n\nFour spaces\n    ===\n\nTrailing\n===  \n\nTabbed\n---\t\n"
    ),
    "comments": (
        "<!-- [one line](a.md) -->[after a comment](b.md)\n"
        "<!--\n[two lines](c.md)\n# Hidden\n<a name=\"hidden\"></a>\n-->\n"
        "<!-- unclosed [x](d.md)\n[visible](e.md)\n"
    ),
    "link-text": (
        "[plain](a.md) [nested [brackets] inside](b.md) [two [deep [no]]](c.md)\n"
        "\\[escaped open](d.md) [escaped \\] close](e.md) [escaped \\[ open](f.md)\n"
        "![image](g.png) [empty]() [spaced]( h.md ) [angle](<i j.md>) [unclosed](<k.md\n"
        "[parens](l(m).md) [title](n.md \"Title\") [code `[x](o.md)`](p.md)\n"
        "`[in a span](q.md)` ``[double ` span](r.md)`` [after spans](s.md)\n"
        "``a```b`` [past a longer run](w.md) `\n"
        "[a](t.md)[b](u.md) [label][ref] [gap] (v.md)\n"
    ),
    "references": (
        "[label]: a.md\n[spaced]:   b.md \"Title\"\n[angle]: <c d.md>\n   [three]: e.md\n"
        "    [four]: f.md\n[esc\\]aped]: g.md\n[]: h.md\n[tab]:\ti.md\n[none]:\n"
        "[a]: j.md [k](k.md)\n"
    ),
    "html": (
        "<a href=\"a.md\">a</a> <img src='b.png'> <a HREF=\"c.md\">c</a>\n"
        "<a href = \"d.md?x=1&amp;y=2#part\">d</a> <a data-href=\"e.md\">e</a>\n"
        "<a title=\"x\" href=\"f.md\">f</a> <a href=g.md>g</a> `<a href=\"h.md\">`\n"
        "<a name=\"one\"></a> <span id='two'></span> <p ID=\"upper\"> <a NAME=\"upper\">\n"
        "<a name=\"amp&amp;ersand\"></a> <a data-id=\"data\"></a> <a id=\"\"></a>\n"
        "1 < 2 and <3 href=\"i.md\"> `<a id=\"code\">`\n"
        "<a xhref=\"z.md\">x</a> <a xid=\"x-id\"></a> <a xname=\"x-name\"></a>\n"
    ),
    "line-ends": "[crlf](a.md)\r\n# Heading\r\nSetext\r\n---\r\n[cr](b.md)\r# After\r",
}
# Anchors of a link to a file or folder, which auto_revert.resolves and
# check_links.check_anchor must decide alike: lines of a file, headings of Markdown.
LINE_ANCHORS = ("L1", "L3", "L4", "L0", "L1-L3", "L2-L2", "L3-L1", "L1-L4", "L1C2",
                "L1C2-L3C4", "L2C1-L3", "L1-L3C9", "L01", "l1", "L1-", "L1-3", "LL1", "L",
                "1", "L1C", "C1", "L1-L2-L3", "L1 ", "folder", "Folder", "a-part")


class GitHub:
    """Only the endpoints used by the script, with no real HTTP layer."""

    def __init__(self):
        self.calls = []
        self.pulls = {}
        self.labels = {}
        self.issues = {}
        self.open_issues = []
        self.after = ""
        self.pushed_head = ""
        self.pr = None
        self.queue = None
        self.broken = None
        self.deleted = []
        self.tip_reads = []
        self.comparisons = {}
        self.issued_permissions = None
        self.jwt = None
        self.pages = {}

    def __call__(self, method, path, token, data):
        self.calls.append((method, path, token, copy.deepcopy(data)))
        if self.broken and self.broken(method, path, token, data):
            raise RuntimeError(f"{WORKFLOW_TOKEN} {APP_TOKEN} {token}")
        root = f"/repos/{SLUG}"
        if (method, path) in self.pages:
            return self.pages[method, path]
        if method == "GET" and path.startswith(root + "/labels?"):
            return [{"name": name} for name in self.labels]
        if method == "POST" and path == root + "/labels":
            if token != WORKFLOW_TOKEN:
                raise AssertionError("Labels must be created with the workflow token")
            self.labels[data["name"]] = data
            return {"name": data["name"]}
        if method == "GET" and path.startswith(root + "/pulls/"):
            return copy.deepcopy(self.pulls[int(path.rsplit("/", 1)[1])])
        if method == "GET" and path == root + "/git/ref/heads/main":
            if self.tip_reads:
                tip = self.tip_reads.pop(0) if len(self.tip_reads) > 1 else self.tip_reads[0]
                return {"object": {"sha": tip}}
            return {"object": {"sha": self.after}}
        if method == "GET" and path.startswith(root + "/compare/"):
            if path in self.comparisons:
                return copy.deepcopy(self.comparisons[path])
            raise AssertionError(f"No comparison evidence for {path}")
        if method == "GET" and path == root + "/installation":
            self.jwt = token
            return {"id": 42}
        if method == "POST" and path == "/app/installations/42/access_tokens":
            if token != self.jwt or data["repositories"] != ["edition"]:
                raise AssertionError("Wrong token scope")
            self.issued_permissions = data["permissions"]
            return {"token": APP_TOKEN}
        if method == "POST" and path == root + "/issues":
            if token != WORKFLOW_TOKEN:
                raise AssertionError("Issues must use the workflow token")
            number = 1000 + len(self.issues)
            self.issues[number] = copy.deepcopy(data)
            return {"number": number}
        if method == "PATCH" and path.startswith(root + "/issues/"):
            if token != WORKFLOW_TOKEN:
                raise AssertionError("Issue outcomes must use the workflow token")
            number = int(path.rsplit("/", 1)[1])
            self.issues[number].update(data)
            return {"number": number}
        if method == "POST" and path == root + "/pulls":
            if token != APP_TOKEN:
                raise AssertionError("Pull requests must use the App token")
            self.pr = copy.deepcopy(data)
            return {"number": 2000, "node_id": "PR_revert", "head": {"sha": self.pushed_head}}
        if method == "POST" and path == root + "/issues/2000/labels":
            if token != APP_TOKEN:
                raise AssertionError("Pull request labels must use the App token")
            self.pr["labels"] = data["labels"]
            return [{"name": name} for name in data["labels"]]
        if method == "POST" and path == "/graphql":
            if token != APP_TOKEN:
                raise AssertionError("Queue requests must use the App token")
            self.queue = data
            return {"data": {"enqueuePullRequest": {"mergeQueueEntry": {"id": "queue-entry"}}}}
        if method == "GET" and path.startswith(root + "/issues?"):
            return copy.deepcopy(self.open_issues)
        if method == "DELETE" and path.endswith("/labels/main-red"):
            self.deleted.append(int(path.split("/")[-3]))
            return [{"name": "blocks-release"}]
        raise AssertionError(f"Unexpected HTTP operation: {method} {path}")


class AutoRevert(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.keys = tempfile.TemporaryDirectory(prefix="stoicheia-revert-test-key-")
        directory = Path(cls.keys.name)
        path = directory / "key.pem"
        command(directory, "openssl", "genrsa", "-out", str(path), "2048")
        cls.key = path.read_text(encoding="utf-8")

    @classmethod
    def tearDownClass(cls):
        cls.keys.cleanup()

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="stoicheia-revert-test-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.repo = self.directory / "source"
        self.repo.mkdir()
        command(self.repo, "git", "init", "-b", "main")
        self.write("chapter.txt", "Original chapter.\n")
        self.commit("Initial edition")
        self.before = self.rev()
        self.remote = self.directory / "receiver.git"
        command(self.directory, "git", "init", "--bare", str(self.remote))
        self.api = GitHub()
        self.env = {"GITHUB_TOKEN": WORKFLOW_TOKEN, "STOICHEIA_REVERT_APP_ID": "1234",
                    "STOICHEIA_REVERT_APP_KEY": self.key}
        self.pushes = []
        self.network = mock.patch.object(socket.socket, "connect",
                                         side_effect=AssertionError("Network is forbidden"))
        self.network.start()
        self.addCleanup(self.network.stop)
        no_http = mock.patch.object(ar, "request",
                                    side_effect=AssertionError("Real HTTP is forbidden"))
        no_http.start()
        self.addCleanup(no_http.stop)

    def git(self, *args):
        return command(self.repo, "git", *args)

    def rev(self):
        return self.git("rev-parse", "HEAD")

    def write(self, name, text):
        path = self.repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def commit(self, subject):
        self.git("add", ".")
        self.git("commit", "-m", subject)

    def train(self, number=11, path="chapter.txt", text="Changed chapter.\n", labels=("text",)):
        self.git("switch", "-c", f"train/test-{number}")
        self.write(path, text)
        self.commit(f"Member of train {number}")
        head = self.rev()
        self.git("switch", "main")
        self.git("merge", "--no-ff", f"train/test-{number}", "-m",
                 f"Merge pull request #{number} from owner/train/test-{number}")
        merge = self.rev()
        self.api.pulls[number] = {
            "number": number, "title": f"Train {number}", "merged": True,
            "merge_commit_sha": merge, "head": {"sha": head, "ref": f"train/test-{number}"},
            "base": {"ref": "main", "repo": {"full_name": SLUG}},
            "labels": [{"name": name} for name in labels],
        }
        self.api.after = merge
        return merge

    def push(self, repo, slug, branch, token):
        self.assertEqual(slug, SLUG)
        self.assertEqual(token, WORKFLOW_TOKEN)
        head = command(repo, "git", "rev-parse", "HEAD")
        subjects = command(repo, "git", "log", "--reverse", "--format=%B",
                           f"{self.api.after}..{head}")
        command(repo, "git", "push", str(self.remote), f"HEAD:refs/heads/{branch}")
        self.api.pushed_head = head
        self.pushes.append({"head": head, "subjects": subjects, "branch": branch,
                            "tree": command(repo, "git", "rev-parse", "HEAD^{tree}")})

    def run_revert(self, *extra, before=None, after=None, env=None, http=None, push=None):
        after = after or self.rev()
        args = ["--before", before or self.before, "--after", after, "--repo", SLUG,
                "--run-url", f"https://github.com/{SLUG}/actions/runs/99",
                "--failed-jobs", "integration / check: failure\nintegration / model: failure",
                *extra]
        output = io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            status = ar.main(args, http=http or self.api, push=push or self.push,
                             repo_dir=self.repo, env=self.env if env is None else env)
        return status, output.getvalue()

    def body(self):
        self.assertEqual(len(self.api.issues), 1)
        return self.api.issues[1000]["body"]

    def assert_issue_only(self, status):
        self.assertEqual(status, 1, self.api.calls)
        self.assertEqual(len(self.api.issues), 1)
        self.assertIsNone(self.api.pr)
        self.assertIsNone(self.api.queue)
        self.assertEqual(self.pushes, [])

    def test_one_train_reverted_and_enqueued(self):
        merge = self.train()
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.pushes[0]["tree"], self.git("rev-parse", self.before + "^{tree}"))
        self.assertEqual(self.pushes[0]["branch"], f"revert/{merge[:12]}")
        self.assertEqual(self.api.queue["variables"]["input"],
                         {"pullRequestId": "PR_revert", "expectedHeadOid": self.api.pushed_head})
        self.assertIn(f"Reverts: {merge}\n", self.api.pr["body"])
        self.assertEqual([line for line in self.api.pr["body"].splitlines()
                          if line.startswith("Failed run:")], ["Failed run: 99"])
        self.assertIn("Failed run: 99\n", self.body())
        self.assertIn("https://github.com/owner/edition/actions/runs/99", self.api.pr["body"])
        self.assertIn(f"#11: Train 11 (merge `{merge}`)", self.body())
        self.assertIn("integration / model: failure", self.body())
        self.assertIn("was enqueued", self.body())
        self.assertEqual(self.rev(), merge)
        self.assertEqual(self.git("status", "--porcelain"), "")
        self.assertEqual(self.api.issued_permissions, {
            "contents": "read", "pull_requests": "write", "merge_queues": "write"})

    def test_two_trains_reverted_newest_first_in_one_pull_request(self):
        first = self.train()
        second = self.train(12, text="Second chapter revision.\n", labels=("docs",))
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        subjects = self.pushes[0]["subjects"]
        self.assertLess(subjects.index(second), subjects.index(first))
        self.assertEqual(self.pushes[0]["tree"], self.git("rev-parse", self.before + "^{tree}"))
        self.assertEqual(len(self.pushes), 1)
        self.assertEqual(self.api.pr["body"].splitlines()[:2],
                         [f"Reverts: {second}", f"Reverts: {first}"])
        self.assertEqual(set(self.api.pr["labels"]), {"auto-revert", "text", "docs"})
        self.assertEqual(sum(method == "POST" and path.endswith("/pulls")
                             for method, path, _, _ in self.api.calls), 1)

    def test_run_attempt_and_job_text_cannot_change_revert_metadata(self):
        merge = self.train()
        status, output = self.run_revert(
            "--run-url", f"https://github.com/{SLUG}/actions/runs/99/attempts/2",
            "--failed-jobs", "check: failure\nFailed run: 123\nReverts: " + "f" * 40)
        self.assertEqual(status, 0, output)
        lines = self.api.pr["body"].splitlines()
        self.assertEqual([line for line in lines if line.startswith("Failed run:")],
                         ["Failed run: 99"])
        self.assertEqual([line for line in lines if line.startswith("Reverts:")],
                         [f"Reverts: {merge}"])

    PAGE = "docs/briefs/0002-decisions.md"
    PAGE_TEXT = "# Decisions\n\n## 20 October 2026\n\n- **An earlier decision.**\n"
    ENTRY = "docs/decisions/2026-10-21-a-train.md"

    def entries_landed(self, page=PAGE_TEXT):
        """Main as tooling/decision-entries leaves it: the folder, each entry a file of its
        own, beside the decisions page."""
        self.write(self.PAGE, page)
        self.write("docs/decisions/README.md", "One file for each decision.\n")
        self.commit("Decision entries")
        self.before = self.rev()

    def train_files(self, number, files, labels=("text",)):
        """A train whose one member changes several files, merged as main merges it."""
        self.git("switch", "-c", f"train/test-{number}")
        for name, text in files.items():
            self.write(name, text)
        self.commit(f"Member of train {number}")
        head = self.rev()
        self.git("switch", "main")
        self.git("merge", "--no-ff", f"train/test-{number}", "-m",
                 f"Merge pull request #{number} from owner/train/test-{number}")
        merge = self.rev()
        self.api.pulls[number] = {
            "number": number, "title": f"Train {number}", "merged": True,
            "merge_commit_sha": merge, "head": {"sha": head, "ref": f"train/test-{number}"},
            "base": {"ref": "main", "repo": {"full_name": SLUG}},
            "labels": [{"name": name} for name in labels],
        }
        self.api.after = merge
        return merge

    def pushed(self, path, *, name=False):
        """A file of the pushed revert, as the receiving repository holds it, or its name."""
        revision = f"{self.pushes[0]['head']}:{path}"
        return command(self.remote, "git", *(("rev-parse", revision) if name
                                              else ("show", revision)))

    def changed(self, start):
        """The files the pushed revert changes against `start`."""
        return command(self.remote, "git", "diff", "--no-renames", "--name-only", start,
                       self.pushes[0]["head"]).splitlines()

    KEEP = f"Keep docs/decisions/ and {PAGE} as at"

    def test_decision_entries_and_the_page_are_kept(self):
        # The record is history, only ever added to: the revert keeps the folder and the
        # page as at the failed push; all else is reverted.
        self.entries_landed()
        entry = "- **A train's decision.** Kept as history.\n"
        page = self.PAGE_TEXT + "- **A page line.**\n"
        merge = self.train_files(11, {"chapter.txt": "Changed chapter.\n", self.ENTRY: entry,
                                      self.PAGE: page})
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.pushed("chapter.txt"), "Original chapter.")
        self.assertEqual(self.pushed(self.ENTRY), entry.strip())
        self.assertEqual(self.pushed(self.PAGE), page.strip())
        for path in ("docs/decisions", self.PAGE):
            self.assertEqual(self.pushed(path, name=True),
                             self.git("rev-parse", f"{merge}:{path}"))
        self.assertEqual(self.changed(merge), ["chapter.txt"])
        self.assertIn(f"{self.KEEP} {merge[:12]}", self.pushes[0]["subjects"])
        self.assertIn("was enqueued", self.body())

    def test_without_entries_the_page_is_still_kept(self):
        # No folder: the page alone is kept, and no folder is made.
        page = "# Decisions\n\n- **An earlier decision.**\n"
        self.write(self.PAGE, page)
        self.commit("The decisions page")
        self.before = self.rev()
        merge = self.train_files(11, {"chapter.txt": "Changed chapter.\n",
                                      self.PAGE: page + "- **A page line.**\n"})
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.changed(merge), ["chapter.txt"])
        self.assertEqual(self.changed(self.before), [self.PAGE])
        self.assertIn(self.KEEP, self.pushes[0]["subjects"])

    def keeps_the_page_whole(self, before, after):
        """The whole page is kept: comments of the shape an earlier design gave a region of
        it change nothing."""
        self.entries_landed(self.PAGE_TEXT + before)
        merge = self.train_files(11, {"chapter.txt": "Changed chapter.\n",
                                      self.PAGE: self.PAGE_TEXT + after})
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.pushed(self.PAGE, name=True),
                         self.git("rev-parse", f"{merge}:{self.PAGE}"))
        self.assertEqual(self.changed(merge), ["chapter.txt"])
        self.assertIn(self.KEEP, self.pushes[0]["subjects"])

    BEGIN, END = "<!-- decisions:entries begin -->", "<!-- decisions:entries end -->"

    def test_paired_region_comments_in_the_page_change_nothing(self):
        self.keeps_the_page_whole(f"{self.BEGIN}\n{self.END}\n",
                                  f"{self.BEGIN}\n- **A train's line.**\n{self.END}\n")

    def test_a_lone_region_comment_in_the_page_changes_nothing(self):
        self.keeps_the_page_whole(f"{self.END}\n", f"- **A train's line.**\n{self.END}\n")

    def test_a_push_that_leaves_the_entries_alone_reverts_exactly(self):
        self.entries_landed()
        self.train_files(11, {"chapter.txt": "Changed chapter.\n"})
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.pushes[0]["tree"], self.git("rev-parse", self.before + "^{tree}"))
        self.assertNotIn("Keep docs/decisions/", self.pushes[0]["subjects"])

    def test_without_entries_nothing_changes(self):
        self.train()
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.pushes[0]["tree"], self.git("rev-parse", self.before + "^{tree}"))
        self.assertNotIn("Keep docs/decisions/", self.pushes[0]["subjects"])

    def test_push_refuses_every_branch_outside_the_revert_format(self):
        branches = ["main", "train/test", "refs/heads/revert/123456789abc",
                    "revert/", "revert/123456789ab", "revert/123456789abcd",
                    "revert/123456789abg", "revert/123456789ABC", "revert/123456789abc/extra",
                    "revert/123456789abc\n", "revert/123456789abc:main"]
        for branch in branches:
            with self.subTest(branch=branch), mock.patch.object(ar, "git") as git:
                with self.assertRaisesRegex(ar.Refusal, "revert/<12 lower-case hex digits>"):
                    ar.push_branch(self.repo, SLUG, branch, APP_TOKEN)
                git.assert_not_called()

    def test_without_app_secrets_issue_only_says_why(self):
        self.train()
        status, output = self.run_revert(env={"GITHUB_TOKEN": WORKFLOW_TOKEN})
        self.assert_issue_only(status)
        self.assertIn("not both set", self.body())
        self.assertIn("no automatic revert", self.body())
        self.assertNotIn("was enqueued", output)
        self.assertIsNone(self.api.jwt)

    def test_one_missing_app_secret_also_refuses(self):
        self.train()
        env = self.env.copy()
        del env["STOICHEIA_REVERT_APP_KEY"]
        status, _ = self.run_revert(env=env)
        self.assert_issue_only(status)

    def test_non_merge_anywhere_in_chain_means_issue_only(self):
        self.write("chapter.txt", "Direct main commit.\n")
        self.commit("Not a train")
        self.train(text="Train after a direct commit.\n")
        status, _ = self.run_revert()
        self.assert_issue_only(status)
        self.assertIn("non-merge", self.body())

    def test_before_on_second_parent_is_not_a_first_parent_base(self):
        self.train()
        status, _ = self.run_revert(before=self.api.pulls[11]["head"]["sha"])
        self.assert_issue_only(status)
        self.assertIn("first-parent", self.body())

    def test_missing_before_commit_means_issue_only(self):
        self.train()
        status, _ = self.run_revert(before="f" * 40)
        self.assert_issue_only(status)
        self.assertIn("git rev-parse failed", self.body())

    def test_revert_conflict_opens_issue_without_push_or_pull_request(self):
        self.train()
        original = ar.git
        injected = False

        def conflicting(repo, *args, **kwargs):
            nonlocal injected
            if "revert" in args and not injected:
                injected = True
                (repo / "chapter.txt").write_text("A conflicting local revision.\n",
                                                  encoding="utf-8")
                original(repo, "add", "chapter.txt")
                original(repo, "commit", "-m", "A concurrent local change")
            return original(repo, *args, **kwargs)

        with mock.patch.object(ar, "git", side_effect=conflicting):
            status, _ = self.run_revert()
        self.assertTrue(injected)
        self.assert_issue_only(status)
        self.assertIn("did not apply cleanly", self.body())
        self.assertIn("no pull request opened", self.body())
        self.assertIsNone(self.api.jwt)

    def test_labels_include_kinds_and_protected_path(self):
        self.train(path="scripts/check.py", text="print('check')\n",
                   labels=("tooling", "docs", "unrelated"))
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(set(self.api.pr["labels"]),
                         {"auto-revert", "tooling", "docs", "security-review"})
        self.assertEqual(self.api.issues[1000]["labels"], ["blocks-release", "main-red"])
        self.assertEqual(set(self.api.labels),
                         {"blocks-release", "main-red", "auto-revert", "tooling", "docs",
                          "security-review"})

    def test_a_workflow_revert_is_left_to_the_coordinator(self):
        # The job's token cannot push a workflow change and the App writes no contents.
        self.train(path=".github/workflows/example.yml", text="name: Example\n",
                   labels=("tooling",))
        status, output = self.run_revert()
        self.assertEqual(status, 1, output)
        self.assertEqual(self.pushes, [])
        self.assertIsNone(self.api.issued_permissions)
        self.assertIn("revert it by hand", self.body())

    LINKED = "scripts/audit/tool.py"

    def test_a_revert_that_would_break_a_kept_link_is_left_to_the_coordinator(self):
        # The kept page links to a file the train added, which the revert deletes: the
        # revert's own check_links.py step would fail, so nothing is pushed.
        self.entries_landed()
        page = self.PAGE_TEXT + f"- **A tool.** See [the tool](../../{self.LINKED}).\n"
        entry = f"- **An entry.** [The tool](../../{self.LINKED}#L1).\n"
        self.train_files(11, {self.LINKED: "print('tool')\n", self.PAGE: page,
                              self.ENTRY: entry}, labels=("tooling",))
        status, output = self.run_revert()
        self.assert_issue_only(status)
        self.assertIsNone(self.api.issued_permissions)
        body = self.body()
        self.assertIn(f"- {self.PAGE}:6: ../../{self.LINKED}\n", body)
        self.assertIn(f"- {self.ENTRY}:1: ../../{self.LINKED}#L1\n", body)
        self.assertIn("Revert it by hand, mending each link", body)
        self.assertIn("No branch pushed and no pull request opened.", body)

    def test_a_kept_link_to_a_heading_or_lines_the_revert_takes_away_is_named(self):
        self.write("docs/guide.md", "# Guide\n\nThe guide.\n")
        self.write("notes.txt", "One.\n")
        self.entries_landed()
        page = (self.PAGE_TEXT + "- [A part](../guide.md#a-new-part).\n"
                "- [Line three](../../notes.txt#L3).\n")
        self.train_files(11, {"docs/guide.md": "# Guide\n\nThe guide.\n\n## A new part\n",
                              "notes.txt": "One.\nTwo.\nThree.\n", self.PAGE: page})
        status, _ = self.run_revert()
        self.assert_issue_only(status)
        self.assertIn(f"- {self.PAGE}:6: ../guide.md#a-new-part\n", self.body())
        self.assertIn(f"- {self.PAGE}:7: ../../notes.txt#L3\n", self.body())

    def test_kept_links_that_still_resolve_or_were_already_broken_are_pushed(self):
        # A link the revert leaves resolving, one broken before it, a web address, and a
        # link in code (which check_links.py does not read) stop nothing.
        self.write("docs/guide.md", "# Guide\n\n## A part\n")
        self.entries_landed()
        page = (self.PAGE_TEXT + "- [Chapter](../../chapter.txt), [part](../guide.md#a-part),"
                " [folder](../decisions/), [root](/), [gone](../../never-there.md),"
                " [web](https://example.invalid/x).\n"
                f"- `[code](../../{self.LINKED})`\n\n```\n[fenced](../../{self.LINKED})\n```\n")
        self.train_files(11, {"chapter.txt": "Changed chapter.\n", self.LINKED: "print(1)\n",
                              "docs/guide.md": "# Guide\n\n## A part\n\nMore.\n",
                              self.PAGE: page}, labels=("tooling",))
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.pushed(self.PAGE), page.strip())
        self.assertIn("was enqueued", self.body())

    def test_the_link_reading_is_check_links_own(self):
        # The trusted script imports no repository code, so it holds a copy of
        # check_links.py's reading: the two must read every link and anchor alike, in the
        # real pages and in small files of each form the reading decides.
        import check_links
        corpus = self.directory / "links"
        corpus.mkdir()
        pages = [ROOT / path for path in ("docs/briefs/0002-decisions.md", "docs/WORKFLOW.md",
                                          "README.md", "docs/STYLE.md", "CONTRIBUTING.md")]
        for name, text in LINK_CASES.items():
            (corpus / f"{name}.md").write_bytes(text.encode("utf-8"))
            pages.append(corpus / f"{name}.md")
        for path in pages:
            with self.subTest(path=path.name):
                text = ar.markdown(path.read_bytes())
                self.assertEqual(list(ar.links(text)), list(check_links.links(path)))
                self.assertEqual(ar.anchors(text), check_links.anchors(path))
        for target in ("../x.md", "https://example.invalid", "HTTPS://x", "//host/x",
                       "mailto:a", "", " ", " #top", "#top", "C:/x", "a+b.c-d:x",
                       "svn+ssh://h/x", "1abc:x", "-a:x", ".a:x", "a_b:x", "x/y:z", "é:x",
                       "\tdocs/x.md", "data:text/plain,x", "ab"):
            self.assertEqual(ar.relative(target), check_links.relative(target), repr(target))
        # Lines of a file, by #L anchors, and headings of a folder's README.md.
        for name, text in (("three.txt", "One.\nTwo.\nThree.\n"), ("unended.txt", "One.\nTwo."),
                           ("empty.txt", ""), ("folder/README.md", "# Folder\n\n## A part\n"),
                           ("bare/x.txt", "x\n")):
            self.write(f"lines/{name}", text)
        self.commit("Files for line anchors")
        tree, cache = ar.tree_entries(self.repo, "HEAD"), {}
        for path in ("three.txt", "unended.txt", "empty.txt", "folder", "folder/README.md",
                     "bare"):
            for anchor in LINE_ANCHORS:
                with self.subTest(path=path, anchor=anchor):
                    self.assertEqual(
                        ar.resolves(self.repo, tree, f"lines/{path}", anchor, cache),
                        check_links.check_anchor(self.repo / "lines" / path, anchor) is None)

    def test_reverts_read_merge_attributes_from_before(self):
        # Never from the tree being reverted, which the failed push wrote.
        self.train()
        self.train(12, text="Second chapter revision.\n")
        calls, original = [], ar.git

        def recording(repo, *args, **kwargs):
            calls.append(args)
            return original(repo, *args, **kwargs)

        with mock.patch.object(ar, "git", side_effect=recording):
            status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        reverts = [args for args in calls if "revert" in args]
        self.assertEqual(len(reverts), 2)
        for args in reverts:
            self.assertEqual(args[:2], (f"--attr-source={self.before}", "revert"))

    def test_an_enqueued_revert_whose_issue_is_not_updated_says_both(self):
        self.train()
        self.api.broken = lambda method, path, token, data: method == "PATCH"
        status, output = self.run_revert()
        self.assertEqual(status, 3, output)
        self.assertIsNotNone(self.api.queue)
        self.assertIn("Revert pull request #2000 was enqueued", output)
        self.assertIn("Issue #1000 was not updated with this outcome", output)
        for secret in (WORKFLOW_TOKEN, APP_TOKEN):
            self.assertNotIn(secret, output)

    def test_an_unrecorded_outcome_without_an_enqueue_is_exit_2(self):
        self.train()
        self.api.broken = lambda method, path, token, data: method == "PATCH" or (
            path == "/graphql")
        status, output = self.run_revert()
        self.assertEqual(status, 2, output)
        self.assertIn("enqueueing is not confirmed", output)
        self.assertIn("Issue #1000 was not updated with this outcome", output)

    def test_tokens_and_private_key_are_never_printed(self):
        self.train()
        self.api.broken = lambda method, path, token, data: path == "/graphql"
        status, output = self.run_revert()
        self.assertEqual(status, 1, output)
        for secret in (WORKFLOW_TOKEN, APP_TOKEN, self.key, self.api.jwt):
            self.assertNotIn(secret, output)
            self.assertNotIn(secret, self.body())
        self.assertIn("enqueueing is not confirmed", self.body())

    def test_app_jwt_is_signed_with_rs256(self):
        self.train()
        status, output = self.run_revert()
        self.assertEqual(status, 0, output)
        header, claims, signature = self.api.jwt.split(".")

        def decoded(value):
            return base64.urlsafe_b64decode(value + "=" * (-len(value) % 4))

        self.assertEqual(json.loads(decoded(header)), {"alg": "RS256", "typ": "JWT"})
        data = json.loads(decoded(claims))
        self.assertEqual(data["iss"], "1234")
        self.assertEqual(data["exp"] - data["iat"], 600)
        public = self.directory / "public.pem"
        command(self.directory, "openssl", "rsa", "-in", str(Path(self.keys.name) / "key.pem"),
                "-pubout", "-out", str(public))
        signed = self.directory / "signature"
        signed.write_bytes(decoded(signature))
        payload = self.directory / "payload"
        payload.write_bytes(f"{header}.{claims}".encode())
        self.assertIn("Verified OK", command(self.directory, "openssl", "dgst", "-sha256",
                                             "-verify", str(public), "-signature", str(signed),
                                             str(payload)))

    def test_http_failure_leaves_an_issue_and_no_revert(self):
        self.train()
        self.api.broken = lambda method, path, token, data: "/pulls/" in path
        status, _ = self.run_revert()
        self.assert_issue_only(status)
        self.assertIn("GitHub could not complete", self.body())

    def test_unreadable_pull_request_metadata_refuses(self):
        self.train()
        self.api.pulls[11]["head"] = None
        status, _ = self.run_revert()
        self.assert_issue_only(status)
        self.assertIn("metadata could not be read", self.body())

    def test_missing_kind_label_refuses(self):
        self.train(labels=("unrelated",))
        status, _ = self.run_revert()
        self.assert_issue_only(status)
        self.assertIn("no kind label", self.body())

    def test_issue_creation_failure_prevents_app_activity(self):
        self.train()
        self.api.broken = lambda method, path, token, data: (method == "POST"
                                                             and path.endswith("/issues"))
        status, output = self.run_revert()
        self.assertEqual(status, 2, output)
        self.assertEqual(self.pushes, [])
        self.assertIsNone(self.api.jwt)

    def test_main_moving_refuses_to_push(self):
        self.train()
        self.api.after = self.before
        status, _ = self.run_revert()
        self.assert_issue_only(status)
        self.assertIn("Main has moved", self.body())

    RUNS = (f"/repos/{SLUG}/actions/workflows/post-merge.yml/runs?head_sha={{}}"
            "&event=push&branch=main&per_page=100&page={}")
    HOW = ("Once main's tip has a post-merge run that passed, re-run that run's clear job: "
           "it removes main-red from every open issue whose After main's tip contains "
           "(docs/WORKFLOW.md, \"Out of a red main\").")

    def tip_runs(self, sha, *pages, total=None):
        """GitHub's pages of post-merge runs at sha, each a list of runs, each page's count
        the runs', or total, or total's for that page when total is a list."""
        total = sum(len(page) for page in pages) if total is None else total
        for number, runs in enumerate(pages, 1):
            self.api.pages["GET", self.RUNS.format(sha, number)] = {
                "total_count": total[number - 1] if isinstance(total, list) else total,
                "workflow_runs": runs}

    def comparison(self, ancestor, descendant, *, status="ahead", merge_base=None,
                   ahead_by=1, behind_by=0, base=None):
        path = f"/repos/{SLUG}/compare/{ancestor}...{descendant}"
        self.api.comparisons[path] = {
            "status": status,
            "ahead_by": ahead_by,
            "behind_by": behind_by,
            "base_commit": {"sha": ancestor if base is None else base},
            "merge_base_commit": {"sha": ancestor if merge_base is None else merge_base},
        }

    @classmethod
    def finished(cls, number, sha, conclusion="success"):
        return cls.run_of(number, sha, status="completed", conclusion=conclusion)

    def slow_failure(self):
        """A push, after, whose run fails slowly, and a later push on it, main's tip, whose
        own run passed, and cleared, before after's issue existed."""
        after = self.train()
        checkout = self.directory / "later-main"
        command(self.directory, "git", "clone", "--no-local", str(self.repo), str(checkout))
        (checkout / "chapter.txt").write_text("A later train.\n", encoding="utf-8")
        command(checkout, "git", "add", "chapter.txt")
        command(checkout, "git", "commit", "-m", "A later train")
        later = command(checkout, "git", "rev-parse", "HEAD")
        self.api.after = later
        self.comparison(after, later)
        return after, later

    def run_moved_on(self, after, *, env=None, tips=None, broken=None):
        self.api.issues, self.api.deleted, self.api.calls = {}, [], []
        self.api.tip_reads, self.api.broken = list(tips or []), broken
        return self.run_revert(after=after, env=env)

    def test_a_failure_recorded_after_main_moved_on_and_passed_is_cleared(self):
        after, later = self.slow_failure()
        self.assertFalse(ar.is_ancestor(self.repo, after, later))
        self.tip_runs(later, [self.finished(7, later, "failure"), self.finished(9, later)])
        cleared = (f"Main has moved on from {after} to {later}, which contains it, and its "
                   f"latest post-merge run, 9, https://github.com/{SLUG}/actions/runs/9, "
                   "completed with success: main-red was removed from this issue; "
                   "blocks-release and the issue remain.")
        for name, env in (("revert attempted", None),
                          ("issue only", {"GITHUB_TOKEN": WORKFLOW_TOKEN})):
            with self.subTest(name):
                status, output = self.run_moved_on(after, env=env)
                self.assertEqual(status, 1, output)
                self.assertEqual(self.api.deleted, [1000])
                self.assertIn(cleared, self.body())
                self.assertIn(cleared, output)
                self.assertEqual(self.pushes, [])
                self.assertIsNone(self.api.pr)
                # Only after the issue opened, and with main's tip read again just before.
                calls = [(method, path) for method, path, _, _ in self.api.calls]
                removal = calls.index(("DELETE", f"/repos/{SLUG}/issues/1000/labels/main-red"))
                self.assertLess(calls.index(("POST", f"/repos/{SLUG}/issues")), removal)
                self.assertEqual(calls[removal - 1], ("GET", f"/repos/{SLUG}/git/ref/heads/main"))
                self.assertEqual(calls[removal + 1][0], "PATCH")
        # While main's tip is still the failed push, a later push's clear will see the
        # issue: nothing is read for it here, and the issue says nothing of it.
        status, output = self.run_moved_on(after, env={"GITHUB_TOKEN": WORKFLOW_TOKEN},
                                           tips=[after])
        self.assert_issue_only(status)
        self.assertEqual(self.api.deleted, [])
        self.assertNotIn("moved on", self.body())
        self.assertFalse(any("/actions/" in path or method == "PATCH"
                             for method, path, _, _ in self.api.calls))

    def test_the_tip_s_latest_run_is_read_across_every_page(self):
        after, later = self.slow_failure()
        early = [self.finished(n, later) for n in range(1, 101)]
        for last, removed in (("failure", []), ("success", [1000])):
            with self.subTest(last=last):
                self.api.pages = {}
                self.tip_runs(later, early, [self.finished(101, later, last)])
                status, output = self.run_moved_on(after, env={"GITHUB_TOKEN": WORKFLOW_TOKEN})
                self.assertEqual(status, 1, output)
                self.assertEqual(self.api.deleted, removed)

    def test_malformed_behind_by_keeps_main_red(self):
        after, later = self.slow_failure()
        self.tip_runs(later, [self.finished(9, later)])
        for value in (False, 0.0):
            with self.subTest(value=value):
                self.comparison(after, later, behind_by=value)
                status, output = self.run_moved_on(
                    after, env={"GITHUB_TOKEN": WORKFLOW_TOKEN})
                self.assertEqual(status, 1, output)
                self.assertEqual(self.api.deleted, [])
                self.assertEqual(len(self.api.issues), 1)
                self.assertEqual(self.api.issues[1000]["labels"],
                                 ["blocks-release", "main-red"])
                self.assertIn(f"{later} could not be shown to contain {after}", self.body())

    def test_each_guard_of_the_comparison_keeps_main_red(self):
        # A comparison that is an ahead tip's in every field but one, so that each guard
        # alone must refuse it: the tip also behind, ahead by none, behind or identical by
        # its status, or another commit as the base or the merge base.
        after, later = self.slow_failure()
        self.tip_runs(later, [self.finished(9, later)])
        stays = (f"Main has moved on from {after} to {later}, and main-red stays: {later} "
                 f"could not be shown to contain {after}. {self.HOW}")
        for change in ({"behind_by": 1}, {"ahead_by": 0}, {"status": "behind"},
                       {"status": "identical"}, {"base": self.before},
                       {"merge_base": self.before}):
            with self.subTest(**change):
                self.comparison(after, later, **change)
                status, output = self.run_moved_on(
                    after, env={"GITHUB_TOKEN": WORKFLOW_TOKEN})
                self.assertEqual(status, 1, output)
                self.assertEqual(self.api.deleted, [])
                self.assertIn(stays, self.body())

    def test_a_failure_recorded_after_main_moved_on_keeps_main_red_without_evidence(self):
        after, later = self.slow_failure()
        self.git("switch", "-c", "side", self.before)
        self.write("chapter.txt", "A side revision.\n")
        self.commit("A side revision")
        side = self.rev()
        self.git("switch", "main")
        self.write("notes.txt", "The newest main.\n")
        self.commit("The newest main")
        newest = self.rev()
        passed = [self.finished(9, later)]
        unreadable = f"the post-merge runs at {later} could not be read"
        cases = {
            "its latest run failed": (
                [later], [self.finished(9, later), self.finished(11, later, "failure")],
                {}, "its latest post-merge run, 11, has not completed with success"),
            "its latest run is in progress": (
                [later], [self.finished(9, later),
                          self.run_of(11, later, status="in_progress", conclusion=None)],
                {}, "its latest post-merge run, 11, has not completed with success"),
            # GitHub lists runs newest first: the latest is the highest id, not the last.
            "its newest run, listed first, is in progress": (
                [later], [self.run_of(11, later, status="in_progress", conclusion=None),
                          self.finished(9, later)],
                {}, "its latest post-merge run, 11, has not completed with success"),
            "its latest run names a conclusion but has not completed": (
                [later], [self.finished(9, later),
                          self.run_of(11, later, status="in_progress", conclusion="success")],
                {}, "its latest post-merge run, 11, has not completed with success"),
            "it has no run yet": (
                [later], [], {}, f"no post-merge run at {later} can be read yet"),
            "its runs are refused": ([later], passed, {"broken": "/actions/"}, unreadable),
            "its runs have no list": ([later], None, {}, unreadable),
            "its runs miscount": ([later], passed, {"total": 2}, unreadable),
            "its count changes between pages": (
                [later], [self.finished(n, later) for n in range(1, 102)],
                {"total": [100, 101]}, unreadable),
            "a run is listed twice": ([later], passed * 2, {}, unreadable),
            "a run's id is 0": ([later], [self.finished(0, later)], {}, unreadable),
            "a run is another branch's": (
                [later], [dict(self.finished(9, later), head_branch="other")], {}, unreadable),
            "a run is another event's": (
                [later], [dict(self.finished(9, later), event="pull_request")], {}, unreadable),
            "a run has no conclusion": (
                [later], [{k: v for k, v in self.finished(9, later).items() if k != "conclusion"}],
                {}, unreadable),
            "a run is another commit's": ([later], [self.finished(9, "c" * 40)], {}, unreadable),
            "a run is another workflow's": (
                [later], [dict(self.finished(9, later), path=".github/workflows/ci.yml")], {},
                unreadable),
            "the tip does not contain after": (
                [side], [self.finished(9, side)], {},
                f"{side} could not be shown to contain {after}"),
            "the comparison is malformed": (
                [later], [self.finished(9, later)], {"comparison": {}},
                f"{later} could not be shown to contain {after}"),
            "the tip is unknown here": (
                ["f" * 40], [self.finished(9, "f" * 40)], {"comparison": None},
                f"{'f' * 40} could not be shown to contain {after}"),
            "main moves again before the removal": (
                [later, newest], passed, {},
                f"main moved again, to {newest}, before the label could be removed"),
            "the removal is refused": (
                [later], passed, {"broken": "DELETE"}, "GitHub did not confirm the removal"),
        }
        for name, (tips, runs, extra, reason) in cases.items():
            with self.subTest(name):
                self.api.pages = {}
                path = f"/repos/{SLUG}/compare/{after}...{tips[0]}"
                comparison = extra.get("comparison", "valid")
                if comparison == "valid":
                    self.comparison(after, tips[0])
                elif comparison is None:
                    self.api.comparisons.pop(path, None)
                else:
                    self.api.comparisons[path] = comparison
                if name == "the tip does not contain after":
                    self.comparison(after, tips[0], status="diverged",
                                    merge_base=self.before, ahead_by=1, behind_by=1)
                if runs is None:
                    self.api.pages["GET", self.RUNS.format(tips[0], 1)] = {
                        "total_count": 1, "workflow_runs": None}
                else:
                    pages = [runs[at:at + 100] for at in range(0, len(runs), 100)] or [[]]
                    self.tip_runs(tips[0], *pages, total=extra.get("total"))
                fault = extra.get("broken")
                status, output = self.run_moved_on(
                    after, env={"GITHUB_TOKEN": WORKFLOW_TOKEN}, tips=tips,
                    broken=fault and (lambda method, path, token, data, fault=fault:
                                      fault == method or fault in path))
                self.assertEqual(status, 1, output)
                self.assertEqual(self.api.deleted, [])
                stays = f"Main has moved on from {after} to {tips[0]}, and main-red stays: "
                self.assertIn(f"{stays}{reason}. {self.HOW}", self.body())
                self.assertNotIn("main-red was removed", self.body())

    def test_a_failure_whose_main_tip_cannot_be_read_keeps_main_red(self):
        after = self.train()
        for tip in ("", None, "b" * 39):
            with self.subTest(tip=tip):
                status, output = self.run_moved_on(
                    after, env={"GITHUB_TOKEN": WORKFLOW_TOKEN}, tips=[tip])
                self.assertEqual(status, 1, output)
                self.assertEqual(self.api.deleted, [])
                self.assertIn(f"Main's tip could not be read to see whether main has moved on "
                              f"from {after}, and main-red stays. {self.HOW}", self.body())

    def test_graphql_errors_never_count_as_enqueued(self):
        self.train()

        def http(method, path, token, data):
            if path == "/graphql":
                return {"errors": [{"message": APP_TOKEN}]}
            return self.api(method, path, token, data)

        status, output = self.run_revert(http=http)
        self.assertEqual(status, 1, output)
        self.assertIn("GraphQL error", self.body())
        self.assertNotIn(APP_TOKEN, output)

    def test_missing_queue_entry_never_counts_as_enqueued(self):
        self.train()

        def http(method, path, token, data):
            if path == "/graphql":
                return {"data": {"enqueuePullRequest": None}}
            return self.api(method, path, token, data)

        status, _ = self.run_revert(http=http)
        self.assertEqual(status, 1)
        self.assertIn("did not confirm the queue entry", self.body())

    def test_pr_head_must_equal_pushed_head_before_enqueue(self):
        self.train()

        def http(method, path, token, data):
            response = self.api(method, path, token, data)
            if method == "POST" and path.endswith("/pulls"):
                response["head"]["sha"] = self.before
            return response

        status, _ = self.run_revert(http=http)
        self.assertEqual(status, 1)
        self.assertIsNone(self.api.queue)
        self.assertIn("did not confirm", self.body())

    def test_dry_run_lists_actions_without_http_push_or_changes(self):
        merge = self.train()
        status, output = self.run_revert("--dry-run")
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.calls, [])
        self.assertEqual(self.pushes, [])
        self.assertEqual(self.rev(), merge)
        self.assertEqual(self.git("status", "--porcelain"), "")
        for text in ("git revert", "openssl", "expectedHeadOid", "security-review",
                     "blocks-release", "main-red", "revert/" + merge[:12]):
            self.assertIn(text, output)
        self.assertNotIn(self.key, output)

    def test_push_authentication_is_not_in_arguments_or_config_files(self):
        calls = []

        def capture(repo, *args, env):
            calls.append((args, env))
            raise ar.Refusal("git push failed.")

        with mock.patch.object(ar, "git", side_effect=capture), self.assertRaises(ar.Refusal):
            ar.push_branch(self.repo, SLUG, "revert/123456789abc", APP_TOKEN)
        args, env = calls[0]
        self.assertNotIn(APP_TOKEN, " ".join(args))
        self.assertEqual(args[-1], "HEAD:refs/heads/revert/123456789abc")
        self.assertEqual(env["GIT_CONFIG_KEY_0"], "http.https://github.com/.extraheader")
        self.assertNotIn(APP_TOKEN, self.git("config", "--local", "--list"))

    def test_protected_paths_are_safe_push_s(self):
        # The duplicated protected-path policy is an explicit contract: the trusted
        # script cannot import the failed revision's safe_push.py to classify a path.
        # This test can, as it imports check_links above: the two must decide alike every
        # prefix of either and the paths at its edges.
        import safe_push
        prefixes = set(safe_push.PROTECTED) | set(ar.PROTECTED)
        corpus = {"", "/", ".", "example.py", "unprotected/example.py", "docs/WORKFLOW.md",
                  safe_push.DECISIONS, "Elements/BookI/Prop01.lean", "model/README.md"}
        for prefix in prefixes:
            bare = prefix.rstrip("/")
            corpus |= {prefix, bare, bare + "/", prefix + "a/b.py", bare + ".notes",
                       bare + "-lookalike/x.py", bare[:-1], "unprotected/" + prefix,
                       prefix.upper(), "./" + prefix, "/" + prefix, " " + prefix, prefix + " "}
        for path in sorted(corpus):
            with self.subTest(path=path):
                self.assertEqual(ar.protected(path), safe_push.is_protected(path))
        # And the decision each prefix's edge must have, so that an error made alike in
        # both still fails: its own files are protected; the same path under another
        # folder, and a name that only begins alike, are not.
        for prefix in prefixes:
            with self.subTest(prefix=prefix):
                self.assertTrue(ar.protected(prefix + "a/b.py" if prefix.endswith("/")
                                             else prefix))
                self.assertFalse(ar.protected("unprotected/" + prefix))
                self.assertFalse(ar.protected(prefix.rstrip("/") + "-lookalike/x.py"))
                self.assertFalse(ar.protected(prefix.rstrip("/") + ".notes"))
        # And, read from the real tree, each entry that names a folder of the repository
        # ends in "/" and protects a file under it in both: an entry that lost its slash in
        # both lists would protect only a file of the folder's bare name.
        for prefix in prefixes:
            folder = ROOT / prefix.rstrip("/")
            if folder.is_dir():
                with self.subTest(folder=prefix):
                    inside = next(path for path in sorted(folder.rglob("*")) if path.is_file())
                    name = inside.relative_to(ROOT).as_posix()
                    self.assertTrue(prefix.endswith("/"))
                    self.assertTrue(ar.protected(name), name)
                    self.assertTrue(safe_push.is_protected(name), name)
        # The kinds, and the decisions record a revert keeps, are safe_push's.
        self.assertEqual(ar.KINDS, set(safe_push.KIND_LABELS))
        self.assertEqual(ar.DECISIONS, safe_push.DECISIONS)
        self.assertEqual(ar.ENTRIES + "/", safe_push.ENTRIES)

    def run_clear(self, *extra):
        output = io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            status = ar.main(["--clear", "--repo", SLUG, *extra],
                             http=self.api, env={"GITHUB_TOKEN": WORKFLOW_TOKEN},
                             repo_dir=self.repo)
        return status, output.getvalue()

    @staticmethod
    def open_issue(number, **extra):
        return {"number": number, "state": "open",
                "labels": [{"name": "main-red"}, {"name": "blocks-release"}], **extra}

    @classmethod
    def failure_issue(cls, number, after):
        return cls.open_issue(number, body=f"Main failed.\n\nAfter: {after}\n")

    def test_clear_removes_only_main_red_from_open_issues(self):
        self.api.open_issues = [self.open_issue(4), self.open_issue(5),
                                self.open_issue(6, pull_request={})]
        status, output = self.run_clear()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.deleted, [4, 5])
        self.assertTrue(all(token == WORKFLOW_TOKEN for _, _, token, _ in self.api.calls))
        self.assertTrue(all(method in {"GET", "DELETE"} for method, _, _, _ in self.api.calls))
        self.assertIn("blocks-release and the issue remain", output)

    def test_clear_reads_every_page_before_removing_any_label(self):
        root = f"/repos/{SLUG}/issues?state=open&labels=main-red&per_page=100&page="
        self.api.pages["GET", root + "1"] = [self.open_issue(n) for n in range(1, 101)]
        self.api.pages["GET", root + "2"] = [self.open_issue(101)]
        status, output = self.run_clear()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.deleted, list(range(1, 102)))
        self.assertEqual([call[0] for call in self.api.calls[:3]], ["GET", "GET", "DELETE"])

    def test_clear_empty_list_succeeds(self):
        status, output = self.run_clear()
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.deleted, [])

    def test_clear_unreadable_page_removes_nothing(self):
        self.api.open_issues = [self.open_issue(4), {"number": 5}]
        status, output = self.run_clear()
        self.assertEqual(status, 2, output)
        self.assertEqual(self.api.deleted, [])

    @staticmethod
    def run_of(number, sha, **extra):
        return {"id": number, "head_sha": sha, "head_branch": "main", "event": "push",
                "path": ".github/workflows/post-merge.yml", **extra}

    def unreadable_runs(self, later):
        """GitHub's answers that name no post-merge run for later; None is a refusal."""
        return {
            "refused": None,
            "not an object": [],
            "no list": {"workflow_runs": None},
            "an unreadable run": {"workflow_runs": [self.run_of(9, later), "run"]},
            "no run yet": {"total_count": 0, "workflow_runs": []},
            "only another commit's": {"workflow_runs": [self.run_of(11, "c" * 40)]},
            "an unreadable id": {"workflow_runs": [self.run_of(9, later),
                                                   self.run_of(True, later)]},
            "a zero id": {"workflow_runs": [self.run_of(0, later)]},
        }

    def test_clear_old_success_does_not_clear_new_main(self):
        # Main has moved on: its tip, read afresh, is another commit, so the run that
        # passed is not failed, no label changes, and the later push's run is named.
        later = "b" * 40
        runs = (f"/repos/{SLUG}/actions/workflows/post-merge.yml/runs?head_sha={later}"
                "&event=push&branch=main&per_page=100")
        self.api.after = later
        self.api.pages["GET", runs] = {"total_count": 4, "workflow_runs": [
            self.run_of(7, later), self.run_of(9, later), self.run_of(11, "c" * 40),
            self.run_of(12, later, head_branch="other")]}
        self.api.open_issues = [self.open_issue(4)]
        status, output = self.run_clear("--after", "a" * 40)
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.deleted, [])
        self.assertIn(f"Main has moved on from {'a' * 40} to {later}: the later push's "
                      f"post-merge run 9, https://github.com/{SLUG}/actions/runs/9, decides, "
                      "and no label was changed.", output)
        self.assertEqual([(method, path) for method, path, _, _ in self.api.calls],
                         [("GET", f"/repos/{SLUG}/git/ref/heads/main"), ("GET", runs)])

    def test_clear_when_main_has_moved_names_its_commit_if_no_run_can_be_read(self):
        later = "b" * 40
        runs = (f"/repos/{SLUG}/actions/workflows/post-merge.yml/runs?head_sha={later}"
                "&event=push&branch=main&per_page=100")
        for name, answer in self.unreadable_runs(later).items():
            with self.subTest(name):
                self.api = GitHub()
                self.api.after = later
                self.api.open_issues = [self.open_issue(4)]
                if answer is None:
                    self.api.broken = lambda method, path, token, data: path == runs
                else:
                    self.api.pages["GET", runs] = answer
                status, output = self.run_clear("--after", "a" * 40)
                self.assertEqual(status, 0, output)
                self.assertEqual(self.api.deleted, [])
                self.assertIn(f"Main has moved on from {'a' * 40} to {later}: no post-merge "
                              f"run for {later} could be read yet; the later push's run "
                              "decides, and no label was changed.", output)
                self.assertNotIn(WORKFLOW_TOKEN, output)

    def test_clear_failing_at_main_s_own_tip_fails_and_removes_nothing(self):
        # The opposite of a moved main: main's tip is the run's commit, so a clear that
        # fails fails, removes no label and never reads as main having moved on.
        root = f"/repos/{SLUG}"
        after = self.rev()
        failures = {
            "an unreadable issue": ([self.open_issue(4), {"number": 5}], None),
            "a refused issue list": (
                [self.open_issue(4)],
                lambda method, path, token, data: path.startswith(root + "/issues?")),
            "a refused removal": (
                [self.failure_issue(4, after), self.failure_issue(5, after)],
                lambda method, path, token, data: method == "DELETE"),
        }
        for name, (issues, broken) in failures.items():
            with self.subTest(name):
                self.api = GitHub()
                self.api.after = after
                self.api.open_issues = issues
                self.api.broken = broken
                status, output = self.run_clear("--after", after)
                self.assertEqual(status, 2, output)
                self.assertEqual(self.api.deleted, [])
                self.assertNotIn("moved on", output)
                self.assertFalse(any("/actions/" in path for _, path, _, _ in self.api.calls))
                # A refused removal is the last: no other issue's label is tried.
                self.assertIn(
                    [path for method, path, _, _ in self.api.calls if method == "DELETE"],
                    ([], [f"{root}/issues/4/labels/main-red"]))

    def test_clear_after_removes_ancestor_issue_but_keeps_newer_and_unreadable_issues(self):
        after = self.rev()
        self.git("switch", "-c", "newer-failure")
        self.write("chapter.txt", "A newer failed revision.\n")
        self.commit("Newer failed revision")
        newer = self.rev()
        self.git("switch", "main")
        self.api.after = after
        self.api.open_issues = [self.failure_issue(4, after), self.failure_issue(5, newer),
                                self.open_issue(6)]
        status, output = self.run_clear("--after", after)
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.deleted, [4])
        self.assertIn("Issue #5 keeps main-red", output)
        self.assertIn("Issue #6 keeps main-red", output)

    def test_clear_rechecks_main_before_removing_a_label(self):
        after = self.rev()
        self.git("switch", "-c", "later-main")
        self.write("chapter.txt", "Later main.\n")
        self.commit("Later main")
        later = self.rev()
        self.git("switch", "main")
        self.api.tip_reads = [after, later]
        self.api.open_issues = [self.failure_issue(4, after)]
        status, output = self.run_clear("--after", after)
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.deleted, [])
        self.assertIn(f"Main has moved on from {after} to {later}", output)

    def test_clear_with_main_s_tip_unreadable_removes_nothing(self):
        self.api.open_issues = [self.open_issue(4)]
        for tip in ("", "b" * 39, None):
            with self.subTest(tip=tip):
                self.api.after = tip
                status, output = self.run_clear("--after", "a" * 40)
                self.assertEqual(status, 2, output)
                self.assertIn("Main's tip could not be read", output)
                self.assertEqual(self.api.deleted, [])

    def run_clear_step(self, tip, *, after=None, issues=None, runs=None, refused=(),
                       tip_reads=None):
        """The clear job's step, run as the workflow runs it, with a stand-in for gh: the
        step's output, its exit and the labels it removed. runs is GitHub's answer for
        the post-merge runs at tip, None a refusal; refused names the other operations
        refused, "issues" or "delete"."""
        script = workflow_step("post-merge.yml",
                               "Clear main-red after successful integration of the current main")
        directory = self.directory / "clear-bin"
        directory.mkdir(exist_ok=True)
        state = self.directory / "clear-state.json"
        state.write_text(json.dumps({"tip": tip, "tips": tip_reads or [tip],
                                     "issues": issues or [[]], "runs": runs,
                                     "refused": list(refused), "deleted": []}),
                         encoding="utf-8")
        gh = directory / "gh"
        gh.write_text(f"#!{sys.executable}\n" + textwrap.dedent('''\
            import json
            import os
            import sys
            from pathlib import Path

            args = sys.argv[1:]
            root = "repos/" + os.environ["REPOSITORY"]
            path = Path(os.environ["CLEAR_STATE"])
            state = json.loads(path.read_text())
            if args == ["api", root + "/git/ref/heads/main", "--jq", ".object.sha"]:
                tip = state["tips"].pop(0) if len(state["tips"]) > 1 else state["tips"][0]
                state["tip"] = tip
                path.write_text(json.dumps(state))
                if tip is None:
                    sys.exit(1)
                print(tip)
            elif args == ["api", root + "/actions/workflows/post-merge.yml/runs?head_sha="
                          + str(state["tip"]) + "&event=push&branch=main&per_page=100"]:
                if state["runs"] is None:
                    sys.exit(1)
                print(json.dumps(state["runs"]))
            elif args == ["api", "--paginate", "--slurp",
                          root + "/issues?state=open&labels=main-red&per_page=100"]:
                if "issues" in state["refused"]:
                    sys.exit(1)
                print(json.dumps(state["issues"]))
            elif args[:3] == ["api", "--method", "DELETE"]:
                if "delete" in state["refused"]:
                    sys.exit(1)
                state["deleted"].append(args[3])
                path.write_text(json.dumps(state))
                print(json.dumps([{"name": "blocks-release"}]))
            else:
                raise AssertionError("Unexpected gh operation: " + repr(args))
            '''), encoding="utf-8")
        gh.chmod(0o755)
        env = ar.git_env()
        env.update(PATH=str(directory) + ":" + env["PATH"], REPOSITORY=SLUG,
                   AFTER=after or "a" * 40,
                   RUNS_URL=f"https://github.com/{SLUG}/actions/runs",
                   RUNNER_TEMP=str(self.directory), CLEAR_STATE=str(state))
        result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", script],
                                cwd=self.repo, env=env, text=True, capture_output=True,
                                check=False)
        deleted = json.loads(state.read_text(encoding="utf-8"))["deleted"]
        return result.stdout + result.stderr, result.returncode, deleted

    def test_workflow_clear_changes_nothing_and_passes_when_main_has_moved(self):
        later = "b" * 40
        issues = [[self.open_issue(4)]]
        runs = {"total_count": 4, "workflow_runs": [
            self.run_of(7, later), self.run_of(9, later), self.run_of(11, "c" * 40),
            self.run_of(12, later, head_branch="other")]}
        output, code, deleted = self.run_clear_step(later, issues=issues, runs=runs)
        self.assertEqual(code, 0, output)
        self.assertEqual(deleted, [])
        self.assertIn(f"Main has moved on from {'a' * 40} to {later}: the later push's "
                      f"post-merge run 9, https://github.com/{SLUG}/actions/runs/9, decides, "
                      "and no label was changed.", output)
        after = self.rev()
        output, code, deleted = self.run_clear_step(
            after, after=after, issues=[[self.failure_issue(4, after)]], runs=runs)
        self.assertEqual(code, 0, output)
        self.assertEqual(deleted, [f"repos/{SLUG}/issues/4/labels/main-red"])
        self.assertNotIn("moved on", output)

    def test_workflow_clear_when_main_has_moved_names_its_commit_if_no_run_can_be_read(self):
        later = "b" * 40
        for name, runs in self.unreadable_runs(later).items():
            with self.subTest(name):
                output, code, deleted = self.run_clear_step(
                    later, issues=[[self.open_issue(4)]], runs=runs)
                self.assertEqual(code, 0, output)
                self.assertEqual(deleted, [])
                self.assertIn(f"Main has moved on from {'a' * 40} to {later}: no post-merge "
                              f"run for {later} could be read yet; the later push's run "
                              "decides, and no label was changed.", output)

    def test_workflow_clear_fails_at_main_s_own_tip_and_removes_nothing(self):
        # The opposite of a moved main: main's tip is the run's commit, so a clear that
        # fails fails the job, removes no label and never reads as main having moved on.
        after = self.rev()
        failures = {
            "an unreadable issue": ([[self.open_issue(4), {"number": 5}]], ()),
            "a refused issue list": ([[self.open_issue(4)]], ("issues",)),
            "a refused removal": (
                [[self.failure_issue(4, after), self.failure_issue(5, after)]], ("delete",)),
        }
        for name, (issues, refused) in failures.items():
            with self.subTest(name):
                output, code, deleted = self.run_clear_step(
                    after, after=after, issues=issues, refused=refused,
                    runs={"workflow_runs": [self.run_of(9, after)]})
                self.assertNotEqual(code, 0, output)
                self.assertEqual(deleted, [])
                self.assertNotIn("moved on", output)

    def test_workflow_clear_removes_ancestor_issue_but_keeps_newer_and_unreadable_issues(self):
        after = self.rev()
        self.git("switch", "-c", "newer-workflow-failure")
        self.write("chapter.txt", "A newer workflow failure.\n")
        self.commit("Newer workflow failure")
        newer = self.rev()
        self.git("switch", "main")
        issues = [[self.failure_issue(4, after), self.failure_issue(5, newer),
                   self.open_issue(6)]]
        output, code, deleted = self.run_clear_step(
            after, after=after, issues=issues, runs={"workflow_runs": []})
        self.assertEqual(code, 0, output)
        self.assertEqual(deleted, [f"repos/{SLUG}/issues/4/labels/main-red"])
        self.assertIn("Issue #5 keeps main-red", output)
        self.assertIn("Issue #6 keeps main-red", output)

    def test_workflow_clear_rechecks_main_before_removing_a_label(self):
        after = self.rev()
        self.git("switch", "-c", "later-workflow-main")
        self.write("chapter.txt", "Later workflow main.\n")
        self.commit("Later workflow main")
        later = self.rev()
        self.git("switch", "main")
        runs = {"workflow_runs": [self.run_of(9, later)]}
        output, code, deleted = self.run_clear_step(
            after, after=after, issues=[[self.failure_issue(4, after)]], runs=runs,
            tip_reads=[after, later])
        self.assertEqual(code, 0, output)
        self.assertEqual(deleted, [])
        self.assertIn(f"Main has moved on from {after} to {later}", output)

    def test_workflow_clear_fails_when_main_s_tip_is_unreadable(self):
        for tip in (None, "", "not a commit"):
            with self.subTest(tip=tip):
                output, code, deleted = self.run_clear_step(tip, issues=[[self.open_issue(4)]])
                self.assertNotEqual(code, 0, output)
                self.assertEqual(deleted, [])

    def test_clear_dry_run_never_contacts_github(self):
        status, output = self.run_clear("--dry-run")
        self.assertEqual(status, 0, output)
        self.assertEqual(self.api.calls, [])
        self.assertIn("DELETE main-red", output)

    def test_clear_unconfirmed_deletion_fails(self):
        self.api.open_issues = [self.open_issue(4)]
        self.api.pages["DELETE", f"/repos/{SLUG}/issues/4/labels/main-red"] = None
        status, output = self.run_clear()
        self.assertEqual(status, 2, output)
        self.assertIn("did not confirm clearing", output)

    def run_acceptance_event(self, name, data):
        script = workflow_step("ci.yml", "Identify main for this event")
        event = self.directory / "event.json"
        event.write_text(json.dumps(data), encoding="utf-8")
        output = self.directory / "github-env"
        output.write_text("", encoding="utf-8")
        env = ar.git_env()
        env.update(GITHUB_EVENT_NAME=name, GITHUB_EVENT_PATH=str(event), GITHUB_ENV=str(output))
        result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", script],
                                cwd=self.repo, env=env, text=True, capture_output=True,
                                check=False)
        return result, output.read_text(encoding="utf-8")

    def test_acceptance_push_compares_with_before_not_last_merge_parent(self):
        first = self.train()
        after = self.train(12, text="Second revision.\n")
        result, output = self.run_acceptance_event(
            "push", {"before": self.before, "after": after, "ref": "refs/heads/main",
                     "deleted": False})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, f"MAIN_SHA={self.before}\n")
        self.assertNotIn(first, output)

    def test_acceptance_group_compares_with_group_base(self):
        self.train()
        after = self.train(12, text="Second revision.\n")
        result, output = self.run_acceptance_event(
            "merge_group", {"merge_group": {"head_sha": after, "base_sha": self.before,
                                            "base_ref": "refs/heads/main"}})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, f"MAIN_SHA={self.before}\n")

    def test_acceptance_pull_request_uses_checkout_first_parent(self):
        main = self.train()
        self.train(12, text="Second revision.\n")
        result, output = self.run_acceptance_event(
            "pull_request", {"pull_request": {"head": {"sha": self.api.pulls[12]["head"]["sha"]},
                                            "base": {"sha": self.before}}})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, f"MAIN_SHA={main}\n")

    def test_acceptance_unknown_missing_and_mismatched_events_fail_closed(self):
        after = self.train()
        cases = [
            ("workflow_call", {}),
            ("push", {"after": after, "ref": "refs/heads/main", "deleted": False}),
            ("push", {"before": "0" * 40, "after": after, "ref": "refs/heads/main",
                      "deleted": False}),
            ("push", {"before": self.before, "after": self.before, "ref": "refs/heads/main",
                      "deleted": False}),
            ("merge_group", {"merge_group": {"head_sha": after, "base_sha": self.before,
                                            "base_ref": "refs/heads/other"}}),
        ]
        for name, data in cases:
            with self.subTest(name=name, data=data):
                result, output = self.run_acceptance_event(name, data)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(output, "")

    def test_queue_does_not_pass_when_acceptance_failed_or_was_skipped(self):
        script = workflow_step("ci.yml", "Require a completed acceptance check")
        for status in ("success", "failure", "cancelled", "skipped", "", "unknown"):
            with self.subTest(status=status):
                env = ar.git_env()
                env["ACCEPTANCE_RESULT"] = status
                result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", script],
                                        cwd=self.repo, env=env, capture_output=True, check=False)
                self.assertEqual(result.returncode == 0, status == "success",
                                 result.stderr.decode())

    @staticmethod
    def successful_run(before, **changes):
        return {"id": 98, "head_sha": before, "head_branch": "main", "event": "push",
                "path": ".github/workflows/post-merge.yml", "status": "completed",
                "conclusion": "success", **changes}

    def workflow_env(self, before, pages, *, unreadable=False, jobs=None):
        directory = self.directory / "bin"
        directory.mkdir(exist_ok=True)
        fixture = self.directory / "workflow-api.json"
        fixture.write_text(json.dumps({"pages": pages, "unreadable": unreadable,
                                       "jobs": jobs}), encoding="utf-8")
        gh = directory / "gh"
        gh.write_text(f"#!{sys.executable}\n" + textwrap.dedent('''\
            import json
            import os
            import sys
            from pathlib import Path

            args = sys.argv[1:]
            root = "repos/" + os.environ["REPOSITORY"]
            with open(os.environ["API_CALLS"], "a", encoding="utf-8") as calls:
                calls.write(json.dumps(args) + "\\n")
            query = root + "/actions/workflows/post-merge.yml/runs?head_sha=" + (
                os.environ["BEFORE"] + "&event=push&branch=main&per_page=100")
            fixture = json.loads(Path(os.environ["API_FIXTURE"]).read_text())
            if args == ["api", "--paginate", "--slurp", query]:
                if fixture["unreadable"]:
                    sys.exit(1)
                print(json.dumps(fixture["pages"]))
            elif args == ["api", "--paginate", "--slurp",
                          root + "/actions/runs/99/attempts/1/jobs?per_page=100"]:
                if fixture["jobs"] is None:
                    sys.exit(1)
                print(json.dumps(fixture["jobs"]))
            elif args == ["api", "--paginate", root + "/labels?per_page=100", "--jq", ".[].name"]:
                print("blocks-release\\nmain-red")
            elif args == ["api", root + "/pulls/11", "--jq", ".title"]:
                print("Train 11")
            elif args[:4] == ["api", "--method", "POST", root + "/issues"]:
                payload = Path(args[args.index("--input") + 1]).read_text()
                Path(os.environ["ISSUE_PAYLOAD"]).write_text(payload)
                print("Opened issue #1000")
            else:
                raise AssertionError("Unexpected gh operation: " + repr(args))
            '''), encoding="utf-8")
        gh.chmod(0o755)
        output = self.directory / "github-output"
        for name in ("github-output", "github-env-file", "github-path-file", "api-calls"):
            (self.directory / name).write_text("", encoding="utf-8")
        jobs = self.directory / "failed-jobs"
        jobs.write_text("integration / check: failure\n", encoding="utf-8")
        env = ar.git_env()
        env.update(PATH=str(directory) + ":" + env["PATH"], BEFORE=before, AFTER=self.rev(),
                   RUNNER_TEMP=str(self.directory), GITHUB_OUTPUT=str(output), REPOSITORY=SLUG,
                   GITHUB_ENV=str(self.directory / "github-env-file"),
                   GITHUB_PATH=str(self.directory / "github-path-file"),
                   RUN_ID="99", RUN_URL=f"https://github.com/{SLUG}/actions/runs/99",
                   API_FIXTURE=str(fixture), API_CALLS=str(self.directory / "api-calls"),
                   ISSUE_PAYLOAD=str(self.directory / "issue.json"), FAILED_JOBS=str(jobs))
        return env

    # The commands the step that takes the trusted script runs, as traced, on each path
    # through its text, by the reason it gives ("" when it takes the script): it reads the
    # runs only for a previous commit of 40 hex digits, not all zeros, judges them only when
    # GitHub answers, and reads the script only from a previous main whose run passed.
    READ_RUNS = "set script= +mktemp reason= [[ [[ response= +mktemp verdict= +mktemp reason= gh"
    TRUSTED_PATHS = {
        "The previous main commit is invalid.": (
            "set script= +mktemp reason= [[ rm echo printf",
            "set script= +mktemp reason= [[ [[ rm echo printf"),
        "The previous main's post-merge runs could not be read.": (
            READ_RUNS + " rm echo printf", READ_RUNS + " jq rm echo printf"),
        "No post-merge run was found for the previous main.": (
            READ_RUNS + " jq reason= +cat [[ rm echo printf",),
        "The latest post-merge run for the previous main did not conclude success.": (
            READ_RUNS + " jq reason= +cat [[ rm echo printf",),
        "The successful previous main has no readable revert script.": (
            READ_RUNS + " jq reason= +cat [[ reason= git rm echo printf",
            READ_RUNS + " jq reason= +cat [[ reason= git test rm echo printf"),
        "": (READ_RUNS + " jq reason= +cat [[ reason= git test echo echo exit",),
    }

    def run_trusted_extraction(self, before, pages=None, *, unreadable=False):
        script = workflow_step("post-merge.yml", "Take the revert script from the previous main")
        if pages is None:
            pages = [{"total_count": 1, "workflow_runs": [self.successful_run(before)]}]
        env = self.workflow_env(before, pages, unreadable=unreadable)
        result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", TRACE + script],
                                cwd=self.repo, env=env, text=True, capture_output=True,
                                check=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_nothing_for_later_steps(env)
        self.trusted_outputs = dict(
            line.split("=", 1) for line in
            Path(env["GITHUB_OUTPUT"]).read_text(encoding="utf-8").splitlines())
        self.assertIn(" ".join(commands(result.stderr)),
                      self.TRUSTED_PATHS[self.trusted_outputs["reason"]], result.stderr)
        self.workflow_environment = env
        return self.trusted_outputs["script"]

    def assert_nothing_for_later_steps(self, env):
        """A step before the record writes no variable or path for the later steps: through
        either (BASH_ENV, say, or another python3 first on the path), the failed push's
        code could run in the record step, which holds the App's key."""
        self.assertEqual([Path(env[name]).read_text(encoding="utf-8")
                          for name in ("GITHUB_ENV", "GITHUB_PATH")], ["", ""])

    def assert_fallback_issue(self, reason):
        script = workflow_step(
            "post-merge.yml",
            "Open the issue when the trusted script or failed jobs are unavailable")
        env = self.workflow_environment.copy()
        env["TRUST_FAILURE"] = self.trusted_outputs["reason"]
        result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", script],
                                cwd=self.repo, env=env, text=True, capture_output=True,
                                check=False)
        self.assertEqual(result.returncode, 1, result.stderr)
        payload = json.loads(Path(env["ISSUE_PAYLOAD"]).read_text(encoding="utf-8"))
        self.assertIn(reason, payload["body"])
        self.assertIn("Failed run: 99\n", payload["body"])
        self.assertIn("Issue only; no automatic revert or pull request was attempted.",
                      payload["body"])
        self.assertEqual(payload["labels"], ["blocks-release", "main-red"])
        calls = [json.loads(line) for line in Path(env["API_CALLS"]).read_text().splitlines()]
        self.assertEqual(sum(call[:3] == ["api", "--method", "POST"] for call in calls), 1)

    def test_workflow_executes_previous_main_script_despite_after_replacement(self):
        self.write("scripts/auto_revert.py", "print('Previous main script')\n")
        self.commit("Install trusted script")
        before = self.rev()
        self.train(path="scripts/auto_revert.py",
                   text="raise RuntimeError('Failed revision ran')\n")
        extracted = self.run_trusted_extraction(before)
        self.assertEqual(command(self.directory, sys.executable, "-I", extracted),
                         "Previous main script")
        self.assertEqual(self.trusted_outputs["reason"], "")

    def test_workflow_does_not_use_after_script_when_before_has_none(self):
        self.train(path="scripts/auto_revert.py",
                   text="raise RuntimeError('Failed revision ran')\n")
        self.assertEqual(self.run_trusted_extraction(self.before), "")
        self.assert_fallback_issue("no readable revert script")

    def test_workflow_refuses_before_without_a_successful_post_merge_run(self):
        self.write("scripts/auto_revert.py", "raise RuntimeError('Untrusted previous main ran')\n")
        self.commit("Install untrusted script")
        before = self.rev()
        good = self.successful_run(before)
        cases = [
            ([{"total_count": 0, "workflow_runs": []}], False, "No post-merge run"),
            ([{"total_count": 1, "workflow_runs": [dict(good, conclusion="failure")]}],
             False, "did not conclude success"),
            ([{"total_count": 1,
               "workflow_runs": [dict(good, status="in_progress", conclusion=None)]}],
             False, "did not conclude success"),
            ([{"total_count": 1, "workflow_runs": [good]}], True, "could not be read"),
            ([{"workflow_runs": [good]}], False, "could not be read"),
            ([], False, "could not be read"),
            ([{"total_count": 1, "workflow_runs": None}], False, "could not be read"),
            ([{"total_count": 2, "workflow_runs": [good]}], False, "could not be read"),
            ([{"total_count": 2, "workflow_runs": [good, good]}], False, "could not be read"),
            ([{"total_count": 1, "workflow_runs": [good]},
              {"total_count": 0, "workflow_runs": []}], False, "could not be read"),
            ([{"total_count": 1, "workflow_runs": [{key: value for key, value in good.items()
                                                   if key != "conclusion"}]}],
             False, "could not be read"),
        ]
        for pages, unreadable, reason in cases:
            with self.subTest(pages=pages, unreadable=unreadable):
                self.assertEqual(
                    self.run_trusted_extraction(before, pages, unreadable=unreadable), "")
                self.assert_fallback_issue(reason)

    def test_workflow_refuses_a_run_for_another_commit_branch_event_or_workflow(self):
        self.write("scripts/auto_revert.py", "print('Must not be trusted')\n")
        self.commit("Install script")
        before = self.rev()
        changes = [{"head_sha": "f" * 40}, {"head_branch": "topic"}, {"event": "pull_request"},
                   {"path": ".github/workflows/ci.yml"}, {"id": "98"}, {"id": 0},
                   {"id": 1.5}, {"id": True}, {"status": None}, {"conclusion": []}]
        for change in changes:
            with self.subTest(change=change):
                pages = [{"total_count": 1,
                          "workflow_runs": [self.successful_run(before, **change)]}]
                self.assertEqual(self.run_trusted_extraction(before, pages), "")
                self.assert_fallback_issue("could not be read")

    def test_workflow_uses_latest_run_across_all_pages(self):
        self.write("scripts/auto_revert.py", "print('Previous main script')\n")
        self.commit("Install script")
        before = self.rev()
        good = self.successful_run(before)
        for conclusion in ("failure", "success"):
            with self.subTest(conclusion=conclusion):
                pages = [{"total_count": 2, "workflow_runs": [good]},
                         {"total_count": 2,
                          "workflow_runs": [dict(good, id=99, conclusion=conclusion)]}]
                extracted = self.run_trusted_extraction(before, pages)
                if conclusion == "failure":
                    self.assertEqual(extracted, "")
                    self.assert_fallback_issue("did not conclude success")
                else:
                    self.assertEqual(command(self.directory, sys.executable, "-I", extracted),
                                     "Previous main script")

    def test_workflow_refuses_an_invalid_previous_commit(self):
        for before in ("0" * 40, "invalid", "a" * 39):
            with self.subTest(before=before):
                self.assertEqual(self.run_trusted_extraction(before), "")
                self.assert_fallback_issue("previous main commit is invalid")

    def test_workflow_reads_the_failed_jobs_and_nothing_for_later_steps(self):
        # The step that reads the failed jobs, run on GitHub's answers: it names them, or
        # says they could not be read, and leaves the later steps alone. It runs the
        # commands of its text alone, traced as the record step's are.
        script = workflow_step("post-merge.yml", "Read the failed jobs")
        unread = "Failed job details could not be read; integration reported failure.\n"
        page = {"jobs": [{"name": "integration / check", "conclusion": "failure"},
                         {"name": "integration / model", "conclusion": "success"},
                         {"name": "integration / lean", "conclusion": None},
                         {"name": "integration / acceptance", "conclusion": "skipped"},
                         {"name": "integration / gaps", "conclusion": "neutral"}]}
        for jobs, readable, text, ran in (
                ([page], "true", "integration / check: failure\n", "gh jq echo echo"),
                (None, "false", unread, "gh echo echo echo"),
                ([{"jobs": []}], "false", unread, "gh jq echo echo echo")):
            with self.subTest(jobs=jobs):
                env = self.workflow_env(self.before, [], jobs=jobs)
                env["RUN_ATTEMPT"] = "1"
                result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", TRACE + script],
                                        cwd=self.repo, env=env, text=True, capture_output=True,
                                        check=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(commands(result.stderr),
                                 ("set jobs= +mktemp response= +mktemp " + ran).split(),
                                 result.stderr)
                outputs = dict(line.split("=", 1) for line in Path(
                    env["GITHUB_OUTPUT"]).read_text(encoding="utf-8").splitlines())
                self.assertEqual(outputs["readable"], readable)
                self.assertEqual(Path(outputs["path"]).read_text(encoding="utf-8"), text)
                self.assert_nothing_for_later_steps(env)

    RECORD = "Record the failure and enqueue the revert"
    FALLBACK = "Open the issue when the trusted script or failed jobs are unavailable"
    # The revert job's steps before those two, as post-merge.yml holds them less their run
    # text, which the tests above run; the conditions read the ids failed and trusted.
    EARLIER = [
        {"uses": "actions/checkout@v5", "with": {
            "fetch-depth": "0", "persist-credentials": "false",
            "ref": "${{ github.event.after }}"}},
        {"name": "Read the failed jobs", "if": "always()", "id": "failed",
         "env": {"RUN_ATTEMPT": "${{ github.run_attempt }}"}, "shell": "bash"},
        {"name": "Take the revert script from the previous main", "if": "always()",
         "id": "trusted", "shell": "bash"},
    ]
    # The variables the record step and the fallback run with: the job's, then each one's.
    VARIABLES = {
        "job": {"GH_TOKEN", "REPOSITORY", "BEFORE", "AFTER", "RUN_ID", "RUN_URL"},
        "record": {"GITHUB_TOKEN", "STOICHEIA_REVERT_APP_ID", "STOICHEIA_REVERT_APP_KEY",
                   "TRUSTED_SCRIPT", "FAILED_JOBS"},
        "fallback": {"FAILED_JOBS", "TRUST_FAILURE"},
    }

    def test_workflow_records_a_failure_as_actions_runs_the_revert_job(self):
        # The revert job's last two steps, as post-merge.yml holds them, run as Actions
        # runs them, with stand-ins for python3 and gh that record each call.
        job = workflow_job("post-merge.yml", "revert")
        record, fallback = job_step(job, self.RECORD), job_step(job, self.FALLBACK)
        # Its permissions, its steps in order, and the variables each of the two runs
        # with. So a step added (one that rewrites the trusted script before the record
        # runs it, say, or puts another python3 first on the path), an id the conditions
        # read renamed, or a variable added (BASH_ENV, say, or LD_PRELOAD, either of which
        # would run the failed push's code with the credentials) fails.
        self.assertEqual(job.get("permissions"), {"contents": "write", "issues": "write",
                                                  "actions": "read", "pull-requests": "read"})
        self.assertEqual([{key: value for key, value in step.items() if key != "run"}
                          for step in job["steps"][:-2]], self.EARLIER)
        self.assertEqual(job["steps"][-2:], [record, fallback])
        self.assertEqual({scope: set(held.get("env", {})) for scope, held in (
            ("job", job), ("record", record), ("fallback", fallback))}, self.VARIABLES)
        credentials = {WORKFLOW_TOKEN: "the job's token", self.key: "the App's key"}

        def holding(env):
            """Which credential each variable of env holds, of those that hold one."""
            return {key: credentials[value] for key, value in env.items()
                    if value in credentials}

        # The job runs when integration failed, and only then: its if reads the status of
        # the jobs it needs, and a job that needs none starts with the run, at success.
        for result in ("success", "failure", "cancelled"):
            status = result if job.get("needs") == "integration" else "success"
            self.assertEqual(condition(job.get("if"), {}, status), result == "failure", result)
        # Exactly one of the two steps runs, whatever the earlier steps left, and whether
        # or not one of them failed.
        for script, readable, status in itertools.product(
                ("/runner/auto-revert.abc123", ""), ("true", "false", ""),
                ("success", "failure", "cancelled")):
            outputs = {"trusted": {"script": script}, "failed": {"readable": readable}}
            with self.subTest(script=script, readable=readable, status=status):
                runs = condition(record.get("if"), outputs, status)
                self.assertEqual(runs, bool(script) and readable == "true")
                self.assertEqual(condition(fallback.get("if"), outputs, status), not runs)
        merge = self.train()
        runner = self.directory / "runner"
        (runner / "bin").mkdir(parents=True)
        calls = runner / "calls"
        for name in ("python3", "gh"):
            stand_in = runner / "bin" / name
            stand_in.write_text(f"#!{sys.executable}\n"
                                + RECORDER.format(calls=str(calls), slug=SLUG), encoding="utf-8")
            stand_in.chmod(0o755)
        path = f"{runner / 'bin'}:{os.environ['PATH']}"
        jobs = runner / "failed-jobs"
        jobs.write_text("integration / check: failure\nintegration / model: failure\n",
                        encoding="utf-8")
        trusted = runner / "auto-revert.abc123"
        run_url = f"https://github.com/{SLUG}/actions/runs/99"
        # The App's secrets are the auto-revert environment's alone (WORKFLOW, section 10).
        secrets = {"secrets.STOICHEIA_REVERT_APP_ID": "1234",
                   "secrets.STOICHEIA_REVERT_APP_KEY": self.key}
        if job.get("environment") != "auto-revert":
            secrets = dict.fromkeys(secrets, "")
        values = {"github.token": WORKFLOW_TOKEN, "github.repository": SLUG,
                  "github.event.before": self.before, "github.event.after": merge,
                  "github.run_id": "99", "github.server_url": "https://github.com",
                  "steps.trusted.outputs.script": str(trusted),
                  "steps.trusted.outputs.reason": "", "steps.failed.outputs.path": str(jobs),
                  **secrets}

        def made():
            return [json.loads(line) for line in calls.read_text(encoding="utf-8").splitlines()]

        for code in (0, 1, 2, 3):
            with self.subTest(exit=code):
                calls.write_text("", encoding="utf-8")
                (runner / "exit").write_text(str(code), encoding="utf-8")
                result, fails = run_step(job, record, values, runner, self.repo, path)
                self.assertEqual([call[:2] for call in made()], [["python3", [
                    "-I", str(trusted), "--before", self.before, "--after", merge,
                    "--repo", SLUG, "--run-url", run_url, "--failed-jobs",
                    "integration / check: failure\nintegration / model: failure"]]],
                    result.stderr)
                env = made()[0][2]
                self.assertEqual({key: env.get(key) for key in (
                    "GITHUB_TOKEN", "STOICHEIA_REVERT_APP_ID", "STOICHEIA_REVERT_APP_KEY")},
                    {"GITHUB_TOKEN": WORKFLOW_TOKEN, "STOICHEIA_REVERT_APP_ID": "1234",
                     "STOICHEIA_REVERT_APP_KEY": self.key})
                # The job's token in GH_TOKEN and GITHUB_TOKEN, and the App's key in the
                # step's own STOICHEIA_REVERT_APP_KEY alone.
                self.assertEqual(holding(env), {"GH_TOKEN": "the job's token",
                                                "GITHUB_TOKEN": "the job's token",
                                                "STOICHEIA_REVERT_APP_KEY": "the App's key"})
                # The step runs the trusted script and, in its arguments, the read of the
                # failed jobs alone, and may exit: any other command it runs here fails, as
                # commands() reads them, even one that finds in the test's checkout no file
                # of the failed push to run.
                self.assertEqual([name for name in commands(result.stderr) if name != "exit"],
                                 ["python3", "+cat"], result.stderr)
                # The script's exit is the step's, and any but 0 fails the job.
                self.assertEqual(result.returncode, code, result.stderr)
                self.assertEqual(fails, code != 0)
        # The fallback, run in a state that runs it: it opens the issue with gh and the
        # job's token alone, and fails the job.
        reason = "No post-merge run was found for the previous main."
        values.update({"steps.trusted.outputs.script": "",
                       "steps.trusted.outputs.reason": reason})
        calls.write_text("", encoding="utf-8")
        result, fails = run_step(job, fallback, values, runner, self.repo, path)
        self.assertEqual((result.returncode, fails), (1, True), result.stderr)
        # These commands alone, in this order: gh reads the labels and the train's title and
        # opens the issue, and exit fails the job.
        self.assertEqual(commands(result.stderr), (
            "set labels= +mktemp gh for grep for grep body= +mktemp printf printf [[ [[ history="
            " +mktemp git IFS= read commit= subject= [[ number= title= +gh printf IFS= read"
            " printf test test cat printf printf printf payload= +mktemp jq gh exit").split(),
            result.stderr)
        self.assertEqual([call[0] for call in made()], ["gh"] * 3)
        self.assertEqual([holding(call[2]) for call in made()],
                         [{"GH_TOKEN": "the job's token"}] * 3)
        opened = made()[-1][1]
        self.assertEqual(opened[:4], ["api", "--method", "POST", f"repos/{SLUG}/issues"])
        payload = json.loads(Path(opened[opened.index("--input") + 1]).read_text())
        self.assertEqual(payload["title"], f"Main integration failed at {merge[:12]}")
        self.assertEqual(payload["labels"], ["blocks-release", "main-red"])
        for text in (f"Before: {self.before}\nAfter: {merge}\n",
                     f"- #11: Train 11 (merge {merge})\n", "integration / model: failure\n",
                     f"Failed run: 99\nRun: {run_url}\n", reason,
                     "Issue only; no automatic revert or pull request was attempted."):
            self.assertIn(text, payload["body"])

    def test_the_condition_reader_refuses_every_other_form(self):
        # So that a changed condition fails the test above rather than being misread.
        for text in ("!cancelled()", "${{ always() }}", "always() &&", "(always()",
                     "'a' == 'a' == 'a'", "'a' 'b'", "always() == 'true'",
                     "github.event_name == 'push'", "steps.trusted.outputs.script != \"\"",
                     "always() and true", "steps.trusted.outputs", "always() || 'x' <= 'y'"):
            with self.subTest(text=text):
                with self.assertRaisesRegex(AssertionError, "does not read"):
                    condition(text, {}, "success")


if __name__ == "__main__":
    unittest.main()
