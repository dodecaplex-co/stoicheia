"""Ask Jev, TypeSafe's decision model, the questions of the independent acceptance audit.

Brief 0005, stage 6 ("Independent acceptance audit with Jev", issue #36) asks a third model
family, one that wrote none of Stoicheia, to audit the review items. Jev is a hosted
multiple-choice decision model, not a chat model: it is given a state and a question with
its options, and returns a choice with a probability for every option. This client was
written fresh for Stoicheia, from TypeSafe's public documentation (https://docs.typesafe.ai:
the API reference and the pages on Models, Choice, Images, Confidence and Jev 1.13's jagged
edges, read on 18 October 2026). We thank TypeSafe warmly for Jev and for documentation clear
enough to build from.

Run it from anywhere, with Python 3.11 or later; it needs nothing but the standard library
(and rsvg-convert, only to send an SVG figure):

    python3 scripts/audit/jev.py preflight            the model listing, and the pinned model
    python3 scripts/audit/jev.py smoke                preflight, then one trivial decision
    python3 scripts/audit/jev.py run FILE --out OUT   preflight, then one request for each row
    python3 scripts/audit/jev.py run FILE --dry-run   print every request; read no key, send
                                                      nothing
    python3 scripts/audit/jev.py score OUT            agreement with the expected answers, and
                                                      what goes to the adjudicator
    python3 scripts/audit/jev.py self-test            all of it, against a stand-in for the
                                                      service on this machine

**The key** is read only from the file that the environment variable `STOICHEIA_JEV_KEY_FILE`
names, a file outside the repository: never from the command line, never from the
environment itself. It is never printed, logged or written, and anything echoed back from the
service (an error's body, say) has it redacted. A dry run and the self-test never read it.

**What it sends.** Each row of FILE (JSON Lines) is one request to `POST /v1/systemone`, with
retries off, no redirect followed (so the key is never carried to another address), HTTPS
only (plain HTTP to this machine alone, for the self-test), and a timeout. Only the row's
`state`, `question` and `assets` are sent; its `expected` answer and every other field stay
here. A row:

    {"id": "09-I.40-record",             unique; carried to the output
     "state": ...,                       what Jev reads: text, or JSON
     "question": {"type": "choice", "instructions": ..., "criteria": {option: description}},
     "assets": {"<reference>": "figures/I/01.svg"},     optional: images, by repository path
     "expected": "<an option>",          optional: the answer a correct reader gives
     "item": 9, "ref": "I.40", "seeded": true}          optional labels, carried to the output

A question is a `choice`, or a `noul` (a yes-or-no question, answered by the probability of
yes; its `expected` is true or false). Each choice is asked twice in its request, the second
time with its options in reverse order, since TypeSafe notes that Jev 1.13 can lean toward
the option that comes first; the output says whether the two answers agree (`--no-order-check`
asks once). An image is a PNG or JPEG of 280 to 1568 pixels a side, or an SVG, which is
rendered to PNG first (`--svg-width`, 700 by default); a request with images carries the
header `TypeSafe-Danger-Zone-Images: true`. Every reference must occur in the state or the
question, and is best a string that cannot occur by accident.

**What it writes.** One JSON line for each row, as it goes: the row's id and labels; the model
asked for and the model that answered; the choice, every option's probability and Jev's
confidence (or the noul); the latency in seconds; the tokens used; the SHA-256 of the exact
body sent, so an answer can be tied to its request; the SHA-256 of the input and its number
of rows, and whether the order check was on; whether it agrees with `expected`; and the
reversed asking. A failed request is written as its status and its redacted error, and so
is an answer that is not the shape TypeSafe documents, a reply that names no answering
model among them. Retries are off: a refused key, a
rate limit or an overload stops the run, and any other failure is recorded and the run goes
on. `--resume` sends again, by hand, only the rows that an earlier output of the same input,
model and order check has no answer for (a line naming no answering model is not an
answer, and is sent again), and `--pause` waits between requests.

**The model is pinned.** Each run names a versioned model id (`jev-1.13.0` by default, which
`jev-latest` points to on 18 October 2026), and records it with every answer, so that a
result can always be traced to the model that gave it. An alias such as `jev-latest` moves
when TypeSafe ships a release, and is refused unless `--allow-alias` is given.

**Smoke first.** The brief asks for the model listing, then one trivial decision, before any
audit traffic:

    export STOICHEIA_JEV_KEY_FILE=<a file outside the repository, holding the key>
    python3 scripts/audit/jev.py smoke
    python3 scripts/audit/jev.py run docs/reports/acceptance/jev/calibration.jsonl \\
        --out docs/reports/acceptance/jev/calibration-<model>-<date>.jsonl
    python3 scripts/audit/jev.py score docs/reports/acceptance/jev/calibration-<model>-<date>.jsonl

`score` lists every answer that disagrees with its expected answer, has, in either asking,
a confidence under `--low` (0.5 by default, the threshold under which the example on
TypeSafe's Confidence page sends an answer to a person; a noul's confidence is |2p - 1|,
as that page gives it) or none, changes when its options are reversed, or comes from
another model than the one pinned: these go to the adjudicator. A line whose reversed asking
is not an answer, or that names no answering model, is refused. It also counts
how many of the input's rows are answered. With `--bar`, it exits 1 when agreement falls
under the bar, when any request failed, or when any row of the input has no answer: a bar
is met only when every row of the input is answered.

The self-test runs every command above against a stand-in for the service on this machine,
with a key it makes up, and checks among other things that the key appears in no output,
that a dry run reads no key and sends nothing, that no redirect is followed, that the
timeout holds, that images are checked and sent with their header, that `expected` is never
sent, and that the calibration set reads. It needs no network and no key.
"""

from __future__ import annotations

import argparse
import base64
import datetime as dt
import hashlib
import http.client
import http.server
import ipaddress
import json
import math
import os
import re
import secrets
import shutil
import socket
import stat
import struct
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import zlib
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
CALIBRATION = ROOT / "docs" / "reports" / "acceptance" / "jev" / "calibration.jsonl"
KEY_ENV = "STOICHEIA_JEV_KEY_FILE"
BASE_URL = "https://api.typesafe.ai"
DEFAULT_MODEL = "jev-1.13.0"
VERSIONED = re.compile(r"^jev-\d+\.\d+\.\d+$")
IMAGES_HEADER = "TypeSafe-Danger-Zone-Images"
USER_AGENT = "stoicheia-jev-audit/1 (+https://github.com/dodecaplex-co/stoicheia)"
# Labels carried from a row to its output line; nothing else of the row is written.
LABELS = ("id", "item", "ref", "seeded", "expected")
# Statuses after which no later request can succeed: a refused key, a rate limit, an overload.
STOP = {401, 403, 429, 529}
REVERSED = "__reversed"
MIN_SIDE, MAX_SIDE = 280, 1568
MAX_IMAGE = 16 * 1024 * 1024
MAX_BODY = 32 * 1024 * 1024
LOW = 0.5
REDACTED = "[redacted]"


class Failure(Exception):
    """A refusal, with the message to print."""


# The key, once read, so that everything printed or written can be redacted.
_secret: list[str] = []


def spellings(key: str) -> list[str]:
    """The key as it may stand in what the service sends back or what is written: as it
    is, and escaped in a JSON string (where a / may also be written \\/), longest first."""
    forms = {key, json.dumps(key)[1:-1], json.dumps(key, ensure_ascii=False)[1:-1]}
    forms |= {form.replace("/", "\\/") for form in forms}
    return sorted(forms, key=len, reverse=True)


def redact(text: str) -> str:
    for key in _secret:
        text = text.replace(key, REDACTED)
    return re.sub(r"(?i)\b(bearer\s+)[^\s\"',;\\]+", r"\1" + REDACTED, text)


def say(message: str, *, err: bool = True) -> None:
    print(redact(message), file=sys.stderr if err else sys.stdout, flush=True)


def read_key() -> str:
    """The key, from the file STOICHEIA_JEV_KEY_FILE names. The file's name is not printed
    either: it is the owner's, and private."""
    name = os.environ.get(KEY_ENV, "").strip()
    if not name:
        raise Failure(f"set {KEY_ENV} to the name of a file, outside the repository, that "
                      "holds the key (the key itself never goes in the environment or on the "
                      "command line)")
    path = Path(name).expanduser()
    try:
        raw = path.read_text(encoding="utf-8")
        mode = path.stat().st_mode
    except (OSError, UnicodeDecodeError) as e:
        reason = e.strerror if isinstance(e, OSError) and e.strerror else type(e).__name__
        raise Failure(f"the file {KEY_ENV} names cannot be read ({reason})") from None
    key = raw.strip()
    if not key or any(c.isspace() for c in key):
        raise Failure(f"the file {KEY_ENV} names should hold the key alone, on one line")
    try:
        inside = path.resolve().is_relative_to(ROOT)
    except OSError:
        inside = False
    if inside:
        raise Failure(f"the file {KEY_ENV} names is inside the repository; keep the key "
                      "outside it, where no commit can take it")
    _secret.extend(spellings(key))
    if mode & (stat.S_IRWXG | stat.S_IRWXO):
        say(f"note: the file {KEY_ENV} names can be read by other users; chmod 600 it")
    return key


# ---------------------------------------------------------------------------------------
# HTTP: urllib, with no redirect followed and no retry.


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    """A redirect is not followed: urllib would carry the Authorization header to the new
    address. The 3xx comes back as an error, and is recorded as one."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):  # noqa: D401
        return None


_OPENER = urllib.request.build_opener(_NoRedirect)
# This machine is reached directly, never through a proxy the environment names.
_LOCAL_OPENER = urllib.request.build_opener(urllib.request.ProxyHandler({}), _NoRedirect)


def loopback(host: str) -> bool:
    if host == "localhost":
        return True
    try:
        return ipaddress.ip_address(host).is_loopback
    except ValueError:
        return False


def check_base(base: str) -> str:
    parts = urllib.parse.urlsplit(base)
    if parts.scheme == "https" and parts.hostname:
        pass
    elif parts.scheme == "http" and parts.hostname and loopback(parts.hostname):
        pass
    else:
        raise Failure(f"--base-url must be https:// (or http:// to this machine, for the "
                      f"self-test): {base!r}")
    if parts.query or parts.fragment or parts.username or parts.password:
        raise Failure("--base-url takes a scheme, a host and a path only")
    return base.rstrip("/")


class Reply:
    def __init__(self, status: int | None, body: bytes, seconds: float, error: str = ""):
        self.status, self.body, self.seconds, self.error = status, body, seconds, error

    def json(self) -> Any:
        return json.loads(self.body.decode("utf-8"))

    def text(self, limit: int = 2000) -> str:
        # Redacted whole, then cut: a key that the cut ran through would keep its start.
        return redact(self.body.decode("utf-8", errors="replace"))[:limit]


def request(method: str, url: str, key: str, timeout: float, body: bytes | None = None,
            images: bool = False) -> Reply:
    headers = {"Authorization": "Bearer " + key, "Accept": "application/json",
               "User-Agent": USER_AGENT}
    if body is not None:
        headers["Content-Type"] = "application/json"
    if images:
        headers[IMAGES_HEADER] = "true"
    req = urllib.request.Request(url, data=body, method=method, headers=headers)
    opener = _LOCAL_OPENER if loopback(urllib.parse.urlsplit(url).hostname or "") else _OPENER
    start = time.monotonic()
    try:
        with opener.open(req, timeout=timeout) as resp:
            data = resp.read()
            return Reply(resp.status, data, time.monotonic() - start)
    except urllib.error.HTTPError as e:
        try:
            data = e.read()
        except Exception:  # the body of an error is a courtesy; its status is what counts
            data = b""
        return Reply(e.code, data, time.monotonic() - start)
    except (TimeoutError, socket.timeout):
        return Reply(None, b"", time.monotonic() - start, f"no answer within {timeout:g} s")
    except urllib.error.URLError as e:
        reason = e.reason
        if isinstance(reason, (TimeoutError, socket.timeout)):
            return Reply(None, b"", time.monotonic() - start, f"no answer within {timeout:g} s")
        return Reply(None, b"", time.monotonic() - start, redact(f"cannot connect: {reason}"))
    except OSError as e:
        return Reply(None, b"", time.monotonic() - start, redact(f"connection failed: {e}"))
    except http.client.HTTPException as e:     # an answer broken off, or not HTTP at all
        return Reply(None, b"", time.monotonic() - start,
                     redact(f"a broken answer: {e!r}")[:300])


# ---------------------------------------------------------------------------------------
# Rows and their requests.


def png_or_jpeg(data: bytes) -> tuple[str, int, int]:
    """The format, width and height of a PNG or JPEG, read from its header; ValueError for
    anything else, an animated PNG included (TypeSafe refuses those)."""
    if data[:8] == b"\x89PNG\r\n\x1a\n":
        if data[12:16] != b"IHDR":
            raise ValueError("a PNG without its IHDR chunk")
        width, height = struct.unpack(">II", data[16:24])
        pos = 8
        while pos + 8 <= len(data):
            length, kind = struct.unpack(">I4s", data[pos:pos + 8])
            if kind == b"acTL":
                raise ValueError("an animated PNG")
            if kind in (b"IDAT", b"IEND"):
                break
            pos += 12 + length
        return "png", width, height
    if data[:2] == b"\xff\xd8":
        pos = 2
        while pos + 4 <= len(data):
            if data[pos] != 0xFF:
                raise ValueError("a JPEG whose markers cannot be read")
            marker = data[pos + 1]
            if marker == 0xFF:
                pos += 1
                continue
            if marker in (0xD8, 0x01) or 0xD0 <= marker <= 0xD7:
                pos += 2
                continue
            (length,) = struct.unpack(">H", data[pos + 2:pos + 4])
            if 0xC0 <= marker <= 0xCF and marker not in (0xC4, 0xC8, 0xCC):
                height, width = struct.unpack(">HH", data[pos + 5:pos + 9])
                return "jpg", width, height
            pos += 2 + length
        raise ValueError("a JPEG with no frame header")
    raise ValueError("neither PNG nor JPEG")


def load_asset(root: Path, rel: str, svg_width: int) -> tuple[str, bytes, int, int]:
    """The format, bytes and size of the image at `rel`, a path under `root`; an SVG is
    rendered to PNG by rsvg-convert. Raises Failure when the image will not do."""
    if not isinstance(rel, str) or not rel or Path(rel).is_absolute():
        raise Failure(f"an asset is named by a path relative to {root.name}/: {rel!r}")
    path = (root / rel).resolve()
    if not path.is_relative_to(root.resolve()):
        raise Failure(f"an asset must lie inside {root.name}/: {rel!r}")
    if not path.is_file():
        raise Failure(f"no such image: {rel}")
    suffix = path.suffix.lower()
    if suffix == ".svg":
        tool = shutil.which("rsvg-convert")
        if not tool:
            raise Failure(f"{rel} is an SVG, and rsvg-convert, which renders it, is not on "
                          "the PATH; render it to PNG first")
        r = subprocess.run([tool, "-w", str(svg_width), "-f", "png", str(path)],
                           capture_output=True)
        if r.returncode != 0:
            raise Failure(f"rsvg-convert cannot render {rel}: "
                          f"{r.stderr.decode(errors='replace').strip()[:300]}")
        data = r.stdout
    elif suffix in (".png", ".jpg", ".jpeg"):
        data = path.read_bytes()
    else:
        raise Failure(f"an image is a PNG, a JPEG or an SVG: {rel}")
    if len(data) > MAX_IMAGE:
        raise Failure(f"{rel} is over 16 MiB")
    try:
        fmt, width, height = png_or_jpeg(data)
    except (ValueError, struct.error) as e:
        raise Failure(f"{rel}: {e}") from None
    if not (MIN_SIDE <= width <= MAX_SIDE and MIN_SIDE <= height <= MAX_SIDE):
        hint = " (for an SVG, try another --svg-width)" if suffix == ".svg" else ""
        raise Failure(f"{rel} is {width} x {height} pixels; TypeSafe takes {MIN_SIDE} to "
                      f"{MAX_SIDE} a side{hint}")
    return fmt, data, width, height


def check_row(row: Any, where: str, seen: set[str]) -> list[str]:
    """Everything wrong with one row, as messages; [] when it will do."""
    if not isinstance(row, dict):
        return [f"{where}: a row is a JSON object"]
    problems = []
    rid = row.get("id")
    if not isinstance(rid, str) or not rid.strip():
        problems.append(f"{where}: no id")
    elif rid in seen:
        problems.append(f"{where}: the id {rid!r} is used twice")
    else:
        seen.add(rid)
    if row.get("state") in (None, "", [], {}):
        problems.append(f"{where}: no state")
    q = row.get("question")
    if not isinstance(q, dict):
        return problems + [f"{where}: no question"]
    kind = q.get("type")
    if q.get("instructions") in (None, "", [], {}):
        problems.append(f"{where}: the question has no instructions")
    if kind == "choice":
        crit = q.get("criteria")
        if not isinstance(crit, dict) or not 2 <= len(crit) <= 255:
            problems.append(f"{where}: a choice has 2 to 255 options in its criteria")
        elif "expected" in row and row["expected"] not in crit:
            problems.append(f"{where}: expected {row['expected']!r} is not an option")
    elif kind == "noul":
        crit = q.get("criteria", {})
        if not isinstance(crit, dict) or not set(crit) <= {"true", "false"}:
            problems.append(f"{where}: a noul's criteria may say only what true and false mean")
        if "expected" in row and not isinstance(row["expected"], bool):
            problems.append(f"{where}: a noul's expected answer is true or false")
    else:
        problems.append(f"{where}: the question's type is choice or noul, not {kind!r}")
    unknown = set(q) - {"type", "instructions", "criteria"}
    if unknown:
        problems.append(f"{where}: the question has unknown keys {sorted(unknown)}")
    assets = row.get("assets", {})
    if not isinstance(assets, dict):
        problems.append(f"{where}: assets map a reference to a path")
    else:
        sent = json.dumps([row.get("state"), q], ensure_ascii=False)
        total = 0
        for ref in assets:
            size = len(ref.encode("utf-8"))
            total += size
            if not ref.strip() or size > 1024:
                problems.append(f"{where}: an asset's reference is 1 to 1,024 bytes")
            elif ref not in sent:
                problems.append(f"{where}: the asset {ref!r} is referenced nowhere in the "
                                "state or the question (TypeSafe refuses it)")
        if total > 65536:
            problems.append(f"{where}: the assets' references are over 65,536 bytes together")
    return problems


def _no_constant(name: str) -> None:
    raise ValueError(f"{name} is not a number TypeSafe accepts")


def read_rows(path: Path) -> list[dict]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError) as e:
        raise Failure(f"cannot read {path.name}: {e}") from None
    rows, problems, seen = [], [], set()
    for n, line in enumerate(lines, 1):
        if not line.strip():
            continue
        where = f"{path.name}:{n}"
        try:
            row = json.loads(line, parse_constant=_no_constant)
        except ValueError as e:
            problems.append(f"{where}: not JSON ({getattr(e, 'msg', e)})")
            continue
        problems += check_row(row, where, seen)
        rows.append(row)
    if problems:
        raise Failure("the rows will not do:\n  " + "\n  ".join(problems))
    if not rows:
        raise Failure(f"{path.name} has no rows")
    return rows


def build(row: dict, model: str, order_check: bool, assets_root: Path,
          svg_width: int) -> tuple[dict, list[str]]:
    """The request body for one row, and a description of each image in it."""
    q = row["question"]
    questions = {"q": q}
    if order_check and q["type"] == "choice":
        questions["q" + REVERSED] = {**q, "criteria": dict(reversed(list(q["criteria"].items())))}
    body: dict[str, Any] = {"model": model, "state": row["state"], "questions": questions}
    shown = []
    if row.get("assets"):
        body["assets"] = {}
        for ref, rel in row["assets"].items():
            fmt, data, width, height = load_asset(assets_root, rel, svg_width)
            body["assets"][ref] = {"type": "image", "format": fmt,
                                   "data_base64": base64.b64encode(data).decode("ascii")}
            shown.append(f"{ref}: {rel}, {fmt} {width} x {height}, {len(data):,} bytes")
    return body, shown


def encode(body: dict) -> bytes:
    data = json.dumps(body, ensure_ascii=False, allow_nan=False).encode("utf-8")
    if len(data) > MAX_BODY:
        raise Failure("a request is over TypeSafe's 32 MiB limit")
    return data


def _number(value: Any) -> bool:
    if isinstance(value, bool):
        return False
    return isinstance(value, int) or (isinstance(value, float) and math.isfinite(value))


def _model_id(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def answer_of(reply_json: Any, qid: str, q: dict) -> dict:
    """One answer, checked against its question; raises ValueError when it is malformed."""
    if not isinstance(reply_json, dict):
        raise ValueError("the reply is not a JSON object")
    answers = reply_json.get("answers")
    if not isinstance(answers, dict):
        raise ValueError("the reply's answers are not a JSON object")
    a = answers.get(qid)
    if not isinstance(a, dict):
        raise ValueError(f"the answer to {qid} is missing or not a JSON object")
    if q["type"] == "choice":
        choice, probs = a.get("choice"), a.get("probabilities")
        if not isinstance(probs, dict) or not all(_number(p) and 0 <= p <= 1
                                                  for p in probs.values()):
            raise ValueError("the probabilities are not an object of numbers from 0 to 1")
        if (not isinstance(choice, str) or choice not in q["criteria"]
                or set(probs) != set(q["criteria"])):
            raise ValueError("the answer's options are not the question's")
        if abs(sum(probs.values()) - 1) > 0.02:
            raise ValueError("the probabilities do not sum to 1")
        confidence = a.get("confidence")
        # A confidence out of range would be read as high, and kept from the adjudicator.
        if confidence is not None and not (_number(confidence) and 0 <= confidence <= 1):
            raise ValueError("the confidence is not a number from 0 to 1")
        return {"choice": choice, "probabilities": {k: probs[k] for k in q["criteria"]},
                "confidence": confidence}
    p = a.get("noul")
    if not (_number(p) and 0 <= p <= 1):
        raise ValueError("the noul is not a number from 0 to 1")
    return {"noul": float(p)}


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# ---------------------------------------------------------------------------------------
# The commands.


def pin(args) -> str:
    if not VERSIONED.match(args.model) and not args.allow_alias:
        raise Failure(f"pin a versioned model id, as {DEFAULT_MODEL}: an alias such as "
                      f"{args.model!r} moves when TypeSafe ships a release, and each run "
                      "records the model it pinned (brief 0005, stage 6); --allow-alias "
                      "sends it anyway")
    return args.model


def preflight(args, key: str) -> list[str]:
    reply = request("GET", f"{args.base}/v1/models", key, args.timeout)
    if reply.status != 200:
        raise Failure("model listing failed: "
                      + (f"HTTP {reply.status}: {reply.text(400)}" if reply.status
                         else reply.error))
    try:
        names = [m["name"] for m in reply.json()["models"]]
        listed = ", ".join(names) or "nothing"
    except (ValueError, KeyError, TypeError, ArithmeticError, RecursionError):
        raise Failure("the model listing is not the shape TypeSafe documents") from None
    if args.model in names:
        say(f"preflight: {args.model} is listed ({listed}), in {reply.seconds:.2f} s")
    elif VERSIONED.match(args.model):
        say(f"preflight: the key is accepted; the listing names {listed}, and a versioned "
            f"id such as {args.model} is accepted whether or not it is listed (TypeSafe's "
            f"Models page), in {reply.seconds:.2f} s")
    else:
        raise Failure(f"{args.model} is not in the model listing ({listed})")
    return names


def cmd_preflight(args) -> int:
    pin(args)
    preflight(args, read_key())
    return 0


SMOKE = {"id": "smoke", "expected": "geometry",
         "state": "Euclid's Elements opens with definitions of a point, a line and a circle.",
         "question": {"type": "choice", "instructions": "What is the text in the state about?",
                      "criteria": {"geometry": "Points, lines, figures and their properties.",
                                   "cookery": "Recipes, ingredients and cooking."}}}


def cmd_smoke(args) -> int:
    model = pin(args)
    key = read_key()
    preflight(args, key)
    body, _ = build(SMOKE, model, False, ROOT, args.svg_width)
    reply = request("POST", f"{args.base}/v1/systemone", key, args.timeout, encode(body))
    if reply.status != 200:
        raise Failure("the trivial decision failed: "
                      + (f"HTTP {reply.status}: {reply.text(400)}" if reply.status
                         else reply.error))
    try:
        data = reply.json()
        got = answer_of(data, "q", SMOKE["question"])
    except (ValueError, KeyError, TypeError, AttributeError, ArithmeticError,
            RecursionError) as e:
        raise Failure(f"the answer is not the shape TypeSafe documents ({e})") from None
    usage = data.get("usage")
    tokens = usage.get("input_tokens", "?") if isinstance(usage, dict) else "?"
    say(f"smoke: {data.get('model')} chose {got['choice']!r} (p = "
        f"{got['probabilities'][got['choice']]:.2f}, confidence {got['confidence']}) in "
        f"{reply.seconds:.2f} s, {tokens} input tokens")
    if data.get("model") != model:
        say(f"note: {model} was asked for, and {data.get('model')} answered")
    if got["choice"] != SMOKE["expected"]:
        say("smoke: the trivial decision came back wrong; look before sending audit traffic")
        return 1
    return 0


def cmd_run(args) -> int:
    model = pin(args)
    rows = read_rows(Path(args.file))
    order_check = not args.no_order_check
    # What every line records of the run, and what --resume holds an earlier output to.
    made = {"model_requested": model, "order_check": order_check,
            "input_sha256": hashlib.sha256(Path(args.file).read_bytes()).hexdigest(),
            "input_rows": len(rows)}
    built = []
    for row in rows:                    # every request is built, its images checked, first
        body, shown = build(row, model, order_check, args.assets_root, args.svg_width)
        built.append((row, body, shown, encode(body)))
    url = f"{args.base}/v1/systemone"
    if args.dry_run:
        say(f"GET {args.base}/v1/models", err=False)
        say(f"  Authorization: Bearer {REDACTED}    (the key {KEY_ENV} names; a dry run "
            "reads none)", err=False)
        for row, body, shown, payload in built:
            preview = json.loads(json.dumps(body))
            for ref, asset in preview.get("assets", {}).items():
                asset["data_base64"] = f"<{len(asset['data_base64']):,} characters of base64>"
            say(f"\n# {row['id']}: {len(payload):,} bytes, SHA-256 "
                f"{hashlib.sha256(payload).hexdigest()}", err=False)
            say(f"POST {url}", err=False)
            say(f"  Authorization: Bearer {REDACTED}", err=False)
            say("  Content-Type: application/json", err=False)
            if "assets" in body:
                say(f"  {IMAGES_HEADER}: true", err=False)
                for line in shown:
                    say(f"  # image {line}", err=False)
            say(json.dumps(preview, ensure_ascii=False, indent=2), err=False)
        say(f"dry run: {len(built)} request(s) built and checked; nothing read, nothing sent")
        return 0
    out_path = Path(args.out) if args.out else None
    if args.resume and (not out_path or args.overwrite):
        raise Failure("--resume needs --out, and not --overwrite")
    if out_path and out_path.exists() and not (args.overwrite or args.resume):
        raise Failure(f"{out_path.name} exists; --overwrite replaces it, and --resume sends "
                      "only the rows it has no answer for")
    if out_path and not out_path.parent.is_dir():
        raise Failure(f"the folder for {out_path.name} does not exist")
    kept: list[str] = []
    if args.resume and out_path.exists():
        kept = answered_lines(out_path, made)
        done_ids = {json.loads(l)["id"] for l in kept}
        built = [b for b in built if b[0]["id"] not in done_ids]
        say(f"resume: {len(kept)} row(s) already answered; {len(built)} to send")
    key = read_key()
    preflight(args, key)
    out = out_path.open("w", encoding="utf-8") if out_path else sys.stdout
    for line in kept:
        out.write(line + "\n")
    if out_path:
        out.flush()
        os.fsync(out.fileno())
    failed = 0
    try:
        for done, (row, body, _, payload) in enumerate(built, 1):
            if done > 1 and args.pause:
                time.sleep(args.pause)
            reply = request("POST", url, key, args.timeout, payload, images="assets" in body)
            line: dict[str, Any] = {k: row[k] for k in LABELS if k in row}
            line.update(time=now(), **made, request_sha256=hashlib.sha256(payload).hexdigest(),
                        latency_s=round(reply.seconds, 3), status=reply.status)
            stop = False
            if reply.status == 200:
                try:
                    data = reply.json()
                    got = answer_of(data, "q", row["question"])
                    line["model"] = data.get("model")
                    if not _model_id(line["model"]):
                        raise ValueError("the reply's model is not a nonempty string")
                    line.update(got)
                    if "q" + REVERSED in body["questions"]:
                        again = answer_of(data, "q" + REVERSED, body["questions"]["q" + REVERSED])
                        again["consistent"] = again["choice"] == line["choice"]
                        line["reversed"] = again
                    line["usage"] = data.get("usage")
                    if "expected" in row:
                        line["agrees"] = (line["choice"] == row["expected"] if "choice" in line
                                          else (line["noul"] >= 0.5) == row["expected"])
                    if line["model"] != model:
                        line["model_differs"] = True
                except (ValueError, KeyError, TypeError, AttributeError, ArithmeticError,
                        RecursionError) as e:
                    line["error"] = f"the answer is not the shape TypeSafe documents ({e})"
                    line["body"] = reply.text()
            else:
                line["error"] = f"HTTP {reply.status}" if reply.status else reply.error
                if reply.body:
                    line["body"] = reply.text()
                stop = reply.status in STOP
            if "error" in line:
                failed += 1
            out.write(redact(json.dumps(line, ensure_ascii=False)) + "\n")
            out.flush()
            verdict = line.get("choice", line.get("noul", line.get("error")))
            say(f"{row['id']}: {verdict} ({reply.seconds:.2f} s)")
            if stop:
                say(f"stopped: HTTP {reply.status} ends the run (retries are off); "
                    f"{len(built) - done} row(s) not sent")
                return 1
    finally:
        if out_path:
            out.close()
    say(f"run: {len(built) - failed} of {len(built)} answered, model {model}")
    return 1 if failed else 0


def answered_lines(path: Path, made: dict[str, Any]) -> list[str]:
    """The lines of an earlier output that hold an answer, for --resume; a failed request's
    line, or one naming no answering model, is dropped, so that its row is sent again.
    Refuses an output made from another input, with another model or with another order
    check."""
    kept = []
    for n, text in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not text.strip():
            continue
        try:
            line = json.loads(text)
        except ValueError:
            raise Failure(f"{path.name}:{n} is not JSON; start afresh with --overwrite") from None
        if not isinstance(line, dict):
            raise Failure(f"{path.name}:{n} is not a JSON object; start afresh with --overwrite")
        if any(line.get(k) != made[k] for k in ("input_sha256", "input_rows", "model_requested")):
            raise Failure(f"{path.name} was made from another input or with another model; "
                          "start afresh with --overwrite, or write to another file")
        if line.get("order_check") != made["order_check"]:
            raise Failure(f"{path.name} was made {'with' if made['order_check'] else 'without'} "
                          "--no-order-check; resume it as it was made, start afresh with "
                          "--overwrite, or write to another file")
        if "error" not in line and not _model_id(line.get("model")):
            say(f"{path.name}:{n}: its answering model is not a nonempty string; resume "
                "will send this row again")
        if ("error" not in line and _model_id(line.get("model"))
                and isinstance(line.get("id"), str)):
            kept.append(text)
    return kept


def cmd_score(args) -> int:
    try:
        rows = [json.loads(l) for l in Path(args.file).read_text(encoding="utf-8").splitlines()
                if l.strip()]
    except (OSError, ValueError) as e:
        raise Failure(f"cannot read {Path(args.file).name}: {e}") from None
    answered = [r for r in rows if "error" not in r and ("choice" in r or "noul" in r)]
    for r in answered:
        if not _model_id(r.get("model")):
            raise Failure(f"{r.get('id')}: its answering model is not a nonempty string; score "
                          "reads only lines that `run` wrote")
        if "reversed" in r and not isinstance(r["reversed"], dict):
            raise Failure(f"{r.get('id')}: its reversed asking is not an answer; score reads "
                          "only lines that `run` wrote")
    labelled = [r for r in answered if "agrees" in r]
    agree = [r for r in labelled if r["agrees"]]
    runs = {(r.get("input_sha256"), r.get("input_rows")) for r in rows}
    total = None
    if len(runs) == 1:
        sha, count = next(iter(runs))
        if (isinstance(sha, str) and isinstance(count, int) and not isinstance(count, bool)
                and count > 0):
            total = count
    done = {r.get("id") for r in answered}
    print(f"{len(rows)} row(s); {len(answered)} answered; models "
          f"{', '.join(sorted({str(r.get('model')) for r in answered})) or 'none'}")
    if total:
        print(f"  the input: {len(done)} of its {total} row(s) answered")
    else:
        print("  the input: its row count is missing from a line, or differs between lines")
    for name, group in (("seeded", [r for r in labelled if r.get("seeded")]),
                        ("controls", [r for r in labelled if not r.get("seeded")])):
        if group:
            print(f"  {name}: {sum(r['agrees'] for r in group)} of {len(group)} as expected")
    rate = len(agree) / len(labelled) if labelled else 0.0
    if labelled:
        print(f"  agreement: {len(agree)} of {len(labelled)} ({rate:.0%})")
    errors = [r for r in rows if "error" in r]
    adjudicate = []
    for r in answered:
        why = []
        if r.get("agrees") is False:
            why.append(f"chose {r.get('choice', r.get('noul'))!r}, expected {r.get('expected')!r}")
        answers = [(r, "")]
        if isinstance(r.get("reversed"), dict):
            answers.append((r["reversed"], " with the options reversed"))
        for answer, order in answers:
            confidence = answer.get("confidence")
            if confidence is None and isinstance(answer.get("noul"), (int, float)):
                confidence = abs(2 * answer["noul"] - 1)
            if confidence is None:
                why.append("no confidence given" + order)
            elif confidence < args.low:
                why.append(f"confidence {confidence:.2f}" + order)
        if isinstance(r.get("reversed"), dict) and r["reversed"].get("consistent") is False:
            why.append(f"chose {r['reversed']['choice']!r} with the options reversed")
        if r.get("model_differs"):
            why.append(f"answered by {r.get('model')}, not {r.get('model_requested')}")
        if why:
            adjudicate.append(f"  {r.get('id')}: " + "; ".join(why))
    print(f"for adjudication: {len(adjudicate)}")
    for line in adjudicate:
        print(line)
    if errors:
        print(f"failed requests: {len(errors)}")
        for r in errors:
            print(f"  {r.get('id')}: {r['error']}")
    if args.bar is not None:
        if errors:
            print(f"below the bar of {args.bar:.0%}: {len(errors)} request(s) failed, and a "
                  "bar is met only when every row of the input is answered (--resume sends "
                  "them again)")
            return 1
        if not total or len(done) < total:
            why = (f"{total - len(done)} of the input's {total} row(s) have no answer" if total
                   else "the lines do not all carry one input and its row count")
            print(f"below the bar of {args.bar:.0%}: {why}, and a bar is met only when every "
                  "row of the input is answered (--resume sends the rows not yet answered)")
            return 1
        if not labelled or rate < args.bar:
            print(f"below the bar of {args.bar:.0%}")
            return 1
        print(f"at or above the bar of {args.bar:.0%}")
    return 0


# ---------------------------------------------------------------------------------------
# The self-test: a stand-in for TypeSafe on this machine, and every command run against it.


def _png(width: int, height: int) -> bytes:
    def chunk(kind: bytes, data: bytes) -> bytes:
        return (struct.pack(">I", len(data)) + kind + data
                + struct.pack(">I", zlib.crc32(kind + data) & 0xFFFFFFFF))
    raw = b"".join(b"\x00" + b"\xff" * (width * 3) for _ in range(height))
    return (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0))
            + chunk(b"IDAT", zlib.compress(raw)) + chunk(b"IEND", b""))


def _words(value: Any) -> set[str]:
    return {w.rstrip("s") for w in re.findall(r"[a-z]+", json.dumps(value).lower())}


class _StandIn(http.server.BaseHTTPRequestHandler):
    """Answers in the shape TypeSafe's documentation gives: the model listing, and each
    choice by the option whose description shares most words with the state (ties to the
    first in alphabetical order), so that a reversed asking agrees."""

    key = ""
    seen: list[dict] = []

    def log_message(self, *args):
        pass

    def _send(self, status: int, payload: Any, headers: dict | None = None) -> None:
        data = json.dumps(payload).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        for k, v in (headers or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(data)

    def _record(self, body: bytes) -> None:
        self.seen.append({"method": self.command, "path": self.path,
                          "headers": {k.lower(): v for k, v in self.headers.items()},
                          "body": body.decode("utf-8", errors="replace")})

    def _authorised(self) -> bool:
        if self.headers.get("Authorization") == "Bearer " + self.key:
            return True
        token = self.headers.get("Authorization", "")
        self._send(401, {"detail": f"Invalid API key: {token}"})
        return False

    def do_GET(self):
        self._record(b"")
        if self.path == "/v1/models" and self._authorised():
            self._send(200, {"models": [{"name": "jev-latest", "description": "stand-in",
                                         "release_date": "2026-10-01"}]})
        elif self.path != "/v1/models":
            self._send(404, {"detail": "Not Found"})

    def do_POST(self):
        body = self.rfile.read(int(self.headers.get("Content-Length", 0)))
        self._record(body)
        if self.path != "/v1/systemone":
            return self._send(404, {"detail": "Not Found"})
        if not self._authorised():
            return
        req = json.loads(body)
        text = json.dumps(req)
        if "assets" in req and self.headers.get(IMAGES_HEADER) != "true":
            return self._send(400, {"detail": "images are not turned on"})
        if "SELFTEST-ECHO" in text:
            return self._send(422, {"detail": f"bad request from {self.headers.get('Authorization')}"})
        if "SELFTEST-BEARER-WORD" in text:    # "bearer" and a word, in a JSON string
            return self._send(401, {"detail": "Invalid bearer token"})
        if "SELFTEST-NOT-AN-OBJECT" in text:  # a 200 whose body is JSON, but not an object
            return self._send(200, [{"model": req["model"]}])
        if "SELFTEST-LONG-ECHO" in text:      # the key runs through the 2,000th character
            return self._send(422, {"detail": "x" * 1968 + self.key})
        if "SELFTEST-ESCAPED-ECHO" in text:   # the key in a JSON string, its / written \/
            data = ('{"detail": "unknown key ' + self.key.replace("/", "\\/") + '"}').encode()
            self.send_response(422)
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            return self.wfile.write(data)
        if "SELFTEST-BROKEN" in text:         # the connection closes before the body ends
            self.send_response(200)
            self.send_header("Content-Length", "1000")
            self.end_headers()
            return self.wfile.write(b'{"model"')
        if "SELFTEST-REDIRECT" in text:
            return self._send(307, {}, {"Location": "/elsewhere"})
        if "SELFTEST-SLOW" in text:
            time.sleep(2.5)
        answers = {}
        for qid, q in req["questions"].items():
            if q["type"] == "choice":
                state = _words(req["state"])
                options = sorted(q["criteria"],
                                 key=lambda o: (-len(state & _words(q["criteria"][o])), o))
                rest = (1 - 0.7) / (len(options) - 1)
                probs = {o: (0.7 if o == options[0] else rest) for o in q["criteria"]}
                answers[qid] = {"type": "choice", "choice": options[0], "probabilities": probs,
                                "confidence": round((0.7 - 1 / len(options)) / (1 - 1 / len(options)), 2)}
            else:
                answers[qid] = {"type": "noul", "noul": 0.9}
        if "SELFTEST-PROBABILITIES-LIST" in text:   # the option names, without their numbers
            for a in answers.values():
                if "probabilities" in a:
                    a["probabilities"] = list(a["probabilities"])
        if "SELFTEST-CONFIDENCE-SCALE" in text:     # a confidence out of 100, not out of 1
            for a in answers.values():
                if "confidence" in a:
                    a["confidence"] = 42
        if "SELFTEST-HUGE-NUMBER" in text:          # a probability as a 400-digit integer
            for a in answers.values():
                if "probabilities" in a:
                    a["probabilities"] = {o: 10 ** 399 for o in a["probabilities"]}
        if "SELFTEST-NOUL-STRING" in text:          # a noul written as a string
            for a in answers.values():
                if "noul" in a:
                    a["noul"] = "0.9"
        model = req["model"] if VERSIONED.match(req["model"]) else DEFAULT_MODEL
        self._send(200, {"model": model, "answers": answers,
                         "usage": {"input_tokens": len(body) // 4, "output_tokens": 20}})


class _QuietServer(http.server.ThreadingHTTPServer):
    daemon_threads = True

    def handle_error(self, request, client_address):
        pass            # a client that timed out and hung up, as the timeout check makes one


def cmd_self_test(args) -> int:
    # A / in each, so that a key echoed with its / escaped can be looked for.
    key = "jev-self-test/" + secrets.token_hex(16)
    wrong = "jev-self-test/" + secrets.token_hex(16)
    _StandIn.key = key
    server = _QuietServer(("127.0.0.1", 0), _StandIn)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    base = f"http://127.0.0.1:{server.server_address[1]}"
    failures: list[str] = []
    tmp = Path(tempfile.mkdtemp(prefix="jev-self-test-"))
    try:
        key_file, wrong_file = tmp / "key", tmp / "wrong"
        key_file.write_text(key + "\n")
        wrong_file.write_text(wrong + "\n")
        key_file.chmod(0o600)
        wrong_file.chmod(0o600)

        def run(*argv: str, key_path: Path | None = key_file, timeout: float = 60):
            env = {k: v for k, v in os.environ.items() if k != KEY_ENV}
            if key_path is not None:
                env[KEY_ENV] = str(key_path)
            r = subprocess.run([sys.executable, "-I", str(Path(__file__).resolve()), *argv],
                               capture_output=True, text=True, env=env, timeout=timeout)
            return r.returncode, r.stdout, r.stderr

        def check(ok: bool, what: str, detail: str = "") -> None:
            print(f"  {'ok  ' if ok else 'FAIL'} {what}")
            if not ok:
                failures.append(what + (f": {detail[-600:]}" if detail else ""))

        def clean(*texts: str) -> bool:
            return not any(k in t for t in texts for k in spellings(key) + spellings(wrong))

        def posts() -> int:
            return sum(1 for s in _StandIn.seen if s["method"] == "POST")

        def parsed(text: str) -> list | None:
            try:
                return [json.loads(l) for l in text.splitlines() if l.strip()]
            except ValueError:
                return None

        common = ("--base-url", base)
        rows = read_rows(CALIBRATION)
        check(True, f"the calibration set reads: {len(rows)} rows")
        seeded = {r["id"] for r in rows if r.get("seeded")}
        for ref in ("I.40", "II.1", "III.14", "III.24"):
            check(f"09-{ref}-labelled-full" in seeded, f"the old {ref} statement is seeded, labelled full")
        check(any(r.get("item") == 10 and r.get("seeded") for r in rows), "a planted dummy citation is seeded")
        check(any(not r.get("seeded") for r in rows), "the calibration set holds controls")
        check(all("expected" in r for r in rows), "every calibration row has its expected answer")

        before = len(_StandIn.seen)
        code, out, err = run("run", str(CALIBRATION), "--dry-run", *common,
                             key_path=tmp / "no-such-file")
        check(code == 0, "a dry run needs no key", err)
        check(len(_StandIn.seen) == before, "a dry run sends nothing")
        check(out.count("POST ") == len(rows), "a dry run prints one request for each row", out[-300:])

        code, out, err = run("preflight", *common)
        check(code == 0 and clean(out, err), "preflight, with the key kept out of the output", err)
        gets = [s for s in _StandIn.seen if s["method"] == "GET"]
        check(bool(gets) and gets[-1]["headers"].get("authorization") == "Bearer " + key,
              "the key goes in the Authorization header")

        code, out, err = run("preflight", *common, key_path=wrong_file)
        check(code == 1 and clean(out, err), "a refused key fails, and is redacted from the echo", err)

        before = len(_StandIn.seen)
        code, out, err = run("smoke", "--model", "jev-latest", *common)
        check(code != 0 and len(_StandIn.seen) == before, "an alias is refused, and nothing sent", err)

        code, out, err = run("smoke", *common)
        check(code == 0 and clean(out, err), "smoke: preflight, then one trivial decision", err)

        results = tmp / "out.jsonl"
        before = posts()
        code, out, err = run("run", str(CALIBRATION), "--out", str(results), *common)
        check(code == 0, "the calibration set runs", err)
        check(posts() - before == len(rows), "one request for each row")
        lines = [json.loads(l) for l in results.read_text().splitlines()] if results.exists() else []
        check(len(lines) == len(rows), "one output line for each row")
        check(all({"choice", "probabilities", "model", "latency_s", "confidence", "request_sha256"}
                  <= set(l) for l in lines), "each line has the choice, probabilities, model and latency")
        check(all(l.get("reversed", {}).get("consistent") is True for l in lines),
              "each choice is asked again with its options reversed")
        check(clean(out, err, results.read_text() if results.exists() else ""),
              "the key is in no output")
        sent = [s["body"] for s in _StandIn.seen[-len(rows):]]
        check(not any(json.dumps(r["why"], ensure_ascii=False)[1:-1] in b or '"expected"' in b
                      for r in rows for b in sent),
              "neither the expected answer nor its reason is sent")
        check(all(json.loads(b)["model"] == DEFAULT_MODEL for b in sent), "the pinned model is sent")

        code, out, err = run("run", str(CALIBRATION), "--out", str(results), *common)
        check(code != 0 and "exists" in err, "an existing output is not overwritten", err)

        partial = tmp / "partial.jsonl"
        first = results.read_text().splitlines()
        failed_line = json.dumps({**json.loads(first[5]), "error": "HTTP 529"})
        partial.write_text("\n".join(first[:5] + [failed_line]) + "\n")
        before = posts()
        code, out, err = run("run", str(CALIBRATION), "--out", str(partial), "--resume", *common)
        resumed = [json.loads(l) for l in partial.read_text().splitlines()]
        check(code == 0 and posts() - before == len(rows) - 5
              and [l["id"] for l in resumed] == [r["id"] for r in rows],
              "--resume sends only the rows not yet answered", err)
        code, out, err = run("run", str(CALIBRATION), "--out", str(partial), "--resume",
                             "--model", "jev-1.14.0", *common)
        check(code != 0 and "another model" in err, "--resume refuses another model's output", err)
        before = len(_StandIn.seen)
        code, out, err = run("run", str(CALIBRATION), "--out", str(partial), "--resume",
                             "--no-order-check", *common)
        check(code != 0 and "--no-order-check" in err and len(_StandIn.seen) == before,
              "--resume refuses an output made with the other order check", err)

        code, out, err = run("score", str(results))
        check(code == 0 and "for adjudication" in out, "score reads the output", out + err)
        code, out, err = run("score", str(results), "--bar", "1.0")
        check(code == 1, "score holds a bar", out)
        code, out, err = run("score", str(results), "--bar", "0")
        check(code == 0 and f"{len(rows)} of its {len(rows)} row(s) answered" in out,
              "a run with every row answered meets a bar it reaches", out + err)
        code, out, err = run("score", str(partial), "--bar", "0")
        check(code == 0, "a resumed run with every row answered meets a bar it reaches", out + err)
        failed_run = tmp / "failed.jsonl"
        failed_run.write_text("\n".join(first[:5] + [failed_line]) + "\n")
        code, out, err = run("score", str(failed_run), "--bar", "0")
        check(code == 1 and "failed" in out, "no bar is met by a run with a failed request", out)
        truncated = tmp / "truncated.jsonl"
        truncated.write_text("\n".join(first[:5]) + "\n")
        code, out, err = run("score", str(truncated), "--bar", "0")
        check(code == 1 and "no answer" in out and "--resume" in out,
              "no bar is met by a run cut short, with rows never sent", out + err)
        unsure = tmp / "unsure.jsonl"
        null_line, absent_line = json.loads(first[0]), json.loads(first[1])
        null_line["confidence"] = None
        del absent_line["confidence"]
        unsure.write_text(json.dumps(null_line) + "\n" + json.dumps(absent_line) + "\n")
        code, out, err = run("score", str(unsure))
        listed = {l.split(":")[0].strip() for l in out.splitlines() if "no confidence given" in l}
        check(code == 0 and {null_line["id"], absent_line["id"]} <= listed,
              "a choice with no confidence goes to adjudication", out + err)

        confidence_cases = []
        for name, reversed_confidence in (("reversed-low", 0.49),
                                          ("reversed-null", None),
                                          ("boundary", 0.5)):
            row = json.loads(first[0])
            row["id"] = name
            row["expected"] = row["choice"]
            row["agrees"] = True
            row["confidence"] = 0.5
            row["reversed"]["confidence"] = reversed_confidence
            row["reversed"]["consistent"] = True
            confidence_cases.append(row)
        reversed_missing = json.loads(first[0])
        reversed_missing["id"] = "reversed-missing"
        reversed_missing["expected"] = reversed_missing["choice"]
        reversed_missing["agrees"] = True
        reversed_missing["confidence"] = 0.5
        reversed_missing["reversed"]["consistent"] = True
        del reversed_missing["reversed"]["confidence"]
        confidence_cases.append(reversed_missing)
        single_order = json.loads(first[0])
        single_order["id"] = "single-order-low"
        single_order["expected"] = single_order["choice"]
        single_order["agrees"] = True
        single_order["confidence"] = 0.49
        single_order.pop("reversed")
        single_order["order_check"] = False
        confidence_cases.append(single_order)
        confidence_cases.extend([
            {"id": "noul-low", "noul": 0.74, "model": DEFAULT_MODEL},
            {"id": "noul-boundary", "noul": 0.75, "model": DEFAULT_MODEL},
        ])
        confidence_file = tmp / "confidence.jsonl"
        confidence_file.write_text("".join(json.dumps(row) + "\n" for row in confidence_cases))
        code, out, err = run("score", str(confidence_file))
        case_ids = {row["id"] for row in confidence_cases}
        listed = {row_id for row_id in case_ids if f"  {row_id}:" in out}
        check(code == 0 and listed == {"reversed-low", "reversed-null", "reversed-missing",
                                      "single-order-low", "noul-low"}
              and "confidence 0.49 with the options reversed" in out
              and "no confidence given with the options reversed" in out,
              "score checks confidence in each asking and keeps the threshold exclusive",
              out + err)
        for broken in (None, [], "reversed", 1, True):
            valid = json.loads(first[1])
            valid["id"] = "valid-before-reversed-broken"
            row = json.loads(first[0])
            row["id"] = "reversed-broken"
            row["expected"] = row["choice"]
            row["agrees"] = True
            row["confidence"] = 0.9
            row["reversed"] = broken
            broken_file = tmp / "reversed-broken.jsonl"
            broken_file.write_text(json.dumps(valid) + "\n" + json.dumps(row) + "\n")
            for extra in ((), ("--bar", "0")):
                code, out, err = run("score", str(broken_file), *extra)
                check(code == 1 and out == "" and "reversed asking is not an answer" in err,
                      f"score refuses a reversed asking of {broken!r}"
                      + (" under a bar" if extra else ""), out + err)

        def one(name: str, row: dict) -> Path:
            p = tmp / name
            p.write_text(json.dumps(row) + "\n")
            return p

        base_row = {"id": "t", "question": {"type": "choice", "instructions": "Which?",
                                             "criteria": {"a": None, "b": None}}}
        echo = one("echo.jsonl", {**base_row, "state": "SELFTEST-ECHO"})
        code, out, err = run("run", str(echo), "--out", str(tmp / "echo-out.jsonl"), *common)
        echoed = (tmp / "echo-out.jsonl").read_text() if (tmp / "echo-out.jsonl").exists() else ""
        check(code == 1 and REDACTED in echoed and clean(out, err, echoed)
              and bool(parsed(echoed)),
              "a key echoed in an error's body is redacted, and the line is still JSON",
              echoed + err)
        for name, what in (("LONG", "a key the body's cut runs through is redacted whole"),
                           ("ESCAPED", "a key echoed with its / escaped is redacted")):
            row = one(f"{name}.jsonl", {**base_row, "state": f"SELFTEST-{name}-ECHO"})
            code, out, err = run("run", str(row), *common)
            check(code == 1 and REDACTED in out and clean(out, err)
                  and key.split("/")[1][:6] not in out and bool(parsed(out)), what, out + err)
        word = one("word.jsonl", {**base_row, "state": "SELFTEST-BEARER-WORD"})
        code, out, err = run("run", str(word), "--out", str(tmp / "word-out.jsonl"), *common)
        worded = parsed((tmp / "word-out.jsonl").read_text()
                        if (tmp / "word-out.jsonl").exists() else "")
        check(code == 1 and bool(worded) and worded[-1].get("status") == 401,
              "a 401 that says \"bearer\" in a JSON string is written as JSON", err)
        broken = one("broken.jsonl", {**base_row, "state": "SELFTEST-BROKEN"})
        code, out, err = run("run", str(broken), *common)
        check(code == 1 and '"error"' in out and "Traceback" not in err,
              "an answer broken off is recorded as a failure, not a crash", out + err)
        malformed = tmp / "malformed.jsonl"
        noul_row = {"id": "t", "question": {"type": "noul", "instructions": "Is it?"}}
        malformed.write_text("".join(
            json.dumps({**template, "id": f"t-{name}", "state": f"SELFTEST-{name}"}) + "\n"
            for name, template in (("NOT-AN-OBJECT", base_row), ("PROBABILITIES-LIST", base_row),
                                   ("CONFIDENCE-SCALE", base_row), ("HUGE-NUMBER", base_row),
                                   ("NOUL-STRING", noul_row))))
        code, out, err = run("run", str(malformed), *common)
        got = parsed(out) or []
        check(code == 1 and "Traceback" not in err and len(got) == 5
              and all(l.get("status") == 200 and "error" in l for l in got),
              "a 200 that is not the documented shape is recorded as a failure, and the run "
              "goes on", out + err)

        redirect = one("redirect.jsonl", {**base_row, "state": "SELFTEST-REDIRECT"})
        code, out, err = run("run", str(redirect), *common)
        check(code == 1 and '"status": 307' in out and
              not any(s["path"] == "/elsewhere" for s in _StandIn.seen),
              "a redirect is not followed", out + err)

        slow = one("slow.jsonl", {**base_row, "state": "SELFTEST-SLOW"})
        code, out, err = run("run", str(slow), "--timeout", "1", *common)
        check(code == 1 and "no answer within 1 s" in out, "the timeout holds", out + err)

        (tmp / "figure.png").write_bytes(_png(300, 320))
        (tmp / "small.png").write_bytes(_png(100, 100))
        ref = "fig-" + secrets.token_hex(4)
        image = one("image.jsonl", {**base_row, "state": {"figure": ref},
                                    "assets": {ref: "figure.png"}})
        code, out, err = run("run", str(image), "--assets-root", str(tmp), *common)
        last = _StandIn.seen[-1]
        req = json.loads(last["body"]) if last["method"] == "POST" else {}
        asset = req.get("assets", {}).get(ref, {})
        check(code == 0 and last["headers"].get(IMAGES_HEADER.lower()) == "true"
              and asset.get("format") == "png"
              and base64.b64decode(asset.get("data_base64", "")) == _png(300, 320),
              "an image is sent in assets, with its header", out + err)
        small = one("small.jsonl", {**base_row, "state": {"figure": ref},
                                    "assets": {ref: "small.png"}})
        before = len(_StandIn.seen)
        code, out, err = run("run", str(small), "--assets-root", str(tmp), *common)
        check(code != 0 and "100 x 100" in err and len(_StandIn.seen) == before,
              "an image under 280 pixels is refused before anything is sent", err)
        outside = one("outside.jsonl", {**base_row, "state": {"figure": ref},
                                        "assets": {ref: "../key"}})
        code, out, err = run("run", str(outside), "--assets-root", str(tmp / "sub"), *common)
        check(code != 0 and clean(out, err), "an asset outside its root is refused", err)
        unref = one("unref.jsonl", {**base_row, "state": "no reference here",
                                    "assets": {ref: "figure.png"}})
        code, out, err = run("run", str(unref), "--assets-root", str(tmp), "--dry-run", *common)
        check(code != 0 and "referenced nowhere" in err, "an asset referenced nowhere is refused", err)

        code, out, err = run("preflight", "--base-url", "http://example.com")
        check(code != 0 and "https" in err, "plain HTTP is refused, but to this machine", err)
    finally:
        server.shutdown()
        shutil.rmtree(tmp, ignore_errors=True)
    if failures:
        print(f"self-test: {len(failures)} failure(s)", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        return 1
    print("self-test: every check passed")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Ask Jev (TypeSafe) the audit's questions; see this file's docstring.")
    sub = parser.add_subparsers(dest="command", required=True)

    def common(p: argparse.ArgumentParser) -> None:
        p.add_argument("--model", default=DEFAULT_MODEL,
                       help=f"a versioned model id (default {DEFAULT_MODEL})")
        p.add_argument("--allow-alias", action="store_true",
                       help="send an alias such as jev-latest, which moves between releases")
        p.add_argument("--base-url", dest="base", default=BASE_URL, help=argparse.SUPPRESS)
        p.add_argument("--timeout", type=float, default=30.0,
                       help="seconds to wait for each answer (default 30)")
        p.add_argument("--svg-width", type=int, default=700,
                       help="the width an SVG figure is rendered at (default 700)")

    p = sub.add_parser("preflight", help="the model listing, and the pinned model")
    common(p)
    p.set_defaults(func=cmd_preflight)
    p = sub.add_parser("smoke", help="preflight, then one trivial decision")
    common(p)
    p.set_defaults(func=cmd_smoke)
    p = sub.add_parser("run", help="preflight, then one request for each row of FILE")
    common(p)
    p.add_argument("file", help="the rows, as JSON Lines")
    p.add_argument("--out", help="where to write the answers (default: standard output)")
    p.add_argument("--overwrite", action="store_true", help="replace an existing --out")
    p.add_argument("--resume", action="store_true",
                   help="keep the answers already in --out, and send only the other rows")
    p.add_argument("--pause", type=float, default=0.0,
                   help="seconds to wait between requests, to keep under a rate limit")
    p.add_argument("--dry-run", action="store_true",
                   help="print every request; read no key, send nothing")
    p.add_argument("--no-order-check", action="store_true",
                   help="ask each choice once, not again with its options reversed")
    p.add_argument("--assets-root", type=Path, default=ROOT,
                   help="the folder asset paths are read from (default: the repository)")
    p.set_defaults(func=cmd_run)
    p = sub.add_parser("score", help="agreement with the expected answers, and what to adjudicate")
    p.add_argument("file", help="the output of run")
    p.add_argument("--bar", type=float,
                   help="exit 1 when agreement is under this fraction, or a request failed, "
                        "or a row of the input has no answer: a bar is met only when every "
                        "row of the input is answered")
    p.add_argument("--low", type=float, default=LOW,
                   help=f"a confidence under this in either asking goes to adjudication, "
                        f"as does an asking with none (default {LOW})")
    p.set_defaults(func=cmd_score)
    p = sub.add_parser("self-test", help="every command, against a stand-in on this machine")
    p.set_defaults(func=cmd_self_test)

    args = parser.parse_args(argv)
    try:
        if hasattr(args, "base"):
            args.base = check_base(args.base)
        return args.func(args)
    except Failure as e:
        say(f"jev: {e}")
        return 1
    except KeyboardInterrupt:
        say("jev: interrupted")
        return 130


if __name__ == "__main__":
    sys.exit(main())
