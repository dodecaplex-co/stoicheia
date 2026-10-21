"""Model provenance regressions, using in-process replies and no service."""

import contextlib
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

source = (Path(sys.argv.pop(1)) if len(sys.argv) > 1 else
          Path(__file__).resolve().parents[1] / "scripts/audit/jev.py")
jev = types.ModuleType("jev_under_test")
jev.__file__ = str(source.resolve())
exec(compile(source.read_text(), str(source), "exec"), jev.__dict__)

MODELS = (None, "", "  ", True, 1, "jev-1.13.0", "jev-1.14.0")
ANSWER = {"choice": "a", "probabilities": {"a": 1, "b": 0}, "confidence": 1}
INPUT = {"id": "model", "state": "Local probe", "expected": "a",
         "question": {"type": "choice", "instructions": "Which?",
                      "criteria": {"a": "First", "b": "Second"}}}
MADE = {"input_sha256": "0" * 64, "input_rows": 1,
        "model_requested": "jev-1.13.0", "order_check": False}


def stored(model, made=MADE):
    row = {"id": "model", **ANSWER, **made, "expected": "a", "agrees": True}
    if model is not None:
        row["model"] = model
    if model != MADE["model_requested"]:
        row["model_differs"] = True
    return json.dumps(row) + "\n"


class ModelIdentity(unittest.TestCase):
    def test_run(self):
        for model in MODELS:
            reply = {"answers": {"q": ANSWER}}
            if model is not None:
                reply["model"] = model
            with self.subTest(model=model), \
                    patch.object(Path, "read_text", return_value=json.dumps(INPUT)), \
                    patch.object(Path, "read_bytes", return_value=json.dumps(INPUT).encode()), \
                    patch.object(jev, "read_key", return_value="offline"), \
                    patch.object(jev, "preflight", return_value=[]), \
                    patch.object(jev, "request", return_value=jev.Reply(
                        200, json.dumps(reply).encode(), 0)), \
                    contextlib.redirect_stdout(io.StringIO()) as out, \
                    contextlib.redirect_stderr(io.StringIO()):
                code = jev.main(["run", "input.jsonl", "--no-order-check"])
                invalid = model not in ("jev-1.13.0", "jev-1.14.0")
                self.assertEqual(code, int(invalid))
                self.assertEqual("error" in json.loads(out.getvalue()), invalid)

    def test_score(self):
        for model in MODELS:
            with self.subTest(model=model), \
                    patch.object(Path, "read_text", return_value=stored(model)), \
                    contextlib.redirect_stdout(io.StringIO()) as out, \
                    contextlib.redirect_stderr(io.StringIO()):
                code = jev.main(["score", "answers.jsonl", "--bar", "1"])
                invalid = model not in ("jev-1.13.0", "jev-1.14.0")
                self.assertEqual(code, int(invalid))
                if invalid:
                    self.assertEqual(out.getvalue(), "")
                else:
                    count = int(model != MADE["model_requested"])
                    self.assertIn(f"for adjudication: {count}\n", out.getvalue())

    def test_resume(self):
        for model in MODELS:
            with self.subTest(model=model), tempfile.TemporaryDirectory() as directory:
                folder = Path(directory)
                input_file = folder / "input.jsonl"
                output_file = folder / "answers.jsonl"
                input_file.write_text(json.dumps(INPUT) + "\n")
                made = {**MADE, "input_sha256": hashlib.sha256(
                    input_file.read_bytes()).hexdigest()}
                output_file.write_text(stored(model, made))
                reply = {"model": MADE["model_requested"], "answers": {"q": ANSWER}}
                errors = io.StringIO()
                with patch.object(jev, "read_key", return_value="offline"), \
                        patch.object(jev, "preflight", return_value=[]), \
                        patch.object(jev, "request", return_value=jev.Reply(
                            200, json.dumps(reply).encode(), 0)) as request, \
                        contextlib.redirect_stdout(io.StringIO()), \
                        contextlib.redirect_stderr(errors):
                    code = jev.main(["run", str(input_file), "--out", str(output_file),
                                     "--resume", "--no-order-check"])
                valid = model in ("jev-1.13.0", "jev-1.14.0")
                self.assertEqual(code, 0)
                self.assertEqual(request.call_count, int(not valid))
                self.assertEqual(json.loads(output_file.read_text())["model"],
                                 model if valid else MADE["model_requested"])
                diagnostic = (f"{output_file.name}:1: its answering model is not a "
                              "nonempty string; resume will send this row again\n")
                self.assertEqual(diagnostic in errors.getvalue(), not valid)


if __name__ == "__main__":
    unittest.main()
