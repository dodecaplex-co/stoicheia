#!/usr/bin/env python3
"""The group lane's check (docs/decisions/2026-11-12-ci-scope-1a.md): scripts/risk.py's
GROUP_LANE, read by ast, is None, as built, and every merge group is R5; or it names the
condition under which a group may be classed by its diff, and that condition is in force in
this checkout's code:

- "L6": post-merge.yml runs on a push to main, and holds a job that runs
  `scripts/preflight_checklist.py verify --kind main --jobs negative,formal_model` under no
  condition of its own, judged by its own outcome in that job's last step, which always
  runs; its revert job needs that job, runs on its failure, and takes the revert script from
  the previous main and runs it; and GROUP_LANE_GROUNDS, a decisions entry, names a recorded
  run of that verification that failed on a disposable repository and the revert it made.
- "GROUP-VERIFY": ci.yml's negative and formal-model jobs each verify a signed group
  checklist on merge_group, for every class (`scripts/preflight_checklist.py verify --kind
  group --jobs negative`, and `--jobs formal_model`), each judged by its own outcome in its
  job's last step, which always runs.

Anything else fails, naming why. Whether post-merge.yml is enabled on GitHub is a setting the
check cannot see, so the pull request that turns the lane on cites the condition's first
live runs in its decisions entry.

    python3 -m pip install -r scripts/requirements-test_safe_push.txt
    python3 -I tests/test_group_lane.py

PyYAML at the pinned version, standard library otherwise; no network, no Lean. The planted
cases write only in temporary folders.
"""

import ast
import re
import sys
import tempfile
import unittest
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
MAIN_VERIFY = "scripts/preflight_checklist.py verify --kind main --jobs negative,formal_model"
GROUP_VERIFY = {"negative": "scripts/preflight_checklist.py verify --kind group --jobs negative",
                "formal-model": ("scripts/preflight_checklist.py verify --kind group --jobs "
                                 "formal_model")}
# The grounds of L6: a run of the verification that failed on a disposable repository, and
# the revert it made, by its commit or by its pull request and head.
RED_RUN = re.compile(r"^- Red verify run: https://github\.com/[\w.-]+/[\w.-]+/actions/runs/\d+$",
                     re.M)
REVERT = re.compile(r"^- (?:Revert commit: [0-9a-f]{40}|Revert pull request: #\d+ at "
                    r"[0-9a-f]{40})$", re.M)


def switch(root: Path) -> tuple[object, object]:
    """GROUP_LANE and GROUP_LANE_GROUNDS of root's scripts/risk.py, read by ast."""
    found = {}
    for node in ast.parse((root / "scripts/risk.py").read_text(encoding="utf-8")).body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 \
                and isinstance(node.targets[0], ast.Name) \
                and node.targets[0].id in ("GROUP_LANE", "GROUP_LANE_GROUNDS"):
            found[node.targets[0].id] = ast.literal_eval(node.value)
    return found.get("GROUP_LANE", "(none)"), found.get("GROUP_LANE_GROUNDS")


def workflow(root: Path, name: str) -> dict:
    path = root / ".github/workflows" / name
    return yaml.safe_load(path.read_text(encoding="utf-8")) if path.is_file() else {}


def condition(step: dict) -> str:
    value = str(step.get("if", "")).strip()
    if value.startswith("${{") and value.endswith("}}"):
        value = value[3:-2].strip()
    return value


def judged(job: dict, step_id: str) -> bool:
    """Whether the job's last step always runs and reads the step's own outcome."""
    steps = job.get("steps") or []
    if not steps or condition(steps[-1]) != "always()":
        return False
    text = str(steps[-1].get("run", "")) + " ".join(map(str, (steps[-1].get("env") or {}).values()))
    return f"steps.{step_id}.outcome" in text


def l6_problems(root: Path, grounds) -> list[str]:
    post = workflow(root, "post-merge.yml")
    events = post.get("on") or post.get(True) or {}
    push = events.get("push") if isinstance(events, dict) else None
    jobs = post.get("jobs") or {}
    verify = [(name, job, step) for name, job in jobs.items() if isinstance(job, dict)
              for step in job.get("steps") or [] if MAIN_VERIFY in str(step.get("run", ""))]
    revert = jobs.get("revert") or {}
    needs = revert.get("needs") or []
    needs = [needs] if isinstance(needs, str) else needs
    if not (isinstance(push, dict) and push.get("branches") == ["main"]) or len(verify) != 1 \
            or verify[0][0] not in needs or "failure()" not in condition(revert):
        return ["group lane: on because L6, but post-merge.yml holds no verify of the "
                "after-merge negative and formal_model with a revert on its failure"]
    name, job, step = verify[0]
    if "if" in step or not step.get("id") or not judged(job, step["id"]):
        return ["group lane: on because L6, but the verify step can be skipped while its job "
                "passes"]
    steps = revert.get("steps") or []
    takes = [s for s in steps if s.get("id") == "trusted"
             and 'git show "$BEFORE:scripts/auto_revert.py"' in str(s.get("run", ""))]
    runs = [s for s in steps if 'python3 -I "$TRUSTED_SCRIPT"' in str(s.get("run", ""))
            and "steps.trusted.outputs.script" in str((s.get("env") or {}).get("TRUSTED_SCRIPT"))]
    if not takes or not runs:
        return ["group lane: on because L6, but the revert job does not run the trusted revert"]
    entry = root / grounds if isinstance(grounds, str) and grounds.startswith(
        "docs/decisions/") else None
    text = entry.read_text(encoding="utf-8") if entry is not None and entry.is_file() else ""
    if not RED_RUN.search(text) or not REVERT.search(text):
        return ["group lane: on because L6, but its grounds name no demonstrated revert"]
    return []


def group_verify_problems(root: Path) -> list[str]:
    jobs = workflow(root, "ci.yml").get("jobs") or {}
    problems = []
    for name, command in GROUP_VERIFY.items():
        job = jobs.get(name) or {}
        steps = [s for s in job.get("steps") or [] if command in str(s.get("run", ""))]
        if len(steps) != 1 or not steps[0].get("id") \
                or condition(steps[0]) not in ("", "github.event_name == 'merge_group'") \
                or not judged(job, steps[0]["id"]):
            problems.append(f"group lane: on because GROUP-VERIFY, but ci.yml's {name} does not "
                            "verify a group checklist for every class on merge_group by its "
                            "step's outcome")
    return problems


def lane_problems(root: Path) -> tuple[str, list[str]]:
    """The line the check prints when it passes, and why it fails, if it does."""
    lane, grounds = switch(root)
    if lane is None:
        return "group lane: off; every merge group is R5", []
    if lane == "L6":
        return "group lane: on because L6, held in code", l6_problems(root, grounds)
    if lane == "GROUP-VERIFY":
        return "group lane: on because GROUP-VERIFY, held in code", group_verify_problems(root)
    return "", [f"group lane: {lane!r} names no condition"]


# A post-merge.yml that holds L6 in code (L1.s5): the verify job, judged by its own outcome,
# and the revert job, which takes the previous main's revert script and runs it.
POST_MERGE = """name: Post-merge
on:
  push:
    branches: [main]
jobs:
  integration:
    uses: ./.github/workflows/ci.yml
  verify:
    runs-on: ubuntu-latest
    steps:
      - id: verify
        run: python3 scripts/preflight_checklist.py verify --kind main --jobs negative,formal_model
      - if: always()
        env:
          VERIFY: ${{ steps.verify.outcome }}
        run: test "$VERIFY" = success
  revert:
    needs: [integration, verify]
    if: failure()
    runs-on: ubuntu-latest
    steps:
      - id: trusted
        run: git show "$BEFORE:scripts/auto_revert.py" > "$RUNNER_TEMP/auto_revert.py"
      - env:
          TRUSTED_SCRIPT: ${{ steps.trusted.outputs.script }}
        run: python3 -I "$TRUSTED_SCRIPT" --before "$BEFORE" --after "$AFTER"
"""
GROUNDS = ("- Red verify run: https://github.com/owner/disposable/actions/runs/101\n"
           "- Revert commit: " + "1" * 40 + "\n")
CI_GROUP_VERIFY = """jobs:
  negative:
    steps:
      - id: verify
        if: github.event_name == 'merge_group'
        run: python3 scripts/preflight_checklist.py verify --kind group --jobs negative
      - if: always()
        env:
          WORK: ${{ steps.verify.outcome }}
        run: test "$WORK" = success
  formal-model:
    steps:
      - id: verify
        if: github.event_name == 'merge_group'
        run: python3 scripts/preflight_checklist.py verify --kind group --jobs formal_model
      - if: always()
        env:
          WORK: ${{ steps.verify.outcome }}
        run: test "$WORK" = success
"""


class GroupLane(unittest.TestCase):
    def test_the_checkout(self):
        line, problems = lane_problems(ROOT)
        self.assertEqual(problems, [], "\n".join(problems))
        print(f"  {line}")

    def planted(self, lane, grounds=None, post_merge=None, ci=None, entry=None) -> list[str]:
        """lane_problems over a tree of the test's own: risk.py's switch, and the given
        post-merge.yml, ci.yml and decisions entry."""
        root = Path(self.enterContext(tempfile.TemporaryDirectory()))
        (root / "scripts").mkdir()
        (root / ".github/workflows").mkdir(parents=True)
        (root / "docs/decisions").mkdir(parents=True)
        (root / "scripts/risk.py").write_text(f"GROUP_LANE = {lane!r}\n"
                                              f"GROUP_LANE_GROUNDS = {grounds!r}\n")
        for name, text in (("post-merge.yml", post_merge), ("ci.yml", ci)):
            if text is not None:
                (root / ".github/workflows" / name).write_text(text)
        if entry is not None:
            (root / "docs/decisions/grounds.md").write_text(entry)
        return lane_problems(root)[1]

    def assertRefused(self, label, message, **planted):
        problems = self.planted(**planted)
        self.assertEqual(problems, [message])
        print(f"  {label}: {message}")

    def test_L1_s1_off_as_built(self):
        line, problems = lane_problems(ROOT)
        self.assertEqual(switch(ROOT), (None, None))
        self.assertEqual((line, problems), ("group lane: off; every merge group is R5", []))
        print(f"  L1.s1: {line}")

    def test_L1_s2_L6_without_the_verify_job_and_its_revert(self):
        real = (ROOT / ".github/workflows/post-merge.yml").read_text(encoding="utf-8")
        self.assertRefused("L1.s2", "group lane: on because L6, but post-merge.yml holds no "
                           "verify of the after-merge negative and formal_model with a revert "
                           "on its failure", lane="L6", grounds="docs/decisions/grounds.md",
                           post_merge=real, entry=GROUNDS)

    def test_L1_s3_GROUP_VERIFY_without_the_group_checklist(self):
        real = (ROOT / ".github/workflows/ci.yml").read_text(encoding="utf-8")
        problems = self.planted("GROUP-VERIFY", ci=real)
        self.assertEqual(problems, [
            f"group lane: on because GROUP-VERIFY, but ci.yml's {job} does not verify a group "
            "checklist for every class on merge_group by its step's outcome"
            for job in ("negative", "formal-model")])
        print(f"  L1.s3: {problems[0]}")

    def test_L1_s4_a_value_that_names_no_condition(self):
        self.assertRefused("L1.s4", "group lane: 'L2' names no condition", lane="L2")

    def test_L1_s5_L6_held_in_code_passes(self):
        self.assertEqual(self.planted("L6", "docs/decisions/grounds.md", POST_MERGE,
                                      entry=GROUNDS), [])
        print("  L1.s5: GROUP_LANE 'L6' with the verify job, its revert and the grounds: passes")

    def test_L1_s7_a_revert_job_that_does_not_run_the_trusted_revert(self):
        text = POST_MERGE[:POST_MERGE.index("    steps:\n      - id: trusted")] + \
            '    steps:\n      - run: echo TODO\n'
        self.assertRefused("L1.s7", "group lane: on because L6, but the revert job does not run "
                           "the trusted revert", lane="L6", grounds="docs/decisions/grounds.md",
                           post_merge=text, entry=GROUNDS)

    def test_L1_s8_a_verify_step_that_can_be_skipped(self):
        text = POST_MERGE.replace("      - id: verify\n",
                                  "      - id: verify\n        if: ${{ false }}\n")
        self.assertRefused("L1.s8", "group lane: on because L6, but the verify step can be "
                           "skipped while its job passes", lane="L6",
                           grounds="docs/decisions/grounds.md", post_merge=text, entry=GROUNDS)
        # And a verify step its job's last step does not judge.
        text = POST_MERGE.replace("          VERIFY: ${{ steps.verify.outcome }}\n", "")
        self.assertEqual(self.planted("L6", "docs/decisions/grounds.md", text, entry=GROUNDS),
                         ["group lane: on because L6, but the verify step can be skipped "
                          "while its job passes"])

    def test_L1_s9_grounds_that_name_no_demonstrated_revert(self):
        for grounds, entry in ((None, None), ("docs/decisions/grounds.md", "No run.\n"),
                               ("docs/decisions/grounds.md", GROUNDS.splitlines()[0] + "\n")):
            with self.subTest(entry=entry):
                self.assertEqual(self.planted("L6", grounds, POST_MERGE, entry=entry),
                                 ["group lane: on because L6, but its grounds name no "
                                  "demonstrated revert"])
        print("  L1.s9: group lane: on because L6, but its grounds name no demonstrated revert")

    def test_L1_0_clause_GROUP_VERIFY_held_in_code_passes(self):
        self.assertEqual(self.planted("GROUP-VERIFY", ci=CI_GROUP_VERIFY), [])
        # Each job must verify by its own step's outcome, for every class.
        for change in ("        if: github.event_name == 'merge_group'\n",
                       "          WORK: ${{ steps.verify.outcome }}\n"):
            replaced = CI_GROUP_VERIFY.replace(
                change, "        if: needs.risk.outputs.class == 'R5'\n"
                if change.startswith("        if") else "", 1)
            self.assertEqual(self.planted("GROUP-VERIFY", ci=replaced), [
                "group lane: on because GROUP-VERIFY, but ci.yml's negative does not verify a "
                "group checklist for every class on merge_group by its step's outcome"])
        print("  L1.0.clause: GROUP_LANE 'GROUP-VERIFY' passes only with both jobs verifying a "
              "group checklist on merge_group by their verify steps' own outcomes")


if __name__ == "__main__":
    unittest.main(verbosity=1)
